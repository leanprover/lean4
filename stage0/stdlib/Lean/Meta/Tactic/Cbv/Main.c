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
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* lean_io_mono_nanos_now();
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
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
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_sym_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t l_Lean_Name_isAnonymous(lean_object*);
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
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___lam__0___closed__0;
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
static const lean_string_object l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "cbv: "};
static const lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___closed__1;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "cbv: no change"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___closed__3;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cbv:"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "decide_cbv: "};
static const lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0___closed__1;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "decide_cbv: closed goal"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 88, .m_capacity = 88, .m_length = 87, .m_data = "`decide_cbv` failed: could not reduce the expression to a boolean value; got stuck at: "};
static const lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__1;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "`decide_cbv` failed: the proposition evaluates to `false`"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__3;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__4_value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 65, .m_capacity = 65, .m_length = 64, .m_data = "`decide_cbv`: expected goal of the form `decide _ = true`, got: "};
static const lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__6;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "decide_cbv:"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__7 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v_contextDependent_714_; uint8_t v___x_715_; 
v_contextDependent_714_ = lean_ctor_get_uint8(v_a_702_, 1);
v___x_715_ = lean_bool_not(v_contextDependent_714_);
v___y_704_ = v___x_715_;
goto v___jp_703_;
}
else
{
uint8_t v_contextDependent_716_; uint8_t v___x_717_; 
v_contextDependent_716_ = lean_ctor_get_uint8(v_a_702_, sizeof(void*)*2 + 1);
v___x_717_ = lean_bool_not(v_contextDependent_716_);
v___y_704_ = v___x_717_;
goto v___jp_703_;
}
}
v___jp_703_:
{
if (v___y_704_ == 0)
{
lean_dec(v_a_702_);
return v___x_701_;
}
else
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConstApp___boxed(lean_object* v_e_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConstApp(v_e_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_);
lean_dec(v_a_727_);
lean_dec_ref(v_a_726_);
lean_dec(v_a_725_);
lean_dec_ref(v_a_724_);
lean_dec(v_a_723_);
lean_dec_ref(v_a_722_);
lean_dec(v_a_721_);
lean_dec_ref(v_a_720_);
lean_dec(v_a_719_);
return v_res_729_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp___lam__0(lean_object* v_a_730_, uint8_t v_done_731_, lean_object* v_x_732_){
_start:
{
uint8_t v___x_733_; 
v___x_733_ = l_Lean_ConstantInfo_hasValue(v_a_730_, v_done_731_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp___lam__0___boxed(lean_object* v_a_734_, lean_object* v_done_735_, lean_object* v_x_736_){
_start:
{
uint8_t v_done_18491__boxed_737_; uint8_t v_res_738_; lean_object* v_r_739_; 
v_done_18491__boxed_737_ = lean_unbox(v_done_735_);
v_res_738_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp___lam__0(v_a_734_, v_done_18491__boxed_737_, v_x_736_);
lean_dec_ref(v_x_736_);
lean_dec_ref(v_a_734_);
v_r_739_ = lean_box(v_res_738_);
return v_r_739_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_740_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_741_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_742_, 0, v___x_741_);
return v___x_742_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_743_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_744_ = lean_unsigned_to_nat(0u);
v___x_745_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_745_, 0, v___x_744_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
lean_ctor_set(v___x_745_, 2, v___x_744_);
lean_ctor_set(v___x_745_, 3, v___x_744_);
lean_ctor_set(v___x_745_, 4, v___x_743_);
lean_ctor_set(v___x_745_, 5, v___x_743_);
lean_ctor_set(v___x_745_, 6, v___x_743_);
lean_ctor_set(v___x_745_, 7, v___x_743_);
lean_ctor_set(v___x_745_, 8, v___x_743_);
lean_ctor_set(v___x_745_, 9, v___x_743_);
return v___x_745_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_746_ = lean_unsigned_to_nat(32u);
v___x_747_ = lean_mk_empty_array_with_capacity(v___x_746_);
v___x_748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_748_, 0, v___x_747_);
return v___x_748_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_749_ = ((size_t)5ULL);
v___x_750_ = lean_unsigned_to_nat(0u);
v___x_751_ = lean_unsigned_to_nat(32u);
v___x_752_ = lean_mk_empty_array_with_capacity(v___x_751_);
v___x_753_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_754_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_754_, 0, v___x_753_);
lean_ctor_set(v___x_754_, 1, v___x_752_);
lean_ctor_set(v___x_754_, 2, v___x_750_);
lean_ctor_set(v___x_754_, 3, v___x_750_);
lean_ctor_set_usize(v___x_754_, 4, v___x_749_);
return v___x_754_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_755_ = lean_box(1);
v___x_756_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_757_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_758_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_758_, 0, v___x_757_);
lean_ctor_set(v___x_758_, 1, v___x_756_);
lean_ctor_set(v___x_758_, 2, v___x_755_);
return v___x_758_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_760_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6));
v___x_761_ = l_Lean_stringToMessageData(v___x_760_);
return v___x_761_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_763_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8));
v___x_764_ = l_Lean_stringToMessageData(v___x_763_);
return v___x_764_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_766_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10));
v___x_767_ = l_Lean_stringToMessageData(v___x_766_);
return v___x_767_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_769_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12));
v___x_770_ = l_Lean_stringToMessageData(v___x_769_);
return v___x_770_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15(void){
_start:
{
lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_772_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14));
v___x_773_ = l_Lean_stringToMessageData(v___x_772_);
return v___x_773_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17(void){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_775_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16));
v___x_776_ = l_Lean_stringToMessageData(v___x_775_);
return v___x_776_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19(void){
_start:
{
lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_778_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18));
v___x_779_ = l_Lean_stringToMessageData(v___x_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_msg_780_, lean_object* v_declHint_781_, lean_object* v___y_782_){
_start:
{
lean_object* v___x_784_; lean_object* v_env_785_; uint8_t v___y_787_; uint8_t v___x_843_; uint8_t v___x_844_; 
v___x_784_ = lean_st_ref_get(v___y_782_);
v_env_785_ = lean_ctor_get(v___x_784_, 0);
lean_inc_ref(v_env_785_);
lean_dec(v___x_784_);
v___x_843_ = l_Lean_Name_isAnonymous(v_declHint_781_);
v___x_844_ = lean_bool_not(v___x_843_);
if (v___x_844_ == 0)
{
v___y_787_ = v___x_844_;
goto v___jp_786_;
}
else
{
uint8_t v_isExporting_845_; 
v_isExporting_845_ = lean_ctor_get_uint8(v_env_785_, sizeof(void*)*8);
v___y_787_ = v_isExporting_845_;
goto v___jp_786_;
}
v___jp_786_:
{
if (v___y_787_ == 0)
{
lean_object* v___x_788_; 
lean_dec_ref(v_env_785_);
lean_dec(v_declHint_781_);
v___x_788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_788_, 0, v_msg_780_);
return v___x_788_;
}
else
{
uint8_t v___x_789_; lean_object* v___x_790_; uint8_t v___x_791_; 
v___x_789_ = 0;
lean_inc_ref(v_env_785_);
v___x_790_ = l_Lean_Environment_setExporting(v_env_785_, v___x_789_);
lean_inc(v_declHint_781_);
lean_inc_ref(v___x_790_);
v___x_791_ = l_Lean_Environment_contains(v___x_790_, v_declHint_781_, v___y_787_);
if (v___x_791_ == 0)
{
lean_object* v___x_792_; 
lean_dec_ref(v___x_790_);
lean_dec_ref(v_env_785_);
lean_dec(v_declHint_781_);
v___x_792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_792_, 0, v_msg_780_);
return v___x_792_;
}
else
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v_c_798_; lean_object* v___x_799_; 
v___x_793_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_794_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_795_ = l_Lean_Options_empty;
v___x_796_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_796_, 0, v___x_790_);
lean_ctor_set(v___x_796_, 1, v___x_793_);
lean_ctor_set(v___x_796_, 2, v___x_794_);
lean_ctor_set(v___x_796_, 3, v___x_795_);
lean_inc(v_declHint_781_);
v___x_797_ = l_Lean_MessageData_ofConstName(v_declHint_781_, v___x_789_);
v_c_798_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_798_, 0, v___x_796_);
lean_ctor_set(v_c_798_, 1, v___x_797_);
v___x_799_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_785_, v_declHint_781_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
lean_dec_ref(v_env_785_);
lean_dec(v_declHint_781_);
v___x_800_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_801_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_801_, 0, v___x_800_);
lean_ctor_set(v___x_801_, 1, v_c_798_);
v___x_802_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_803_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_803_, 0, v___x_801_);
lean_ctor_set(v___x_803_, 1, v___x_802_);
v___x_804_ = l_Lean_MessageData_note(v___x_803_);
v___x_805_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_805_, 0, v_msg_780_);
lean_ctor_set(v___x_805_, 1, v___x_804_);
v___x_806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_806_, 0, v___x_805_);
return v___x_806_;
}
else
{
lean_object* v_val_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_842_; 
v_val_807_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_842_ == 0)
{
v___x_809_ = v___x_799_;
v_isShared_810_ = v_isSharedCheck_842_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_val_807_);
lean_dec(v___x_799_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_842_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v_mod_814_; uint8_t v___x_815_; 
v___x_811_ = lean_box(0);
v___x_812_ = l_Lean_Environment_header(v_env_785_);
lean_dec_ref(v_env_785_);
v___x_813_ = l_Lean_EnvironmentHeader_moduleNames(v___x_812_);
v_mod_814_ = lean_array_get(v___x_811_, v___x_813_, v_val_807_);
lean_dec(v_val_807_);
lean_dec_ref(v___x_813_);
v___x_815_ = l_Lean_isPrivateName(v_declHint_781_);
lean_dec(v_declHint_781_);
if (v___x_815_ == 0)
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_827_; 
v___x_816_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_816_);
lean_ctor_set(v___x_817_, 1, v_c_798_);
v___x_818_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_819_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_819_, 0, v___x_817_);
lean_ctor_set(v___x_819_, 1, v___x_818_);
v___x_820_ = l_Lean_MessageData_ofName(v_mod_814_);
v___x_821_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_821_, 0, v___x_819_);
lean_ctor_set(v___x_821_, 1, v___x_820_);
v___x_822_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_823_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_823_, 0, v___x_821_);
lean_ctor_set(v___x_823_, 1, v___x_822_);
v___x_824_ = l_Lean_MessageData_note(v___x_823_);
v___x_825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_825_, 0, v_msg_780_);
lean_ctor_set(v___x_825_, 1, v___x_824_);
if (v_isShared_810_ == 0)
{
lean_ctor_set_tag(v___x_809_, 0);
lean_ctor_set(v___x_809_, 0, v___x_825_);
v___x_827_ = v___x_809_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v___x_825_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
else
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_840_; 
v___x_829_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_830_, 0, v___x_829_);
lean_ctor_set(v___x_830_, 1, v_c_798_);
v___x_831_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_832_, 0, v___x_830_);
lean_ctor_set(v___x_832_, 1, v___x_831_);
v___x_833_ = l_Lean_MessageData_ofName(v_mod_814_);
v___x_834_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_834_, 0, v___x_832_);
lean_ctor_set(v___x_834_, 1, v___x_833_);
v___x_835_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
v___x_836_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_836_, 0, v___x_834_);
lean_ctor_set(v___x_836_, 1, v___x_835_);
v___x_837_ = l_Lean_MessageData_note(v___x_836_);
v___x_838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_838_, 0, v_msg_780_);
lean_ctor_set(v___x_838_, 1, v___x_837_);
if (v_isShared_810_ == 0)
{
lean_ctor_set_tag(v___x_809_, 0);
lean_ctor_set(v___x_809_, 0, v___x_838_);
v___x_840_ = v___x_809_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v___x_838_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msg_846_, lean_object* v_declHint_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_846_, v_declHint_847_, v___y_848_);
lean_dec(v___y_848_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_msg_851_, lean_object* v_declHint_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_){
_start:
{
lean_object* v___x_863_; lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_873_; 
v___x_863_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_851_, v_declHint_852_, v___y_861_);
v_a_864_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_873_ == 0)
{
v___x_866_ = v___x_863_;
v_isShared_867_ = v_isSharedCheck_873_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_863_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_873_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_871_; 
v___x_868_ = l_Lean_unknownIdentifierMessageTag;
v___x_869_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_869_, 0, v___x_868_);
lean_ctor_set(v___x_869_, 1, v_a_864_);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 0, v___x_869_);
v___x_871_ = v___x_866_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_869_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_msg_874_, lean_object* v_declHint_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_874_, v_declHint_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
lean_dec(v___y_884_);
lean_dec_ref(v___y_883_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec(v___y_878_);
lean_dec_ref(v___y_877_);
lean_dec(v___y_876_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_msg_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
lean_object* v_ref_893_; lean_object* v___x_894_; lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_903_; 
v_ref_893_ = lean_ctor_get(v___y_890_, 5);
v___x_894_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0_spec__0(v_msg_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_);
v_a_895_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_903_ == 0)
{
v___x_897_ = v___x_894_;
v_isShared_898_ = v_isSharedCheck_903_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_894_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_903_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_899_; lean_object* v___x_901_; 
lean_inc(v_ref_893_);
v___x_899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_899_, 0, v_ref_893_);
lean_ctor_set(v___x_899_, 1, v_a_895_);
if (v_isShared_898_ == 0)
{
lean_ctor_set_tag(v___x_897_, 1);
lean_ctor_set(v___x_897_, 0, v___x_899_);
v___x_901_ = v___x_897_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v___x_899_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_msg_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_911_, lean_object* v_msg_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v_fileName_923_; lean_object* v_fileMap_924_; lean_object* v_options_925_; lean_object* v_currRecDepth_926_; lean_object* v_maxRecDepth_927_; lean_object* v_ref_928_; lean_object* v_currNamespace_929_; lean_object* v_openDecls_930_; lean_object* v_initHeartbeats_931_; lean_object* v_maxHeartbeats_932_; lean_object* v_quotContext_933_; lean_object* v_currMacroScope_934_; uint8_t v_diag_935_; lean_object* v_cancelTk_x3f_936_; uint8_t v_suppressElabErrors_937_; lean_object* v_inheritedTraceOptions_938_; lean_object* v_ref_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v_fileName_923_ = lean_ctor_get(v___y_920_, 0);
v_fileMap_924_ = lean_ctor_get(v___y_920_, 1);
v_options_925_ = lean_ctor_get(v___y_920_, 2);
v_currRecDepth_926_ = lean_ctor_get(v___y_920_, 3);
v_maxRecDepth_927_ = lean_ctor_get(v___y_920_, 4);
v_ref_928_ = lean_ctor_get(v___y_920_, 5);
v_currNamespace_929_ = lean_ctor_get(v___y_920_, 6);
v_openDecls_930_ = lean_ctor_get(v___y_920_, 7);
v_initHeartbeats_931_ = lean_ctor_get(v___y_920_, 8);
v_maxHeartbeats_932_ = lean_ctor_get(v___y_920_, 9);
v_quotContext_933_ = lean_ctor_get(v___y_920_, 10);
v_currMacroScope_934_ = lean_ctor_get(v___y_920_, 11);
v_diag_935_ = lean_ctor_get_uint8(v___y_920_, sizeof(void*)*14);
v_cancelTk_x3f_936_ = lean_ctor_get(v___y_920_, 12);
v_suppressElabErrors_937_ = lean_ctor_get_uint8(v___y_920_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_938_ = lean_ctor_get(v___y_920_, 13);
v_ref_939_ = l_Lean_replaceRef(v_ref_911_, v_ref_928_);
lean_inc_ref(v_inheritedTraceOptions_938_);
lean_inc(v_cancelTk_x3f_936_);
lean_inc(v_currMacroScope_934_);
lean_inc(v_quotContext_933_);
lean_inc(v_maxHeartbeats_932_);
lean_inc(v_initHeartbeats_931_);
lean_inc(v_openDecls_930_);
lean_inc(v_currNamespace_929_);
lean_inc(v_maxRecDepth_927_);
lean_inc(v_currRecDepth_926_);
lean_inc_ref(v_options_925_);
lean_inc_ref(v_fileMap_924_);
lean_inc_ref(v_fileName_923_);
v___x_940_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_940_, 0, v_fileName_923_);
lean_ctor_set(v___x_940_, 1, v_fileMap_924_);
lean_ctor_set(v___x_940_, 2, v_options_925_);
lean_ctor_set(v___x_940_, 3, v_currRecDepth_926_);
lean_ctor_set(v___x_940_, 4, v_maxRecDepth_927_);
lean_ctor_set(v___x_940_, 5, v_ref_939_);
lean_ctor_set(v___x_940_, 6, v_currNamespace_929_);
lean_ctor_set(v___x_940_, 7, v_openDecls_930_);
lean_ctor_set(v___x_940_, 8, v_initHeartbeats_931_);
lean_ctor_set(v___x_940_, 9, v_maxHeartbeats_932_);
lean_ctor_set(v___x_940_, 10, v_quotContext_933_);
lean_ctor_set(v___x_940_, 11, v_currMacroScope_934_);
lean_ctor_set(v___x_940_, 12, v_cancelTk_x3f_936_);
lean_ctor_set(v___x_940_, 13, v_inheritedTraceOptions_938_);
lean_ctor_set_uint8(v___x_940_, sizeof(void*)*14, v_diag_935_);
lean_ctor_set_uint8(v___x_940_, sizeof(void*)*14 + 1, v_suppressElabErrors_937_);
v___x_941_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_912_, v___y_918_, v___y_919_, v___x_940_, v___y_921_);
lean_dec_ref_known(v___x_940_, 14);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_942_, lean_object* v_msg_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_942_, v_msg_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec(v___y_950_);
lean_dec_ref(v___y_949_);
lean_dec(v___y_948_);
lean_dec_ref(v___y_947_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
lean_dec(v___y_944_);
lean_dec(v_ref_942_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_955_, lean_object* v_msg_956_, lean_object* v_declHint_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_){
_start:
{
lean_object* v___x_968_; lean_object* v_a_969_; lean_object* v___x_970_; 
v___x_968_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_956_, v_declHint_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_);
v_a_969_ = lean_ctor_get(v___x_968_, 0);
lean_inc(v_a_969_);
lean_dec_ref(v___x_968_);
v___x_970_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_955_, v_a_969_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_971_, lean_object* v_msg_972_, lean_object* v_declHint_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_971_, v_msg_972_, v_declHint_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
lean_dec(v___y_974_);
lean_dec(v_ref_971_);
return v_res_984_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_986_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_987_ = l_Lean_stringToMessageData(v___x_986_);
return v___x_987_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_989_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_990_ = l_Lean_stringToMessageData(v___x_989_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_991_, lean_object* v_constName_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
lean_object* v___x_1003_; uint8_t v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1003_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1004_ = 0;
lean_inc(v_constName_992_);
v___x_1005_ = l_Lean_MessageData_ofConstName(v_constName_992_, v___x_1004_);
v___x_1006_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1003_);
lean_ctor_set(v___x_1006_, 1, v___x_1005_);
v___x_1007_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_1008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1006_);
lean_ctor_set(v___x_1008_, 1, v___x_1007_);
v___x_1009_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_991_, v___x_1008_, v_constName_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1010_, lean_object* v_constName_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg(v_ref_1010_, v_constName_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
lean_dec(v___y_1012_);
lean_dec(v_ref_1010_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0___redArg(lean_object* v_constName_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
lean_object* v_ref_1034_; lean_object* v___x_1035_; 
v_ref_1034_ = lean_ctor_get(v___y_1031_, 5);
v___x_1035_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg(v_ref_1034_, v_constName_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0___redArg(v_constName_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
lean_dec(v___y_1037_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0(lean_object* v_constName_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v___x_1059_; lean_object* v_env_1060_; uint8_t v___x_1061_; lean_object* v___x_1062_; 
v___x_1059_ = lean_st_ref_get(v___y_1057_);
v_env_1060_ = lean_ctor_get(v___x_1059_, 0);
lean_inc_ref(v_env_1060_);
lean_dec(v___x_1059_);
v___x_1061_ = 0;
lean_inc(v_constName_1048_);
v___x_1062_ = l_Lean_Environment_find_x3f(v_env_1060_, v_constName_1048_, v___x_1061_);
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_object* v___x_1063_; 
v___x_1063_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0___redArg(v_constName_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
return v___x_1063_;
}
else
{
lean_object* v_val_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1071_; 
lean_dec(v_constName_1048_);
v_val_1064_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1066_ = v___x_1062_;
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_val_1064_);
lean_dec(v___x_1062_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1069_; 
if (v_isShared_1067_ == 0)
{
lean_ctor_set_tag(v___x_1066_, 0);
v___x_1069_ = v___x_1066_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_val_1064_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0___boxed(lean_object* v_constName_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_){
_start:
{
lean_object* v_res_1083_; 
v_res_1083_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0(v_constName_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp(lean_object* v_e_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_){
_start:
{
lean_object* v___y_1096_; lean_object* v___y_1097_; uint8_t v___y_1098_; uint8_t v___x_1101_; 
v___x_1101_ = l_Lean_Expr_isApp(v_e_1084_);
if (v___x_1101_ == 0)
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
lean_dec_ref(v_e_1084_);
v___x_1102_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_1102_, 0, v___x_1101_);
lean_ctor_set_uint8(v___x_1102_, 1, v___x_1101_);
v___x_1103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1102_);
return v___x_1103_;
}
else
{
lean_object* v_fn_1104_; 
v_fn_1104_ = l_Lean_Expr_getAppFn(v_e_1084_);
switch(lean_obj_tag(v_fn_1104_))
{
case 4:
{
lean_object* v_declName_1105_; lean_object* v___x_1106_; 
v_declName_1105_ = lean_ctor_get(v_fn_1104_, 0);
lean_inc(v_declName_1105_);
lean_dec_ref_known(v_fn_1104_, 2);
v___x_1106_ = l_Lean_Meta_Tactic_Cbv_isCbvOpaque___redArg(v_declName_1105_, v_a_1093_);
if (lean_obj_tag(v___x_1106_) == 0)
{
lean_object* v_a_1107_; uint8_t v___x_1108_; 
v_a_1107_ = lean_ctor_get(v___x_1106_, 0);
lean_inc(v_a_1107_);
lean_dec_ref_known(v___x_1106_, 1);
v___x_1108_ = lean_unbox(v_a_1107_);
lean_dec(v_a_1107_);
if (v___x_1108_ == 0)
{
lean_object* v___x_1109_; 
v___x_1109_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0(v_declName_1105_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_);
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v_a_1110_; lean_object* v___x_1111_; 
v_a_1110_ = lean_ctor_get(v___x_1109_, 0);
lean_inc(v_a_1110_);
lean_dec_ref_known(v___x_1109_, 1);
lean_inc_ref(v_e_1084_);
v___x_1111_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems(v_e_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_);
if (lean_obj_tag(v___x_1111_) == 0)
{
lean_object* v_a_1112_; 
v_a_1112_ = lean_ctor_get(v___x_1111_, 0);
lean_inc(v_a_1112_);
if (lean_obj_tag(v_a_1112_) == 0)
{
uint8_t v_done_1113_; uint8_t v_contextDependent_1114_; lean_object* v___y_1116_; lean_object* v_a_1117_; lean_object* v___y_1123_; 
v_done_1113_ = lean_ctor_get_uint8(v_a_1112_, 0);
v_contextDependent_1114_ = lean_ctor_get_uint8(v_a_1112_, 1);
lean_dec_ref_known(v_a_1112_, 0);
if (v_done_1113_ == 0)
{
lean_object* v___x_1125_; lean_object* v___f_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
lean_dec_ref_known(v___x_1111_, 1);
v___x_1125_ = lean_box(v_done_1113_);
v___f_1126_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1126_, 0, v_a_1110_);
lean_closure_set(v___f_1126_, 1, v___x_1125_);
v___x_1127_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConstApp___boxed), 11, 0);
lean_inc_ref(v_e_1084_);
v___x_1128_ = l_Lean_Meta_Tactic_Cbv_guardSimproc(v___f_1126_, v___x_1127_, v_e_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_);
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_object* v_a_1129_; 
v_a_1129_ = lean_ctor_get(v___x_1128_, 0);
lean_inc(v_a_1129_);
if (lean_obj_tag(v_a_1129_) == 0)
{
uint8_t v_done_1130_; 
v_done_1130_ = lean_ctor_get_uint8(v_a_1129_, 0);
if (v_done_1130_ == 0)
{
uint8_t v_contextDependent_1131_; lean_object* v___x_1132_; 
lean_dec_ref_known(v___x_1128_, 1);
v_contextDependent_1131_ = lean_ctor_get_uint8(v_a_1129_, 1);
lean_dec_ref_known(v_a_1129_, 0);
v___x_1132_ = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher(v_e_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_);
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_object* v_a_1133_; uint8_t v___y_1135_; 
v_a_1133_ = lean_ctor_get(v___x_1132_, 0);
lean_inc(v_a_1133_);
if (v_contextDependent_1131_ == 0)
{
lean_dec(v_a_1133_);
v___y_1123_ = v___x_1132_;
goto v___jp_1122_;
}
else
{
if (lean_obj_tag(v_a_1133_) == 0)
{
uint8_t v_contextDependent_1145_; uint8_t v___x_1146_; 
v_contextDependent_1145_ = lean_ctor_get_uint8(v_a_1133_, 1);
v___x_1146_ = lean_bool_not(v_contextDependent_1145_);
v___y_1135_ = v___x_1146_;
goto v___jp_1134_;
}
else
{
uint8_t v_contextDependent_1147_; uint8_t v___x_1148_; 
v_contextDependent_1147_ = lean_ctor_get_uint8(v_a_1133_, sizeof(void*)*2 + 1);
v___x_1148_ = lean_bool_not(v_contextDependent_1147_);
v___y_1135_ = v___x_1148_;
goto v___jp_1134_;
}
}
v___jp_1134_:
{
if (v___y_1135_ == 0)
{
lean_dec(v_a_1133_);
v___y_1123_ = v___x_1132_;
goto v___jp_1122_;
}
else
{
lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1143_; 
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1143_ == 0)
{
lean_object* v_unused_1144_; 
v_unused_1144_ = lean_ctor_get(v___x_1132_, 0);
lean_dec(v_unused_1144_);
v___x_1137_ = v___x_1132_;
v_isShared_1138_ = v_isSharedCheck_1143_;
goto v_resetjp_1136_;
}
else
{
lean_dec(v___x_1132_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1143_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1139_; lean_object* v___x_1141_; 
v___x_1139_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1133_);
lean_inc_ref(v___x_1139_);
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 0, v___x_1139_);
v___x_1141_ = v___x_1137_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v___x_1139_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
v___y_1116_ = v___x_1141_;
v_a_1117_ = v___x_1139_;
goto v___jp_1115_;
}
}
}
}
}
else
{
v___y_1123_ = v___x_1132_;
goto v___jp_1122_;
}
}
else
{
lean_dec_ref_known(v_a_1129_, 0);
lean_dec_ref(v_e_1084_);
v___y_1123_ = v___x_1128_;
goto v___jp_1122_;
}
}
else
{
lean_dec_ref_known(v_a_1129_, 2);
lean_dec_ref(v_e_1084_);
v___y_1123_ = v___x_1128_;
goto v___jp_1122_;
}
}
else
{
lean_dec_ref(v_e_1084_);
v___y_1123_ = v___x_1128_;
goto v___jp_1122_;
}
}
else
{
lean_dec(v_a_1110_);
lean_dec_ref(v_e_1084_);
return v___x_1111_;
}
v___jp_1115_:
{
if (v_contextDependent_1114_ == 0)
{
lean_dec_ref(v_a_1117_);
return v___y_1116_;
}
else
{
if (lean_obj_tag(v_a_1117_) == 0)
{
uint8_t v_contextDependent_1118_; uint8_t v___x_1119_; 
v_contextDependent_1118_ = lean_ctor_get_uint8(v_a_1117_, 1);
v___x_1119_ = lean_bool_not(v_contextDependent_1118_);
v___y_1096_ = v___y_1116_;
v___y_1097_ = v_a_1117_;
v___y_1098_ = v___x_1119_;
goto v___jp_1095_;
}
else
{
uint8_t v_contextDependent_1120_; uint8_t v___x_1121_; 
v_contextDependent_1120_ = lean_ctor_get_uint8(v_a_1117_, sizeof(void*)*2 + 1);
v___x_1121_ = lean_bool_not(v_contextDependent_1120_);
v___y_1096_ = v___y_1116_;
v___y_1097_ = v_a_1117_;
v___y_1098_ = v___x_1121_;
goto v___jp_1095_;
}
}
}
v___jp_1122_:
{
if (lean_obj_tag(v___y_1123_) == 0)
{
lean_object* v_a_1124_; 
v_a_1124_ = lean_ctor_get(v___y_1123_, 0);
lean_inc(v_a_1124_);
v___y_1116_ = v___y_1123_;
v_a_1117_ = v_a_1124_;
goto v___jp_1115_;
}
else
{
return v___y_1123_;
}
}
}
else
{
lean_dec_ref_known(v_a_1112_, 2);
lean_dec(v_a_1110_);
lean_dec_ref(v_e_1084_);
return v___x_1111_;
}
}
else
{
lean_dec(v_a_1110_);
lean_dec_ref(v_e_1084_);
return v___x_1111_;
}
}
else
{
lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1156_; 
lean_dec_ref(v_e_1084_);
v_a_1149_ = lean_ctor_get(v___x_1109_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1151_ = v___x_1109_;
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_dec(v___x_1109_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1154_; 
if (v_isShared_1152_ == 0)
{
v___x_1154_ = v___x_1151_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_a_1149_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
}
else
{
lean_object* v___x_1157_; 
lean_dec(v_declName_1105_);
v___x_1157_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems(v_e_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_);
if (lean_obj_tag(v___x_1157_) == 0)
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1166_; 
v_a_1158_ = lean_ctor_get(v___x_1157_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1160_ = v___x_1157_;
v_isShared_1161_ = v_isSharedCheck_1166_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1157_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1166_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1162_; lean_object* v___x_1164_; 
v___x_1162_ = l_Lean_Meta_Tactic_Cbv_markAsDoneIfFailed(v_a_1158_);
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 0, v___x_1162_);
v___x_1164_ = v___x_1160_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v___x_1162_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
else
{
return v___x_1157_;
}
}
}
else
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1174_; 
lean_dec(v_declName_1105_);
lean_dec_ref(v_e_1084_);
v_a_1167_ = lean_ctor_get(v___x_1106_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1169_ = v___x_1106_;
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___x_1106_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1172_; 
if (v_isShared_1170_ == 0)
{
v___x_1172_ = v___x_1169_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_a_1167_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
case 6:
{
lean_object* v___x_1175_; 
lean_dec_ref_known(v_fn_1104_, 3);
v___x_1175_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg(v_e_1084_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_);
return v___x_1175_;
}
default: 
{
lean_object* v___x_1176_; lean_object* v___x_1177_; 
lean_dec_ref(v_fn_1104_);
lean_dec_ref(v_e_1084_);
v___x_1176_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
v___x_1177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1176_);
return v___x_1177_;
}
}
}
v___jp_1095_:
{
if (v___y_1098_ == 0)
{
lean_dec_ref(v___y_1097_);
return v___y_1096_;
}
else
{
lean_object* v___x_1099_; lean_object* v___x_1100_; 
lean_dec_ref(v___y_1096_);
v___x_1099_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_1097_);
v___x_1100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1099_);
return v___x_1100_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp___boxed(lean_object* v_e_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp(v_e_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_);
lean_dec(v_a_1187_);
lean_dec_ref(v_a_1186_);
lean_dec(v_a_1185_);
lean_dec_ref(v_a_1184_);
lean_dec(v_a_1183_);
lean_dec_ref(v_a_1182_);
lean_dec(v_a_1181_);
lean_dec_ref(v_a_1180_);
lean_dec(v_a_1179_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0(lean_object* v_00_u03b1_1190_, lean_object* v_constName_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
lean_object* v___x_1202_; 
v___x_1202_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0___redArg(v_constName_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1203_, lean_object* v_constName_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0(v_00_u03b1_1203_, v_constName_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1212_);
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_dec(v___y_1209_);
lean_dec_ref(v___y_1208_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v___y_1205_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1216_, lean_object* v_ref_1217_, lean_object* v_constName_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
lean_object* v___x_1229_; 
v___x_1229_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg(v_ref_1217_, v_constName_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1230_, lean_object* v_ref_1231_, lean_object* v_constName_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
lean_object* v_res_1243_; 
v_res_1243_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1(v_00_u03b1_1230_, v_ref_1231_, v_constName_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec(v___y_1233_);
lean_dec(v_ref_1231_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1244_, lean_object* v_ref_1245_, lean_object* v_msg_1246_, lean_object* v_declHint_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
lean_object* v___x_1258_; 
v___x_1258_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1245_, v_msg_1246_, v_declHint_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1259_, lean_object* v_ref_1260_, lean_object* v_msg_1261_, lean_object* v_declHint_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1259_, v_ref_1260_, v_msg_1261_, v_declHint_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
lean_dec(v___y_1263_);
lean_dec(v_ref_1260_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_1274_, lean_object* v_declHint_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
lean_object* v___x_1286_; 
v___x_1286_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1274_, v_declHint_1275_, v___y_1284_);
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_1287_, lean_object* v_declHint_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_1287_, v_declHint_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
lean_dec(v___y_1293_);
lean_dec_ref(v___y_1292_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
lean_dec(v___y_1289_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_1300_, lean_object* v_ref_1301_, lean_object* v_msg_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_){
_start:
{
lean_object* v___x_1313_; 
v___x_1313_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1301_, v_msg_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_1314_, lean_object* v_ref_1315_, lean_object* v_msg_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_1314_, v_ref_1315_, v_msg_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec(v___y_1317_);
lean_dec(v_ref_1315_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_1328_, lean_object* v_msg_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
lean_object* v___x_1340_; 
v___x_1340_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_1329_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1341_, lean_object* v_msg_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_){
_start:
{
lean_object* v_res_1353_; 
v_res_1353_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(v_00_u03b1_1341_, v_msg_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
lean_dec(v___y_1343_);
return v_res_1353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleOpaqueConst(lean_object* v_e_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_){
_start:
{
if (lean_obj_tag(v_e_1354_) == 4)
{
lean_object* v_declName_1365_; lean_object* v___x_1366_; 
v_declName_1365_ = lean_ctor_get(v_e_1354_, 0);
v___x_1366_ = l_Lean_Meta_Tactic_Cbv_isCbvOpaque___redArg(v_declName_1365_, v_a_1363_);
if (lean_obj_tag(v___x_1366_) == 0)
{
lean_object* v_a_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1388_; 
v_a_1367_ = lean_ctor_get(v___x_1366_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1369_ = v___x_1366_;
v_isShared_1370_ = v_isSharedCheck_1388_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_a_1367_);
lean_dec(v___x_1366_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1388_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
uint8_t v___x_1371_; 
v___x_1371_ = lean_unbox(v_a_1367_);
if (v___x_1371_ == 0)
{
lean_object* v___x_1372_; uint8_t v___x_1373_; uint8_t v___x_1374_; lean_object* v___x_1376_; 
lean_dec_ref_known(v_e_1354_, 2);
v___x_1372_ = lean_alloc_ctor(0, 0, 2);
v___x_1373_ = lean_unbox(v_a_1367_);
lean_ctor_set_uint8(v___x_1372_, 0, v___x_1373_);
v___x_1374_ = lean_unbox(v_a_1367_);
lean_dec(v_a_1367_);
lean_ctor_set_uint8(v___x_1372_, 1, v___x_1374_);
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 0, v___x_1372_);
v___x_1376_ = v___x_1369_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v___x_1372_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
else
{
lean_object* v___x_1378_; 
lean_del_object(v___x_1369_);
lean_dec(v_a_1367_);
v___x_1378_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems(v_e_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_object* v_a_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1387_; 
v_a_1379_ = lean_ctor_get(v___x_1378_, 0);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1381_ = v___x_1378_;
v_isShared_1382_ = v_isSharedCheck_1387_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_a_1379_);
lean_dec(v___x_1378_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1387_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1383_; lean_object* v___x_1385_; 
v___x_1383_ = l_Lean_Meta_Tactic_Cbv_markAsDoneIfFailed(v_a_1379_);
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 0, v___x_1383_);
v___x_1385_ = v___x_1381_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v___x_1383_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
else
{
return v___x_1378_;
}
}
}
}
else
{
lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1396_; 
lean_dec_ref_known(v_e_1354_, 2);
v_a_1389_ = lean_ctor_get(v___x_1366_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1391_ = v___x_1366_;
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v___x_1366_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1394_; 
if (v_isShared_1392_ == 0)
{
v___x_1394_ = v___x_1391_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_a_1389_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
}
}
else
{
lean_object* v___x_1397_; lean_object* v___x_1398_; 
lean_dec_ref(v_e_1354_);
v___x_1397_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
v___x_1398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1398_, 0, v___x_1397_);
return v___x_1398_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleOpaqueConst___boxed(lean_object* v_e_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_){
_start:
{
lean_object* v_res_1410_; 
v_res_1410_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleOpaqueConst(v_e_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_);
lean_dec(v_a_1408_);
lean_dec_ref(v_a_1407_);
lean_dec(v_a_1406_);
lean_dec_ref(v_a_1405_);
lean_dec(v_a_1404_);
lean_dec_ref(v_a_1403_);
lean_dec(v_a_1402_);
lean_dec_ref(v_a_1401_);
lean_dec(v_a_1400_);
return v_res_1410_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__1(void){
_start:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1412_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__0));
v___x_1413_ = l_Lean_stringToMessageData(v___x_1412_);
return v___x_1413_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__3(void){
_start:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; 
v___x_1415_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__2));
v___x_1416_ = l_Lean_stringToMessageData(v___x_1415_);
return v___x_1416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg(lean_object* v_e_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_){
_start:
{
lean_object* v___x_1425_; 
lean_inc_ref(v_e_1417_);
v___x_1425_ = l_Lean_Expr_rawNatLit_x3f(v_e_1417_);
if (lean_obj_tag(v___x_1425_) == 1)
{
lean_object* v_val_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
v_val_1426_ = lean_ctor_get(v___x_1425_, 0);
lean_inc(v_val_1426_);
lean_dec_ref_known(v___x_1425_, 1);
v___x_1427_ = l_Lean_mkNatLit(v_val_1426_);
v___x_1428_ = l_Lean_Meta_Sym_shareCommonInc(v___x_1427_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_);
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_object* v_a_1429_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1435_; lean_object* v___y_1436_; lean_object* v_options_1456_; uint8_t v_hasTrace_1457_; 
v_a_1429_ = lean_ctor_get(v___x_1428_, 0);
lean_inc(v_a_1429_);
lean_dec_ref_known(v___x_1428_, 1);
v_options_1456_ = lean_ctor_get(v_a_1422_, 2);
v_hasTrace_1457_ = lean_ctor_get_uint8(v_options_1456_, sizeof(void*)*1);
if (v_hasTrace_1457_ == 0)
{
v___y_1431_ = v_a_1418_;
v___y_1432_ = v_a_1419_;
v___y_1433_ = v_a_1420_;
v___y_1434_ = v_a_1421_;
v___y_1435_ = v_a_1422_;
v___y_1436_ = v_a_1423_;
goto v___jp_1430_;
}
else
{
lean_object* v_inheritedTraceOptions_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; uint8_t v___x_1461_; 
v_inheritedTraceOptions_1458_ = lean_ctor_get(v_a_1422_, 13);
v___x_1459_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2));
v___x_1460_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3);
v___x_1461_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1458_, v_options_1456_, v___x_1460_);
if (v___x_1461_ == 0)
{
v___y_1431_ = v_a_1418_;
v___y_1432_ = v_a_1419_;
v___y_1433_ = v_a_1420_;
v___y_1434_ = v_a_1421_;
v___y_1435_ = v_a_1422_;
v___y_1436_ = v_a_1423_;
goto v___jp_1430_;
}
else
{
lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1462_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__1, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__1);
lean_inc_ref(v_e_1417_);
v___x_1463_ = l_Lean_MessageData_ofExpr(v_e_1417_);
v___x_1464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1464_, 0, v___x_1462_);
lean_ctor_set(v___x_1464_, 1, v___x_1463_);
v___x_1465_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__3, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__3);
v___x_1466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1466_, 0, v___x_1464_);
lean_ctor_set(v___x_1466_, 1, v___x_1465_);
lean_inc(v_a_1429_);
v___x_1467_ = l_Lean_MessageData_ofExpr(v_a_1429_);
v___x_1468_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1468_, 0, v___x_1466_);
lean_ctor_set(v___x_1468_, 1, v___x_1467_);
v___x_1469_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(v___x_1459_, v___x_1468_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_);
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_dec_ref_known(v___x_1469_, 1);
v___y_1431_ = v_a_1418_;
v___y_1432_ = v_a_1419_;
v___y_1433_ = v_a_1420_;
v___y_1434_ = v_a_1421_;
v___y_1435_ = v_a_1422_;
v___y_1436_ = v_a_1423_;
goto v___jp_1430_;
}
else
{
lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1477_; 
lean_dec(v_a_1429_);
lean_dec_ref(v_e_1417_);
v_a_1470_ = lean_ctor_get(v___x_1469_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1472_ = v___x_1469_;
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_dec(v___x_1469_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1475_; 
if (v_isShared_1473_ == 0)
{
v___x_1475_ = v___x_1472_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_a_1470_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
}
}
v___jp_1430_:
{
lean_object* v___x_1437_; 
v___x_1437_ = l_Lean_Meta_Sym_mkEqRefl(v_e_1417_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_);
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1447_; 
v_a_1438_ = lean_ctor_get(v___x_1437_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1440_ = v___x_1437_;
v_isShared_1441_ = v_isSharedCheck_1447_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v___x_1437_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1447_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
uint8_t v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1445_; 
v___x_1442_ = 0;
v___x_1443_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1443_, 0, v_a_1429_);
lean_ctor_set(v___x_1443_, 1, v_a_1438_);
lean_ctor_set_uint8(v___x_1443_, sizeof(void*)*2, v___x_1442_);
lean_ctor_set_uint8(v___x_1443_, sizeof(void*)*2 + 1, v___x_1442_);
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 0, v___x_1443_);
v___x_1445_ = v___x_1440_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v___x_1443_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
}
else
{
lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1455_; 
lean_dec(v_a_1429_);
v_a_1448_ = lean_ctor_get(v___x_1437_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1450_ = v___x_1437_;
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_dec(v___x_1437_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1453_; 
if (v_isShared_1451_ == 0)
{
v___x_1453_ = v___x_1450_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_a_1448_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
return v___x_1453_;
}
}
}
}
}
else
{
lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1485_; 
lean_dec_ref(v_e_1417_);
v_a_1478_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1485_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1480_ = v___x_1428_;
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v___x_1428_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1483_; 
if (v_isShared_1481_ == 0)
{
v___x_1483_ = v___x_1480_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_a_1478_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
}
else
{
lean_object* v___x_1486_; lean_object* v___x_1487_; 
lean_dec(v___x_1425_);
lean_dec_ref(v_e_1417_);
v___x_1486_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
v___x_1487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1486_);
return v___x_1487_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___boxed(lean_object* v_e_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_){
_start:
{
lean_object* v_res_1496_; 
v_res_1496_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg(v_e_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_);
lean_dec(v_a_1494_);
lean_dec_ref(v_a_1493_);
lean_dec(v_a_1492_);
lean_dec_ref(v_a_1491_);
lean_dec(v_a_1490_);
lean_dec_ref(v_a_1489_);
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit(lean_object* v_e_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_){
_start:
{
lean_object* v___x_1508_; 
v___x_1508_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg(v_e_1497_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___boxed(lean_object* v_e_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_){
_start:
{
lean_object* v_res_1520_; 
v_res_1520_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit(v_e_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_);
lean_dec(v_a_1518_);
lean_dec_ref(v_a_1517_);
lean_dec(v_a_1516_);
lean_dec_ref(v_a_1515_);
lean_dec(v_a_1514_);
lean_dec_ref(v_a_1513_);
lean_dec(v_a_1512_);
lean_dec_ref(v_a_1511_);
lean_dec(v_a_1510_);
return v_res_1520_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg___closed__1(void){
_start:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1522_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg___closed__0));
v___x_1523_ = l_Lean_stringToMessageData(v___x_1522_);
return v___x_1523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg(lean_object* v_e_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_){
_start:
{
if (lean_obj_tag(v_e_1524_) == 8)
{
lean_object* v_value_1532_; lean_object* v_body_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; uint8_t v___x_1537_; lean_object* v_new_1538_; lean_object* v___x_1539_; 
v_value_1532_ = lean_ctor_get(v_e_1524_, 2);
v_body_1533_ = lean_ctor_get(v_e_1524_, 3);
v___x_1534_ = lean_unsigned_to_nat(1u);
v___x_1535_ = lean_mk_empty_array_with_capacity(v___x_1534_);
lean_inc_ref(v_value_1532_);
v___x_1536_ = lean_array_push(v___x_1535_, v_value_1532_);
v___x_1537_ = 1;
v_new_1538_ = l_Lean_Meta_expandLet(v_body_1533_, v___x_1536_, v___x_1537_);
v___x_1539_ = l_Lean_Meta_Sym_shareCommonInc(v_new_1538_, v_a_1525_, v_a_1526_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_);
if (lean_obj_tag(v___x_1539_) == 0)
{
lean_object* v_a_1540_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1545_; lean_object* v___y_1546_; lean_object* v___y_1547_; lean_object* v_options_1567_; uint8_t v_hasTrace_1568_; 
v_a_1540_ = lean_ctor_get(v___x_1539_, 0);
lean_inc(v_a_1540_);
lean_dec_ref_known(v___x_1539_, 1);
v_options_1567_ = lean_ctor_get(v_a_1529_, 2);
v_hasTrace_1568_ = lean_ctor_get_uint8(v_options_1567_, sizeof(void*)*1);
if (v_hasTrace_1568_ == 0)
{
lean_dec_ref_known(v_e_1524_, 4);
v___y_1542_ = v_a_1525_;
v___y_1543_ = v_a_1526_;
v___y_1544_ = v_a_1527_;
v___y_1545_ = v_a_1528_;
v___y_1546_ = v_a_1529_;
v___y_1547_ = v_a_1530_;
goto v___jp_1541_;
}
else
{
lean_object* v_inheritedTraceOptions_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; uint8_t v___x_1572_; 
v_inheritedTraceOptions_1569_ = lean_ctor_get(v_a_1529_, 13);
v___x_1570_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2));
v___x_1571_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3);
v___x_1572_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1569_, v_options_1567_, v___x_1571_);
if (v___x_1572_ == 0)
{
lean_dec_ref_known(v_e_1524_, 4);
v___y_1542_ = v_a_1525_;
v___y_1543_ = v_a_1526_;
v___y_1544_ = v_a_1527_;
v___y_1545_ = v_a_1528_;
v___y_1546_ = v_a_1529_;
v___y_1547_ = v_a_1530_;
goto v___jp_1541_;
}
else
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___x_1573_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg___closed__1, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg___closed__1);
v___x_1574_ = l_Lean_indentExpr(v_e_1524_);
v___x_1575_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1573_);
lean_ctor_set(v___x_1575_, 1, v___x_1574_);
v___x_1576_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_1577_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1575_);
lean_ctor_set(v___x_1577_, 1, v___x_1576_);
lean_inc(v_a_1540_);
v___x_1578_ = l_Lean_indentExpr(v_a_1540_);
v___x_1579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1577_);
lean_ctor_set(v___x_1579_, 1, v___x_1578_);
v___x_1580_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(v___x_1570_, v___x_1579_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_);
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_dec_ref_known(v___x_1580_, 1);
v___y_1542_ = v_a_1525_;
v___y_1543_ = v_a_1526_;
v___y_1544_ = v_a_1527_;
v___y_1545_ = v_a_1528_;
v___y_1546_ = v_a_1529_;
v___y_1547_ = v_a_1530_;
goto v___jp_1541_;
}
else
{
lean_object* v_a_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1588_; 
lean_dec(v_a_1540_);
v_a_1581_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1588_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1583_ = v___x_1580_;
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_a_1581_);
lean_dec(v___x_1580_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___x_1586_; 
if (v_isShared_1584_ == 0)
{
v___x_1586_ = v___x_1583_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v_a_1581_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
return v___x_1586_;
}
}
}
}
}
v___jp_1541_:
{
lean_object* v___x_1548_; 
lean_inc(v_a_1540_);
v___x_1548_ = l_Lean_Meta_Sym_mkEqRefl(v_a_1540_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v_a_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1558_; 
v_a_1549_ = lean_ctor_get(v___x_1548_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1551_ = v___x_1548_;
v_isShared_1552_ = v_isSharedCheck_1558_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_a_1549_);
lean_dec(v___x_1548_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1558_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
uint8_t v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1556_; 
v___x_1553_ = 0;
v___x_1554_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1554_, 0, v_a_1540_);
lean_ctor_set(v___x_1554_, 1, v_a_1549_);
lean_ctor_set_uint8(v___x_1554_, sizeof(void*)*2, v___x_1553_);
lean_ctor_set_uint8(v___x_1554_, sizeof(void*)*2 + 1, v___x_1553_);
if (v_isShared_1552_ == 0)
{
lean_ctor_set(v___x_1551_, 0, v___x_1554_);
v___x_1556_ = v___x_1551_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v___x_1554_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
return v___x_1556_;
}
}
}
else
{
lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1566_; 
lean_dec(v_a_1540_);
v_a_1559_ = lean_ctor_get(v___x_1548_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1561_ = v___x_1548_;
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v___x_1548_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1564_; 
if (v_isShared_1562_ == 0)
{
v___x_1564_ = v___x_1561_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_a_1559_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
}
}
}
else
{
lean_object* v_a_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1596_; 
lean_dec_ref_known(v_e_1524_, 4);
v_a_1589_ = lean_ctor_get(v___x_1539_, 0);
v_isSharedCheck_1596_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1591_ = v___x_1539_;
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_a_1589_);
lean_dec(v___x_1539_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1594_; 
if (v_isShared_1592_ == 0)
{
v___x_1594_ = v___x_1591_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_a_1589_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
}
else
{
lean_object* v___x_1597_; lean_object* v___x_1598_; 
lean_dec_ref(v_e_1524_);
v___x_1597_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
v___x_1598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1598_, 0, v___x_1597_);
return v___x_1598_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg___boxed(lean_object* v_e_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_){
_start:
{
lean_object* v_res_1607_; 
v_res_1607_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg(v_e_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_);
lean_dec(v_a_1605_);
lean_dec_ref(v_a_1604_);
lean_dec(v_a_1603_);
lean_dec_ref(v_a_1602_);
lean_dec(v_a_1601_);
lean_dec_ref(v_a_1600_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce(lean_object* v_e_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_){
_start:
{
lean_object* v___x_1619_; 
v___x_1619_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg(v_e_1608_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_, v_a_1617_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___boxed(lean_object* v_e_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce(v_e_1620_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_);
lean_dec(v_a_1629_);
lean_dec_ref(v_a_1628_);
lean_dec(v_a_1627_);
lean_dec_ref(v_a_1626_);
lean_dec(v_a_1625_);
lean_dec_ref(v_a_1624_);
lean_dec(v_a_1623_);
lean_dec_ref(v_a_1622_);
lean_dec(v_a_1621_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(lean_object* v_structName_1632_, lean_object* v_idx_1633_, lean_object* v_struct_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_){
_start:
{
lean_object* v___y_1643_; lean_object* v___x_1646_; uint8_t v_debug_1647_; 
v___x_1646_ = lean_st_ref_get(v___y_1636_);
v_debug_1647_ = lean_ctor_get_uint8(v___x_1646_, sizeof(void*)*11);
lean_dec(v___x_1646_);
if (v_debug_1647_ == 0)
{
v___y_1643_ = v___y_1636_;
goto v___jp_1642_;
}
else
{
lean_object* v___x_1648_; 
lean_inc_ref(v_struct_1634_);
v___x_1648_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_struct_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_);
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_dec_ref_known(v___x_1648_, 1);
v___y_1643_ = v___y_1636_;
goto v___jp_1642_;
}
else
{
lean_object* v_a_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1656_; 
lean_dec_ref(v_struct_1634_);
lean_dec(v_idx_1633_);
lean_dec(v_structName_1632_);
v_a_1649_ = lean_ctor_get(v___x_1648_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1651_ = v___x_1648_;
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_dec(v___x_1648_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1654_; 
if (v_isShared_1652_ == 0)
{
v___x_1654_ = v___x_1651_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_a_1649_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
}
v___jp_1642_:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1644_ = l_Lean_Expr_proj___override(v_structName_1632_, v_idx_1633_, v_struct_1634_);
v___x_1645_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1644_, v___y_1643_);
return v___x_1645_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg___boxed(lean_object* v_structName_1657_, lean_object* v_idx_1658_, lean_object* v_struct_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_){
_start:
{
lean_object* v_res_1667_; 
v_res_1667_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_structName_1657_, v_idx_1658_, v_struct_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_);
lean_dec(v___y_1665_);
lean_dec_ref(v___y_1664_);
lean_dec(v___y_1663_);
lean_dec_ref(v___y_1662_);
lean_dec(v___y_1661_);
lean_dec_ref(v___y_1660_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0(lean_object* v_structName_1668_, lean_object* v_idx_1669_, lean_object* v_struct_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_){
_start:
{
lean_object* v___x_1681_; 
v___x_1681_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_structName_1668_, v_idx_1669_, v_struct_1670_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
return v___x_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___boxed(lean_object* v_structName_1682_, lean_object* v_idx_1683_, lean_object* v_struct_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0(v_structName_1682_, v_idx_1683_, v_struct_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
lean_dec(v___y_1685_);
return v_res_1695_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1696_; 
v___x_1696_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM(lean_box(0));
return v___x_1696_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1(lean_object* v_msg_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
lean_object* v___x_1708_; lean_object* v___x_146377__overap_1709_; lean_object* v___x_1710_; 
v___x_1708_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___closed__0);
v___x_146377__overap_1709_ = lean_panic_fn_borrowed(v___x_1708_, v_msg_1697_);
lean_inc(v___y_1706_);
lean_inc_ref(v___y_1705_);
lean_inc(v___y_1704_);
lean_inc_ref(v___y_1703_);
lean_inc(v___y_1702_);
lean_inc_ref(v___y_1701_);
lean_inc(v___y_1700_);
lean_inc_ref(v___y_1699_);
lean_inc(v___y_1698_);
v___x_1710_ = lean_apply_10(v___x_146377__overap_1709_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, lean_box(0));
return v___x_1710_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___boxed(lean_object* v_msg_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
lean_object* v_res_1722_; 
v_res_1722_ = l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1(v_msg_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1713_);
lean_dec(v___y_1712_);
return v_res_1722_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1723_ = lean_unsigned_to_nat(32u);
v___x_1724_ = lean_mk_empty_array_with_capacity(v___x_1723_);
v___x_1725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1725_, 0, v___x_1724_);
return v___x_1725_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; 
v___x_1726_ = ((size_t)5ULL);
v___x_1727_ = lean_unsigned_to_nat(0u);
v___x_1728_ = lean_unsigned_to_nat(32u);
v___x_1729_ = lean_mk_empty_array_with_capacity(v___x_1728_);
v___x_1730_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__0);
v___x_1731_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1731_, 0, v___x_1730_);
lean_ctor_set(v___x_1731_, 1, v___x_1729_);
lean_ctor_set(v___x_1731_, 2, v___x_1727_);
lean_ctor_set(v___x_1731_, 3, v___x_1727_);
lean_ctor_set_usize(v___x_1731_, 4, v___x_1726_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg(lean_object* v___y_1732_){
_start:
{
lean_object* v___x_1734_; lean_object* v_traceState_1735_; lean_object* v_traces_1736_; lean_object* v___x_1737_; lean_object* v_traceState_1738_; lean_object* v_env_1739_; lean_object* v_nextMacroScope_1740_; lean_object* v_ngen_1741_; lean_object* v_auxDeclNGen_1742_; lean_object* v_cache_1743_; lean_object* v_messages_1744_; lean_object* v_infoState_1745_; lean_object* v_snapshotTasks_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1765_; 
v___x_1734_ = lean_st_ref_get(v___y_1732_);
v_traceState_1735_ = lean_ctor_get(v___x_1734_, 4);
lean_inc_ref(v_traceState_1735_);
lean_dec(v___x_1734_);
v_traces_1736_ = lean_ctor_get(v_traceState_1735_, 0);
lean_inc_ref(v_traces_1736_);
lean_dec_ref(v_traceState_1735_);
v___x_1737_ = lean_st_ref_take(v___y_1732_);
v_traceState_1738_ = lean_ctor_get(v___x_1737_, 4);
v_env_1739_ = lean_ctor_get(v___x_1737_, 0);
v_nextMacroScope_1740_ = lean_ctor_get(v___x_1737_, 1);
v_ngen_1741_ = lean_ctor_get(v___x_1737_, 2);
v_auxDeclNGen_1742_ = lean_ctor_get(v___x_1737_, 3);
v_cache_1743_ = lean_ctor_get(v___x_1737_, 5);
v_messages_1744_ = lean_ctor_get(v___x_1737_, 6);
v_infoState_1745_ = lean_ctor_get(v___x_1737_, 7);
v_snapshotTasks_1746_ = lean_ctor_get(v___x_1737_, 8);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1748_ = v___x_1737_;
v_isShared_1749_ = v_isSharedCheck_1765_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_snapshotTasks_1746_);
lean_inc(v_infoState_1745_);
lean_inc(v_messages_1744_);
lean_inc(v_cache_1743_);
lean_inc(v_traceState_1738_);
lean_inc(v_auxDeclNGen_1742_);
lean_inc(v_ngen_1741_);
lean_inc(v_nextMacroScope_1740_);
lean_inc(v_env_1739_);
lean_dec(v___x_1737_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1765_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
uint64_t v_tid_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1763_; 
v_tid_1750_ = lean_ctor_get_uint64(v_traceState_1738_, sizeof(void*)*1);
v_isSharedCheck_1763_ = !lean_is_exclusive(v_traceState_1738_);
if (v_isSharedCheck_1763_ == 0)
{
lean_object* v_unused_1764_; 
v_unused_1764_ = lean_ctor_get(v_traceState_1738_, 0);
lean_dec(v_unused_1764_);
v___x_1752_ = v_traceState_1738_;
v_isShared_1753_ = v_isSharedCheck_1763_;
goto v_resetjp_1751_;
}
else
{
lean_dec(v_traceState_1738_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1763_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1754_; lean_object* v___x_1756_; 
v___x_1754_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1);
if (v_isShared_1753_ == 0)
{
lean_ctor_set(v___x_1752_, 0, v___x_1754_);
v___x_1756_ = v___x_1752_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v___x_1754_);
lean_ctor_set_uint64(v_reuseFailAlloc_1762_, sizeof(void*)*1, v_tid_1750_);
v___x_1756_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
lean_object* v___x_1758_; 
if (v_isShared_1749_ == 0)
{
lean_ctor_set(v___x_1748_, 4, v___x_1756_);
v___x_1758_ = v___x_1748_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v_env_1739_);
lean_ctor_set(v_reuseFailAlloc_1761_, 1, v_nextMacroScope_1740_);
lean_ctor_set(v_reuseFailAlloc_1761_, 2, v_ngen_1741_);
lean_ctor_set(v_reuseFailAlloc_1761_, 3, v_auxDeclNGen_1742_);
lean_ctor_set(v_reuseFailAlloc_1761_, 4, v___x_1756_);
lean_ctor_set(v_reuseFailAlloc_1761_, 5, v_cache_1743_);
lean_ctor_set(v_reuseFailAlloc_1761_, 6, v_messages_1744_);
lean_ctor_set(v_reuseFailAlloc_1761_, 7, v_infoState_1745_);
lean_ctor_set(v_reuseFailAlloc_1761_, 8, v_snapshotTasks_1746_);
v___x_1758_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1759_ = lean_st_ref_set(v___y_1732_, v___x_1758_);
v___x_1760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1760_, 0, v_traces_1736_);
return v___x_1760_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___boxed(lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
lean_object* v_res_1768_; 
v_res_1768_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg(v___y_1766_);
lean_dec(v___y_1766_);
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2(lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_){
_start:
{
lean_object* v___x_1779_; 
v___x_1779_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg(v___y_1777_);
return v___x_1779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___boxed(lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2(v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec(v___y_1784_);
lean_dec_ref(v___y_1783_);
lean_dec(v___y_1782_);
lean_dec_ref(v___y_1781_);
lean_dec(v___y_1780_);
return v_res_1790_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(lean_object* v_opts_1791_, lean_object* v_opt_1792_){
_start:
{
lean_object* v_name_1793_; lean_object* v_defValue_1794_; lean_object* v_map_1795_; lean_object* v___x_1796_; 
v_name_1793_ = lean_ctor_get(v_opt_1792_, 0);
v_defValue_1794_ = lean_ctor_get(v_opt_1792_, 1);
v_map_1795_ = lean_ctor_get(v_opts_1791_, 0);
v___x_1796_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1795_, v_name_1793_);
if (lean_obj_tag(v___x_1796_) == 0)
{
uint8_t v___x_1797_; 
v___x_1797_ = lean_unbox(v_defValue_1794_);
return v___x_1797_;
}
else
{
lean_object* v_val_1798_; 
v_val_1798_ = lean_ctor_get(v___x_1796_, 0);
lean_inc(v_val_1798_);
lean_dec_ref_known(v___x_1796_, 1);
if (lean_obj_tag(v_val_1798_) == 1)
{
uint8_t v_v_1799_; 
v_v_1799_ = lean_ctor_get_uint8(v_val_1798_, 0);
lean_dec_ref_known(v_val_1798_, 0);
return v_v_1799_;
}
else
{
uint8_t v___x_1800_; 
lean_dec(v_val_1798_);
v___x_1800_ = lean_unbox(v_defValue_1794_);
return v___x_1800_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___boxed(lean_object* v_opts_1801_, lean_object* v_opt_1802_){
_start:
{
uint8_t v_res_1803_; lean_object* v_r_1804_; 
v_res_1803_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_1801_, v_opt_1802_);
lean_dec_ref(v_opt_1802_);
lean_dec_ref(v_opts_1801_);
v_r_1804_ = lean_box(v_res_1803_);
return v_r_1804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0(uint8_t v___x_1805_, lean_object* v_e_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_){
_start:
{
lean_object* v___x_1812_; uint8_t v_foApprox_1813_; uint8_t v_ctxApprox_1814_; uint8_t v_quasiPatternApprox_1815_; uint8_t v_constApprox_1816_; uint8_t v_isDefEqStuckEx_1817_; uint8_t v_unificationHints_1818_; uint8_t v_proofIrrelevance_1819_; uint8_t v_assignSyntheticOpaque_1820_; uint8_t v_offsetCnstrs_1821_; uint8_t v_etaStruct_1822_; uint8_t v_univApprox_1823_; uint8_t v_iota_1824_; uint8_t v_beta_1825_; uint8_t v_proj_1826_; uint8_t v_zeta_1827_; uint8_t v_zetaDelta_1828_; uint8_t v_zetaUnused_1829_; uint8_t v_zetaHave_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1869_; 
v___x_1812_ = l_Lean_Meta_Context_config(v___y_1807_);
v_foApprox_1813_ = lean_ctor_get_uint8(v___x_1812_, 0);
v_ctxApprox_1814_ = lean_ctor_get_uint8(v___x_1812_, 1);
v_quasiPatternApprox_1815_ = lean_ctor_get_uint8(v___x_1812_, 2);
v_constApprox_1816_ = lean_ctor_get_uint8(v___x_1812_, 3);
v_isDefEqStuckEx_1817_ = lean_ctor_get_uint8(v___x_1812_, 4);
v_unificationHints_1818_ = lean_ctor_get_uint8(v___x_1812_, 5);
v_proofIrrelevance_1819_ = lean_ctor_get_uint8(v___x_1812_, 6);
v_assignSyntheticOpaque_1820_ = lean_ctor_get_uint8(v___x_1812_, 7);
v_offsetCnstrs_1821_ = lean_ctor_get_uint8(v___x_1812_, 8);
v_etaStruct_1822_ = lean_ctor_get_uint8(v___x_1812_, 10);
v_univApprox_1823_ = lean_ctor_get_uint8(v___x_1812_, 11);
v_iota_1824_ = lean_ctor_get_uint8(v___x_1812_, 12);
v_beta_1825_ = lean_ctor_get_uint8(v___x_1812_, 13);
v_proj_1826_ = lean_ctor_get_uint8(v___x_1812_, 14);
v_zeta_1827_ = lean_ctor_get_uint8(v___x_1812_, 15);
v_zetaDelta_1828_ = lean_ctor_get_uint8(v___x_1812_, 16);
v_zetaUnused_1829_ = lean_ctor_get_uint8(v___x_1812_, 17);
v_zetaHave_1830_ = lean_ctor_get_uint8(v___x_1812_, 18);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1832_ = v___x_1812_;
v_isShared_1833_ = v_isSharedCheck_1869_;
goto v_resetjp_1831_;
}
else
{
lean_dec(v___x_1812_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1869_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
uint8_t v_trackZetaDelta_1834_; lean_object* v_zetaDeltaSet_1835_; lean_object* v_lctx_1836_; lean_object* v_localInstances_1837_; lean_object* v_defEqCtx_x3f_1838_; lean_object* v_synthPendingDepth_1839_; lean_object* v_canUnfold_x3f_1840_; uint8_t v_univApprox_1841_; uint8_t v_inTypeClassResolution_1842_; uint8_t v_cacheInferType_1843_; lean_object* v_config_1845_; 
v_trackZetaDelta_1834_ = lean_ctor_get_uint8(v___y_1807_, sizeof(void*)*7);
v_zetaDeltaSet_1835_ = lean_ctor_get(v___y_1807_, 1);
lean_inc(v_zetaDeltaSet_1835_);
v_lctx_1836_ = lean_ctor_get(v___y_1807_, 2);
lean_inc_ref(v_lctx_1836_);
v_localInstances_1837_ = lean_ctor_get(v___y_1807_, 3);
lean_inc_ref(v_localInstances_1837_);
v_defEqCtx_x3f_1838_ = lean_ctor_get(v___y_1807_, 4);
lean_inc(v_defEqCtx_x3f_1838_);
v_synthPendingDepth_1839_ = lean_ctor_get(v___y_1807_, 5);
lean_inc(v_synthPendingDepth_1839_);
v_canUnfold_x3f_1840_ = lean_ctor_get(v___y_1807_, 6);
lean_inc(v_canUnfold_x3f_1840_);
v_univApprox_1841_ = lean_ctor_get_uint8(v___y_1807_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1842_ = lean_ctor_get_uint8(v___y_1807_, sizeof(void*)*7 + 2);
v_cacheInferType_1843_ = lean_ctor_get_uint8(v___y_1807_, sizeof(void*)*7 + 3);
if (v_isShared_1833_ == 0)
{
v_config_1845_ = v___x_1832_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1868_, 0, v_foApprox_1813_);
lean_ctor_set_uint8(v_reuseFailAlloc_1868_, 1, v_ctxApprox_1814_);
lean_ctor_set_uint8(v_reuseFailAlloc_1868_, 2, v_quasiPatternApprox_1815_);
lean_ctor_set_uint8(v_reuseFailAlloc_1868_, 3, v_constApprox_1816_);
lean_ctor_set_uint8(v_reuseFailAlloc_1868_, 4, v_isDefEqStuckEx_1817_);
lean_ctor_set_uint8(v_reuseFailAlloc_1868_, 5, v_unificationHints_1818_);
lean_ctor_set_uint8(v_reuseFailAlloc_1868_, 6, v_proofIrrelevance_1819_);
lean_ctor_set_uint8(v_reuseFailAlloc_1868_, 7, v_assignSyntheticOpaque_1820_);
lean_ctor_set_uint8(v_reuseFailAlloc_1868_, 8, v_offsetCnstrs_1821_);
lean_ctor_set_uint8(v_reuseFailAlloc_1868_, 10, v_etaStruct_1822_);
lean_ctor_set_uint8(v_reuseFailAlloc_1868_, 11, v_univApprox_1823_);
lean_ctor_set_uint8(v_reuseFailAlloc_1868_, 12, v_iota_1824_);
lean_ctor_set_uint8(v_reuseFailAlloc_1868_, 13, v_beta_1825_);
lean_ctor_set_uint8(v_reuseFailAlloc_1868_, 14, v_proj_1826_);
lean_ctor_set_uint8(v_reuseFailAlloc_1868_, 15, v_zeta_1827_);
lean_ctor_set_uint8(v_reuseFailAlloc_1868_, 16, v_zetaDelta_1828_);
lean_ctor_set_uint8(v_reuseFailAlloc_1868_, 17, v_zetaUnused_1829_);
lean_ctor_set_uint8(v_reuseFailAlloc_1868_, 18, v_zetaHave_1830_);
v_config_1845_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
uint64_t v___x_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1860_; 
lean_ctor_set_uint8(v_config_1845_, 9, v___x_1805_);
v___x_1846_ = l_Lean_Meta_Context_configKey(v___y_1807_);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___y_1807_);
if (v_isSharedCheck_1860_ == 0)
{
lean_object* v_unused_1861_; lean_object* v_unused_1862_; lean_object* v_unused_1863_; lean_object* v_unused_1864_; lean_object* v_unused_1865_; lean_object* v_unused_1866_; lean_object* v_unused_1867_; 
v_unused_1861_ = lean_ctor_get(v___y_1807_, 6);
lean_dec(v_unused_1861_);
v_unused_1862_ = lean_ctor_get(v___y_1807_, 5);
lean_dec(v_unused_1862_);
v_unused_1863_ = lean_ctor_get(v___y_1807_, 4);
lean_dec(v_unused_1863_);
v_unused_1864_ = lean_ctor_get(v___y_1807_, 3);
lean_dec(v_unused_1864_);
v_unused_1865_ = lean_ctor_get(v___y_1807_, 2);
lean_dec(v_unused_1865_);
v_unused_1866_ = lean_ctor_get(v___y_1807_, 1);
lean_dec(v_unused_1866_);
v_unused_1867_ = lean_ctor_get(v___y_1807_, 0);
lean_dec(v_unused_1867_);
v___x_1848_ = v___y_1807_;
v_isShared_1849_ = v_isSharedCheck_1860_;
goto v_resetjp_1847_;
}
else
{
lean_dec(v___y_1807_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1860_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
uint64_t v___x_1850_; uint64_t v___x_1851_; uint64_t v___x_1852_; uint64_t v___x_1853_; uint64_t v_key_1854_; lean_object* v___x_1855_; lean_object* v___x_1857_; 
v___x_1850_ = 3ULL;
v___x_1851_ = lean_uint64_shift_right(v___x_1846_, v___x_1850_);
v___x_1852_ = lean_uint64_shift_left(v___x_1851_, v___x_1850_);
v___x_1853_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_1805_);
v_key_1854_ = lean_uint64_lor(v___x_1852_, v___x_1853_);
v___x_1855_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1855_, 0, v_config_1845_);
lean_ctor_set_uint64(v___x_1855_, sizeof(void*)*1, v_key_1854_);
if (v_isShared_1849_ == 0)
{
lean_ctor_set(v___x_1848_, 0, v___x_1855_);
v___x_1857_ = v___x_1848_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v___x_1855_);
lean_ctor_set(v_reuseFailAlloc_1859_, 1, v_zetaDeltaSet_1835_);
lean_ctor_set(v_reuseFailAlloc_1859_, 2, v_lctx_1836_);
lean_ctor_set(v_reuseFailAlloc_1859_, 3, v_localInstances_1837_);
lean_ctor_set(v_reuseFailAlloc_1859_, 4, v_defEqCtx_x3f_1838_);
lean_ctor_set(v_reuseFailAlloc_1859_, 5, v_synthPendingDepth_1839_);
lean_ctor_set(v_reuseFailAlloc_1859_, 6, v_canUnfold_x3f_1840_);
lean_ctor_set_uint8(v_reuseFailAlloc_1859_, sizeof(void*)*7, v_trackZetaDelta_1834_);
lean_ctor_set_uint8(v_reuseFailAlloc_1859_, sizeof(void*)*7 + 1, v_univApprox_1841_);
lean_ctor_set_uint8(v_reuseFailAlloc_1859_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1842_);
lean_ctor_set_uint8(v_reuseFailAlloc_1859_, sizeof(void*)*7 + 3, v_cacheInferType_1843_);
v___x_1857_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
lean_object* v___x_1858_; 
v___x_1858_ = l_Lean_Meta_reduceProj_x3f(v_e_1806_, v___x_1857_, v___y_1808_, v___y_1809_, v___y_1810_);
lean_dec_ref(v___x_1857_);
return v___x_1858_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___boxed(lean_object* v___x_1870_, lean_object* v_e_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_){
_start:
{
uint8_t v___x_162644__boxed_1877_; lean_object* v_res_1878_; 
v___x_162644__boxed_1877_ = lean_unbox(v___x_1870_);
v_res_1878_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0(v___x_162644__boxed_1877_, v_e_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_);
lean_dec(v___y_1875_);
lean_dec_ref(v___y_1874_);
lean_dec(v___y_1873_);
return v_res_1878_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1880_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__0));
v___x_1881_ = l_Lean_stringToMessageData(v___x_1880_);
return v___x_1881_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___x_1883_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__2));
v___x_1884_ = l_Lean_stringToMessageData(v___x_1883_);
return v___x_1884_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__5(void){
_start:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1886_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__4));
v___x_1887_ = l_Lean_stringToMessageData(v___x_1886_);
return v___x_1887_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__7(void){
_start:
{
lean_object* v___x_1889_; lean_object* v___x_1890_; 
v___x_1889_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__6));
v___x_1890_ = l_Lean_stringToMessageData(v___x_1889_);
return v___x_1890_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__9(void){
_start:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1892_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__8));
v___x_1893_ = l_Lean_stringToMessageData(v___x_1892_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2(lean_object* v_typeName_1894_, lean_object* v_idx_1895_, lean_object* v_e_1896_, lean_object* v_x_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_){
_start:
{
if (lean_obj_tag(v_x_1897_) == 0)
{
lean_object* v_a_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1928_; 
lean_dec_ref(v_e_1896_);
v_a_1908_ = lean_ctor_get(v_x_1897_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v_x_1897_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1910_ = v_x_1897_;
v_isShared_1911_ = v_isSharedCheck_1928_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_a_1908_);
lean_dec(v_x_1897_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1928_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1919_; 
v___x_1912_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__1, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__1);
v___x_1913_ = l_Lean_MessageData_ofName(v_typeName_1894_);
v___x_1914_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1912_);
lean_ctor_set(v___x_1914_, 1, v___x_1913_);
v___x_1915_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_1916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1914_);
lean_ctor_set(v___x_1916_, 1, v___x_1915_);
v___x_1917_ = l_Nat_reprFast(v_idx_1895_);
if (v_isShared_1911_ == 0)
{
lean_ctor_set_tag(v___x_1910_, 3);
lean_ctor_set(v___x_1910_, 0, v___x_1917_);
v___x_1919_ = v___x_1910_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v___x_1917_);
v___x_1919_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1920_ = l_Lean_MessageData_ofFormat(v___x_1919_);
v___x_1921_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1916_);
lean_ctor_set(v___x_1921_, 1, v___x_1920_);
v___x_1922_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__3, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__3_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__3);
v___x_1923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1921_);
lean_ctor_set(v___x_1923_, 1, v___x_1922_);
v___x_1924_ = l_Lean_Exception_toMessageData(v_a_1908_);
v___x_1925_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1923_);
lean_ctor_set(v___x_1925_, 1, v___x_1924_);
v___x_1926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1925_);
return v___x_1926_;
}
}
}
else
{
lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1985_; 
v_a_1929_ = lean_ctor_get(v_x_1897_, 0);
v_isSharedCheck_1985_ = !lean_is_exclusive(v_x_1897_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1931_ = v_x_1897_;
v_isShared_1932_ = v_isSharedCheck_1985_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v_x_1897_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1985_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
if (lean_obj_tag(v_a_1929_) == 0)
{
uint8_t v_done_1933_; 
v_done_1933_ = lean_ctor_get_uint8(v_a_1929_, 0);
lean_dec_ref_known(v_a_1929_, 0);
if (v_done_1933_ == 1)
{
lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1941_; 
v___x_1934_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__1, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__1);
v___x_1935_ = l_Lean_MessageData_ofName(v_typeName_1894_);
v___x_1936_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1936_, 0, v___x_1934_);
lean_ctor_set(v___x_1936_, 1, v___x_1935_);
v___x_1937_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_1938_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1936_);
lean_ctor_set(v___x_1938_, 1, v___x_1937_);
v___x_1939_ = l_Nat_reprFast(v_idx_1895_);
if (v_isShared_1932_ == 0)
{
lean_ctor_set_tag(v___x_1931_, 3);
lean_ctor_set(v___x_1931_, 0, v___x_1939_);
v___x_1941_ = v___x_1931_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v___x_1939_);
v___x_1941_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; 
v___x_1942_ = l_Lean_MessageData_ofFormat(v___x_1941_);
v___x_1943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1943_, 0, v___x_1938_);
lean_ctor_set(v___x_1943_, 1, v___x_1942_);
v___x_1944_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__5, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__5_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__5);
v___x_1945_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1943_);
lean_ctor_set(v___x_1945_, 1, v___x_1944_);
v___x_1946_ = l_Lean_indentExpr(v_e_1896_);
v___x_1947_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1945_);
lean_ctor_set(v___x_1947_, 1, v___x_1946_);
v___x_1948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1948_, 0, v___x_1947_);
return v___x_1948_;
}
}
else
{
lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1957_; 
lean_dec_ref(v_e_1896_);
v___x_1950_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__1, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__1);
v___x_1951_ = l_Lean_MessageData_ofName(v_typeName_1894_);
v___x_1952_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1950_);
lean_ctor_set(v___x_1952_, 1, v___x_1951_);
v___x_1953_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_1954_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1954_, 0, v___x_1952_);
lean_ctor_set(v___x_1954_, 1, v___x_1953_);
v___x_1955_ = l_Nat_reprFast(v_idx_1895_);
if (v_isShared_1932_ == 0)
{
lean_ctor_set_tag(v___x_1931_, 3);
lean_ctor_set(v___x_1931_, 0, v___x_1955_);
v___x_1957_ = v___x_1931_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v___x_1955_);
v___x_1957_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; 
v___x_1958_ = l_Lean_MessageData_ofFormat(v___x_1957_);
v___x_1959_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1959_, 0, v___x_1954_);
lean_ctor_set(v___x_1959_, 1, v___x_1958_);
v___x_1960_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__7, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__7_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__7);
v___x_1961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1961_, 0, v___x_1959_);
lean_ctor_set(v___x_1961_, 1, v___x_1960_);
v___x_1962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1961_);
return v___x_1962_;
}
}
}
else
{
lean_object* v_e_x27_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1972_; 
v_e_x27_1964_ = lean_ctor_get(v_a_1929_, 0);
lean_inc_ref(v_e_x27_1964_);
lean_dec_ref_known(v_a_1929_, 2);
v___x_1965_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__1, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__1);
v___x_1966_ = l_Lean_MessageData_ofName(v_typeName_1894_);
v___x_1967_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1967_, 0, v___x_1965_);
lean_ctor_set(v___x_1967_, 1, v___x_1966_);
v___x_1968_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_1969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1969_, 0, v___x_1967_);
lean_ctor_set(v___x_1969_, 1, v___x_1968_);
v___x_1970_ = l_Nat_reprFast(v_idx_1895_);
if (v_isShared_1932_ == 0)
{
lean_ctor_set_tag(v___x_1931_, 3);
lean_ctor_set(v___x_1931_, 0, v___x_1970_);
v___x_1972_ = v___x_1931_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v___x_1970_);
v___x_1972_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; 
v___x_1973_ = l_Lean_MessageData_ofFormat(v___x_1972_);
v___x_1974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1974_, 0, v___x_1969_);
lean_ctor_set(v___x_1974_, 1, v___x_1973_);
v___x_1975_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__9, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__9_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__9);
v___x_1976_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1976_, 0, v___x_1974_);
lean_ctor_set(v___x_1976_, 1, v___x_1975_);
v___x_1977_ = l_Lean_indentExpr(v_e_1896_);
v___x_1978_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1976_);
lean_ctor_set(v___x_1978_, 1, v___x_1977_);
v___x_1979_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_1980_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1980_, 0, v___x_1978_);
lean_ctor_set(v___x_1980_, 1, v___x_1979_);
v___x_1981_ = l_Lean_indentExpr(v_e_x27_1964_);
v___x_1982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1980_);
lean_ctor_set(v___x_1982_, 1, v___x_1981_);
v___x_1983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1983_, 0, v___x_1982_);
return v___x_1983_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___boxed(lean_object* v_typeName_1986_, lean_object* v_idx_1987_, lean_object* v_e_1988_, lean_object* v_x_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_){
_start:
{
lean_object* v_res_2000_; 
v_res_2000_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2(v_typeName_1986_, v_idx_1987_, v_e_1988_, v_x_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_);
lean_dec(v___y_1998_);
lean_dec_ref(v___y_1997_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
lean_dec(v___y_1990_);
return v_res_2000_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5___redArg(lean_object* v_x_2001_){
_start:
{
if (lean_obj_tag(v_x_2001_) == 0)
{
lean_object* v_a_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2010_; 
v_a_2003_ = lean_ctor_get(v_x_2001_, 0);
v_isSharedCheck_2010_ = !lean_is_exclusive(v_x_2001_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_2005_ = v_x_2001_;
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_a_2003_);
lean_dec(v_x_2001_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___x_2008_; 
if (v_isShared_2006_ == 0)
{
lean_ctor_set_tag(v___x_2005_, 1);
v___x_2008_ = v___x_2005_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_a_2003_);
v___x_2008_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
return v___x_2008_;
}
}
}
else
{
lean_object* v_a_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2018_; 
v_a_2011_ = lean_ctor_get(v_x_2001_, 0);
v_isSharedCheck_2018_ = !lean_is_exclusive(v_x_2001_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_2013_ = v_x_2001_;
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_a_2011_);
lean_dec(v_x_2001_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2016_; 
if (v_isShared_2014_ == 0)
{
lean_ctor_set_tag(v___x_2013_, 0);
v___x_2016_ = v___x_2013_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_a_2011_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
return v___x_2016_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5___redArg___boxed(lean_object* v_x_2019_, lean_object* v___y_2020_){
_start:
{
lean_object* v_res_2021_; 
v_res_2021_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5___redArg(v_x_2019_);
return v_res_2021_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4_spec__5(size_t v_sz_2022_, size_t v_i_2023_, lean_object* v_bs_2024_){
_start:
{
uint8_t v___x_2025_; 
v___x_2025_ = lean_usize_dec_lt(v_i_2023_, v_sz_2022_);
if (v___x_2025_ == 0)
{
return v_bs_2024_;
}
else
{
lean_object* v_v_2026_; lean_object* v_msg_2027_; lean_object* v___x_2028_; lean_object* v_bs_x27_2029_; size_t v___x_2030_; size_t v___x_2031_; lean_object* v___x_2032_; 
v_v_2026_ = lean_array_uget_borrowed(v_bs_2024_, v_i_2023_);
v_msg_2027_ = lean_ctor_get(v_v_2026_, 1);
lean_inc_ref(v_msg_2027_);
v___x_2028_ = lean_unsigned_to_nat(0u);
v_bs_x27_2029_ = lean_array_uset(v_bs_2024_, v_i_2023_, v___x_2028_);
v___x_2030_ = ((size_t)1ULL);
v___x_2031_ = lean_usize_add(v_i_2023_, v___x_2030_);
v___x_2032_ = lean_array_uset(v_bs_x27_2029_, v_i_2023_, v_msg_2027_);
v_i_2023_ = v___x_2031_;
v_bs_2024_ = v___x_2032_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4_spec__5___boxed(lean_object* v_sz_2034_, lean_object* v_i_2035_, lean_object* v_bs_2036_){
_start:
{
size_t v_sz_boxed_2037_; size_t v_i_boxed_2038_; lean_object* v_res_2039_; 
v_sz_boxed_2037_ = lean_unbox_usize(v_sz_2034_);
lean_dec(v_sz_2034_);
v_i_boxed_2038_ = lean_unbox_usize(v_i_2035_);
lean_dec(v_i_2035_);
v_res_2039_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4_spec__5(v_sz_boxed_2037_, v_i_boxed_2038_, v_bs_2036_);
return v_res_2039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4___redArg(lean_object* v_oldTraces_2040_, lean_object* v_data_2041_, lean_object* v_ref_2042_, lean_object* v_msg_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_){
_start:
{
lean_object* v_fileName_2049_; lean_object* v_fileMap_2050_; lean_object* v_options_2051_; lean_object* v_currRecDepth_2052_; lean_object* v_maxRecDepth_2053_; lean_object* v_ref_2054_; lean_object* v_currNamespace_2055_; lean_object* v_openDecls_2056_; lean_object* v_initHeartbeats_2057_; lean_object* v_maxHeartbeats_2058_; lean_object* v_quotContext_2059_; lean_object* v_currMacroScope_2060_; uint8_t v_diag_2061_; lean_object* v_cancelTk_x3f_2062_; uint8_t v_suppressElabErrors_2063_; lean_object* v_inheritedTraceOptions_2064_; lean_object* v___x_2065_; lean_object* v_traceState_2066_; lean_object* v_traces_2067_; lean_object* v_ref_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; size_t v_sz_2071_; size_t v___x_2072_; lean_object* v___x_2073_; lean_object* v_msg_2074_; lean_object* v___x_2075_; lean_object* v_a_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2113_; 
v_fileName_2049_ = lean_ctor_get(v___y_2046_, 0);
v_fileMap_2050_ = lean_ctor_get(v___y_2046_, 1);
v_options_2051_ = lean_ctor_get(v___y_2046_, 2);
v_currRecDepth_2052_ = lean_ctor_get(v___y_2046_, 3);
v_maxRecDepth_2053_ = lean_ctor_get(v___y_2046_, 4);
v_ref_2054_ = lean_ctor_get(v___y_2046_, 5);
v_currNamespace_2055_ = lean_ctor_get(v___y_2046_, 6);
v_openDecls_2056_ = lean_ctor_get(v___y_2046_, 7);
v_initHeartbeats_2057_ = lean_ctor_get(v___y_2046_, 8);
v_maxHeartbeats_2058_ = lean_ctor_get(v___y_2046_, 9);
v_quotContext_2059_ = lean_ctor_get(v___y_2046_, 10);
v_currMacroScope_2060_ = lean_ctor_get(v___y_2046_, 11);
v_diag_2061_ = lean_ctor_get_uint8(v___y_2046_, sizeof(void*)*14);
v_cancelTk_x3f_2062_ = lean_ctor_get(v___y_2046_, 12);
v_suppressElabErrors_2063_ = lean_ctor_get_uint8(v___y_2046_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2064_ = lean_ctor_get(v___y_2046_, 13);
v___x_2065_ = lean_st_ref_get(v___y_2047_);
v_traceState_2066_ = lean_ctor_get(v___x_2065_, 4);
lean_inc_ref(v_traceState_2066_);
lean_dec(v___x_2065_);
v_traces_2067_ = lean_ctor_get(v_traceState_2066_, 0);
lean_inc_ref(v_traces_2067_);
lean_dec_ref(v_traceState_2066_);
v_ref_2068_ = l_Lean_replaceRef(v_ref_2042_, v_ref_2054_);
lean_inc_ref(v_inheritedTraceOptions_2064_);
lean_inc(v_cancelTk_x3f_2062_);
lean_inc(v_currMacroScope_2060_);
lean_inc(v_quotContext_2059_);
lean_inc(v_maxHeartbeats_2058_);
lean_inc(v_initHeartbeats_2057_);
lean_inc(v_openDecls_2056_);
lean_inc(v_currNamespace_2055_);
lean_inc(v_maxRecDepth_2053_);
lean_inc(v_currRecDepth_2052_);
lean_inc_ref(v_options_2051_);
lean_inc_ref(v_fileMap_2050_);
lean_inc_ref(v_fileName_2049_);
v___x_2069_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2069_, 0, v_fileName_2049_);
lean_ctor_set(v___x_2069_, 1, v_fileMap_2050_);
lean_ctor_set(v___x_2069_, 2, v_options_2051_);
lean_ctor_set(v___x_2069_, 3, v_currRecDepth_2052_);
lean_ctor_set(v___x_2069_, 4, v_maxRecDepth_2053_);
lean_ctor_set(v___x_2069_, 5, v_ref_2068_);
lean_ctor_set(v___x_2069_, 6, v_currNamespace_2055_);
lean_ctor_set(v___x_2069_, 7, v_openDecls_2056_);
lean_ctor_set(v___x_2069_, 8, v_initHeartbeats_2057_);
lean_ctor_set(v___x_2069_, 9, v_maxHeartbeats_2058_);
lean_ctor_set(v___x_2069_, 10, v_quotContext_2059_);
lean_ctor_set(v___x_2069_, 11, v_currMacroScope_2060_);
lean_ctor_set(v___x_2069_, 12, v_cancelTk_x3f_2062_);
lean_ctor_set(v___x_2069_, 13, v_inheritedTraceOptions_2064_);
lean_ctor_set_uint8(v___x_2069_, sizeof(void*)*14, v_diag_2061_);
lean_ctor_set_uint8(v___x_2069_, sizeof(void*)*14 + 1, v_suppressElabErrors_2063_);
v___x_2070_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2067_);
lean_dec_ref(v_traces_2067_);
v_sz_2071_ = lean_array_size(v___x_2070_);
v___x_2072_ = ((size_t)0ULL);
v___x_2073_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4_spec__5(v_sz_2071_, v___x_2072_, v___x_2070_);
v_msg_2074_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2074_, 0, v_data_2041_);
lean_ctor_set(v_msg_2074_, 1, v_msg_2043_);
lean_ctor_set(v_msg_2074_, 2, v___x_2073_);
v___x_2075_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0_spec__0(v_msg_2074_, v___y_2044_, v___y_2045_, v___x_2069_, v___y_2047_);
lean_dec_ref_known(v___x_2069_, 14);
v_a_2076_ = lean_ctor_get(v___x_2075_, 0);
v_isSharedCheck_2113_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2078_ = v___x_2075_;
v_isShared_2079_ = v_isSharedCheck_2113_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_a_2076_);
lean_dec(v___x_2075_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2113_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2080_; lean_object* v_traceState_2081_; lean_object* v_env_2082_; lean_object* v_nextMacroScope_2083_; lean_object* v_ngen_2084_; lean_object* v_auxDeclNGen_2085_; lean_object* v_cache_2086_; lean_object* v_messages_2087_; lean_object* v_infoState_2088_; lean_object* v_snapshotTasks_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2112_; 
v___x_2080_ = lean_st_ref_take(v___y_2047_);
v_traceState_2081_ = lean_ctor_get(v___x_2080_, 4);
v_env_2082_ = lean_ctor_get(v___x_2080_, 0);
v_nextMacroScope_2083_ = lean_ctor_get(v___x_2080_, 1);
v_ngen_2084_ = lean_ctor_get(v___x_2080_, 2);
v_auxDeclNGen_2085_ = lean_ctor_get(v___x_2080_, 3);
v_cache_2086_ = lean_ctor_get(v___x_2080_, 5);
v_messages_2087_ = lean_ctor_get(v___x_2080_, 6);
v_infoState_2088_ = lean_ctor_get(v___x_2080_, 7);
v_snapshotTasks_2089_ = lean_ctor_get(v___x_2080_, 8);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2080_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2091_ = v___x_2080_;
v_isShared_2092_ = v_isSharedCheck_2112_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_snapshotTasks_2089_);
lean_inc(v_infoState_2088_);
lean_inc(v_messages_2087_);
lean_inc(v_cache_2086_);
lean_inc(v_traceState_2081_);
lean_inc(v_auxDeclNGen_2085_);
lean_inc(v_ngen_2084_);
lean_inc(v_nextMacroScope_2083_);
lean_inc(v_env_2082_);
lean_dec(v___x_2080_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2112_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
uint64_t v_tid_2093_; lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2110_; 
v_tid_2093_ = lean_ctor_get_uint64(v_traceState_2081_, sizeof(void*)*1);
v_isSharedCheck_2110_ = !lean_is_exclusive(v_traceState_2081_);
if (v_isSharedCheck_2110_ == 0)
{
lean_object* v_unused_2111_; 
v_unused_2111_ = lean_ctor_get(v_traceState_2081_, 0);
lean_dec(v_unused_2111_);
v___x_2095_ = v_traceState_2081_;
v_isShared_2096_ = v_isSharedCheck_2110_;
goto v_resetjp_2094_;
}
else
{
lean_dec(v_traceState_2081_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2110_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2100_; 
v___x_2097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2097_, 0, v_ref_2042_);
lean_ctor_set(v___x_2097_, 1, v_a_2076_);
v___x_2098_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2040_, v___x_2097_);
if (v_isShared_2096_ == 0)
{
lean_ctor_set(v___x_2095_, 0, v___x_2098_);
v___x_2100_ = v___x_2095_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v___x_2098_);
lean_ctor_set_uint64(v_reuseFailAlloc_2109_, sizeof(void*)*1, v_tid_2093_);
v___x_2100_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
lean_object* v___x_2102_; 
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 4, v___x_2100_);
v___x_2102_ = v___x_2091_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_env_2082_);
lean_ctor_set(v_reuseFailAlloc_2108_, 1, v_nextMacroScope_2083_);
lean_ctor_set(v_reuseFailAlloc_2108_, 2, v_ngen_2084_);
lean_ctor_set(v_reuseFailAlloc_2108_, 3, v_auxDeclNGen_2085_);
lean_ctor_set(v_reuseFailAlloc_2108_, 4, v___x_2100_);
lean_ctor_set(v_reuseFailAlloc_2108_, 5, v_cache_2086_);
lean_ctor_set(v_reuseFailAlloc_2108_, 6, v_messages_2087_);
lean_ctor_set(v_reuseFailAlloc_2108_, 7, v_infoState_2088_);
lean_ctor_set(v_reuseFailAlloc_2108_, 8, v_snapshotTasks_2089_);
v___x_2102_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2106_; 
v___x_2103_ = lean_st_ref_set(v___y_2047_, v___x_2102_);
v___x_2104_ = lean_box(0);
if (v_isShared_2079_ == 0)
{
lean_ctor_set(v___x_2078_, 0, v___x_2104_);
v___x_2106_ = v___x_2078_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v___x_2104_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
return v___x_2106_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4___redArg___boxed(lean_object* v_oldTraces_2114_, lean_object* v_data_2115_, lean_object* v_ref_2116_, lean_object* v_msg_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_){
_start:
{
lean_object* v_res_2123_; 
v_res_2123_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4___redArg(v_oldTraces_2114_, v_data_2115_, v_ref_2116_, v_msg_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
lean_dec(v___y_2121_);
lean_dec_ref(v___y_2120_);
lean_dec(v___y_2119_);
lean_dec_ref(v___y_2118_);
return v_res_2123_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__6(lean_object* v_e_2124_){
_start:
{
if (lean_obj_tag(v_e_2124_) == 0)
{
uint8_t v___x_2125_; 
v___x_2125_ = 2;
return v___x_2125_;
}
else
{
uint8_t v___x_2126_; 
v___x_2126_ = 0;
return v___x_2126_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__6___boxed(lean_object* v_e_2127_){
_start:
{
uint8_t v_res_2128_; lean_object* v_r_2129_; 
v_res_2128_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__6(v_e_2127_);
lean_dec_ref(v_e_2127_);
v_r_2129_ = lean_box(v_res_2128_);
return v_r_2129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(lean_object* v_opts_2130_, lean_object* v_opt_2131_){
_start:
{
lean_object* v_name_2132_; lean_object* v_defValue_2133_; lean_object* v_map_2134_; lean_object* v___x_2135_; 
v_name_2132_ = lean_ctor_get(v_opt_2131_, 0);
v_defValue_2133_ = lean_ctor_get(v_opt_2131_, 1);
v_map_2134_ = lean_ctor_get(v_opts_2130_, 0);
v___x_2135_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2134_, v_name_2132_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_inc(v_defValue_2133_);
return v_defValue_2133_;
}
else
{
lean_object* v_val_2136_; 
v_val_2136_ = lean_ctor_get(v___x_2135_, 0);
lean_inc(v_val_2136_);
lean_dec_ref_known(v___x_2135_, 1);
if (lean_obj_tag(v_val_2136_) == 3)
{
lean_object* v_v_2137_; 
v_v_2137_ = lean_ctor_get(v_val_2136_, 0);
lean_inc(v_v_2137_);
lean_dec_ref_known(v_val_2136_, 1);
return v_v_2137_;
}
else
{
lean_dec(v_val_2136_);
lean_inc(v_defValue_2133_);
return v_defValue_2133_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7___boxed(lean_object* v_opts_2138_, lean_object* v_opt_2139_){
_start:
{
lean_object* v_res_2140_; 
v_res_2140_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_2138_, v_opt_2139_);
lean_dec_ref(v_opt_2139_);
lean_dec_ref(v_opts_2138_);
return v_res_2140_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1(void){
_start:
{
lean_object* v___x_2142_; lean_object* v___x_2143_; 
v___x_2142_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__0));
v___x_2143_ = l_Lean_stringToMessageData(v___x_2142_);
return v___x_2143_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2(void){
_start:
{
lean_object* v___x_2144_; double v___x_2145_; 
v___x_2144_ = lean_unsigned_to_nat(1000u);
v___x_2145_ = lean_float_of_nat(v___x_2144_);
return v___x_2145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4(lean_object* v_cls_2146_, uint8_t v_collapsed_2147_, lean_object* v_tag_2148_, lean_object* v_opts_2149_, uint8_t v_clsEnabled_2150_, lean_object* v_oldTraces_2151_, lean_object* v_msg_2152_, lean_object* v_resStartStop_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_){
_start:
{
lean_object* v_fst_2164_; lean_object* v_snd_2165_; lean_object* v___y_2167_; lean_object* v___y_2168_; lean_object* v_data_2169_; lean_object* v_fst_2180_; lean_object* v_snd_2181_; lean_object* v___x_2182_; uint8_t v___x_2183_; lean_object* v___y_2185_; lean_object* v_a_2186_; uint8_t v___y_2201_; double v___y_2232_; 
v_fst_2164_ = lean_ctor_get(v_resStartStop_2153_, 0);
lean_inc(v_fst_2164_);
v_snd_2165_ = lean_ctor_get(v_resStartStop_2153_, 1);
lean_inc(v_snd_2165_);
lean_dec_ref(v_resStartStop_2153_);
v_fst_2180_ = lean_ctor_get(v_snd_2165_, 0);
lean_inc(v_fst_2180_);
v_snd_2181_ = lean_ctor_get(v_snd_2165_, 1);
lean_inc(v_snd_2181_);
lean_dec(v_snd_2165_);
v___x_2182_ = l_Lean_trace_profiler;
v___x_2183_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_2149_, v___x_2182_);
if (v___x_2183_ == 0)
{
v___y_2201_ = v___x_2183_;
goto v___jp_2200_;
}
else
{
lean_object* v___x_2237_; uint8_t v___x_2238_; 
v___x_2237_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2238_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_2149_, v___x_2237_);
if (v___x_2238_ == 0)
{
lean_object* v___x_2239_; lean_object* v___x_2240_; double v___x_2241_; double v___x_2242_; double v___x_2243_; 
v___x_2239_ = l_Lean_trace_profiler_threshold;
v___x_2240_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_2149_, v___x_2239_);
v___x_2241_ = lean_float_of_nat(v___x_2240_);
v___x_2242_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2);
v___x_2243_ = lean_float_div(v___x_2241_, v___x_2242_);
v___y_2232_ = v___x_2243_;
goto v___jp_2231_;
}
else
{
lean_object* v___x_2244_; lean_object* v___x_2245_; double v___x_2246_; 
v___x_2244_ = l_Lean_trace_profiler_threshold;
v___x_2245_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_2149_, v___x_2244_);
v___x_2246_ = lean_float_of_nat(v___x_2245_);
v___y_2232_ = v___x_2246_;
goto v___jp_2231_;
}
}
v___jp_2166_:
{
lean_object* v___x_2170_; 
lean_inc(v___y_2168_);
v___x_2170_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4___redArg(v_oldTraces_2151_, v_data_2169_, v___y_2168_, v___y_2167_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_object* v___x_2171_; 
lean_dec_ref_known(v___x_2170_, 1);
v___x_2171_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5___redArg(v_fst_2164_);
return v___x_2171_;
}
else
{
lean_object* v_a_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2179_; 
lean_dec(v_fst_2164_);
v_a_2172_ = lean_ctor_get(v___x_2170_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2174_ = v___x_2170_;
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_a_2172_);
lean_dec(v___x_2170_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2177_; 
if (v_isShared_2175_ == 0)
{
v___x_2177_ = v___x_2174_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_a_2172_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
}
}
v___jp_2184_:
{
uint8_t v_result_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; double v___x_2190_; lean_object* v_data_2191_; 
v_result_2187_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__6(v_fst_2164_);
v___x_2188_ = lean_box(v_result_2187_);
v___x_2189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2189_, 0, v___x_2188_);
v___x_2190_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_2148_);
lean_inc_ref(v___x_2189_);
lean_inc(v_cls_2146_);
v_data_2191_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2191_, 0, v_cls_2146_);
lean_ctor_set(v_data_2191_, 1, v___x_2189_);
lean_ctor_set(v_data_2191_, 2, v_tag_2148_);
lean_ctor_set_float(v_data_2191_, sizeof(void*)*3, v___x_2190_);
lean_ctor_set_float(v_data_2191_, sizeof(void*)*3 + 8, v___x_2190_);
lean_ctor_set_uint8(v_data_2191_, sizeof(void*)*3 + 16, v_collapsed_2147_);
if (v___x_2183_ == 0)
{
lean_dec_ref_known(v___x_2189_, 1);
lean_dec(v_snd_2181_);
lean_dec(v_fst_2180_);
lean_dec_ref(v_tag_2148_);
lean_dec(v_cls_2146_);
v___y_2167_ = v_a_2186_;
v___y_2168_ = v___y_2185_;
v_data_2169_ = v_data_2191_;
goto v___jp_2166_;
}
else
{
lean_object* v_data_2192_; double v___x_2193_; double v___x_2194_; 
lean_dec_ref_known(v_data_2191_, 3);
v_data_2192_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2192_, 0, v_cls_2146_);
lean_ctor_set(v_data_2192_, 1, v___x_2189_);
lean_ctor_set(v_data_2192_, 2, v_tag_2148_);
v___x_2193_ = lean_unbox_float(v_fst_2180_);
lean_dec(v_fst_2180_);
lean_ctor_set_float(v_data_2192_, sizeof(void*)*3, v___x_2193_);
v___x_2194_ = lean_unbox_float(v_snd_2181_);
lean_dec(v_snd_2181_);
lean_ctor_set_float(v_data_2192_, sizeof(void*)*3 + 8, v___x_2194_);
lean_ctor_set_uint8(v_data_2192_, sizeof(void*)*3 + 16, v_collapsed_2147_);
v___y_2167_ = v_a_2186_;
v___y_2168_ = v___y_2185_;
v_data_2169_ = v_data_2192_;
goto v___jp_2166_;
}
}
v___jp_2195_:
{
lean_object* v_ref_2196_; lean_object* v___x_2197_; 
v_ref_2196_ = lean_ctor_get(v___y_2161_, 5);
lean_inc(v___y_2162_);
lean_inc_ref(v___y_2161_);
lean_inc(v___y_2160_);
lean_inc_ref(v___y_2159_);
lean_inc(v___y_2158_);
lean_inc_ref(v___y_2157_);
lean_inc(v___y_2156_);
lean_inc_ref(v___y_2155_);
lean_inc(v___y_2154_);
lean_inc(v_fst_2164_);
v___x_2197_ = lean_apply_11(v_msg_2152_, v_fst_2164_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, lean_box(0));
if (lean_obj_tag(v___x_2197_) == 0)
{
lean_object* v_a_2198_; 
v_a_2198_ = lean_ctor_get(v___x_2197_, 0);
lean_inc(v_a_2198_);
lean_dec_ref_known(v___x_2197_, 1);
v___y_2185_ = v_ref_2196_;
v_a_2186_ = v_a_2198_;
goto v___jp_2184_;
}
else
{
lean_object* v___x_2199_; 
lean_dec_ref_known(v___x_2197_, 1);
v___x_2199_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1);
v___y_2185_ = v_ref_2196_;
v_a_2186_ = v___x_2199_;
goto v___jp_2184_;
}
}
v___jp_2200_:
{
if (v_clsEnabled_2150_ == 0)
{
if (v___y_2201_ == 0)
{
lean_object* v___x_2202_; lean_object* v_traceState_2203_; lean_object* v_env_2204_; lean_object* v_nextMacroScope_2205_; lean_object* v_ngen_2206_; lean_object* v_auxDeclNGen_2207_; lean_object* v_cache_2208_; lean_object* v_messages_2209_; lean_object* v_infoState_2210_; lean_object* v_snapshotTasks_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2230_; 
lean_dec(v_snd_2181_);
lean_dec(v_fst_2180_);
lean_dec_ref(v_msg_2152_);
lean_dec_ref(v_tag_2148_);
lean_dec(v_cls_2146_);
v___x_2202_ = lean_st_ref_take(v___y_2162_);
v_traceState_2203_ = lean_ctor_get(v___x_2202_, 4);
v_env_2204_ = lean_ctor_get(v___x_2202_, 0);
v_nextMacroScope_2205_ = lean_ctor_get(v___x_2202_, 1);
v_ngen_2206_ = lean_ctor_get(v___x_2202_, 2);
v_auxDeclNGen_2207_ = lean_ctor_get(v___x_2202_, 3);
v_cache_2208_ = lean_ctor_get(v___x_2202_, 5);
v_messages_2209_ = lean_ctor_get(v___x_2202_, 6);
v_infoState_2210_ = lean_ctor_get(v___x_2202_, 7);
v_snapshotTasks_2211_ = lean_ctor_get(v___x_2202_, 8);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2213_ = v___x_2202_;
v_isShared_2214_ = v_isSharedCheck_2230_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_snapshotTasks_2211_);
lean_inc(v_infoState_2210_);
lean_inc(v_messages_2209_);
lean_inc(v_cache_2208_);
lean_inc(v_traceState_2203_);
lean_inc(v_auxDeclNGen_2207_);
lean_inc(v_ngen_2206_);
lean_inc(v_nextMacroScope_2205_);
lean_inc(v_env_2204_);
lean_dec(v___x_2202_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2230_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
uint64_t v_tid_2215_; lean_object* v_traces_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2229_; 
v_tid_2215_ = lean_ctor_get_uint64(v_traceState_2203_, sizeof(void*)*1);
v_traces_2216_ = lean_ctor_get(v_traceState_2203_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v_traceState_2203_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2218_ = v_traceState_2203_;
v_isShared_2219_ = v_isSharedCheck_2229_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_traces_2216_);
lean_dec(v_traceState_2203_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2229_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2220_; lean_object* v___x_2222_; 
v___x_2220_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2151_, v_traces_2216_);
lean_dec_ref(v_traces_2216_);
if (v_isShared_2219_ == 0)
{
lean_ctor_set(v___x_2218_, 0, v___x_2220_);
v___x_2222_ = v___x_2218_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v___x_2220_);
lean_ctor_set_uint64(v_reuseFailAlloc_2228_, sizeof(void*)*1, v_tid_2215_);
v___x_2222_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
lean_object* v___x_2224_; 
if (v_isShared_2214_ == 0)
{
lean_ctor_set(v___x_2213_, 4, v___x_2222_);
v___x_2224_ = v___x_2213_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_env_2204_);
lean_ctor_set(v_reuseFailAlloc_2227_, 1, v_nextMacroScope_2205_);
lean_ctor_set(v_reuseFailAlloc_2227_, 2, v_ngen_2206_);
lean_ctor_set(v_reuseFailAlloc_2227_, 3, v_auxDeclNGen_2207_);
lean_ctor_set(v_reuseFailAlloc_2227_, 4, v___x_2222_);
lean_ctor_set(v_reuseFailAlloc_2227_, 5, v_cache_2208_);
lean_ctor_set(v_reuseFailAlloc_2227_, 6, v_messages_2209_);
lean_ctor_set(v_reuseFailAlloc_2227_, 7, v_infoState_2210_);
lean_ctor_set(v_reuseFailAlloc_2227_, 8, v_snapshotTasks_2211_);
v___x_2224_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2225_ = lean_st_ref_set(v___y_2162_, v___x_2224_);
v___x_2226_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5___redArg(v_fst_2164_);
return v___x_2226_;
}
}
}
}
}
else
{
goto v___jp_2195_;
}
}
else
{
goto v___jp_2195_;
}
}
v___jp_2231_:
{
double v___x_2233_; double v___x_2234_; double v___x_2235_; uint8_t v___x_2236_; 
v___x_2233_ = lean_unbox_float(v_snd_2181_);
v___x_2234_ = lean_unbox_float(v_fst_2180_);
v___x_2235_ = lean_float_sub(v___x_2233_, v___x_2234_);
v___x_2236_ = lean_float_decLt(v___y_2232_, v___x_2235_);
v___y_2201_ = v___x_2236_;
goto v___jp_2200_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___boxed(lean_object** _args){
lean_object* v_cls_2247_ = _args[0];
lean_object* v_collapsed_2248_ = _args[1];
lean_object* v_tag_2249_ = _args[2];
lean_object* v_opts_2250_ = _args[3];
lean_object* v_clsEnabled_2251_ = _args[4];
lean_object* v_oldTraces_2252_ = _args[5];
lean_object* v_msg_2253_ = _args[6];
lean_object* v_resStartStop_2254_ = _args[7];
lean_object* v___y_2255_ = _args[8];
lean_object* v___y_2256_ = _args[9];
lean_object* v___y_2257_ = _args[10];
lean_object* v___y_2258_ = _args[11];
lean_object* v___y_2259_ = _args[12];
lean_object* v___y_2260_ = _args[13];
lean_object* v___y_2261_ = _args[14];
lean_object* v___y_2262_ = _args[15];
lean_object* v___y_2263_ = _args[16];
lean_object* v___y_2264_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_2265_; uint8_t v_clsEnabled_boxed_2266_; lean_object* v_res_2267_; 
v_collapsed_boxed_2265_ = lean_unbox(v_collapsed_2248_);
v_clsEnabled_boxed_2266_ = lean_unbox(v_clsEnabled_2251_);
v_res_2267_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4(v_cls_2247_, v_collapsed_boxed_2265_, v_tag_2249_, v_opts_2250_, v_clsEnabled_boxed_2266_, v_oldTraces_2252_, v_msg_2253_, v_resStartStop_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2258_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v_opts_2250_);
return v_res_2267_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2(void){
_start:
{
lean_object* v___x_2271_; lean_object* v___x_2272_; 
v___x_2271_ = lean_unsigned_to_nat(0u);
v___x_2272_ = l_Lean_Expr_bvar___override(v___x_2271_);
return v___x_2272_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8(void){
_start:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___x_2279_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__7));
v___x_2280_ = lean_unsigned_to_nat(48u);
v___x_2281_ = lean_unsigned_to_nat(219u);
v___x_2282_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__6));
v___x_2283_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__5));
v___x_2284_ = l_mkPanicMessageWithDecl(v___x_2283_, v___x_2282_, v___x_2281_, v___x_2280_, v___x_2279_);
return v___x_2284_;
}
}
static double _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9(void){
_start:
{
lean_object* v___x_2285_; double v___x_2286_; 
v___x_2285_ = lean_unsigned_to_nat(1000000000u);
v___x_2286_ = lean_float_of_nat(v___x_2285_);
return v___x_2286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj(lean_object* v_e_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_){
_start:
{
uint8_t v___y_2299_; lean_object* v___y_2300_; uint8_t v___y_2301_; lean_object* v_a_2302_; uint8_t v___y_2306_; lean_object* v___y_2307_; lean_object* v_a_2308_; 
if (lean_obj_tag(v_e_2287_) == 11)
{
lean_object* v_typeName_2312_; lean_object* v_idx_2313_; lean_object* v_struct_2314_; lean_object* v_res_2316_; lean_object* v___y_2317_; lean_object* v___y_2318_; lean_object* v___y_2319_; lean_object* v___y_2320_; lean_object* v___y_2321_; lean_object* v___y_2322_; lean_object* v___y_2323_; lean_object* v___y_2324_; lean_object* v___y_2325_; lean_object* v_options_2556_; lean_object* v_inheritedTraceOptions_2557_; uint8_t v_hasTrace_2558_; uint8_t v___x_2559_; 
v_typeName_2312_ = lean_ctor_get(v_e_2287_, 0);
v_idx_2313_ = lean_ctor_get(v_e_2287_, 1);
v_struct_2314_ = lean_ctor_get(v_e_2287_, 2);
v_options_2556_ = lean_ctor_get(v_a_2295_, 2);
v_inheritedTraceOptions_2557_ = lean_ctor_get(v_a_2295_, 13);
v_hasTrace_2558_ = lean_ctor_get_uint8(v_options_2556_, sizeof(void*)*1);
v___x_2559_ = lean_bool_not(v_hasTrace_2558_);
if (v___x_2559_ == 0)
{
lean_object* v___f_2560_; lean_object* v___x_2561_; uint8_t v___x_2562_; lean_object* v___x_2563_; lean_object* v___y_2565_; uint8_t v___y_2566_; lean_object* v___y_2567_; lean_object* v_a_2568_; lean_object* v___y_2581_; uint8_t v___y_2582_; lean_object* v___y_2583_; lean_object* v_a_2584_; lean_object* v___y_2587_; uint8_t v___y_2588_; lean_object* v___y_2589_; lean_object* v_a_2590_; uint8_t v___y_2593_; uint8_t v___y_2594_; lean_object* v___y_2595_; lean_object* v___y_2596_; uint8_t v___y_2597_; lean_object* v___y_2598_; lean_object* v_a_2599_; lean_object* v___y_2602_; uint8_t v___y_2603_; lean_object* v___y_2604_; lean_object* v___y_2605_; uint8_t v___y_2609_; uint8_t v___y_2610_; lean_object* v___y_2611_; uint8_t v___y_2612_; lean_object* v___y_2613_; lean_object* v___y_2614_; lean_object* v_a_2615_; lean_object* v___y_2618_; uint8_t v___y_2619_; lean_object* v___y_2620_; lean_object* v_a_2621_; lean_object* v___y_2631_; uint8_t v___y_2632_; lean_object* v___y_2633_; lean_object* v_a_2634_; uint8_t v___y_2637_; lean_object* v___y_2638_; lean_object* v___y_2639_; uint8_t v___y_2640_; lean_object* v___y_2641_; lean_object* v_a_2642_; uint8_t v___y_2645_; lean_object* v___y_2646_; uint8_t v___y_2647_; lean_object* v___y_2648_; lean_object* v___y_2649_; lean_object* v_a_2650_; lean_object* v___y_2653_; uint8_t v___y_2654_; lean_object* v___y_2655_; lean_object* v_a_2656_; lean_object* v___y_2659_; uint8_t v___y_2660_; lean_object* v___y_2661_; lean_object* v___y_2662_; uint8_t v___y_2666_; uint8_t v_a_2866_; 
lean_inc_ref(v_e_2287_);
lean_inc(v_idx_2313_);
lean_inc(v_typeName_2312_);
v___f_2560_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___boxed), 14, 3);
lean_closure_set(v___f_2560_, 0, v_typeName_2312_);
lean_closure_set(v___f_2560_, 1, v_idx_2313_);
lean_closure_set(v___f_2560_, 2, v_e_2287_);
v___x_2561_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2));
v___x_2562_ = 1;
v___x_2563_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__1));
if (v_hasTrace_2558_ == 0)
{
v_a_2866_ = v_hasTrace_2558_;
goto v___jp_2865_;
}
else
{
lean_object* v___x_2871_; uint8_t v___x_2872_; 
v___x_2871_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3);
v___x_2872_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2557_, v_options_2556_, v___x_2871_);
if (v___x_2872_ == 0)
{
v_a_2866_ = v___x_2872_;
goto v___jp_2865_;
}
else
{
v___y_2666_ = v___x_2872_;
goto v___jp_2665_;
}
}
v___jp_2564_:
{
lean_object* v___x_2569_; double v___x_2570_; double v___x_2571_; double v___x_2572_; double v___x_2573_; double v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; 
v___x_2569_ = lean_io_mono_nanos_now();
v___x_2570_ = lean_float_of_nat(v___y_2565_);
v___x_2571_ = lean_float_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9);
v___x_2572_ = lean_float_div(v___x_2570_, v___x_2571_);
v___x_2573_ = lean_float_of_nat(v___x_2569_);
v___x_2574_ = lean_float_div(v___x_2573_, v___x_2571_);
v___x_2575_ = lean_box_float(v___x_2572_);
v___x_2576_ = lean_box_float(v___x_2574_);
v___x_2577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2577_, 0, v___x_2575_);
lean_ctor_set(v___x_2577_, 1, v___x_2576_);
v___x_2578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2578_, 0, v_a_2568_);
lean_ctor_set(v___x_2578_, 1, v___x_2577_);
v___x_2579_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4(v___x_2561_, v___x_2562_, v___x_2563_, v_options_2556_, v___y_2566_, v___y_2567_, v___f_2560_, v___x_2578_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
return v___x_2579_;
}
v___jp_2580_:
{
lean_object* v___x_2585_; 
v___x_2585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2585_, 0, v_a_2584_);
v___y_2565_ = v___y_2581_;
v___y_2566_ = v___y_2582_;
v___y_2567_ = v___y_2583_;
v_a_2568_ = v___x_2585_;
goto v___jp_2564_;
}
v___jp_2586_:
{
lean_object* v___x_2591_; 
v___x_2591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2591_, 0, v_a_2590_);
v___y_2565_ = v___y_2587_;
v___y_2566_ = v___y_2588_;
v___y_2567_ = v___y_2589_;
v_a_2568_ = v___x_2591_;
goto v___jp_2564_;
}
v___jp_2592_:
{
lean_object* v___x_2600_; 
v___x_2600_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2600_, 0, v_a_2599_);
lean_ctor_set(v___x_2600_, 1, v___y_2596_);
lean_ctor_set_uint8(v___x_2600_, sizeof(void*)*2, v___y_2594_);
lean_ctor_set_uint8(v___x_2600_, sizeof(void*)*2 + 1, v___y_2593_);
v___y_2587_ = v___y_2595_;
v___y_2588_ = v___y_2597_;
v___y_2589_ = v___y_2598_;
v_a_2590_ = v___x_2600_;
goto v___jp_2586_;
}
v___jp_2601_:
{
if (lean_obj_tag(v___y_2605_) == 0)
{
lean_object* v_a_2606_; 
v_a_2606_ = lean_ctor_get(v___y_2605_, 0);
lean_inc(v_a_2606_);
lean_dec_ref_known(v___y_2605_, 1);
v___y_2587_ = v___y_2602_;
v___y_2588_ = v___y_2603_;
v___y_2589_ = v___y_2604_;
v_a_2590_ = v_a_2606_;
goto v___jp_2586_;
}
else
{
lean_object* v_a_2607_; 
v_a_2607_ = lean_ctor_get(v___y_2605_, 0);
lean_inc(v_a_2607_);
lean_dec_ref_known(v___y_2605_, 1);
v___y_2581_ = v___y_2602_;
v___y_2582_ = v___y_2603_;
v___y_2583_ = v___y_2604_;
v_a_2584_ = v_a_2607_;
goto v___jp_2580_;
}
}
v___jp_2608_:
{
lean_object* v___x_2616_; 
v___x_2616_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2616_, 0, v_a_2615_);
lean_ctor_set(v___x_2616_, 1, v___y_2614_);
lean_ctor_set_uint8(v___x_2616_, sizeof(void*)*2, v___y_2610_);
lean_ctor_set_uint8(v___x_2616_, sizeof(void*)*2 + 1, v___y_2609_);
v___y_2587_ = v___y_2611_;
v___y_2588_ = v___y_2612_;
v___y_2589_ = v___y_2613_;
v_a_2590_ = v___x_2616_;
goto v___jp_2586_;
}
v___jp_2617_:
{
lean_object* v___x_2622_; double v___x_2623_; double v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; 
v___x_2622_ = lean_io_get_num_heartbeats();
v___x_2623_ = lean_float_of_nat(v___y_2618_);
v___x_2624_ = lean_float_of_nat(v___x_2622_);
v___x_2625_ = lean_box_float(v___x_2623_);
v___x_2626_ = lean_box_float(v___x_2624_);
v___x_2627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2627_, 0, v___x_2625_);
lean_ctor_set(v___x_2627_, 1, v___x_2626_);
v___x_2628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2628_, 0, v_a_2621_);
lean_ctor_set(v___x_2628_, 1, v___x_2627_);
v___x_2629_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4(v___x_2561_, v___x_2562_, v___x_2563_, v_options_2556_, v___y_2619_, v___y_2620_, v___f_2560_, v___x_2628_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
return v___x_2629_;
}
v___jp_2630_:
{
lean_object* v___x_2635_; 
v___x_2635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2635_, 0, v_a_2634_);
v___y_2618_ = v___y_2631_;
v___y_2619_ = v___y_2632_;
v___y_2620_ = v___y_2633_;
v_a_2621_ = v___x_2635_;
goto v___jp_2617_;
}
v___jp_2636_:
{
lean_object* v___x_2643_; 
v___x_2643_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2643_, 0, v_a_2642_);
lean_ctor_set(v___x_2643_, 1, v___y_2638_);
lean_ctor_set_uint8(v___x_2643_, sizeof(void*)*2, v___y_2637_);
lean_ctor_set_uint8(v___x_2643_, sizeof(void*)*2 + 1, v___x_2559_);
v___y_2631_ = v___y_2639_;
v___y_2632_ = v___y_2640_;
v___y_2633_ = v___y_2641_;
v_a_2634_ = v___x_2643_;
goto v___jp_2630_;
}
v___jp_2644_:
{
lean_object* v___x_2651_; 
v___x_2651_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2651_, 0, v_a_2650_);
lean_ctor_set(v___x_2651_, 1, v___y_2648_);
lean_ctor_set_uint8(v___x_2651_, sizeof(void*)*2, v___y_2645_);
lean_ctor_set_uint8(v___x_2651_, sizeof(void*)*2 + 1, v___x_2559_);
v___y_2631_ = v___y_2646_;
v___y_2632_ = v___y_2647_;
v___y_2633_ = v___y_2649_;
v_a_2634_ = v___x_2651_;
goto v___jp_2630_;
}
v___jp_2652_:
{
lean_object* v___x_2657_; 
v___x_2657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2657_, 0, v_a_2656_);
v___y_2618_ = v___y_2653_;
v___y_2619_ = v___y_2654_;
v___y_2620_ = v___y_2655_;
v_a_2621_ = v___x_2657_;
goto v___jp_2617_;
}
v___jp_2658_:
{
if (lean_obj_tag(v___y_2662_) == 0)
{
lean_object* v_a_2663_; 
v_a_2663_ = lean_ctor_get(v___y_2662_, 0);
lean_inc(v_a_2663_);
lean_dec_ref_known(v___y_2662_, 1);
v___y_2631_ = v___y_2659_;
v___y_2632_ = v___y_2660_;
v___y_2633_ = v___y_2661_;
v_a_2634_ = v_a_2663_;
goto v___jp_2630_;
}
else
{
lean_object* v_a_2664_; 
v_a_2664_ = lean_ctor_get(v___y_2662_, 0);
lean_inc(v_a_2664_);
lean_dec_ref_known(v___y_2662_, 1);
v___y_2653_ = v___y_2659_;
v___y_2654_ = v___y_2660_;
v___y_2655_ = v___y_2661_;
v_a_2656_ = v_a_2664_;
goto v___jp_2652_;
}
}
v___jp_2665_:
{
lean_object* v___x_2667_; lean_object* v_a_2668_; lean_object* v___x_2669_; uint8_t v___x_2670_; 
v___x_2667_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg(v_a_2296_);
v_a_2668_ = lean_ctor_get(v___x_2667_, 0);
lean_inc(v_a_2668_);
lean_dec_ref(v___x_2667_);
v___x_2669_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2670_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_2556_, v___x_2669_);
if (v___x_2670_ == 0)
{
lean_object* v___x_2671_; lean_object* v___x_2672_; 
v___x_2671_ = lean_io_mono_nanos_now();
lean_inc(v_a_2296_);
lean_inc_ref(v_a_2295_);
lean_inc(v_a_2294_);
lean_inc_ref(v_a_2293_);
lean_inc(v_a_2292_);
lean_inc_ref(v_a_2291_);
lean_inc(v_a_2290_);
lean_inc_ref(v_a_2289_);
lean_inc(v_a_2288_);
lean_inc_ref(v_struct_2314_);
v___x_2672_ = lean_sym_simp(v_struct_2314_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
if (lean_obj_tag(v___x_2672_) == 0)
{
lean_object* v_a_2673_; 
v_a_2673_ = lean_ctor_get(v___x_2672_, 0);
lean_inc(v_a_2673_);
lean_dec_ref_known(v___x_2672_, 1);
if (lean_obj_tag(v_a_2673_) == 0)
{
uint8_t v_contextDependent_2674_; lean_object* v___x_2676_; uint8_t v_isShared_2677_; uint8_t v_isSharedCheck_2695_; 
v_contextDependent_2674_ = lean_ctor_get_uint8(v_a_2673_, 1);
v_isSharedCheck_2695_ = !lean_is_exclusive(v_a_2673_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2676_ = v_a_2673_;
v_isShared_2677_ = v_isSharedCheck_2695_;
goto v_resetjp_2675_;
}
else
{
lean_dec(v_a_2673_);
v___x_2676_ = lean_box(0);
v_isShared_2677_ = v_isSharedCheck_2695_;
goto v_resetjp_2675_;
}
v_resetjp_2675_:
{
uint8_t v___x_2678_; lean_object* v___x_2679_; lean_object* v___f_2680_; lean_object* v___x_2681_; 
v___x_2678_ = 1;
v___x_2679_ = lean_box(v___x_2678_);
v___f_2680_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2680_, 0, v___x_2679_);
lean_closure_set(v___f_2680_, 1, v_e_2287_);
v___x_2681_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___f_2680_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
if (lean_obj_tag(v___x_2681_) == 0)
{
lean_object* v_a_2682_; 
v_a_2682_ = lean_ctor_get(v___x_2681_, 0);
lean_inc(v_a_2682_);
lean_dec_ref_known(v___x_2681_, 1);
if (lean_obj_tag(v_a_2682_) == 1)
{
lean_object* v_val_2683_; lean_object* v___x_2684_; 
lean_del_object(v___x_2676_);
v_val_2683_ = lean_ctor_get(v_a_2682_, 0);
lean_inc(v_val_2683_);
lean_dec_ref_known(v_a_2682_, 1);
v___x_2684_ = l_Lean_Meta_Sym_shareCommonInc(v_val_2683_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
if (lean_obj_tag(v___x_2684_) == 0)
{
lean_object* v_a_2685_; lean_object* v___x_2686_; 
v_a_2685_ = lean_ctor_get(v___x_2684_, 0);
lean_inc_n(v_a_2685_, 2);
lean_dec_ref_known(v___x_2684_, 1);
v___x_2686_ = l_Lean_Meta_Sym_mkEqRefl(v_a_2685_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
if (lean_obj_tag(v___x_2686_) == 0)
{
lean_object* v_a_2687_; lean_object* v___x_2688_; 
v_a_2687_ = lean_ctor_get(v___x_2686_, 0);
lean_inc(v_a_2687_);
lean_dec_ref_known(v___x_2686_, 1);
v___x_2688_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2688_, 0, v_a_2685_);
lean_ctor_set(v___x_2688_, 1, v_a_2687_);
lean_ctor_set_uint8(v___x_2688_, sizeof(void*)*2, v_contextDependent_2674_);
lean_ctor_set_uint8(v___x_2688_, sizeof(void*)*2 + 1, v___x_2670_);
v___y_2587_ = v___x_2671_;
v___y_2588_ = v___y_2666_;
v___y_2589_ = v_a_2668_;
v_a_2590_ = v___x_2688_;
goto v___jp_2586_;
}
else
{
lean_object* v_a_2689_; 
lean_dec(v_a_2685_);
v_a_2689_ = lean_ctor_get(v___x_2686_, 0);
lean_inc(v_a_2689_);
lean_dec_ref_known(v___x_2686_, 1);
v___y_2581_ = v___x_2671_;
v___y_2582_ = v___y_2666_;
v___y_2583_ = v_a_2668_;
v_a_2584_ = v_a_2689_;
goto v___jp_2580_;
}
}
else
{
lean_object* v_a_2690_; 
v_a_2690_ = lean_ctor_get(v___x_2684_, 0);
lean_inc(v_a_2690_);
lean_dec_ref_known(v___x_2684_, 1);
v___y_2581_ = v___x_2671_;
v___y_2582_ = v___y_2666_;
v___y_2583_ = v_a_2668_;
v_a_2584_ = v_a_2690_;
goto v___jp_2580_;
}
}
else
{
lean_object* v___x_2692_; 
lean_dec(v_a_2682_);
if (v_isShared_2677_ == 0)
{
v___x_2692_ = v___x_2676_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v_reuseFailAlloc_2693_, 1, v_contextDependent_2674_);
v___x_2692_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
lean_ctor_set_uint8(v___x_2692_, 0, v___x_2562_);
v___y_2587_ = v___x_2671_;
v___y_2588_ = v___y_2666_;
v___y_2589_ = v_a_2668_;
v_a_2590_ = v___x_2692_;
goto v___jp_2586_;
}
}
}
else
{
lean_object* v_a_2694_; 
lean_del_object(v___x_2676_);
v_a_2694_ = lean_ctor_get(v___x_2681_, 0);
lean_inc(v_a_2694_);
lean_dec_ref_known(v___x_2681_, 1);
v___y_2581_ = v___x_2671_;
v___y_2582_ = v___y_2666_;
v___y_2583_ = v_a_2668_;
v_a_2584_ = v_a_2694_;
goto v___jp_2580_;
}
}
}
else
{
lean_object* v_e_x27_2696_; lean_object* v_proof_2697_; uint8_t v_contextDependent_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2767_; 
v_e_x27_2696_ = lean_ctor_get(v_a_2673_, 0);
v_proof_2697_ = lean_ctor_get(v_a_2673_, 1);
v_contextDependent_2698_ = lean_ctor_get_uint8(v_a_2673_, sizeof(void*)*2 + 1);
v_isSharedCheck_2767_ = !lean_is_exclusive(v_a_2673_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2700_ = v_a_2673_;
v_isShared_2701_ = v_isSharedCheck_2767_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_proof_2697_);
lean_inc(v_e_x27_2696_);
lean_dec(v_a_2673_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2767_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v___x_2702_; 
lean_inc_ref(v_e_x27_2696_);
v___x_2702_ = l_Lean_Meta_Sym_inferType(v_e_x27_2696_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
if (lean_obj_tag(v___x_2702_) == 0)
{
lean_object* v_a_2703_; lean_object* v___x_2704_; uint8_t v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; 
v_a_2703_ = lean_ctor_get(v___x_2702_, 0);
lean_inc(v_a_2703_);
lean_dec_ref_known(v___x_2702_, 1);
v___x_2704_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__1));
v___x_2705_ = 0;
v___x_2706_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2);
lean_inc(v_idx_2313_);
lean_inc(v_typeName_2312_);
v___x_2707_ = l_Lean_Expr_proj___override(v_typeName_2312_, v_idx_2313_, v___x_2706_);
v___x_2708_ = l_Lean_mkLambda(v___x_2704_, v___x_2705_, v_a_2703_, v___x_2707_);
lean_inc_ref(v___x_2708_);
v___x_2709_ = l_Lean_Meta_Sym_inferType(v___x_2708_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
if (lean_obj_tag(v___x_2709_) == 0)
{
lean_object* v_a_2710_; uint8_t v___x_2711_; 
v_a_2710_ = lean_ctor_get(v___x_2709_, 0);
lean_inc(v_a_2710_);
lean_dec_ref_known(v___x_2709_, 1);
v___x_2711_ = l_Lean_Expr_isArrow(v_a_2710_);
if (v___x_2711_ == 0)
{
uint8_t v___x_2712_; lean_object* v___x_2713_; lean_object* v___f_2714_; lean_object* v___x_2715_; 
lean_dec(v_a_2710_);
v___x_2712_ = 1;
v___x_2713_ = lean_box(v___x_2712_);
lean_inc_ref(v_e_2287_);
v___f_2714_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2714_, 0, v___x_2713_);
lean_closure_set(v___f_2714_, 1, v_e_2287_);
v___x_2715_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___f_2714_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
if (lean_obj_tag(v___x_2715_) == 0)
{
lean_object* v_a_2716_; 
v_a_2716_ = lean_ctor_get(v___x_2715_, 0);
lean_inc(v_a_2716_);
lean_dec_ref_known(v___x_2715_, 1);
if (lean_obj_tag(v_a_2716_) == 0)
{
lean_object* v___x_2717_; 
lean_del_object(v___x_2700_);
lean_inc_ref(v_e_x27_2696_);
lean_inc_ref(v_struct_2314_);
v___x_2717_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_struct_2314_, v_e_x27_2696_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
if (lean_obj_tag(v___x_2717_) == 0)
{
lean_object* v_a_2718_; uint8_t v___x_2719_; 
v_a_2718_ = lean_ctor_get(v___x_2717_, 0);
lean_inc(v_a_2718_);
lean_dec_ref_known(v___x_2717_, 1);
v___x_2719_ = lean_unbox(v_a_2718_);
lean_dec(v_a_2718_);
if (v___x_2719_ == 0)
{
lean_object* v___x_2720_; 
lean_dec_ref(v___x_2708_);
lean_dec_ref(v_proof_2697_);
lean_dec_ref(v_e_x27_2696_);
lean_dec_ref_known(v_e_2287_, 3);
v___x_2720_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2720_, 0, v___x_2562_);
lean_ctor_set_uint8(v___x_2720_, 1, v_contextDependent_2698_);
v___y_2587_ = v___x_2671_;
v___y_2588_ = v___y_2666_;
v___y_2589_ = v_a_2668_;
v_a_2590_ = v___x_2720_;
goto v___jp_2586_;
}
else
{
lean_object* v___x_2721_; 
v___x_2721_ = l_Lean_Meta_mkHCongr(v___x_2708_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
if (lean_obj_tag(v___x_2721_) == 0)
{
lean_object* v_a_2722_; lean_object* v_proof_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; 
v_a_2722_ = lean_ctor_get(v___x_2721_, 0);
lean_inc(v_a_2722_);
lean_dec_ref_known(v___x_2721_, 1);
v_proof_2723_ = lean_ctor_get(v_a_2722_, 1);
lean_inc_ref(v_proof_2723_);
lean_dec(v_a_2722_);
lean_inc_ref(v_e_x27_2696_);
lean_inc_ref(v_struct_2314_);
v___x_2724_ = l_Lean_mkApp3(v_proof_2723_, v_struct_2314_, v_e_x27_2696_, v_proof_2697_);
v___x_2725_ = l_Lean_Meta_mkEqOfHEq(v___x_2724_, v___x_2670_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
if (lean_obj_tag(v___x_2725_) == 0)
{
lean_object* v_a_2726_; uint8_t v___x_2727_; 
v_a_2726_ = lean_ctor_get(v___x_2725_, 0);
lean_inc(v_a_2726_);
lean_dec_ref_known(v___x_2725_, 1);
v___x_2727_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_2314_, v_e_x27_2696_);
if (v___x_2727_ == 0)
{
lean_object* v___x_2728_; 
lean_inc(v_idx_2313_);
lean_inc(v_typeName_2312_);
lean_dec_ref_known(v_e_2287_, 3);
v___x_2728_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_typeName_2312_, v_idx_2313_, v_e_x27_2696_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
if (lean_obj_tag(v___x_2728_) == 0)
{
lean_object* v_a_2729_; 
v_a_2729_ = lean_ctor_get(v___x_2728_, 0);
lean_inc(v_a_2729_);
lean_dec_ref_known(v___x_2728_, 1);
v___y_2593_ = v___x_2670_;
v___y_2594_ = v_contextDependent_2698_;
v___y_2595_ = v___x_2671_;
v___y_2596_ = v_a_2726_;
v___y_2597_ = v___y_2666_;
v___y_2598_ = v_a_2668_;
v_a_2599_ = v_a_2729_;
goto v___jp_2592_;
}
else
{
lean_object* v_a_2730_; 
lean_dec(v_a_2726_);
v_a_2730_ = lean_ctor_get(v___x_2728_, 0);
lean_inc(v_a_2730_);
lean_dec_ref_known(v___x_2728_, 1);
v___y_2581_ = v___x_2671_;
v___y_2582_ = v___y_2666_;
v___y_2583_ = v_a_2668_;
v_a_2584_ = v_a_2730_;
goto v___jp_2580_;
}
}
else
{
lean_dec_ref(v_e_x27_2696_);
v___y_2593_ = v___x_2670_;
v___y_2594_ = v_contextDependent_2698_;
v___y_2595_ = v___x_2671_;
v___y_2596_ = v_a_2726_;
v___y_2597_ = v___y_2666_;
v___y_2598_ = v_a_2668_;
v_a_2599_ = v_e_2287_;
goto v___jp_2592_;
}
}
else
{
lean_object* v_a_2731_; 
lean_dec_ref(v_e_x27_2696_);
lean_dec_ref_known(v_e_2287_, 3);
v_a_2731_ = lean_ctor_get(v___x_2725_, 0);
lean_inc(v_a_2731_);
lean_dec_ref_known(v___x_2725_, 1);
v___y_2581_ = v___x_2671_;
v___y_2582_ = v___y_2666_;
v___y_2583_ = v_a_2668_;
v_a_2584_ = v_a_2731_;
goto v___jp_2580_;
}
}
else
{
lean_object* v_a_2732_; 
lean_dec_ref(v_proof_2697_);
lean_dec_ref(v_e_x27_2696_);
lean_dec_ref_known(v_e_2287_, 3);
v_a_2732_ = lean_ctor_get(v___x_2721_, 0);
lean_inc(v_a_2732_);
lean_dec_ref_known(v___x_2721_, 1);
v___y_2581_ = v___x_2671_;
v___y_2582_ = v___y_2666_;
v___y_2583_ = v_a_2668_;
v_a_2584_ = v_a_2732_;
goto v___jp_2580_;
}
}
}
else
{
lean_object* v_a_2733_; 
lean_dec_ref(v___x_2708_);
lean_dec_ref(v_proof_2697_);
lean_dec_ref(v_e_x27_2696_);
lean_dec_ref_known(v_e_2287_, 3);
v_a_2733_ = lean_ctor_get(v___x_2717_, 0);
lean_inc(v_a_2733_);
lean_dec_ref_known(v___x_2717_, 1);
v___y_2581_ = v___x_2671_;
v___y_2582_ = v___y_2666_;
v___y_2583_ = v_a_2668_;
v_a_2584_ = v_a_2733_;
goto v___jp_2580_;
}
}
else
{
lean_object* v_val_2734_; lean_object* v___x_2735_; 
lean_dec_ref(v___x_2708_);
lean_dec_ref(v_proof_2697_);
lean_dec_ref(v_e_x27_2696_);
lean_dec_ref_known(v_e_2287_, 3);
v_val_2734_ = lean_ctor_get(v_a_2716_, 0);
lean_inc(v_val_2734_);
lean_dec_ref_known(v_a_2716_, 1);
v___x_2735_ = l_Lean_Meta_Sym_shareCommonInc(v_val_2734_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
if (lean_obj_tag(v___x_2735_) == 0)
{
lean_object* v_a_2736_; lean_object* v___x_2737_; 
v_a_2736_ = lean_ctor_get(v___x_2735_, 0);
lean_inc_n(v_a_2736_, 2);
lean_dec_ref_known(v___x_2735_, 1);
v___x_2737_ = l_Lean_Meta_Sym_mkEqRefl(v_a_2736_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
if (lean_obj_tag(v___x_2737_) == 0)
{
lean_object* v_a_2738_; lean_object* v___x_2740_; 
v_a_2738_ = lean_ctor_get(v___x_2737_, 0);
lean_inc(v_a_2738_);
lean_dec_ref_known(v___x_2737_, 1);
if (v_isShared_2701_ == 0)
{
lean_ctor_set(v___x_2700_, 1, v_a_2738_);
lean_ctor_set(v___x_2700_, 0, v_a_2736_);
v___x_2740_ = v___x_2700_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v_a_2736_);
lean_ctor_set(v_reuseFailAlloc_2741_, 1, v_a_2738_);
v___x_2740_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
lean_ctor_set_uint8(v___x_2740_, sizeof(void*)*2, v_contextDependent_2698_);
lean_ctor_set_uint8(v___x_2740_, sizeof(void*)*2 + 1, v___x_2670_);
v___y_2587_ = v___x_2671_;
v___y_2588_ = v___y_2666_;
v___y_2589_ = v_a_2668_;
v_a_2590_ = v___x_2740_;
goto v___jp_2586_;
}
}
else
{
lean_object* v_a_2742_; 
lean_dec(v_a_2736_);
lean_del_object(v___x_2700_);
v_a_2742_ = lean_ctor_get(v___x_2737_, 0);
lean_inc(v_a_2742_);
lean_dec_ref_known(v___x_2737_, 1);
v___y_2581_ = v___x_2671_;
v___y_2582_ = v___y_2666_;
v___y_2583_ = v_a_2668_;
v_a_2584_ = v_a_2742_;
goto v___jp_2580_;
}
}
else
{
lean_object* v_a_2743_; 
lean_del_object(v___x_2700_);
v_a_2743_ = lean_ctor_get(v___x_2735_, 0);
lean_inc(v_a_2743_);
lean_dec_ref_known(v___x_2735_, 1);
v___y_2581_ = v___x_2671_;
v___y_2582_ = v___y_2666_;
v___y_2583_ = v_a_2668_;
v_a_2584_ = v_a_2743_;
goto v___jp_2580_;
}
}
}
else
{
lean_object* v_a_2744_; 
lean_dec_ref(v___x_2708_);
lean_del_object(v___x_2700_);
lean_dec_ref(v_proof_2697_);
lean_dec_ref(v_e_x27_2696_);
lean_dec_ref_known(v_e_2287_, 3);
v_a_2744_ = lean_ctor_get(v___x_2715_, 0);
lean_inc(v_a_2744_);
lean_dec_ref_known(v___x_2715_, 1);
v___y_2581_ = v___x_2671_;
v___y_2582_ = v___y_2666_;
v___y_2583_ = v_a_2668_;
v_a_2584_ = v_a_2744_;
goto v___jp_2580_;
}
}
else
{
lean_del_object(v___x_2700_);
if (lean_obj_tag(v_a_2710_) == 7)
{
lean_object* v_binderType_2745_; lean_object* v_body_2746_; lean_object* v___x_2747_; 
v_binderType_2745_ = lean_ctor_get(v_a_2710_, 1);
lean_inc_ref_n(v_binderType_2745_, 2);
v_body_2746_ = lean_ctor_get(v_a_2710_, 2);
lean_inc_ref(v_body_2746_);
lean_dec_ref_known(v_a_2710_, 3);
v___x_2747_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_2745_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
if (lean_obj_tag(v___x_2747_) == 0)
{
lean_object* v_a_2748_; lean_object* v___x_2749_; 
v_a_2748_ = lean_ctor_get(v___x_2747_, 0);
lean_inc(v_a_2748_);
lean_dec_ref_known(v___x_2747_, 1);
lean_inc_ref(v_body_2746_);
v___x_2749_ = l_Lean_Meta_Sym_getLevel___redArg(v_body_2746_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
if (lean_obj_tag(v___x_2749_) == 0)
{
lean_object* v_a_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; uint8_t v___x_2757_; 
v_a_2750_ = lean_ctor_get(v___x_2749_, 0);
lean_inc(v_a_2750_);
lean_dec_ref_known(v___x_2749_, 1);
v___x_2751_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4));
v___x_2752_ = lean_box(0);
v___x_2753_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2753_, 0, v_a_2750_);
lean_ctor_set(v___x_2753_, 1, v___x_2752_);
v___x_2754_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2754_, 0, v_a_2748_);
lean_ctor_set(v___x_2754_, 1, v___x_2753_);
v___x_2755_ = l_Lean_mkConst(v___x_2751_, v___x_2754_);
lean_inc_ref(v_e_x27_2696_);
lean_inc_ref(v_struct_2314_);
v___x_2756_ = l_Lean_mkApp6(v___x_2755_, v_binderType_2745_, v_body_2746_, v_struct_2314_, v_e_x27_2696_, v___x_2708_, v_proof_2697_);
v___x_2757_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_2314_, v_e_x27_2696_);
if (v___x_2757_ == 0)
{
lean_object* v___x_2758_; 
lean_inc(v_idx_2313_);
lean_inc(v_typeName_2312_);
lean_dec_ref_known(v_e_2287_, 3);
v___x_2758_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_typeName_2312_, v_idx_2313_, v_e_x27_2696_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
if (lean_obj_tag(v___x_2758_) == 0)
{
lean_object* v_a_2759_; 
v_a_2759_ = lean_ctor_get(v___x_2758_, 0);
lean_inc(v_a_2759_);
lean_dec_ref_known(v___x_2758_, 1);
v___y_2609_ = v___x_2670_;
v___y_2610_ = v_contextDependent_2698_;
v___y_2611_ = v___x_2671_;
v___y_2612_ = v___y_2666_;
v___y_2613_ = v_a_2668_;
v___y_2614_ = v___x_2756_;
v_a_2615_ = v_a_2759_;
goto v___jp_2608_;
}
else
{
lean_object* v_a_2760_; 
lean_dec_ref(v___x_2756_);
v_a_2760_ = lean_ctor_get(v___x_2758_, 0);
lean_inc(v_a_2760_);
lean_dec_ref_known(v___x_2758_, 1);
v___y_2581_ = v___x_2671_;
v___y_2582_ = v___y_2666_;
v___y_2583_ = v_a_2668_;
v_a_2584_ = v_a_2760_;
goto v___jp_2580_;
}
}
else
{
lean_dec_ref(v_e_x27_2696_);
v___y_2609_ = v___x_2670_;
v___y_2610_ = v_contextDependent_2698_;
v___y_2611_ = v___x_2671_;
v___y_2612_ = v___y_2666_;
v___y_2613_ = v_a_2668_;
v___y_2614_ = v___x_2756_;
v_a_2615_ = v_e_2287_;
goto v___jp_2608_;
}
}
else
{
lean_object* v_a_2761_; 
lean_dec(v_a_2748_);
lean_dec_ref(v_body_2746_);
lean_dec_ref(v_binderType_2745_);
lean_dec_ref(v___x_2708_);
lean_dec_ref(v_proof_2697_);
lean_dec_ref(v_e_x27_2696_);
lean_dec_ref_known(v_e_2287_, 3);
v_a_2761_ = lean_ctor_get(v___x_2749_, 0);
lean_inc(v_a_2761_);
lean_dec_ref_known(v___x_2749_, 1);
v___y_2581_ = v___x_2671_;
v___y_2582_ = v___y_2666_;
v___y_2583_ = v_a_2668_;
v_a_2584_ = v_a_2761_;
goto v___jp_2580_;
}
}
else
{
lean_object* v_a_2762_; 
lean_dec_ref(v_body_2746_);
lean_dec_ref(v_binderType_2745_);
lean_dec_ref(v___x_2708_);
lean_dec_ref(v_proof_2697_);
lean_dec_ref(v_e_x27_2696_);
lean_dec_ref_known(v_e_2287_, 3);
v_a_2762_ = lean_ctor_get(v___x_2747_, 0);
lean_inc(v_a_2762_);
lean_dec_ref_known(v___x_2747_, 1);
v___y_2581_ = v___x_2671_;
v___y_2582_ = v___y_2666_;
v___y_2583_ = v_a_2668_;
v_a_2584_ = v_a_2762_;
goto v___jp_2580_;
}
}
else
{
lean_object* v___x_2763_; lean_object* v___x_2764_; 
lean_dec(v_a_2710_);
lean_dec_ref(v___x_2708_);
lean_dec_ref(v_proof_2697_);
lean_dec_ref(v_e_x27_2696_);
lean_dec_ref_known(v_e_2287_, 3);
v___x_2763_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8);
v___x_2764_ = l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1(v___x_2763_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
v___y_2602_ = v___x_2671_;
v___y_2603_ = v___y_2666_;
v___y_2604_ = v_a_2668_;
v___y_2605_ = v___x_2764_;
goto v___jp_2601_;
}
}
}
else
{
lean_object* v_a_2765_; 
lean_dec_ref(v___x_2708_);
lean_del_object(v___x_2700_);
lean_dec_ref(v_proof_2697_);
lean_dec_ref(v_e_x27_2696_);
lean_dec_ref_known(v_e_2287_, 3);
v_a_2765_ = lean_ctor_get(v___x_2709_, 0);
lean_inc(v_a_2765_);
lean_dec_ref_known(v___x_2709_, 1);
v___y_2581_ = v___x_2671_;
v___y_2582_ = v___y_2666_;
v___y_2583_ = v_a_2668_;
v_a_2584_ = v_a_2765_;
goto v___jp_2580_;
}
}
else
{
lean_object* v_a_2766_; 
lean_del_object(v___x_2700_);
lean_dec_ref(v_proof_2697_);
lean_dec_ref(v_e_x27_2696_);
lean_dec_ref_known(v_e_2287_, 3);
v_a_2766_ = lean_ctor_get(v___x_2702_, 0);
lean_inc(v_a_2766_);
lean_dec_ref_known(v___x_2702_, 1);
v___y_2581_ = v___x_2671_;
v___y_2582_ = v___y_2666_;
v___y_2583_ = v_a_2668_;
v_a_2584_ = v_a_2766_;
goto v___jp_2580_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_2287_, 3);
v___y_2602_ = v___x_2671_;
v___y_2603_ = v___y_2666_;
v___y_2604_ = v_a_2668_;
v___y_2605_ = v___x_2672_;
goto v___jp_2601_;
}
}
else
{
lean_object* v___x_2768_; lean_object* v___x_2769_; 
v___x_2768_ = lean_io_get_num_heartbeats();
lean_inc(v_a_2296_);
lean_inc_ref(v_a_2295_);
lean_inc(v_a_2294_);
lean_inc_ref(v_a_2293_);
lean_inc(v_a_2292_);
lean_inc_ref(v_a_2291_);
lean_inc(v_a_2290_);
lean_inc_ref(v_a_2289_);
lean_inc(v_a_2288_);
lean_inc_ref(v_struct_2314_);
v___x_2769_ = lean_sym_simp(v_struct_2314_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
if (lean_obj_tag(v___x_2769_) == 0)
{
lean_object* v_a_2770_; 
v_a_2770_ = lean_ctor_get(v___x_2769_, 0);
lean_inc(v_a_2770_);
lean_dec_ref_known(v___x_2769_, 1);
if (lean_obj_tag(v_a_2770_) == 0)
{
uint8_t v_contextDependent_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2792_; 
v_contextDependent_2771_ = lean_ctor_get_uint8(v_a_2770_, 1);
v_isSharedCheck_2792_ = !lean_is_exclusive(v_a_2770_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2773_ = v_a_2770_;
v_isShared_2774_ = v_isSharedCheck_2792_;
goto v_resetjp_2772_;
}
else
{
lean_dec(v_a_2770_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2792_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
uint8_t v___x_2775_; lean_object* v___x_2776_; lean_object* v___f_2777_; lean_object* v___x_2778_; 
v___x_2775_ = 1;
v___x_2776_ = lean_box(v___x_2775_);
v___f_2777_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2777_, 0, v___x_2776_);
lean_closure_set(v___f_2777_, 1, v_e_2287_);
v___x_2778_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___f_2777_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_object* v_a_2779_; 
v_a_2779_ = lean_ctor_get(v___x_2778_, 0);
lean_inc(v_a_2779_);
lean_dec_ref_known(v___x_2778_, 1);
if (lean_obj_tag(v_a_2779_) == 1)
{
lean_object* v_val_2780_; lean_object* v___x_2781_; 
lean_del_object(v___x_2773_);
v_val_2780_ = lean_ctor_get(v_a_2779_, 0);
lean_inc(v_val_2780_);
lean_dec_ref_known(v_a_2779_, 1);
v___x_2781_ = l_Lean_Meta_Sym_shareCommonInc(v_val_2780_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
if (lean_obj_tag(v___x_2781_) == 0)
{
lean_object* v_a_2782_; lean_object* v___x_2783_; 
v_a_2782_ = lean_ctor_get(v___x_2781_, 0);
lean_inc_n(v_a_2782_, 2);
lean_dec_ref_known(v___x_2781_, 1);
v___x_2783_ = l_Lean_Meta_Sym_mkEqRefl(v_a_2782_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
if (lean_obj_tag(v___x_2783_) == 0)
{
lean_object* v_a_2784_; lean_object* v___x_2785_; 
v_a_2784_ = lean_ctor_get(v___x_2783_, 0);
lean_inc(v_a_2784_);
lean_dec_ref_known(v___x_2783_, 1);
v___x_2785_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2785_, 0, v_a_2782_);
lean_ctor_set(v___x_2785_, 1, v_a_2784_);
lean_ctor_set_uint8(v___x_2785_, sizeof(void*)*2, v_contextDependent_2771_);
lean_ctor_set_uint8(v___x_2785_, sizeof(void*)*2 + 1, v___x_2559_);
v___y_2631_ = v___x_2768_;
v___y_2632_ = v___y_2666_;
v___y_2633_ = v_a_2668_;
v_a_2634_ = v___x_2785_;
goto v___jp_2630_;
}
else
{
lean_object* v_a_2786_; 
lean_dec(v_a_2782_);
v_a_2786_ = lean_ctor_get(v___x_2783_, 0);
lean_inc(v_a_2786_);
lean_dec_ref_known(v___x_2783_, 1);
v___y_2653_ = v___x_2768_;
v___y_2654_ = v___y_2666_;
v___y_2655_ = v_a_2668_;
v_a_2656_ = v_a_2786_;
goto v___jp_2652_;
}
}
else
{
lean_object* v_a_2787_; 
v_a_2787_ = lean_ctor_get(v___x_2781_, 0);
lean_inc(v_a_2787_);
lean_dec_ref_known(v___x_2781_, 1);
v___y_2653_ = v___x_2768_;
v___y_2654_ = v___y_2666_;
v___y_2655_ = v_a_2668_;
v_a_2656_ = v_a_2787_;
goto v___jp_2652_;
}
}
else
{
lean_object* v___x_2789_; 
lean_dec(v_a_2779_);
if (v_isShared_2774_ == 0)
{
v___x_2789_ = v___x_2773_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v_reuseFailAlloc_2790_, 1, v_contextDependent_2771_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
lean_ctor_set_uint8(v___x_2789_, 0, v___x_2670_);
v___y_2631_ = v___x_2768_;
v___y_2632_ = v___y_2666_;
v___y_2633_ = v_a_2668_;
v_a_2634_ = v___x_2789_;
goto v___jp_2630_;
}
}
}
else
{
lean_object* v_a_2791_; 
lean_del_object(v___x_2773_);
v_a_2791_ = lean_ctor_get(v___x_2778_, 0);
lean_inc(v_a_2791_);
lean_dec_ref_known(v___x_2778_, 1);
v___y_2653_ = v___x_2768_;
v___y_2654_ = v___y_2666_;
v___y_2655_ = v_a_2668_;
v_a_2656_ = v_a_2791_;
goto v___jp_2652_;
}
}
}
else
{
lean_object* v_e_x27_2793_; lean_object* v_proof_2794_; uint8_t v_contextDependent_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2864_; 
v_e_x27_2793_ = lean_ctor_get(v_a_2770_, 0);
v_proof_2794_ = lean_ctor_get(v_a_2770_, 1);
v_contextDependent_2795_ = lean_ctor_get_uint8(v_a_2770_, sizeof(void*)*2 + 1);
v_isSharedCheck_2864_ = !lean_is_exclusive(v_a_2770_);
if (v_isSharedCheck_2864_ == 0)
{
v___x_2797_ = v_a_2770_;
v_isShared_2798_ = v_isSharedCheck_2864_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_proof_2794_);
lean_inc(v_e_x27_2793_);
lean_dec(v_a_2770_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2864_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v___x_2799_; 
lean_inc_ref(v_e_x27_2793_);
v___x_2799_ = l_Lean_Meta_Sym_inferType(v_e_x27_2793_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
if (lean_obj_tag(v___x_2799_) == 0)
{
lean_object* v_a_2800_; lean_object* v___x_2801_; uint8_t v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; 
v_a_2800_ = lean_ctor_get(v___x_2799_, 0);
lean_inc(v_a_2800_);
lean_dec_ref_known(v___x_2799_, 1);
v___x_2801_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__1));
v___x_2802_ = 0;
v___x_2803_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2);
lean_inc(v_idx_2313_);
lean_inc(v_typeName_2312_);
v___x_2804_ = l_Lean_Expr_proj___override(v_typeName_2312_, v_idx_2313_, v___x_2803_);
v___x_2805_ = l_Lean_mkLambda(v___x_2801_, v___x_2802_, v_a_2800_, v___x_2804_);
lean_inc_ref(v___x_2805_);
v___x_2806_ = l_Lean_Meta_Sym_inferType(v___x_2805_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
if (lean_obj_tag(v___x_2806_) == 0)
{
lean_object* v_a_2807_; uint8_t v___x_2808_; 
v_a_2807_ = lean_ctor_get(v___x_2806_, 0);
lean_inc(v_a_2807_);
lean_dec_ref_known(v___x_2806_, 1);
v___x_2808_ = l_Lean_Expr_isArrow(v_a_2807_);
if (v___x_2808_ == 0)
{
uint8_t v___x_2809_; lean_object* v___x_2810_; lean_object* v___f_2811_; lean_object* v___x_2812_; 
lean_dec(v_a_2807_);
v___x_2809_ = 1;
v___x_2810_ = lean_box(v___x_2809_);
lean_inc_ref(v_e_2287_);
v___f_2811_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2811_, 0, v___x_2810_);
lean_closure_set(v___f_2811_, 1, v_e_2287_);
v___x_2812_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___f_2811_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_object* v_a_2813_; 
v_a_2813_ = lean_ctor_get(v___x_2812_, 0);
lean_inc(v_a_2813_);
lean_dec_ref_known(v___x_2812_, 1);
if (lean_obj_tag(v_a_2813_) == 0)
{
lean_object* v___x_2814_; 
lean_del_object(v___x_2797_);
lean_inc_ref(v_e_x27_2793_);
lean_inc_ref(v_struct_2314_);
v___x_2814_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_struct_2314_, v_e_x27_2793_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
if (lean_obj_tag(v___x_2814_) == 0)
{
lean_object* v_a_2815_; uint8_t v___x_2816_; 
v_a_2815_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_a_2815_);
lean_dec_ref_known(v___x_2814_, 1);
v___x_2816_ = lean_unbox(v_a_2815_);
lean_dec(v_a_2815_);
if (v___x_2816_ == 0)
{
lean_object* v___x_2817_; 
lean_dec_ref(v___x_2805_);
lean_dec_ref(v_proof_2794_);
lean_dec_ref(v_e_x27_2793_);
lean_dec_ref_known(v_e_2287_, 3);
v___x_2817_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2817_, 0, v___x_2670_);
lean_ctor_set_uint8(v___x_2817_, 1, v_contextDependent_2795_);
v___y_2631_ = v___x_2768_;
v___y_2632_ = v___y_2666_;
v___y_2633_ = v_a_2668_;
v_a_2634_ = v___x_2817_;
goto v___jp_2630_;
}
else
{
lean_object* v___x_2818_; 
v___x_2818_ = l_Lean_Meta_mkHCongr(v___x_2805_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
if (lean_obj_tag(v___x_2818_) == 0)
{
lean_object* v_a_2819_; lean_object* v_proof_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; 
v_a_2819_ = lean_ctor_get(v___x_2818_, 0);
lean_inc(v_a_2819_);
lean_dec_ref_known(v___x_2818_, 1);
v_proof_2820_ = lean_ctor_get(v_a_2819_, 1);
lean_inc_ref(v_proof_2820_);
lean_dec(v_a_2819_);
lean_inc_ref(v_e_x27_2793_);
lean_inc_ref(v_struct_2314_);
v___x_2821_ = l_Lean_mkApp3(v_proof_2820_, v_struct_2314_, v_e_x27_2793_, v_proof_2794_);
v___x_2822_ = l_Lean_Meta_mkEqOfHEq(v___x_2821_, v___x_2559_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
if (lean_obj_tag(v___x_2822_) == 0)
{
lean_object* v_a_2823_; uint8_t v___x_2824_; 
v_a_2823_ = lean_ctor_get(v___x_2822_, 0);
lean_inc(v_a_2823_);
lean_dec_ref_known(v___x_2822_, 1);
v___x_2824_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_2314_, v_e_x27_2793_);
if (v___x_2824_ == 0)
{
lean_object* v___x_2825_; 
lean_inc(v_idx_2313_);
lean_inc(v_typeName_2312_);
lean_dec_ref_known(v_e_2287_, 3);
v___x_2825_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_typeName_2312_, v_idx_2313_, v_e_x27_2793_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_object* v_a_2826_; 
v_a_2826_ = lean_ctor_get(v___x_2825_, 0);
lean_inc(v_a_2826_);
lean_dec_ref_known(v___x_2825_, 1);
v___y_2637_ = v_contextDependent_2795_;
v___y_2638_ = v_a_2823_;
v___y_2639_ = v___x_2768_;
v___y_2640_ = v___y_2666_;
v___y_2641_ = v_a_2668_;
v_a_2642_ = v_a_2826_;
goto v___jp_2636_;
}
else
{
lean_object* v_a_2827_; 
lean_dec(v_a_2823_);
v_a_2827_ = lean_ctor_get(v___x_2825_, 0);
lean_inc(v_a_2827_);
lean_dec_ref_known(v___x_2825_, 1);
v___y_2653_ = v___x_2768_;
v___y_2654_ = v___y_2666_;
v___y_2655_ = v_a_2668_;
v_a_2656_ = v_a_2827_;
goto v___jp_2652_;
}
}
else
{
lean_dec_ref(v_e_x27_2793_);
v___y_2637_ = v_contextDependent_2795_;
v___y_2638_ = v_a_2823_;
v___y_2639_ = v___x_2768_;
v___y_2640_ = v___y_2666_;
v___y_2641_ = v_a_2668_;
v_a_2642_ = v_e_2287_;
goto v___jp_2636_;
}
}
else
{
lean_object* v_a_2828_; 
lean_dec_ref(v_e_x27_2793_);
lean_dec_ref_known(v_e_2287_, 3);
v_a_2828_ = lean_ctor_get(v___x_2822_, 0);
lean_inc(v_a_2828_);
lean_dec_ref_known(v___x_2822_, 1);
v___y_2653_ = v___x_2768_;
v___y_2654_ = v___y_2666_;
v___y_2655_ = v_a_2668_;
v_a_2656_ = v_a_2828_;
goto v___jp_2652_;
}
}
else
{
lean_object* v_a_2829_; 
lean_dec_ref(v_proof_2794_);
lean_dec_ref(v_e_x27_2793_);
lean_dec_ref_known(v_e_2287_, 3);
v_a_2829_ = lean_ctor_get(v___x_2818_, 0);
lean_inc(v_a_2829_);
lean_dec_ref_known(v___x_2818_, 1);
v___y_2653_ = v___x_2768_;
v___y_2654_ = v___y_2666_;
v___y_2655_ = v_a_2668_;
v_a_2656_ = v_a_2829_;
goto v___jp_2652_;
}
}
}
else
{
lean_object* v_a_2830_; 
lean_dec_ref(v___x_2805_);
lean_dec_ref(v_proof_2794_);
lean_dec_ref(v_e_x27_2793_);
lean_dec_ref_known(v_e_2287_, 3);
v_a_2830_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_a_2830_);
lean_dec_ref_known(v___x_2814_, 1);
v___y_2653_ = v___x_2768_;
v___y_2654_ = v___y_2666_;
v___y_2655_ = v_a_2668_;
v_a_2656_ = v_a_2830_;
goto v___jp_2652_;
}
}
else
{
lean_object* v_val_2831_; lean_object* v___x_2832_; 
lean_dec_ref(v___x_2805_);
lean_dec_ref(v_proof_2794_);
lean_dec_ref(v_e_x27_2793_);
lean_dec_ref_known(v_e_2287_, 3);
v_val_2831_ = lean_ctor_get(v_a_2813_, 0);
lean_inc(v_val_2831_);
lean_dec_ref_known(v_a_2813_, 1);
v___x_2832_ = l_Lean_Meta_Sym_shareCommonInc(v_val_2831_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
if (lean_obj_tag(v___x_2832_) == 0)
{
lean_object* v_a_2833_; lean_object* v___x_2834_; 
v_a_2833_ = lean_ctor_get(v___x_2832_, 0);
lean_inc_n(v_a_2833_, 2);
lean_dec_ref_known(v___x_2832_, 1);
v___x_2834_ = l_Lean_Meta_Sym_mkEqRefl(v_a_2833_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
if (lean_obj_tag(v___x_2834_) == 0)
{
lean_object* v_a_2835_; lean_object* v___x_2837_; 
v_a_2835_ = lean_ctor_get(v___x_2834_, 0);
lean_inc(v_a_2835_);
lean_dec_ref_known(v___x_2834_, 1);
if (v_isShared_2798_ == 0)
{
lean_ctor_set(v___x_2797_, 1, v_a_2835_);
lean_ctor_set(v___x_2797_, 0, v_a_2833_);
v___x_2837_ = v___x_2797_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v_a_2833_);
lean_ctor_set(v_reuseFailAlloc_2838_, 1, v_a_2835_);
v___x_2837_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
lean_ctor_set_uint8(v___x_2837_, sizeof(void*)*2, v_contextDependent_2795_);
lean_ctor_set_uint8(v___x_2837_, sizeof(void*)*2 + 1, v___x_2559_);
v___y_2631_ = v___x_2768_;
v___y_2632_ = v___y_2666_;
v___y_2633_ = v_a_2668_;
v_a_2634_ = v___x_2837_;
goto v___jp_2630_;
}
}
else
{
lean_object* v_a_2839_; 
lean_dec(v_a_2833_);
lean_del_object(v___x_2797_);
v_a_2839_ = lean_ctor_get(v___x_2834_, 0);
lean_inc(v_a_2839_);
lean_dec_ref_known(v___x_2834_, 1);
v___y_2653_ = v___x_2768_;
v___y_2654_ = v___y_2666_;
v___y_2655_ = v_a_2668_;
v_a_2656_ = v_a_2839_;
goto v___jp_2652_;
}
}
else
{
lean_object* v_a_2840_; 
lean_del_object(v___x_2797_);
v_a_2840_ = lean_ctor_get(v___x_2832_, 0);
lean_inc(v_a_2840_);
lean_dec_ref_known(v___x_2832_, 1);
v___y_2653_ = v___x_2768_;
v___y_2654_ = v___y_2666_;
v___y_2655_ = v_a_2668_;
v_a_2656_ = v_a_2840_;
goto v___jp_2652_;
}
}
}
else
{
lean_object* v_a_2841_; 
lean_dec_ref(v___x_2805_);
lean_del_object(v___x_2797_);
lean_dec_ref(v_proof_2794_);
lean_dec_ref(v_e_x27_2793_);
lean_dec_ref_known(v_e_2287_, 3);
v_a_2841_ = lean_ctor_get(v___x_2812_, 0);
lean_inc(v_a_2841_);
lean_dec_ref_known(v___x_2812_, 1);
v___y_2653_ = v___x_2768_;
v___y_2654_ = v___y_2666_;
v___y_2655_ = v_a_2668_;
v_a_2656_ = v_a_2841_;
goto v___jp_2652_;
}
}
else
{
lean_del_object(v___x_2797_);
if (lean_obj_tag(v_a_2807_) == 7)
{
lean_object* v_binderType_2842_; lean_object* v_body_2843_; lean_object* v___x_2844_; 
v_binderType_2842_ = lean_ctor_get(v_a_2807_, 1);
lean_inc_ref_n(v_binderType_2842_, 2);
v_body_2843_ = lean_ctor_get(v_a_2807_, 2);
lean_inc_ref(v_body_2843_);
lean_dec_ref_known(v_a_2807_, 3);
v___x_2844_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_2842_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
if (lean_obj_tag(v___x_2844_) == 0)
{
lean_object* v_a_2845_; lean_object* v___x_2846_; 
v_a_2845_ = lean_ctor_get(v___x_2844_, 0);
lean_inc(v_a_2845_);
lean_dec_ref_known(v___x_2844_, 1);
lean_inc_ref(v_body_2843_);
v___x_2846_ = l_Lean_Meta_Sym_getLevel___redArg(v_body_2843_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
if (lean_obj_tag(v___x_2846_) == 0)
{
lean_object* v_a_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; uint8_t v___x_2854_; 
v_a_2847_ = lean_ctor_get(v___x_2846_, 0);
lean_inc(v_a_2847_);
lean_dec_ref_known(v___x_2846_, 1);
v___x_2848_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4));
v___x_2849_ = lean_box(0);
v___x_2850_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2850_, 0, v_a_2847_);
lean_ctor_set(v___x_2850_, 1, v___x_2849_);
v___x_2851_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2851_, 0, v_a_2845_);
lean_ctor_set(v___x_2851_, 1, v___x_2850_);
v___x_2852_ = l_Lean_mkConst(v___x_2848_, v___x_2851_);
lean_inc_ref(v_e_x27_2793_);
lean_inc_ref(v_struct_2314_);
v___x_2853_ = l_Lean_mkApp6(v___x_2852_, v_binderType_2842_, v_body_2843_, v_struct_2314_, v_e_x27_2793_, v___x_2805_, v_proof_2794_);
v___x_2854_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_2314_, v_e_x27_2793_);
if (v___x_2854_ == 0)
{
lean_object* v___x_2855_; 
lean_inc(v_idx_2313_);
lean_inc(v_typeName_2312_);
lean_dec_ref_known(v_e_2287_, 3);
v___x_2855_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_typeName_2312_, v_idx_2313_, v_e_x27_2793_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
if (lean_obj_tag(v___x_2855_) == 0)
{
lean_object* v_a_2856_; 
v_a_2856_ = lean_ctor_get(v___x_2855_, 0);
lean_inc(v_a_2856_);
lean_dec_ref_known(v___x_2855_, 1);
v___y_2645_ = v_contextDependent_2795_;
v___y_2646_ = v___x_2768_;
v___y_2647_ = v___y_2666_;
v___y_2648_ = v___x_2853_;
v___y_2649_ = v_a_2668_;
v_a_2650_ = v_a_2856_;
goto v___jp_2644_;
}
else
{
lean_object* v_a_2857_; 
lean_dec_ref(v___x_2853_);
v_a_2857_ = lean_ctor_get(v___x_2855_, 0);
lean_inc(v_a_2857_);
lean_dec_ref_known(v___x_2855_, 1);
v___y_2653_ = v___x_2768_;
v___y_2654_ = v___y_2666_;
v___y_2655_ = v_a_2668_;
v_a_2656_ = v_a_2857_;
goto v___jp_2652_;
}
}
else
{
lean_dec_ref(v_e_x27_2793_);
v___y_2645_ = v_contextDependent_2795_;
v___y_2646_ = v___x_2768_;
v___y_2647_ = v___y_2666_;
v___y_2648_ = v___x_2853_;
v___y_2649_ = v_a_2668_;
v_a_2650_ = v_e_2287_;
goto v___jp_2644_;
}
}
else
{
lean_object* v_a_2858_; 
lean_dec(v_a_2845_);
lean_dec_ref(v_body_2843_);
lean_dec_ref(v_binderType_2842_);
lean_dec_ref(v___x_2805_);
lean_dec_ref(v_proof_2794_);
lean_dec_ref(v_e_x27_2793_);
lean_dec_ref_known(v_e_2287_, 3);
v_a_2858_ = lean_ctor_get(v___x_2846_, 0);
lean_inc(v_a_2858_);
lean_dec_ref_known(v___x_2846_, 1);
v___y_2653_ = v___x_2768_;
v___y_2654_ = v___y_2666_;
v___y_2655_ = v_a_2668_;
v_a_2656_ = v_a_2858_;
goto v___jp_2652_;
}
}
else
{
lean_object* v_a_2859_; 
lean_dec_ref(v_body_2843_);
lean_dec_ref(v_binderType_2842_);
lean_dec_ref(v___x_2805_);
lean_dec_ref(v_proof_2794_);
lean_dec_ref(v_e_x27_2793_);
lean_dec_ref_known(v_e_2287_, 3);
v_a_2859_ = lean_ctor_get(v___x_2844_, 0);
lean_inc(v_a_2859_);
lean_dec_ref_known(v___x_2844_, 1);
v___y_2653_ = v___x_2768_;
v___y_2654_ = v___y_2666_;
v___y_2655_ = v_a_2668_;
v_a_2656_ = v_a_2859_;
goto v___jp_2652_;
}
}
else
{
lean_object* v___x_2860_; lean_object* v___x_2861_; 
lean_dec(v_a_2807_);
lean_dec_ref(v___x_2805_);
lean_dec_ref(v_proof_2794_);
lean_dec_ref(v_e_x27_2793_);
lean_dec_ref_known(v_e_2287_, 3);
v___x_2860_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8);
v___x_2861_ = l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1(v___x_2860_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
v___y_2659_ = v___x_2768_;
v___y_2660_ = v___y_2666_;
v___y_2661_ = v_a_2668_;
v___y_2662_ = v___x_2861_;
goto v___jp_2658_;
}
}
}
else
{
lean_object* v_a_2862_; 
lean_dec_ref(v___x_2805_);
lean_del_object(v___x_2797_);
lean_dec_ref(v_proof_2794_);
lean_dec_ref(v_e_x27_2793_);
lean_dec_ref_known(v_e_2287_, 3);
v_a_2862_ = lean_ctor_get(v___x_2806_, 0);
lean_inc(v_a_2862_);
lean_dec_ref_known(v___x_2806_, 1);
v___y_2653_ = v___x_2768_;
v___y_2654_ = v___y_2666_;
v___y_2655_ = v_a_2668_;
v_a_2656_ = v_a_2862_;
goto v___jp_2652_;
}
}
else
{
lean_object* v_a_2863_; 
lean_del_object(v___x_2797_);
lean_dec_ref(v_proof_2794_);
lean_dec_ref(v_e_x27_2793_);
lean_dec_ref_known(v_e_2287_, 3);
v_a_2863_ = lean_ctor_get(v___x_2799_, 0);
lean_inc(v_a_2863_);
lean_dec_ref_known(v___x_2799_, 1);
v___y_2653_ = v___x_2768_;
v___y_2654_ = v___y_2666_;
v___y_2655_ = v_a_2668_;
v_a_2656_ = v_a_2863_;
goto v___jp_2652_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_2287_, 3);
v___y_2659_ = v___x_2768_;
v___y_2660_ = v___y_2666_;
v___y_2661_ = v_a_2668_;
v___y_2662_ = v___x_2769_;
goto v___jp_2658_;
}
}
}
v___jp_2865_:
{
lean_object* v___x_2867_; uint8_t v___x_2868_; 
v___x_2867_ = l_Lean_trace_profiler;
v___x_2868_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_2556_, v___x_2867_);
if (v___x_2868_ == 0)
{
lean_object* v___x_2869_; 
lean_dec_ref(v___f_2560_);
lean_inc(v_a_2296_);
lean_inc_ref(v_a_2295_);
lean_inc(v_a_2294_);
lean_inc_ref(v_a_2293_);
lean_inc(v_a_2292_);
lean_inc_ref(v_a_2291_);
lean_inc(v_a_2290_);
lean_inc_ref(v_a_2289_);
lean_inc(v_a_2288_);
lean_inc_ref(v_struct_2314_);
v___x_2869_ = lean_sym_simp(v_struct_2314_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
if (lean_obj_tag(v___x_2869_) == 0)
{
lean_object* v_a_2870_; 
v_a_2870_ = lean_ctor_get(v___x_2869_, 0);
lean_inc(v_a_2870_);
lean_dec_ref_known(v___x_2869_, 1);
v_res_2316_ = v_a_2870_;
v___y_2317_ = v_a_2288_;
v___y_2318_ = v_a_2289_;
v___y_2319_ = v_a_2290_;
v___y_2320_ = v_a_2291_;
v___y_2321_ = v_a_2292_;
v___y_2322_ = v_a_2293_;
v___y_2323_ = v_a_2294_;
v___y_2324_ = v_a_2295_;
v___y_2325_ = v_a_2296_;
goto v___jp_2315_;
}
else
{
lean_dec_ref_known(v_e_2287_, 3);
return v___x_2869_;
}
}
else
{
v___y_2666_ = v_a_2866_;
goto v___jp_2665_;
}
}
}
else
{
lean_object* v___x_2873_; 
lean_inc(v_a_2296_);
lean_inc_ref(v_a_2295_);
lean_inc(v_a_2294_);
lean_inc_ref(v_a_2293_);
lean_inc(v_a_2292_);
lean_inc_ref(v_a_2291_);
lean_inc(v_a_2290_);
lean_inc_ref(v_a_2289_);
lean_inc(v_a_2288_);
lean_inc_ref(v_struct_2314_);
v___x_2873_ = lean_sym_simp(v_struct_2314_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
if (lean_obj_tag(v___x_2873_) == 0)
{
lean_object* v_a_2874_; 
v_a_2874_ = lean_ctor_get(v___x_2873_, 0);
lean_inc(v_a_2874_);
lean_dec_ref_known(v___x_2873_, 1);
v_res_2316_ = v_a_2874_;
v___y_2317_ = v_a_2288_;
v___y_2318_ = v_a_2289_;
v___y_2319_ = v_a_2290_;
v___y_2320_ = v_a_2291_;
v___y_2321_ = v_a_2292_;
v___y_2322_ = v_a_2293_;
v___y_2323_ = v_a_2294_;
v___y_2324_ = v_a_2295_;
v___y_2325_ = v_a_2296_;
goto v___jp_2315_;
}
else
{
lean_dec_ref_known(v_e_2287_, 3);
return v___x_2873_;
}
}
v___jp_2315_:
{
if (lean_obj_tag(v_res_2316_) == 0)
{
uint8_t v_contextDependent_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2384_; 
v_contextDependent_2326_ = lean_ctor_get_uint8(v_res_2316_, 1);
v_isSharedCheck_2384_ = !lean_is_exclusive(v_res_2316_);
if (v_isSharedCheck_2384_ == 0)
{
v___x_2328_ = v_res_2316_;
v_isShared_2329_ = v_isSharedCheck_2384_;
goto v_resetjp_2327_;
}
else
{
lean_dec(v_res_2316_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2384_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
uint8_t v___x_2330_; lean_object* v___x_2331_; lean_object* v___f_2332_; lean_object* v___x_2333_; 
v___x_2330_ = 1;
v___x_2331_ = lean_box(v___x_2330_);
v___f_2332_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2332_, 0, v___x_2331_);
lean_closure_set(v___f_2332_, 1, v_e_2287_);
v___x_2333_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___f_2332_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
if (lean_obj_tag(v___x_2333_) == 0)
{
lean_object* v_a_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2375_; 
v_a_2334_ = lean_ctor_get(v___x_2333_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2336_ = v___x_2333_;
v_isShared_2337_ = v_isSharedCheck_2375_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_a_2334_);
lean_dec(v___x_2333_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2375_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
if (lean_obj_tag(v_a_2334_) == 1)
{
lean_object* v_val_2338_; lean_object* v___x_2339_; 
lean_del_object(v___x_2336_);
lean_del_object(v___x_2328_);
v_val_2338_ = lean_ctor_get(v_a_2334_, 0);
lean_inc(v_val_2338_);
lean_dec_ref_known(v_a_2334_, 1);
v___x_2339_ = l_Lean_Meta_Sym_shareCommonInc(v_val_2338_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v_a_2340_; lean_object* v___x_2341_; 
v_a_2340_ = lean_ctor_get(v___x_2339_, 0);
lean_inc_n(v_a_2340_, 2);
lean_dec_ref_known(v___x_2339_, 1);
v___x_2341_ = l_Lean_Meta_Sym_mkEqRefl(v_a_2340_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
if (lean_obj_tag(v___x_2341_) == 0)
{
lean_object* v_a_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2351_; 
v_a_2342_ = lean_ctor_get(v___x_2341_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___x_2341_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2344_ = v___x_2341_;
v_isShared_2345_ = v_isSharedCheck_2351_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_a_2342_);
lean_dec(v___x_2341_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2351_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
uint8_t v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2349_; 
v___x_2346_ = 0;
v___x_2347_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2347_, 0, v_a_2340_);
lean_ctor_set(v___x_2347_, 1, v_a_2342_);
lean_ctor_set_uint8(v___x_2347_, sizeof(void*)*2, v_contextDependent_2326_);
lean_ctor_set_uint8(v___x_2347_, sizeof(void*)*2 + 1, v___x_2346_);
if (v_isShared_2345_ == 0)
{
lean_ctor_set(v___x_2344_, 0, v___x_2347_);
v___x_2349_ = v___x_2344_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v___x_2347_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
}
}
}
else
{
lean_object* v_a_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2359_; 
lean_dec(v_a_2340_);
v_a_2352_ = lean_ctor_get(v___x_2341_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2341_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2354_ = v___x_2341_;
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_a_2352_);
lean_dec(v___x_2341_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2357_; 
if (v_isShared_2355_ == 0)
{
v___x_2357_ = v___x_2354_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_a_2352_);
v___x_2357_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
return v___x_2357_;
}
}
}
}
else
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2367_; 
v_a_2360_ = lean_ctor_get(v___x_2339_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2362_ = v___x_2339_;
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2339_);
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
uint8_t v___x_2368_; lean_object* v___x_2370_; 
lean_dec(v_a_2334_);
v___x_2368_ = 1;
if (v_isShared_2329_ == 0)
{
v___x_2370_ = v___x_2328_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v_reuseFailAlloc_2374_, 1, v_contextDependent_2326_);
v___x_2370_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
lean_object* v___x_2372_; 
lean_ctor_set_uint8(v___x_2370_, 0, v___x_2368_);
if (v_isShared_2337_ == 0)
{
lean_ctor_set(v___x_2336_, 0, v___x_2370_);
v___x_2372_ = v___x_2336_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v___x_2370_);
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
lean_object* v_a_2376_; lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2383_; 
lean_del_object(v___x_2328_);
v_a_2376_ = lean_ctor_get(v___x_2333_, 0);
v_isSharedCheck_2383_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2383_ == 0)
{
v___x_2378_ = v___x_2333_;
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_a_2376_);
lean_dec(v___x_2333_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
lean_object* v___x_2381_; 
if (v_isShared_2379_ == 0)
{
v___x_2381_ = v___x_2378_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v_a_2376_);
v___x_2381_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
return v___x_2381_;
}
}
}
}
}
else
{
lean_object* v_e_x27_2385_; lean_object* v_proof_2386_; uint8_t v_contextDependent_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2555_; 
v_e_x27_2385_ = lean_ctor_get(v_res_2316_, 0);
v_proof_2386_ = lean_ctor_get(v_res_2316_, 1);
v_contextDependent_2387_ = lean_ctor_get_uint8(v_res_2316_, sizeof(void*)*2 + 1);
v_isSharedCheck_2555_ = !lean_is_exclusive(v_res_2316_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2389_ = v_res_2316_;
v_isShared_2390_ = v_isSharedCheck_2555_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_proof_2386_);
lean_inc(v_e_x27_2385_);
lean_dec(v_res_2316_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2555_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___x_2391_; 
lean_inc_ref(v_e_x27_2385_);
v___x_2391_ = l_Lean_Meta_Sym_inferType(v_e_x27_2385_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
if (lean_obj_tag(v___x_2391_) == 0)
{
lean_object* v_a_2392_; lean_object* v___x_2393_; uint8_t v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; 
v_a_2392_ = lean_ctor_get(v___x_2391_, 0);
lean_inc(v_a_2392_);
lean_dec_ref_known(v___x_2391_, 1);
v___x_2393_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__1));
v___x_2394_ = 0;
v___x_2395_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2);
lean_inc(v_idx_2313_);
lean_inc(v_typeName_2312_);
v___x_2396_ = l_Lean_Expr_proj___override(v_typeName_2312_, v_idx_2313_, v___x_2395_);
v___x_2397_ = l_Lean_mkLambda(v___x_2393_, v___x_2394_, v_a_2392_, v___x_2396_);
lean_inc_ref(v___x_2397_);
v___x_2398_ = l_Lean_Meta_Sym_inferType(v___x_2397_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
if (lean_obj_tag(v___x_2398_) == 0)
{
lean_object* v_a_2399_; uint8_t v___x_2400_; 
v_a_2399_ = lean_ctor_get(v___x_2398_, 0);
lean_inc(v_a_2399_);
lean_dec_ref_known(v___x_2398_, 1);
v___x_2400_ = l_Lean_Expr_isArrow(v_a_2399_);
if (v___x_2400_ == 0)
{
uint8_t v___x_2401_; lean_object* v___x_2402_; lean_object* v___f_2403_; lean_object* v___x_2404_; 
lean_dec(v_a_2399_);
v___x_2401_ = 1;
v___x_2402_ = lean_box(v___x_2401_);
lean_inc_ref(v_e_2287_);
v___f_2403_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2403_, 0, v___x_2402_);
lean_closure_set(v___f_2403_, 1, v_e_2287_);
v___x_2404_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___f_2403_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
if (lean_obj_tag(v___x_2404_) == 0)
{
lean_object* v_a_2405_; 
v_a_2405_ = lean_ctor_get(v___x_2404_, 0);
lean_inc(v_a_2405_);
lean_dec_ref_known(v___x_2404_, 1);
if (lean_obj_tag(v_a_2405_) == 0)
{
lean_object* v___x_2406_; 
lean_del_object(v___x_2389_);
lean_inc_ref(v_e_x27_2385_);
lean_inc_ref(v_struct_2314_);
v___x_2406_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_struct_2314_, v_e_x27_2385_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
if (lean_obj_tag(v___x_2406_) == 0)
{
lean_object* v_a_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2450_; 
v_a_2407_ = lean_ctor_get(v___x_2406_, 0);
v_isSharedCheck_2450_ = !lean_is_exclusive(v___x_2406_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2409_ = v___x_2406_;
v_isShared_2410_ = v_isSharedCheck_2450_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_a_2407_);
lean_dec(v___x_2406_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2450_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
uint8_t v___x_2411_; 
v___x_2411_ = lean_unbox(v_a_2407_);
lean_dec(v_a_2407_);
if (v___x_2411_ == 0)
{
uint8_t v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2415_; 
lean_dec_ref(v___x_2397_);
lean_dec_ref(v_proof_2386_);
lean_dec_ref(v_e_x27_2385_);
lean_dec_ref_known(v_e_2287_, 3);
v___x_2412_ = 1;
v___x_2413_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2413_, 0, v___x_2412_);
lean_ctor_set_uint8(v___x_2413_, 1, v_contextDependent_2387_);
if (v_isShared_2410_ == 0)
{
lean_ctor_set(v___x_2409_, 0, v___x_2413_);
v___x_2415_ = v___x_2409_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v___x_2413_);
v___x_2415_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
return v___x_2415_;
}
}
else
{
lean_object* v___x_2417_; 
lean_del_object(v___x_2409_);
v___x_2417_ = l_Lean_Meta_mkHCongr(v___x_2397_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
if (lean_obj_tag(v___x_2417_) == 0)
{
lean_object* v_a_2418_; lean_object* v_proof_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; 
v_a_2418_ = lean_ctor_get(v___x_2417_, 0);
lean_inc(v_a_2418_);
lean_dec_ref_known(v___x_2417_, 1);
v_proof_2419_ = lean_ctor_get(v_a_2418_, 1);
lean_inc_ref(v_proof_2419_);
lean_dec(v_a_2418_);
lean_inc_ref(v_e_x27_2385_);
lean_inc_ref(v_struct_2314_);
v___x_2420_ = l_Lean_mkApp3(v_proof_2419_, v_struct_2314_, v_e_x27_2385_, v_proof_2386_);
v___x_2421_ = l_Lean_Meta_mkEqOfHEq(v___x_2420_, v___x_2400_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
if (lean_obj_tag(v___x_2421_) == 0)
{
lean_object* v_a_2422_; uint8_t v___x_2423_; 
v_a_2422_ = lean_ctor_get(v___x_2421_, 0);
lean_inc(v_a_2422_);
lean_dec_ref_known(v___x_2421_, 1);
v___x_2423_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_2314_, v_e_x27_2385_);
if (v___x_2423_ == 0)
{
lean_object* v___x_2424_; 
lean_inc(v_idx_2313_);
lean_inc(v_typeName_2312_);
lean_dec_ref_known(v_e_2287_, 3);
v___x_2424_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_typeName_2312_, v_idx_2313_, v_e_x27_2385_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
if (lean_obj_tag(v___x_2424_) == 0)
{
lean_object* v_a_2425_; 
v_a_2425_ = lean_ctor_get(v___x_2424_, 0);
lean_inc(v_a_2425_);
lean_dec_ref_known(v___x_2424_, 1);
v___y_2299_ = v___x_2400_;
v___y_2300_ = v_a_2422_;
v___y_2301_ = v_contextDependent_2387_;
v_a_2302_ = v_a_2425_;
goto v___jp_2298_;
}
else
{
lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2433_; 
lean_dec(v_a_2422_);
v_a_2426_ = lean_ctor_get(v___x_2424_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2428_ = v___x_2424_;
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_dec(v___x_2424_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v___x_2431_; 
if (v_isShared_2429_ == 0)
{
v___x_2431_ = v___x_2428_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_a_2426_);
v___x_2431_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
return v___x_2431_;
}
}
}
}
else
{
lean_dec_ref(v_e_x27_2385_);
v___y_2299_ = v___x_2400_;
v___y_2300_ = v_a_2422_;
v___y_2301_ = v_contextDependent_2387_;
v_a_2302_ = v_e_2287_;
goto v___jp_2298_;
}
}
else
{
lean_object* v_a_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2441_; 
lean_dec_ref(v_e_x27_2385_);
lean_dec_ref_known(v_e_2287_, 3);
v_a_2434_ = lean_ctor_get(v___x_2421_, 0);
v_isSharedCheck_2441_ = !lean_is_exclusive(v___x_2421_);
if (v_isSharedCheck_2441_ == 0)
{
v___x_2436_ = v___x_2421_;
v_isShared_2437_ = v_isSharedCheck_2441_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_a_2434_);
lean_dec(v___x_2421_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2441_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
lean_object* v___x_2439_; 
if (v_isShared_2437_ == 0)
{
v___x_2439_ = v___x_2436_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v_a_2434_);
v___x_2439_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
return v___x_2439_;
}
}
}
}
else
{
lean_object* v_a_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2449_; 
lean_dec_ref(v_proof_2386_);
lean_dec_ref(v_e_x27_2385_);
lean_dec_ref_known(v_e_2287_, 3);
v_a_2442_ = lean_ctor_get(v___x_2417_, 0);
v_isSharedCheck_2449_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2449_ == 0)
{
v___x_2444_ = v___x_2417_;
v_isShared_2445_ = v_isSharedCheck_2449_;
goto v_resetjp_2443_;
}
else
{
lean_inc(v_a_2442_);
lean_dec(v___x_2417_);
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
}
}
else
{
lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2458_; 
lean_dec_ref(v___x_2397_);
lean_dec_ref(v_proof_2386_);
lean_dec_ref(v_e_x27_2385_);
lean_dec_ref_known(v_e_2287_, 3);
v_a_2451_ = lean_ctor_get(v___x_2406_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2406_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2453_ = v___x_2406_;
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v___x_2406_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2456_; 
if (v_isShared_2454_ == 0)
{
v___x_2456_ = v___x_2453_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_a_2451_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
}
}
else
{
lean_object* v_val_2459_; lean_object* v___x_2460_; 
lean_dec_ref(v___x_2397_);
lean_dec_ref(v_proof_2386_);
lean_dec_ref(v_e_x27_2385_);
lean_dec_ref_known(v_e_2287_, 3);
v_val_2459_ = lean_ctor_get(v_a_2405_, 0);
lean_inc(v_val_2459_);
lean_dec_ref_known(v_a_2405_, 1);
v___x_2460_ = l_Lean_Meta_Sym_shareCommonInc(v_val_2459_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
if (lean_obj_tag(v___x_2460_) == 0)
{
lean_object* v_a_2461_; lean_object* v___x_2462_; 
v_a_2461_ = lean_ctor_get(v___x_2460_, 0);
lean_inc_n(v_a_2461_, 2);
lean_dec_ref_known(v___x_2460_, 1);
v___x_2462_ = l_Lean_Meta_Sym_mkEqRefl(v_a_2461_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
if (lean_obj_tag(v___x_2462_) == 0)
{
lean_object* v_a_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2473_; 
v_a_2463_ = lean_ctor_get(v___x_2462_, 0);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___x_2462_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2465_ = v___x_2462_;
v_isShared_2466_ = v_isSharedCheck_2473_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_a_2463_);
lean_dec(v___x_2462_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2473_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v___x_2468_; 
if (v_isShared_2390_ == 0)
{
lean_ctor_set(v___x_2389_, 1, v_a_2463_);
lean_ctor_set(v___x_2389_, 0, v_a_2461_);
v___x_2468_ = v___x_2389_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_a_2461_);
lean_ctor_set(v_reuseFailAlloc_2472_, 1, v_a_2463_);
v___x_2468_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
lean_object* v___x_2470_; 
lean_ctor_set_uint8(v___x_2468_, sizeof(void*)*2, v_contextDependent_2387_);
lean_ctor_set_uint8(v___x_2468_, sizeof(void*)*2 + 1, v___x_2400_);
if (v_isShared_2466_ == 0)
{
lean_ctor_set(v___x_2465_, 0, v___x_2468_);
v___x_2470_ = v___x_2465_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v___x_2468_);
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
lean_object* v_a_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2481_; 
lean_dec(v_a_2461_);
lean_del_object(v___x_2389_);
v_a_2474_ = lean_ctor_get(v___x_2462_, 0);
v_isSharedCheck_2481_ = !lean_is_exclusive(v___x_2462_);
if (v_isSharedCheck_2481_ == 0)
{
v___x_2476_ = v___x_2462_;
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_a_2474_);
lean_dec(v___x_2462_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
lean_object* v___x_2479_; 
if (v_isShared_2477_ == 0)
{
v___x_2479_ = v___x_2476_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v_a_2474_);
v___x_2479_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
return v___x_2479_;
}
}
}
}
else
{
lean_object* v_a_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2489_; 
lean_del_object(v___x_2389_);
v_a_2482_ = lean_ctor_get(v___x_2460_, 0);
v_isSharedCheck_2489_ = !lean_is_exclusive(v___x_2460_);
if (v_isSharedCheck_2489_ == 0)
{
v___x_2484_ = v___x_2460_;
v_isShared_2485_ = v_isSharedCheck_2489_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_a_2482_);
lean_dec(v___x_2460_);
v___x_2484_ = lean_box(0);
v_isShared_2485_ = v_isSharedCheck_2489_;
goto v_resetjp_2483_;
}
v_resetjp_2483_:
{
lean_object* v___x_2487_; 
if (v_isShared_2485_ == 0)
{
v___x_2487_ = v___x_2484_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v_a_2482_);
v___x_2487_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
return v___x_2487_;
}
}
}
}
}
else
{
lean_object* v_a_2490_; lean_object* v___x_2492_; uint8_t v_isShared_2493_; uint8_t v_isSharedCheck_2497_; 
lean_dec_ref(v___x_2397_);
lean_del_object(v___x_2389_);
lean_dec_ref(v_proof_2386_);
lean_dec_ref(v_e_x27_2385_);
lean_dec_ref_known(v_e_2287_, 3);
v_a_2490_ = lean_ctor_get(v___x_2404_, 0);
v_isSharedCheck_2497_ = !lean_is_exclusive(v___x_2404_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2492_ = v___x_2404_;
v_isShared_2493_ = v_isSharedCheck_2497_;
goto v_resetjp_2491_;
}
else
{
lean_inc(v_a_2490_);
lean_dec(v___x_2404_);
v___x_2492_ = lean_box(0);
v_isShared_2493_ = v_isSharedCheck_2497_;
goto v_resetjp_2491_;
}
v_resetjp_2491_:
{
lean_object* v___x_2495_; 
if (v_isShared_2493_ == 0)
{
v___x_2495_ = v___x_2492_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_a_2490_);
v___x_2495_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
return v___x_2495_;
}
}
}
}
else
{
lean_del_object(v___x_2389_);
if (lean_obj_tag(v_a_2399_) == 7)
{
lean_object* v_binderType_2498_; lean_object* v_body_2499_; lean_object* v___x_2500_; 
v_binderType_2498_ = lean_ctor_get(v_a_2399_, 1);
lean_inc_ref_n(v_binderType_2498_, 2);
v_body_2499_ = lean_ctor_get(v_a_2399_, 2);
lean_inc_ref(v_body_2499_);
lean_dec_ref_known(v_a_2399_, 3);
v___x_2500_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_2498_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
if (lean_obj_tag(v___x_2500_) == 0)
{
lean_object* v_a_2501_; lean_object* v___x_2502_; 
v_a_2501_ = lean_ctor_get(v___x_2500_, 0);
lean_inc(v_a_2501_);
lean_dec_ref_known(v___x_2500_, 1);
lean_inc_ref(v_body_2499_);
v___x_2502_ = l_Lean_Meta_Sym_getLevel___redArg(v_body_2499_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
if (lean_obj_tag(v___x_2502_) == 0)
{
lean_object* v_a_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; uint8_t v___x_2510_; 
v_a_2503_ = lean_ctor_get(v___x_2502_, 0);
lean_inc(v_a_2503_);
lean_dec_ref_known(v___x_2502_, 1);
v___x_2504_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4));
v___x_2505_ = lean_box(0);
v___x_2506_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2506_, 0, v_a_2503_);
lean_ctor_set(v___x_2506_, 1, v___x_2505_);
v___x_2507_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2507_, 0, v_a_2501_);
lean_ctor_set(v___x_2507_, 1, v___x_2506_);
v___x_2508_ = l_Lean_mkConst(v___x_2504_, v___x_2507_);
lean_inc_ref(v_e_x27_2385_);
lean_inc_ref(v_struct_2314_);
v___x_2509_ = l_Lean_mkApp6(v___x_2508_, v_binderType_2498_, v_body_2499_, v_struct_2314_, v_e_x27_2385_, v___x_2397_, v_proof_2386_);
v___x_2510_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_2314_, v_e_x27_2385_);
if (v___x_2510_ == 0)
{
lean_object* v___x_2511_; 
lean_inc(v_idx_2313_);
lean_inc(v_typeName_2312_);
lean_dec_ref_known(v_e_2287_, 3);
v___x_2511_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_typeName_2312_, v_idx_2313_, v_e_x27_2385_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
if (lean_obj_tag(v___x_2511_) == 0)
{
lean_object* v_a_2512_; 
v_a_2512_ = lean_ctor_get(v___x_2511_, 0);
lean_inc(v_a_2512_);
lean_dec_ref_known(v___x_2511_, 1);
v___y_2306_ = v_contextDependent_2387_;
v___y_2307_ = v___x_2509_;
v_a_2308_ = v_a_2512_;
goto v___jp_2305_;
}
else
{
lean_object* v_a_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2520_; 
lean_dec_ref(v___x_2509_);
v_a_2513_ = lean_ctor_get(v___x_2511_, 0);
v_isSharedCheck_2520_ = !lean_is_exclusive(v___x_2511_);
if (v_isSharedCheck_2520_ == 0)
{
v___x_2515_ = v___x_2511_;
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_a_2513_);
lean_dec(v___x_2511_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v___x_2518_; 
if (v_isShared_2516_ == 0)
{
v___x_2518_ = v___x_2515_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v_a_2513_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
}
}
else
{
lean_dec_ref(v_e_x27_2385_);
v___y_2306_ = v_contextDependent_2387_;
v___y_2307_ = v___x_2509_;
v_a_2308_ = v_e_2287_;
goto v___jp_2305_;
}
}
else
{
lean_object* v_a_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2528_; 
lean_dec(v_a_2501_);
lean_dec_ref(v_body_2499_);
lean_dec_ref(v_binderType_2498_);
lean_dec_ref(v___x_2397_);
lean_dec_ref(v_proof_2386_);
lean_dec_ref(v_e_x27_2385_);
lean_dec_ref_known(v_e_2287_, 3);
v_a_2521_ = lean_ctor_get(v___x_2502_, 0);
v_isSharedCheck_2528_ = !lean_is_exclusive(v___x_2502_);
if (v_isSharedCheck_2528_ == 0)
{
v___x_2523_ = v___x_2502_;
v_isShared_2524_ = v_isSharedCheck_2528_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_a_2521_);
lean_dec(v___x_2502_);
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
lean_dec_ref(v_body_2499_);
lean_dec_ref(v_binderType_2498_);
lean_dec_ref(v___x_2397_);
lean_dec_ref(v_proof_2386_);
lean_dec_ref(v_e_x27_2385_);
lean_dec_ref_known(v_e_2287_, 3);
v_a_2529_ = lean_ctor_get(v___x_2500_, 0);
v_isSharedCheck_2536_ = !lean_is_exclusive(v___x_2500_);
if (v_isSharedCheck_2536_ == 0)
{
v___x_2531_ = v___x_2500_;
v_isShared_2532_ = v_isSharedCheck_2536_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_a_2529_);
lean_dec(v___x_2500_);
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
else
{
lean_object* v___x_2537_; lean_object* v___x_2538_; 
lean_dec(v_a_2399_);
lean_dec_ref(v___x_2397_);
lean_dec_ref(v_proof_2386_);
lean_dec_ref(v_e_x27_2385_);
lean_dec_ref_known(v_e_2287_, 3);
v___x_2537_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8);
v___x_2538_ = l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1(v___x_2537_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
return v___x_2538_;
}
}
}
else
{
lean_object* v_a_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2546_; 
lean_dec_ref(v___x_2397_);
lean_del_object(v___x_2389_);
lean_dec_ref(v_proof_2386_);
lean_dec_ref(v_e_x27_2385_);
lean_dec_ref_known(v_e_2287_, 3);
v_a_2539_ = lean_ctor_get(v___x_2398_, 0);
v_isSharedCheck_2546_ = !lean_is_exclusive(v___x_2398_);
if (v_isSharedCheck_2546_ == 0)
{
v___x_2541_ = v___x_2398_;
v_isShared_2542_ = v_isSharedCheck_2546_;
goto v_resetjp_2540_;
}
else
{
lean_inc(v_a_2539_);
lean_dec(v___x_2398_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2546_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
lean_object* v___x_2544_; 
if (v_isShared_2542_ == 0)
{
v___x_2544_ = v___x_2541_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v_a_2539_);
v___x_2544_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
return v___x_2544_;
}
}
}
}
else
{
lean_object* v_a_2547_; lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2554_; 
lean_del_object(v___x_2389_);
lean_dec_ref(v_proof_2386_);
lean_dec_ref(v_e_x27_2385_);
lean_dec_ref_known(v_e_2287_, 3);
v_a_2547_ = lean_ctor_get(v___x_2391_, 0);
v_isSharedCheck_2554_ = !lean_is_exclusive(v___x_2391_);
if (v_isSharedCheck_2554_ == 0)
{
v___x_2549_ = v___x_2391_;
v_isShared_2550_ = v_isSharedCheck_2554_;
goto v_resetjp_2548_;
}
else
{
lean_inc(v_a_2547_);
lean_dec(v___x_2391_);
v___x_2549_ = lean_box(0);
v_isShared_2550_ = v_isSharedCheck_2554_;
goto v_resetjp_2548_;
}
v_resetjp_2548_:
{
lean_object* v___x_2552_; 
if (v_isShared_2550_ == 0)
{
v___x_2552_ = v___x_2549_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v_a_2547_);
v___x_2552_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
return v___x_2552_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2875_; lean_object* v___x_2876_; 
lean_dec_ref(v_e_2287_);
v___x_2875_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
v___x_2876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2876_, 0, v___x_2875_);
return v___x_2876_;
}
v___jp_2298_:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2303_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2303_, 0, v_a_2302_);
lean_ctor_set(v___x_2303_, 1, v___y_2300_);
lean_ctor_set_uint8(v___x_2303_, sizeof(void*)*2, v___y_2301_);
lean_ctor_set_uint8(v___x_2303_, sizeof(void*)*2 + 1, v___y_2299_);
v___x_2304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2303_);
return v___x_2304_;
}
v___jp_2305_:
{
uint8_t v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; 
v___x_2309_ = 0;
v___x_2310_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2310_, 0, v_a_2308_);
lean_ctor_set(v___x_2310_, 1, v___y_2307_);
lean_ctor_set_uint8(v___x_2310_, sizeof(void*)*2, v___y_2306_);
lean_ctor_set_uint8(v___x_2310_, sizeof(void*)*2 + 1, v___x_2309_);
v___x_2311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2311_, 0, v___x_2310_);
return v___x_2311_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___boxed(lean_object* v_e_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_){
_start:
{
lean_object* v_res_2888_; 
v_res_2888_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj(v_e_2877_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_);
lean_dec(v_a_2886_);
lean_dec_ref(v_a_2885_);
lean_dec(v_a_2884_);
lean_dec_ref(v_a_2883_);
lean_dec(v_a_2882_);
lean_dec_ref(v_a_2881_);
lean_dec(v_a_2880_);
lean_dec_ref(v_a_2879_);
lean_dec(v_a_2878_);
return v_res_2888_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5(lean_object* v_00_u03b1_2889_, lean_object* v_x_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_){
_start:
{
lean_object* v___x_2901_; 
v___x_2901_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5___redArg(v_x_2890_);
return v___x_2901_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5___boxed(lean_object* v_00_u03b1_2902_, lean_object* v_x_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_){
_start:
{
lean_object* v_res_2914_; 
v_res_2914_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5(v_00_u03b1_2902_, v_x_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_);
lean_dec(v___y_2912_);
lean_dec_ref(v___y_2911_);
lean_dec(v___y_2910_);
lean_dec_ref(v___y_2909_);
lean_dec(v___y_2908_);
lean_dec_ref(v___y_2907_);
lean_dec(v___y_2906_);
lean_dec_ref(v___y_2905_);
lean_dec(v___y_2904_);
return v_res_2914_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4(lean_object* v_oldTraces_2915_, lean_object* v_data_2916_, lean_object* v_ref_2917_, lean_object* v_msg_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
lean_object* v___x_2929_; 
v___x_2929_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4___redArg(v_oldTraces_2915_, v_data_2916_, v_ref_2917_, v_msg_2918_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_);
return v___x_2929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4___boxed(lean_object* v_oldTraces_2930_, lean_object* v_data_2931_, lean_object* v_ref_2932_, lean_object* v_msg_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_){
_start:
{
lean_object* v_res_2944_; 
v_res_2944_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4(v_oldTraces_2930_, v_data_2931_, v_ref_2932_, v_msg_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_);
lean_dec(v___y_2942_);
lean_dec_ref(v___y_2941_);
lean_dec(v___y_2940_);
lean_dec_ref(v___y_2939_);
lean_dec(v___y_2938_);
lean_dec_ref(v___y_2937_);
lean_dec(v___y_2936_);
lean_dec_ref(v___y_2935_);
lean_dec(v___y_2934_);
return v_res_2944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0_spec__1___redArg(lean_object* v_f_2945_, lean_object* v_a_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_){
_start:
{
lean_object* v___y_2955_; lean_object* v___x_2958_; uint8_t v_debug_2959_; 
v___x_2958_ = lean_st_ref_get(v___y_2948_);
v_debug_2959_ = lean_ctor_get_uint8(v___x_2958_, sizeof(void*)*11);
lean_dec(v___x_2958_);
if (v_debug_2959_ == 0)
{
v___y_2955_ = v___y_2948_;
goto v___jp_2954_;
}
else
{
lean_object* v___x_2960_; 
lean_inc_ref(v_f_2945_);
v___x_2960_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_2945_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_);
if (lean_obj_tag(v___x_2960_) == 0)
{
lean_object* v___x_2961_; 
lean_dec_ref_known(v___x_2960_, 1);
lean_inc_ref(v_a_2946_);
v___x_2961_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_);
if (lean_obj_tag(v___x_2961_) == 0)
{
lean_dec_ref_known(v___x_2961_, 1);
v___y_2955_ = v___y_2948_;
goto v___jp_2954_;
}
else
{
lean_object* v_a_2962_; lean_object* v___x_2964_; uint8_t v_isShared_2965_; uint8_t v_isSharedCheck_2969_; 
lean_dec_ref(v_a_2946_);
lean_dec_ref(v_f_2945_);
v_a_2962_ = lean_ctor_get(v___x_2961_, 0);
v_isSharedCheck_2969_ = !lean_is_exclusive(v___x_2961_);
if (v_isSharedCheck_2969_ == 0)
{
v___x_2964_ = v___x_2961_;
v_isShared_2965_ = v_isSharedCheck_2969_;
goto v_resetjp_2963_;
}
else
{
lean_inc(v_a_2962_);
lean_dec(v___x_2961_);
v___x_2964_ = lean_box(0);
v_isShared_2965_ = v_isSharedCheck_2969_;
goto v_resetjp_2963_;
}
v_resetjp_2963_:
{
lean_object* v___x_2967_; 
if (v_isShared_2965_ == 0)
{
v___x_2967_ = v___x_2964_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v_a_2962_);
v___x_2967_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
return v___x_2967_;
}
}
}
}
else
{
lean_object* v_a_2970_; lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_2977_; 
lean_dec_ref(v_a_2946_);
lean_dec_ref(v_f_2945_);
v_a_2970_ = lean_ctor_get(v___x_2960_, 0);
v_isSharedCheck_2977_ = !lean_is_exclusive(v___x_2960_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2972_ = v___x_2960_;
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_a_2970_);
lean_dec(v___x_2960_);
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
v___jp_2954_:
{
lean_object* v___x_2956_; lean_object* v___x_2957_; 
v___x_2956_ = l_Lean_Expr_app___override(v_f_2945_, v_a_2946_);
v___x_2957_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2956_, v___y_2955_);
return v___x_2957_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_2978_, lean_object* v_a_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_){
_start:
{
lean_object* v_res_2987_; 
v_res_2987_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0_spec__1___redArg(v_f_2978_, v_a_2979_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
lean_dec(v___y_2983_);
lean_dec_ref(v___y_2982_);
lean_dec(v___y_2981_);
lean_dec_ref(v___y_2980_);
return v_res_2987_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0(lean_object* v_args_2988_, lean_object* v_endIdx_2989_, lean_object* v_b_2990_, lean_object* v_i_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_){
_start:
{
uint8_t v___x_3002_; 
v___x_3002_ = lean_nat_dec_le(v_endIdx_2989_, v_i_2991_);
if (v___x_3002_ == 0)
{
lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; 
v___x_3003_ = l_Lean_instInhabitedExpr;
v___x_3004_ = lean_array_get_borrowed(v___x_3003_, v_args_2988_, v_i_2991_);
lean_inc(v___x_3004_);
v___x_3005_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0_spec__1___redArg(v_b_2990_, v___x_3004_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_);
if (lean_obj_tag(v___x_3005_) == 0)
{
lean_object* v_a_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; 
v_a_3006_ = lean_ctor_get(v___x_3005_, 0);
lean_inc(v_a_3006_);
lean_dec_ref_known(v___x_3005_, 1);
v___x_3007_ = lean_unsigned_to_nat(1u);
v___x_3008_ = lean_nat_add(v_i_2991_, v___x_3007_);
lean_dec(v_i_2991_);
v_b_2990_ = v_a_3006_;
v_i_2991_ = v___x_3008_;
goto _start;
}
else
{
lean_dec(v_i_2991_);
return v___x_3005_;
}
}
else
{
lean_object* v___x_3010_; 
lean_dec(v_i_2991_);
v___x_3010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3010_, 0, v_b_2990_);
return v___x_3010_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0___boxed(lean_object* v_args_3011_, lean_object* v_endIdx_3012_, lean_object* v_b_3013_, lean_object* v_i_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_){
_start:
{
lean_object* v_res_3025_; 
v_res_3025_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0(v_args_3011_, v_endIdx_3012_, v_b_3013_, v_i_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_);
lean_dec(v___y_3023_);
lean_dec_ref(v___y_3022_);
lean_dec(v___y_3021_);
lean_dec_ref(v___y_3020_);
lean_dec(v___y_3019_);
lean_dec_ref(v___y_3018_);
lean_dec(v___y_3017_);
lean_dec_ref(v___y_3016_);
lean_dec(v___y_3015_);
lean_dec(v_endIdx_3012_);
lean_dec_ref(v_args_3011_);
return v_res_3025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0(lean_object* v_f_3026_, lean_object* v_args_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_){
_start:
{
lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; 
v___x_3038_ = lean_unsigned_to_nat(0u);
v___x_3039_ = lean_array_get_size(v_args_3027_);
v___x_3040_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0(v_args_3027_, v___x_3039_, v_f_3026_, v___x_3038_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_);
return v___x_3040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0___boxed(lean_object* v_f_3041_, lean_object* v_args_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_){
_start:
{
lean_object* v_res_3053_; 
v_res_3053_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0(v_f_3041_, v_args_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_);
lean_dec(v___y_3051_);
lean_dec_ref(v___y_3050_);
lean_dec(v___y_3049_);
lean_dec_ref(v___y_3048_);
lean_dec(v___y_3047_);
lean_dec_ref(v___y_3046_);
lean_dec(v___y_3045_);
lean_dec_ref(v___y_3044_);
lean_dec(v___y_3043_);
lean_dec_ref(v_args_3042_);
return v_res_3053_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__0(void){
_start:
{
lean_object* v___x_3054_; lean_object* v_dummy_3055_; 
v___x_3054_ = lean_box(0);
v_dummy_3055_ = l_Lean_Expr_sort___override(v___x_3054_);
return v_dummy_3055_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__2(void){
_start:
{
lean_object* v___x_3057_; lean_object* v___x_3058_; 
v___x_3057_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__1));
v___x_3058_ = l_Lean_stringToMessageData(v___x_3057_);
return v___x_3058_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn(lean_object* v_e_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_){
_start:
{
uint8_t v___x_3073_; 
v___x_3073_ = l_Lean_Expr_isApp(v_e_3059_);
if (v___x_3073_ == 0)
{
lean_object* v___x_3074_; lean_object* v___x_3075_; 
lean_dec_ref(v_e_3059_);
v___x_3074_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_3074_, 0, v___x_3073_);
lean_ctor_set_uint8(v___x_3074_, 1, v___x_3073_);
v___x_3075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3075_, 0, v___x_3074_);
return v___x_3075_;
}
else
{
lean_object* v_fn_3076_; uint8_t v___x_3077_; 
v_fn_3076_ = l_Lean_Expr_getAppFn(v_e_3059_);
v___x_3077_ = l_Lean_Expr_isLambda(v_fn_3076_);
if (v___x_3077_ == 0)
{
uint8_t v___x_3078_; 
v___x_3078_ = l_Lean_Expr_isConst(v_fn_3076_);
if (v___x_3078_ == 0)
{
lean_object* v___x_3079_; 
lean_inc(v_a_3068_);
lean_inc_ref(v_a_3067_);
lean_inc(v_a_3066_);
lean_inc_ref(v_a_3065_);
lean_inc(v_a_3064_);
lean_inc_ref(v_a_3063_);
lean_inc(v_a_3062_);
lean_inc_ref(v_a_3061_);
lean_inc(v_a_3060_);
lean_inc_ref(v_fn_3076_);
v___x_3079_ = lean_sym_simp(v_fn_3076_, v_a_3060_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_);
if (lean_obj_tag(v___x_3079_) == 0)
{
lean_object* v_a_3080_; 
v_a_3080_ = lean_ctor_get(v___x_3079_, 0);
lean_inc(v_a_3080_);
if (lean_obj_tag(v_a_3080_) == 0)
{
lean_dec_ref_known(v_a_3080_, 0);
lean_dec_ref(v_fn_3076_);
lean_dec_ref(v_e_3059_);
return v___x_3079_;
}
else
{
lean_object* v_e_x27_3081_; lean_object* v_proof_3082_; uint8_t v_contextDependent_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3187_; 
lean_dec_ref_known(v___x_3079_, 1);
v_e_x27_3081_ = lean_ctor_get(v_a_3080_, 0);
v_proof_3082_ = lean_ctor_get(v_a_3080_, 1);
v_contextDependent_3083_ = lean_ctor_get_uint8(v_a_3080_, sizeof(void*)*2 + 1);
v_isSharedCheck_3187_ = !lean_is_exclusive(v_a_3080_);
if (v_isSharedCheck_3187_ == 0)
{
v___x_3085_ = v_a_3080_;
v_isShared_3086_ = v_isSharedCheck_3187_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_proof_3082_);
lean_inc(v_e_x27_3081_);
lean_dec(v_a_3080_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3187_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
lean_object* v___x_3087_; 
lean_inc_ref(v_e_x27_3081_);
v___x_3087_ = l_Lean_Meta_Sym_inferType(v_e_x27_3081_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_);
if (lean_obj_tag(v___x_3087_) == 0)
{
lean_object* v_a_3088_; lean_object* v___x_3089_; lean_object* v_dummy_3090_; lean_object* v_nargs_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; 
v_a_3088_ = lean_ctor_get(v___x_3087_, 0);
lean_inc(v_a_3088_);
lean_dec_ref_known(v___x_3087_, 1);
v___x_3089_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2);
v_dummy_3090_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__0, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__0_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__0);
v_nargs_3091_ = l_Lean_Expr_getAppNumArgs(v_e_3059_);
lean_inc(v_nargs_3091_);
v___x_3092_ = lean_mk_array(v_nargs_3091_, v_dummy_3090_);
v___x_3093_ = lean_unsigned_to_nat(1u);
v___x_3094_ = lean_nat_sub(v_nargs_3091_, v___x_3093_);
lean_dec(v_nargs_3091_);
lean_inc_ref(v_e_3059_);
v___x_3095_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3059_, v___x_3092_, v___x_3094_);
v___x_3096_ = l_Lean_mkAppN(v___x_3089_, v___x_3095_);
lean_inc_ref(v_e_x27_3081_);
v___x_3097_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0(v_e_x27_3081_, v___x_3095_, v_a_3060_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_);
lean_dec_ref(v___x_3095_);
if (lean_obj_tag(v___x_3097_) == 0)
{
lean_object* v_a_3098_; lean_object* v___x_3099_; 
v_a_3098_ = lean_ctor_get(v___x_3097_, 0);
lean_inc(v_a_3098_);
lean_dec_ref_known(v___x_3097_, 1);
lean_inc_ref(v_e_3059_);
v___x_3099_ = l_Lean_Meta_Sym_inferType(v_e_3059_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_);
if (lean_obj_tag(v___x_3099_) == 0)
{
lean_object* v_a_3100_; lean_object* v___x_3101_; uint8_t v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; 
v_a_3100_ = lean_ctor_get(v___x_3099_, 0);
lean_inc(v_a_3100_);
lean_dec_ref_known(v___x_3099_, 1);
v___x_3101_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__1));
v___x_3102_ = 0;
lean_inc_n(v_a_3088_, 2);
v___x_3103_ = l_Lean_mkLambda(v___x_3101_, v___x_3102_, v_a_3088_, v___x_3096_);
v___x_3104_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_3088_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_);
if (lean_obj_tag(v___x_3104_) == 0)
{
lean_object* v_a_3105_; lean_object* v___x_3106_; 
v_a_3105_ = lean_ctor_get(v___x_3104_, 0);
lean_inc(v_a_3105_);
lean_dec_ref_known(v___x_3104_, 1);
lean_inc(v_a_3100_);
v___x_3106_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_3100_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_);
if (lean_obj_tag(v___x_3106_) == 0)
{
lean_object* v_options_3107_; lean_object* v_a_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3146_; 
v_options_3107_ = lean_ctor_get(v_a_3067_, 2);
v_a_3108_ = lean_ctor_get(v___x_3106_, 0);
v_isSharedCheck_3146_ = !lean_is_exclusive(v___x_3106_);
if (v_isSharedCheck_3146_ == 0)
{
v___x_3110_ = v___x_3106_;
v_isShared_3111_ = v_isSharedCheck_3146_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_a_3108_);
lean_dec(v___x_3106_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3146_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
lean_object* v_inheritedTraceOptions_3112_; uint8_t v_hasTrace_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; 
v_inheritedTraceOptions_3112_ = lean_ctor_get(v_a_3067_, 13);
v_hasTrace_3113_ = lean_ctor_get_uint8(v_options_3107_, sizeof(void*)*1);
v___x_3114_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4));
v___x_3115_ = lean_box(0);
v___x_3116_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3116_, 0, v_a_3108_);
lean_ctor_set(v___x_3116_, 1, v___x_3115_);
v___x_3117_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3117_, 0, v_a_3105_);
lean_ctor_set(v___x_3117_, 1, v___x_3116_);
v___x_3118_ = l_Lean_mkConst(v___x_3114_, v___x_3117_);
v___x_3119_ = l_Lean_mkApp6(v___x_3118_, v_a_3088_, v_a_3100_, v_fn_3076_, v_e_x27_3081_, v___x_3103_, v_proof_3082_);
if (v_hasTrace_3113_ == 0)
{
lean_dec_ref(v_e_3059_);
goto v___jp_3120_;
}
else
{
lean_object* v___x_3127_; lean_object* v___x_3128_; uint8_t v___x_3129_; 
v___x_3127_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2));
v___x_3128_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3);
v___x_3129_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3112_, v_options_3107_, v___x_3128_);
if (v___x_3129_ == 0)
{
lean_dec_ref(v_e_3059_);
goto v___jp_3120_;
}
else
{
lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; 
v___x_3130_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__2, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__2);
v___x_3131_ = l_Lean_indentExpr(v_e_3059_);
v___x_3132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3132_, 0, v___x_3130_);
lean_ctor_set(v___x_3132_, 1, v___x_3131_);
v___x_3133_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_3134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3134_, 0, v___x_3132_);
lean_ctor_set(v___x_3134_, 1, v___x_3133_);
lean_inc(v_a_3098_);
v___x_3135_ = l_Lean_indentExpr(v_a_3098_);
v___x_3136_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3136_, 0, v___x_3134_);
lean_ctor_set(v___x_3136_, 1, v___x_3135_);
v___x_3137_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(v___x_3127_, v___x_3136_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_);
if (lean_obj_tag(v___x_3137_) == 0)
{
lean_dec_ref_known(v___x_3137_, 1);
goto v___jp_3120_;
}
else
{
lean_object* v_a_3138_; lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3145_; 
lean_dec_ref(v___x_3119_);
lean_del_object(v___x_3110_);
lean_dec(v_a_3098_);
lean_del_object(v___x_3085_);
v_a_3138_ = lean_ctor_get(v___x_3137_, 0);
v_isSharedCheck_3145_ = !lean_is_exclusive(v___x_3137_);
if (v_isSharedCheck_3145_ == 0)
{
v___x_3140_ = v___x_3137_;
v_isShared_3141_ = v_isSharedCheck_3145_;
goto v_resetjp_3139_;
}
else
{
lean_inc(v_a_3138_);
lean_dec(v___x_3137_);
v___x_3140_ = lean_box(0);
v_isShared_3141_ = v_isSharedCheck_3145_;
goto v_resetjp_3139_;
}
v_resetjp_3139_:
{
lean_object* v___x_3143_; 
if (v_isShared_3141_ == 0)
{
v___x_3143_ = v___x_3140_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v_a_3138_);
v___x_3143_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
return v___x_3143_;
}
}
}
}
}
v___jp_3120_:
{
lean_object* v___x_3122_; 
if (v_isShared_3086_ == 0)
{
lean_ctor_set(v___x_3085_, 1, v___x_3119_);
lean_ctor_set(v___x_3085_, 0, v_a_3098_);
v___x_3122_ = v___x_3085_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v_a_3098_);
lean_ctor_set(v_reuseFailAlloc_3126_, 1, v___x_3119_);
v___x_3122_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
lean_object* v___x_3124_; 
lean_ctor_set_uint8(v___x_3122_, sizeof(void*)*2, v_contextDependent_3083_);
lean_ctor_set_uint8(v___x_3122_, sizeof(void*)*2 + 1, v___x_3078_);
if (v_isShared_3111_ == 0)
{
lean_ctor_set(v___x_3110_, 0, v___x_3122_);
v___x_3124_ = v___x_3110_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v___x_3122_);
v___x_3124_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
return v___x_3124_;
}
}
}
}
}
else
{
lean_object* v_a_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3154_; 
lean_dec(v_a_3105_);
lean_dec_ref(v___x_3103_);
lean_dec(v_a_3100_);
lean_dec(v_a_3098_);
lean_dec(v_a_3088_);
lean_del_object(v___x_3085_);
lean_dec_ref(v_proof_3082_);
lean_dec_ref(v_e_x27_3081_);
lean_dec_ref(v_fn_3076_);
lean_dec_ref(v_e_3059_);
v_a_3147_ = lean_ctor_get(v___x_3106_, 0);
v_isSharedCheck_3154_ = !lean_is_exclusive(v___x_3106_);
if (v_isSharedCheck_3154_ == 0)
{
v___x_3149_ = v___x_3106_;
v_isShared_3150_ = v_isSharedCheck_3154_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_a_3147_);
lean_dec(v___x_3106_);
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
else
{
lean_object* v_a_3155_; lean_object* v___x_3157_; uint8_t v_isShared_3158_; uint8_t v_isSharedCheck_3162_; 
lean_dec_ref(v___x_3103_);
lean_dec(v_a_3100_);
lean_dec(v_a_3098_);
lean_dec(v_a_3088_);
lean_del_object(v___x_3085_);
lean_dec_ref(v_proof_3082_);
lean_dec_ref(v_e_x27_3081_);
lean_dec_ref(v_fn_3076_);
lean_dec_ref(v_e_3059_);
v_a_3155_ = lean_ctor_get(v___x_3104_, 0);
v_isSharedCheck_3162_ = !lean_is_exclusive(v___x_3104_);
if (v_isSharedCheck_3162_ == 0)
{
v___x_3157_ = v___x_3104_;
v_isShared_3158_ = v_isSharedCheck_3162_;
goto v_resetjp_3156_;
}
else
{
lean_inc(v_a_3155_);
lean_dec(v___x_3104_);
v___x_3157_ = lean_box(0);
v_isShared_3158_ = v_isSharedCheck_3162_;
goto v_resetjp_3156_;
}
v_resetjp_3156_:
{
lean_object* v___x_3160_; 
if (v_isShared_3158_ == 0)
{
v___x_3160_ = v___x_3157_;
goto v_reusejp_3159_;
}
else
{
lean_object* v_reuseFailAlloc_3161_; 
v_reuseFailAlloc_3161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3161_, 0, v_a_3155_);
v___x_3160_ = v_reuseFailAlloc_3161_;
goto v_reusejp_3159_;
}
v_reusejp_3159_:
{
return v___x_3160_;
}
}
}
}
else
{
lean_object* v_a_3163_; lean_object* v___x_3165_; uint8_t v_isShared_3166_; uint8_t v_isSharedCheck_3170_; 
lean_dec(v_a_3098_);
lean_dec_ref(v___x_3096_);
lean_dec(v_a_3088_);
lean_del_object(v___x_3085_);
lean_dec_ref(v_proof_3082_);
lean_dec_ref(v_e_x27_3081_);
lean_dec_ref(v_fn_3076_);
lean_dec_ref(v_e_3059_);
v_a_3163_ = lean_ctor_get(v___x_3099_, 0);
v_isSharedCheck_3170_ = !lean_is_exclusive(v___x_3099_);
if (v_isSharedCheck_3170_ == 0)
{
v___x_3165_ = v___x_3099_;
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
else
{
lean_inc(v_a_3163_);
lean_dec(v___x_3099_);
v___x_3165_ = lean_box(0);
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
v_resetjp_3164_:
{
lean_object* v___x_3168_; 
if (v_isShared_3166_ == 0)
{
v___x_3168_ = v___x_3165_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_a_3163_);
v___x_3168_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
return v___x_3168_;
}
}
}
}
else
{
lean_object* v_a_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3178_; 
lean_dec_ref(v___x_3096_);
lean_dec(v_a_3088_);
lean_del_object(v___x_3085_);
lean_dec_ref(v_proof_3082_);
lean_dec_ref(v_e_x27_3081_);
lean_dec_ref(v_fn_3076_);
lean_dec_ref(v_e_3059_);
v_a_3171_ = lean_ctor_get(v___x_3097_, 0);
v_isSharedCheck_3178_ = !lean_is_exclusive(v___x_3097_);
if (v_isSharedCheck_3178_ == 0)
{
v___x_3173_ = v___x_3097_;
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
else
{
lean_inc(v_a_3171_);
lean_dec(v___x_3097_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
lean_object* v___x_3176_; 
if (v_isShared_3174_ == 0)
{
v___x_3176_ = v___x_3173_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v_a_3171_);
v___x_3176_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
return v___x_3176_;
}
}
}
}
else
{
lean_object* v_a_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3186_; 
lean_del_object(v___x_3085_);
lean_dec_ref(v_proof_3082_);
lean_dec_ref(v_e_x27_3081_);
lean_dec_ref(v_fn_3076_);
lean_dec_ref(v_e_3059_);
v_a_3179_ = lean_ctor_get(v___x_3087_, 0);
v_isSharedCheck_3186_ = !lean_is_exclusive(v___x_3087_);
if (v_isSharedCheck_3186_ == 0)
{
v___x_3181_ = v___x_3087_;
v_isShared_3182_ = v_isSharedCheck_3186_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_a_3179_);
lean_dec(v___x_3087_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3186_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
lean_object* v___x_3184_; 
if (v_isShared_3182_ == 0)
{
v___x_3184_ = v___x_3181_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v_a_3179_);
v___x_3184_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3183_;
}
v_reusejp_3183_:
{
return v___x_3184_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_fn_3076_);
lean_dec_ref(v_e_3059_);
return v___x_3079_;
}
}
else
{
lean_dec_ref(v_fn_3076_);
lean_dec_ref(v_e_3059_);
goto v___jp_3070_;
}
}
else
{
lean_dec_ref(v_fn_3076_);
lean_dec_ref(v_e_3059_);
goto v___jp_3070_;
}
}
v___jp_3070_:
{
lean_object* v___x_3071_; lean_object* v___x_3072_; 
v___x_3071_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
v___x_3072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3072_, 0, v___x_3071_);
return v___x_3072_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___boxed(lean_object* v_e_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_, lean_object* v_a_3193_, lean_object* v_a_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_){
_start:
{
lean_object* v_res_3199_; 
v_res_3199_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn(v_e_3188_, v_a_3189_, v_a_3190_, v_a_3191_, v_a_3192_, v_a_3193_, v_a_3194_, v_a_3195_, v_a_3196_, v_a_3197_);
lean_dec(v_a_3197_);
lean_dec_ref(v_a_3196_);
lean_dec(v_a_3195_);
lean_dec_ref(v_a_3194_);
lean_dec(v_a_3193_);
lean_dec_ref(v_a_3192_);
lean_dec(v_a_3191_);
lean_dec_ref(v_a_3190_);
lean_dec(v_a_3189_);
return v_res_3199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0_spec__1(lean_object* v_f_3200_, lean_object* v_a_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_){
_start:
{
lean_object* v___x_3212_; 
v___x_3212_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0_spec__1___redArg(v_f_3200_, v_a_3201_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
return v___x_3212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0_spec__1___boxed(lean_object* v_f_3213_, lean_object* v_a_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_){
_start:
{
lean_object* v_res_3225_; 
v_res_3225_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0_spec__1(v_f_3213_, v_a_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_);
lean_dec(v___y_3223_);
lean_dec_ref(v___y_3222_);
lean_dec(v___y_3221_);
lean_dec_ref(v___y_3220_);
lean_dec(v___y_3219_);
lean_dec_ref(v___y_3218_);
lean_dec(v___y_3217_);
lean_dec_ref(v___y_3216_);
lean_dec(v___y_3215_);
return v_res_3225_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___closed__1(void){
_start:
{
lean_object* v___x_3227_; lean_object* v___x_3228_; 
v___x_3227_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___closed__0));
v___x_3228_ = l_Lean_stringToMessageData(v___x_3227_);
return v___x_3228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst(lean_object* v_e_3229_, lean_object* v_a_3230_, lean_object* v_a_3231_, lean_object* v_a_3232_, lean_object* v_a_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_){
_start:
{
if (lean_obj_tag(v_e_3229_) == 4)
{
lean_object* v_declName_3240_; lean_object* v_us_3241_; lean_object* v___x_3242_; 
v_declName_3240_ = lean_ctor_get(v_e_3229_, 0);
v_us_3241_ = lean_ctor_get(v_e_3229_, 1);
lean_inc(v_declName_3240_);
v___x_3242_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0(v_declName_3240_, v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_);
if (lean_obj_tag(v___x_3242_) == 0)
{
lean_object* v_a_3243_; lean_object* v___x_3245_; uint8_t v_isShared_3246_; uint8_t v_isSharedCheck_3370_; 
v_a_3243_ = lean_ctor_get(v___x_3242_, 0);
v_isSharedCheck_3370_ = !lean_is_exclusive(v___x_3242_);
if (v_isSharedCheck_3370_ == 0)
{
v___x_3245_ = v___x_3242_;
v_isShared_3246_ = v_isSharedCheck_3370_;
goto v_resetjp_3244_;
}
else
{
lean_inc(v_a_3243_);
lean_dec(v___x_3242_);
v___x_3245_ = lean_box(0);
v_isShared_3246_ = v_isSharedCheck_3370_;
goto v_resetjp_3244_;
}
v_resetjp_3244_:
{
uint8_t v___x_3247_; 
v___x_3247_ = l_Lean_ConstantInfo_isDefinition(v_a_3243_);
if (v___x_3247_ == 0)
{
lean_object* v___x_3248_; lean_object* v___x_3250_; 
lean_dec(v_a_3243_);
lean_dec_ref_known(v_e_3229_, 2);
v___x_3248_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_3248_, 0, v___x_3247_);
lean_ctor_set_uint8(v___x_3248_, 1, v___x_3247_);
if (v_isShared_3246_ == 0)
{
lean_ctor_set(v___x_3245_, 0, v___x_3248_);
v___x_3250_ = v___x_3245_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v___x_3248_);
v___x_3250_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
return v___x_3250_;
}
}
else
{
lean_object* v___x_3252_; 
v___x_3252_ = l_Lean_ConstantInfo_type(v_a_3243_);
if (lean_obj_tag(v___x_3252_) == 7)
{
lean_object* v___x_3253_; lean_object* v___x_3255_; 
lean_dec_ref_known(v___x_3252_, 3);
lean_dec(v_a_3243_);
lean_dec_ref_known(v_e_3229_, 2);
v___x_3253_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
if (v_isShared_3246_ == 0)
{
lean_ctor_set(v___x_3245_, 0, v___x_3253_);
v___x_3255_ = v___x_3245_;
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
else
{
lean_object* v___x_3257_; 
v___x_3257_ = l_Lean_Meta_whnfD(v___x_3252_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_);
if (lean_obj_tag(v___x_3257_) == 0)
{
lean_object* v_a_3258_; lean_object* v___x_3260_; uint8_t v_isShared_3261_; uint8_t v_isSharedCheck_3361_; 
v_a_3258_ = lean_ctor_get(v___x_3257_, 0);
v_isSharedCheck_3361_ = !lean_is_exclusive(v___x_3257_);
if (v_isSharedCheck_3361_ == 0)
{
v___x_3260_ = v___x_3257_;
v_isShared_3261_ = v_isSharedCheck_3361_;
goto v_resetjp_3259_;
}
else
{
lean_inc(v_a_3258_);
lean_dec(v___x_3257_);
v___x_3260_ = lean_box(0);
v_isShared_3261_ = v_isSharedCheck_3361_;
goto v_resetjp_3259_;
}
v_resetjp_3259_:
{
uint8_t v___x_3262_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3266_; lean_object* v___y_3267_; lean_object* v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3270_; uint8_t v___y_3290_; 
v___x_3262_ = 0;
if (lean_obj_tag(v_a_3258_) == 7)
{
lean_object* v___x_3352_; lean_object* v___x_3354_; 
lean_dec_ref_known(v_a_3258_, 3);
lean_del_object(v___x_3260_);
lean_dec(v_a_3243_);
lean_dec_ref_known(v_e_3229_, 2);
v___x_3352_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
if (v_isShared_3246_ == 0)
{
lean_ctor_set(v___x_3245_, 0, v___x_3352_);
v___x_3354_ = v___x_3245_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v___x_3352_);
v___x_3354_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
return v___x_3354_;
}
}
else
{
uint8_t v___x_3356_; 
lean_dec(v_a_3258_);
lean_del_object(v___x_3245_);
v___x_3356_ = l_Lean_ConstantInfo_hasValue(v_a_3243_, v___x_3262_);
if (v___x_3356_ == 0)
{
v___y_3290_ = v___x_3356_;
goto v___jp_3289_;
}
else
{
lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; uint8_t v___x_3360_; 
v___x_3357_ = l_Lean_ConstantInfo_levelParams(v_a_3243_);
v___x_3358_ = l_List_lengthTR___redArg(v___x_3357_);
lean_dec(v___x_3357_);
v___x_3359_ = l_List_lengthTR___redArg(v_us_3241_);
v___x_3360_ = lean_nat_dec_eq(v___x_3358_, v___x_3359_);
lean_dec(v___x_3359_);
lean_dec(v___x_3358_);
v___y_3290_ = v___x_3360_;
goto v___jp_3289_;
}
}
v___jp_3263_:
{
lean_object* v___x_3271_; 
lean_inc_ref(v___y_3264_);
v___x_3271_ = l_Lean_Meta_Sym_mkEqRefl(v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_);
if (lean_obj_tag(v___x_3271_) == 0)
{
lean_object* v_a_3272_; lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3280_; 
v_a_3272_ = lean_ctor_get(v___x_3271_, 0);
v_isSharedCheck_3280_ = !lean_is_exclusive(v___x_3271_);
if (v_isSharedCheck_3280_ == 0)
{
v___x_3274_ = v___x_3271_;
v_isShared_3275_ = v_isSharedCheck_3280_;
goto v_resetjp_3273_;
}
else
{
lean_inc(v_a_3272_);
lean_dec(v___x_3271_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3280_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
lean_object* v___x_3276_; lean_object* v___x_3278_; 
v___x_3276_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3276_, 0, v___y_3264_);
lean_ctor_set(v___x_3276_, 1, v_a_3272_);
lean_ctor_set_uint8(v___x_3276_, sizeof(void*)*2, v___x_3262_);
lean_ctor_set_uint8(v___x_3276_, sizeof(void*)*2 + 1, v___x_3262_);
if (v_isShared_3275_ == 0)
{
lean_ctor_set(v___x_3274_, 0, v___x_3276_);
v___x_3278_ = v___x_3274_;
goto v_reusejp_3277_;
}
else
{
lean_object* v_reuseFailAlloc_3279_; 
v_reuseFailAlloc_3279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3279_, 0, v___x_3276_);
v___x_3278_ = v_reuseFailAlloc_3279_;
goto v_reusejp_3277_;
}
v_reusejp_3277_:
{
return v___x_3278_;
}
}
}
else
{
lean_object* v_a_3281_; lean_object* v___x_3283_; uint8_t v_isShared_3284_; uint8_t v_isSharedCheck_3288_; 
lean_dec_ref(v___y_3264_);
v_a_3281_ = lean_ctor_get(v___x_3271_, 0);
v_isSharedCheck_3288_ = !lean_is_exclusive(v___x_3271_);
if (v_isSharedCheck_3288_ == 0)
{
v___x_3283_ = v___x_3271_;
v_isShared_3284_ = v_isSharedCheck_3288_;
goto v_resetjp_3282_;
}
else
{
lean_inc(v_a_3281_);
lean_dec(v___x_3271_);
v___x_3283_ = lean_box(0);
v_isShared_3284_ = v_isSharedCheck_3288_;
goto v_resetjp_3282_;
}
v_resetjp_3282_:
{
lean_object* v___x_3286_; 
if (v_isShared_3284_ == 0)
{
v___x_3286_ = v___x_3283_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3287_; 
v_reuseFailAlloc_3287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3287_, 0, v_a_3281_);
v___x_3286_ = v_reuseFailAlloc_3287_;
goto v_reusejp_3285_;
}
v_reusejp_3285_:
{
return v___x_3286_;
}
}
}
}
v___jp_3289_:
{
if (v___y_3290_ == 0)
{
lean_object* v___x_3291_; lean_object* v___x_3293_; 
lean_dec(v_a_3243_);
lean_dec_ref_known(v_e_3229_, 2);
v___x_3291_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
if (v_isShared_3261_ == 0)
{
lean_ctor_set(v___x_3260_, 0, v___x_3291_);
v___x_3293_ = v___x_3260_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v___x_3291_);
v___x_3293_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3292_;
}
v_reusejp_3292_:
{
return v___x_3293_;
}
}
else
{
lean_object* v___x_3295_; 
lean_del_object(v___x_3260_);
lean_inc(v_us_3241_);
v___x_3295_ = l_Lean_Core_instantiateValueLevelParams(v_a_3243_, v_us_3241_, v___x_3262_, v_a_3237_, v_a_3238_);
lean_dec(v_a_3243_);
if (lean_obj_tag(v___x_3295_) == 0)
{
lean_object* v_a_3296_; lean_object* v___x_3297_; 
v_a_3296_ = lean_ctor_get(v___x_3295_, 0);
lean_inc(v_a_3296_);
lean_dec_ref_known(v___x_3295_, 1);
v___x_3297_ = l_Lean_Meta_Sym_unfoldReducible(v_a_3296_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_);
if (lean_obj_tag(v___x_3297_) == 0)
{
lean_object* v_a_3298_; lean_object* v___x_3299_; 
v_a_3298_ = lean_ctor_get(v___x_3297_, 0);
lean_inc(v_a_3298_);
lean_dec_ref_known(v___x_3297_, 1);
v___x_3299_ = l_Lean_Meta_Sym_shareCommonInc(v_a_3298_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_);
if (lean_obj_tag(v___x_3299_) == 0)
{
lean_object* v_options_3300_; uint8_t v_hasTrace_3301_; 
v_options_3300_ = lean_ctor_get(v_a_3237_, 2);
v_hasTrace_3301_ = lean_ctor_get_uint8(v_options_3300_, sizeof(void*)*1);
if (v_hasTrace_3301_ == 0)
{
lean_object* v_a_3302_; 
lean_dec_ref_known(v_e_3229_, 2);
v_a_3302_ = lean_ctor_get(v___x_3299_, 0);
lean_inc(v_a_3302_);
lean_dec_ref_known(v___x_3299_, 1);
v___y_3264_ = v_a_3302_;
v___y_3265_ = v_a_3233_;
v___y_3266_ = v_a_3234_;
v___y_3267_ = v_a_3235_;
v___y_3268_ = v_a_3236_;
v___y_3269_ = v_a_3237_;
v___y_3270_ = v_a_3238_;
goto v___jp_3263_;
}
else
{
lean_object* v_a_3303_; lean_object* v_inheritedTraceOptions_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; uint8_t v___x_3307_; 
v_a_3303_ = lean_ctor_get(v___x_3299_, 0);
lean_inc(v_a_3303_);
lean_dec_ref_known(v___x_3299_, 1);
v_inheritedTraceOptions_3304_ = lean_ctor_get(v_a_3237_, 13);
v___x_3305_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__1));
v___x_3306_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__2, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__2);
v___x_3307_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3304_, v_options_3300_, v___x_3306_);
if (v___x_3307_ == 0)
{
lean_dec_ref_known(v_e_3229_, 2);
v___y_3264_ = v_a_3303_;
v___y_3265_ = v_a_3233_;
v___y_3266_ = v_a_3234_;
v___y_3267_ = v_a_3235_;
v___y_3268_ = v_a_3236_;
v___y_3269_ = v_a_3237_;
v___y_3270_ = v_a_3238_;
goto v___jp_3263_;
}
else
{
lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; 
v___x_3308_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___closed__1, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___closed__1);
lean_inc(v_declName_3240_);
v___x_3309_ = l_Lean_MessageData_ofName(v_declName_3240_);
v___x_3310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3310_, 0, v___x_3308_);
lean_ctor_set(v___x_3310_, 1, v___x_3309_);
v___x_3311_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8);
v___x_3312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3312_, 0, v___x_3310_);
lean_ctor_set(v___x_3312_, 1, v___x_3311_);
v___x_3313_ = l_Lean_indentExpr(v_e_3229_);
v___x_3314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3314_, 0, v___x_3312_);
lean_ctor_set(v___x_3314_, 1, v___x_3313_);
v___x_3315_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_3316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3316_, 0, v___x_3314_);
lean_ctor_set(v___x_3316_, 1, v___x_3315_);
lean_inc(v_a_3303_);
v___x_3317_ = l_Lean_indentExpr(v_a_3303_);
v___x_3318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3318_, 0, v___x_3316_);
lean_ctor_set(v___x_3318_, 1, v___x_3317_);
v___x_3319_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(v___x_3305_, v___x_3318_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_);
if (lean_obj_tag(v___x_3319_) == 0)
{
lean_dec_ref_known(v___x_3319_, 1);
v___y_3264_ = v_a_3303_;
v___y_3265_ = v_a_3233_;
v___y_3266_ = v_a_3234_;
v___y_3267_ = v_a_3235_;
v___y_3268_ = v_a_3236_;
v___y_3269_ = v_a_3237_;
v___y_3270_ = v_a_3238_;
goto v___jp_3263_;
}
else
{
lean_object* v_a_3320_; lean_object* v___x_3322_; uint8_t v_isShared_3323_; uint8_t v_isSharedCheck_3327_; 
lean_dec(v_a_3303_);
v_a_3320_ = lean_ctor_get(v___x_3319_, 0);
v_isSharedCheck_3327_ = !lean_is_exclusive(v___x_3319_);
if (v_isSharedCheck_3327_ == 0)
{
v___x_3322_ = v___x_3319_;
v_isShared_3323_ = v_isSharedCheck_3327_;
goto v_resetjp_3321_;
}
else
{
lean_inc(v_a_3320_);
lean_dec(v___x_3319_);
v___x_3322_ = lean_box(0);
v_isShared_3323_ = v_isSharedCheck_3327_;
goto v_resetjp_3321_;
}
v_resetjp_3321_:
{
lean_object* v___x_3325_; 
if (v_isShared_3323_ == 0)
{
v___x_3325_ = v___x_3322_;
goto v_reusejp_3324_;
}
else
{
lean_object* v_reuseFailAlloc_3326_; 
v_reuseFailAlloc_3326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3326_, 0, v_a_3320_);
v___x_3325_ = v_reuseFailAlloc_3326_;
goto v_reusejp_3324_;
}
v_reusejp_3324_:
{
return v___x_3325_;
}
}
}
}
}
}
else
{
lean_object* v_a_3328_; lean_object* v___x_3330_; uint8_t v_isShared_3331_; uint8_t v_isSharedCheck_3335_; 
lean_dec_ref_known(v_e_3229_, 2);
v_a_3328_ = lean_ctor_get(v___x_3299_, 0);
v_isSharedCheck_3335_ = !lean_is_exclusive(v___x_3299_);
if (v_isSharedCheck_3335_ == 0)
{
v___x_3330_ = v___x_3299_;
v_isShared_3331_ = v_isSharedCheck_3335_;
goto v_resetjp_3329_;
}
else
{
lean_inc(v_a_3328_);
lean_dec(v___x_3299_);
v___x_3330_ = lean_box(0);
v_isShared_3331_ = v_isSharedCheck_3335_;
goto v_resetjp_3329_;
}
v_resetjp_3329_:
{
lean_object* v___x_3333_; 
if (v_isShared_3331_ == 0)
{
v___x_3333_ = v___x_3330_;
goto v_reusejp_3332_;
}
else
{
lean_object* v_reuseFailAlloc_3334_; 
v_reuseFailAlloc_3334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3334_, 0, v_a_3328_);
v___x_3333_ = v_reuseFailAlloc_3334_;
goto v_reusejp_3332_;
}
v_reusejp_3332_:
{
return v___x_3333_;
}
}
}
}
else
{
lean_object* v_a_3336_; lean_object* v___x_3338_; uint8_t v_isShared_3339_; uint8_t v_isSharedCheck_3343_; 
lean_dec_ref_known(v_e_3229_, 2);
v_a_3336_ = lean_ctor_get(v___x_3297_, 0);
v_isSharedCheck_3343_ = !lean_is_exclusive(v___x_3297_);
if (v_isSharedCheck_3343_ == 0)
{
v___x_3338_ = v___x_3297_;
v_isShared_3339_ = v_isSharedCheck_3343_;
goto v_resetjp_3337_;
}
else
{
lean_inc(v_a_3336_);
lean_dec(v___x_3297_);
v___x_3338_ = lean_box(0);
v_isShared_3339_ = v_isSharedCheck_3343_;
goto v_resetjp_3337_;
}
v_resetjp_3337_:
{
lean_object* v___x_3341_; 
if (v_isShared_3339_ == 0)
{
v___x_3341_ = v___x_3338_;
goto v_reusejp_3340_;
}
else
{
lean_object* v_reuseFailAlloc_3342_; 
v_reuseFailAlloc_3342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3342_, 0, v_a_3336_);
v___x_3341_ = v_reuseFailAlloc_3342_;
goto v_reusejp_3340_;
}
v_reusejp_3340_:
{
return v___x_3341_;
}
}
}
}
else
{
lean_object* v_a_3344_; lean_object* v___x_3346_; uint8_t v_isShared_3347_; uint8_t v_isSharedCheck_3351_; 
lean_dec_ref_known(v_e_3229_, 2);
v_a_3344_ = lean_ctor_get(v___x_3295_, 0);
v_isSharedCheck_3351_ = !lean_is_exclusive(v___x_3295_);
if (v_isSharedCheck_3351_ == 0)
{
v___x_3346_ = v___x_3295_;
v_isShared_3347_ = v_isSharedCheck_3351_;
goto v_resetjp_3345_;
}
else
{
lean_inc(v_a_3344_);
lean_dec(v___x_3295_);
v___x_3346_ = lean_box(0);
v_isShared_3347_ = v_isSharedCheck_3351_;
goto v_resetjp_3345_;
}
v_resetjp_3345_:
{
lean_object* v___x_3349_; 
if (v_isShared_3347_ == 0)
{
v___x_3349_ = v___x_3346_;
goto v_reusejp_3348_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v_a_3344_);
v___x_3349_ = v_reuseFailAlloc_3350_;
goto v_reusejp_3348_;
}
v_reusejp_3348_:
{
return v___x_3349_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3369_; 
lean_del_object(v___x_3245_);
lean_dec(v_a_3243_);
lean_dec_ref_known(v_e_3229_, 2);
v_a_3362_ = lean_ctor_get(v___x_3257_, 0);
v_isSharedCheck_3369_ = !lean_is_exclusive(v___x_3257_);
if (v_isSharedCheck_3369_ == 0)
{
v___x_3364_ = v___x_3257_;
v_isShared_3365_ = v_isSharedCheck_3369_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_a_3362_);
lean_dec(v___x_3257_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3369_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
lean_object* v___x_3367_; 
if (v_isShared_3365_ == 0)
{
v___x_3367_ = v___x_3364_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v_a_3362_);
v___x_3367_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3366_;
}
v_reusejp_3366_:
{
return v___x_3367_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3371_; lean_object* v___x_3373_; uint8_t v_isShared_3374_; uint8_t v_isSharedCheck_3378_; 
lean_dec_ref_known(v_e_3229_, 2);
v_a_3371_ = lean_ctor_get(v___x_3242_, 0);
v_isSharedCheck_3378_ = !lean_is_exclusive(v___x_3242_);
if (v_isSharedCheck_3378_ == 0)
{
v___x_3373_ = v___x_3242_;
v_isShared_3374_ = v_isSharedCheck_3378_;
goto v_resetjp_3372_;
}
else
{
lean_inc(v_a_3371_);
lean_dec(v___x_3242_);
v___x_3373_ = lean_box(0);
v_isShared_3374_ = v_isSharedCheck_3378_;
goto v_resetjp_3372_;
}
v_resetjp_3372_:
{
lean_object* v___x_3376_; 
if (v_isShared_3374_ == 0)
{
v___x_3376_ = v___x_3373_;
goto v_reusejp_3375_;
}
else
{
lean_object* v_reuseFailAlloc_3377_; 
v_reuseFailAlloc_3377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3377_, 0, v_a_3371_);
v___x_3376_ = v_reuseFailAlloc_3377_;
goto v_reusejp_3375_;
}
v_reusejp_3375_:
{
return v___x_3376_;
}
}
}
}
else
{
lean_object* v___x_3379_; lean_object* v___x_3380_; 
lean_dec_ref(v_e_3229_);
v___x_3379_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
v___x_3380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3380_, 0, v___x_3379_);
return v___x_3380_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___boxed(lean_object* v_e_3381_, lean_object* v_a_3382_, lean_object* v_a_3383_, lean_object* v_a_3384_, lean_object* v_a_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_){
_start:
{
lean_object* v_res_3392_; 
v_res_3392_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst(v_e_3381_, v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_, v_a_3390_);
lean_dec(v_a_3390_);
lean_dec_ref(v_a_3389_);
lean_dec(v_a_3388_);
lean_dec_ref(v_a_3387_);
lean_dec(v_a_3386_);
lean_dec_ref(v_a_3385_);
lean_dec(v_a_3384_);
lean_dec_ref(v_a_3383_);
lean_dec(v_a_3382_);
return v_res_3392_;
}
}
static uint8_t _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___lam__0___closed__0(void){
_start:
{
uint8_t v___x_3393_; uint8_t v___x_3394_; 
v___x_3393_ = 0;
v___x_3394_ = lean_bool_not(v___x_3393_);
return v___x_3394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___lam__0(lean_object* v_x_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_){
_start:
{
lean_object* v___x_3407_; 
lean_inc_ref(v___y_3396_);
v___x_3407_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems(v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_);
if (lean_obj_tag(v___x_3407_) == 0)
{
lean_object* v_a_3408_; 
v_a_3408_ = lean_ctor_get(v___x_3407_, 0);
lean_inc(v_a_3408_);
if (lean_obj_tag(v_a_3408_) == 0)
{
uint8_t v_done_3409_; 
v_done_3409_ = lean_ctor_get_uint8(v_a_3408_, 0);
if (v_done_3409_ == 0)
{
uint8_t v_contextDependent_3410_; lean_object* v___x_3411_; 
lean_dec_ref_known(v___x_3407_, 1);
v_contextDependent_3410_ = lean_ctor_get_uint8(v_a_3408_, 1);
lean_dec_ref_known(v_a_3408_, 0);
v___x_3411_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst(v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_);
if (lean_obj_tag(v___x_3411_) == 0)
{
lean_object* v_a_3412_; uint8_t v___y_3414_; 
v_a_3412_ = lean_ctor_get(v___x_3411_, 0);
lean_inc(v_a_3412_);
if (v_contextDependent_3410_ == 0)
{
lean_dec(v_a_3412_);
return v___x_3411_;
}
else
{
if (lean_obj_tag(v_a_3412_) == 0)
{
uint8_t v_contextDependent_3424_; uint8_t v___x_3425_; 
v_contextDependent_3424_ = lean_ctor_get_uint8(v_a_3412_, 1);
v___x_3425_ = lean_bool_not(v_contextDependent_3424_);
v___y_3414_ = v___x_3425_;
goto v___jp_3413_;
}
else
{
uint8_t v___x_3426_; 
v___x_3426_ = lean_uint8_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___lam__0___closed__0, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___lam__0___closed__0_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___lam__0___closed__0);
v___y_3414_ = v___x_3426_;
goto v___jp_3413_;
}
}
v___jp_3413_:
{
if (v___y_3414_ == 0)
{
lean_dec(v_a_3412_);
return v___x_3411_;
}
else
{
lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3422_; 
v_isSharedCheck_3422_ = !lean_is_exclusive(v___x_3411_);
if (v_isSharedCheck_3422_ == 0)
{
lean_object* v_unused_3423_; 
v_unused_3423_ = lean_ctor_get(v___x_3411_, 0);
lean_dec(v_unused_3423_);
v___x_3416_ = v___x_3411_;
v_isShared_3417_ = v_isSharedCheck_3422_;
goto v_resetjp_3415_;
}
else
{
lean_dec(v___x_3411_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3422_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
lean_object* v___x_3418_; lean_object* v___x_3420_; 
v___x_3418_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3412_);
if (v_isShared_3417_ == 0)
{
lean_ctor_set(v___x_3416_, 0, v___x_3418_);
v___x_3420_ = v___x_3416_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v___x_3418_);
v___x_3420_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
return v___x_3420_;
}
}
}
}
}
else
{
return v___x_3411_;
}
}
else
{
lean_dec_ref_known(v_a_3408_, 0);
lean_dec_ref(v___y_3396_);
return v___x_3407_;
}
}
else
{
lean_dec_ref_known(v_a_3408_, 2);
lean_dec_ref(v___y_3396_);
return v___x_3407_;
}
}
else
{
lean_dec_ref(v___y_3396_);
return v___x_3407_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___lam__0___boxed(lean_object* v_x_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_){
_start:
{
lean_object* v_res_3439_; 
v_res_3439_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___lam__0(v_x_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_);
lean_dec(v___y_3437_);
lean_dec_ref(v___y_3436_);
lean_dec(v___y_3435_);
lean_dec_ref(v___y_3434_);
lean_dec(v___y_3433_);
lean_dec_ref(v___y_3432_);
lean_dec(v___y_3431_);
lean_dec_ref(v___y_3430_);
lean_dec(v___y_3429_);
return v_res_3439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep(lean_object* v_e_3443_, lean_object* v_a_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_, lean_object* v_a_3450_, lean_object* v_a_3451_, lean_object* v_a_3452_){
_start:
{
switch(lean_obj_tag(v_e_3443_))
{
case 9:
{
lean_object* v___x_3457_; 
v___x_3457_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg(v_e_3443_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_, v_a_3451_, v_a_3452_);
return v___x_3457_;
}
case 11:
{
lean_object* v___x_3458_; 
v___x_3458_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj(v_e_3443_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_, v_a_3451_, v_a_3452_);
return v___x_3458_;
}
case 4:
{
lean_object* v___x_3459_; 
lean_inc_ref(v_e_3443_);
v___x_3459_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleOpaqueConst(v_e_3443_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_, v_a_3451_, v_a_3452_);
if (lean_obj_tag(v___x_3459_) == 0)
{
lean_object* v_a_3460_; lean_object* v___x_3461_; 
v_a_3460_ = lean_ctor_get(v___x_3459_, 0);
lean_inc(v_a_3460_);
v___x_3461_ = lean_box(0);
if (lean_obj_tag(v_a_3460_) == 0)
{
uint8_t v_done_3462_; 
v_done_3462_ = lean_ctor_get_uint8(v_a_3460_, 0);
if (v_done_3462_ == 0)
{
uint8_t v_contextDependent_3463_; lean_object* v___x_3464_; 
lean_dec_ref_known(v___x_3459_, 1);
v_contextDependent_3463_ = lean_ctor_get_uint8(v_a_3460_, 1);
lean_dec_ref_known(v_a_3460_, 0);
v___x_3464_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___lam__0(v___x_3461_, v_e_3443_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_, v_a_3451_, v_a_3452_);
if (lean_obj_tag(v___x_3464_) == 0)
{
lean_object* v_a_3465_; uint8_t v___y_3467_; 
v_a_3465_ = lean_ctor_get(v___x_3464_, 0);
lean_inc(v_a_3465_);
if (v_contextDependent_3463_ == 0)
{
lean_dec(v_a_3465_);
return v___x_3464_;
}
else
{
if (lean_obj_tag(v_a_3465_) == 0)
{
uint8_t v_contextDependent_3477_; uint8_t v___x_3478_; 
v_contextDependent_3477_ = lean_ctor_get_uint8(v_a_3465_, 1);
v___x_3478_ = lean_bool_not(v_contextDependent_3477_);
v___y_3467_ = v___x_3478_;
goto v___jp_3466_;
}
else
{
uint8_t v_contextDependent_3479_; uint8_t v___x_3480_; 
v_contextDependent_3479_ = lean_ctor_get_uint8(v_a_3465_, sizeof(void*)*2 + 1);
v___x_3480_ = lean_bool_not(v_contextDependent_3479_);
v___y_3467_ = v___x_3480_;
goto v___jp_3466_;
}
}
v___jp_3466_:
{
if (v___y_3467_ == 0)
{
lean_dec(v_a_3465_);
return v___x_3464_;
}
else
{
lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3475_; 
v_isSharedCheck_3475_ = !lean_is_exclusive(v___x_3464_);
if (v_isSharedCheck_3475_ == 0)
{
lean_object* v_unused_3476_; 
v_unused_3476_ = lean_ctor_get(v___x_3464_, 0);
lean_dec(v_unused_3476_);
v___x_3469_ = v___x_3464_;
v_isShared_3470_ = v_isSharedCheck_3475_;
goto v_resetjp_3468_;
}
else
{
lean_dec(v___x_3464_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3475_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
lean_object* v___x_3471_; lean_object* v___x_3473_; 
v___x_3471_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3465_);
if (v_isShared_3470_ == 0)
{
lean_ctor_set(v___x_3469_, 0, v___x_3471_);
v___x_3473_ = v___x_3469_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v___x_3471_);
v___x_3473_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
return v___x_3473_;
}
}
}
}
}
else
{
return v___x_3464_;
}
}
else
{
lean_dec_ref_known(v_a_3460_, 0);
lean_dec_ref_known(v_e_3443_, 2);
return v___x_3459_;
}
}
else
{
uint8_t v_done_3481_; 
v_done_3481_ = lean_ctor_get_uint8(v_a_3460_, sizeof(void*)*2);
if (v_done_3481_ == 0)
{
lean_object* v_e_x27_3482_; lean_object* v_proof_3483_; uint8_t v_contextDependent_3484_; lean_object* v___x_3486_; uint8_t v_isShared_3487_; uint8_t v_isSharedCheck_3534_; 
lean_dec_ref_known(v___x_3459_, 1);
v_e_x27_3482_ = lean_ctor_get(v_a_3460_, 0);
v_proof_3483_ = lean_ctor_get(v_a_3460_, 1);
v_contextDependent_3484_ = lean_ctor_get_uint8(v_a_3460_, sizeof(void*)*2 + 1);
v_isSharedCheck_3534_ = !lean_is_exclusive(v_a_3460_);
if (v_isSharedCheck_3534_ == 0)
{
v___x_3486_ = v_a_3460_;
v_isShared_3487_ = v_isSharedCheck_3534_;
goto v_resetjp_3485_;
}
else
{
lean_inc(v_proof_3483_);
lean_inc(v_e_x27_3482_);
lean_dec(v_a_3460_);
v___x_3486_ = lean_box(0);
v_isShared_3487_ = v_isSharedCheck_3534_;
goto v_resetjp_3485_;
}
v_resetjp_3485_:
{
lean_object* v___x_3488_; 
lean_inc_ref(v_e_x27_3482_);
v___x_3488_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___lam__0(v___x_3461_, v_e_x27_3482_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_, v_a_3451_, v_a_3452_);
if (lean_obj_tag(v___x_3488_) == 0)
{
lean_object* v_a_3489_; lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3533_; 
v_a_3489_ = lean_ctor_get(v___x_3488_, 0);
v_isSharedCheck_3533_ = !lean_is_exclusive(v___x_3488_);
if (v_isSharedCheck_3533_ == 0)
{
v___x_3491_ = v___x_3488_;
v_isShared_3492_ = v_isSharedCheck_3533_;
goto v_resetjp_3490_;
}
else
{
lean_inc(v_a_3489_);
lean_dec(v___x_3488_);
v___x_3491_ = lean_box(0);
v_isShared_3492_ = v_isSharedCheck_3533_;
goto v_resetjp_3490_;
}
v_resetjp_3490_:
{
if (lean_obj_tag(v_a_3489_) == 0)
{
uint8_t v_done_3493_; uint8_t v_contextDependent_3494_; uint8_t v___y_3496_; 
lean_dec_ref_known(v_e_3443_, 2);
v_done_3493_ = lean_ctor_get_uint8(v_a_3489_, 0);
v_contextDependent_3494_ = lean_ctor_get_uint8(v_a_3489_, 1);
lean_dec_ref_known(v_a_3489_, 0);
if (v_contextDependent_3484_ == 0)
{
v___y_3496_ = v_contextDependent_3494_;
goto v___jp_3495_;
}
else
{
v___y_3496_ = v_contextDependent_3484_;
goto v___jp_3495_;
}
v___jp_3495_:
{
lean_object* v___x_3498_; 
if (v_isShared_3487_ == 0)
{
v___x_3498_ = v___x_3486_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v_e_x27_3482_);
lean_ctor_set(v_reuseFailAlloc_3502_, 1, v_proof_3483_);
v___x_3498_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
lean_object* v___x_3500_; 
lean_ctor_set_uint8(v___x_3498_, sizeof(void*)*2, v_done_3493_);
lean_ctor_set_uint8(v___x_3498_, sizeof(void*)*2 + 1, v___y_3496_);
if (v_isShared_3492_ == 0)
{
lean_ctor_set(v___x_3491_, 0, v___x_3498_);
v___x_3500_ = v___x_3491_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v___x_3498_);
v___x_3500_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
return v___x_3500_;
}
}
}
}
else
{
lean_object* v_e_x27_3503_; lean_object* v_proof_3504_; uint8_t v_done_3505_; uint8_t v_contextDependent_3506_; lean_object* v___x_3508_; uint8_t v_isShared_3509_; uint8_t v_isSharedCheck_3532_; 
lean_del_object(v___x_3491_);
lean_del_object(v___x_3486_);
v_e_x27_3503_ = lean_ctor_get(v_a_3489_, 0);
v_proof_3504_ = lean_ctor_get(v_a_3489_, 1);
v_done_3505_ = lean_ctor_get_uint8(v_a_3489_, sizeof(void*)*2);
v_contextDependent_3506_ = lean_ctor_get_uint8(v_a_3489_, sizeof(void*)*2 + 1);
v_isSharedCheck_3532_ = !lean_is_exclusive(v_a_3489_);
if (v_isSharedCheck_3532_ == 0)
{
v___x_3508_ = v_a_3489_;
v_isShared_3509_ = v_isSharedCheck_3532_;
goto v_resetjp_3507_;
}
else
{
lean_inc(v_proof_3504_);
lean_inc(v_e_x27_3503_);
lean_dec(v_a_3489_);
v___x_3508_ = lean_box(0);
v_isShared_3509_ = v_isSharedCheck_3532_;
goto v_resetjp_3507_;
}
v_resetjp_3507_:
{
lean_object* v___x_3510_; 
lean_inc_ref(v_e_x27_3503_);
v___x_3510_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v_e_3443_, v_e_x27_3482_, v_proof_3483_, v_e_x27_3503_, v_proof_3504_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_, v_a_3451_, v_a_3452_);
if (lean_obj_tag(v___x_3510_) == 0)
{
lean_object* v_a_3511_; lean_object* v___x_3513_; uint8_t v_isShared_3514_; uint8_t v_isSharedCheck_3523_; 
v_a_3511_ = lean_ctor_get(v___x_3510_, 0);
v_isSharedCheck_3523_ = !lean_is_exclusive(v___x_3510_);
if (v_isSharedCheck_3523_ == 0)
{
v___x_3513_ = v___x_3510_;
v_isShared_3514_ = v_isSharedCheck_3523_;
goto v_resetjp_3512_;
}
else
{
lean_inc(v_a_3511_);
lean_dec(v___x_3510_);
v___x_3513_ = lean_box(0);
v_isShared_3514_ = v_isSharedCheck_3523_;
goto v_resetjp_3512_;
}
v_resetjp_3512_:
{
uint8_t v___y_3516_; 
if (v_contextDependent_3484_ == 0)
{
v___y_3516_ = v_contextDependent_3506_;
goto v___jp_3515_;
}
else
{
v___y_3516_ = v_contextDependent_3484_;
goto v___jp_3515_;
}
v___jp_3515_:
{
lean_object* v___x_3518_; 
if (v_isShared_3509_ == 0)
{
lean_ctor_set(v___x_3508_, 1, v_a_3511_);
v___x_3518_ = v___x_3508_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3522_; 
v_reuseFailAlloc_3522_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3522_, 0, v_e_x27_3503_);
lean_ctor_set(v_reuseFailAlloc_3522_, 1, v_a_3511_);
lean_ctor_set_uint8(v_reuseFailAlloc_3522_, sizeof(void*)*2, v_done_3505_);
v___x_3518_ = v_reuseFailAlloc_3522_;
goto v_reusejp_3517_;
}
v_reusejp_3517_:
{
lean_object* v___x_3520_; 
lean_ctor_set_uint8(v___x_3518_, sizeof(void*)*2 + 1, v___y_3516_);
if (v_isShared_3514_ == 0)
{
lean_ctor_set(v___x_3513_, 0, v___x_3518_);
v___x_3520_ = v___x_3513_;
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
}
}
else
{
lean_object* v_a_3524_; lean_object* v___x_3526_; uint8_t v_isShared_3527_; uint8_t v_isSharedCheck_3531_; 
lean_del_object(v___x_3508_);
lean_dec_ref(v_e_x27_3503_);
v_a_3524_ = lean_ctor_get(v___x_3510_, 0);
v_isSharedCheck_3531_ = !lean_is_exclusive(v___x_3510_);
if (v_isSharedCheck_3531_ == 0)
{
v___x_3526_ = v___x_3510_;
v_isShared_3527_ = v_isSharedCheck_3531_;
goto v_resetjp_3525_;
}
else
{
lean_inc(v_a_3524_);
lean_dec(v___x_3510_);
v___x_3526_ = lean_box(0);
v_isShared_3527_ = v_isSharedCheck_3531_;
goto v_resetjp_3525_;
}
v_resetjp_3525_:
{
lean_object* v___x_3529_; 
if (v_isShared_3527_ == 0)
{
v___x_3529_ = v___x_3526_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3530_; 
v_reuseFailAlloc_3530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3530_, 0, v_a_3524_);
v___x_3529_ = v_reuseFailAlloc_3530_;
goto v_reusejp_3528_;
}
v_reusejp_3528_:
{
return v___x_3529_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_3486_);
lean_dec_ref(v_proof_3483_);
lean_dec_ref(v_e_x27_3482_);
lean_dec_ref_known(v_e_3443_, 2);
return v___x_3488_;
}
}
}
else
{
lean_dec_ref_known(v_a_3460_, 2);
lean_dec_ref_known(v_e_3443_, 2);
return v___x_3459_;
}
}
}
else
{
lean_dec_ref_known(v_e_3443_, 2);
return v___x_3459_;
}
}
case 5:
{
lean_object* v___x_3535_; 
lean_inc_ref(v_e_3443_);
v___x_3535_ = l_Lean_Meta_Tactic_Cbv_tryMatcher(v_e_3443_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_, v_a_3451_, v_a_3452_);
if (lean_obj_tag(v___x_3535_) == 0)
{
lean_object* v_a_3536_; 
v_a_3536_ = lean_ctor_get(v___x_3535_, 0);
lean_inc(v_a_3536_);
if (lean_obj_tag(v_a_3536_) == 0)
{
uint8_t v_done_3537_; 
v_done_3537_ = lean_ctor_get_uint8(v_a_3536_, 0);
if (v_done_3537_ == 0)
{
uint8_t v_contextDependent_3538_; lean_object* v___x_3539_; 
lean_dec_ref_known(v___x_3535_, 1);
v_contextDependent_3538_ = lean_ctor_get_uint8(v_a_3536_, 1);
lean_dec_ref_known(v_a_3536_, 0);
v___x_3539_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn(v_e_3443_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_, v_a_3451_, v_a_3452_);
if (lean_obj_tag(v___x_3539_) == 0)
{
lean_object* v_a_3540_; uint8_t v___y_3542_; 
v_a_3540_ = lean_ctor_get(v___x_3539_, 0);
lean_inc(v_a_3540_);
if (v_contextDependent_3538_ == 0)
{
lean_dec(v_a_3540_);
return v___x_3539_;
}
else
{
if (lean_obj_tag(v_a_3540_) == 0)
{
uint8_t v_contextDependent_3552_; uint8_t v___x_3553_; 
v_contextDependent_3552_ = lean_ctor_get_uint8(v_a_3540_, 1);
v___x_3553_ = lean_bool_not(v_contextDependent_3552_);
v___y_3542_ = v___x_3553_;
goto v___jp_3541_;
}
else
{
uint8_t v_contextDependent_3554_; uint8_t v___x_3555_; 
v_contextDependent_3554_ = lean_ctor_get_uint8(v_a_3540_, sizeof(void*)*2 + 1);
v___x_3555_ = lean_bool_not(v_contextDependent_3554_);
v___y_3542_ = v___x_3555_;
goto v___jp_3541_;
}
}
v___jp_3541_:
{
if (v___y_3542_ == 0)
{
lean_dec(v_a_3540_);
return v___x_3539_;
}
else
{
lean_object* v___x_3544_; uint8_t v_isShared_3545_; uint8_t v_isSharedCheck_3550_; 
v_isSharedCheck_3550_ = !lean_is_exclusive(v___x_3539_);
if (v_isSharedCheck_3550_ == 0)
{
lean_object* v_unused_3551_; 
v_unused_3551_ = lean_ctor_get(v___x_3539_, 0);
lean_dec(v_unused_3551_);
v___x_3544_ = v___x_3539_;
v_isShared_3545_ = v_isSharedCheck_3550_;
goto v_resetjp_3543_;
}
else
{
lean_dec(v___x_3539_);
v___x_3544_ = lean_box(0);
v_isShared_3545_ = v_isSharedCheck_3550_;
goto v_resetjp_3543_;
}
v_resetjp_3543_:
{
lean_object* v___x_3546_; lean_object* v___x_3548_; 
v___x_3546_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3540_);
if (v_isShared_3545_ == 0)
{
lean_ctor_set(v___x_3544_, 0, v___x_3546_);
v___x_3548_ = v___x_3544_;
goto v_reusejp_3547_;
}
else
{
lean_object* v_reuseFailAlloc_3549_; 
v_reuseFailAlloc_3549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3549_, 0, v___x_3546_);
v___x_3548_ = v_reuseFailAlloc_3549_;
goto v_reusejp_3547_;
}
v_reusejp_3547_:
{
return v___x_3548_;
}
}
}
}
}
else
{
return v___x_3539_;
}
}
else
{
lean_dec_ref_known(v_a_3536_, 0);
lean_dec_ref_known(v_e_3443_, 2);
return v___x_3535_;
}
}
else
{
lean_dec_ref_known(v_a_3536_, 2);
lean_dec_ref_known(v_e_3443_, 2);
return v___x_3535_;
}
}
else
{
lean_dec_ref_known(v_e_3443_, 2);
return v___x_3535_;
}
}
case 8:
{
uint8_t v___x_3556_; 
v___x_3556_ = l_Lean_Expr_letNondep_x21(v_e_3443_);
if (v___x_3556_ == 0)
{
lean_object* v___x_3557_; 
v___x_3557_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg(v_e_3443_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_, v_a_3451_, v_a_3452_);
return v___x_3557_;
}
else
{
lean_object* v___x_3558_; 
v___x_3558_ = l_Lean_Meta_Sym_Simp_toBetaApp(v_e_3443_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_, v_a_3451_, v_a_3452_);
if (lean_obj_tag(v___x_3558_) == 0)
{
lean_object* v_a_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3570_; 
v_a_3559_ = lean_ctor_get(v___x_3558_, 0);
v_isSharedCheck_3570_ = !lean_is_exclusive(v___x_3558_);
if (v_isSharedCheck_3570_ == 0)
{
v___x_3561_ = v___x_3558_;
v_isShared_3562_ = v_isSharedCheck_3570_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_a_3559_);
lean_dec(v___x_3558_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3570_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
lean_object* v_e_3563_; lean_object* v_h_3564_; uint8_t v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3568_; 
v_e_3563_ = lean_ctor_get(v_a_3559_, 2);
lean_inc_ref(v_e_3563_);
v_h_3564_ = lean_ctor_get(v_a_3559_, 3);
lean_inc_ref(v_h_3564_);
lean_dec(v_a_3559_);
v___x_3565_ = 0;
v___x_3566_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3566_, 0, v_e_3563_);
lean_ctor_set(v___x_3566_, 1, v_h_3564_);
lean_ctor_set_uint8(v___x_3566_, sizeof(void*)*2, v___x_3565_);
lean_ctor_set_uint8(v___x_3566_, sizeof(void*)*2 + 1, v___x_3565_);
if (v_isShared_3562_ == 0)
{
lean_ctor_set(v___x_3561_, 0, v___x_3566_);
v___x_3568_ = v___x_3561_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v___x_3566_);
v___x_3568_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
return v___x_3568_;
}
}
}
else
{
lean_object* v_a_3571_; lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3578_; 
v_a_3571_ = lean_ctor_get(v___x_3558_, 0);
v_isSharedCheck_3578_ = !lean_is_exclusive(v___x_3558_);
if (v_isSharedCheck_3578_ == 0)
{
v___x_3573_ = v___x_3558_;
v_isShared_3574_ = v_isSharedCheck_3578_;
goto v_resetjp_3572_;
}
else
{
lean_inc(v_a_3571_);
lean_dec(v___x_3558_);
v___x_3573_ = lean_box(0);
v_isShared_3574_ = v_isSharedCheck_3578_;
goto v_resetjp_3572_;
}
v_resetjp_3572_:
{
lean_object* v___x_3576_; 
if (v_isShared_3574_ == 0)
{
v___x_3576_ = v___x_3573_;
goto v_reusejp_3575_;
}
else
{
lean_object* v_reuseFailAlloc_3577_; 
v_reuseFailAlloc_3577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3577_, 0, v_a_3571_);
v___x_3576_ = v_reuseFailAlloc_3577_;
goto v_reusejp_3575_;
}
v_reusejp_3575_:
{
return v___x_3576_;
}
}
}
}
}
case 7:
{
lean_dec_ref_known(v_e_3443_, 3);
goto v___jp_3454_;
}
case 6:
{
lean_dec_ref_known(v_e_3443_, 3);
goto v___jp_3454_;
}
case 1:
{
lean_object* v___x_3579_; lean_object* v___x_3580_; 
lean_dec_ref_known(v_e_3443_, 1);
v___x_3579_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___closed__0));
v___x_3580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3580_, 0, v___x_3579_);
return v___x_3580_;
}
case 2:
{
lean_object* v___x_3581_; lean_object* v___x_3582_; 
lean_dec_ref_known(v_e_3443_, 1);
v___x_3581_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___closed__0));
v___x_3582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3582_, 0, v___x_3581_);
return v___x_3582_;
}
case 0:
{
lean_object* v___x_3583_; lean_object* v___x_3584_; 
lean_dec_ref_known(v_e_3443_, 1);
v___x_3583_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___closed__0));
v___x_3584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3584_, 0, v___x_3583_);
return v___x_3584_;
}
case 3:
{
lean_object* v___x_3585_; lean_object* v___x_3586_; 
lean_dec_ref_known(v_e_3443_, 1);
v___x_3585_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___closed__0));
v___x_3586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3586_, 0, v___x_3585_);
return v___x_3586_;
}
default: 
{
lean_object* v___x_3587_; lean_object* v___x_3588_; 
lean_dec_ref(v_e_3443_);
v___x_3587_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
v___x_3588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3588_, 0, v___x_3587_);
return v___x_3588_;
}
}
v___jp_3454_:
{
lean_object* v___x_3455_; lean_object* v___x_3456_; 
v___x_3455_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___closed__0));
v___x_3456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3456_, 0, v___x_3455_);
return v___x_3456_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___boxed(lean_object* v_e_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_, lean_object* v_a_3596_, lean_object* v_a_3597_, lean_object* v_a_3598_, lean_object* v_a_3599_){
_start:
{
lean_object* v_res_3600_; 
v_res_3600_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep(v_e_3589_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_, v_a_3598_);
lean_dec(v_a_3598_);
lean_dec_ref(v_a_3597_);
lean_dec(v_a_3596_);
lean_dec_ref(v_a_3595_);
lean_dec(v_a_3594_);
lean_dec_ref(v_a_3593_);
lean_dec(v_a_3592_);
lean_dec_ref(v_a_3591_);
lean_dec(v_a_3590_);
return v_res_3600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPre(lean_object* v_simprocs_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_, lean_object* v_a_3604_, lean_object* v_a_3605_, lean_object* v_a_3606_, lean_object* v_a_3607_, lean_object* v_a_3608_, lean_object* v_a_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_){
_start:
{
lean_object* v___y_3614_; lean_object* v___y_3615_; uint8_t v___y_3616_; lean_object* v___x_3619_; 
lean_inc_ref(v_a_3602_);
v___x_3619_ = l_Lean_Meta_Tactic_Cbv_isBuiltinValue___redArg(v_a_3602_);
if (lean_obj_tag(v___x_3619_) == 0)
{
lean_object* v_a_3620_; 
v_a_3620_ = lean_ctor_get(v___x_3619_, 0);
lean_inc(v_a_3620_);
if (lean_obj_tag(v_a_3620_) == 0)
{
uint8_t v_done_3621_; uint8_t v_contextDependent_3622_; lean_object* v___y_3624_; lean_object* v_a_3625_; lean_object* v___y_3631_; lean_object* v___y_3632_; uint8_t v___y_3633_; lean_object* v___y_3637_; 
v_done_3621_ = lean_ctor_get_uint8(v_a_3620_, 0);
v_contextDependent_3622_ = lean_ctor_get_uint8(v_a_3620_, 1);
lean_dec_ref_known(v_a_3620_, 0);
if (v_done_3621_ == 0)
{
lean_object* v___x_3639_; 
lean_dec_ref_known(v___x_3619_, 1);
lean_inc_ref(v_a_3602_);
v___x_3639_ = l_Lean_Meta_Tactic_Cbv_isProofTerm___redArg(v_a_3602_, v_a_3606_, v_a_3607_, v_a_3608_, v_a_3609_, v_a_3610_, v_a_3611_);
if (lean_obj_tag(v___x_3639_) == 0)
{
lean_object* v_a_3640_; 
v_a_3640_ = lean_ctor_get(v___x_3639_, 0);
lean_inc(v_a_3640_);
if (lean_obj_tag(v_a_3640_) == 0)
{
uint8_t v_done_3641_; uint8_t v_contextDependent_3642_; lean_object* v___y_3644_; lean_object* v_a_3645_; lean_object* v___y_3651_; 
v_done_3641_ = lean_ctor_get_uint8(v_a_3640_, 0);
v_contextDependent_3642_ = lean_ctor_get_uint8(v_a_3640_, 1);
lean_dec_ref_known(v_a_3640_, 0);
if (v_done_3641_ == 0)
{
lean_object* v_pre_3653_; lean_object* v_erased_3654_; lean_object* v___x_3655_; 
lean_dec_ref_known(v___x_3639_, 1);
v_pre_3653_ = lean_ctor_get(v_simprocs_3601_, 0);
v_erased_3654_ = lean_ctor_get(v_simprocs_3601_, 4);
lean_inc_ref(v_a_3602_);
v___x_3655_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch(v_pre_3653_, v_erased_3654_, v_a_3602_, v_a_3603_, v_a_3604_, v_a_3605_, v_a_3606_, v_a_3607_, v_a_3608_, v_a_3609_, v_a_3610_, v_a_3611_);
if (lean_obj_tag(v___x_3655_) == 0)
{
lean_object* v_a_3656_; 
v_a_3656_ = lean_ctor_get(v___x_3655_, 0);
lean_inc(v_a_3656_);
if (lean_obj_tag(v_a_3656_) == 0)
{
uint8_t v_done_3657_; 
v_done_3657_ = lean_ctor_get_uint8(v_a_3656_, 0);
if (v_done_3657_ == 0)
{
uint8_t v_contextDependent_3658_; lean_object* v___x_3659_; 
lean_dec_ref_known(v___x_3655_, 1);
v_contextDependent_3658_ = lean_ctor_get_uint8(v_a_3656_, 1);
lean_dec_ref_known(v_a_3656_, 0);
v___x_3659_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep(v_a_3602_, v_a_3603_, v_a_3604_, v_a_3605_, v_a_3606_, v_a_3607_, v_a_3608_, v_a_3609_, v_a_3610_, v_a_3611_);
if (lean_obj_tag(v___x_3659_) == 0)
{
lean_object* v_a_3660_; uint8_t v___y_3662_; 
v_a_3660_ = lean_ctor_get(v___x_3659_, 0);
lean_inc(v_a_3660_);
if (v_contextDependent_3658_ == 0)
{
lean_dec(v_a_3660_);
v___y_3651_ = v___x_3659_;
goto v___jp_3650_;
}
else
{
if (lean_obj_tag(v_a_3660_) == 0)
{
uint8_t v_contextDependent_3672_; uint8_t v___x_3673_; 
v_contextDependent_3672_ = lean_ctor_get_uint8(v_a_3660_, 1);
v___x_3673_ = lean_bool_not(v_contextDependent_3672_);
v___y_3662_ = v___x_3673_;
goto v___jp_3661_;
}
else
{
uint8_t v_contextDependent_3674_; uint8_t v___x_3675_; 
v_contextDependent_3674_ = lean_ctor_get_uint8(v_a_3660_, sizeof(void*)*2 + 1);
v___x_3675_ = lean_bool_not(v_contextDependent_3674_);
v___y_3662_ = v___x_3675_;
goto v___jp_3661_;
}
}
v___jp_3661_:
{
if (v___y_3662_ == 0)
{
lean_dec(v_a_3660_);
v___y_3651_ = v___x_3659_;
goto v___jp_3650_;
}
else
{
lean_object* v___x_3664_; uint8_t v_isShared_3665_; uint8_t v_isSharedCheck_3670_; 
v_isSharedCheck_3670_ = !lean_is_exclusive(v___x_3659_);
if (v_isSharedCheck_3670_ == 0)
{
lean_object* v_unused_3671_; 
v_unused_3671_ = lean_ctor_get(v___x_3659_, 0);
lean_dec(v_unused_3671_);
v___x_3664_ = v___x_3659_;
v_isShared_3665_ = v_isSharedCheck_3670_;
goto v_resetjp_3663_;
}
else
{
lean_dec(v___x_3659_);
v___x_3664_ = lean_box(0);
v_isShared_3665_ = v_isSharedCheck_3670_;
goto v_resetjp_3663_;
}
v_resetjp_3663_:
{
lean_object* v___x_3666_; lean_object* v___x_3668_; 
v___x_3666_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3660_);
lean_inc_ref(v___x_3666_);
if (v_isShared_3665_ == 0)
{
lean_ctor_set(v___x_3664_, 0, v___x_3666_);
v___x_3668_ = v___x_3664_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v___x_3666_);
v___x_3668_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3667_;
}
v_reusejp_3667_:
{
v___y_3644_ = v___x_3668_;
v_a_3645_ = v___x_3666_;
goto v___jp_3643_;
}
}
}
}
}
else
{
v___y_3651_ = v___x_3659_;
goto v___jp_3650_;
}
}
else
{
lean_dec_ref_known(v_a_3656_, 0);
lean_dec_ref(v_a_3602_);
v___y_3651_ = v___x_3655_;
goto v___jp_3650_;
}
}
else
{
lean_dec_ref_known(v_a_3656_, 2);
lean_dec_ref(v_a_3602_);
v___y_3651_ = v___x_3655_;
goto v___jp_3650_;
}
}
else
{
lean_dec_ref(v_a_3602_);
v___y_3651_ = v___x_3655_;
goto v___jp_3650_;
}
}
else
{
lean_dec_ref(v_a_3602_);
v___y_3637_ = v___x_3639_;
goto v___jp_3636_;
}
v___jp_3643_:
{
if (v_contextDependent_3642_ == 0)
{
v___y_3624_ = v___y_3644_;
v_a_3625_ = v_a_3645_;
goto v___jp_3623_;
}
else
{
if (lean_obj_tag(v_a_3645_) == 0)
{
uint8_t v_contextDependent_3646_; uint8_t v___x_3647_; 
v_contextDependent_3646_ = lean_ctor_get_uint8(v_a_3645_, 1);
v___x_3647_ = lean_bool_not(v_contextDependent_3646_);
v___y_3631_ = v_a_3645_;
v___y_3632_ = v___y_3644_;
v___y_3633_ = v___x_3647_;
goto v___jp_3630_;
}
else
{
uint8_t v_contextDependent_3648_; uint8_t v___x_3649_; 
v_contextDependent_3648_ = lean_ctor_get_uint8(v_a_3645_, sizeof(void*)*2 + 1);
v___x_3649_ = lean_bool_not(v_contextDependent_3648_);
v___y_3631_ = v_a_3645_;
v___y_3632_ = v___y_3644_;
v___y_3633_ = v___x_3649_;
goto v___jp_3630_;
}
}
}
v___jp_3650_:
{
if (lean_obj_tag(v___y_3651_) == 0)
{
lean_object* v_a_3652_; 
v_a_3652_ = lean_ctor_get(v___y_3651_, 0);
lean_inc(v_a_3652_);
v___y_3644_ = v___y_3651_;
v_a_3645_ = v_a_3652_;
goto v___jp_3643_;
}
else
{
return v___y_3651_;
}
}
}
else
{
lean_dec_ref_known(v_a_3640_, 2);
lean_dec_ref(v_a_3602_);
v___y_3637_ = v___x_3639_;
goto v___jp_3636_;
}
}
else
{
lean_dec_ref(v_a_3602_);
v___y_3637_ = v___x_3639_;
goto v___jp_3636_;
}
}
else
{
lean_dec_ref(v_a_3602_);
return v___x_3619_;
}
v___jp_3623_:
{
if (v_contextDependent_3622_ == 0)
{
lean_dec_ref(v_a_3625_);
return v___y_3624_;
}
else
{
if (lean_obj_tag(v_a_3625_) == 0)
{
uint8_t v_contextDependent_3626_; uint8_t v___x_3627_; 
v_contextDependent_3626_ = lean_ctor_get_uint8(v_a_3625_, 1);
v___x_3627_ = lean_bool_not(v_contextDependent_3626_);
v___y_3614_ = v___y_3624_;
v___y_3615_ = v_a_3625_;
v___y_3616_ = v___x_3627_;
goto v___jp_3613_;
}
else
{
uint8_t v_contextDependent_3628_; uint8_t v___x_3629_; 
v_contextDependent_3628_ = lean_ctor_get_uint8(v_a_3625_, sizeof(void*)*2 + 1);
v___x_3629_ = lean_bool_not(v_contextDependent_3628_);
v___y_3614_ = v___y_3624_;
v___y_3615_ = v_a_3625_;
v___y_3616_ = v___x_3629_;
goto v___jp_3613_;
}
}
}
v___jp_3630_:
{
if (v___y_3633_ == 0)
{
v___y_3624_ = v___y_3632_;
v_a_3625_ = v___y_3631_;
goto v___jp_3623_;
}
else
{
lean_object* v___x_3634_; lean_object* v___x_3635_; 
lean_dec_ref(v___y_3632_);
v___x_3634_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_3631_);
lean_inc_ref(v___x_3634_);
v___x_3635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3635_, 0, v___x_3634_);
v___y_3624_ = v___x_3635_;
v_a_3625_ = v___x_3634_;
goto v___jp_3623_;
}
}
v___jp_3636_:
{
if (lean_obj_tag(v___y_3637_) == 0)
{
lean_object* v_a_3638_; 
v_a_3638_ = lean_ctor_get(v___y_3637_, 0);
lean_inc(v_a_3638_);
v___y_3624_ = v___y_3637_;
v_a_3625_ = v_a_3638_;
goto v___jp_3623_;
}
else
{
return v___y_3637_;
}
}
}
else
{
lean_dec_ref_known(v_a_3620_, 2);
lean_dec_ref(v_a_3602_);
return v___x_3619_;
}
}
else
{
lean_dec_ref(v_a_3602_);
return v___x_3619_;
}
v___jp_3613_:
{
if (v___y_3616_ == 0)
{
lean_dec_ref(v___y_3615_);
return v___y_3614_;
}
else
{
lean_object* v___x_3617_; lean_object* v___x_3618_; 
lean_dec_ref(v___y_3614_);
v___x_3617_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_3615_);
v___x_3618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3618_, 0, v___x_3617_);
return v___x_3618_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPre___boxed(lean_object* v_simprocs_3676_, lean_object* v_a_3677_, lean_object* v_a_3678_, lean_object* v_a_3679_, lean_object* v_a_3680_, lean_object* v_a_3681_, lean_object* v_a_3682_, lean_object* v_a_3683_, lean_object* v_a_3684_, lean_object* v_a_3685_, lean_object* v_a_3686_, lean_object* v_a_3687_){
_start:
{
lean_object* v_res_3688_; 
v_res_3688_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPre(v_simprocs_3676_, v_a_3677_, v_a_3678_, v_a_3679_, v_a_3680_, v_a_3681_, v_a_3682_, v_a_3683_, v_a_3684_, v_a_3685_, v_a_3686_);
lean_dec(v_a_3686_);
lean_dec_ref(v_a_3685_);
lean_dec(v_a_3684_);
lean_dec_ref(v_a_3683_);
lean_dec(v_a_3682_);
lean_dec_ref(v_a_3681_);
lean_dec(v_a_3680_);
lean_dec_ref(v_a_3679_);
lean_dec(v_a_3678_);
lean_dec_ref(v_simprocs_3676_);
return v_res_3688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPost(lean_object* v_simprocs_3689_, lean_object* v_a_3690_, lean_object* v_a_3691_, lean_object* v_a_3692_, lean_object* v_a_3693_, lean_object* v_a_3694_, lean_object* v_a_3695_, lean_object* v_a_3696_, lean_object* v_a_3697_, lean_object* v_a_3698_, lean_object* v_a_3699_){
_start:
{
lean_object* v___y_3702_; lean_object* v___y_3703_; uint8_t v___y_3704_; lean_object* v___x_3707_; lean_object* v___x_3708_; 
v___x_3707_ = lean_unsigned_to_nat(255u);
lean_inc_ref(v_a_3690_);
v___x_3708_ = l_Lean_Meta_Sym_Simp_evalGround___redArg(v___x_3707_, v_a_3690_, v_a_3694_, v_a_3695_, v_a_3696_, v_a_3697_, v_a_3698_, v_a_3699_);
if (lean_obj_tag(v___x_3708_) == 0)
{
lean_object* v_a_3709_; 
v_a_3709_ = lean_ctor_get(v___x_3708_, 0);
lean_inc(v_a_3709_);
if (lean_obj_tag(v_a_3709_) == 0)
{
uint8_t v_done_3710_; uint8_t v_contextDependent_3711_; lean_object* v___y_3713_; lean_object* v_a_3714_; lean_object* v___y_3720_; lean_object* v___y_3721_; uint8_t v___y_3722_; lean_object* v___y_3726_; 
v_done_3710_ = lean_ctor_get_uint8(v_a_3709_, 0);
v_contextDependent_3711_ = lean_ctor_get_uint8(v_a_3709_, 1);
lean_dec_ref_known(v_a_3709_, 0);
if (v_done_3710_ == 0)
{
lean_object* v_eval_3728_; lean_object* v_post_3729_; lean_object* v_erased_3730_; lean_object* v___x_3731_; 
lean_dec_ref_known(v___x_3708_, 1);
v_eval_3728_ = lean_ctor_get(v_simprocs_3689_, 1);
v_post_3729_ = lean_ctor_get(v_simprocs_3689_, 2);
v_erased_3730_ = lean_ctor_get(v_simprocs_3689_, 4);
lean_inc_ref(v_a_3690_);
v___x_3731_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch(v_eval_3728_, v_erased_3730_, v_a_3690_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_, v_a_3697_, v_a_3698_, v_a_3699_);
if (lean_obj_tag(v___x_3731_) == 0)
{
lean_object* v_a_3732_; 
v_a_3732_ = lean_ctor_get(v___x_3731_, 0);
lean_inc(v_a_3732_);
if (lean_obj_tag(v_a_3732_) == 0)
{
uint8_t v_done_3733_; uint8_t v_contextDependent_3734_; lean_object* v___y_3736_; lean_object* v_a_3737_; lean_object* v___y_3743_; 
v_done_3733_ = lean_ctor_get_uint8(v_a_3732_, 0);
v_contextDependent_3734_ = lean_ctor_get_uint8(v_a_3732_, 1);
lean_dec_ref_known(v_a_3732_, 0);
if (v_done_3733_ == 0)
{
lean_object* v___x_3745_; 
lean_dec_ref_known(v___x_3731_, 1);
lean_inc_ref(v_a_3690_);
v___x_3745_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp(v_a_3690_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_, v_a_3697_, v_a_3698_, v_a_3699_);
if (lean_obj_tag(v___x_3745_) == 0)
{
lean_object* v_a_3746_; 
v_a_3746_ = lean_ctor_get(v___x_3745_, 0);
lean_inc(v_a_3746_);
if (lean_obj_tag(v_a_3746_) == 0)
{
uint8_t v_done_3747_; 
v_done_3747_ = lean_ctor_get_uint8(v_a_3746_, 0);
if (v_done_3747_ == 0)
{
uint8_t v_contextDependent_3748_; lean_object* v___x_3749_; 
lean_dec_ref_known(v___x_3745_, 1);
v_contextDependent_3748_ = lean_ctor_get_uint8(v_a_3746_, 1);
lean_dec_ref_known(v_a_3746_, 0);
v___x_3749_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch(v_post_3729_, v_erased_3730_, v_a_3690_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_, v_a_3697_, v_a_3698_, v_a_3699_);
if (lean_obj_tag(v___x_3749_) == 0)
{
lean_object* v_a_3750_; uint8_t v___y_3752_; 
v_a_3750_ = lean_ctor_get(v___x_3749_, 0);
lean_inc(v_a_3750_);
if (v_contextDependent_3748_ == 0)
{
lean_dec(v_a_3750_);
v___y_3743_ = v___x_3749_;
goto v___jp_3742_;
}
else
{
if (lean_obj_tag(v_a_3750_) == 0)
{
uint8_t v_contextDependent_3762_; uint8_t v___x_3763_; 
v_contextDependent_3762_ = lean_ctor_get_uint8(v_a_3750_, 1);
v___x_3763_ = lean_bool_not(v_contextDependent_3762_);
v___y_3752_ = v___x_3763_;
goto v___jp_3751_;
}
else
{
uint8_t v_contextDependent_3764_; uint8_t v___x_3765_; 
v_contextDependent_3764_ = lean_ctor_get_uint8(v_a_3750_, sizeof(void*)*2 + 1);
v___x_3765_ = lean_bool_not(v_contextDependent_3764_);
v___y_3752_ = v___x_3765_;
goto v___jp_3751_;
}
}
v___jp_3751_:
{
if (v___y_3752_ == 0)
{
lean_dec(v_a_3750_);
v___y_3743_ = v___x_3749_;
goto v___jp_3742_;
}
else
{
lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_3760_; 
v_isSharedCheck_3760_ = !lean_is_exclusive(v___x_3749_);
if (v_isSharedCheck_3760_ == 0)
{
lean_object* v_unused_3761_; 
v_unused_3761_ = lean_ctor_get(v___x_3749_, 0);
lean_dec(v_unused_3761_);
v___x_3754_ = v___x_3749_;
v_isShared_3755_ = v_isSharedCheck_3760_;
goto v_resetjp_3753_;
}
else
{
lean_dec(v___x_3749_);
v___x_3754_ = lean_box(0);
v_isShared_3755_ = v_isSharedCheck_3760_;
goto v_resetjp_3753_;
}
v_resetjp_3753_:
{
lean_object* v___x_3756_; lean_object* v___x_3758_; 
v___x_3756_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3750_);
lean_inc_ref(v___x_3756_);
if (v_isShared_3755_ == 0)
{
lean_ctor_set(v___x_3754_, 0, v___x_3756_);
v___x_3758_ = v___x_3754_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3759_; 
v_reuseFailAlloc_3759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3759_, 0, v___x_3756_);
v___x_3758_ = v_reuseFailAlloc_3759_;
goto v_reusejp_3757_;
}
v_reusejp_3757_:
{
v___y_3736_ = v___x_3758_;
v_a_3737_ = v___x_3756_;
goto v___jp_3735_;
}
}
}
}
}
else
{
v___y_3743_ = v___x_3749_;
goto v___jp_3742_;
}
}
else
{
lean_dec_ref_known(v_a_3746_, 0);
lean_dec_ref(v_a_3690_);
v___y_3743_ = v___x_3745_;
goto v___jp_3742_;
}
}
else
{
lean_dec_ref_known(v_a_3746_, 2);
lean_dec_ref(v_a_3690_);
v___y_3743_ = v___x_3745_;
goto v___jp_3742_;
}
}
else
{
lean_dec_ref(v_a_3690_);
v___y_3743_ = v___x_3745_;
goto v___jp_3742_;
}
}
else
{
lean_dec_ref(v_a_3690_);
v___y_3726_ = v___x_3731_;
goto v___jp_3725_;
}
v___jp_3735_:
{
if (v_contextDependent_3734_ == 0)
{
v___y_3713_ = v___y_3736_;
v_a_3714_ = v_a_3737_;
goto v___jp_3712_;
}
else
{
if (lean_obj_tag(v_a_3737_) == 0)
{
uint8_t v_contextDependent_3738_; uint8_t v___x_3739_; 
v_contextDependent_3738_ = lean_ctor_get_uint8(v_a_3737_, 1);
v___x_3739_ = lean_bool_not(v_contextDependent_3738_);
v___y_3720_ = v_a_3737_;
v___y_3721_ = v___y_3736_;
v___y_3722_ = v___x_3739_;
goto v___jp_3719_;
}
else
{
uint8_t v_contextDependent_3740_; uint8_t v___x_3741_; 
v_contextDependent_3740_ = lean_ctor_get_uint8(v_a_3737_, sizeof(void*)*2 + 1);
v___x_3741_ = lean_bool_not(v_contextDependent_3740_);
v___y_3720_ = v_a_3737_;
v___y_3721_ = v___y_3736_;
v___y_3722_ = v___x_3741_;
goto v___jp_3719_;
}
}
}
v___jp_3742_:
{
if (lean_obj_tag(v___y_3743_) == 0)
{
lean_object* v_a_3744_; 
v_a_3744_ = lean_ctor_get(v___y_3743_, 0);
lean_inc(v_a_3744_);
v___y_3736_ = v___y_3743_;
v_a_3737_ = v_a_3744_;
goto v___jp_3735_;
}
else
{
return v___y_3743_;
}
}
}
else
{
lean_dec_ref_known(v_a_3732_, 2);
lean_dec_ref(v_a_3690_);
v___y_3726_ = v___x_3731_;
goto v___jp_3725_;
}
}
else
{
lean_dec_ref(v_a_3690_);
v___y_3726_ = v___x_3731_;
goto v___jp_3725_;
}
}
else
{
lean_dec_ref(v_a_3690_);
return v___x_3708_;
}
v___jp_3712_:
{
if (v_contextDependent_3711_ == 0)
{
lean_dec_ref(v_a_3714_);
return v___y_3713_;
}
else
{
if (lean_obj_tag(v_a_3714_) == 0)
{
uint8_t v_contextDependent_3715_; uint8_t v___x_3716_; 
v_contextDependent_3715_ = lean_ctor_get_uint8(v_a_3714_, 1);
v___x_3716_ = lean_bool_not(v_contextDependent_3715_);
v___y_3702_ = v___y_3713_;
v___y_3703_ = v_a_3714_;
v___y_3704_ = v___x_3716_;
goto v___jp_3701_;
}
else
{
uint8_t v_contextDependent_3717_; uint8_t v___x_3718_; 
v_contextDependent_3717_ = lean_ctor_get_uint8(v_a_3714_, sizeof(void*)*2 + 1);
v___x_3718_ = lean_bool_not(v_contextDependent_3717_);
v___y_3702_ = v___y_3713_;
v___y_3703_ = v_a_3714_;
v___y_3704_ = v___x_3718_;
goto v___jp_3701_;
}
}
}
v___jp_3719_:
{
if (v___y_3722_ == 0)
{
v___y_3713_ = v___y_3721_;
v_a_3714_ = v___y_3720_;
goto v___jp_3712_;
}
else
{
lean_object* v___x_3723_; lean_object* v___x_3724_; 
lean_dec_ref(v___y_3721_);
v___x_3723_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_3720_);
lean_inc_ref(v___x_3723_);
v___x_3724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3724_, 0, v___x_3723_);
v___y_3713_ = v___x_3724_;
v_a_3714_ = v___x_3723_;
goto v___jp_3712_;
}
}
v___jp_3725_:
{
if (lean_obj_tag(v___y_3726_) == 0)
{
lean_object* v_a_3727_; 
v_a_3727_ = lean_ctor_get(v___y_3726_, 0);
lean_inc(v_a_3727_);
v___y_3713_ = v___y_3726_;
v_a_3714_ = v_a_3727_;
goto v___jp_3712_;
}
else
{
return v___y_3726_;
}
}
}
else
{
lean_dec_ref_known(v_a_3709_, 2);
lean_dec_ref(v_a_3690_);
return v___x_3708_;
}
}
else
{
lean_dec_ref(v_a_3690_);
return v___x_3708_;
}
v___jp_3701_:
{
if (v___y_3704_ == 0)
{
lean_dec_ref(v___y_3703_);
return v___y_3702_;
}
else
{
lean_object* v___x_3705_; lean_object* v___x_3706_; 
lean_dec_ref(v___y_3702_);
v___x_3705_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_3703_);
v___x_3706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3706_, 0, v___x_3705_);
return v___x_3706_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPost___boxed(lean_object* v_simprocs_3766_, lean_object* v_a_3767_, lean_object* v_a_3768_, lean_object* v_a_3769_, lean_object* v_a_3770_, lean_object* v_a_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_, lean_object* v_a_3777_){
_start:
{
lean_object* v_res_3778_; 
v_res_3778_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPost(v_simprocs_3766_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_);
lean_dec(v_a_3776_);
lean_dec_ref(v_a_3775_);
lean_dec(v_a_3774_);
lean_dec_ref(v_a_3773_);
lean_dec(v_a_3772_);
lean_dec_ref(v_a_3771_);
lean_dec(v_a_3770_);
lean_dec_ref(v_a_3769_);
lean_dec(v_a_3768_);
lean_dec_ref(v_simprocs_3766_);
return v_res_3778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(lean_object* v_simprocs_3779_){
_start:
{
lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; 
lean_inc_ref(v_simprocs_3779_);
v___x_3780_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPre___boxed), 12, 1);
lean_closure_set(v___x_3780_, 0, v_simprocs_3779_);
v___x_3781_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPost___boxed), 12, 1);
lean_closure_set(v___x_3781_, 0, v_simprocs_3779_);
v___x_3782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3782_, 0, v___x_3780_);
lean_ctor_set(v___x_3782_, 1, v___x_3781_);
return v___x_3782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0___redArg(lean_object* v_x_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_){
_start:
{
lean_object* v_config_3791_; lean_object* v_sharedExprs_3792_; uint8_t v_verbose_3793_; uint8_t v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; 
v_config_3791_ = lean_ctor_get(v___y_3784_, 1);
v_sharedExprs_3792_ = lean_ctor_get(v___y_3784_, 0);
v_verbose_3793_ = lean_ctor_get_uint8(v_config_3791_, 0);
v___x_3794_ = 0;
v___x_3795_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v___x_3795_, 0, v_verbose_3793_);
lean_ctor_set_uint8(v___x_3795_, 1, v___x_3794_);
lean_ctor_set_uint8(v___x_3795_, 2, v___x_3794_);
lean_inc_ref(v_sharedExprs_3792_);
v___x_3796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3796_, 0, v_sharedExprs_3792_);
lean_ctor_set(v___x_3796_, 1, v___x_3795_);
lean_inc(v___y_3789_);
lean_inc_ref(v___y_3788_);
lean_inc(v___y_3787_);
lean_inc_ref(v___y_3786_);
lean_inc(v___y_3785_);
v___x_3797_ = lean_apply_7(v_x_3783_, v___x_3796_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_, lean_box(0));
return v___x_3797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0___redArg___boxed(lean_object* v_x_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_){
_start:
{
lean_object* v_res_3806_; 
v_res_3806_ = l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0___redArg(v_x_3798_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_);
lean_dec(v___y_3804_);
lean_dec_ref(v___y_3803_);
lean_dec(v___y_3802_);
lean_dec_ref(v___y_3801_);
lean_dec(v___y_3800_);
lean_dec_ref(v___y_3799_);
return v_res_3806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0(lean_object* v_00_u03b1_3807_, lean_object* v_x_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_){
_start:
{
lean_object* v___x_3816_; 
v___x_3816_ = l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0___redArg(v_x_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_);
return v___x_3816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0___boxed(lean_object* v_00_u03b1_3817_, lean_object* v_x_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_){
_start:
{
lean_object* v_res_3826_; 
v_res_3826_ = l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0(v_00_u03b1_3817_, v_x_3818_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_);
lean_dec(v___y_3824_);
lean_dec_ref(v___y_3823_);
lean_dec(v___y_3822_);
lean_dec_ref(v___y_3821_);
lean_dec(v___y_3820_);
lean_dec_ref(v___y_3819_);
return v_res_3826_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore___lam__0(lean_object* v_e_3827_, lean_object* v_config_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_){
_start:
{
lean_object* v___x_3836_; 
v___x_3836_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v___y_3834_);
if (lean_obj_tag(v___x_3836_) == 0)
{
lean_object* v_a_3837_; lean_object* v_methods_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; 
v_a_3837_ = lean_ctor_get(v___x_3836_, 0);
lean_inc(v_a_3837_);
lean_dec_ref_known(v___x_3836_, 1);
v_methods_3838_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(v_a_3837_);
v___x_3839_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_3839_, 0, v_e_3827_);
v___x_3840_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v___x_3839_, v_methods_3838_, v_config_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_);
return v___x_3840_;
}
else
{
lean_object* v_a_3841_; lean_object* v___x_3843_; uint8_t v_isShared_3844_; uint8_t v_isSharedCheck_3848_; 
lean_dec_ref(v_config_3828_);
lean_dec_ref(v_e_3827_);
v_a_3841_ = lean_ctor_get(v___x_3836_, 0);
v_isSharedCheck_3848_ = !lean_is_exclusive(v___x_3836_);
if (v_isSharedCheck_3848_ == 0)
{
v___x_3843_ = v___x_3836_;
v_isShared_3844_ = v_isSharedCheck_3848_;
goto v_resetjp_3842_;
}
else
{
lean_inc(v_a_3841_);
lean_dec(v___x_3836_);
v___x_3843_ = lean_box(0);
v_isShared_3844_ = v_isSharedCheck_3848_;
goto v_resetjp_3842_;
}
v_resetjp_3842_:
{
lean_object* v___x_3846_; 
if (v_isShared_3844_ == 0)
{
v___x_3846_ = v___x_3843_;
goto v_reusejp_3845_;
}
else
{
lean_object* v_reuseFailAlloc_3847_; 
v_reuseFailAlloc_3847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3847_, 0, v_a_3841_);
v___x_3846_ = v_reuseFailAlloc_3847_;
goto v_reusejp_3845_;
}
v_reusejp_3845_:
{
return v___x_3846_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore___lam__0___boxed(lean_object* v_e_3849_, lean_object* v_config_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_){
_start:
{
lean_object* v_res_3858_; 
v_res_3858_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore___lam__0(v_e_3849_, v_config_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_);
lean_dec(v___y_3856_);
lean_dec_ref(v___y_3855_);
lean_dec(v___y_3854_);
lean_dec_ref(v___y_3853_);
lean_dec(v___y_3852_);
lean_dec_ref(v___y_3851_);
return v_res_3858_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(lean_object* v_e_3859_, lean_object* v_config_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_, lean_object* v_a_3865_, lean_object* v_a_3866_){
_start:
{
lean_object* v___f_3868_; lean_object* v___x_3869_; 
v___f_3868_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore___lam__0___boxed), 9, 2);
lean_closure_set(v___f_3868_, 0, v_e_3859_);
lean_closure_set(v___f_3868_, 1, v_config_3860_);
v___x_3869_ = l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0___redArg(v___f_3868_, v_a_3861_, v_a_3862_, v_a_3863_, v_a_3864_, v_a_3865_, v_a_3866_);
return v___x_3869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore___boxed(lean_object* v_e_3870_, lean_object* v_config_3871_, lean_object* v_a_3872_, lean_object* v_a_3873_, lean_object* v_a_3874_, lean_object* v_a_3875_, lean_object* v_a_3876_, lean_object* v_a_3877_, lean_object* v_a_3878_){
_start:
{
lean_object* v_res_3879_; 
v_res_3879_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v_e_3870_, v_config_3871_, v_a_3872_, v_a_3873_, v_a_3874_, v_a_3875_, v_a_3876_, v_a_3877_);
lean_dec(v_a_3877_);
lean_dec_ref(v_a_3876_);
lean_dec(v_a_3875_);
lean_dec_ref(v_a_3874_);
lean_dec(v_a_3873_);
lean_dec_ref(v_a_3872_);
return v_res_3879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg(lean_object* v___y_3880_){
_start:
{
lean_object* v___x_3882_; lean_object* v_traceState_3883_; lean_object* v_traces_3884_; lean_object* v___x_3885_; lean_object* v_traceState_3886_; lean_object* v_env_3887_; lean_object* v_nextMacroScope_3888_; lean_object* v_ngen_3889_; lean_object* v_auxDeclNGen_3890_; lean_object* v_cache_3891_; lean_object* v_messages_3892_; lean_object* v_infoState_3893_; lean_object* v_snapshotTasks_3894_; lean_object* v___x_3896_; uint8_t v_isShared_3897_; uint8_t v_isSharedCheck_3915_; 
v___x_3882_ = lean_st_ref_get(v___y_3880_);
v_traceState_3883_ = lean_ctor_get(v___x_3882_, 4);
lean_inc_ref(v_traceState_3883_);
lean_dec(v___x_3882_);
v_traces_3884_ = lean_ctor_get(v_traceState_3883_, 0);
lean_inc_ref(v_traces_3884_);
lean_dec_ref(v_traceState_3883_);
v___x_3885_ = lean_st_ref_take(v___y_3880_);
v_traceState_3886_ = lean_ctor_get(v___x_3885_, 4);
v_env_3887_ = lean_ctor_get(v___x_3885_, 0);
v_nextMacroScope_3888_ = lean_ctor_get(v___x_3885_, 1);
v_ngen_3889_ = lean_ctor_get(v___x_3885_, 2);
v_auxDeclNGen_3890_ = lean_ctor_get(v___x_3885_, 3);
v_cache_3891_ = lean_ctor_get(v___x_3885_, 5);
v_messages_3892_ = lean_ctor_get(v___x_3885_, 6);
v_infoState_3893_ = lean_ctor_get(v___x_3885_, 7);
v_snapshotTasks_3894_ = lean_ctor_get(v___x_3885_, 8);
v_isSharedCheck_3915_ = !lean_is_exclusive(v___x_3885_);
if (v_isSharedCheck_3915_ == 0)
{
v___x_3896_ = v___x_3885_;
v_isShared_3897_ = v_isSharedCheck_3915_;
goto v_resetjp_3895_;
}
else
{
lean_inc(v_snapshotTasks_3894_);
lean_inc(v_infoState_3893_);
lean_inc(v_messages_3892_);
lean_inc(v_cache_3891_);
lean_inc(v_traceState_3886_);
lean_inc(v_auxDeclNGen_3890_);
lean_inc(v_ngen_3889_);
lean_inc(v_nextMacroScope_3888_);
lean_inc(v_env_3887_);
lean_dec(v___x_3885_);
v___x_3896_ = lean_box(0);
v_isShared_3897_ = v_isSharedCheck_3915_;
goto v_resetjp_3895_;
}
v_resetjp_3895_:
{
uint64_t v_tid_3898_; lean_object* v___x_3900_; uint8_t v_isShared_3901_; uint8_t v_isSharedCheck_3913_; 
v_tid_3898_ = lean_ctor_get_uint64(v_traceState_3886_, sizeof(void*)*1);
v_isSharedCheck_3913_ = !lean_is_exclusive(v_traceState_3886_);
if (v_isSharedCheck_3913_ == 0)
{
lean_object* v_unused_3914_; 
v_unused_3914_ = lean_ctor_get(v_traceState_3886_, 0);
lean_dec(v_unused_3914_);
v___x_3900_ = v_traceState_3886_;
v_isShared_3901_ = v_isSharedCheck_3913_;
goto v_resetjp_3899_;
}
else
{
lean_dec(v_traceState_3886_);
v___x_3900_ = lean_box(0);
v_isShared_3901_ = v_isSharedCheck_3913_;
goto v_resetjp_3899_;
}
v_resetjp_3899_:
{
lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3906_; 
v___x_3902_ = lean_unsigned_to_nat(32u);
v___x_3903_ = lean_mk_empty_array_with_capacity(v___x_3902_);
lean_dec_ref(v___x_3903_);
v___x_3904_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1);
if (v_isShared_3901_ == 0)
{
lean_ctor_set(v___x_3900_, 0, v___x_3904_);
v___x_3906_ = v___x_3900_;
goto v_reusejp_3905_;
}
else
{
lean_object* v_reuseFailAlloc_3912_; 
v_reuseFailAlloc_3912_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3912_, 0, v___x_3904_);
lean_ctor_set_uint64(v_reuseFailAlloc_3912_, sizeof(void*)*1, v_tid_3898_);
v___x_3906_ = v_reuseFailAlloc_3912_;
goto v_reusejp_3905_;
}
v_reusejp_3905_:
{
lean_object* v___x_3908_; 
if (v_isShared_3897_ == 0)
{
lean_ctor_set(v___x_3896_, 4, v___x_3906_);
v___x_3908_ = v___x_3896_;
goto v_reusejp_3907_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v_env_3887_);
lean_ctor_set(v_reuseFailAlloc_3911_, 1, v_nextMacroScope_3888_);
lean_ctor_set(v_reuseFailAlloc_3911_, 2, v_ngen_3889_);
lean_ctor_set(v_reuseFailAlloc_3911_, 3, v_auxDeclNGen_3890_);
lean_ctor_set(v_reuseFailAlloc_3911_, 4, v___x_3906_);
lean_ctor_set(v_reuseFailAlloc_3911_, 5, v_cache_3891_);
lean_ctor_set(v_reuseFailAlloc_3911_, 6, v_messages_3892_);
lean_ctor_set(v_reuseFailAlloc_3911_, 7, v_infoState_3893_);
lean_ctor_set(v_reuseFailAlloc_3911_, 8, v_snapshotTasks_3894_);
v___x_3908_ = v_reuseFailAlloc_3911_;
goto v_reusejp_3907_;
}
v_reusejp_3907_:
{
lean_object* v___x_3909_; lean_object* v___x_3910_; 
v___x_3909_ = lean_st_ref_set(v___y_3880_, v___x_3908_);
v___x_3910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3910_, 0, v_traces_3884_);
return v___x_3910_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg___boxed(lean_object* v___y_3916_, lean_object* v___y_3917_){
_start:
{
lean_object* v_res_3918_; 
v_res_3918_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg(v___y_3916_);
lean_dec(v___y_3916_);
return v_res_3918_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0(lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_){
_start:
{
lean_object* v___x_3924_; 
v___x_3924_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg(v___y_3922_);
return v___x_3924_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___boxed(lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_){
_start:
{
lean_object* v_res_3930_; 
v_res_3930_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0(v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_);
lean_dec(v___y_3928_);
lean_dec_ref(v___y_3927_);
lean_dec(v___y_3926_);
lean_dec_ref(v___y_3925_);
return v_res_3930_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3932_; lean_object* v___x_3933_; 
v___x_3932_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___closed__0));
v___x_3933_ = l_Lean_stringToMessageData(v___x_3932_);
return v___x_3933_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3935_; lean_object* v___x_3936_; 
v___x_3935_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___closed__2));
v___x_3936_ = l_Lean_stringToMessageData(v___x_3935_);
return v___x_3936_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3938_; lean_object* v___x_3939_; 
v___x_3938_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___closed__4));
v___x_3939_ = l_Lean_stringToMessageData(v___x_3938_);
return v___x_3939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0(lean_object* v_e_3940_, lean_object* v_x_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_){
_start:
{
if (lean_obj_tag(v_x_3941_) == 0)
{
lean_object* v_a_3947_; lean_object* v___x_3949_; uint8_t v_isShared_3950_; uint8_t v_isSharedCheck_3957_; 
lean_dec_ref(v_e_3940_);
v_a_3947_ = lean_ctor_get(v_x_3941_, 0);
v_isSharedCheck_3957_ = !lean_is_exclusive(v_x_3941_);
if (v_isSharedCheck_3957_ == 0)
{
v___x_3949_ = v_x_3941_;
v_isShared_3950_ = v_isSharedCheck_3957_;
goto v_resetjp_3948_;
}
else
{
lean_inc(v_a_3947_);
lean_dec(v_x_3941_);
v___x_3949_ = lean_box(0);
v_isShared_3950_ = v_isSharedCheck_3957_;
goto v_resetjp_3948_;
}
v_resetjp_3948_:
{
lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3955_; 
v___x_3951_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___closed__1);
v___x_3952_ = l_Lean_Exception_toMessageData(v_a_3947_);
v___x_3953_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3953_, 0, v___x_3951_);
lean_ctor_set(v___x_3953_, 1, v___x_3952_);
if (v_isShared_3950_ == 0)
{
lean_ctor_set(v___x_3949_, 0, v___x_3953_);
v___x_3955_ = v___x_3949_;
goto v_reusejp_3954_;
}
else
{
lean_object* v_reuseFailAlloc_3956_; 
v_reuseFailAlloc_3956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3956_, 0, v___x_3953_);
v___x_3955_ = v_reuseFailAlloc_3956_;
goto v_reusejp_3954_;
}
v_reusejp_3954_:
{
return v___x_3955_;
}
}
}
else
{
lean_object* v_a_3958_; lean_object* v___x_3960_; uint8_t v_isShared_3961_; uint8_t v_isSharedCheck_3979_; 
v_a_3958_ = lean_ctor_get(v_x_3941_, 0);
v_isSharedCheck_3979_ = !lean_is_exclusive(v_x_3941_);
if (v_isSharedCheck_3979_ == 0)
{
v___x_3960_ = v_x_3941_;
v_isShared_3961_ = v_isSharedCheck_3979_;
goto v_resetjp_3959_;
}
else
{
lean_inc(v_a_3958_);
lean_dec(v_x_3941_);
v___x_3960_ = lean_box(0);
v_isShared_3961_ = v_isSharedCheck_3979_;
goto v_resetjp_3959_;
}
v_resetjp_3959_:
{
if (lean_obj_tag(v_a_3958_) == 0)
{
lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3966_; 
lean_dec_ref_known(v_a_3958_, 0);
v___x_3962_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___closed__3, &l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___closed__3);
v___x_3963_ = l_Lean_indentExpr(v_e_3940_);
v___x_3964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3964_, 0, v___x_3962_);
lean_ctor_set(v___x_3964_, 1, v___x_3963_);
if (v_isShared_3961_ == 0)
{
lean_ctor_set_tag(v___x_3960_, 0);
lean_ctor_set(v___x_3960_, 0, v___x_3964_);
v___x_3966_ = v___x_3960_;
goto v_reusejp_3965_;
}
else
{
lean_object* v_reuseFailAlloc_3967_; 
v_reuseFailAlloc_3967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3967_, 0, v___x_3964_);
v___x_3966_ = v_reuseFailAlloc_3967_;
goto v_reusejp_3965_;
}
v_reusejp_3965_:
{
return v___x_3966_;
}
}
else
{
lean_object* v_e_x27_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3977_; 
v_e_x27_3968_ = lean_ctor_get(v_a_3958_, 0);
lean_inc_ref(v_e_x27_3968_);
lean_dec_ref_known(v_a_3958_, 2);
v___x_3969_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___closed__5, &l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___closed__5_once, _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___closed__5);
v___x_3970_ = l_Lean_indentExpr(v_e_3940_);
v___x_3971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3971_, 0, v___x_3969_);
lean_ctor_set(v___x_3971_, 1, v___x_3970_);
v___x_3972_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_3973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3973_, 0, v___x_3971_);
lean_ctor_set(v___x_3973_, 1, v___x_3972_);
v___x_3974_ = l_Lean_indentExpr(v_e_x27_3968_);
v___x_3975_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3975_, 0, v___x_3973_);
lean_ctor_set(v___x_3975_, 1, v___x_3974_);
if (v_isShared_3961_ == 0)
{
lean_ctor_set_tag(v___x_3960_, 0);
lean_ctor_set(v___x_3960_, 0, v___x_3975_);
v___x_3977_ = v___x_3960_;
goto v_reusejp_3976_;
}
else
{
lean_object* v_reuseFailAlloc_3978_; 
v_reuseFailAlloc_3978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3978_, 0, v___x_3975_);
v___x_3977_ = v_reuseFailAlloc_3978_;
goto v_reusejp_3976_;
}
v_reusejp_3976_:
{
return v___x_3977_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___boxed(lean_object* v_e_3980_, lean_object* v_x_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_){
_start:
{
lean_object* v_res_3987_; 
v_res_3987_ = l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0(v_e_3980_, v_x_3981_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_);
lean_dec(v___y_3985_);
lean_dec_ref(v___y_3984_);
lean_dec(v___y_3983_);
lean_dec_ref(v___y_3982_);
return v_res_3987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1(lean_object* v_a_3988_, lean_object* v___x_3989_, lean_object* v___x_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_){
_start:
{
lean_object* v___x_3998_; 
v___x_3998_ = l_Lean_Meta_Sym_shareCommon(v_a_3988_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_);
if (lean_obj_tag(v___x_3998_) == 0)
{
lean_object* v_a_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; 
v_a_3999_ = lean_ctor_get(v___x_3998_, 0);
lean_inc(v_a_3999_);
lean_dec_ref_known(v___x_3998_, 1);
v___x_4000_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_4000_, 0, v_a_3999_);
v___x_4001_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v___x_4000_, v___x_3989_, v___x_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_);
return v___x_4001_;
}
else
{
lean_object* v_a_4002_; lean_object* v___x_4004_; uint8_t v_isShared_4005_; uint8_t v_isSharedCheck_4009_; 
lean_dec_ref(v___x_3990_);
lean_dec_ref(v___x_3989_);
v_a_4002_ = lean_ctor_get(v___x_3998_, 0);
v_isSharedCheck_4009_ = !lean_is_exclusive(v___x_3998_);
if (v_isSharedCheck_4009_ == 0)
{
v___x_4004_ = v___x_3998_;
v_isShared_4005_ = v_isSharedCheck_4009_;
goto v_resetjp_4003_;
}
else
{
lean_inc(v_a_4002_);
lean_dec(v___x_3998_);
v___x_4004_ = lean_box(0);
v_isShared_4005_ = v_isSharedCheck_4009_;
goto v_resetjp_4003_;
}
v_resetjp_4003_:
{
lean_object* v___x_4007_; 
if (v_isShared_4005_ == 0)
{
v___x_4007_ = v___x_4004_;
goto v_reusejp_4006_;
}
else
{
lean_object* v_reuseFailAlloc_4008_; 
v_reuseFailAlloc_4008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4008_, 0, v_a_4002_);
v___x_4007_ = v_reuseFailAlloc_4008_;
goto v_reusejp_4006_;
}
v_reusejp_4006_:
{
return v___x_4007_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___boxed(lean_object* v_a_4010_, lean_object* v___x_4011_, lean_object* v___x_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_){
_start:
{
lean_object* v_res_4020_; 
v_res_4020_ = l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1(v_a_4010_, v___x_4011_, v___x_4012_, v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_);
lean_dec(v___y_4018_);
lean_dec_ref(v___y_4017_);
lean_dec(v___y_4016_);
lean_dec_ref(v___y_4015_);
lean_dec(v___y_4014_);
lean_dec_ref(v___y_4013_);
return v_res_4020_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg(lean_object* v_x_4021_){
_start:
{
if (lean_obj_tag(v_x_4021_) == 0)
{
lean_object* v_a_4023_; lean_object* v___x_4025_; uint8_t v_isShared_4026_; uint8_t v_isSharedCheck_4030_; 
v_a_4023_ = lean_ctor_get(v_x_4021_, 0);
v_isSharedCheck_4030_ = !lean_is_exclusive(v_x_4021_);
if (v_isSharedCheck_4030_ == 0)
{
v___x_4025_ = v_x_4021_;
v_isShared_4026_ = v_isSharedCheck_4030_;
goto v_resetjp_4024_;
}
else
{
lean_inc(v_a_4023_);
lean_dec(v_x_4021_);
v___x_4025_ = lean_box(0);
v_isShared_4026_ = v_isSharedCheck_4030_;
goto v_resetjp_4024_;
}
v_resetjp_4024_:
{
lean_object* v___x_4028_; 
if (v_isShared_4026_ == 0)
{
lean_ctor_set_tag(v___x_4025_, 1);
v___x_4028_ = v___x_4025_;
goto v_reusejp_4027_;
}
else
{
lean_object* v_reuseFailAlloc_4029_; 
v_reuseFailAlloc_4029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4029_, 0, v_a_4023_);
v___x_4028_ = v_reuseFailAlloc_4029_;
goto v_reusejp_4027_;
}
v_reusejp_4027_:
{
return v___x_4028_;
}
}
}
else
{
lean_object* v_a_4031_; lean_object* v___x_4033_; uint8_t v_isShared_4034_; uint8_t v_isSharedCheck_4038_; 
v_a_4031_ = lean_ctor_get(v_x_4021_, 0);
v_isSharedCheck_4038_ = !lean_is_exclusive(v_x_4021_);
if (v_isSharedCheck_4038_ == 0)
{
v___x_4033_ = v_x_4021_;
v_isShared_4034_ = v_isSharedCheck_4038_;
goto v_resetjp_4032_;
}
else
{
lean_inc(v_a_4031_);
lean_dec(v_x_4021_);
v___x_4033_ = lean_box(0);
v_isShared_4034_ = v_isSharedCheck_4038_;
goto v_resetjp_4032_;
}
v_resetjp_4032_:
{
lean_object* v___x_4036_; 
if (v_isShared_4034_ == 0)
{
lean_ctor_set_tag(v___x_4033_, 0);
v___x_4036_ = v___x_4033_;
goto v_reusejp_4035_;
}
else
{
lean_object* v_reuseFailAlloc_4037_; 
v_reuseFailAlloc_4037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4037_, 0, v_a_4031_);
v___x_4036_ = v_reuseFailAlloc_4037_;
goto v_reusejp_4035_;
}
v_reusejp_4035_:
{
return v___x_4036_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg___boxed(lean_object* v_x_4039_, lean_object* v___y_4040_){
_start:
{
lean_object* v_res_4041_; 
v_res_4041_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg(v_x_4039_);
return v_res_4041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__1(lean_object* v_oldTraces_4042_, lean_object* v_data_4043_, lean_object* v_ref_4044_, lean_object* v_msg_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_){
_start:
{
lean_object* v_fileName_4051_; lean_object* v_fileMap_4052_; lean_object* v_options_4053_; lean_object* v_currRecDepth_4054_; lean_object* v_maxRecDepth_4055_; lean_object* v_ref_4056_; lean_object* v_currNamespace_4057_; lean_object* v_openDecls_4058_; lean_object* v_initHeartbeats_4059_; lean_object* v_maxHeartbeats_4060_; lean_object* v_quotContext_4061_; lean_object* v_currMacroScope_4062_; uint8_t v_diag_4063_; lean_object* v_cancelTk_x3f_4064_; uint8_t v_suppressElabErrors_4065_; lean_object* v_inheritedTraceOptions_4066_; lean_object* v___x_4067_; lean_object* v_traceState_4068_; lean_object* v_traces_4069_; lean_object* v_ref_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; size_t v_sz_4073_; size_t v___x_4074_; lean_object* v___x_4075_; lean_object* v_msg_4076_; lean_object* v___x_4077_; lean_object* v_a_4078_; lean_object* v___x_4080_; uint8_t v_isShared_4081_; uint8_t v_isSharedCheck_4115_; 
v_fileName_4051_ = lean_ctor_get(v___y_4048_, 0);
v_fileMap_4052_ = lean_ctor_get(v___y_4048_, 1);
v_options_4053_ = lean_ctor_get(v___y_4048_, 2);
v_currRecDepth_4054_ = lean_ctor_get(v___y_4048_, 3);
v_maxRecDepth_4055_ = lean_ctor_get(v___y_4048_, 4);
v_ref_4056_ = lean_ctor_get(v___y_4048_, 5);
v_currNamespace_4057_ = lean_ctor_get(v___y_4048_, 6);
v_openDecls_4058_ = lean_ctor_get(v___y_4048_, 7);
v_initHeartbeats_4059_ = lean_ctor_get(v___y_4048_, 8);
v_maxHeartbeats_4060_ = lean_ctor_get(v___y_4048_, 9);
v_quotContext_4061_ = lean_ctor_get(v___y_4048_, 10);
v_currMacroScope_4062_ = lean_ctor_get(v___y_4048_, 11);
v_diag_4063_ = lean_ctor_get_uint8(v___y_4048_, sizeof(void*)*14);
v_cancelTk_x3f_4064_ = lean_ctor_get(v___y_4048_, 12);
v_suppressElabErrors_4065_ = lean_ctor_get_uint8(v___y_4048_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_4066_ = lean_ctor_get(v___y_4048_, 13);
v___x_4067_ = lean_st_ref_get(v___y_4049_);
v_traceState_4068_ = lean_ctor_get(v___x_4067_, 4);
lean_inc_ref(v_traceState_4068_);
lean_dec(v___x_4067_);
v_traces_4069_ = lean_ctor_get(v_traceState_4068_, 0);
lean_inc_ref(v_traces_4069_);
lean_dec_ref(v_traceState_4068_);
v_ref_4070_ = l_Lean_replaceRef(v_ref_4044_, v_ref_4056_);
lean_inc_ref(v_inheritedTraceOptions_4066_);
lean_inc(v_cancelTk_x3f_4064_);
lean_inc(v_currMacroScope_4062_);
lean_inc(v_quotContext_4061_);
lean_inc(v_maxHeartbeats_4060_);
lean_inc(v_initHeartbeats_4059_);
lean_inc(v_openDecls_4058_);
lean_inc(v_currNamespace_4057_);
lean_inc(v_maxRecDepth_4055_);
lean_inc(v_currRecDepth_4054_);
lean_inc_ref(v_options_4053_);
lean_inc_ref(v_fileMap_4052_);
lean_inc_ref(v_fileName_4051_);
v___x_4071_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_4071_, 0, v_fileName_4051_);
lean_ctor_set(v___x_4071_, 1, v_fileMap_4052_);
lean_ctor_set(v___x_4071_, 2, v_options_4053_);
lean_ctor_set(v___x_4071_, 3, v_currRecDepth_4054_);
lean_ctor_set(v___x_4071_, 4, v_maxRecDepth_4055_);
lean_ctor_set(v___x_4071_, 5, v_ref_4070_);
lean_ctor_set(v___x_4071_, 6, v_currNamespace_4057_);
lean_ctor_set(v___x_4071_, 7, v_openDecls_4058_);
lean_ctor_set(v___x_4071_, 8, v_initHeartbeats_4059_);
lean_ctor_set(v___x_4071_, 9, v_maxHeartbeats_4060_);
lean_ctor_set(v___x_4071_, 10, v_quotContext_4061_);
lean_ctor_set(v___x_4071_, 11, v_currMacroScope_4062_);
lean_ctor_set(v___x_4071_, 12, v_cancelTk_x3f_4064_);
lean_ctor_set(v___x_4071_, 13, v_inheritedTraceOptions_4066_);
lean_ctor_set_uint8(v___x_4071_, sizeof(void*)*14, v_diag_4063_);
lean_ctor_set_uint8(v___x_4071_, sizeof(void*)*14 + 1, v_suppressElabErrors_4065_);
v___x_4072_ = l_Lean_PersistentArray_toArray___redArg(v_traces_4069_);
lean_dec_ref(v_traces_4069_);
v_sz_4073_ = lean_array_size(v___x_4072_);
v___x_4074_ = ((size_t)0ULL);
v___x_4075_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4_spec__5(v_sz_4073_, v___x_4074_, v___x_4072_);
v_msg_4076_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_4076_, 0, v_data_4043_);
lean_ctor_set(v_msg_4076_, 1, v_msg_4045_);
lean_ctor_set(v_msg_4076_, 2, v___x_4075_);
v___x_4077_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0_spec__0(v_msg_4076_, v___y_4046_, v___y_4047_, v___x_4071_, v___y_4049_);
lean_dec_ref_known(v___x_4071_, 14);
v_a_4078_ = lean_ctor_get(v___x_4077_, 0);
v_isSharedCheck_4115_ = !lean_is_exclusive(v___x_4077_);
if (v_isSharedCheck_4115_ == 0)
{
v___x_4080_ = v___x_4077_;
v_isShared_4081_ = v_isSharedCheck_4115_;
goto v_resetjp_4079_;
}
else
{
lean_inc(v_a_4078_);
lean_dec(v___x_4077_);
v___x_4080_ = lean_box(0);
v_isShared_4081_ = v_isSharedCheck_4115_;
goto v_resetjp_4079_;
}
v_resetjp_4079_:
{
lean_object* v___x_4082_; lean_object* v_traceState_4083_; lean_object* v_env_4084_; lean_object* v_nextMacroScope_4085_; lean_object* v_ngen_4086_; lean_object* v_auxDeclNGen_4087_; lean_object* v_cache_4088_; lean_object* v_messages_4089_; lean_object* v_infoState_4090_; lean_object* v_snapshotTasks_4091_; lean_object* v___x_4093_; uint8_t v_isShared_4094_; uint8_t v_isSharedCheck_4114_; 
v___x_4082_ = lean_st_ref_take(v___y_4049_);
v_traceState_4083_ = lean_ctor_get(v___x_4082_, 4);
v_env_4084_ = lean_ctor_get(v___x_4082_, 0);
v_nextMacroScope_4085_ = lean_ctor_get(v___x_4082_, 1);
v_ngen_4086_ = lean_ctor_get(v___x_4082_, 2);
v_auxDeclNGen_4087_ = lean_ctor_get(v___x_4082_, 3);
v_cache_4088_ = lean_ctor_get(v___x_4082_, 5);
v_messages_4089_ = lean_ctor_get(v___x_4082_, 6);
v_infoState_4090_ = lean_ctor_get(v___x_4082_, 7);
v_snapshotTasks_4091_ = lean_ctor_get(v___x_4082_, 8);
v_isSharedCheck_4114_ = !lean_is_exclusive(v___x_4082_);
if (v_isSharedCheck_4114_ == 0)
{
v___x_4093_ = v___x_4082_;
v_isShared_4094_ = v_isSharedCheck_4114_;
goto v_resetjp_4092_;
}
else
{
lean_inc(v_snapshotTasks_4091_);
lean_inc(v_infoState_4090_);
lean_inc(v_messages_4089_);
lean_inc(v_cache_4088_);
lean_inc(v_traceState_4083_);
lean_inc(v_auxDeclNGen_4087_);
lean_inc(v_ngen_4086_);
lean_inc(v_nextMacroScope_4085_);
lean_inc(v_env_4084_);
lean_dec(v___x_4082_);
v___x_4093_ = lean_box(0);
v_isShared_4094_ = v_isSharedCheck_4114_;
goto v_resetjp_4092_;
}
v_resetjp_4092_:
{
uint64_t v_tid_4095_; lean_object* v___x_4097_; uint8_t v_isShared_4098_; uint8_t v_isSharedCheck_4112_; 
v_tid_4095_ = lean_ctor_get_uint64(v_traceState_4083_, sizeof(void*)*1);
v_isSharedCheck_4112_ = !lean_is_exclusive(v_traceState_4083_);
if (v_isSharedCheck_4112_ == 0)
{
lean_object* v_unused_4113_; 
v_unused_4113_ = lean_ctor_get(v_traceState_4083_, 0);
lean_dec(v_unused_4113_);
v___x_4097_ = v_traceState_4083_;
v_isShared_4098_ = v_isSharedCheck_4112_;
goto v_resetjp_4096_;
}
else
{
lean_dec(v_traceState_4083_);
v___x_4097_ = lean_box(0);
v_isShared_4098_ = v_isSharedCheck_4112_;
goto v_resetjp_4096_;
}
v_resetjp_4096_:
{
lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4102_; 
v___x_4099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4099_, 0, v_ref_4044_);
lean_ctor_set(v___x_4099_, 1, v_a_4078_);
v___x_4100_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_4042_, v___x_4099_);
if (v_isShared_4098_ == 0)
{
lean_ctor_set(v___x_4097_, 0, v___x_4100_);
v___x_4102_ = v___x_4097_;
goto v_reusejp_4101_;
}
else
{
lean_object* v_reuseFailAlloc_4111_; 
v_reuseFailAlloc_4111_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4111_, 0, v___x_4100_);
lean_ctor_set_uint64(v_reuseFailAlloc_4111_, sizeof(void*)*1, v_tid_4095_);
v___x_4102_ = v_reuseFailAlloc_4111_;
goto v_reusejp_4101_;
}
v_reusejp_4101_:
{
lean_object* v___x_4104_; 
if (v_isShared_4094_ == 0)
{
lean_ctor_set(v___x_4093_, 4, v___x_4102_);
v___x_4104_ = v___x_4093_;
goto v_reusejp_4103_;
}
else
{
lean_object* v_reuseFailAlloc_4110_; 
v_reuseFailAlloc_4110_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4110_, 0, v_env_4084_);
lean_ctor_set(v_reuseFailAlloc_4110_, 1, v_nextMacroScope_4085_);
lean_ctor_set(v_reuseFailAlloc_4110_, 2, v_ngen_4086_);
lean_ctor_set(v_reuseFailAlloc_4110_, 3, v_auxDeclNGen_4087_);
lean_ctor_set(v_reuseFailAlloc_4110_, 4, v___x_4102_);
lean_ctor_set(v_reuseFailAlloc_4110_, 5, v_cache_4088_);
lean_ctor_set(v_reuseFailAlloc_4110_, 6, v_messages_4089_);
lean_ctor_set(v_reuseFailAlloc_4110_, 7, v_infoState_4090_);
lean_ctor_set(v_reuseFailAlloc_4110_, 8, v_snapshotTasks_4091_);
v___x_4104_ = v_reuseFailAlloc_4110_;
goto v_reusejp_4103_;
}
v_reusejp_4103_:
{
lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4108_; 
v___x_4105_ = lean_st_ref_set(v___y_4049_, v___x_4104_);
v___x_4106_ = lean_box(0);
if (v_isShared_4081_ == 0)
{
lean_ctor_set(v___x_4080_, 0, v___x_4106_);
v___x_4108_ = v___x_4080_;
goto v_reusejp_4107_;
}
else
{
lean_object* v_reuseFailAlloc_4109_; 
v_reuseFailAlloc_4109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4109_, 0, v___x_4106_);
v___x_4108_ = v_reuseFailAlloc_4109_;
goto v_reusejp_4107_;
}
v_reusejp_4107_:
{
return v___x_4108_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__1___boxed(lean_object* v_oldTraces_4116_, lean_object* v_data_4117_, lean_object* v_ref_4118_, lean_object* v_msg_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_){
_start:
{
lean_object* v_res_4125_; 
v_res_4125_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__1(v_oldTraces_4116_, v_data_4117_, v_ref_4118_, v_msg_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_);
lean_dec(v___y_4123_);
lean_dec_ref(v___y_4122_);
lean_dec(v___y_4121_);
lean_dec_ref(v___y_4120_);
return v_res_4125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1(lean_object* v_cls_4126_, uint8_t v_collapsed_4127_, lean_object* v_tag_4128_, lean_object* v_opts_4129_, uint8_t v_clsEnabled_4130_, lean_object* v_oldTraces_4131_, lean_object* v_msg_4132_, lean_object* v_resStartStop_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_){
_start:
{
lean_object* v_fst_4139_; lean_object* v_snd_4140_; lean_object* v___y_4142_; lean_object* v___y_4143_; lean_object* v_data_4144_; lean_object* v_fst_4155_; lean_object* v_snd_4156_; lean_object* v___x_4157_; uint8_t v___x_4158_; lean_object* v___y_4160_; lean_object* v_a_4161_; uint8_t v___y_4176_; double v___y_4207_; 
v_fst_4139_ = lean_ctor_get(v_resStartStop_4133_, 0);
lean_inc(v_fst_4139_);
v_snd_4140_ = lean_ctor_get(v_resStartStop_4133_, 1);
lean_inc(v_snd_4140_);
lean_dec_ref(v_resStartStop_4133_);
v_fst_4155_ = lean_ctor_get(v_snd_4140_, 0);
lean_inc(v_fst_4155_);
v_snd_4156_ = lean_ctor_get(v_snd_4140_, 1);
lean_inc(v_snd_4156_);
lean_dec(v_snd_4140_);
v___x_4157_ = l_Lean_trace_profiler;
v___x_4158_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_4129_, v___x_4157_);
if (v___x_4158_ == 0)
{
v___y_4176_ = v___x_4158_;
goto v___jp_4175_;
}
else
{
lean_object* v___x_4212_; uint8_t v___x_4213_; 
v___x_4212_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4213_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_4129_, v___x_4212_);
if (v___x_4213_ == 0)
{
lean_object* v___x_4214_; lean_object* v___x_4215_; double v___x_4216_; double v___x_4217_; double v___x_4218_; 
v___x_4214_ = l_Lean_trace_profiler_threshold;
v___x_4215_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_4129_, v___x_4214_);
v___x_4216_ = lean_float_of_nat(v___x_4215_);
v___x_4217_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2);
v___x_4218_ = lean_float_div(v___x_4216_, v___x_4217_);
v___y_4207_ = v___x_4218_;
goto v___jp_4206_;
}
else
{
lean_object* v___x_4219_; lean_object* v___x_4220_; double v___x_4221_; 
v___x_4219_ = l_Lean_trace_profiler_threshold;
v___x_4220_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_4129_, v___x_4219_);
v___x_4221_ = lean_float_of_nat(v___x_4220_);
v___y_4207_ = v___x_4221_;
goto v___jp_4206_;
}
}
v___jp_4141_:
{
lean_object* v___x_4145_; 
lean_inc(v___y_4143_);
v___x_4145_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__1(v_oldTraces_4131_, v_data_4144_, v___y_4143_, v___y_4142_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_);
if (lean_obj_tag(v___x_4145_) == 0)
{
lean_object* v___x_4146_; 
lean_dec_ref_known(v___x_4145_, 1);
v___x_4146_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg(v_fst_4139_);
return v___x_4146_;
}
else
{
lean_object* v_a_4147_; lean_object* v___x_4149_; uint8_t v_isShared_4150_; uint8_t v_isSharedCheck_4154_; 
lean_dec(v_fst_4139_);
v_a_4147_ = lean_ctor_get(v___x_4145_, 0);
v_isSharedCheck_4154_ = !lean_is_exclusive(v___x_4145_);
if (v_isSharedCheck_4154_ == 0)
{
v___x_4149_ = v___x_4145_;
v_isShared_4150_ = v_isSharedCheck_4154_;
goto v_resetjp_4148_;
}
else
{
lean_inc(v_a_4147_);
lean_dec(v___x_4145_);
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
v___jp_4159_:
{
uint8_t v_result_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; double v___x_4165_; lean_object* v_data_4166_; 
v_result_4162_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__6(v_fst_4139_);
v___x_4163_ = lean_box(v_result_4162_);
v___x_4164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4164_, 0, v___x_4163_);
v___x_4165_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_4128_);
lean_inc_ref(v___x_4164_);
lean_inc(v_cls_4126_);
v_data_4166_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4166_, 0, v_cls_4126_);
lean_ctor_set(v_data_4166_, 1, v___x_4164_);
lean_ctor_set(v_data_4166_, 2, v_tag_4128_);
lean_ctor_set_float(v_data_4166_, sizeof(void*)*3, v___x_4165_);
lean_ctor_set_float(v_data_4166_, sizeof(void*)*3 + 8, v___x_4165_);
lean_ctor_set_uint8(v_data_4166_, sizeof(void*)*3 + 16, v_collapsed_4127_);
if (v___x_4158_ == 0)
{
lean_dec_ref_known(v___x_4164_, 1);
lean_dec(v_snd_4156_);
lean_dec(v_fst_4155_);
lean_dec_ref(v_tag_4128_);
lean_dec(v_cls_4126_);
v___y_4142_ = v_a_4161_;
v___y_4143_ = v___y_4160_;
v_data_4144_ = v_data_4166_;
goto v___jp_4141_;
}
else
{
lean_object* v_data_4167_; double v___x_4168_; double v___x_4169_; 
lean_dec_ref_known(v_data_4166_, 3);
v_data_4167_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4167_, 0, v_cls_4126_);
lean_ctor_set(v_data_4167_, 1, v___x_4164_);
lean_ctor_set(v_data_4167_, 2, v_tag_4128_);
v___x_4168_ = lean_unbox_float(v_fst_4155_);
lean_dec(v_fst_4155_);
lean_ctor_set_float(v_data_4167_, sizeof(void*)*3, v___x_4168_);
v___x_4169_ = lean_unbox_float(v_snd_4156_);
lean_dec(v_snd_4156_);
lean_ctor_set_float(v_data_4167_, sizeof(void*)*3 + 8, v___x_4169_);
lean_ctor_set_uint8(v_data_4167_, sizeof(void*)*3 + 16, v_collapsed_4127_);
v___y_4142_ = v_a_4161_;
v___y_4143_ = v___y_4160_;
v_data_4144_ = v_data_4167_;
goto v___jp_4141_;
}
}
v___jp_4170_:
{
lean_object* v_ref_4171_; lean_object* v___x_4172_; 
v_ref_4171_ = lean_ctor_get(v___y_4136_, 5);
lean_inc(v___y_4137_);
lean_inc_ref(v___y_4136_);
lean_inc(v___y_4135_);
lean_inc_ref(v___y_4134_);
lean_inc(v_fst_4139_);
v___x_4172_ = lean_apply_6(v_msg_4132_, v_fst_4139_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_, lean_box(0));
if (lean_obj_tag(v___x_4172_) == 0)
{
lean_object* v_a_4173_; 
v_a_4173_ = lean_ctor_get(v___x_4172_, 0);
lean_inc(v_a_4173_);
lean_dec_ref_known(v___x_4172_, 1);
v___y_4160_ = v_ref_4171_;
v_a_4161_ = v_a_4173_;
goto v___jp_4159_;
}
else
{
lean_object* v___x_4174_; 
lean_dec_ref_known(v___x_4172_, 1);
v___x_4174_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1);
v___y_4160_ = v_ref_4171_;
v_a_4161_ = v___x_4174_;
goto v___jp_4159_;
}
}
v___jp_4175_:
{
if (v_clsEnabled_4130_ == 0)
{
if (v___y_4176_ == 0)
{
lean_object* v___x_4177_; lean_object* v_traceState_4178_; lean_object* v_env_4179_; lean_object* v_nextMacroScope_4180_; lean_object* v_ngen_4181_; lean_object* v_auxDeclNGen_4182_; lean_object* v_cache_4183_; lean_object* v_messages_4184_; lean_object* v_infoState_4185_; lean_object* v_snapshotTasks_4186_; lean_object* v___x_4188_; uint8_t v_isShared_4189_; uint8_t v_isSharedCheck_4205_; 
lean_dec(v_snd_4156_);
lean_dec(v_fst_4155_);
lean_dec_ref(v_msg_4132_);
lean_dec_ref(v_tag_4128_);
lean_dec(v_cls_4126_);
v___x_4177_ = lean_st_ref_take(v___y_4137_);
v_traceState_4178_ = lean_ctor_get(v___x_4177_, 4);
v_env_4179_ = lean_ctor_get(v___x_4177_, 0);
v_nextMacroScope_4180_ = lean_ctor_get(v___x_4177_, 1);
v_ngen_4181_ = lean_ctor_get(v___x_4177_, 2);
v_auxDeclNGen_4182_ = lean_ctor_get(v___x_4177_, 3);
v_cache_4183_ = lean_ctor_get(v___x_4177_, 5);
v_messages_4184_ = lean_ctor_get(v___x_4177_, 6);
v_infoState_4185_ = lean_ctor_get(v___x_4177_, 7);
v_snapshotTasks_4186_ = lean_ctor_get(v___x_4177_, 8);
v_isSharedCheck_4205_ = !lean_is_exclusive(v___x_4177_);
if (v_isSharedCheck_4205_ == 0)
{
v___x_4188_ = v___x_4177_;
v_isShared_4189_ = v_isSharedCheck_4205_;
goto v_resetjp_4187_;
}
else
{
lean_inc(v_snapshotTasks_4186_);
lean_inc(v_infoState_4185_);
lean_inc(v_messages_4184_);
lean_inc(v_cache_4183_);
lean_inc(v_traceState_4178_);
lean_inc(v_auxDeclNGen_4182_);
lean_inc(v_ngen_4181_);
lean_inc(v_nextMacroScope_4180_);
lean_inc(v_env_4179_);
lean_dec(v___x_4177_);
v___x_4188_ = lean_box(0);
v_isShared_4189_ = v_isSharedCheck_4205_;
goto v_resetjp_4187_;
}
v_resetjp_4187_:
{
uint64_t v_tid_4190_; lean_object* v_traces_4191_; lean_object* v___x_4193_; uint8_t v_isShared_4194_; uint8_t v_isSharedCheck_4204_; 
v_tid_4190_ = lean_ctor_get_uint64(v_traceState_4178_, sizeof(void*)*1);
v_traces_4191_ = lean_ctor_get(v_traceState_4178_, 0);
v_isSharedCheck_4204_ = !lean_is_exclusive(v_traceState_4178_);
if (v_isSharedCheck_4204_ == 0)
{
v___x_4193_ = v_traceState_4178_;
v_isShared_4194_ = v_isSharedCheck_4204_;
goto v_resetjp_4192_;
}
else
{
lean_inc(v_traces_4191_);
lean_dec(v_traceState_4178_);
v___x_4193_ = lean_box(0);
v_isShared_4194_ = v_isSharedCheck_4204_;
goto v_resetjp_4192_;
}
v_resetjp_4192_:
{
lean_object* v___x_4195_; lean_object* v___x_4197_; 
v___x_4195_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_4131_, v_traces_4191_);
lean_dec_ref(v_traces_4191_);
if (v_isShared_4194_ == 0)
{
lean_ctor_set(v___x_4193_, 0, v___x_4195_);
v___x_4197_ = v___x_4193_;
goto v_reusejp_4196_;
}
else
{
lean_object* v_reuseFailAlloc_4203_; 
v_reuseFailAlloc_4203_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4203_, 0, v___x_4195_);
lean_ctor_set_uint64(v_reuseFailAlloc_4203_, sizeof(void*)*1, v_tid_4190_);
v___x_4197_ = v_reuseFailAlloc_4203_;
goto v_reusejp_4196_;
}
v_reusejp_4196_:
{
lean_object* v___x_4199_; 
if (v_isShared_4189_ == 0)
{
lean_ctor_set(v___x_4188_, 4, v___x_4197_);
v___x_4199_ = v___x_4188_;
goto v_reusejp_4198_;
}
else
{
lean_object* v_reuseFailAlloc_4202_; 
v_reuseFailAlloc_4202_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4202_, 0, v_env_4179_);
lean_ctor_set(v_reuseFailAlloc_4202_, 1, v_nextMacroScope_4180_);
lean_ctor_set(v_reuseFailAlloc_4202_, 2, v_ngen_4181_);
lean_ctor_set(v_reuseFailAlloc_4202_, 3, v_auxDeclNGen_4182_);
lean_ctor_set(v_reuseFailAlloc_4202_, 4, v___x_4197_);
lean_ctor_set(v_reuseFailAlloc_4202_, 5, v_cache_4183_);
lean_ctor_set(v_reuseFailAlloc_4202_, 6, v_messages_4184_);
lean_ctor_set(v_reuseFailAlloc_4202_, 7, v_infoState_4185_);
lean_ctor_set(v_reuseFailAlloc_4202_, 8, v_snapshotTasks_4186_);
v___x_4199_ = v_reuseFailAlloc_4202_;
goto v_reusejp_4198_;
}
v_reusejp_4198_:
{
lean_object* v___x_4200_; lean_object* v___x_4201_; 
v___x_4200_ = lean_st_ref_set(v___y_4137_, v___x_4199_);
v___x_4201_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg(v_fst_4139_);
return v___x_4201_;
}
}
}
}
}
else
{
goto v___jp_4170_;
}
}
else
{
goto v___jp_4170_;
}
}
v___jp_4206_:
{
double v___x_4208_; double v___x_4209_; double v___x_4210_; uint8_t v___x_4211_; 
v___x_4208_ = lean_unbox_float(v_snd_4156_);
v___x_4209_ = lean_unbox_float(v_fst_4155_);
v___x_4210_ = lean_float_sub(v___x_4208_, v___x_4209_);
v___x_4211_ = lean_float_decLt(v___y_4207_, v___x_4210_);
v___y_4176_ = v___x_4211_;
goto v___jp_4175_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1___boxed(lean_object* v_cls_4222_, lean_object* v_collapsed_4223_, lean_object* v_tag_4224_, lean_object* v_opts_4225_, lean_object* v_clsEnabled_4226_, lean_object* v_oldTraces_4227_, lean_object* v_msg_4228_, lean_object* v_resStartStop_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_){
_start:
{
uint8_t v_collapsed_boxed_4235_; uint8_t v_clsEnabled_boxed_4236_; lean_object* v_res_4237_; 
v_collapsed_boxed_4235_ = lean_unbox(v_collapsed_4223_);
v_clsEnabled_boxed_4236_ = lean_unbox(v_clsEnabled_4226_);
v_res_4237_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1(v_cls_4222_, v_collapsed_boxed_4235_, v_tag_4224_, v_opts_4225_, v_clsEnabled_boxed_4236_, v_oldTraces_4227_, v_msg_4228_, v_resStartStop_4229_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_);
lean_dec(v___y_4233_);
lean_dec_ref(v___y_4232_);
lean_dec(v___y_4231_);
lean_dec_ref(v___y_4230_);
lean_dec_ref(v_opts_4225_);
return v_res_4237_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1(void){
_start:
{
lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; 
v___x_4242_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0));
v___x_4243_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__3));
v___x_4244_ = l_Lean_Name_append(v___x_4243_, v___x_4242_);
return v___x_4244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry(lean_object* v_e_4245_, lean_object* v_a_4246_, lean_object* v_a_4247_, lean_object* v_a_4248_, lean_object* v_a_4249_){
_start:
{
lean_object* v_options_4251_; lean_object* v_inheritedTraceOptions_4252_; uint8_t v_hasTrace_4253_; uint8_t v___x_4254_; 
v_options_4251_ = lean_ctor_get(v_a_4248_, 2);
v_inheritedTraceOptions_4252_ = lean_ctor_get(v_a_4248_, 13);
v_hasTrace_4253_ = lean_ctor_get_uint8(v_options_4251_, sizeof(void*)*1);
v___x_4254_ = lean_bool_not(v_hasTrace_4253_);
if (v___x_4254_ == 0)
{
lean_object* v___f_4255_; lean_object* v___x_4256_; uint8_t v___x_4257_; lean_object* v___x_4258_; uint8_t v___y_4260_; lean_object* v___y_4261_; lean_object* v___y_4262_; lean_object* v_a_4263_; lean_object* v___y_4276_; uint8_t v___y_4277_; lean_object* v___y_4278_; lean_object* v_a_4279_; uint8_t v___y_4282_; lean_object* v___y_4283_; lean_object* v___y_4284_; lean_object* v_a_4285_; lean_object* v___y_4295_; uint8_t v___y_4296_; lean_object* v___y_4297_; lean_object* v_a_4298_; uint8_t v___y_4301_; uint8_t v_a_4355_; 
lean_inc_ref(v_e_4245_);
v___f_4255_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4255_, 0, v_e_4245_);
v___x_4256_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0));
v___x_4257_ = 1;
v___x_4258_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__1));
if (v_hasTrace_4253_ == 0)
{
v_a_4355_ = v_hasTrace_4253_;
goto v___jp_4354_;
}
else
{
lean_object* v___x_4386_; uint8_t v___x_4387_; 
v___x_4386_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1);
v___x_4387_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4252_, v_options_4251_, v___x_4386_);
if (v___x_4387_ == 0)
{
v_a_4355_ = v___x_4387_;
goto v___jp_4354_;
}
else
{
v___y_4301_ = v___x_4387_;
goto v___jp_4300_;
}
}
v___jp_4259_:
{
lean_object* v___x_4264_; double v___x_4265_; double v___x_4266_; double v___x_4267_; double v___x_4268_; double v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; 
v___x_4264_ = lean_io_mono_nanos_now();
v___x_4265_ = lean_float_of_nat(v___y_4261_);
v___x_4266_ = lean_float_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9);
v___x_4267_ = lean_float_div(v___x_4265_, v___x_4266_);
v___x_4268_ = lean_float_of_nat(v___x_4264_);
v___x_4269_ = lean_float_div(v___x_4268_, v___x_4266_);
v___x_4270_ = lean_box_float(v___x_4267_);
v___x_4271_ = lean_box_float(v___x_4269_);
v___x_4272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4272_, 0, v___x_4270_);
lean_ctor_set(v___x_4272_, 1, v___x_4271_);
v___x_4273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4273_, 0, v_a_4263_);
lean_ctor_set(v___x_4273_, 1, v___x_4272_);
v___x_4274_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1(v___x_4256_, v___x_4257_, v___x_4258_, v_options_4251_, v___y_4260_, v___y_4262_, v___f_4255_, v___x_4273_, v_a_4246_, v_a_4247_, v_a_4248_, v_a_4249_);
return v___x_4274_;
}
v___jp_4275_:
{
lean_object* v___x_4280_; 
v___x_4280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4280_, 0, v_a_4279_);
v___y_4260_ = v___y_4277_;
v___y_4261_ = v___y_4276_;
v___y_4262_ = v___y_4278_;
v_a_4263_ = v___x_4280_;
goto v___jp_4259_;
}
v___jp_4281_:
{
lean_object* v___x_4286_; double v___x_4287_; double v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; 
v___x_4286_ = lean_io_get_num_heartbeats();
v___x_4287_ = lean_float_of_nat(v___y_4283_);
v___x_4288_ = lean_float_of_nat(v___x_4286_);
v___x_4289_ = lean_box_float(v___x_4287_);
v___x_4290_ = lean_box_float(v___x_4288_);
v___x_4291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4291_, 0, v___x_4289_);
lean_ctor_set(v___x_4291_, 1, v___x_4290_);
v___x_4292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4292_, 0, v_a_4285_);
lean_ctor_set(v___x_4292_, 1, v___x_4291_);
v___x_4293_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1(v___x_4256_, v___x_4257_, v___x_4258_, v_options_4251_, v___y_4282_, v___y_4284_, v___f_4255_, v___x_4292_, v_a_4246_, v_a_4247_, v_a_4248_, v_a_4249_);
return v___x_4293_;
}
v___jp_4294_:
{
lean_object* v___x_4299_; 
v___x_4299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4299_, 0, v_a_4298_);
v___y_4282_ = v___y_4296_;
v___y_4283_ = v___y_4295_;
v___y_4284_ = v___y_4297_;
v_a_4285_ = v___x_4299_;
goto v___jp_4281_;
}
v___jp_4300_:
{
lean_object* v___x_4302_; lean_object* v_a_4303_; lean_object* v___x_4304_; uint8_t v___x_4305_; 
v___x_4302_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg(v_a_4249_);
v_a_4303_ = lean_ctor_get(v___x_4302_, 0);
lean_inc(v_a_4303_);
lean_dec_ref(v___x_4302_);
v___x_4304_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4305_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_4251_, v___x_4304_);
if (v___x_4305_ == 0)
{
lean_object* v___x_4306_; lean_object* v___x_4307_; 
v___x_4306_ = lean_io_mono_nanos_now();
v___x_4307_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_4249_);
if (lean_obj_tag(v___x_4307_) == 0)
{
lean_object* v_a_4308_; lean_object* v___x_4309_; 
v_a_4308_ = lean_ctor_get(v___x_4307_, 0);
lean_inc(v_a_4308_);
lean_dec_ref_known(v___x_4307_, 1);
v___x_4309_ = l_Lean_Meta_Sym_unfoldReducible(v_e_4245_, v_a_4246_, v_a_4247_, v_a_4248_, v_a_4249_);
if (lean_obj_tag(v___x_4309_) == 0)
{
lean_object* v_a_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___f_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; 
v_a_4310_ = lean_ctor_get(v___x_4309_, 0);
lean_inc(v_a_4310_);
lean_dec_ref_known(v___x_4309_, 1);
v___x_4311_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_4312_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_4251_, v___x_4311_);
v___x_4313_ = lean_unsigned_to_nat(2u);
v___x_4314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4314_, 0, v___x_4312_);
lean_ctor_set(v___x_4314_, 1, v___x_4313_);
v___x_4315_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(v_a_4308_);
v___f_4316_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___boxed), 10, 3);
lean_closure_set(v___f_4316_, 0, v_a_4310_);
lean_closure_set(v___f_4316_, 1, v___x_4315_);
lean_closure_set(v___f_4316_, 2, v___x_4314_);
v___x_4317_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0___boxed), 9, 2);
lean_closure_set(v___x_4317_, 0, lean_box(0));
lean_closure_set(v___x_4317_, 1, v___f_4316_);
v___x_4318_ = l_Lean_Meta_Sym_SymM_run___redArg(v___x_4317_, v_a_4246_, v_a_4247_, v_a_4248_, v_a_4249_);
if (lean_obj_tag(v___x_4318_) == 0)
{
lean_object* v_a_4319_; lean_object* v___x_4321_; uint8_t v_isShared_4322_; uint8_t v_isSharedCheck_4326_; 
v_a_4319_ = lean_ctor_get(v___x_4318_, 0);
v_isSharedCheck_4326_ = !lean_is_exclusive(v___x_4318_);
if (v_isSharedCheck_4326_ == 0)
{
v___x_4321_ = v___x_4318_;
v_isShared_4322_ = v_isSharedCheck_4326_;
goto v_resetjp_4320_;
}
else
{
lean_inc(v_a_4319_);
lean_dec(v___x_4318_);
v___x_4321_ = lean_box(0);
v_isShared_4322_ = v_isSharedCheck_4326_;
goto v_resetjp_4320_;
}
v_resetjp_4320_:
{
lean_object* v___x_4324_; 
if (v_isShared_4322_ == 0)
{
lean_ctor_set_tag(v___x_4321_, 1);
v___x_4324_ = v___x_4321_;
goto v_reusejp_4323_;
}
else
{
lean_object* v_reuseFailAlloc_4325_; 
v_reuseFailAlloc_4325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4325_, 0, v_a_4319_);
v___x_4324_ = v_reuseFailAlloc_4325_;
goto v_reusejp_4323_;
}
v_reusejp_4323_:
{
v___y_4260_ = v___y_4301_;
v___y_4261_ = v___x_4306_;
v___y_4262_ = v_a_4303_;
v_a_4263_ = v___x_4324_;
goto v___jp_4259_;
}
}
}
else
{
lean_object* v_a_4327_; 
v_a_4327_ = lean_ctor_get(v___x_4318_, 0);
lean_inc(v_a_4327_);
lean_dec_ref_known(v___x_4318_, 1);
v___y_4276_ = v___x_4306_;
v___y_4277_ = v___y_4301_;
v___y_4278_ = v_a_4303_;
v_a_4279_ = v_a_4327_;
goto v___jp_4275_;
}
}
else
{
lean_object* v_a_4328_; 
lean_dec(v_a_4308_);
v_a_4328_ = lean_ctor_get(v___x_4309_, 0);
lean_inc(v_a_4328_);
lean_dec_ref_known(v___x_4309_, 1);
v___y_4276_ = v___x_4306_;
v___y_4277_ = v___y_4301_;
v___y_4278_ = v_a_4303_;
v_a_4279_ = v_a_4328_;
goto v___jp_4275_;
}
}
else
{
lean_object* v_a_4329_; 
lean_dec_ref(v_e_4245_);
v_a_4329_ = lean_ctor_get(v___x_4307_, 0);
lean_inc(v_a_4329_);
lean_dec_ref_known(v___x_4307_, 1);
v___y_4276_ = v___x_4306_;
v___y_4277_ = v___y_4301_;
v___y_4278_ = v_a_4303_;
v_a_4279_ = v_a_4329_;
goto v___jp_4275_;
}
}
else
{
lean_object* v___x_4330_; lean_object* v___x_4331_; 
v___x_4330_ = lean_io_get_num_heartbeats();
v___x_4331_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_4249_);
if (lean_obj_tag(v___x_4331_) == 0)
{
lean_object* v_a_4332_; lean_object* v___x_4333_; 
v_a_4332_ = lean_ctor_get(v___x_4331_, 0);
lean_inc(v_a_4332_);
lean_dec_ref_known(v___x_4331_, 1);
v___x_4333_ = l_Lean_Meta_Sym_unfoldReducible(v_e_4245_, v_a_4246_, v_a_4247_, v_a_4248_, v_a_4249_);
if (lean_obj_tag(v___x_4333_) == 0)
{
lean_object* v_a_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___f_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; 
v_a_4334_ = lean_ctor_get(v___x_4333_, 0);
lean_inc(v_a_4334_);
lean_dec_ref_known(v___x_4333_, 1);
v___x_4335_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_4336_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_4251_, v___x_4335_);
v___x_4337_ = lean_unsigned_to_nat(2u);
v___x_4338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4338_, 0, v___x_4336_);
lean_ctor_set(v___x_4338_, 1, v___x_4337_);
v___x_4339_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(v_a_4332_);
v___f_4340_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___boxed), 10, 3);
lean_closure_set(v___f_4340_, 0, v_a_4334_);
lean_closure_set(v___f_4340_, 1, v___x_4339_);
lean_closure_set(v___f_4340_, 2, v___x_4338_);
v___x_4341_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0___boxed), 9, 2);
lean_closure_set(v___x_4341_, 0, lean_box(0));
lean_closure_set(v___x_4341_, 1, v___f_4340_);
v___x_4342_ = l_Lean_Meta_Sym_SymM_run___redArg(v___x_4341_, v_a_4246_, v_a_4247_, v_a_4248_, v_a_4249_);
if (lean_obj_tag(v___x_4342_) == 0)
{
lean_object* v_a_4343_; lean_object* v___x_4345_; uint8_t v_isShared_4346_; uint8_t v_isSharedCheck_4350_; 
v_a_4343_ = lean_ctor_get(v___x_4342_, 0);
v_isSharedCheck_4350_ = !lean_is_exclusive(v___x_4342_);
if (v_isSharedCheck_4350_ == 0)
{
v___x_4345_ = v___x_4342_;
v_isShared_4346_ = v_isSharedCheck_4350_;
goto v_resetjp_4344_;
}
else
{
lean_inc(v_a_4343_);
lean_dec(v___x_4342_);
v___x_4345_ = lean_box(0);
v_isShared_4346_ = v_isSharedCheck_4350_;
goto v_resetjp_4344_;
}
v_resetjp_4344_:
{
lean_object* v___x_4348_; 
if (v_isShared_4346_ == 0)
{
lean_ctor_set_tag(v___x_4345_, 1);
v___x_4348_ = v___x_4345_;
goto v_reusejp_4347_;
}
else
{
lean_object* v_reuseFailAlloc_4349_; 
v_reuseFailAlloc_4349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4349_, 0, v_a_4343_);
v___x_4348_ = v_reuseFailAlloc_4349_;
goto v_reusejp_4347_;
}
v_reusejp_4347_:
{
v___y_4282_ = v___y_4301_;
v___y_4283_ = v___x_4330_;
v___y_4284_ = v_a_4303_;
v_a_4285_ = v___x_4348_;
goto v___jp_4281_;
}
}
}
else
{
lean_object* v_a_4351_; 
v_a_4351_ = lean_ctor_get(v___x_4342_, 0);
lean_inc(v_a_4351_);
lean_dec_ref_known(v___x_4342_, 1);
v___y_4295_ = v___x_4330_;
v___y_4296_ = v___y_4301_;
v___y_4297_ = v_a_4303_;
v_a_4298_ = v_a_4351_;
goto v___jp_4294_;
}
}
else
{
lean_object* v_a_4352_; 
lean_dec(v_a_4332_);
v_a_4352_ = lean_ctor_get(v___x_4333_, 0);
lean_inc(v_a_4352_);
lean_dec_ref_known(v___x_4333_, 1);
v___y_4295_ = v___x_4330_;
v___y_4296_ = v___y_4301_;
v___y_4297_ = v_a_4303_;
v_a_4298_ = v_a_4352_;
goto v___jp_4294_;
}
}
else
{
lean_object* v_a_4353_; 
lean_dec_ref(v_e_4245_);
v_a_4353_ = lean_ctor_get(v___x_4331_, 0);
lean_inc(v_a_4353_);
lean_dec_ref_known(v___x_4331_, 1);
v___y_4295_ = v___x_4330_;
v___y_4296_ = v___y_4301_;
v___y_4297_ = v_a_4303_;
v_a_4298_ = v_a_4353_;
goto v___jp_4294_;
}
}
}
v___jp_4354_:
{
lean_object* v___x_4356_; uint8_t v___x_4357_; 
v___x_4356_ = l_Lean_trace_profiler;
v___x_4357_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_4251_, v___x_4356_);
if (v___x_4357_ == 0)
{
lean_object* v___x_4358_; 
lean_dec_ref(v___f_4255_);
v___x_4358_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_4249_);
if (lean_obj_tag(v___x_4358_) == 0)
{
lean_object* v_a_4359_; lean_object* v___x_4360_; 
v_a_4359_ = lean_ctor_get(v___x_4358_, 0);
lean_inc(v_a_4359_);
lean_dec_ref_known(v___x_4358_, 1);
v___x_4360_ = l_Lean_Meta_Sym_unfoldReducible(v_e_4245_, v_a_4246_, v_a_4247_, v_a_4248_, v_a_4249_);
if (lean_obj_tag(v___x_4360_) == 0)
{
lean_object* v_a_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___f_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; 
v_a_4361_ = lean_ctor_get(v___x_4360_, 0);
lean_inc(v_a_4361_);
lean_dec_ref_known(v___x_4360_, 1);
v___x_4362_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_4363_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_4251_, v___x_4362_);
v___x_4364_ = lean_unsigned_to_nat(2u);
v___x_4365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4365_, 0, v___x_4363_);
lean_ctor_set(v___x_4365_, 1, v___x_4364_);
v___x_4366_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(v_a_4359_);
v___f_4367_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___boxed), 10, 3);
lean_closure_set(v___f_4367_, 0, v_a_4361_);
lean_closure_set(v___f_4367_, 1, v___x_4366_);
lean_closure_set(v___f_4367_, 2, v___x_4365_);
v___x_4368_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0___boxed), 9, 2);
lean_closure_set(v___x_4368_, 0, lean_box(0));
lean_closure_set(v___x_4368_, 1, v___f_4367_);
v___x_4369_ = l_Lean_Meta_Sym_SymM_run___redArg(v___x_4368_, v_a_4246_, v_a_4247_, v_a_4248_, v_a_4249_);
return v___x_4369_;
}
else
{
lean_object* v_a_4370_; lean_object* v___x_4372_; uint8_t v_isShared_4373_; uint8_t v_isSharedCheck_4377_; 
lean_dec(v_a_4359_);
v_a_4370_ = lean_ctor_get(v___x_4360_, 0);
v_isSharedCheck_4377_ = !lean_is_exclusive(v___x_4360_);
if (v_isSharedCheck_4377_ == 0)
{
v___x_4372_ = v___x_4360_;
v_isShared_4373_ = v_isSharedCheck_4377_;
goto v_resetjp_4371_;
}
else
{
lean_inc(v_a_4370_);
lean_dec(v___x_4360_);
v___x_4372_ = lean_box(0);
v_isShared_4373_ = v_isSharedCheck_4377_;
goto v_resetjp_4371_;
}
v_resetjp_4371_:
{
lean_object* v___x_4375_; 
if (v_isShared_4373_ == 0)
{
v___x_4375_ = v___x_4372_;
goto v_reusejp_4374_;
}
else
{
lean_object* v_reuseFailAlloc_4376_; 
v_reuseFailAlloc_4376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4376_, 0, v_a_4370_);
v___x_4375_ = v_reuseFailAlloc_4376_;
goto v_reusejp_4374_;
}
v_reusejp_4374_:
{
return v___x_4375_;
}
}
}
}
else
{
lean_object* v_a_4378_; lean_object* v___x_4380_; uint8_t v_isShared_4381_; uint8_t v_isSharedCheck_4385_; 
lean_dec_ref(v_e_4245_);
v_a_4378_ = lean_ctor_get(v___x_4358_, 0);
v_isSharedCheck_4385_ = !lean_is_exclusive(v___x_4358_);
if (v_isSharedCheck_4385_ == 0)
{
v___x_4380_ = v___x_4358_;
v_isShared_4381_ = v_isSharedCheck_4385_;
goto v_resetjp_4379_;
}
else
{
lean_inc(v_a_4378_);
lean_dec(v___x_4358_);
v___x_4380_ = lean_box(0);
v_isShared_4381_ = v_isSharedCheck_4385_;
goto v_resetjp_4379_;
}
v_resetjp_4379_:
{
lean_object* v___x_4383_; 
if (v_isShared_4381_ == 0)
{
v___x_4383_ = v___x_4380_;
goto v_reusejp_4382_;
}
else
{
lean_object* v_reuseFailAlloc_4384_; 
v_reuseFailAlloc_4384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4384_, 0, v_a_4378_);
v___x_4383_ = v_reuseFailAlloc_4384_;
goto v_reusejp_4382_;
}
v_reusejp_4382_:
{
return v___x_4383_;
}
}
}
}
else
{
v___y_4301_ = v_a_4355_;
goto v___jp_4300_;
}
}
}
else
{
lean_object* v___x_4388_; 
v___x_4388_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_4249_);
if (lean_obj_tag(v___x_4388_) == 0)
{
lean_object* v_a_4389_; lean_object* v___x_4390_; 
v_a_4389_ = lean_ctor_get(v___x_4388_, 0);
lean_inc(v_a_4389_);
lean_dec_ref_known(v___x_4388_, 1);
v___x_4390_ = l_Lean_Meta_Sym_unfoldReducible(v_e_4245_, v_a_4246_, v_a_4247_, v_a_4248_, v_a_4249_);
if (lean_obj_tag(v___x_4390_) == 0)
{
lean_object* v_a_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___f_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; 
v_a_4391_ = lean_ctor_get(v___x_4390_, 0);
lean_inc(v_a_4391_);
lean_dec_ref_known(v___x_4390_, 1);
v___x_4392_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_4393_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_4251_, v___x_4392_);
v___x_4394_ = lean_unsigned_to_nat(2u);
v___x_4395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4395_, 0, v___x_4393_);
lean_ctor_set(v___x_4395_, 1, v___x_4394_);
v___x_4396_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(v_a_4389_);
v___f_4397_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___boxed), 10, 3);
lean_closure_set(v___f_4397_, 0, v_a_4391_);
lean_closure_set(v___f_4397_, 1, v___x_4396_);
lean_closure_set(v___f_4397_, 2, v___x_4395_);
v___x_4398_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0___boxed), 9, 2);
lean_closure_set(v___x_4398_, 0, lean_box(0));
lean_closure_set(v___x_4398_, 1, v___f_4397_);
v___x_4399_ = l_Lean_Meta_Sym_SymM_run___redArg(v___x_4398_, v_a_4246_, v_a_4247_, v_a_4248_, v_a_4249_);
return v___x_4399_;
}
else
{
lean_object* v_a_4400_; lean_object* v___x_4402_; uint8_t v_isShared_4403_; uint8_t v_isSharedCheck_4407_; 
lean_dec(v_a_4389_);
v_a_4400_ = lean_ctor_get(v___x_4390_, 0);
v_isSharedCheck_4407_ = !lean_is_exclusive(v___x_4390_);
if (v_isSharedCheck_4407_ == 0)
{
v___x_4402_ = v___x_4390_;
v_isShared_4403_ = v_isSharedCheck_4407_;
goto v_resetjp_4401_;
}
else
{
lean_inc(v_a_4400_);
lean_dec(v___x_4390_);
v___x_4402_ = lean_box(0);
v_isShared_4403_ = v_isSharedCheck_4407_;
goto v_resetjp_4401_;
}
v_resetjp_4401_:
{
lean_object* v___x_4405_; 
if (v_isShared_4403_ == 0)
{
v___x_4405_ = v___x_4402_;
goto v_reusejp_4404_;
}
else
{
lean_object* v_reuseFailAlloc_4406_; 
v_reuseFailAlloc_4406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4406_, 0, v_a_4400_);
v___x_4405_ = v_reuseFailAlloc_4406_;
goto v_reusejp_4404_;
}
v_reusejp_4404_:
{
return v___x_4405_;
}
}
}
}
else
{
lean_object* v_a_4408_; lean_object* v___x_4410_; uint8_t v_isShared_4411_; uint8_t v_isSharedCheck_4415_; 
lean_dec_ref(v_e_4245_);
v_a_4408_ = lean_ctor_get(v___x_4388_, 0);
v_isSharedCheck_4415_ = !lean_is_exclusive(v___x_4388_);
if (v_isSharedCheck_4415_ == 0)
{
v___x_4410_ = v___x_4388_;
v_isShared_4411_ = v_isSharedCheck_4415_;
goto v_resetjp_4409_;
}
else
{
lean_inc(v_a_4408_);
lean_dec(v___x_4388_);
v___x_4410_ = lean_box(0);
v_isShared_4411_ = v_isSharedCheck_4415_;
goto v_resetjp_4409_;
}
v_resetjp_4409_:
{
lean_object* v___x_4413_; 
if (v_isShared_4411_ == 0)
{
v___x_4413_ = v___x_4410_;
goto v_reusejp_4412_;
}
else
{
lean_object* v_reuseFailAlloc_4414_; 
v_reuseFailAlloc_4414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4414_, 0, v_a_4408_);
v___x_4413_ = v_reuseFailAlloc_4414_;
goto v_reusejp_4412_;
}
v_reusejp_4412_:
{
return v___x_4413_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___boxed(lean_object* v_e_4416_, lean_object* v_a_4417_, lean_object* v_a_4418_, lean_object* v_a_4419_, lean_object* v_a_4420_, lean_object* v_a_4421_){
_start:
{
lean_object* v_res_4422_; 
v_res_4422_ = l_Lean_Meta_Tactic_Cbv_cbvEntry(v_e_4416_, v_a_4417_, v_a_4418_, v_a_4419_, v_a_4420_);
lean_dec(v_a_4420_);
lean_dec_ref(v_a_4419_);
lean_dec(v_a_4418_);
lean_dec_ref(v_a_4417_);
return v_res_4422_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2(lean_object* v_00_u03b1_4423_, lean_object* v_x_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_){
_start:
{
lean_object* v___x_4430_; 
v___x_4430_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg(v_x_4424_);
return v___x_4430_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___boxed(lean_object* v_00_u03b1_4431_, lean_object* v_x_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_){
_start:
{
lean_object* v_res_4438_; 
v_res_4438_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2(v_00_u03b1_4431_, v_x_4432_, v___y_4433_, v___y_4434_, v___y_4435_, v___y_4436_);
lean_dec(v___y_4436_);
lean_dec_ref(v___y_4435_);
lean_dec(v___y_4434_);
lean_dec_ref(v___y_4433_);
return v_res_4438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1___redArg(lean_object* v___y_4439_){
_start:
{
lean_object* v___x_4441_; lean_object* v_traceState_4442_; lean_object* v_traces_4443_; lean_object* v___x_4444_; lean_object* v_traceState_4445_; lean_object* v_env_4446_; lean_object* v_nextMacroScope_4447_; lean_object* v_ngen_4448_; lean_object* v_auxDeclNGen_4449_; lean_object* v_cache_4450_; lean_object* v_messages_4451_; lean_object* v_infoState_4452_; lean_object* v_snapshotTasks_4453_; lean_object* v___x_4455_; uint8_t v_isShared_4456_; uint8_t v_isSharedCheck_4474_; 
v___x_4441_ = lean_st_ref_get(v___y_4439_);
v_traceState_4442_ = lean_ctor_get(v___x_4441_, 4);
lean_inc_ref(v_traceState_4442_);
lean_dec(v___x_4441_);
v_traces_4443_ = lean_ctor_get(v_traceState_4442_, 0);
lean_inc_ref(v_traces_4443_);
lean_dec_ref(v_traceState_4442_);
v___x_4444_ = lean_st_ref_take(v___y_4439_);
v_traceState_4445_ = lean_ctor_get(v___x_4444_, 4);
v_env_4446_ = lean_ctor_get(v___x_4444_, 0);
v_nextMacroScope_4447_ = lean_ctor_get(v___x_4444_, 1);
v_ngen_4448_ = lean_ctor_get(v___x_4444_, 2);
v_auxDeclNGen_4449_ = lean_ctor_get(v___x_4444_, 3);
v_cache_4450_ = lean_ctor_get(v___x_4444_, 5);
v_messages_4451_ = lean_ctor_get(v___x_4444_, 6);
v_infoState_4452_ = lean_ctor_get(v___x_4444_, 7);
v_snapshotTasks_4453_ = lean_ctor_get(v___x_4444_, 8);
v_isSharedCheck_4474_ = !lean_is_exclusive(v___x_4444_);
if (v_isSharedCheck_4474_ == 0)
{
v___x_4455_ = v___x_4444_;
v_isShared_4456_ = v_isSharedCheck_4474_;
goto v_resetjp_4454_;
}
else
{
lean_inc(v_snapshotTasks_4453_);
lean_inc(v_infoState_4452_);
lean_inc(v_messages_4451_);
lean_inc(v_cache_4450_);
lean_inc(v_traceState_4445_);
lean_inc(v_auxDeclNGen_4449_);
lean_inc(v_ngen_4448_);
lean_inc(v_nextMacroScope_4447_);
lean_inc(v_env_4446_);
lean_dec(v___x_4444_);
v___x_4455_ = lean_box(0);
v_isShared_4456_ = v_isSharedCheck_4474_;
goto v_resetjp_4454_;
}
v_resetjp_4454_:
{
uint64_t v_tid_4457_; lean_object* v___x_4459_; uint8_t v_isShared_4460_; uint8_t v_isSharedCheck_4472_; 
v_tid_4457_ = lean_ctor_get_uint64(v_traceState_4445_, sizeof(void*)*1);
v_isSharedCheck_4472_ = !lean_is_exclusive(v_traceState_4445_);
if (v_isSharedCheck_4472_ == 0)
{
lean_object* v_unused_4473_; 
v_unused_4473_ = lean_ctor_get(v_traceState_4445_, 0);
lean_dec(v_unused_4473_);
v___x_4459_ = v_traceState_4445_;
v_isShared_4460_ = v_isSharedCheck_4472_;
goto v_resetjp_4458_;
}
else
{
lean_dec(v_traceState_4445_);
v___x_4459_ = lean_box(0);
v_isShared_4460_ = v_isSharedCheck_4472_;
goto v_resetjp_4458_;
}
v_resetjp_4458_:
{
lean_object* v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; lean_object* v___x_4465_; 
v___x_4461_ = lean_unsigned_to_nat(32u);
v___x_4462_ = lean_mk_empty_array_with_capacity(v___x_4461_);
lean_dec_ref(v___x_4462_);
v___x_4463_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1);
if (v_isShared_4460_ == 0)
{
lean_ctor_set(v___x_4459_, 0, v___x_4463_);
v___x_4465_ = v___x_4459_;
goto v_reusejp_4464_;
}
else
{
lean_object* v_reuseFailAlloc_4471_; 
v_reuseFailAlloc_4471_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4471_, 0, v___x_4463_);
lean_ctor_set_uint64(v_reuseFailAlloc_4471_, sizeof(void*)*1, v_tid_4457_);
v___x_4465_ = v_reuseFailAlloc_4471_;
goto v_reusejp_4464_;
}
v_reusejp_4464_:
{
lean_object* v___x_4467_; 
if (v_isShared_4456_ == 0)
{
lean_ctor_set(v___x_4455_, 4, v___x_4465_);
v___x_4467_ = v___x_4455_;
goto v_reusejp_4466_;
}
else
{
lean_object* v_reuseFailAlloc_4470_; 
v_reuseFailAlloc_4470_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4470_, 0, v_env_4446_);
lean_ctor_set(v_reuseFailAlloc_4470_, 1, v_nextMacroScope_4447_);
lean_ctor_set(v_reuseFailAlloc_4470_, 2, v_ngen_4448_);
lean_ctor_set(v_reuseFailAlloc_4470_, 3, v_auxDeclNGen_4449_);
lean_ctor_set(v_reuseFailAlloc_4470_, 4, v___x_4465_);
lean_ctor_set(v_reuseFailAlloc_4470_, 5, v_cache_4450_);
lean_ctor_set(v_reuseFailAlloc_4470_, 6, v_messages_4451_);
lean_ctor_set(v_reuseFailAlloc_4470_, 7, v_infoState_4452_);
lean_ctor_set(v_reuseFailAlloc_4470_, 8, v_snapshotTasks_4453_);
v___x_4467_ = v_reuseFailAlloc_4470_;
goto v_reusejp_4466_;
}
v_reusejp_4466_:
{
lean_object* v___x_4468_; lean_object* v___x_4469_; 
v___x_4468_ = lean_st_ref_set(v___y_4439_, v___x_4467_);
v___x_4469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4469_, 0, v_traces_4443_);
return v___x_4469_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1___redArg___boxed(lean_object* v___y_4475_, lean_object* v___y_4476_){
_start:
{
lean_object* v_res_4477_; 
v_res_4477_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1___redArg(v___y_4475_);
lean_dec(v___y_4475_);
return v_res_4477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1(lean_object* v___y_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_){
_start:
{
lean_object* v___x_4485_; 
v___x_4485_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1___redArg(v___y_4483_);
return v___x_4485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1___boxed(lean_object* v___y_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_){
_start:
{
lean_object* v_res_4493_; 
v_res_4493_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1(v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_);
lean_dec(v___y_4491_);
lean_dec_ref(v___y_4490_);
lean_dec(v___y_4489_);
lean_dec_ref(v___y_4488_);
lean_dec(v___y_4487_);
lean_dec_ref(v___y_4486_);
return v_res_4493_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg___lam__0(lean_object* v_x_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_){
_start:
{
lean_object* v___x_4502_; 
lean_inc(v___y_4496_);
lean_inc_ref(v___y_4495_);
v___x_4502_ = lean_apply_7(v_x_4494_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_, v___y_4500_, lean_box(0));
return v___x_4502_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg___lam__0___boxed(lean_object* v_x_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_){
_start:
{
lean_object* v_res_4511_; 
v_res_4511_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg___lam__0(v_x_4503_, v___y_4504_, v___y_4505_, v___y_4506_, v___y_4507_, v___y_4508_, v___y_4509_);
lean_dec(v___y_4505_);
lean_dec_ref(v___y_4504_);
return v_res_4511_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg(lean_object* v_mvarId_4512_, lean_object* v_x_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_){
_start:
{
lean_object* v___f_4521_; lean_object* v___x_4522_; 
lean_inc(v___y_4515_);
lean_inc_ref(v___y_4514_);
v___f_4521_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4521_, 0, v_x_4513_);
lean_closure_set(v___f_4521_, 1, v___y_4514_);
lean_closure_set(v___f_4521_, 2, v___y_4515_);
v___x_4522_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_4512_, v___f_4521_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_);
if (lean_obj_tag(v___x_4522_) == 0)
{
return v___x_4522_;
}
else
{
lean_object* v_a_4523_; lean_object* v___x_4525_; uint8_t v_isShared_4526_; uint8_t v_isSharedCheck_4530_; 
v_a_4523_ = lean_ctor_get(v___x_4522_, 0);
v_isSharedCheck_4530_ = !lean_is_exclusive(v___x_4522_);
if (v_isSharedCheck_4530_ == 0)
{
v___x_4525_ = v___x_4522_;
v_isShared_4526_ = v_isSharedCheck_4530_;
goto v_resetjp_4524_;
}
else
{
lean_inc(v_a_4523_);
lean_dec(v___x_4522_);
v___x_4525_ = lean_box(0);
v_isShared_4526_ = v_isSharedCheck_4530_;
goto v_resetjp_4524_;
}
v_resetjp_4524_:
{
lean_object* v___x_4528_; 
if (v_isShared_4526_ == 0)
{
v___x_4528_ = v___x_4525_;
goto v_reusejp_4527_;
}
else
{
lean_object* v_reuseFailAlloc_4529_; 
v_reuseFailAlloc_4529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4529_, 0, v_a_4523_);
v___x_4528_ = v_reuseFailAlloc_4529_;
goto v_reusejp_4527_;
}
v_reusejp_4527_:
{
return v___x_4528_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg___boxed(lean_object* v_mvarId_4531_, lean_object* v_x_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_){
_start:
{
lean_object* v_res_4540_; 
v_res_4540_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg(v_mvarId_4531_, v_x_4532_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_);
lean_dec(v___y_4538_);
lean_dec_ref(v___y_4537_);
lean_dec(v___y_4536_);
lean_dec_ref(v___y_4535_);
lean_dec(v___y_4534_);
lean_dec_ref(v___y_4533_);
return v_res_4540_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4(lean_object* v_00_u03b1_4541_, lean_object* v_mvarId_4542_, lean_object* v_x_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_){
_start:
{
lean_object* v___x_4551_; 
v___x_4551_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg(v_mvarId_4542_, v_x_4543_, v___y_4544_, v___y_4545_, v___y_4546_, v___y_4547_, v___y_4548_, v___y_4549_);
return v___x_4551_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___boxed(lean_object* v_00_u03b1_4552_, lean_object* v_mvarId_4553_, lean_object* v_x_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_){
_start:
{
lean_object* v_res_4562_; 
v_res_4562_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4(v_00_u03b1_4552_, v_mvarId_4553_, v_x_4554_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_);
lean_dec(v___y_4560_);
lean_dec_ref(v___y_4559_);
lean_dec(v___y_4558_);
lean_dec_ref(v___y_4557_);
lean_dec(v___y_4556_);
lean_dec_ref(v___y_4555_);
return v_res_4562_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4564_; lean_object* v___x_4565_; 
v___x_4564_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__0));
v___x_4565_ = l_Lean_stringToMessageData(v___x_4564_);
return v___x_4565_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4567_; lean_object* v___x_4568_; 
v___x_4567_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__2));
v___x_4568_ = l_Lean_stringToMessageData(v___x_4567_);
return v___x_4568_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4570_; lean_object* v___x_4571_; 
v___x_4570_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__4));
v___x_4571_ = l_Lean_stringToMessageData(v___x_4570_);
return v___x_4571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0(lean_object* v_a_4572_, lean_object* v_x_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_){
_start:
{
if (lean_obj_tag(v_x_4573_) == 0)
{
lean_object* v_a_4581_; lean_object* v___x_4583_; uint8_t v_isShared_4584_; uint8_t v_isSharedCheck_4591_; 
lean_dec_ref(v_a_4572_);
v_a_4581_ = lean_ctor_get(v_x_4573_, 0);
v_isSharedCheck_4591_ = !lean_is_exclusive(v_x_4573_);
if (v_isSharedCheck_4591_ == 0)
{
v___x_4583_ = v_x_4573_;
v_isShared_4584_ = v_isSharedCheck_4591_;
goto v_resetjp_4582_;
}
else
{
lean_inc(v_a_4581_);
lean_dec(v_x_4573_);
v___x_4583_ = lean_box(0);
v_isShared_4584_ = v_isSharedCheck_4591_;
goto v_resetjp_4582_;
}
v_resetjp_4582_:
{
lean_object* v___x_4585_; lean_object* v___x_4586_; lean_object* v___x_4587_; lean_object* v___x_4589_; 
v___x_4585_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__1);
v___x_4586_ = l_Lean_Exception_toMessageData(v_a_4581_);
v___x_4587_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4587_, 0, v___x_4585_);
lean_ctor_set(v___x_4587_, 1, v___x_4586_);
if (v_isShared_4584_ == 0)
{
lean_ctor_set(v___x_4583_, 0, v___x_4587_);
v___x_4589_ = v___x_4583_;
goto v_reusejp_4588_;
}
else
{
lean_object* v_reuseFailAlloc_4590_; 
v_reuseFailAlloc_4590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4590_, 0, v___x_4587_);
v___x_4589_ = v_reuseFailAlloc_4590_;
goto v_reusejp_4588_;
}
v_reusejp_4588_:
{
return v___x_4589_;
}
}
}
else
{
lean_object* v_a_4592_; lean_object* v___x_4594_; uint8_t v_isShared_4595_; uint8_t v_isSharedCheck_4611_; 
v_a_4592_ = lean_ctor_get(v_x_4573_, 0);
v_isSharedCheck_4611_ = !lean_is_exclusive(v_x_4573_);
if (v_isSharedCheck_4611_ == 0)
{
v___x_4594_ = v_x_4573_;
v_isShared_4595_ = v_isSharedCheck_4611_;
goto v_resetjp_4593_;
}
else
{
lean_inc(v_a_4592_);
lean_dec(v_x_4573_);
v___x_4594_ = lean_box(0);
v_isShared_4595_ = v_isSharedCheck_4611_;
goto v_resetjp_4593_;
}
v_resetjp_4593_:
{
if (lean_obj_tag(v_a_4592_) == 0)
{
lean_object* v___x_4596_; lean_object* v___x_4598_; 
lean_dec_ref_known(v_a_4592_, 0);
lean_dec_ref(v_a_4572_);
v___x_4596_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__3, &l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__3);
if (v_isShared_4595_ == 0)
{
lean_ctor_set_tag(v___x_4594_, 0);
lean_ctor_set(v___x_4594_, 0, v___x_4596_);
v___x_4598_ = v___x_4594_;
goto v_reusejp_4597_;
}
else
{
lean_object* v_reuseFailAlloc_4599_; 
v_reuseFailAlloc_4599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4599_, 0, v___x_4596_);
v___x_4598_ = v_reuseFailAlloc_4599_;
goto v_reusejp_4597_;
}
v_reusejp_4597_:
{
return v___x_4598_;
}
}
else
{
lean_object* v_e_x27_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4609_; 
v_e_x27_4600_ = lean_ctor_get(v_a_4592_, 0);
lean_inc_ref(v_e_x27_4600_);
lean_dec_ref_known(v_a_4592_, 2);
v___x_4601_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__5, &l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__5_once, _init_l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__5);
v___x_4602_ = l_Lean_indentExpr(v_a_4572_);
v___x_4603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4603_, 0, v___x_4601_);
lean_ctor_set(v___x_4603_, 1, v___x_4602_);
v___x_4604_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_4605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4605_, 0, v___x_4603_);
lean_ctor_set(v___x_4605_, 1, v___x_4604_);
v___x_4606_ = l_Lean_indentExpr(v_e_x27_4600_);
v___x_4607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4607_, 0, v___x_4605_);
lean_ctor_set(v___x_4607_, 1, v___x_4606_);
if (v_isShared_4595_ == 0)
{
lean_ctor_set_tag(v___x_4594_, 0);
lean_ctor_set(v___x_4594_, 0, v___x_4607_);
v___x_4609_ = v___x_4594_;
goto v_reusejp_4608_;
}
else
{
lean_object* v_reuseFailAlloc_4610_; 
v_reuseFailAlloc_4610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4610_, 0, v___x_4607_);
v___x_4609_ = v_reuseFailAlloc_4610_;
goto v_reusejp_4608_;
}
v_reusejp_4608_:
{
return v___x_4609_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___boxed(lean_object* v_a_4612_, lean_object* v_x_4613_, lean_object* v___y_4614_, lean_object* v___y_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_, lean_object* v___y_4620_){
_start:
{
lean_object* v_res_4621_; 
v_res_4621_ = l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0(v_a_4612_, v_x_4613_, v___y_4614_, v___y_4615_, v___y_4616_, v___y_4617_, v___y_4618_, v___y_4619_);
lean_dec(v___y_4619_);
lean_dec_ref(v___y_4618_);
lean_dec(v___y_4617_);
lean_dec_ref(v___y_4616_);
lean_dec(v___y_4615_);
lean_dec_ref(v___y_4614_);
return v_res_4621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__3___redArg(lean_object* v_oldTraces_4622_, lean_object* v_data_4623_, lean_object* v_ref_4624_, lean_object* v_msg_4625_, lean_object* v___y_4626_, lean_object* v___y_4627_, lean_object* v___y_4628_, lean_object* v___y_4629_){
_start:
{
lean_object* v_fileName_4631_; lean_object* v_fileMap_4632_; lean_object* v_options_4633_; lean_object* v_currRecDepth_4634_; lean_object* v_maxRecDepth_4635_; lean_object* v_ref_4636_; lean_object* v_currNamespace_4637_; lean_object* v_openDecls_4638_; lean_object* v_initHeartbeats_4639_; lean_object* v_maxHeartbeats_4640_; lean_object* v_quotContext_4641_; lean_object* v_currMacroScope_4642_; uint8_t v_diag_4643_; lean_object* v_cancelTk_x3f_4644_; uint8_t v_suppressElabErrors_4645_; lean_object* v_inheritedTraceOptions_4646_; lean_object* v___x_4647_; lean_object* v_traceState_4648_; lean_object* v_traces_4649_; lean_object* v_ref_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; size_t v_sz_4653_; size_t v___x_4654_; lean_object* v___x_4655_; lean_object* v_msg_4656_; lean_object* v___x_4657_; lean_object* v_a_4658_; lean_object* v___x_4660_; uint8_t v_isShared_4661_; uint8_t v_isSharedCheck_4695_; 
v_fileName_4631_ = lean_ctor_get(v___y_4628_, 0);
v_fileMap_4632_ = lean_ctor_get(v___y_4628_, 1);
v_options_4633_ = lean_ctor_get(v___y_4628_, 2);
v_currRecDepth_4634_ = lean_ctor_get(v___y_4628_, 3);
v_maxRecDepth_4635_ = lean_ctor_get(v___y_4628_, 4);
v_ref_4636_ = lean_ctor_get(v___y_4628_, 5);
v_currNamespace_4637_ = lean_ctor_get(v___y_4628_, 6);
v_openDecls_4638_ = lean_ctor_get(v___y_4628_, 7);
v_initHeartbeats_4639_ = lean_ctor_get(v___y_4628_, 8);
v_maxHeartbeats_4640_ = lean_ctor_get(v___y_4628_, 9);
v_quotContext_4641_ = lean_ctor_get(v___y_4628_, 10);
v_currMacroScope_4642_ = lean_ctor_get(v___y_4628_, 11);
v_diag_4643_ = lean_ctor_get_uint8(v___y_4628_, sizeof(void*)*14);
v_cancelTk_x3f_4644_ = lean_ctor_get(v___y_4628_, 12);
v_suppressElabErrors_4645_ = lean_ctor_get_uint8(v___y_4628_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_4646_ = lean_ctor_get(v___y_4628_, 13);
v___x_4647_ = lean_st_ref_get(v___y_4629_);
v_traceState_4648_ = lean_ctor_get(v___x_4647_, 4);
lean_inc_ref(v_traceState_4648_);
lean_dec(v___x_4647_);
v_traces_4649_ = lean_ctor_get(v_traceState_4648_, 0);
lean_inc_ref(v_traces_4649_);
lean_dec_ref(v_traceState_4648_);
v_ref_4650_ = l_Lean_replaceRef(v_ref_4624_, v_ref_4636_);
lean_inc_ref(v_inheritedTraceOptions_4646_);
lean_inc(v_cancelTk_x3f_4644_);
lean_inc(v_currMacroScope_4642_);
lean_inc(v_quotContext_4641_);
lean_inc(v_maxHeartbeats_4640_);
lean_inc(v_initHeartbeats_4639_);
lean_inc(v_openDecls_4638_);
lean_inc(v_currNamespace_4637_);
lean_inc(v_maxRecDepth_4635_);
lean_inc(v_currRecDepth_4634_);
lean_inc_ref(v_options_4633_);
lean_inc_ref(v_fileMap_4632_);
lean_inc_ref(v_fileName_4631_);
v___x_4651_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_4651_, 0, v_fileName_4631_);
lean_ctor_set(v___x_4651_, 1, v_fileMap_4632_);
lean_ctor_set(v___x_4651_, 2, v_options_4633_);
lean_ctor_set(v___x_4651_, 3, v_currRecDepth_4634_);
lean_ctor_set(v___x_4651_, 4, v_maxRecDepth_4635_);
lean_ctor_set(v___x_4651_, 5, v_ref_4650_);
lean_ctor_set(v___x_4651_, 6, v_currNamespace_4637_);
lean_ctor_set(v___x_4651_, 7, v_openDecls_4638_);
lean_ctor_set(v___x_4651_, 8, v_initHeartbeats_4639_);
lean_ctor_set(v___x_4651_, 9, v_maxHeartbeats_4640_);
lean_ctor_set(v___x_4651_, 10, v_quotContext_4641_);
lean_ctor_set(v___x_4651_, 11, v_currMacroScope_4642_);
lean_ctor_set(v___x_4651_, 12, v_cancelTk_x3f_4644_);
lean_ctor_set(v___x_4651_, 13, v_inheritedTraceOptions_4646_);
lean_ctor_set_uint8(v___x_4651_, sizeof(void*)*14, v_diag_4643_);
lean_ctor_set_uint8(v___x_4651_, sizeof(void*)*14 + 1, v_suppressElabErrors_4645_);
v___x_4652_ = l_Lean_PersistentArray_toArray___redArg(v_traces_4649_);
lean_dec_ref(v_traces_4649_);
v_sz_4653_ = lean_array_size(v___x_4652_);
v___x_4654_ = ((size_t)0ULL);
v___x_4655_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4_spec__5(v_sz_4653_, v___x_4654_, v___x_4652_);
v_msg_4656_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_4656_, 0, v_data_4623_);
lean_ctor_set(v_msg_4656_, 1, v_msg_4625_);
lean_ctor_set(v_msg_4656_, 2, v___x_4655_);
v___x_4657_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0_spec__0(v_msg_4656_, v___y_4626_, v___y_4627_, v___x_4651_, v___y_4629_);
lean_dec_ref_known(v___x_4651_, 14);
v_a_4658_ = lean_ctor_get(v___x_4657_, 0);
v_isSharedCheck_4695_ = !lean_is_exclusive(v___x_4657_);
if (v_isSharedCheck_4695_ == 0)
{
v___x_4660_ = v___x_4657_;
v_isShared_4661_ = v_isSharedCheck_4695_;
goto v_resetjp_4659_;
}
else
{
lean_inc(v_a_4658_);
lean_dec(v___x_4657_);
v___x_4660_ = lean_box(0);
v_isShared_4661_ = v_isSharedCheck_4695_;
goto v_resetjp_4659_;
}
v_resetjp_4659_:
{
lean_object* v___x_4662_; lean_object* v_traceState_4663_; lean_object* v_env_4664_; lean_object* v_nextMacroScope_4665_; lean_object* v_ngen_4666_; lean_object* v_auxDeclNGen_4667_; lean_object* v_cache_4668_; lean_object* v_messages_4669_; lean_object* v_infoState_4670_; lean_object* v_snapshotTasks_4671_; lean_object* v___x_4673_; uint8_t v_isShared_4674_; uint8_t v_isSharedCheck_4694_; 
v___x_4662_ = lean_st_ref_take(v___y_4629_);
v_traceState_4663_ = lean_ctor_get(v___x_4662_, 4);
v_env_4664_ = lean_ctor_get(v___x_4662_, 0);
v_nextMacroScope_4665_ = lean_ctor_get(v___x_4662_, 1);
v_ngen_4666_ = lean_ctor_get(v___x_4662_, 2);
v_auxDeclNGen_4667_ = lean_ctor_get(v___x_4662_, 3);
v_cache_4668_ = lean_ctor_get(v___x_4662_, 5);
v_messages_4669_ = lean_ctor_get(v___x_4662_, 6);
v_infoState_4670_ = lean_ctor_get(v___x_4662_, 7);
v_snapshotTasks_4671_ = lean_ctor_get(v___x_4662_, 8);
v_isSharedCheck_4694_ = !lean_is_exclusive(v___x_4662_);
if (v_isSharedCheck_4694_ == 0)
{
v___x_4673_ = v___x_4662_;
v_isShared_4674_ = v_isSharedCheck_4694_;
goto v_resetjp_4672_;
}
else
{
lean_inc(v_snapshotTasks_4671_);
lean_inc(v_infoState_4670_);
lean_inc(v_messages_4669_);
lean_inc(v_cache_4668_);
lean_inc(v_traceState_4663_);
lean_inc(v_auxDeclNGen_4667_);
lean_inc(v_ngen_4666_);
lean_inc(v_nextMacroScope_4665_);
lean_inc(v_env_4664_);
lean_dec(v___x_4662_);
v___x_4673_ = lean_box(0);
v_isShared_4674_ = v_isSharedCheck_4694_;
goto v_resetjp_4672_;
}
v_resetjp_4672_:
{
uint64_t v_tid_4675_; lean_object* v___x_4677_; uint8_t v_isShared_4678_; uint8_t v_isSharedCheck_4692_; 
v_tid_4675_ = lean_ctor_get_uint64(v_traceState_4663_, sizeof(void*)*1);
v_isSharedCheck_4692_ = !lean_is_exclusive(v_traceState_4663_);
if (v_isSharedCheck_4692_ == 0)
{
lean_object* v_unused_4693_; 
v_unused_4693_ = lean_ctor_get(v_traceState_4663_, 0);
lean_dec(v_unused_4693_);
v___x_4677_ = v_traceState_4663_;
v_isShared_4678_ = v_isSharedCheck_4692_;
goto v_resetjp_4676_;
}
else
{
lean_dec(v_traceState_4663_);
v___x_4677_ = lean_box(0);
v_isShared_4678_ = v_isSharedCheck_4692_;
goto v_resetjp_4676_;
}
v_resetjp_4676_:
{
lean_object* v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4682_; 
v___x_4679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4679_, 0, v_ref_4624_);
lean_ctor_set(v___x_4679_, 1, v_a_4658_);
v___x_4680_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_4622_, v___x_4679_);
if (v_isShared_4678_ == 0)
{
lean_ctor_set(v___x_4677_, 0, v___x_4680_);
v___x_4682_ = v___x_4677_;
goto v_reusejp_4681_;
}
else
{
lean_object* v_reuseFailAlloc_4691_; 
v_reuseFailAlloc_4691_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4691_, 0, v___x_4680_);
lean_ctor_set_uint64(v_reuseFailAlloc_4691_, sizeof(void*)*1, v_tid_4675_);
v___x_4682_ = v_reuseFailAlloc_4691_;
goto v_reusejp_4681_;
}
v_reusejp_4681_:
{
lean_object* v___x_4684_; 
if (v_isShared_4674_ == 0)
{
lean_ctor_set(v___x_4673_, 4, v___x_4682_);
v___x_4684_ = v___x_4673_;
goto v_reusejp_4683_;
}
else
{
lean_object* v_reuseFailAlloc_4690_; 
v_reuseFailAlloc_4690_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4690_, 0, v_env_4664_);
lean_ctor_set(v_reuseFailAlloc_4690_, 1, v_nextMacroScope_4665_);
lean_ctor_set(v_reuseFailAlloc_4690_, 2, v_ngen_4666_);
lean_ctor_set(v_reuseFailAlloc_4690_, 3, v_auxDeclNGen_4667_);
lean_ctor_set(v_reuseFailAlloc_4690_, 4, v___x_4682_);
lean_ctor_set(v_reuseFailAlloc_4690_, 5, v_cache_4668_);
lean_ctor_set(v_reuseFailAlloc_4690_, 6, v_messages_4669_);
lean_ctor_set(v_reuseFailAlloc_4690_, 7, v_infoState_4670_);
lean_ctor_set(v_reuseFailAlloc_4690_, 8, v_snapshotTasks_4671_);
v___x_4684_ = v_reuseFailAlloc_4690_;
goto v_reusejp_4683_;
}
v_reusejp_4683_:
{
lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4688_; 
v___x_4685_ = lean_st_ref_set(v___y_4629_, v___x_4684_);
v___x_4686_ = lean_box(0);
if (v_isShared_4661_ == 0)
{
lean_ctor_set(v___x_4660_, 0, v___x_4686_);
v___x_4688_ = v___x_4660_;
goto v_reusejp_4687_;
}
else
{
lean_object* v_reuseFailAlloc_4689_; 
v_reuseFailAlloc_4689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4689_, 0, v___x_4686_);
v___x_4688_ = v_reuseFailAlloc_4689_;
goto v_reusejp_4687_;
}
v_reusejp_4687_:
{
return v___x_4688_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__3___redArg___boxed(lean_object* v_oldTraces_4696_, lean_object* v_data_4697_, lean_object* v_ref_4698_, lean_object* v_msg_4699_, lean_object* v___y_4700_, lean_object* v___y_4701_, lean_object* v___y_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_){
_start:
{
lean_object* v_res_4705_; 
v_res_4705_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__3___redArg(v_oldTraces_4696_, v_data_4697_, v_ref_4698_, v_msg_4699_, v___y_4700_, v___y_4701_, v___y_4702_, v___y_4703_);
lean_dec(v___y_4703_);
lean_dec_ref(v___y_4702_);
lean_dec(v___y_4701_);
lean_dec_ref(v___y_4700_);
return v_res_4705_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4___redArg(lean_object* v_x_4706_){
_start:
{
if (lean_obj_tag(v_x_4706_) == 0)
{
lean_object* v_a_4708_; lean_object* v___x_4710_; uint8_t v_isShared_4711_; uint8_t v_isSharedCheck_4715_; 
v_a_4708_ = lean_ctor_get(v_x_4706_, 0);
v_isSharedCheck_4715_ = !lean_is_exclusive(v_x_4706_);
if (v_isSharedCheck_4715_ == 0)
{
v___x_4710_ = v_x_4706_;
v_isShared_4711_ = v_isSharedCheck_4715_;
goto v_resetjp_4709_;
}
else
{
lean_inc(v_a_4708_);
lean_dec(v_x_4706_);
v___x_4710_ = lean_box(0);
v_isShared_4711_ = v_isSharedCheck_4715_;
goto v_resetjp_4709_;
}
v_resetjp_4709_:
{
lean_object* v___x_4713_; 
if (v_isShared_4711_ == 0)
{
lean_ctor_set_tag(v___x_4710_, 1);
v___x_4713_ = v___x_4710_;
goto v_reusejp_4712_;
}
else
{
lean_object* v_reuseFailAlloc_4714_; 
v_reuseFailAlloc_4714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4714_, 0, v_a_4708_);
v___x_4713_ = v_reuseFailAlloc_4714_;
goto v_reusejp_4712_;
}
v_reusejp_4712_:
{
return v___x_4713_;
}
}
}
else
{
lean_object* v_a_4716_; lean_object* v___x_4718_; uint8_t v_isShared_4719_; uint8_t v_isSharedCheck_4723_; 
v_a_4716_ = lean_ctor_get(v_x_4706_, 0);
v_isSharedCheck_4723_ = !lean_is_exclusive(v_x_4706_);
if (v_isSharedCheck_4723_ == 0)
{
v___x_4718_ = v_x_4706_;
v_isShared_4719_ = v_isSharedCheck_4723_;
goto v_resetjp_4717_;
}
else
{
lean_inc(v_a_4716_);
lean_dec(v_x_4706_);
v___x_4718_ = lean_box(0);
v_isShared_4719_ = v_isSharedCheck_4723_;
goto v_resetjp_4717_;
}
v_resetjp_4717_:
{
lean_object* v___x_4721_; 
if (v_isShared_4719_ == 0)
{
lean_ctor_set_tag(v___x_4718_, 0);
v___x_4721_ = v___x_4718_;
goto v_reusejp_4720_;
}
else
{
lean_object* v_reuseFailAlloc_4722_; 
v_reuseFailAlloc_4722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4722_, 0, v_a_4716_);
v___x_4721_ = v_reuseFailAlloc_4722_;
goto v_reusejp_4720_;
}
v_reusejp_4720_:
{
return v___x_4721_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4___redArg___boxed(lean_object* v_x_4724_, lean_object* v___y_4725_){
_start:
{
lean_object* v_res_4726_; 
v_res_4726_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4___redArg(v_x_4724_);
return v_res_4726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2(lean_object* v_cls_4727_, uint8_t v_collapsed_4728_, lean_object* v_tag_4729_, lean_object* v_opts_4730_, uint8_t v_clsEnabled_4731_, lean_object* v_oldTraces_4732_, lean_object* v_msg_4733_, lean_object* v_resStartStop_4734_, lean_object* v___y_4735_, lean_object* v___y_4736_, lean_object* v___y_4737_, lean_object* v___y_4738_, lean_object* v___y_4739_, lean_object* v___y_4740_){
_start:
{
lean_object* v_fst_4742_; lean_object* v_snd_4743_; lean_object* v___y_4745_; lean_object* v___y_4746_; lean_object* v_data_4747_; lean_object* v_fst_4758_; lean_object* v_snd_4759_; lean_object* v___x_4760_; uint8_t v___x_4761_; lean_object* v___y_4763_; lean_object* v_a_4764_; uint8_t v___y_4779_; double v___y_4810_; 
v_fst_4742_ = lean_ctor_get(v_resStartStop_4734_, 0);
lean_inc(v_fst_4742_);
v_snd_4743_ = lean_ctor_get(v_resStartStop_4734_, 1);
lean_inc(v_snd_4743_);
lean_dec_ref(v_resStartStop_4734_);
v_fst_4758_ = lean_ctor_get(v_snd_4743_, 0);
lean_inc(v_fst_4758_);
v_snd_4759_ = lean_ctor_get(v_snd_4743_, 1);
lean_inc(v_snd_4759_);
lean_dec(v_snd_4743_);
v___x_4760_ = l_Lean_trace_profiler;
v___x_4761_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_4730_, v___x_4760_);
if (v___x_4761_ == 0)
{
v___y_4779_ = v___x_4761_;
goto v___jp_4778_;
}
else
{
lean_object* v___x_4815_; uint8_t v___x_4816_; 
v___x_4815_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4816_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_4730_, v___x_4815_);
if (v___x_4816_ == 0)
{
lean_object* v___x_4817_; lean_object* v___x_4818_; double v___x_4819_; double v___x_4820_; double v___x_4821_; 
v___x_4817_ = l_Lean_trace_profiler_threshold;
v___x_4818_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_4730_, v___x_4817_);
v___x_4819_ = lean_float_of_nat(v___x_4818_);
v___x_4820_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2);
v___x_4821_ = lean_float_div(v___x_4819_, v___x_4820_);
v___y_4810_ = v___x_4821_;
goto v___jp_4809_;
}
else
{
lean_object* v___x_4822_; lean_object* v___x_4823_; double v___x_4824_; 
v___x_4822_ = l_Lean_trace_profiler_threshold;
v___x_4823_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_4730_, v___x_4822_);
v___x_4824_ = lean_float_of_nat(v___x_4823_);
v___y_4810_ = v___x_4824_;
goto v___jp_4809_;
}
}
v___jp_4744_:
{
lean_object* v___x_4748_; 
lean_inc(v___y_4745_);
v___x_4748_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__3___redArg(v_oldTraces_4732_, v_data_4747_, v___y_4745_, v___y_4746_, v___y_4737_, v___y_4738_, v___y_4739_, v___y_4740_);
if (lean_obj_tag(v___x_4748_) == 0)
{
lean_object* v___x_4749_; 
lean_dec_ref_known(v___x_4748_, 1);
v___x_4749_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4___redArg(v_fst_4742_);
return v___x_4749_;
}
else
{
lean_object* v_a_4750_; lean_object* v___x_4752_; uint8_t v_isShared_4753_; uint8_t v_isSharedCheck_4757_; 
lean_dec(v_fst_4742_);
v_a_4750_ = lean_ctor_get(v___x_4748_, 0);
v_isSharedCheck_4757_ = !lean_is_exclusive(v___x_4748_);
if (v_isSharedCheck_4757_ == 0)
{
v___x_4752_ = v___x_4748_;
v_isShared_4753_ = v_isSharedCheck_4757_;
goto v_resetjp_4751_;
}
else
{
lean_inc(v_a_4750_);
lean_dec(v___x_4748_);
v___x_4752_ = lean_box(0);
v_isShared_4753_ = v_isSharedCheck_4757_;
goto v_resetjp_4751_;
}
v_resetjp_4751_:
{
lean_object* v___x_4755_; 
if (v_isShared_4753_ == 0)
{
v___x_4755_ = v___x_4752_;
goto v_reusejp_4754_;
}
else
{
lean_object* v_reuseFailAlloc_4756_; 
v_reuseFailAlloc_4756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4756_, 0, v_a_4750_);
v___x_4755_ = v_reuseFailAlloc_4756_;
goto v_reusejp_4754_;
}
v_reusejp_4754_:
{
return v___x_4755_;
}
}
}
}
v___jp_4762_:
{
uint8_t v_result_4765_; lean_object* v___x_4766_; lean_object* v___x_4767_; double v___x_4768_; lean_object* v_data_4769_; 
v_result_4765_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__6(v_fst_4742_);
v___x_4766_ = lean_box(v_result_4765_);
v___x_4767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4767_, 0, v___x_4766_);
v___x_4768_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_4729_);
lean_inc_ref(v___x_4767_);
lean_inc(v_cls_4727_);
v_data_4769_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4769_, 0, v_cls_4727_);
lean_ctor_set(v_data_4769_, 1, v___x_4767_);
lean_ctor_set(v_data_4769_, 2, v_tag_4729_);
lean_ctor_set_float(v_data_4769_, sizeof(void*)*3, v___x_4768_);
lean_ctor_set_float(v_data_4769_, sizeof(void*)*3 + 8, v___x_4768_);
lean_ctor_set_uint8(v_data_4769_, sizeof(void*)*3 + 16, v_collapsed_4728_);
if (v___x_4761_ == 0)
{
lean_dec_ref_known(v___x_4767_, 1);
lean_dec(v_snd_4759_);
lean_dec(v_fst_4758_);
lean_dec_ref(v_tag_4729_);
lean_dec(v_cls_4727_);
v___y_4745_ = v___y_4763_;
v___y_4746_ = v_a_4764_;
v_data_4747_ = v_data_4769_;
goto v___jp_4744_;
}
else
{
lean_object* v_data_4770_; double v___x_4771_; double v___x_4772_; 
lean_dec_ref_known(v_data_4769_, 3);
v_data_4770_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4770_, 0, v_cls_4727_);
lean_ctor_set(v_data_4770_, 1, v___x_4767_);
lean_ctor_set(v_data_4770_, 2, v_tag_4729_);
v___x_4771_ = lean_unbox_float(v_fst_4758_);
lean_dec(v_fst_4758_);
lean_ctor_set_float(v_data_4770_, sizeof(void*)*3, v___x_4771_);
v___x_4772_ = lean_unbox_float(v_snd_4759_);
lean_dec(v_snd_4759_);
lean_ctor_set_float(v_data_4770_, sizeof(void*)*3 + 8, v___x_4772_);
lean_ctor_set_uint8(v_data_4770_, sizeof(void*)*3 + 16, v_collapsed_4728_);
v___y_4745_ = v___y_4763_;
v___y_4746_ = v_a_4764_;
v_data_4747_ = v_data_4770_;
goto v___jp_4744_;
}
}
v___jp_4773_:
{
lean_object* v_ref_4774_; lean_object* v___x_4775_; 
v_ref_4774_ = lean_ctor_get(v___y_4739_, 5);
lean_inc(v___y_4740_);
lean_inc_ref(v___y_4739_);
lean_inc(v___y_4738_);
lean_inc_ref(v___y_4737_);
lean_inc(v___y_4736_);
lean_inc_ref(v___y_4735_);
lean_inc(v_fst_4742_);
v___x_4775_ = lean_apply_8(v_msg_4733_, v_fst_4742_, v___y_4735_, v___y_4736_, v___y_4737_, v___y_4738_, v___y_4739_, v___y_4740_, lean_box(0));
if (lean_obj_tag(v___x_4775_) == 0)
{
lean_object* v_a_4776_; 
v_a_4776_ = lean_ctor_get(v___x_4775_, 0);
lean_inc(v_a_4776_);
lean_dec_ref_known(v___x_4775_, 1);
v___y_4763_ = v_ref_4774_;
v_a_4764_ = v_a_4776_;
goto v___jp_4762_;
}
else
{
lean_object* v___x_4777_; 
lean_dec_ref_known(v___x_4775_, 1);
v___x_4777_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1);
v___y_4763_ = v_ref_4774_;
v_a_4764_ = v___x_4777_;
goto v___jp_4762_;
}
}
v___jp_4778_:
{
if (v_clsEnabled_4731_ == 0)
{
if (v___y_4779_ == 0)
{
lean_object* v___x_4780_; lean_object* v_traceState_4781_; lean_object* v_env_4782_; lean_object* v_nextMacroScope_4783_; lean_object* v_ngen_4784_; lean_object* v_auxDeclNGen_4785_; lean_object* v_cache_4786_; lean_object* v_messages_4787_; lean_object* v_infoState_4788_; lean_object* v_snapshotTasks_4789_; lean_object* v___x_4791_; uint8_t v_isShared_4792_; uint8_t v_isSharedCheck_4808_; 
lean_dec(v_snd_4759_);
lean_dec(v_fst_4758_);
lean_dec_ref(v_msg_4733_);
lean_dec_ref(v_tag_4729_);
lean_dec(v_cls_4727_);
v___x_4780_ = lean_st_ref_take(v___y_4740_);
v_traceState_4781_ = lean_ctor_get(v___x_4780_, 4);
v_env_4782_ = lean_ctor_get(v___x_4780_, 0);
v_nextMacroScope_4783_ = lean_ctor_get(v___x_4780_, 1);
v_ngen_4784_ = lean_ctor_get(v___x_4780_, 2);
v_auxDeclNGen_4785_ = lean_ctor_get(v___x_4780_, 3);
v_cache_4786_ = lean_ctor_get(v___x_4780_, 5);
v_messages_4787_ = lean_ctor_get(v___x_4780_, 6);
v_infoState_4788_ = lean_ctor_get(v___x_4780_, 7);
v_snapshotTasks_4789_ = lean_ctor_get(v___x_4780_, 8);
v_isSharedCheck_4808_ = !lean_is_exclusive(v___x_4780_);
if (v_isSharedCheck_4808_ == 0)
{
v___x_4791_ = v___x_4780_;
v_isShared_4792_ = v_isSharedCheck_4808_;
goto v_resetjp_4790_;
}
else
{
lean_inc(v_snapshotTasks_4789_);
lean_inc(v_infoState_4788_);
lean_inc(v_messages_4787_);
lean_inc(v_cache_4786_);
lean_inc(v_traceState_4781_);
lean_inc(v_auxDeclNGen_4785_);
lean_inc(v_ngen_4784_);
lean_inc(v_nextMacroScope_4783_);
lean_inc(v_env_4782_);
lean_dec(v___x_4780_);
v___x_4791_ = lean_box(0);
v_isShared_4792_ = v_isSharedCheck_4808_;
goto v_resetjp_4790_;
}
v_resetjp_4790_:
{
uint64_t v_tid_4793_; lean_object* v_traces_4794_; lean_object* v___x_4796_; uint8_t v_isShared_4797_; uint8_t v_isSharedCheck_4807_; 
v_tid_4793_ = lean_ctor_get_uint64(v_traceState_4781_, sizeof(void*)*1);
v_traces_4794_ = lean_ctor_get(v_traceState_4781_, 0);
v_isSharedCheck_4807_ = !lean_is_exclusive(v_traceState_4781_);
if (v_isSharedCheck_4807_ == 0)
{
v___x_4796_ = v_traceState_4781_;
v_isShared_4797_ = v_isSharedCheck_4807_;
goto v_resetjp_4795_;
}
else
{
lean_inc(v_traces_4794_);
lean_dec(v_traceState_4781_);
v___x_4796_ = lean_box(0);
v_isShared_4797_ = v_isSharedCheck_4807_;
goto v_resetjp_4795_;
}
v_resetjp_4795_:
{
lean_object* v___x_4798_; lean_object* v___x_4800_; 
v___x_4798_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_4732_, v_traces_4794_);
lean_dec_ref(v_traces_4794_);
if (v_isShared_4797_ == 0)
{
lean_ctor_set(v___x_4796_, 0, v___x_4798_);
v___x_4800_ = v___x_4796_;
goto v_reusejp_4799_;
}
else
{
lean_object* v_reuseFailAlloc_4806_; 
v_reuseFailAlloc_4806_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4806_, 0, v___x_4798_);
lean_ctor_set_uint64(v_reuseFailAlloc_4806_, sizeof(void*)*1, v_tid_4793_);
v___x_4800_ = v_reuseFailAlloc_4806_;
goto v_reusejp_4799_;
}
v_reusejp_4799_:
{
lean_object* v___x_4802_; 
if (v_isShared_4792_ == 0)
{
lean_ctor_set(v___x_4791_, 4, v___x_4800_);
v___x_4802_ = v___x_4791_;
goto v_reusejp_4801_;
}
else
{
lean_object* v_reuseFailAlloc_4805_; 
v_reuseFailAlloc_4805_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4805_, 0, v_env_4782_);
lean_ctor_set(v_reuseFailAlloc_4805_, 1, v_nextMacroScope_4783_);
lean_ctor_set(v_reuseFailAlloc_4805_, 2, v_ngen_4784_);
lean_ctor_set(v_reuseFailAlloc_4805_, 3, v_auxDeclNGen_4785_);
lean_ctor_set(v_reuseFailAlloc_4805_, 4, v___x_4800_);
lean_ctor_set(v_reuseFailAlloc_4805_, 5, v_cache_4786_);
lean_ctor_set(v_reuseFailAlloc_4805_, 6, v_messages_4787_);
lean_ctor_set(v_reuseFailAlloc_4805_, 7, v_infoState_4788_);
lean_ctor_set(v_reuseFailAlloc_4805_, 8, v_snapshotTasks_4789_);
v___x_4802_ = v_reuseFailAlloc_4805_;
goto v_reusejp_4801_;
}
v_reusejp_4801_:
{
lean_object* v___x_4803_; lean_object* v___x_4804_; 
v___x_4803_ = lean_st_ref_set(v___y_4740_, v___x_4802_);
v___x_4804_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4___redArg(v_fst_4742_);
return v___x_4804_;
}
}
}
}
}
else
{
goto v___jp_4773_;
}
}
else
{
goto v___jp_4773_;
}
}
v___jp_4809_:
{
double v___x_4811_; double v___x_4812_; double v___x_4813_; uint8_t v___x_4814_; 
v___x_4811_ = lean_unbox_float(v_snd_4759_);
v___x_4812_ = lean_unbox_float(v_fst_4758_);
v___x_4813_ = lean_float_sub(v___x_4811_, v___x_4812_);
v___x_4814_ = lean_float_decLt(v___y_4810_, v___x_4813_);
v___y_4779_ = v___x_4814_;
goto v___jp_4778_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2___boxed(lean_object* v_cls_4825_, lean_object* v_collapsed_4826_, lean_object* v_tag_4827_, lean_object* v_opts_4828_, lean_object* v_clsEnabled_4829_, lean_object* v_oldTraces_4830_, lean_object* v_msg_4831_, lean_object* v_resStartStop_4832_, lean_object* v___y_4833_, lean_object* v___y_4834_, lean_object* v___y_4835_, lean_object* v___y_4836_, lean_object* v___y_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_){
_start:
{
uint8_t v_collapsed_boxed_4840_; uint8_t v_clsEnabled_boxed_4841_; lean_object* v_res_4842_; 
v_collapsed_boxed_4840_ = lean_unbox(v_collapsed_4826_);
v_clsEnabled_boxed_4841_ = lean_unbox(v_clsEnabled_4829_);
v_res_4842_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2(v_cls_4825_, v_collapsed_boxed_4840_, v_tag_4827_, v_opts_4828_, v_clsEnabled_boxed_4841_, v_oldTraces_4830_, v_msg_4831_, v_resStartStop_4832_, v___y_4833_, v___y_4834_, v___y_4835_, v___y_4836_, v___y_4837_, v___y_4838_);
lean_dec(v___y_4838_);
lean_dec_ref(v___y_4837_);
lean_dec(v___y_4836_);
lean_dec_ref(v___y_4835_);
lean_dec(v___y_4834_);
lean_dec_ref(v___y_4833_);
lean_dec_ref(v_opts_4828_);
return v_res_4842_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4844_; lean_object* v___x_4845_; 
v___x_4844_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__0));
v___x_4845_ = l_Lean_stringToMessageData(v___x_4844_);
return v___x_4845_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4847_; lean_object* v___x_4848_; 
v___x_4847_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__2));
v___x_4848_ = l_Lean_stringToMessageData(v___x_4847_);
return v___x_4848_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4850_; lean_object* v___x_4851_; 
v___x_4850_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__4));
v___x_4851_ = l_Lean_stringToMessageData(v___x_4850_);
return v___x_4851_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0(lean_object* v_a_4852_, lean_object* v___x_4853_, lean_object* v_x_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_){
_start:
{
if (lean_obj_tag(v_x_4854_) == 0)
{
lean_object* v_a_4862_; lean_object* v___x_4864_; uint8_t v_isShared_4865_; uint8_t v_isSharedCheck_4877_; 
lean_dec_ref(v___x_4853_);
v_a_4862_ = lean_ctor_get(v_x_4854_, 0);
v_isSharedCheck_4877_ = !lean_is_exclusive(v_x_4854_);
if (v_isSharedCheck_4877_ == 0)
{
v___x_4864_ = v_x_4854_;
v_isShared_4865_ = v_isSharedCheck_4877_;
goto v_resetjp_4863_;
}
else
{
lean_inc(v_a_4862_);
lean_dec(v_x_4854_);
v___x_4864_ = lean_box(0);
v_isShared_4865_ = v_isSharedCheck_4877_;
goto v_resetjp_4863_;
}
v_resetjp_4863_:
{
lean_object* v___x_4866_; lean_object* v___x_4867_; lean_object* v___x_4868_; lean_object* v___x_4869_; lean_object* v___x_4870_; lean_object* v___x_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; lean_object* v___x_4875_; 
v___x_4866_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1);
v___x_4867_ = l_Lean_LocalDecl_userName(v_a_4852_);
v___x_4868_ = l_Lean_MessageData_ofName(v___x_4867_);
v___x_4869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4869_, 0, v___x_4866_);
lean_ctor_set(v___x_4869_, 1, v___x_4868_);
v___x_4870_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__3);
v___x_4871_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4871_, 0, v___x_4869_);
lean_ctor_set(v___x_4871_, 1, v___x_4870_);
v___x_4872_ = l_Lean_Exception_toMessageData(v_a_4862_);
v___x_4873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4873_, 0, v___x_4871_);
lean_ctor_set(v___x_4873_, 1, v___x_4872_);
if (v_isShared_4865_ == 0)
{
lean_ctor_set(v___x_4864_, 0, v___x_4873_);
v___x_4875_ = v___x_4864_;
goto v_reusejp_4874_;
}
else
{
lean_object* v_reuseFailAlloc_4876_; 
v_reuseFailAlloc_4876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4876_, 0, v___x_4873_);
v___x_4875_ = v_reuseFailAlloc_4876_;
goto v_reusejp_4874_;
}
v_reusejp_4874_:
{
return v___x_4875_;
}
}
}
else
{
lean_object* v_a_4878_; lean_object* v___x_4880_; uint8_t v_isShared_4881_; uint8_t v_isSharedCheck_4907_; 
v_a_4878_ = lean_ctor_get(v_x_4854_, 0);
v_isSharedCheck_4907_ = !lean_is_exclusive(v_x_4854_);
if (v_isSharedCheck_4907_ == 0)
{
v___x_4880_ = v_x_4854_;
v_isShared_4881_ = v_isSharedCheck_4907_;
goto v_resetjp_4879_;
}
else
{
lean_inc(v_a_4878_);
lean_dec(v_x_4854_);
v___x_4880_ = lean_box(0);
v_isShared_4881_ = v_isSharedCheck_4907_;
goto v_resetjp_4879_;
}
v_resetjp_4879_:
{
if (lean_obj_tag(v_a_4878_) == 0)
{
lean_object* v___x_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; lean_object* v___x_4889_; 
lean_dec_ref_known(v_a_4878_, 0);
lean_dec_ref(v___x_4853_);
v___x_4882_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1);
v___x_4883_ = l_Lean_LocalDecl_userName(v_a_4852_);
v___x_4884_ = l_Lean_MessageData_ofName(v___x_4883_);
v___x_4885_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4885_, 0, v___x_4882_);
lean_ctor_set(v___x_4885_, 1, v___x_4884_);
v___x_4886_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__5);
v___x_4887_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4887_, 0, v___x_4885_);
lean_ctor_set(v___x_4887_, 1, v___x_4886_);
if (v_isShared_4881_ == 0)
{
lean_ctor_set_tag(v___x_4880_, 0);
lean_ctor_set(v___x_4880_, 0, v___x_4887_);
v___x_4889_ = v___x_4880_;
goto v_reusejp_4888_;
}
else
{
lean_object* v_reuseFailAlloc_4890_; 
v_reuseFailAlloc_4890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4890_, 0, v___x_4887_);
v___x_4889_ = v_reuseFailAlloc_4890_;
goto v_reusejp_4888_;
}
v_reusejp_4888_:
{
return v___x_4889_;
}
}
else
{
lean_object* v_e_x27_4891_; lean_object* v___x_4892_; lean_object* v___x_4893_; lean_object* v___x_4894_; lean_object* v___x_4895_; lean_object* v___x_4896_; lean_object* v___x_4897_; lean_object* v___x_4898_; lean_object* v___x_4899_; lean_object* v___x_4900_; lean_object* v___x_4901_; lean_object* v___x_4902_; lean_object* v___x_4903_; lean_object* v___x_4905_; 
v_e_x27_4891_ = lean_ctor_get(v_a_4878_, 0);
lean_inc_ref(v_e_x27_4891_);
lean_dec_ref_known(v_a_4878_, 2);
v___x_4892_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1);
v___x_4893_ = l_Lean_LocalDecl_userName(v_a_4852_);
v___x_4894_ = l_Lean_MessageData_ofName(v___x_4893_);
v___x_4895_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4895_, 0, v___x_4892_);
lean_ctor_set(v___x_4895_, 1, v___x_4894_);
v___x_4896_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8);
v___x_4897_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4897_, 0, v___x_4895_);
lean_ctor_set(v___x_4897_, 1, v___x_4896_);
v___x_4898_ = l_Lean_indentExpr(v___x_4853_);
v___x_4899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4899_, 0, v___x_4897_);
lean_ctor_set(v___x_4899_, 1, v___x_4898_);
v___x_4900_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_4901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4901_, 0, v___x_4899_);
lean_ctor_set(v___x_4901_, 1, v___x_4900_);
v___x_4902_ = l_Lean_indentExpr(v_e_x27_4891_);
v___x_4903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4903_, 0, v___x_4901_);
lean_ctor_set(v___x_4903_, 1, v___x_4902_);
if (v_isShared_4881_ == 0)
{
lean_ctor_set_tag(v___x_4880_, 0);
lean_ctor_set(v___x_4880_, 0, v___x_4903_);
v___x_4905_ = v___x_4880_;
goto v_reusejp_4904_;
}
else
{
lean_object* v_reuseFailAlloc_4906_; 
v_reuseFailAlloc_4906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4906_, 0, v___x_4903_);
v___x_4905_ = v_reuseFailAlloc_4906_;
goto v_reusejp_4904_;
}
v_reusejp_4904_:
{
return v___x_4905_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___boxed(lean_object* v_a_4908_, lean_object* v___x_4909_, lean_object* v_x_4910_, lean_object* v___y_4911_, lean_object* v___y_4912_, lean_object* v___y_4913_, lean_object* v___y_4914_, lean_object* v___y_4915_, lean_object* v___y_4916_, lean_object* v___y_4917_){
_start:
{
lean_object* v_res_4918_; 
v_res_4918_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0(v_a_4908_, v___x_4909_, v_x_4910_, v___y_4911_, v___y_4912_, v___y_4913_, v___y_4914_, v___y_4915_, v___y_4916_);
lean_dec(v___y_4916_);
lean_dec_ref(v___y_4915_);
lean_dec(v___y_4914_);
lean_dec_ref(v___y_4913_);
lean_dec(v___y_4912_);
lean_dec_ref(v___y_4911_);
lean_dec_ref(v_a_4908_);
return v_res_4918_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__7_spec__9___redArg(lean_object* v_x_4919_, lean_object* v_x_4920_, lean_object* v_x_4921_, lean_object* v_x_4922_){
_start:
{
lean_object* v_ks_4923_; lean_object* v_vs_4924_; lean_object* v___x_4926_; uint8_t v_isShared_4927_; uint8_t v_isSharedCheck_4948_; 
v_ks_4923_ = lean_ctor_get(v_x_4919_, 0);
v_vs_4924_ = lean_ctor_get(v_x_4919_, 1);
v_isSharedCheck_4948_ = !lean_is_exclusive(v_x_4919_);
if (v_isSharedCheck_4948_ == 0)
{
v___x_4926_ = v_x_4919_;
v_isShared_4927_ = v_isSharedCheck_4948_;
goto v_resetjp_4925_;
}
else
{
lean_inc(v_vs_4924_);
lean_inc(v_ks_4923_);
lean_dec(v_x_4919_);
v___x_4926_ = lean_box(0);
v_isShared_4927_ = v_isSharedCheck_4948_;
goto v_resetjp_4925_;
}
v_resetjp_4925_:
{
lean_object* v___x_4928_; uint8_t v___x_4929_; 
v___x_4928_ = lean_array_get_size(v_ks_4923_);
v___x_4929_ = lean_nat_dec_lt(v_x_4920_, v___x_4928_);
if (v___x_4929_ == 0)
{
lean_object* v___x_4930_; lean_object* v___x_4931_; lean_object* v___x_4933_; 
lean_dec(v_x_4920_);
v___x_4930_ = lean_array_push(v_ks_4923_, v_x_4921_);
v___x_4931_ = lean_array_push(v_vs_4924_, v_x_4922_);
if (v_isShared_4927_ == 0)
{
lean_ctor_set(v___x_4926_, 1, v___x_4931_);
lean_ctor_set(v___x_4926_, 0, v___x_4930_);
v___x_4933_ = v___x_4926_;
goto v_reusejp_4932_;
}
else
{
lean_object* v_reuseFailAlloc_4934_; 
v_reuseFailAlloc_4934_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4934_, 0, v___x_4930_);
lean_ctor_set(v_reuseFailAlloc_4934_, 1, v___x_4931_);
v___x_4933_ = v_reuseFailAlloc_4934_;
goto v_reusejp_4932_;
}
v_reusejp_4932_:
{
return v___x_4933_;
}
}
else
{
lean_object* v_k_x27_4935_; uint8_t v___x_4936_; 
v_k_x27_4935_ = lean_array_fget_borrowed(v_ks_4923_, v_x_4920_);
v___x_4936_ = l_Lean_instBEqMVarId_beq(v_x_4921_, v_k_x27_4935_);
if (v___x_4936_ == 0)
{
lean_object* v___x_4938_; 
if (v_isShared_4927_ == 0)
{
v___x_4938_ = v___x_4926_;
goto v_reusejp_4937_;
}
else
{
lean_object* v_reuseFailAlloc_4942_; 
v_reuseFailAlloc_4942_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4942_, 0, v_ks_4923_);
lean_ctor_set(v_reuseFailAlloc_4942_, 1, v_vs_4924_);
v___x_4938_ = v_reuseFailAlloc_4942_;
goto v_reusejp_4937_;
}
v_reusejp_4937_:
{
lean_object* v___x_4939_; lean_object* v___x_4940_; 
v___x_4939_ = lean_unsigned_to_nat(1u);
v___x_4940_ = lean_nat_add(v_x_4920_, v___x_4939_);
lean_dec(v_x_4920_);
v_x_4919_ = v___x_4938_;
v_x_4920_ = v___x_4940_;
goto _start;
}
}
else
{
lean_object* v___x_4943_; lean_object* v___x_4944_; lean_object* v___x_4946_; 
v___x_4943_ = lean_array_fset(v_ks_4923_, v_x_4920_, v_x_4921_);
v___x_4944_ = lean_array_fset(v_vs_4924_, v_x_4920_, v_x_4922_);
lean_dec(v_x_4920_);
if (v_isShared_4927_ == 0)
{
lean_ctor_set(v___x_4926_, 1, v___x_4944_);
lean_ctor_set(v___x_4926_, 0, v___x_4943_);
v___x_4946_ = v___x_4926_;
goto v_reusejp_4945_;
}
else
{
lean_object* v_reuseFailAlloc_4947_; 
v_reuseFailAlloc_4947_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4947_, 0, v___x_4943_);
lean_ctor_set(v_reuseFailAlloc_4947_, 1, v___x_4944_);
v___x_4946_ = v_reuseFailAlloc_4947_;
goto v_reusejp_4945_;
}
v_reusejp_4945_:
{
return v___x_4946_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__7___redArg(lean_object* v_n_4949_, lean_object* v_k_4950_, lean_object* v_v_4951_){
_start:
{
lean_object* v___x_4952_; lean_object* v___x_4953_; 
v___x_4952_ = lean_unsigned_to_nat(0u);
v___x_4953_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__7_spec__9___redArg(v_n_4949_, v___x_4952_, v_k_4950_, v_v_4951_);
return v___x_4953_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_4954_; 
v___x_4954_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_4954_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg(lean_object* v_x_4955_, size_t v_x_4956_, size_t v_x_4957_, lean_object* v_x_4958_, lean_object* v_x_4959_){
_start:
{
if (lean_obj_tag(v_x_4955_) == 0)
{
lean_object* v_es_4960_; size_t v___x_4961_; size_t v___x_4962_; lean_object* v_j_4963_; lean_object* v___x_4964_; uint8_t v___x_4965_; 
v_es_4960_ = lean_ctor_get(v_x_4955_, 0);
v___x_4961_ = ((size_t)31ULL);
v___x_4962_ = lean_usize_land(v_x_4956_, v___x_4961_);
v_j_4963_ = lean_usize_to_nat(v___x_4962_);
v___x_4964_ = lean_array_get_size(v_es_4960_);
v___x_4965_ = lean_nat_dec_lt(v_j_4963_, v___x_4964_);
if (v___x_4965_ == 0)
{
lean_dec(v_j_4963_);
lean_dec(v_x_4959_);
lean_dec(v_x_4958_);
return v_x_4955_;
}
else
{
lean_object* v___x_4967_; uint8_t v_isShared_4968_; uint8_t v_isSharedCheck_5004_; 
lean_inc_ref(v_es_4960_);
v_isSharedCheck_5004_ = !lean_is_exclusive(v_x_4955_);
if (v_isSharedCheck_5004_ == 0)
{
lean_object* v_unused_5005_; 
v_unused_5005_ = lean_ctor_get(v_x_4955_, 0);
lean_dec(v_unused_5005_);
v___x_4967_ = v_x_4955_;
v_isShared_4968_ = v_isSharedCheck_5004_;
goto v_resetjp_4966_;
}
else
{
lean_dec(v_x_4955_);
v___x_4967_ = lean_box(0);
v_isShared_4968_ = v_isSharedCheck_5004_;
goto v_resetjp_4966_;
}
v_resetjp_4966_:
{
lean_object* v_v_4969_; lean_object* v___x_4970_; lean_object* v_xs_x27_4971_; lean_object* v___y_4973_; 
v_v_4969_ = lean_array_fget(v_es_4960_, v_j_4963_);
v___x_4970_ = lean_box(0);
v_xs_x27_4971_ = lean_array_fset(v_es_4960_, v_j_4963_, v___x_4970_);
switch(lean_obj_tag(v_v_4969_))
{
case 0:
{
lean_object* v_key_4978_; lean_object* v_val_4979_; lean_object* v___x_4981_; uint8_t v_isShared_4982_; uint8_t v_isSharedCheck_4989_; 
v_key_4978_ = lean_ctor_get(v_v_4969_, 0);
v_val_4979_ = lean_ctor_get(v_v_4969_, 1);
v_isSharedCheck_4989_ = !lean_is_exclusive(v_v_4969_);
if (v_isSharedCheck_4989_ == 0)
{
v___x_4981_ = v_v_4969_;
v_isShared_4982_ = v_isSharedCheck_4989_;
goto v_resetjp_4980_;
}
else
{
lean_inc(v_val_4979_);
lean_inc(v_key_4978_);
lean_dec(v_v_4969_);
v___x_4981_ = lean_box(0);
v_isShared_4982_ = v_isSharedCheck_4989_;
goto v_resetjp_4980_;
}
v_resetjp_4980_:
{
uint8_t v___x_4983_; 
v___x_4983_ = l_Lean_instBEqMVarId_beq(v_x_4958_, v_key_4978_);
if (v___x_4983_ == 0)
{
lean_object* v___x_4984_; lean_object* v___x_4985_; 
lean_del_object(v___x_4981_);
v___x_4984_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_4978_, v_val_4979_, v_x_4958_, v_x_4959_);
v___x_4985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4985_, 0, v___x_4984_);
v___y_4973_ = v___x_4985_;
goto v___jp_4972_;
}
else
{
lean_object* v___x_4987_; 
lean_dec(v_val_4979_);
lean_dec(v_key_4978_);
if (v_isShared_4982_ == 0)
{
lean_ctor_set(v___x_4981_, 1, v_x_4959_);
lean_ctor_set(v___x_4981_, 0, v_x_4958_);
v___x_4987_ = v___x_4981_;
goto v_reusejp_4986_;
}
else
{
lean_object* v_reuseFailAlloc_4988_; 
v_reuseFailAlloc_4988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4988_, 0, v_x_4958_);
lean_ctor_set(v_reuseFailAlloc_4988_, 1, v_x_4959_);
v___x_4987_ = v_reuseFailAlloc_4988_;
goto v_reusejp_4986_;
}
v_reusejp_4986_:
{
v___y_4973_ = v___x_4987_;
goto v___jp_4972_;
}
}
}
}
case 1:
{
lean_object* v_node_4990_; lean_object* v___x_4992_; uint8_t v_isShared_4993_; uint8_t v_isSharedCheck_5002_; 
v_node_4990_ = lean_ctor_get(v_v_4969_, 0);
v_isSharedCheck_5002_ = !lean_is_exclusive(v_v_4969_);
if (v_isSharedCheck_5002_ == 0)
{
v___x_4992_ = v_v_4969_;
v_isShared_4993_ = v_isSharedCheck_5002_;
goto v_resetjp_4991_;
}
else
{
lean_inc(v_node_4990_);
lean_dec(v_v_4969_);
v___x_4992_ = lean_box(0);
v_isShared_4993_ = v_isSharedCheck_5002_;
goto v_resetjp_4991_;
}
v_resetjp_4991_:
{
size_t v___x_4994_; size_t v___x_4995_; size_t v___x_4996_; size_t v___x_4997_; lean_object* v___x_4998_; lean_object* v___x_5000_; 
v___x_4994_ = ((size_t)5ULL);
v___x_4995_ = lean_usize_shift_right(v_x_4956_, v___x_4994_);
v___x_4996_ = ((size_t)1ULL);
v___x_4997_ = lean_usize_add(v_x_4957_, v___x_4996_);
v___x_4998_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg(v_node_4990_, v___x_4995_, v___x_4997_, v_x_4958_, v_x_4959_);
if (v_isShared_4993_ == 0)
{
lean_ctor_set(v___x_4992_, 0, v___x_4998_);
v___x_5000_ = v___x_4992_;
goto v_reusejp_4999_;
}
else
{
lean_object* v_reuseFailAlloc_5001_; 
v_reuseFailAlloc_5001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5001_, 0, v___x_4998_);
v___x_5000_ = v_reuseFailAlloc_5001_;
goto v_reusejp_4999_;
}
v_reusejp_4999_:
{
v___y_4973_ = v___x_5000_;
goto v___jp_4972_;
}
}
}
default: 
{
lean_object* v___x_5003_; 
v___x_5003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5003_, 0, v_x_4958_);
lean_ctor_set(v___x_5003_, 1, v_x_4959_);
v___y_4973_ = v___x_5003_;
goto v___jp_4972_;
}
}
v___jp_4972_:
{
lean_object* v___x_4974_; lean_object* v___x_4976_; 
v___x_4974_ = lean_array_fset(v_xs_x27_4971_, v_j_4963_, v___y_4973_);
lean_dec(v_j_4963_);
if (v_isShared_4968_ == 0)
{
lean_ctor_set(v___x_4967_, 0, v___x_4974_);
v___x_4976_ = v___x_4967_;
goto v_reusejp_4975_;
}
else
{
lean_object* v_reuseFailAlloc_4977_; 
v_reuseFailAlloc_4977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4977_, 0, v___x_4974_);
v___x_4976_ = v_reuseFailAlloc_4977_;
goto v_reusejp_4975_;
}
v_reusejp_4975_:
{
return v___x_4976_;
}
}
}
}
}
else
{
lean_object* v_ks_5006_; lean_object* v_vs_5007_; lean_object* v___x_5009_; uint8_t v_isShared_5010_; uint8_t v_isSharedCheck_5027_; 
v_ks_5006_ = lean_ctor_get(v_x_4955_, 0);
v_vs_5007_ = lean_ctor_get(v_x_4955_, 1);
v_isSharedCheck_5027_ = !lean_is_exclusive(v_x_4955_);
if (v_isSharedCheck_5027_ == 0)
{
v___x_5009_ = v_x_4955_;
v_isShared_5010_ = v_isSharedCheck_5027_;
goto v_resetjp_5008_;
}
else
{
lean_inc(v_vs_5007_);
lean_inc(v_ks_5006_);
lean_dec(v_x_4955_);
v___x_5009_ = lean_box(0);
v_isShared_5010_ = v_isSharedCheck_5027_;
goto v_resetjp_5008_;
}
v_resetjp_5008_:
{
lean_object* v___x_5012_; 
if (v_isShared_5010_ == 0)
{
v___x_5012_ = v___x_5009_;
goto v_reusejp_5011_;
}
else
{
lean_object* v_reuseFailAlloc_5026_; 
v_reuseFailAlloc_5026_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5026_, 0, v_ks_5006_);
lean_ctor_set(v_reuseFailAlloc_5026_, 1, v_vs_5007_);
v___x_5012_ = v_reuseFailAlloc_5026_;
goto v_reusejp_5011_;
}
v_reusejp_5011_:
{
lean_object* v_newNode_5013_; uint8_t v___y_5015_; size_t v___x_5021_; uint8_t v___x_5022_; 
v_newNode_5013_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__7___redArg(v___x_5012_, v_x_4958_, v_x_4959_);
v___x_5021_ = ((size_t)7ULL);
v___x_5022_ = lean_usize_dec_le(v___x_5021_, v_x_4957_);
if (v___x_5022_ == 0)
{
lean_object* v___x_5023_; lean_object* v___x_5024_; uint8_t v___x_5025_; 
v___x_5023_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_5013_);
v___x_5024_ = lean_unsigned_to_nat(4u);
v___x_5025_ = lean_nat_dec_lt(v___x_5023_, v___x_5024_);
lean_dec(v___x_5023_);
v___y_5015_ = v___x_5025_;
goto v___jp_5014_;
}
else
{
v___y_5015_ = v___x_5022_;
goto v___jp_5014_;
}
v___jp_5014_:
{
if (v___y_5015_ == 0)
{
lean_object* v_ks_5016_; lean_object* v_vs_5017_; lean_object* v___x_5018_; lean_object* v___x_5019_; lean_object* v___x_5020_; 
v_ks_5016_ = lean_ctor_get(v_newNode_5013_, 0);
lean_inc_ref(v_ks_5016_);
v_vs_5017_ = lean_ctor_get(v_newNode_5013_, 1);
lean_inc_ref(v_vs_5017_);
lean_dec_ref(v_newNode_5013_);
v___x_5018_ = lean_unsigned_to_nat(0u);
v___x_5019_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg___closed__0);
v___x_5020_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__8___redArg(v_x_4957_, v_ks_5016_, v_vs_5017_, v___x_5018_, v___x_5019_);
lean_dec_ref(v_vs_5017_);
lean_dec_ref(v_ks_5016_);
return v___x_5020_;
}
else
{
return v_newNode_5013_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__8___redArg(size_t v_depth_5028_, lean_object* v_keys_5029_, lean_object* v_vals_5030_, lean_object* v_i_5031_, lean_object* v_entries_5032_){
_start:
{
lean_object* v___x_5033_; uint8_t v___x_5034_; 
v___x_5033_ = lean_array_get_size(v_keys_5029_);
v___x_5034_ = lean_nat_dec_lt(v_i_5031_, v___x_5033_);
if (v___x_5034_ == 0)
{
lean_dec(v_i_5031_);
return v_entries_5032_;
}
else
{
lean_object* v_k_5035_; lean_object* v_v_5036_; uint64_t v___x_5037_; size_t v_h_5038_; size_t v___x_5039_; lean_object* v___x_5040_; size_t v___x_5041_; size_t v___x_5042_; size_t v___x_5043_; size_t v_h_5044_; lean_object* v___x_5045_; lean_object* v___x_5046_; 
v_k_5035_ = lean_array_fget_borrowed(v_keys_5029_, v_i_5031_);
v_v_5036_ = lean_array_fget_borrowed(v_vals_5030_, v_i_5031_);
v___x_5037_ = l_Lean_instHashableMVarId_hash(v_k_5035_);
v_h_5038_ = lean_uint64_to_usize(v___x_5037_);
v___x_5039_ = ((size_t)5ULL);
v___x_5040_ = lean_unsigned_to_nat(1u);
v___x_5041_ = ((size_t)1ULL);
v___x_5042_ = lean_usize_sub(v_depth_5028_, v___x_5041_);
v___x_5043_ = lean_usize_mul(v___x_5039_, v___x_5042_);
v_h_5044_ = lean_usize_shift_right(v_h_5038_, v___x_5043_);
v___x_5045_ = lean_nat_add(v_i_5031_, v___x_5040_);
lean_dec(v_i_5031_);
lean_inc(v_v_5036_);
lean_inc(v_k_5035_);
v___x_5046_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg(v_entries_5032_, v_h_5044_, v_depth_5028_, v_k_5035_, v_v_5036_);
v_i_5031_ = v___x_5045_;
v_entries_5032_ = v___x_5046_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__8___redArg___boxed(lean_object* v_depth_5048_, lean_object* v_keys_5049_, lean_object* v_vals_5050_, lean_object* v_i_5051_, lean_object* v_entries_5052_){
_start:
{
size_t v_depth_boxed_5053_; lean_object* v_res_5054_; 
v_depth_boxed_5053_ = lean_unbox_usize(v_depth_5048_);
lean_dec(v_depth_5048_);
v_res_5054_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__8___redArg(v_depth_boxed_5053_, v_keys_5049_, v_vals_5050_, v_i_5051_, v_entries_5052_);
lean_dec_ref(v_vals_5050_);
lean_dec_ref(v_keys_5049_);
return v_res_5054_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_x_5055_, lean_object* v_x_5056_, lean_object* v_x_5057_, lean_object* v_x_5058_, lean_object* v_x_5059_){
_start:
{
size_t v_x_48488__boxed_5060_; size_t v_x_48489__boxed_5061_; lean_object* v_res_5062_; 
v_x_48488__boxed_5060_ = lean_unbox_usize(v_x_5056_);
lean_dec(v_x_5056_);
v_x_48489__boxed_5061_ = lean_unbox_usize(v_x_5057_);
lean_dec(v_x_5057_);
v_res_5062_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg(v_x_5055_, v_x_48488__boxed_5060_, v_x_48489__boxed_5061_, v_x_5058_, v_x_5059_);
return v_res_5062_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0___redArg(lean_object* v_x_5063_, lean_object* v_x_5064_, lean_object* v_x_5065_){
_start:
{
uint64_t v___x_5066_; size_t v___x_5067_; size_t v___x_5068_; lean_object* v___x_5069_; 
v___x_5066_ = l_Lean_instHashableMVarId_hash(v_x_5064_);
v___x_5067_ = lean_uint64_to_usize(v___x_5066_);
v___x_5068_ = ((size_t)1ULL);
v___x_5069_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg(v_x_5063_, v___x_5067_, v___x_5068_, v_x_5064_, v_x_5065_);
return v___x_5069_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___redArg(lean_object* v_mvarId_5070_, lean_object* v_val_5071_, lean_object* v___y_5072_){
_start:
{
lean_object* v___x_5074_; lean_object* v_mctx_5075_; lean_object* v_cache_5076_; lean_object* v_zetaDeltaFVarIds_5077_; lean_object* v_postponed_5078_; lean_object* v_diag_5079_; lean_object* v___x_5081_; uint8_t v_isShared_5082_; uint8_t v_isSharedCheck_5107_; 
v___x_5074_ = lean_st_ref_take(v___y_5072_);
v_mctx_5075_ = lean_ctor_get(v___x_5074_, 0);
v_cache_5076_ = lean_ctor_get(v___x_5074_, 1);
v_zetaDeltaFVarIds_5077_ = lean_ctor_get(v___x_5074_, 2);
v_postponed_5078_ = lean_ctor_get(v___x_5074_, 3);
v_diag_5079_ = lean_ctor_get(v___x_5074_, 4);
v_isSharedCheck_5107_ = !lean_is_exclusive(v___x_5074_);
if (v_isSharedCheck_5107_ == 0)
{
v___x_5081_ = v___x_5074_;
v_isShared_5082_ = v_isSharedCheck_5107_;
goto v_resetjp_5080_;
}
else
{
lean_inc(v_diag_5079_);
lean_inc(v_postponed_5078_);
lean_inc(v_zetaDeltaFVarIds_5077_);
lean_inc(v_cache_5076_);
lean_inc(v_mctx_5075_);
lean_dec(v___x_5074_);
v___x_5081_ = lean_box(0);
v_isShared_5082_ = v_isSharedCheck_5107_;
goto v_resetjp_5080_;
}
v_resetjp_5080_:
{
lean_object* v_depth_5083_; lean_object* v_levelAssignDepth_5084_; lean_object* v_lmvarCounter_5085_; lean_object* v_mvarCounter_5086_; lean_object* v_lDecls_5087_; lean_object* v_decls_5088_; lean_object* v_userNames_5089_; lean_object* v_lAssignment_5090_; lean_object* v_eAssignment_5091_; lean_object* v_dAssignment_5092_; lean_object* v___x_5094_; uint8_t v_isShared_5095_; uint8_t v_isSharedCheck_5106_; 
v_depth_5083_ = lean_ctor_get(v_mctx_5075_, 0);
v_levelAssignDepth_5084_ = lean_ctor_get(v_mctx_5075_, 1);
v_lmvarCounter_5085_ = lean_ctor_get(v_mctx_5075_, 2);
v_mvarCounter_5086_ = lean_ctor_get(v_mctx_5075_, 3);
v_lDecls_5087_ = lean_ctor_get(v_mctx_5075_, 4);
v_decls_5088_ = lean_ctor_get(v_mctx_5075_, 5);
v_userNames_5089_ = lean_ctor_get(v_mctx_5075_, 6);
v_lAssignment_5090_ = lean_ctor_get(v_mctx_5075_, 7);
v_eAssignment_5091_ = lean_ctor_get(v_mctx_5075_, 8);
v_dAssignment_5092_ = lean_ctor_get(v_mctx_5075_, 9);
v_isSharedCheck_5106_ = !lean_is_exclusive(v_mctx_5075_);
if (v_isSharedCheck_5106_ == 0)
{
v___x_5094_ = v_mctx_5075_;
v_isShared_5095_ = v_isSharedCheck_5106_;
goto v_resetjp_5093_;
}
else
{
lean_inc(v_dAssignment_5092_);
lean_inc(v_eAssignment_5091_);
lean_inc(v_lAssignment_5090_);
lean_inc(v_userNames_5089_);
lean_inc(v_decls_5088_);
lean_inc(v_lDecls_5087_);
lean_inc(v_mvarCounter_5086_);
lean_inc(v_lmvarCounter_5085_);
lean_inc(v_levelAssignDepth_5084_);
lean_inc(v_depth_5083_);
lean_dec(v_mctx_5075_);
v___x_5094_ = lean_box(0);
v_isShared_5095_ = v_isSharedCheck_5106_;
goto v_resetjp_5093_;
}
v_resetjp_5093_:
{
lean_object* v___x_5096_; lean_object* v___x_5098_; 
v___x_5096_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0___redArg(v_eAssignment_5091_, v_mvarId_5070_, v_val_5071_);
if (v_isShared_5095_ == 0)
{
lean_ctor_set(v___x_5094_, 8, v___x_5096_);
v___x_5098_ = v___x_5094_;
goto v_reusejp_5097_;
}
else
{
lean_object* v_reuseFailAlloc_5105_; 
v_reuseFailAlloc_5105_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5105_, 0, v_depth_5083_);
lean_ctor_set(v_reuseFailAlloc_5105_, 1, v_levelAssignDepth_5084_);
lean_ctor_set(v_reuseFailAlloc_5105_, 2, v_lmvarCounter_5085_);
lean_ctor_set(v_reuseFailAlloc_5105_, 3, v_mvarCounter_5086_);
lean_ctor_set(v_reuseFailAlloc_5105_, 4, v_lDecls_5087_);
lean_ctor_set(v_reuseFailAlloc_5105_, 5, v_decls_5088_);
lean_ctor_set(v_reuseFailAlloc_5105_, 6, v_userNames_5089_);
lean_ctor_set(v_reuseFailAlloc_5105_, 7, v_lAssignment_5090_);
lean_ctor_set(v_reuseFailAlloc_5105_, 8, v___x_5096_);
lean_ctor_set(v_reuseFailAlloc_5105_, 9, v_dAssignment_5092_);
v___x_5098_ = v_reuseFailAlloc_5105_;
goto v_reusejp_5097_;
}
v_reusejp_5097_:
{
lean_object* v___x_5100_; 
if (v_isShared_5082_ == 0)
{
lean_ctor_set(v___x_5081_, 0, v___x_5098_);
v___x_5100_ = v___x_5081_;
goto v_reusejp_5099_;
}
else
{
lean_object* v_reuseFailAlloc_5104_; 
v_reuseFailAlloc_5104_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5104_, 0, v___x_5098_);
lean_ctor_set(v_reuseFailAlloc_5104_, 1, v_cache_5076_);
lean_ctor_set(v_reuseFailAlloc_5104_, 2, v_zetaDeltaFVarIds_5077_);
lean_ctor_set(v_reuseFailAlloc_5104_, 3, v_postponed_5078_);
lean_ctor_set(v_reuseFailAlloc_5104_, 4, v_diag_5079_);
v___x_5100_ = v_reuseFailAlloc_5104_;
goto v_reusejp_5099_;
}
v_reusejp_5099_:
{
lean_object* v___x_5101_; lean_object* v___x_5102_; lean_object* v___x_5103_; 
v___x_5101_ = lean_st_ref_set(v___y_5072_, v___x_5100_);
v___x_5102_ = lean_box(0);
v___x_5103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5103_, 0, v___x_5102_);
return v___x_5103_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___redArg___boxed(lean_object* v_mvarId_5108_, lean_object* v_val_5109_, lean_object* v___y_5110_, lean_object* v___y_5111_){
_start:
{
lean_object* v_res_5112_; 
v_res_5112_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___redArg(v_mvarId_5108_, v_val_5109_, v___y_5110_);
lean_dec(v___y_5110_);
return v_res_5112_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3(lean_object* v_mvarId_5120_, lean_object* v_config_5121_, lean_object* v_as_5122_, size_t v_sz_5123_, size_t v_i_5124_, lean_object* v_b_5125_, lean_object* v___y_5126_, lean_object* v___y_5127_, lean_object* v___y_5128_, lean_object* v___y_5129_, lean_object* v___y_5130_, lean_object* v___y_5131_){
_start:
{
lean_object* v_a_5134_; uint8_t v___x_5138_; 
v___x_5138_ = lean_usize_dec_lt(v_i_5124_, v_sz_5123_);
if (v___x_5138_ == 0)
{
lean_object* v___x_5139_; 
lean_dec_ref(v_config_5121_);
lean_dec(v_mvarId_5120_);
v___x_5139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5139_, 0, v_b_5125_);
return v___x_5139_;
}
else
{
lean_object* v_a_5140_; lean_object* v___x_5141_; 
v_a_5140_ = lean_array_uget_borrowed(v_as_5122_, v_i_5124_);
lean_inc(v_a_5140_);
v___x_5141_ = l_Lean_FVarId_getDecl___redArg(v_a_5140_, v___y_5128_, v___y_5130_, v___y_5131_);
if (lean_obj_tag(v___x_5141_) == 0)
{
lean_object* v_options_5142_; lean_object* v_a_5143_; lean_object* v_snd_5144_; lean_object* v___x_5146_; uint8_t v_isShared_5147_; uint8_t v_isSharedCheck_5341_; 
v_options_5142_ = lean_ctor_get(v___y_5130_, 2);
v_a_5143_ = lean_ctor_get(v___x_5141_, 0);
lean_inc(v_a_5143_);
lean_dec_ref_known(v___x_5141_, 1);
v_snd_5144_ = lean_ctor_get(v_b_5125_, 1);
v_isSharedCheck_5341_ = !lean_is_exclusive(v_b_5125_);
if (v_isSharedCheck_5341_ == 0)
{
lean_object* v_unused_5342_; 
v_unused_5342_ = lean_ctor_get(v_b_5125_, 0);
lean_dec(v_unused_5342_);
v___x_5146_ = v_b_5125_;
v_isShared_5147_ = v_isSharedCheck_5341_;
goto v_resetjp_5145_;
}
else
{
lean_inc(v_snd_5144_);
lean_dec(v_b_5125_);
v___x_5146_ = lean_box(0);
v_isShared_5147_ = v_isSharedCheck_5341_;
goto v_resetjp_5145_;
}
v_resetjp_5145_:
{
lean_object* v_inheritedTraceOptions_5148_; uint8_t v_hasTrace_5149_; lean_object* v___x_5150_; lean_object* v___x_5151_; lean_object* v___y_5153_; uint8_t v___x_5250_; 
v_inheritedTraceOptions_5148_ = lean_ctor_get(v___y_5130_, 13);
v_hasTrace_5149_ = lean_ctor_get_uint8(v_options_5142_, sizeof(void*)*1);
v___x_5150_ = lean_box(0);
v___x_5151_ = l_Lean_LocalDecl_type(v_a_5143_);
v___x_5250_ = lean_bool_not(v_hasTrace_5149_);
if (v___x_5250_ == 0)
{
lean_object* v___f_5251_; lean_object* v___x_5252_; lean_object* v___x_5253_; lean_object* v___y_5255_; uint8_t v___y_5256_; lean_object* v___y_5257_; lean_object* v_a_5258_; uint8_t v___y_5271_; lean_object* v___y_5272_; lean_object* v___y_5273_; lean_object* v_a_5274_; uint8_t v___y_5284_; uint8_t v_a_5334_; 
lean_inc_ref(v___x_5151_);
lean_inc(v_a_5143_);
v___f_5251_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___boxed), 10, 2);
lean_closure_set(v___f_5251_, 0, v_a_5143_);
lean_closure_set(v___f_5251_, 1, v___x_5151_);
v___x_5252_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0));
v___x_5253_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__1));
if (v_hasTrace_5149_ == 0)
{
v_a_5334_ = v_hasTrace_5149_;
goto v___jp_5333_;
}
else
{
lean_object* v___x_5338_; uint8_t v___x_5339_; 
v___x_5338_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1);
v___x_5339_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5148_, v_options_5142_, v___x_5338_);
if (v___x_5339_ == 0)
{
v_a_5334_ = v___x_5339_;
goto v___jp_5333_;
}
else
{
v___y_5284_ = v___x_5339_;
goto v___jp_5283_;
}
}
v___jp_5254_:
{
lean_object* v___x_5259_; double v___x_5260_; double v___x_5261_; double v___x_5262_; double v___x_5263_; double v___x_5264_; lean_object* v___x_5265_; lean_object* v___x_5266_; lean_object* v___x_5267_; lean_object* v___x_5268_; lean_object* v___x_5269_; 
v___x_5259_ = lean_io_mono_nanos_now();
v___x_5260_ = lean_float_of_nat(v___y_5255_);
v___x_5261_ = lean_float_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9);
v___x_5262_ = lean_float_div(v___x_5260_, v___x_5261_);
v___x_5263_ = lean_float_of_nat(v___x_5259_);
v___x_5264_ = lean_float_div(v___x_5263_, v___x_5261_);
v___x_5265_ = lean_box_float(v___x_5262_);
v___x_5266_ = lean_box_float(v___x_5264_);
v___x_5267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5267_, 0, v___x_5265_);
lean_ctor_set(v___x_5267_, 1, v___x_5266_);
v___x_5268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5268_, 0, v_a_5258_);
lean_ctor_set(v___x_5268_, 1, v___x_5267_);
v___x_5269_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2(v___x_5252_, v___x_5138_, v___x_5253_, v_options_5142_, v___y_5256_, v___y_5257_, v___f_5251_, v___x_5268_, v___y_5126_, v___y_5127_, v___y_5128_, v___y_5129_, v___y_5130_, v___y_5131_);
v___y_5153_ = v___x_5269_;
goto v___jp_5152_;
}
v___jp_5270_:
{
lean_object* v___x_5275_; double v___x_5276_; double v___x_5277_; lean_object* v___x_5278_; lean_object* v___x_5279_; lean_object* v___x_5280_; lean_object* v___x_5281_; lean_object* v___x_5282_; 
v___x_5275_ = lean_io_get_num_heartbeats();
v___x_5276_ = lean_float_of_nat(v___y_5272_);
v___x_5277_ = lean_float_of_nat(v___x_5275_);
v___x_5278_ = lean_box_float(v___x_5276_);
v___x_5279_ = lean_box_float(v___x_5277_);
v___x_5280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5280_, 0, v___x_5278_);
lean_ctor_set(v___x_5280_, 1, v___x_5279_);
v___x_5281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5281_, 0, v_a_5274_);
lean_ctor_set(v___x_5281_, 1, v___x_5280_);
v___x_5282_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2(v___x_5252_, v___x_5138_, v___x_5253_, v_options_5142_, v___y_5271_, v___y_5273_, v___f_5251_, v___x_5281_, v___y_5126_, v___y_5127_, v___y_5128_, v___y_5129_, v___y_5130_, v___y_5131_);
v___y_5153_ = v___x_5282_;
goto v___jp_5152_;
}
v___jp_5283_:
{
lean_object* v___x_5285_; 
v___x_5285_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1___redArg(v___y_5131_);
if (lean_obj_tag(v___x_5285_) == 0)
{
lean_object* v_a_5286_; lean_object* v___x_5287_; uint8_t v___x_5288_; 
v_a_5286_ = lean_ctor_get(v___x_5285_, 0);
lean_inc(v_a_5286_);
lean_dec_ref_known(v___x_5285_, 1);
v___x_5287_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5288_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_5142_, v___x_5287_);
if (v___x_5288_ == 0)
{
lean_object* v___x_5289_; lean_object* v___x_5290_; 
v___x_5289_ = lean_io_mono_nanos_now();
lean_inc_ref(v_config_5121_);
lean_inc_ref(v___x_5151_);
v___x_5290_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_5151_, v_config_5121_, v___y_5126_, v___y_5127_, v___y_5128_, v___y_5129_, v___y_5130_, v___y_5131_);
if (lean_obj_tag(v___x_5290_) == 0)
{
lean_object* v_a_5291_; lean_object* v___x_5293_; uint8_t v_isShared_5294_; uint8_t v_isSharedCheck_5298_; 
v_a_5291_ = lean_ctor_get(v___x_5290_, 0);
v_isSharedCheck_5298_ = !lean_is_exclusive(v___x_5290_);
if (v_isSharedCheck_5298_ == 0)
{
v___x_5293_ = v___x_5290_;
v_isShared_5294_ = v_isSharedCheck_5298_;
goto v_resetjp_5292_;
}
else
{
lean_inc(v_a_5291_);
lean_dec(v___x_5290_);
v___x_5293_ = lean_box(0);
v_isShared_5294_ = v_isSharedCheck_5298_;
goto v_resetjp_5292_;
}
v_resetjp_5292_:
{
lean_object* v___x_5296_; 
if (v_isShared_5294_ == 0)
{
lean_ctor_set_tag(v___x_5293_, 1);
v___x_5296_ = v___x_5293_;
goto v_reusejp_5295_;
}
else
{
lean_object* v_reuseFailAlloc_5297_; 
v_reuseFailAlloc_5297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5297_, 0, v_a_5291_);
v___x_5296_ = v_reuseFailAlloc_5297_;
goto v_reusejp_5295_;
}
v_reusejp_5295_:
{
v___y_5255_ = v___x_5289_;
v___y_5256_ = v___y_5284_;
v___y_5257_ = v_a_5286_;
v_a_5258_ = v___x_5296_;
goto v___jp_5254_;
}
}
}
else
{
lean_object* v_a_5299_; lean_object* v___x_5301_; uint8_t v_isShared_5302_; uint8_t v_isSharedCheck_5306_; 
v_a_5299_ = lean_ctor_get(v___x_5290_, 0);
v_isSharedCheck_5306_ = !lean_is_exclusive(v___x_5290_);
if (v_isSharedCheck_5306_ == 0)
{
v___x_5301_ = v___x_5290_;
v_isShared_5302_ = v_isSharedCheck_5306_;
goto v_resetjp_5300_;
}
else
{
lean_inc(v_a_5299_);
lean_dec(v___x_5290_);
v___x_5301_ = lean_box(0);
v_isShared_5302_ = v_isSharedCheck_5306_;
goto v_resetjp_5300_;
}
v_resetjp_5300_:
{
lean_object* v___x_5304_; 
if (v_isShared_5302_ == 0)
{
lean_ctor_set_tag(v___x_5301_, 0);
v___x_5304_ = v___x_5301_;
goto v_reusejp_5303_;
}
else
{
lean_object* v_reuseFailAlloc_5305_; 
v_reuseFailAlloc_5305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5305_, 0, v_a_5299_);
v___x_5304_ = v_reuseFailAlloc_5305_;
goto v_reusejp_5303_;
}
v_reusejp_5303_:
{
v___y_5255_ = v___x_5289_;
v___y_5256_ = v___y_5284_;
v___y_5257_ = v_a_5286_;
v_a_5258_ = v___x_5304_;
goto v___jp_5254_;
}
}
}
}
else
{
lean_object* v___x_5307_; lean_object* v___x_5308_; 
v___x_5307_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_config_5121_);
lean_inc_ref(v___x_5151_);
v___x_5308_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_5151_, v_config_5121_, v___y_5126_, v___y_5127_, v___y_5128_, v___y_5129_, v___y_5130_, v___y_5131_);
if (lean_obj_tag(v___x_5308_) == 0)
{
lean_object* v_a_5309_; lean_object* v___x_5311_; uint8_t v_isShared_5312_; uint8_t v_isSharedCheck_5316_; 
v_a_5309_ = lean_ctor_get(v___x_5308_, 0);
v_isSharedCheck_5316_ = !lean_is_exclusive(v___x_5308_);
if (v_isSharedCheck_5316_ == 0)
{
v___x_5311_ = v___x_5308_;
v_isShared_5312_ = v_isSharedCheck_5316_;
goto v_resetjp_5310_;
}
else
{
lean_inc(v_a_5309_);
lean_dec(v___x_5308_);
v___x_5311_ = lean_box(0);
v_isShared_5312_ = v_isSharedCheck_5316_;
goto v_resetjp_5310_;
}
v_resetjp_5310_:
{
lean_object* v___x_5314_; 
if (v_isShared_5312_ == 0)
{
lean_ctor_set_tag(v___x_5311_, 1);
v___x_5314_ = v___x_5311_;
goto v_reusejp_5313_;
}
else
{
lean_object* v_reuseFailAlloc_5315_; 
v_reuseFailAlloc_5315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5315_, 0, v_a_5309_);
v___x_5314_ = v_reuseFailAlloc_5315_;
goto v_reusejp_5313_;
}
v_reusejp_5313_:
{
v___y_5271_ = v___y_5284_;
v___y_5272_ = v___x_5307_;
v___y_5273_ = v_a_5286_;
v_a_5274_ = v___x_5314_;
goto v___jp_5270_;
}
}
}
else
{
lean_object* v_a_5317_; lean_object* v___x_5319_; uint8_t v_isShared_5320_; uint8_t v_isSharedCheck_5324_; 
v_a_5317_ = lean_ctor_get(v___x_5308_, 0);
v_isSharedCheck_5324_ = !lean_is_exclusive(v___x_5308_);
if (v_isSharedCheck_5324_ == 0)
{
v___x_5319_ = v___x_5308_;
v_isShared_5320_ = v_isSharedCheck_5324_;
goto v_resetjp_5318_;
}
else
{
lean_inc(v_a_5317_);
lean_dec(v___x_5308_);
v___x_5319_ = lean_box(0);
v_isShared_5320_ = v_isSharedCheck_5324_;
goto v_resetjp_5318_;
}
v_resetjp_5318_:
{
lean_object* v___x_5322_; 
if (v_isShared_5320_ == 0)
{
lean_ctor_set_tag(v___x_5319_, 0);
v___x_5322_ = v___x_5319_;
goto v_reusejp_5321_;
}
else
{
lean_object* v_reuseFailAlloc_5323_; 
v_reuseFailAlloc_5323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5323_, 0, v_a_5317_);
v___x_5322_ = v_reuseFailAlloc_5323_;
goto v_reusejp_5321_;
}
v_reusejp_5321_:
{
v___y_5271_ = v___y_5284_;
v___y_5272_ = v___x_5307_;
v___y_5273_ = v_a_5286_;
v_a_5274_ = v___x_5322_;
goto v___jp_5270_;
}
}
}
}
}
else
{
lean_object* v_a_5325_; lean_object* v___x_5327_; uint8_t v_isShared_5328_; uint8_t v_isSharedCheck_5332_; 
lean_dec_ref(v___f_5251_);
lean_dec_ref(v___x_5151_);
lean_del_object(v___x_5146_);
lean_dec(v_snd_5144_);
lean_dec(v_a_5143_);
lean_dec_ref(v_config_5121_);
lean_dec(v_mvarId_5120_);
v_a_5325_ = lean_ctor_get(v___x_5285_, 0);
v_isSharedCheck_5332_ = !lean_is_exclusive(v___x_5285_);
if (v_isSharedCheck_5332_ == 0)
{
v___x_5327_ = v___x_5285_;
v_isShared_5328_ = v_isSharedCheck_5332_;
goto v_resetjp_5326_;
}
else
{
lean_inc(v_a_5325_);
lean_dec(v___x_5285_);
v___x_5327_ = lean_box(0);
v_isShared_5328_ = v_isSharedCheck_5332_;
goto v_resetjp_5326_;
}
v_resetjp_5326_:
{
lean_object* v___x_5330_; 
if (v_isShared_5328_ == 0)
{
v___x_5330_ = v___x_5327_;
goto v_reusejp_5329_;
}
else
{
lean_object* v_reuseFailAlloc_5331_; 
v_reuseFailAlloc_5331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5331_, 0, v_a_5325_);
v___x_5330_ = v_reuseFailAlloc_5331_;
goto v_reusejp_5329_;
}
v_reusejp_5329_:
{
return v___x_5330_;
}
}
}
}
v___jp_5333_:
{
lean_object* v___x_5335_; uint8_t v___x_5336_; 
v___x_5335_ = l_Lean_trace_profiler;
v___x_5336_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_5142_, v___x_5335_);
if (v___x_5336_ == 0)
{
lean_object* v___x_5337_; 
lean_dec_ref(v___f_5251_);
lean_inc_ref(v_config_5121_);
lean_inc_ref(v___x_5151_);
v___x_5337_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_5151_, v_config_5121_, v___y_5126_, v___y_5127_, v___y_5128_, v___y_5129_, v___y_5130_, v___y_5131_);
v___y_5153_ = v___x_5337_;
goto v___jp_5152_;
}
else
{
v___y_5284_ = v_a_5334_;
goto v___jp_5283_;
}
}
}
else
{
lean_object* v___x_5340_; 
lean_inc_ref(v_config_5121_);
lean_inc_ref(v___x_5151_);
v___x_5340_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_5151_, v_config_5121_, v___y_5126_, v___y_5127_, v___y_5128_, v___y_5129_, v___y_5130_, v___y_5131_);
v___y_5153_ = v___x_5340_;
goto v___jp_5152_;
}
v___jp_5152_:
{
if (lean_obj_tag(v___y_5153_) == 0)
{
lean_object* v_a_5154_; 
v_a_5154_ = lean_ctor_get(v___y_5153_, 0);
lean_inc(v_a_5154_);
lean_dec_ref_known(v___y_5153_, 1);
if (lean_obj_tag(v_a_5154_) == 0)
{
lean_object* v___x_5156_; 
lean_dec_ref_known(v_a_5154_, 0);
lean_dec_ref(v___x_5151_);
lean_dec(v_a_5143_);
if (v_isShared_5147_ == 0)
{
lean_ctor_set(v___x_5146_, 0, v___x_5150_);
v___x_5156_ = v___x_5146_;
goto v_reusejp_5155_;
}
else
{
lean_object* v_reuseFailAlloc_5157_; 
v_reuseFailAlloc_5157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5157_, 0, v___x_5150_);
lean_ctor_set(v_reuseFailAlloc_5157_, 1, v_snd_5144_);
v___x_5156_ = v_reuseFailAlloc_5157_;
goto v_reusejp_5155_;
}
v_reusejp_5155_:
{
v_a_5134_ = v___x_5156_;
goto v___jp_5133_;
}
}
else
{
lean_object* v_e_x27_5158_; lean_object* v_proof_5159_; uint8_t v___x_5160_; 
v_e_x27_5158_ = lean_ctor_get(v_a_5154_, 0);
lean_inc_ref_n(v_e_x27_5158_, 2);
v_proof_5159_ = lean_ctor_get(v_a_5154_, 1);
lean_inc_ref(v_proof_5159_);
lean_dec_ref_known(v_a_5154_, 2);
v___x_5160_ = l_Lean_Expr_isFalse(v_e_x27_5158_);
if (v___x_5160_ == 0)
{
lean_object* v___x_5161_; 
lean_inc_ref(v___x_5151_);
v___x_5161_ = l_Lean_Meta_Sym_getLevel___redArg(v___x_5151_, v___y_5127_, v___y_5128_, v___y_5129_, v___y_5130_, v___y_5131_);
if (lean_obj_tag(v___x_5161_) == 0)
{
lean_object* v_a_5162_; lean_object* v___x_5163_; lean_object* v___x_5164_; lean_object* v___x_5165_; lean_object* v___x_5166_; lean_object* v___x_5167_; lean_object* v___x_5168_; lean_object* v___x_5169_; uint8_t v___x_5170_; uint8_t v___x_5171_; lean_object* v___x_5172_; lean_object* v___x_5173_; lean_object* v___x_5175_; 
v_a_5162_ = lean_ctor_get(v___x_5161_, 0);
lean_inc(v_a_5162_);
lean_dec_ref_known(v___x_5161_, 1);
v___x_5163_ = l_Lean_LocalDecl_userName(v_a_5143_);
lean_dec(v_a_5143_);
v___x_5164_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___closed__2));
v___x_5165_ = lean_box(0);
v___x_5166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5166_, 0, v_a_5162_);
lean_ctor_set(v___x_5166_, 1, v___x_5165_);
v___x_5167_ = l_Lean_mkConst(v___x_5164_, v___x_5166_);
lean_inc(v_a_5140_);
v___x_5168_ = l_Lean_mkFVar(v_a_5140_);
lean_inc_ref(v_e_x27_5158_);
v___x_5169_ = l_Lean_mkApp4(v___x_5167_, v___x_5151_, v_e_x27_5158_, v_proof_5159_, v___x_5168_);
v___x_5170_ = 0;
v___x_5171_ = 0;
v___x_5172_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5172_, 0, v___x_5163_);
lean_ctor_set(v___x_5172_, 1, v_e_x27_5158_);
lean_ctor_set(v___x_5172_, 2, v___x_5169_);
lean_ctor_set_uint8(v___x_5172_, sizeof(void*)*3, v___x_5170_);
lean_ctor_set_uint8(v___x_5172_, sizeof(void*)*3 + 1, v___x_5171_);
v___x_5173_ = lean_array_push(v_snd_5144_, v___x_5172_);
if (v_isShared_5147_ == 0)
{
lean_ctor_set(v___x_5146_, 1, v___x_5173_);
lean_ctor_set(v___x_5146_, 0, v___x_5150_);
v___x_5175_ = v___x_5146_;
goto v_reusejp_5174_;
}
else
{
lean_object* v_reuseFailAlloc_5176_; 
v_reuseFailAlloc_5176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5176_, 0, v___x_5150_);
lean_ctor_set(v_reuseFailAlloc_5176_, 1, v___x_5173_);
v___x_5175_ = v_reuseFailAlloc_5176_;
goto v_reusejp_5174_;
}
v_reusejp_5174_:
{
v_a_5134_ = v___x_5175_;
goto v___jp_5133_;
}
}
else
{
lean_object* v_a_5177_; lean_object* v___x_5179_; uint8_t v_isShared_5180_; uint8_t v_isSharedCheck_5184_; 
lean_dec_ref(v_proof_5159_);
lean_dec_ref(v_e_x27_5158_);
lean_dec_ref(v___x_5151_);
lean_del_object(v___x_5146_);
lean_dec(v_snd_5144_);
lean_dec(v_a_5143_);
lean_dec_ref(v_config_5121_);
lean_dec(v_mvarId_5120_);
v_a_5177_ = lean_ctor_get(v___x_5161_, 0);
v_isSharedCheck_5184_ = !lean_is_exclusive(v___x_5161_);
if (v_isSharedCheck_5184_ == 0)
{
v___x_5179_ = v___x_5161_;
v_isShared_5180_ = v_isSharedCheck_5184_;
goto v_resetjp_5178_;
}
else
{
lean_inc(v_a_5177_);
lean_dec(v___x_5161_);
v___x_5179_ = lean_box(0);
v_isShared_5180_ = v_isSharedCheck_5184_;
goto v_resetjp_5178_;
}
v_resetjp_5178_:
{
lean_object* v___x_5182_; 
if (v_isShared_5180_ == 0)
{
v___x_5182_ = v___x_5179_;
goto v_reusejp_5181_;
}
else
{
lean_object* v_reuseFailAlloc_5183_; 
v_reuseFailAlloc_5183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5183_, 0, v_a_5177_);
v___x_5182_ = v_reuseFailAlloc_5183_;
goto v_reusejp_5181_;
}
v_reusejp_5181_:
{
return v___x_5182_;
}
}
}
}
else
{
lean_object* v___x_5185_; 
lean_dec(v_a_5143_);
lean_dec_ref(v_config_5121_);
lean_inc_ref(v___x_5151_);
v___x_5185_ = l_Lean_Meta_Sym_getLevel___redArg(v___x_5151_, v___y_5127_, v___y_5128_, v___y_5129_, v___y_5130_, v___y_5131_);
if (lean_obj_tag(v___x_5185_) == 0)
{
lean_object* v_a_5186_; lean_object* v___x_5187_; 
v_a_5186_ = lean_ctor_get(v___x_5185_, 0);
lean_inc(v_a_5186_);
lean_dec_ref_known(v___x_5185_, 1);
lean_inc(v_mvarId_5120_);
v___x_5187_ = l_Lean_MVarId_getType(v_mvarId_5120_, v___y_5128_, v___y_5129_, v___y_5130_, v___y_5131_);
if (lean_obj_tag(v___x_5187_) == 0)
{
lean_object* v_a_5188_; lean_object* v___x_5189_; lean_object* v___x_5190_; lean_object* v___x_5191_; lean_object* v___x_5192_; lean_object* v___x_5193_; lean_object* v___x_5194_; lean_object* v___x_5195_; 
v_a_5188_ = lean_ctor_get(v___x_5187_, 0);
lean_inc(v_a_5188_);
lean_dec_ref_known(v___x_5187_, 1);
v___x_5189_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___closed__2));
v___x_5190_ = lean_box(0);
v___x_5191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5191_, 0, v_a_5186_);
lean_ctor_set(v___x_5191_, 1, v___x_5190_);
v___x_5192_ = l_Lean_mkConst(v___x_5189_, v___x_5191_);
lean_inc(v_a_5140_);
v___x_5193_ = l_Lean_mkFVar(v_a_5140_);
v___x_5194_ = l_Lean_mkApp4(v___x_5192_, v___x_5151_, v_e_x27_5158_, v_proof_5159_, v___x_5193_);
v___x_5195_ = l_Lean_Meta_mkFalseElim(v_a_5188_, v___x_5194_, v___y_5128_, v___y_5129_, v___y_5130_, v___y_5131_);
if (lean_obj_tag(v___x_5195_) == 0)
{
lean_object* v_a_5196_; lean_object* v___x_5197_; 
v_a_5196_ = lean_ctor_get(v___x_5195_, 0);
lean_inc(v_a_5196_);
lean_dec_ref_known(v___x_5195_, 1);
v___x_5197_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___redArg(v_mvarId_5120_, v_a_5196_, v___y_5129_);
if (lean_obj_tag(v___x_5197_) == 0)
{
lean_object* v___x_5199_; uint8_t v_isShared_5200_; uint8_t v_isSharedCheck_5208_; 
v_isSharedCheck_5208_ = !lean_is_exclusive(v___x_5197_);
if (v_isSharedCheck_5208_ == 0)
{
lean_object* v_unused_5209_; 
v_unused_5209_ = lean_ctor_get(v___x_5197_, 0);
lean_dec(v_unused_5209_);
v___x_5199_ = v___x_5197_;
v_isShared_5200_ = v_isSharedCheck_5208_;
goto v_resetjp_5198_;
}
else
{
lean_dec(v___x_5197_);
v___x_5199_ = lean_box(0);
v_isShared_5200_ = v_isSharedCheck_5208_;
goto v_resetjp_5198_;
}
v_resetjp_5198_:
{
lean_object* v___x_5201_; lean_object* v___x_5203_; 
v___x_5201_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___closed__3));
if (v_isShared_5147_ == 0)
{
lean_ctor_set(v___x_5146_, 0, v___x_5201_);
v___x_5203_ = v___x_5146_;
goto v_reusejp_5202_;
}
else
{
lean_object* v_reuseFailAlloc_5207_; 
v_reuseFailAlloc_5207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5207_, 0, v___x_5201_);
lean_ctor_set(v_reuseFailAlloc_5207_, 1, v_snd_5144_);
v___x_5203_ = v_reuseFailAlloc_5207_;
goto v_reusejp_5202_;
}
v_reusejp_5202_:
{
lean_object* v___x_5205_; 
if (v_isShared_5200_ == 0)
{
lean_ctor_set(v___x_5199_, 0, v___x_5203_);
v___x_5205_ = v___x_5199_;
goto v_reusejp_5204_;
}
else
{
lean_object* v_reuseFailAlloc_5206_; 
v_reuseFailAlloc_5206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5206_, 0, v___x_5203_);
v___x_5205_ = v_reuseFailAlloc_5206_;
goto v_reusejp_5204_;
}
v_reusejp_5204_:
{
return v___x_5205_;
}
}
}
}
else
{
lean_object* v_a_5210_; lean_object* v___x_5212_; uint8_t v_isShared_5213_; uint8_t v_isSharedCheck_5217_; 
lean_del_object(v___x_5146_);
lean_dec(v_snd_5144_);
v_a_5210_ = lean_ctor_get(v___x_5197_, 0);
v_isSharedCheck_5217_ = !lean_is_exclusive(v___x_5197_);
if (v_isSharedCheck_5217_ == 0)
{
v___x_5212_ = v___x_5197_;
v_isShared_5213_ = v_isSharedCheck_5217_;
goto v_resetjp_5211_;
}
else
{
lean_inc(v_a_5210_);
lean_dec(v___x_5197_);
v___x_5212_ = lean_box(0);
v_isShared_5213_ = v_isSharedCheck_5217_;
goto v_resetjp_5211_;
}
v_resetjp_5211_:
{
lean_object* v___x_5215_; 
if (v_isShared_5213_ == 0)
{
v___x_5215_ = v___x_5212_;
goto v_reusejp_5214_;
}
else
{
lean_object* v_reuseFailAlloc_5216_; 
v_reuseFailAlloc_5216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5216_, 0, v_a_5210_);
v___x_5215_ = v_reuseFailAlloc_5216_;
goto v_reusejp_5214_;
}
v_reusejp_5214_:
{
return v___x_5215_;
}
}
}
}
else
{
lean_object* v_a_5218_; lean_object* v___x_5220_; uint8_t v_isShared_5221_; uint8_t v_isSharedCheck_5225_; 
lean_del_object(v___x_5146_);
lean_dec(v_snd_5144_);
lean_dec(v_mvarId_5120_);
v_a_5218_ = lean_ctor_get(v___x_5195_, 0);
v_isSharedCheck_5225_ = !lean_is_exclusive(v___x_5195_);
if (v_isSharedCheck_5225_ == 0)
{
v___x_5220_ = v___x_5195_;
v_isShared_5221_ = v_isSharedCheck_5225_;
goto v_resetjp_5219_;
}
else
{
lean_inc(v_a_5218_);
lean_dec(v___x_5195_);
v___x_5220_ = lean_box(0);
v_isShared_5221_ = v_isSharedCheck_5225_;
goto v_resetjp_5219_;
}
v_resetjp_5219_:
{
lean_object* v___x_5223_; 
if (v_isShared_5221_ == 0)
{
v___x_5223_ = v___x_5220_;
goto v_reusejp_5222_;
}
else
{
lean_object* v_reuseFailAlloc_5224_; 
v_reuseFailAlloc_5224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5224_, 0, v_a_5218_);
v___x_5223_ = v_reuseFailAlloc_5224_;
goto v_reusejp_5222_;
}
v_reusejp_5222_:
{
return v___x_5223_;
}
}
}
}
else
{
lean_object* v_a_5226_; lean_object* v___x_5228_; uint8_t v_isShared_5229_; uint8_t v_isSharedCheck_5233_; 
lean_dec(v_a_5186_);
lean_dec_ref(v_proof_5159_);
lean_dec_ref(v_e_x27_5158_);
lean_dec_ref(v___x_5151_);
lean_del_object(v___x_5146_);
lean_dec(v_snd_5144_);
lean_dec(v_mvarId_5120_);
v_a_5226_ = lean_ctor_get(v___x_5187_, 0);
v_isSharedCheck_5233_ = !lean_is_exclusive(v___x_5187_);
if (v_isSharedCheck_5233_ == 0)
{
v___x_5228_ = v___x_5187_;
v_isShared_5229_ = v_isSharedCheck_5233_;
goto v_resetjp_5227_;
}
else
{
lean_inc(v_a_5226_);
lean_dec(v___x_5187_);
v___x_5228_ = lean_box(0);
v_isShared_5229_ = v_isSharedCheck_5233_;
goto v_resetjp_5227_;
}
v_resetjp_5227_:
{
lean_object* v___x_5231_; 
if (v_isShared_5229_ == 0)
{
v___x_5231_ = v___x_5228_;
goto v_reusejp_5230_;
}
else
{
lean_object* v_reuseFailAlloc_5232_; 
v_reuseFailAlloc_5232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5232_, 0, v_a_5226_);
v___x_5231_ = v_reuseFailAlloc_5232_;
goto v_reusejp_5230_;
}
v_reusejp_5230_:
{
return v___x_5231_;
}
}
}
}
else
{
lean_object* v_a_5234_; lean_object* v___x_5236_; uint8_t v_isShared_5237_; uint8_t v_isSharedCheck_5241_; 
lean_dec_ref(v_proof_5159_);
lean_dec_ref(v_e_x27_5158_);
lean_dec_ref(v___x_5151_);
lean_del_object(v___x_5146_);
lean_dec(v_snd_5144_);
lean_dec(v_mvarId_5120_);
v_a_5234_ = lean_ctor_get(v___x_5185_, 0);
v_isSharedCheck_5241_ = !lean_is_exclusive(v___x_5185_);
if (v_isSharedCheck_5241_ == 0)
{
v___x_5236_ = v___x_5185_;
v_isShared_5237_ = v_isSharedCheck_5241_;
goto v_resetjp_5235_;
}
else
{
lean_inc(v_a_5234_);
lean_dec(v___x_5185_);
v___x_5236_ = lean_box(0);
v_isShared_5237_ = v_isSharedCheck_5241_;
goto v_resetjp_5235_;
}
v_resetjp_5235_:
{
lean_object* v___x_5239_; 
if (v_isShared_5237_ == 0)
{
v___x_5239_ = v___x_5236_;
goto v_reusejp_5238_;
}
else
{
lean_object* v_reuseFailAlloc_5240_; 
v_reuseFailAlloc_5240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5240_, 0, v_a_5234_);
v___x_5239_ = v_reuseFailAlloc_5240_;
goto v_reusejp_5238_;
}
v_reusejp_5238_:
{
return v___x_5239_;
}
}
}
}
}
}
else
{
lean_object* v_a_5242_; lean_object* v___x_5244_; uint8_t v_isShared_5245_; uint8_t v_isSharedCheck_5249_; 
lean_dec_ref(v___x_5151_);
lean_del_object(v___x_5146_);
lean_dec(v_snd_5144_);
lean_dec(v_a_5143_);
lean_dec_ref(v_config_5121_);
lean_dec(v_mvarId_5120_);
v_a_5242_ = lean_ctor_get(v___y_5153_, 0);
v_isSharedCheck_5249_ = !lean_is_exclusive(v___y_5153_);
if (v_isSharedCheck_5249_ == 0)
{
v___x_5244_ = v___y_5153_;
v_isShared_5245_ = v_isSharedCheck_5249_;
goto v_resetjp_5243_;
}
else
{
lean_inc(v_a_5242_);
lean_dec(v___y_5153_);
v___x_5244_ = lean_box(0);
v_isShared_5245_ = v_isSharedCheck_5249_;
goto v_resetjp_5243_;
}
v_resetjp_5243_:
{
lean_object* v___x_5247_; 
if (v_isShared_5245_ == 0)
{
v___x_5247_ = v___x_5244_;
goto v_reusejp_5246_;
}
else
{
lean_object* v_reuseFailAlloc_5248_; 
v_reuseFailAlloc_5248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5248_, 0, v_a_5242_);
v___x_5247_ = v_reuseFailAlloc_5248_;
goto v_reusejp_5246_;
}
v_reusejp_5246_:
{
return v___x_5247_;
}
}
}
}
}
}
else
{
lean_object* v_a_5343_; lean_object* v___x_5345_; uint8_t v_isShared_5346_; uint8_t v_isSharedCheck_5350_; 
lean_dec_ref(v_b_5125_);
lean_dec_ref(v_config_5121_);
lean_dec(v_mvarId_5120_);
v_a_5343_ = lean_ctor_get(v___x_5141_, 0);
v_isSharedCheck_5350_ = !lean_is_exclusive(v___x_5141_);
if (v_isSharedCheck_5350_ == 0)
{
v___x_5345_ = v___x_5141_;
v_isShared_5346_ = v_isSharedCheck_5350_;
goto v_resetjp_5344_;
}
else
{
lean_inc(v_a_5343_);
lean_dec(v___x_5141_);
v___x_5345_ = lean_box(0);
v_isShared_5346_ = v_isSharedCheck_5350_;
goto v_resetjp_5344_;
}
v_resetjp_5344_:
{
lean_object* v___x_5348_; 
if (v_isShared_5346_ == 0)
{
v___x_5348_ = v___x_5345_;
goto v_reusejp_5347_;
}
else
{
lean_object* v_reuseFailAlloc_5349_; 
v_reuseFailAlloc_5349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5349_, 0, v_a_5343_);
v___x_5348_ = v_reuseFailAlloc_5349_;
goto v_reusejp_5347_;
}
v_reusejp_5347_:
{
return v___x_5348_;
}
}
}
}
v___jp_5133_:
{
size_t v___x_5135_; size_t v___x_5136_; 
v___x_5135_ = ((size_t)1ULL);
v___x_5136_ = lean_usize_add(v_i_5124_, v___x_5135_);
v_i_5124_ = v___x_5136_;
v_b_5125_ = v_a_5134_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___boxed(lean_object* v_mvarId_5351_, lean_object* v_config_5352_, lean_object* v_as_5353_, lean_object* v_sz_5354_, lean_object* v_i_5355_, lean_object* v_b_5356_, lean_object* v___y_5357_, lean_object* v___y_5358_, lean_object* v___y_5359_, lean_object* v___y_5360_, lean_object* v___y_5361_, lean_object* v___y_5362_, lean_object* v___y_5363_){
_start:
{
size_t v_sz_boxed_5364_; size_t v_i_boxed_5365_; lean_object* v_res_5366_; 
v_sz_boxed_5364_ = lean_unbox_usize(v_sz_5354_);
lean_dec(v_sz_5354_);
v_i_boxed_5365_ = lean_unbox_usize(v_i_5355_);
lean_dec(v_i_5355_);
v_res_5366_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3(v_mvarId_5351_, v_config_5352_, v_as_5353_, v_sz_boxed_5364_, v_i_boxed_5365_, v_b_5356_, v___y_5357_, v___y_5358_, v___y_5359_, v___y_5360_, v___y_5361_, v___y_5362_);
lean_dec(v___y_5362_);
lean_dec_ref(v___y_5361_);
lean_dec(v___y_5360_);
lean_dec_ref(v___y_5359_);
lean_dec(v___y_5358_);
lean_dec_ref(v___y_5357_);
lean_dec_ref(v_as_5353_);
return v_res_5366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__1(lean_object* v_mvarId_5367_, lean_object* v_config_5368_, lean_object* v_fvarIdsToSimp_5369_, size_t v_sz_5370_, size_t v___x_5371_, lean_object* v___x_5372_, uint8_t v_simplifyTarget_5373_, lean_object* v___y_5374_, lean_object* v___y_5375_, lean_object* v___y_5376_, lean_object* v___y_5377_, lean_object* v___y_5378_, lean_object* v___y_5379_){
_start:
{
lean_object* v___y_5382_; lean_object* v___y_5383_; lean_object* v___y_5384_; lean_object* v___y_5385_; lean_object* v___y_5386_; uint8_t v___y_5387_; lean_object* v___x_5407_; 
lean_inc_ref(v_config_5368_);
lean_inc(v_mvarId_5367_);
v___x_5407_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3(v_mvarId_5367_, v_config_5368_, v_fvarIdsToSimp_5369_, v_sz_5370_, v___x_5371_, v___x_5372_, v___y_5374_, v___y_5375_, v___y_5376_, v___y_5377_, v___y_5378_, v___y_5379_);
if (lean_obj_tag(v___x_5407_) == 0)
{
lean_object* v_a_5408_; lean_object* v___x_5410_; uint8_t v_isShared_5411_; uint8_t v_isSharedCheck_5615_; 
v_a_5408_ = lean_ctor_get(v___x_5407_, 0);
v_isSharedCheck_5615_ = !lean_is_exclusive(v___x_5407_);
if (v_isSharedCheck_5615_ == 0)
{
v___x_5410_ = v___x_5407_;
v_isShared_5411_ = v_isSharedCheck_5615_;
goto v_resetjp_5409_;
}
else
{
lean_inc(v_a_5408_);
lean_dec(v___x_5407_);
v___x_5410_ = lean_box(0);
v_isShared_5411_ = v_isSharedCheck_5615_;
goto v_resetjp_5409_;
}
v_resetjp_5409_:
{
lean_object* v_fst_5412_; lean_object* v_snd_5413_; lean_object* v___x_5415_; uint8_t v_isShared_5416_; uint8_t v_isSharedCheck_5614_; 
v_fst_5412_ = lean_ctor_get(v_a_5408_, 0);
v_snd_5413_ = lean_ctor_get(v_a_5408_, 1);
v_isSharedCheck_5614_ = !lean_is_exclusive(v_a_5408_);
if (v_isSharedCheck_5614_ == 0)
{
v___x_5415_ = v_a_5408_;
v_isShared_5416_ = v_isSharedCheck_5614_;
goto v_resetjp_5414_;
}
else
{
lean_inc(v_snd_5413_);
lean_inc(v_fst_5412_);
lean_dec(v_a_5408_);
v___x_5415_ = lean_box(0);
v_isShared_5416_ = v_isSharedCheck_5614_;
goto v_resetjp_5414_;
}
v_resetjp_5414_:
{
lean_object* v_mvarIdNew_5418_; lean_object* v___y_5419_; lean_object* v___y_5420_; lean_object* v___y_5421_; lean_object* v___y_5422_; lean_object* v___y_5469_; 
if (lean_obj_tag(v_fst_5412_) == 0)
{
lean_del_object(v___x_5410_);
if (v_simplifyTarget_5373_ == 0)
{
lean_del_object(v___x_5415_);
lean_dec_ref(v_config_5368_);
v_mvarIdNew_5418_ = v_mvarId_5367_;
v___y_5419_ = v___y_5376_;
v___y_5420_ = v___y_5377_;
v___y_5421_ = v___y_5378_;
v___y_5422_ = v___y_5379_;
goto v___jp_5417_;
}
else
{
lean_object* v___x_5512_; 
lean_inc(v_mvarId_5367_);
v___x_5512_ = l_Lean_MVarId_getType(v_mvarId_5367_, v___y_5376_, v___y_5377_, v___y_5378_, v___y_5379_);
if (lean_obj_tag(v___x_5512_) == 0)
{
lean_object* v_options_5513_; lean_object* v_a_5514_; lean_object* v_inheritedTraceOptions_5515_; uint8_t v_hasTrace_5516_; uint8_t v___x_5517_; 
v_options_5513_ = lean_ctor_get(v___y_5378_, 2);
v_a_5514_ = lean_ctor_get(v___x_5512_, 0);
lean_inc(v_a_5514_);
lean_dec_ref_known(v___x_5512_, 1);
v_inheritedTraceOptions_5515_ = lean_ctor_get(v___y_5378_, 13);
v_hasTrace_5516_ = lean_ctor_get_uint8(v_options_5513_, sizeof(void*)*1);
v___x_5517_ = lean_bool_not(v_hasTrace_5516_);
if (v___x_5517_ == 0)
{
lean_object* v___f_5518_; lean_object* v___x_5519_; lean_object* v___x_5520_; uint8_t v___y_5522_; lean_object* v___y_5523_; lean_object* v___y_5524_; lean_object* v_a_5525_; uint8_t v___y_5540_; lean_object* v___y_5541_; lean_object* v___y_5542_; lean_object* v_a_5543_; uint8_t v___y_5553_; uint8_t v_a_5595_; 
lean_inc(v_a_5514_);
v___f_5518_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___boxed), 9, 1);
lean_closure_set(v___f_5518_, 0, v_a_5514_);
v___x_5519_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0));
v___x_5520_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__1));
if (v_hasTrace_5516_ == 0)
{
v_a_5595_ = v_hasTrace_5516_;
goto v___jp_5594_;
}
else
{
lean_object* v___x_5599_; uint8_t v___x_5600_; 
v___x_5599_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1);
v___x_5600_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5515_, v_options_5513_, v___x_5599_);
if (v___x_5600_ == 0)
{
v_a_5595_ = v___x_5600_;
goto v___jp_5594_;
}
else
{
v___y_5553_ = v___x_5600_;
goto v___jp_5552_;
}
}
v___jp_5521_:
{
lean_object* v___x_5526_; double v___x_5527_; double v___x_5528_; double v___x_5529_; double v___x_5530_; double v___x_5531_; lean_object* v___x_5532_; lean_object* v___x_5533_; lean_object* v___x_5535_; 
v___x_5526_ = lean_io_mono_nanos_now();
v___x_5527_ = lean_float_of_nat(v___y_5524_);
v___x_5528_ = lean_float_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9);
v___x_5529_ = lean_float_div(v___x_5527_, v___x_5528_);
v___x_5530_ = lean_float_of_nat(v___x_5526_);
v___x_5531_ = lean_float_div(v___x_5530_, v___x_5528_);
v___x_5532_ = lean_box_float(v___x_5529_);
v___x_5533_ = lean_box_float(v___x_5531_);
if (v_isShared_5416_ == 0)
{
lean_ctor_set(v___x_5415_, 1, v___x_5533_);
lean_ctor_set(v___x_5415_, 0, v___x_5532_);
v___x_5535_ = v___x_5415_;
goto v_reusejp_5534_;
}
else
{
lean_object* v_reuseFailAlloc_5538_; 
v_reuseFailAlloc_5538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5538_, 0, v___x_5532_);
lean_ctor_set(v_reuseFailAlloc_5538_, 1, v___x_5533_);
v___x_5535_ = v_reuseFailAlloc_5538_;
goto v_reusejp_5534_;
}
v_reusejp_5534_:
{
lean_object* v___x_5536_; lean_object* v___x_5537_; 
v___x_5536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5536_, 0, v_a_5525_);
lean_ctor_set(v___x_5536_, 1, v___x_5535_);
v___x_5537_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2(v___x_5519_, v_simplifyTarget_5373_, v___x_5520_, v_options_5513_, v___y_5522_, v___y_5523_, v___f_5518_, v___x_5536_, v___y_5374_, v___y_5375_, v___y_5376_, v___y_5377_, v___y_5378_, v___y_5379_);
v___y_5469_ = v___x_5537_;
goto v___jp_5468_;
}
}
v___jp_5539_:
{
lean_object* v___x_5544_; double v___x_5545_; double v___x_5546_; lean_object* v___x_5547_; lean_object* v___x_5548_; lean_object* v___x_5549_; lean_object* v___x_5550_; lean_object* v___x_5551_; 
v___x_5544_ = lean_io_get_num_heartbeats();
v___x_5545_ = lean_float_of_nat(v___y_5542_);
v___x_5546_ = lean_float_of_nat(v___x_5544_);
v___x_5547_ = lean_box_float(v___x_5545_);
v___x_5548_ = lean_box_float(v___x_5546_);
v___x_5549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5549_, 0, v___x_5547_);
lean_ctor_set(v___x_5549_, 1, v___x_5548_);
v___x_5550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5550_, 0, v_a_5543_);
lean_ctor_set(v___x_5550_, 1, v___x_5549_);
v___x_5551_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2(v___x_5519_, v_simplifyTarget_5373_, v___x_5520_, v_options_5513_, v___y_5540_, v___y_5541_, v___f_5518_, v___x_5550_, v___y_5374_, v___y_5375_, v___y_5376_, v___y_5377_, v___y_5378_, v___y_5379_);
v___y_5469_ = v___x_5551_;
goto v___jp_5468_;
}
v___jp_5552_:
{
lean_object* v___x_5554_; lean_object* v_a_5555_; lean_object* v___x_5556_; uint8_t v___x_5557_; 
v___x_5554_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1___redArg(v___y_5379_);
v_a_5555_ = lean_ctor_get(v___x_5554_, 0);
lean_inc(v_a_5555_);
lean_dec_ref(v___x_5554_);
v___x_5556_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5557_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_5513_, v___x_5556_);
if (v___x_5557_ == 0)
{
lean_object* v___x_5558_; lean_object* v___x_5559_; 
v___x_5558_ = lean_io_mono_nanos_now();
v___x_5559_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v_a_5514_, v_config_5368_, v___y_5374_, v___y_5375_, v___y_5376_, v___y_5377_, v___y_5378_, v___y_5379_);
if (lean_obj_tag(v___x_5559_) == 0)
{
lean_object* v_a_5560_; lean_object* v___x_5562_; uint8_t v_isShared_5563_; uint8_t v_isSharedCheck_5567_; 
v_a_5560_ = lean_ctor_get(v___x_5559_, 0);
v_isSharedCheck_5567_ = !lean_is_exclusive(v___x_5559_);
if (v_isSharedCheck_5567_ == 0)
{
v___x_5562_ = v___x_5559_;
v_isShared_5563_ = v_isSharedCheck_5567_;
goto v_resetjp_5561_;
}
else
{
lean_inc(v_a_5560_);
lean_dec(v___x_5559_);
v___x_5562_ = lean_box(0);
v_isShared_5563_ = v_isSharedCheck_5567_;
goto v_resetjp_5561_;
}
v_resetjp_5561_:
{
lean_object* v___x_5565_; 
if (v_isShared_5563_ == 0)
{
lean_ctor_set_tag(v___x_5562_, 1);
v___x_5565_ = v___x_5562_;
goto v_reusejp_5564_;
}
else
{
lean_object* v_reuseFailAlloc_5566_; 
v_reuseFailAlloc_5566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5566_, 0, v_a_5560_);
v___x_5565_ = v_reuseFailAlloc_5566_;
goto v_reusejp_5564_;
}
v_reusejp_5564_:
{
v___y_5522_ = v___y_5553_;
v___y_5523_ = v_a_5555_;
v___y_5524_ = v___x_5558_;
v_a_5525_ = v___x_5565_;
goto v___jp_5521_;
}
}
}
else
{
lean_object* v_a_5568_; lean_object* v___x_5570_; uint8_t v_isShared_5571_; uint8_t v_isSharedCheck_5575_; 
v_a_5568_ = lean_ctor_get(v___x_5559_, 0);
v_isSharedCheck_5575_ = !lean_is_exclusive(v___x_5559_);
if (v_isSharedCheck_5575_ == 0)
{
v___x_5570_ = v___x_5559_;
v_isShared_5571_ = v_isSharedCheck_5575_;
goto v_resetjp_5569_;
}
else
{
lean_inc(v_a_5568_);
lean_dec(v___x_5559_);
v___x_5570_ = lean_box(0);
v_isShared_5571_ = v_isSharedCheck_5575_;
goto v_resetjp_5569_;
}
v_resetjp_5569_:
{
lean_object* v___x_5573_; 
if (v_isShared_5571_ == 0)
{
lean_ctor_set_tag(v___x_5570_, 0);
v___x_5573_ = v___x_5570_;
goto v_reusejp_5572_;
}
else
{
lean_object* v_reuseFailAlloc_5574_; 
v_reuseFailAlloc_5574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5574_, 0, v_a_5568_);
v___x_5573_ = v_reuseFailAlloc_5574_;
goto v_reusejp_5572_;
}
v_reusejp_5572_:
{
v___y_5522_ = v___y_5553_;
v___y_5523_ = v_a_5555_;
v___y_5524_ = v___x_5558_;
v_a_5525_ = v___x_5573_;
goto v___jp_5521_;
}
}
}
}
else
{
lean_object* v___x_5576_; lean_object* v___x_5577_; 
lean_del_object(v___x_5415_);
v___x_5576_ = lean_io_get_num_heartbeats();
v___x_5577_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v_a_5514_, v_config_5368_, v___y_5374_, v___y_5375_, v___y_5376_, v___y_5377_, v___y_5378_, v___y_5379_);
if (lean_obj_tag(v___x_5577_) == 0)
{
lean_object* v_a_5578_; lean_object* v___x_5580_; uint8_t v_isShared_5581_; uint8_t v_isSharedCheck_5585_; 
v_a_5578_ = lean_ctor_get(v___x_5577_, 0);
v_isSharedCheck_5585_ = !lean_is_exclusive(v___x_5577_);
if (v_isSharedCheck_5585_ == 0)
{
v___x_5580_ = v___x_5577_;
v_isShared_5581_ = v_isSharedCheck_5585_;
goto v_resetjp_5579_;
}
else
{
lean_inc(v_a_5578_);
lean_dec(v___x_5577_);
v___x_5580_ = lean_box(0);
v_isShared_5581_ = v_isSharedCheck_5585_;
goto v_resetjp_5579_;
}
v_resetjp_5579_:
{
lean_object* v___x_5583_; 
if (v_isShared_5581_ == 0)
{
lean_ctor_set_tag(v___x_5580_, 1);
v___x_5583_ = v___x_5580_;
goto v_reusejp_5582_;
}
else
{
lean_object* v_reuseFailAlloc_5584_; 
v_reuseFailAlloc_5584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5584_, 0, v_a_5578_);
v___x_5583_ = v_reuseFailAlloc_5584_;
goto v_reusejp_5582_;
}
v_reusejp_5582_:
{
v___y_5540_ = v___y_5553_;
v___y_5541_ = v_a_5555_;
v___y_5542_ = v___x_5576_;
v_a_5543_ = v___x_5583_;
goto v___jp_5539_;
}
}
}
else
{
lean_object* v_a_5586_; lean_object* v___x_5588_; uint8_t v_isShared_5589_; uint8_t v_isSharedCheck_5593_; 
v_a_5586_ = lean_ctor_get(v___x_5577_, 0);
v_isSharedCheck_5593_ = !lean_is_exclusive(v___x_5577_);
if (v_isSharedCheck_5593_ == 0)
{
v___x_5588_ = v___x_5577_;
v_isShared_5589_ = v_isSharedCheck_5593_;
goto v_resetjp_5587_;
}
else
{
lean_inc(v_a_5586_);
lean_dec(v___x_5577_);
v___x_5588_ = lean_box(0);
v_isShared_5589_ = v_isSharedCheck_5593_;
goto v_resetjp_5587_;
}
v_resetjp_5587_:
{
lean_object* v___x_5591_; 
if (v_isShared_5589_ == 0)
{
lean_ctor_set_tag(v___x_5588_, 0);
v___x_5591_ = v___x_5588_;
goto v_reusejp_5590_;
}
else
{
lean_object* v_reuseFailAlloc_5592_; 
v_reuseFailAlloc_5592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5592_, 0, v_a_5586_);
v___x_5591_ = v_reuseFailAlloc_5592_;
goto v_reusejp_5590_;
}
v_reusejp_5590_:
{
v___y_5540_ = v___y_5553_;
v___y_5541_ = v_a_5555_;
v___y_5542_ = v___x_5576_;
v_a_5543_ = v___x_5591_;
goto v___jp_5539_;
}
}
}
}
}
v___jp_5594_:
{
lean_object* v___x_5596_; uint8_t v___x_5597_; 
v___x_5596_ = l_Lean_trace_profiler;
v___x_5597_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_5513_, v___x_5596_);
if (v___x_5597_ == 0)
{
lean_object* v___x_5598_; 
lean_dec_ref(v___f_5518_);
lean_del_object(v___x_5415_);
v___x_5598_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v_a_5514_, v_config_5368_, v___y_5374_, v___y_5375_, v___y_5376_, v___y_5377_, v___y_5378_, v___y_5379_);
v___y_5469_ = v___x_5598_;
goto v___jp_5468_;
}
else
{
v___y_5553_ = v_a_5595_;
goto v___jp_5552_;
}
}
}
else
{
lean_object* v___x_5601_; 
lean_del_object(v___x_5415_);
v___x_5601_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v_a_5514_, v_config_5368_, v___y_5374_, v___y_5375_, v___y_5376_, v___y_5377_, v___y_5378_, v___y_5379_);
v___y_5469_ = v___x_5601_;
goto v___jp_5468_;
}
}
else
{
lean_object* v_a_5602_; lean_object* v___x_5604_; uint8_t v_isShared_5605_; uint8_t v_isSharedCheck_5609_; 
lean_del_object(v___x_5415_);
lean_dec(v_snd_5413_);
lean_dec_ref(v_config_5368_);
lean_dec(v_mvarId_5367_);
v_a_5602_ = lean_ctor_get(v___x_5512_, 0);
v_isSharedCheck_5609_ = !lean_is_exclusive(v___x_5512_);
if (v_isSharedCheck_5609_ == 0)
{
v___x_5604_ = v___x_5512_;
v_isShared_5605_ = v_isSharedCheck_5609_;
goto v_resetjp_5603_;
}
else
{
lean_inc(v_a_5602_);
lean_dec(v___x_5512_);
v___x_5604_ = lean_box(0);
v_isShared_5605_ = v_isSharedCheck_5609_;
goto v_resetjp_5603_;
}
v_resetjp_5603_:
{
lean_object* v___x_5607_; 
if (v_isShared_5605_ == 0)
{
v___x_5607_ = v___x_5604_;
goto v_reusejp_5606_;
}
else
{
lean_object* v_reuseFailAlloc_5608_; 
v_reuseFailAlloc_5608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5608_, 0, v_a_5602_);
v___x_5607_ = v_reuseFailAlloc_5608_;
goto v_reusejp_5606_;
}
v_reusejp_5606_:
{
return v___x_5607_;
}
}
}
}
}
else
{
lean_object* v_val_5610_; lean_object* v___x_5612_; 
lean_del_object(v___x_5415_);
lean_dec(v_snd_5413_);
lean_dec_ref(v_config_5368_);
lean_dec(v_mvarId_5367_);
v_val_5610_ = lean_ctor_get(v_fst_5412_, 0);
lean_inc(v_val_5610_);
lean_dec_ref_known(v_fst_5412_, 1);
if (v_isShared_5411_ == 0)
{
lean_ctor_set(v___x_5410_, 0, v_val_5610_);
v___x_5612_ = v___x_5410_;
goto v_reusejp_5611_;
}
else
{
lean_object* v_reuseFailAlloc_5613_; 
v_reuseFailAlloc_5613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5613_, 0, v_val_5610_);
v___x_5612_ = v_reuseFailAlloc_5613_;
goto v_reusejp_5611_;
}
v_reusejp_5611_:
{
return v___x_5612_;
}
}
v___jp_5417_:
{
lean_object* v___x_5423_; 
v___x_5423_ = l_Lean_MVarId_assertHypotheses(v_mvarIdNew_5418_, v_snd_5413_, v___y_5419_, v___y_5420_, v___y_5421_, v___y_5422_);
if (lean_obj_tag(v___x_5423_) == 0)
{
lean_object* v_a_5424_; lean_object* v_snd_5425_; lean_object* v___x_5426_; 
v_a_5424_ = lean_ctor_get(v___x_5423_, 0);
lean_inc(v_a_5424_);
lean_dec_ref_known(v___x_5423_, 1);
v_snd_5425_ = lean_ctor_get(v_a_5424_, 1);
lean_inc(v_snd_5425_);
lean_dec(v_a_5424_);
v___x_5426_ = l_Lean_MVarId_tryClearMany(v_snd_5425_, v_fvarIdsToSimp_5369_, v___y_5419_, v___y_5420_, v___y_5421_, v___y_5422_);
if (lean_obj_tag(v___x_5426_) == 0)
{
lean_object* v_a_5427_; lean_object* v___x_5428_; 
v_a_5427_ = lean_ctor_get(v___x_5426_, 0);
lean_inc(v_a_5427_);
lean_dec_ref_known(v___x_5426_, 1);
v___x_5428_ = l_Lean_Meta_saveState___redArg(v___y_5420_, v___y_5422_);
if (lean_obj_tag(v___x_5428_) == 0)
{
lean_object* v_a_5429_; uint8_t v___x_5430_; lean_object* v___x_5431_; 
v_a_5429_ = lean_ctor_get(v___x_5428_, 0);
lean_inc(v_a_5429_);
lean_dec_ref_known(v___x_5428_, 1);
v___x_5430_ = 1;
lean_inc(v_a_5427_);
v___x_5431_ = l_Lean_MVarId_refl(v_a_5427_, v___x_5430_, v___y_5419_, v___y_5420_, v___y_5421_, v___y_5422_);
if (lean_obj_tag(v___x_5431_) == 0)
{
lean_object* v___x_5433_; uint8_t v_isShared_5434_; uint8_t v_isSharedCheck_5439_; 
lean_dec(v_a_5429_);
lean_dec(v_a_5427_);
v_isSharedCheck_5439_ = !lean_is_exclusive(v___x_5431_);
if (v_isSharedCheck_5439_ == 0)
{
lean_object* v_unused_5440_; 
v_unused_5440_ = lean_ctor_get(v___x_5431_, 0);
lean_dec(v_unused_5440_);
v___x_5433_ = v___x_5431_;
v_isShared_5434_ = v_isSharedCheck_5439_;
goto v_resetjp_5432_;
}
else
{
lean_dec(v___x_5431_);
v___x_5433_ = lean_box(0);
v_isShared_5434_ = v_isSharedCheck_5439_;
goto v_resetjp_5432_;
}
v_resetjp_5432_:
{
lean_object* v___x_5435_; lean_object* v___x_5437_; 
v___x_5435_ = lean_box(0);
if (v_isShared_5434_ == 0)
{
lean_ctor_set(v___x_5433_, 0, v___x_5435_);
v___x_5437_ = v___x_5433_;
goto v_reusejp_5436_;
}
else
{
lean_object* v_reuseFailAlloc_5438_; 
v_reuseFailAlloc_5438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5438_, 0, v___x_5435_);
v___x_5437_ = v_reuseFailAlloc_5438_;
goto v_reusejp_5436_;
}
v_reusejp_5436_:
{
return v___x_5437_;
}
}
}
else
{
lean_object* v_a_5441_; uint8_t v___x_5442_; 
v_a_5441_ = lean_ctor_get(v___x_5431_, 0);
lean_inc(v_a_5441_);
lean_dec_ref_known(v___x_5431_, 1);
v___x_5442_ = l_Lean_Exception_isInterrupt(v_a_5441_);
if (v___x_5442_ == 0)
{
uint8_t v___x_5443_; 
lean_inc(v_a_5441_);
v___x_5443_ = l_Lean_Exception_isRuntime(v_a_5441_);
v___y_5382_ = v___y_5422_;
v___y_5383_ = v___y_5420_;
v___y_5384_ = v_a_5427_;
v___y_5385_ = v_a_5441_;
v___y_5386_ = v_a_5429_;
v___y_5387_ = v___x_5443_;
goto v___jp_5381_;
}
else
{
v___y_5382_ = v___y_5422_;
v___y_5383_ = v___y_5420_;
v___y_5384_ = v_a_5427_;
v___y_5385_ = v_a_5441_;
v___y_5386_ = v_a_5429_;
v___y_5387_ = v___x_5442_;
goto v___jp_5381_;
}
}
}
else
{
lean_object* v_a_5444_; lean_object* v___x_5446_; uint8_t v_isShared_5447_; uint8_t v_isSharedCheck_5451_; 
lean_dec(v_a_5427_);
v_a_5444_ = lean_ctor_get(v___x_5428_, 0);
v_isSharedCheck_5451_ = !lean_is_exclusive(v___x_5428_);
if (v_isSharedCheck_5451_ == 0)
{
v___x_5446_ = v___x_5428_;
v_isShared_5447_ = v_isSharedCheck_5451_;
goto v_resetjp_5445_;
}
else
{
lean_inc(v_a_5444_);
lean_dec(v___x_5428_);
v___x_5446_ = lean_box(0);
v_isShared_5447_ = v_isSharedCheck_5451_;
goto v_resetjp_5445_;
}
v_resetjp_5445_:
{
lean_object* v___x_5449_; 
if (v_isShared_5447_ == 0)
{
v___x_5449_ = v___x_5446_;
goto v_reusejp_5448_;
}
else
{
lean_object* v_reuseFailAlloc_5450_; 
v_reuseFailAlloc_5450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5450_, 0, v_a_5444_);
v___x_5449_ = v_reuseFailAlloc_5450_;
goto v_reusejp_5448_;
}
v_reusejp_5448_:
{
return v___x_5449_;
}
}
}
}
else
{
lean_object* v_a_5452_; lean_object* v___x_5454_; uint8_t v_isShared_5455_; uint8_t v_isSharedCheck_5459_; 
v_a_5452_ = lean_ctor_get(v___x_5426_, 0);
v_isSharedCheck_5459_ = !lean_is_exclusive(v___x_5426_);
if (v_isSharedCheck_5459_ == 0)
{
v___x_5454_ = v___x_5426_;
v_isShared_5455_ = v_isSharedCheck_5459_;
goto v_resetjp_5453_;
}
else
{
lean_inc(v_a_5452_);
lean_dec(v___x_5426_);
v___x_5454_ = lean_box(0);
v_isShared_5455_ = v_isSharedCheck_5459_;
goto v_resetjp_5453_;
}
v_resetjp_5453_:
{
lean_object* v___x_5457_; 
if (v_isShared_5455_ == 0)
{
v___x_5457_ = v___x_5454_;
goto v_reusejp_5456_;
}
else
{
lean_object* v_reuseFailAlloc_5458_; 
v_reuseFailAlloc_5458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5458_, 0, v_a_5452_);
v___x_5457_ = v_reuseFailAlloc_5458_;
goto v_reusejp_5456_;
}
v_reusejp_5456_:
{
return v___x_5457_;
}
}
}
}
else
{
lean_object* v_a_5460_; lean_object* v___x_5462_; uint8_t v_isShared_5463_; uint8_t v_isSharedCheck_5467_; 
v_a_5460_ = lean_ctor_get(v___x_5423_, 0);
v_isSharedCheck_5467_ = !lean_is_exclusive(v___x_5423_);
if (v_isSharedCheck_5467_ == 0)
{
v___x_5462_ = v___x_5423_;
v_isShared_5463_ = v_isSharedCheck_5467_;
goto v_resetjp_5461_;
}
else
{
lean_inc(v_a_5460_);
lean_dec(v___x_5423_);
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
v___jp_5468_:
{
if (lean_obj_tag(v___y_5469_) == 0)
{
lean_object* v_a_5470_; 
v_a_5470_ = lean_ctor_get(v___y_5469_, 0);
lean_inc(v_a_5470_);
lean_dec_ref_known(v___y_5469_, 1);
if (lean_obj_tag(v_a_5470_) == 0)
{
lean_dec_ref_known(v_a_5470_, 0);
v_mvarIdNew_5418_ = v_mvarId_5367_;
v___y_5419_ = v___y_5376_;
v___y_5420_ = v___y_5377_;
v___y_5421_ = v___y_5378_;
v___y_5422_ = v___y_5379_;
goto v___jp_5417_;
}
else
{
lean_object* v_e_x27_5471_; lean_object* v_proof_5472_; uint8_t v___x_5473_; 
v_e_x27_5471_ = lean_ctor_get(v_a_5470_, 0);
lean_inc_ref_n(v_e_x27_5471_, 2);
v_proof_5472_ = lean_ctor_get(v_a_5470_, 1);
lean_inc_ref(v_proof_5472_);
lean_dec_ref_known(v_a_5470_, 2);
v___x_5473_ = l_Lean_Expr_isTrue(v_e_x27_5471_);
if (v___x_5473_ == 0)
{
lean_object* v___x_5474_; 
v___x_5474_ = l_Lean_MVarId_replaceTargetEq(v_mvarId_5367_, v_e_x27_5471_, v_proof_5472_, v___y_5376_, v___y_5377_, v___y_5378_, v___y_5379_);
if (lean_obj_tag(v___x_5474_) == 0)
{
lean_object* v_a_5475_; 
v_a_5475_ = lean_ctor_get(v___x_5474_, 0);
lean_inc(v_a_5475_);
lean_dec_ref_known(v___x_5474_, 1);
v_mvarIdNew_5418_ = v_a_5475_;
v___y_5419_ = v___y_5376_;
v___y_5420_ = v___y_5377_;
v___y_5421_ = v___y_5378_;
v___y_5422_ = v___y_5379_;
goto v___jp_5417_;
}
else
{
lean_object* v_a_5476_; lean_object* v___x_5478_; uint8_t v_isShared_5479_; uint8_t v_isSharedCheck_5483_; 
lean_dec(v_snd_5413_);
v_a_5476_ = lean_ctor_get(v___x_5474_, 0);
v_isSharedCheck_5483_ = !lean_is_exclusive(v___x_5474_);
if (v_isSharedCheck_5483_ == 0)
{
v___x_5478_ = v___x_5474_;
v_isShared_5479_ = v_isSharedCheck_5483_;
goto v_resetjp_5477_;
}
else
{
lean_inc(v_a_5476_);
lean_dec(v___x_5474_);
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
else
{
lean_object* v___x_5484_; 
lean_dec_ref(v_e_x27_5471_);
lean_dec(v_snd_5413_);
v___x_5484_ = l_Lean_Meta_mkOfEqTrue(v_proof_5472_, v___y_5376_, v___y_5377_, v___y_5378_, v___y_5379_);
if (lean_obj_tag(v___x_5484_) == 0)
{
lean_object* v_a_5485_; lean_object* v___x_5486_; lean_object* v___x_5488_; uint8_t v_isShared_5489_; uint8_t v_isSharedCheck_5494_; 
v_a_5485_ = lean_ctor_get(v___x_5484_, 0);
lean_inc(v_a_5485_);
lean_dec_ref_known(v___x_5484_, 1);
v___x_5486_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___redArg(v_mvarId_5367_, v_a_5485_, v___y_5377_);
v_isSharedCheck_5494_ = !lean_is_exclusive(v___x_5486_);
if (v_isSharedCheck_5494_ == 0)
{
lean_object* v_unused_5495_; 
v_unused_5495_ = lean_ctor_get(v___x_5486_, 0);
lean_dec(v_unused_5495_);
v___x_5488_ = v___x_5486_;
v_isShared_5489_ = v_isSharedCheck_5494_;
goto v_resetjp_5487_;
}
else
{
lean_dec(v___x_5486_);
v___x_5488_ = lean_box(0);
v_isShared_5489_ = v_isSharedCheck_5494_;
goto v_resetjp_5487_;
}
v_resetjp_5487_:
{
lean_object* v___x_5490_; lean_object* v___x_5492_; 
v___x_5490_ = lean_box(0);
if (v_isShared_5489_ == 0)
{
lean_ctor_set(v___x_5488_, 0, v___x_5490_);
v___x_5492_ = v___x_5488_;
goto v_reusejp_5491_;
}
else
{
lean_object* v_reuseFailAlloc_5493_; 
v_reuseFailAlloc_5493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5493_, 0, v___x_5490_);
v___x_5492_ = v_reuseFailAlloc_5493_;
goto v_reusejp_5491_;
}
v_reusejp_5491_:
{
return v___x_5492_;
}
}
}
else
{
lean_object* v_a_5496_; lean_object* v___x_5498_; uint8_t v_isShared_5499_; uint8_t v_isSharedCheck_5503_; 
lean_dec(v_mvarId_5367_);
v_a_5496_ = lean_ctor_get(v___x_5484_, 0);
v_isSharedCheck_5503_ = !lean_is_exclusive(v___x_5484_);
if (v_isSharedCheck_5503_ == 0)
{
v___x_5498_ = v___x_5484_;
v_isShared_5499_ = v_isSharedCheck_5503_;
goto v_resetjp_5497_;
}
else
{
lean_inc(v_a_5496_);
lean_dec(v___x_5484_);
v___x_5498_ = lean_box(0);
v_isShared_5499_ = v_isSharedCheck_5503_;
goto v_resetjp_5497_;
}
v_resetjp_5497_:
{
lean_object* v___x_5501_; 
if (v_isShared_5499_ == 0)
{
v___x_5501_ = v___x_5498_;
goto v_reusejp_5500_;
}
else
{
lean_object* v_reuseFailAlloc_5502_; 
v_reuseFailAlloc_5502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5502_, 0, v_a_5496_);
v___x_5501_ = v_reuseFailAlloc_5502_;
goto v_reusejp_5500_;
}
v_reusejp_5500_:
{
return v___x_5501_;
}
}
}
}
}
}
else
{
lean_object* v_a_5504_; lean_object* v___x_5506_; uint8_t v_isShared_5507_; uint8_t v_isSharedCheck_5511_; 
lean_dec(v_snd_5413_);
lean_dec(v_mvarId_5367_);
v_a_5504_ = lean_ctor_get(v___y_5469_, 0);
v_isSharedCheck_5511_ = !lean_is_exclusive(v___y_5469_);
if (v_isSharedCheck_5511_ == 0)
{
v___x_5506_ = v___y_5469_;
v_isShared_5507_ = v_isSharedCheck_5511_;
goto v_resetjp_5505_;
}
else
{
lean_inc(v_a_5504_);
lean_dec(v___y_5469_);
v___x_5506_ = lean_box(0);
v_isShared_5507_ = v_isSharedCheck_5511_;
goto v_resetjp_5505_;
}
v_resetjp_5505_:
{
lean_object* v___x_5509_; 
if (v_isShared_5507_ == 0)
{
v___x_5509_ = v___x_5506_;
goto v_reusejp_5508_;
}
else
{
lean_object* v_reuseFailAlloc_5510_; 
v_reuseFailAlloc_5510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5510_, 0, v_a_5504_);
v___x_5509_ = v_reuseFailAlloc_5510_;
goto v_reusejp_5508_;
}
v_reusejp_5508_:
{
return v___x_5509_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5616_; lean_object* v___x_5618_; uint8_t v_isShared_5619_; uint8_t v_isSharedCheck_5623_; 
lean_dec_ref(v_config_5368_);
lean_dec(v_mvarId_5367_);
v_a_5616_ = lean_ctor_get(v___x_5407_, 0);
v_isSharedCheck_5623_ = !lean_is_exclusive(v___x_5407_);
if (v_isSharedCheck_5623_ == 0)
{
v___x_5618_ = v___x_5407_;
v_isShared_5619_ = v_isSharedCheck_5623_;
goto v_resetjp_5617_;
}
else
{
lean_inc(v_a_5616_);
lean_dec(v___x_5407_);
v___x_5618_ = lean_box(0);
v_isShared_5619_ = v_isSharedCheck_5623_;
goto v_resetjp_5617_;
}
v_resetjp_5617_:
{
lean_object* v___x_5621_; 
if (v_isShared_5619_ == 0)
{
v___x_5621_ = v___x_5618_;
goto v_reusejp_5620_;
}
else
{
lean_object* v_reuseFailAlloc_5622_; 
v_reuseFailAlloc_5622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5622_, 0, v_a_5616_);
v___x_5621_ = v_reuseFailAlloc_5622_;
goto v_reusejp_5620_;
}
v_reusejp_5620_:
{
return v___x_5621_;
}
}
}
v___jp_5381_:
{
if (v___y_5387_ == 0)
{
lean_object* v___x_5388_; 
lean_dec_ref(v___y_5385_);
v___x_5388_ = l_Lean_Meta_SavedState_restore___redArg(v___y_5386_, v___y_5383_, v___y_5382_);
lean_dec_ref(v___y_5386_);
if (lean_obj_tag(v___x_5388_) == 0)
{
lean_object* v___x_5390_; uint8_t v_isShared_5391_; uint8_t v_isSharedCheck_5396_; 
v_isSharedCheck_5396_ = !lean_is_exclusive(v___x_5388_);
if (v_isSharedCheck_5396_ == 0)
{
lean_object* v_unused_5397_; 
v_unused_5397_ = lean_ctor_get(v___x_5388_, 0);
lean_dec(v_unused_5397_);
v___x_5390_ = v___x_5388_;
v_isShared_5391_ = v_isSharedCheck_5396_;
goto v_resetjp_5389_;
}
else
{
lean_dec(v___x_5388_);
v___x_5390_ = lean_box(0);
v_isShared_5391_ = v_isSharedCheck_5396_;
goto v_resetjp_5389_;
}
v_resetjp_5389_:
{
lean_object* v___x_5392_; lean_object* v___x_5394_; 
v___x_5392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5392_, 0, v___y_5384_);
if (v_isShared_5391_ == 0)
{
lean_ctor_set(v___x_5390_, 0, v___x_5392_);
v___x_5394_ = v___x_5390_;
goto v_reusejp_5393_;
}
else
{
lean_object* v_reuseFailAlloc_5395_; 
v_reuseFailAlloc_5395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5395_, 0, v___x_5392_);
v___x_5394_ = v_reuseFailAlloc_5395_;
goto v_reusejp_5393_;
}
v_reusejp_5393_:
{
return v___x_5394_;
}
}
}
else
{
lean_object* v_a_5398_; lean_object* v___x_5400_; uint8_t v_isShared_5401_; uint8_t v_isSharedCheck_5405_; 
lean_dec(v___y_5384_);
v_a_5398_ = lean_ctor_get(v___x_5388_, 0);
v_isSharedCheck_5405_ = !lean_is_exclusive(v___x_5388_);
if (v_isSharedCheck_5405_ == 0)
{
v___x_5400_ = v___x_5388_;
v_isShared_5401_ = v_isSharedCheck_5405_;
goto v_resetjp_5399_;
}
else
{
lean_inc(v_a_5398_);
lean_dec(v___x_5388_);
v___x_5400_ = lean_box(0);
v_isShared_5401_ = v_isSharedCheck_5405_;
goto v_resetjp_5399_;
}
v_resetjp_5399_:
{
lean_object* v___x_5403_; 
if (v_isShared_5401_ == 0)
{
v___x_5403_ = v___x_5400_;
goto v_reusejp_5402_;
}
else
{
lean_object* v_reuseFailAlloc_5404_; 
v_reuseFailAlloc_5404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5404_, 0, v_a_5398_);
v___x_5403_ = v_reuseFailAlloc_5404_;
goto v_reusejp_5402_;
}
v_reusejp_5402_:
{
return v___x_5403_;
}
}
}
}
else
{
lean_object* v___x_5406_; 
lean_dec_ref(v___y_5386_);
lean_dec(v___y_5384_);
v___x_5406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5406_, 0, v___y_5385_);
return v___x_5406_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__1___boxed(lean_object* v_mvarId_5624_, lean_object* v_config_5625_, lean_object* v_fvarIdsToSimp_5626_, lean_object* v_sz_5627_, lean_object* v___x_5628_, lean_object* v___x_5629_, lean_object* v_simplifyTarget_5630_, lean_object* v___y_5631_, lean_object* v___y_5632_, lean_object* v___y_5633_, lean_object* v___y_5634_, lean_object* v___y_5635_, lean_object* v___y_5636_, lean_object* v___y_5637_){
_start:
{
size_t v_sz_boxed_5638_; size_t v___x_49211__boxed_5639_; uint8_t v_simplifyTarget_boxed_5640_; lean_object* v_res_5641_; 
v_sz_boxed_5638_ = lean_unbox_usize(v_sz_5627_);
lean_dec(v_sz_5627_);
v___x_49211__boxed_5639_ = lean_unbox_usize(v___x_5628_);
lean_dec(v___x_5628_);
v_simplifyTarget_boxed_5640_ = lean_unbox(v_simplifyTarget_5630_);
v_res_5641_ = l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__1(v_mvarId_5624_, v_config_5625_, v_fvarIdsToSimp_5626_, v_sz_boxed_5638_, v___x_49211__boxed_5639_, v___x_5629_, v_simplifyTarget_boxed_5640_, v___y_5631_, v___y_5632_, v___y_5633_, v___y_5634_, v___y_5635_, v___y_5636_);
lean_dec(v___y_5636_);
lean_dec_ref(v___y_5635_);
lean_dec(v___y_5634_);
lean_dec_ref(v___y_5633_);
lean_dec(v___y_5632_);
lean_dec_ref(v___y_5631_);
lean_dec_ref(v_fvarIdsToSimp_5626_);
return v_res_5641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__2(lean_object* v_fvarIdsToSimp_5649_, lean_object* v_mvarId_5650_, uint8_t v_simplifyTarget_5651_, lean_object* v___y_5652_, lean_object* v___y_5653_, lean_object* v___y_5654_, lean_object* v___y_5655_, lean_object* v___y_5656_, lean_object* v___y_5657_){
_start:
{
lean_object* v_options_5659_; lean_object* v___x_5660_; lean_object* v___x_5661_; lean_object* v___x_5662_; lean_object* v_config_5663_; lean_object* v___x_5664_; size_t v_sz_5665_; lean_object* v___x_5666_; lean_object* v___x_5667_; lean_object* v___x_5668_; lean_object* v___f_5669_; lean_object* v___x_5670_; 
v_options_5659_ = lean_ctor_get(v___y_5656_, 2);
v___x_5660_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_5661_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_5659_, v___x_5660_);
v___x_5662_ = lean_unsigned_to_nat(2u);
v_config_5663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_config_5663_, 0, v___x_5661_);
lean_ctor_set(v_config_5663_, 1, v___x_5662_);
v___x_5664_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__2___closed__1));
v_sz_5665_ = lean_array_size(v_fvarIdsToSimp_5649_);
v___x_5666_ = lean_box_usize(v_sz_5665_);
v___x_5667_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__2___boxed__const__1));
v___x_5668_ = lean_box(v_simplifyTarget_5651_);
lean_inc(v_mvarId_5650_);
v___f_5669_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__1___boxed), 14, 7);
lean_closure_set(v___f_5669_, 0, v_mvarId_5650_);
lean_closure_set(v___f_5669_, 1, v_config_5663_);
lean_closure_set(v___f_5669_, 2, v_fvarIdsToSimp_5649_);
lean_closure_set(v___f_5669_, 3, v___x_5666_);
lean_closure_set(v___f_5669_, 4, v___x_5667_);
lean_closure_set(v___f_5669_, 5, v___x_5664_);
lean_closure_set(v___f_5669_, 6, v___x_5668_);
v___x_5670_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg(v_mvarId_5650_, v___f_5669_, v___y_5652_, v___y_5653_, v___y_5654_, v___y_5655_, v___y_5656_, v___y_5657_);
return v___x_5670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__2___boxed(lean_object* v_fvarIdsToSimp_5671_, lean_object* v_mvarId_5672_, lean_object* v_simplifyTarget_5673_, lean_object* v___y_5674_, lean_object* v___y_5675_, lean_object* v___y_5676_, lean_object* v___y_5677_, lean_object* v___y_5678_, lean_object* v___y_5679_, lean_object* v___y_5680_){
_start:
{
uint8_t v_simplifyTarget_boxed_5681_; lean_object* v_res_5682_; 
v_simplifyTarget_boxed_5681_ = lean_unbox(v_simplifyTarget_5673_);
v_res_5682_ = l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__2(v_fvarIdsToSimp_5671_, v_mvarId_5672_, v_simplifyTarget_boxed_5681_, v___y_5674_, v___y_5675_, v___y_5676_, v___y_5677_, v___y_5678_, v___y_5679_);
lean_dec(v___y_5679_);
lean_dec_ref(v___y_5678_);
lean_dec(v___y_5677_);
lean_dec_ref(v___y_5676_);
lean_dec(v___y_5675_);
lean_dec_ref(v___y_5674_);
return v_res_5682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore(lean_object* v_mvarId_5683_, uint8_t v_simplifyTarget_5684_, lean_object* v_fvarIdsToSimp_5685_, lean_object* v_a_5686_, lean_object* v_a_5687_, lean_object* v_a_5688_, lean_object* v_a_5689_, lean_object* v_a_5690_, lean_object* v_a_5691_){
_start:
{
lean_object* v___x_5693_; lean_object* v___f_5694_; lean_object* v___x_5695_; 
v___x_5693_ = lean_box(v_simplifyTarget_5684_);
v___f_5694_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__2___boxed), 10, 3);
lean_closure_set(v___f_5694_, 0, v_fvarIdsToSimp_5685_);
lean_closure_set(v___f_5694_, 1, v_mvarId_5683_);
lean_closure_set(v___f_5694_, 2, v___x_5693_);
v___x_5695_ = l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0___redArg(v___f_5694_, v_a_5686_, v_a_5687_, v_a_5688_, v_a_5689_, v_a_5690_, v_a_5691_);
return v___x_5695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___boxed(lean_object* v_mvarId_5696_, lean_object* v_simplifyTarget_5697_, lean_object* v_fvarIdsToSimp_5698_, lean_object* v_a_5699_, lean_object* v_a_5700_, lean_object* v_a_5701_, lean_object* v_a_5702_, lean_object* v_a_5703_, lean_object* v_a_5704_, lean_object* v_a_5705_){
_start:
{
uint8_t v_simplifyTarget_boxed_5706_; lean_object* v_res_5707_; 
v_simplifyTarget_boxed_5706_ = lean_unbox(v_simplifyTarget_5697_);
v_res_5707_ = l_Lean_Meta_Tactic_Cbv_cbvGoalCore(v_mvarId_5696_, v_simplifyTarget_boxed_5706_, v_fvarIdsToSimp_5698_, v_a_5699_, v_a_5700_, v_a_5701_, v_a_5702_, v_a_5703_, v_a_5704_);
lean_dec(v_a_5704_);
lean_dec_ref(v_a_5703_);
lean_dec(v_a_5702_);
lean_dec_ref(v_a_5701_);
lean_dec(v_a_5700_);
lean_dec_ref(v_a_5699_);
return v_res_5707_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0(lean_object* v_mvarId_5708_, lean_object* v_val_5709_, lean_object* v___y_5710_, lean_object* v___y_5711_, lean_object* v___y_5712_, lean_object* v___y_5713_, lean_object* v___y_5714_, lean_object* v___y_5715_){
_start:
{
lean_object* v___x_5717_; 
v___x_5717_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___redArg(v_mvarId_5708_, v_val_5709_, v___y_5713_);
return v___x_5717_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___boxed(lean_object* v_mvarId_5718_, lean_object* v_val_5719_, lean_object* v___y_5720_, lean_object* v___y_5721_, lean_object* v___y_5722_, lean_object* v___y_5723_, lean_object* v___y_5724_, lean_object* v___y_5725_, lean_object* v___y_5726_){
_start:
{
lean_object* v_res_5727_; 
v_res_5727_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0(v_mvarId_5718_, v_val_5719_, v___y_5720_, v___y_5721_, v___y_5722_, v___y_5723_, v___y_5724_, v___y_5725_);
lean_dec(v___y_5725_);
lean_dec_ref(v___y_5724_);
lean_dec(v___y_5723_);
lean_dec_ref(v___y_5722_);
lean_dec(v___y_5721_);
lean_dec_ref(v___y_5720_);
return v_res_5727_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4(lean_object* v_00_u03b1_5728_, lean_object* v_x_5729_, lean_object* v___y_5730_, lean_object* v___y_5731_, lean_object* v___y_5732_, lean_object* v___y_5733_, lean_object* v___y_5734_, lean_object* v___y_5735_){
_start:
{
lean_object* v___x_5737_; 
v___x_5737_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4___redArg(v_x_5729_);
return v___x_5737_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4___boxed(lean_object* v_00_u03b1_5738_, lean_object* v_x_5739_, lean_object* v___y_5740_, lean_object* v___y_5741_, lean_object* v___y_5742_, lean_object* v___y_5743_, lean_object* v___y_5744_, lean_object* v___y_5745_, lean_object* v___y_5746_){
_start:
{
lean_object* v_res_5747_; 
v_res_5747_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4(v_00_u03b1_5738_, v_x_5739_, v___y_5740_, v___y_5741_, v___y_5742_, v___y_5743_, v___y_5744_, v___y_5745_);
lean_dec(v___y_5745_);
lean_dec_ref(v___y_5744_);
lean_dec(v___y_5743_);
lean_dec_ref(v___y_5742_);
lean_dec(v___y_5741_);
lean_dec_ref(v___y_5740_);
return v_res_5747_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0(lean_object* v_00_u03b2_5748_, lean_object* v_x_5749_, lean_object* v_x_5750_, lean_object* v_x_5751_){
_start:
{
lean_object* v___x_5752_; 
v___x_5752_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0___redArg(v_x_5749_, v_x_5750_, v_x_5751_);
return v___x_5752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__3(lean_object* v_oldTraces_5753_, lean_object* v_data_5754_, lean_object* v_ref_5755_, lean_object* v_msg_5756_, lean_object* v___y_5757_, lean_object* v___y_5758_, lean_object* v___y_5759_, lean_object* v___y_5760_, lean_object* v___y_5761_, lean_object* v___y_5762_){
_start:
{
lean_object* v___x_5764_; 
v___x_5764_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__3___redArg(v_oldTraces_5753_, v_data_5754_, v_ref_5755_, v_msg_5756_, v___y_5759_, v___y_5760_, v___y_5761_, v___y_5762_);
return v___x_5764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__3___boxed(lean_object* v_oldTraces_5765_, lean_object* v_data_5766_, lean_object* v_ref_5767_, lean_object* v_msg_5768_, lean_object* v___y_5769_, lean_object* v___y_5770_, lean_object* v___y_5771_, lean_object* v___y_5772_, lean_object* v___y_5773_, lean_object* v___y_5774_, lean_object* v___y_5775_){
_start:
{
lean_object* v_res_5776_; 
v_res_5776_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__3(v_oldTraces_5765_, v_data_5766_, v_ref_5767_, v_msg_5768_, v___y_5769_, v___y_5770_, v___y_5771_, v___y_5772_, v___y_5773_, v___y_5774_);
lean_dec(v___y_5774_);
lean_dec_ref(v___y_5773_);
lean_dec(v___y_5772_);
lean_dec_ref(v___y_5771_);
lean_dec(v___y_5770_);
lean_dec_ref(v___y_5769_);
return v_res_5776_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_5777_, lean_object* v_x_5778_, size_t v_x_5779_, size_t v_x_5780_, lean_object* v_x_5781_, lean_object* v_x_5782_){
_start:
{
lean_object* v___x_5783_; 
v___x_5783_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg(v_x_5778_, v_x_5779_, v_x_5780_, v_x_5781_, v_x_5782_);
return v___x_5783_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_5784_, lean_object* v_x_5785_, lean_object* v_x_5786_, lean_object* v_x_5787_, lean_object* v_x_5788_, lean_object* v_x_5789_){
_start:
{
size_t v_x_49871__boxed_5790_; size_t v_x_49872__boxed_5791_; lean_object* v_res_5792_; 
v_x_49871__boxed_5790_ = lean_unbox_usize(v_x_5786_);
lean_dec(v_x_5786_);
v_x_49872__boxed_5791_ = lean_unbox_usize(v_x_5787_);
lean_dec(v_x_5787_);
v_res_5792_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3(v_00_u03b2_5784_, v_x_5785_, v_x_49871__boxed_5790_, v_x_49872__boxed_5791_, v_x_5788_, v_x_5789_);
return v_res_5792_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__7(lean_object* v_00_u03b2_5793_, lean_object* v_n_5794_, lean_object* v_k_5795_, lean_object* v_v_5796_){
_start:
{
lean_object* v___x_5797_; 
v___x_5797_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__7___redArg(v_n_5794_, v_k_5795_, v_v_5796_);
return v___x_5797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__8(lean_object* v_00_u03b2_5798_, size_t v_depth_5799_, lean_object* v_keys_5800_, lean_object* v_vals_5801_, lean_object* v_heq_5802_, lean_object* v_i_5803_, lean_object* v_entries_5804_){
_start:
{
lean_object* v___x_5805_; 
v___x_5805_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__8___redArg(v_depth_5799_, v_keys_5800_, v_vals_5801_, v_i_5803_, v_entries_5804_);
return v___x_5805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__8___boxed(lean_object* v_00_u03b2_5806_, lean_object* v_depth_5807_, lean_object* v_keys_5808_, lean_object* v_vals_5809_, lean_object* v_heq_5810_, lean_object* v_i_5811_, lean_object* v_entries_5812_){
_start:
{
size_t v_depth_boxed_5813_; lean_object* v_res_5814_; 
v_depth_boxed_5813_ = lean_unbox_usize(v_depth_5807_);
lean_dec(v_depth_5807_);
v_res_5814_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__8(v_00_u03b2_5806_, v_depth_boxed_5813_, v_keys_5808_, v_vals_5809_, v_heq_5810_, v_i_5811_, v_entries_5812_);
lean_dec_ref(v_vals_5809_);
lean_dec_ref(v_keys_5808_);
return v_res_5814_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__7_spec__9(lean_object* v_00_u03b2_5815_, lean_object* v_x_5816_, lean_object* v_x_5817_, lean_object* v_x_5818_, lean_object* v_x_5819_){
_start:
{
lean_object* v___x_5820_; 
v___x_5820_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__7_spec__9___redArg(v_x_5816_, v_x_5817_, v_x_5818_, v_x_5819_);
return v___x_5820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0(lean_object* v_mvarId_5821_, uint8_t v_simplifyTarget_5822_, lean_object* v_fvarIdsToSimp_5823_, lean_object* v___y_5824_, lean_object* v___y_5825_, lean_object* v___y_5826_, lean_object* v___y_5827_, lean_object* v___y_5828_, lean_object* v___y_5829_){
_start:
{
lean_object* v___x_5831_; 
v___x_5831_ = l_Lean_Meta_Sym_preprocessMVar(v_mvarId_5821_, v___y_5824_, v___y_5825_, v___y_5826_, v___y_5827_, v___y_5828_, v___y_5829_);
if (lean_obj_tag(v___x_5831_) == 0)
{
lean_object* v_a_5832_; lean_object* v___x_5833_; 
v_a_5832_ = lean_ctor_get(v___x_5831_, 0);
lean_inc(v_a_5832_);
lean_dec_ref_known(v___x_5831_, 1);
v___x_5833_ = l_Lean_Meta_Tactic_Cbv_cbvGoalCore(v_a_5832_, v_simplifyTarget_5822_, v_fvarIdsToSimp_5823_, v___y_5824_, v___y_5825_, v___y_5826_, v___y_5827_, v___y_5828_, v___y_5829_);
return v___x_5833_;
}
else
{
lean_object* v_a_5834_; lean_object* v___x_5836_; uint8_t v_isShared_5837_; uint8_t v_isSharedCheck_5841_; 
lean_dec_ref(v_fvarIdsToSimp_5823_);
v_a_5834_ = lean_ctor_get(v___x_5831_, 0);
v_isSharedCheck_5841_ = !lean_is_exclusive(v___x_5831_);
if (v_isSharedCheck_5841_ == 0)
{
v___x_5836_ = v___x_5831_;
v_isShared_5837_ = v_isSharedCheck_5841_;
goto v_resetjp_5835_;
}
else
{
lean_inc(v_a_5834_);
lean_dec(v___x_5831_);
v___x_5836_ = lean_box(0);
v_isShared_5837_ = v_isSharedCheck_5841_;
goto v_resetjp_5835_;
}
v_resetjp_5835_:
{
lean_object* v___x_5839_; 
if (v_isShared_5837_ == 0)
{
v___x_5839_ = v___x_5836_;
goto v_reusejp_5838_;
}
else
{
lean_object* v_reuseFailAlloc_5840_; 
v_reuseFailAlloc_5840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5840_, 0, v_a_5834_);
v___x_5839_ = v_reuseFailAlloc_5840_;
goto v_reusejp_5838_;
}
v_reusejp_5838_:
{
return v___x_5839_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___boxed(lean_object* v_mvarId_5842_, lean_object* v_simplifyTarget_5843_, lean_object* v_fvarIdsToSimp_5844_, lean_object* v___y_5845_, lean_object* v___y_5846_, lean_object* v___y_5847_, lean_object* v___y_5848_, lean_object* v___y_5849_, lean_object* v___y_5850_, lean_object* v___y_5851_){
_start:
{
uint8_t v_simplifyTarget_boxed_5852_; lean_object* v_res_5853_; 
v_simplifyTarget_boxed_5852_ = lean_unbox(v_simplifyTarget_5843_);
v_res_5853_ = l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0(v_mvarId_5842_, v_simplifyTarget_boxed_5852_, v_fvarIdsToSimp_5844_, v___y_5845_, v___y_5846_, v___y_5847_, v___y_5848_, v___y_5849_, v___y_5850_);
lean_dec(v___y_5850_);
lean_dec_ref(v___y_5849_);
lean_dec(v___y_5848_);
lean_dec_ref(v___y_5847_);
lean_dec(v___y_5846_);
lean_dec_ref(v___y_5845_);
return v_res_5853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal(lean_object* v_mvarId_5854_, uint8_t v_simplifyTarget_5855_, lean_object* v_fvarIdsToSimp_5856_, lean_object* v_a_5857_, lean_object* v_a_5858_, lean_object* v_a_5859_, lean_object* v_a_5860_){
_start:
{
lean_object* v___x_5862_; lean_object* v___f_5863_; lean_object* v___x_5864_; 
v___x_5862_ = lean_box(v_simplifyTarget_5855_);
v___f_5863_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___boxed), 10, 3);
lean_closure_set(v___f_5863_, 0, v_mvarId_5854_);
lean_closure_set(v___f_5863_, 1, v___x_5862_);
lean_closure_set(v___f_5863_, 2, v_fvarIdsToSimp_5856_);
v___x_5864_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_5863_, v_a_5857_, v_a_5858_, v_a_5859_, v_a_5860_);
return v___x_5864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___boxed(lean_object* v_mvarId_5865_, lean_object* v_simplifyTarget_5866_, lean_object* v_fvarIdsToSimp_5867_, lean_object* v_a_5868_, lean_object* v_a_5869_, lean_object* v_a_5870_, lean_object* v_a_5871_, lean_object* v_a_5872_){
_start:
{
uint8_t v_simplifyTarget_boxed_5873_; lean_object* v_res_5874_; 
v_simplifyTarget_boxed_5873_ = lean_unbox(v_simplifyTarget_5866_);
v_res_5874_ = l_Lean_Meta_Tactic_Cbv_cbvGoal(v_mvarId_5865_, v_simplifyTarget_boxed_5873_, v_fvarIdsToSimp_5867_, v_a_5868_, v_a_5869_, v_a_5870_, v_a_5871_);
lean_dec(v_a_5871_);
lean_dec_ref(v_a_5870_);
lean_dec(v_a_5869_);
lean_dec_ref(v_a_5868_);
return v_res_5874_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5876_; lean_object* v___x_5877_; 
v___x_5876_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0___closed__0));
v___x_5877_ = l_Lean_stringToMessageData(v___x_5876_);
return v___x_5877_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5879_; lean_object* v___x_5880_; 
v___x_5879_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0___closed__2));
v___x_5880_ = l_Lean_stringToMessageData(v___x_5879_);
return v___x_5880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0(lean_object* v_x_5881_, lean_object* v___y_5882_, lean_object* v___y_5883_, lean_object* v___y_5884_, lean_object* v___y_5885_){
_start:
{
if (lean_obj_tag(v_x_5881_) == 0)
{
lean_object* v_a_5887_; lean_object* v___x_5889_; uint8_t v_isShared_5890_; uint8_t v_isSharedCheck_5897_; 
v_a_5887_ = lean_ctor_get(v_x_5881_, 0);
v_isSharedCheck_5897_ = !lean_is_exclusive(v_x_5881_);
if (v_isSharedCheck_5897_ == 0)
{
v___x_5889_ = v_x_5881_;
v_isShared_5890_ = v_isSharedCheck_5897_;
goto v_resetjp_5888_;
}
else
{
lean_inc(v_a_5887_);
lean_dec(v_x_5881_);
v___x_5889_ = lean_box(0);
v_isShared_5890_ = v_isSharedCheck_5897_;
goto v_resetjp_5888_;
}
v_resetjp_5888_:
{
lean_object* v___x_5891_; lean_object* v___x_5892_; lean_object* v___x_5893_; lean_object* v___x_5895_; 
v___x_5891_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0___closed__1);
v___x_5892_ = l_Lean_Exception_toMessageData(v_a_5887_);
v___x_5893_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5893_, 0, v___x_5891_);
lean_ctor_set(v___x_5893_, 1, v___x_5892_);
if (v_isShared_5890_ == 0)
{
lean_ctor_set(v___x_5889_, 0, v___x_5893_);
v___x_5895_ = v___x_5889_;
goto v_reusejp_5894_;
}
else
{
lean_object* v_reuseFailAlloc_5896_; 
v_reuseFailAlloc_5896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5896_, 0, v___x_5893_);
v___x_5895_ = v_reuseFailAlloc_5896_;
goto v_reusejp_5894_;
}
v_reusejp_5894_:
{
return v___x_5895_;
}
}
}
else
{
lean_object* v___x_5899_; uint8_t v_isShared_5900_; uint8_t v_isSharedCheck_5905_; 
v_isSharedCheck_5905_ = !lean_is_exclusive(v_x_5881_);
if (v_isSharedCheck_5905_ == 0)
{
lean_object* v_unused_5906_; 
v_unused_5906_ = lean_ctor_get(v_x_5881_, 0);
lean_dec(v_unused_5906_);
v___x_5899_ = v_x_5881_;
v_isShared_5900_ = v_isSharedCheck_5905_;
goto v_resetjp_5898_;
}
else
{
lean_dec(v_x_5881_);
v___x_5899_ = lean_box(0);
v_isShared_5900_ = v_isSharedCheck_5905_;
goto v_resetjp_5898_;
}
v_resetjp_5898_:
{
lean_object* v___x_5901_; lean_object* v___x_5903_; 
v___x_5901_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0___closed__3, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0___closed__3);
if (v_isShared_5900_ == 0)
{
lean_ctor_set_tag(v___x_5899_, 0);
lean_ctor_set(v___x_5899_, 0, v___x_5901_);
v___x_5903_ = v___x_5899_;
goto v_reusejp_5902_;
}
else
{
lean_object* v_reuseFailAlloc_5904_; 
v_reuseFailAlloc_5904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5904_, 0, v___x_5901_);
v___x_5903_ = v_reuseFailAlloc_5904_;
goto v_reusejp_5902_;
}
v_reusejp_5902_:
{
return v___x_5903_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0___boxed(lean_object* v_x_5907_, lean_object* v___y_5908_, lean_object* v___y_5909_, lean_object* v___y_5910_, lean_object* v___y_5911_, lean_object* v___y_5912_){
_start:
{
lean_object* v_res_5913_; 
v_res_5913_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0(v_x_5907_, v___y_5908_, v___y_5909_, v___y_5910_, v___y_5911_);
lean_dec(v___y_5911_);
lean_dec_ref(v___y_5910_);
lean_dec(v___y_5909_);
lean_dec_ref(v___y_5908_);
return v_res_5913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1(lean_object* v_a_5914_, uint8_t v___x_5915_, lean_object* v___y_5916_, lean_object* v___y_5917_, lean_object* v___y_5918_, lean_object* v___y_5919_, lean_object* v___y_5920_, lean_object* v___y_5921_){
_start:
{
lean_object* v___x_5923_; 
v___x_5923_ = l_Lean_MVarId_refl(v_a_5914_, v___x_5915_, v___y_5918_, v___y_5919_, v___y_5920_, v___y_5921_);
return v___x_5923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___boxed(lean_object* v_a_5924_, lean_object* v___x_5925_, lean_object* v___y_5926_, lean_object* v___y_5927_, lean_object* v___y_5928_, lean_object* v___y_5929_, lean_object* v___y_5930_, lean_object* v___y_5931_, lean_object* v___y_5932_){
_start:
{
uint8_t v___x_24965__boxed_5933_; lean_object* v_res_5934_; 
v___x_24965__boxed_5933_ = lean_unbox(v___x_5925_);
v_res_5934_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1(v_a_5924_, v___x_24965__boxed_5933_, v___y_5926_, v___y_5927_, v___y_5928_, v___y_5929_, v___y_5930_, v___y_5931_);
lean_dec(v___y_5931_);
lean_dec_ref(v___y_5930_);
lean_dec(v___y_5929_);
lean_dec_ref(v___y_5928_);
lean_dec(v___y_5927_);
lean_dec_ref(v___y_5926_);
return v_res_5934_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2___redArg(lean_object* v_cls_5935_, lean_object* v_msg_5936_, lean_object* v___y_5937_, lean_object* v___y_5938_, lean_object* v___y_5939_, lean_object* v___y_5940_){
_start:
{
lean_object* v_ref_5942_; lean_object* v___x_5943_; lean_object* v_a_5944_; lean_object* v___x_5946_; uint8_t v_isShared_5947_; uint8_t v_isSharedCheck_5988_; 
v_ref_5942_ = lean_ctor_get(v___y_5939_, 5);
v___x_5943_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0_spec__0(v_msg_5936_, v___y_5937_, v___y_5938_, v___y_5939_, v___y_5940_);
v_a_5944_ = lean_ctor_get(v___x_5943_, 0);
v_isSharedCheck_5988_ = !lean_is_exclusive(v___x_5943_);
if (v_isSharedCheck_5988_ == 0)
{
v___x_5946_ = v___x_5943_;
v_isShared_5947_ = v_isSharedCheck_5988_;
goto v_resetjp_5945_;
}
else
{
lean_inc(v_a_5944_);
lean_dec(v___x_5943_);
v___x_5946_ = lean_box(0);
v_isShared_5947_ = v_isSharedCheck_5988_;
goto v_resetjp_5945_;
}
v_resetjp_5945_:
{
lean_object* v___x_5948_; lean_object* v_traceState_5949_; lean_object* v_env_5950_; lean_object* v_nextMacroScope_5951_; lean_object* v_ngen_5952_; lean_object* v_auxDeclNGen_5953_; lean_object* v_cache_5954_; lean_object* v_messages_5955_; lean_object* v_infoState_5956_; lean_object* v_snapshotTasks_5957_; lean_object* v___x_5959_; uint8_t v_isShared_5960_; uint8_t v_isSharedCheck_5987_; 
v___x_5948_ = lean_st_ref_take(v___y_5940_);
v_traceState_5949_ = lean_ctor_get(v___x_5948_, 4);
v_env_5950_ = lean_ctor_get(v___x_5948_, 0);
v_nextMacroScope_5951_ = lean_ctor_get(v___x_5948_, 1);
v_ngen_5952_ = lean_ctor_get(v___x_5948_, 2);
v_auxDeclNGen_5953_ = lean_ctor_get(v___x_5948_, 3);
v_cache_5954_ = lean_ctor_get(v___x_5948_, 5);
v_messages_5955_ = lean_ctor_get(v___x_5948_, 6);
v_infoState_5956_ = lean_ctor_get(v___x_5948_, 7);
v_snapshotTasks_5957_ = lean_ctor_get(v___x_5948_, 8);
v_isSharedCheck_5987_ = !lean_is_exclusive(v___x_5948_);
if (v_isSharedCheck_5987_ == 0)
{
v___x_5959_ = v___x_5948_;
v_isShared_5960_ = v_isSharedCheck_5987_;
goto v_resetjp_5958_;
}
else
{
lean_inc(v_snapshotTasks_5957_);
lean_inc(v_infoState_5956_);
lean_inc(v_messages_5955_);
lean_inc(v_cache_5954_);
lean_inc(v_traceState_5949_);
lean_inc(v_auxDeclNGen_5953_);
lean_inc(v_ngen_5952_);
lean_inc(v_nextMacroScope_5951_);
lean_inc(v_env_5950_);
lean_dec(v___x_5948_);
v___x_5959_ = lean_box(0);
v_isShared_5960_ = v_isSharedCheck_5987_;
goto v_resetjp_5958_;
}
v_resetjp_5958_:
{
uint64_t v_tid_5961_; lean_object* v_traces_5962_; lean_object* v___x_5964_; uint8_t v_isShared_5965_; uint8_t v_isSharedCheck_5986_; 
v_tid_5961_ = lean_ctor_get_uint64(v_traceState_5949_, sizeof(void*)*1);
v_traces_5962_ = lean_ctor_get(v_traceState_5949_, 0);
v_isSharedCheck_5986_ = !lean_is_exclusive(v_traceState_5949_);
if (v_isSharedCheck_5986_ == 0)
{
v___x_5964_ = v_traceState_5949_;
v_isShared_5965_ = v_isSharedCheck_5986_;
goto v_resetjp_5963_;
}
else
{
lean_inc(v_traces_5962_);
lean_dec(v_traceState_5949_);
v___x_5964_ = lean_box(0);
v_isShared_5965_ = v_isSharedCheck_5986_;
goto v_resetjp_5963_;
}
v_resetjp_5963_:
{
lean_object* v___x_5966_; double v___x_5967_; uint8_t v___x_5968_; lean_object* v___x_5969_; lean_object* v___x_5970_; lean_object* v___x_5971_; lean_object* v___x_5972_; lean_object* v___x_5973_; lean_object* v___x_5974_; lean_object* v___x_5976_; 
v___x_5966_ = lean_box(0);
v___x_5967_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0);
v___x_5968_ = 0;
v___x_5969_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__1));
v___x_5970_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_5970_, 0, v_cls_5935_);
lean_ctor_set(v___x_5970_, 1, v___x_5966_);
lean_ctor_set(v___x_5970_, 2, v___x_5969_);
lean_ctor_set_float(v___x_5970_, sizeof(void*)*3, v___x_5967_);
lean_ctor_set_float(v___x_5970_, sizeof(void*)*3 + 8, v___x_5967_);
lean_ctor_set_uint8(v___x_5970_, sizeof(void*)*3 + 16, v___x_5968_);
v___x_5971_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__2));
v___x_5972_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_5972_, 0, v___x_5970_);
lean_ctor_set(v___x_5972_, 1, v_a_5944_);
lean_ctor_set(v___x_5972_, 2, v___x_5971_);
lean_inc(v_ref_5942_);
v___x_5973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5973_, 0, v_ref_5942_);
lean_ctor_set(v___x_5973_, 1, v___x_5972_);
v___x_5974_ = l_Lean_PersistentArray_push___redArg(v_traces_5962_, v___x_5973_);
if (v_isShared_5965_ == 0)
{
lean_ctor_set(v___x_5964_, 0, v___x_5974_);
v___x_5976_ = v___x_5964_;
goto v_reusejp_5975_;
}
else
{
lean_object* v_reuseFailAlloc_5985_; 
v_reuseFailAlloc_5985_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5985_, 0, v___x_5974_);
lean_ctor_set_uint64(v_reuseFailAlloc_5985_, sizeof(void*)*1, v_tid_5961_);
v___x_5976_ = v_reuseFailAlloc_5985_;
goto v_reusejp_5975_;
}
v_reusejp_5975_:
{
lean_object* v___x_5978_; 
if (v_isShared_5960_ == 0)
{
lean_ctor_set(v___x_5959_, 4, v___x_5976_);
v___x_5978_ = v___x_5959_;
goto v_reusejp_5977_;
}
else
{
lean_object* v_reuseFailAlloc_5984_; 
v_reuseFailAlloc_5984_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5984_, 0, v_env_5950_);
lean_ctor_set(v_reuseFailAlloc_5984_, 1, v_nextMacroScope_5951_);
lean_ctor_set(v_reuseFailAlloc_5984_, 2, v_ngen_5952_);
lean_ctor_set(v_reuseFailAlloc_5984_, 3, v_auxDeclNGen_5953_);
lean_ctor_set(v_reuseFailAlloc_5984_, 4, v___x_5976_);
lean_ctor_set(v_reuseFailAlloc_5984_, 5, v_cache_5954_);
lean_ctor_set(v_reuseFailAlloc_5984_, 6, v_messages_5955_);
lean_ctor_set(v_reuseFailAlloc_5984_, 7, v_infoState_5956_);
lean_ctor_set(v_reuseFailAlloc_5984_, 8, v_snapshotTasks_5957_);
v___x_5978_ = v_reuseFailAlloc_5984_;
goto v_reusejp_5977_;
}
v_reusejp_5977_:
{
lean_object* v___x_5979_; lean_object* v___x_5980_; lean_object* v___x_5982_; 
v___x_5979_ = lean_st_ref_set(v___y_5940_, v___x_5978_);
v___x_5980_ = lean_box(0);
if (v_isShared_5947_ == 0)
{
lean_ctor_set(v___x_5946_, 0, v___x_5980_);
v___x_5982_ = v___x_5946_;
goto v_reusejp_5981_;
}
else
{
lean_object* v_reuseFailAlloc_5983_; 
v_reuseFailAlloc_5983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5983_, 0, v___x_5980_);
v___x_5982_ = v_reuseFailAlloc_5983_;
goto v_reusejp_5981_;
}
v_reusejp_5981_:
{
return v___x_5982_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2___redArg___boxed(lean_object* v_cls_5989_, lean_object* v_msg_5990_, lean_object* v___y_5991_, lean_object* v___y_5992_, lean_object* v___y_5993_, lean_object* v___y_5994_, lean_object* v___y_5995_){
_start:
{
lean_object* v_res_5996_; 
v_res_5996_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2___redArg(v_cls_5989_, v_msg_5990_, v___y_5991_, v___y_5992_, v___y_5993_, v___y_5994_);
lean_dec(v___y_5994_);
lean_dec_ref(v___y_5993_);
lean_dec(v___y_5992_);
lean_dec_ref(v___y_5991_);
return v_res_5996_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(lean_object* v_msg_5997_, lean_object* v___y_5998_, lean_object* v___y_5999_, lean_object* v___y_6000_, lean_object* v___y_6001_){
_start:
{
lean_object* v_ref_6003_; lean_object* v___x_6004_; lean_object* v_a_6005_; lean_object* v___x_6007_; uint8_t v_isShared_6008_; uint8_t v_isSharedCheck_6013_; 
v_ref_6003_ = lean_ctor_get(v___y_6000_, 5);
v___x_6004_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0_spec__0(v_msg_5997_, v___y_5998_, v___y_5999_, v___y_6000_, v___y_6001_);
v_a_6005_ = lean_ctor_get(v___x_6004_, 0);
v_isSharedCheck_6013_ = !lean_is_exclusive(v___x_6004_);
if (v_isSharedCheck_6013_ == 0)
{
v___x_6007_ = v___x_6004_;
v_isShared_6008_ = v_isSharedCheck_6013_;
goto v_resetjp_6006_;
}
else
{
lean_inc(v_a_6005_);
lean_dec(v___x_6004_);
v___x_6007_ = lean_box(0);
v_isShared_6008_ = v_isSharedCheck_6013_;
goto v_resetjp_6006_;
}
v_resetjp_6006_:
{
lean_object* v___x_6009_; lean_object* v___x_6011_; 
lean_inc(v_ref_6003_);
v___x_6009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6009_, 0, v_ref_6003_);
lean_ctor_set(v___x_6009_, 1, v_a_6005_);
if (v_isShared_6008_ == 0)
{
lean_ctor_set_tag(v___x_6007_, 1);
lean_ctor_set(v___x_6007_, 0, v___x_6009_);
v___x_6011_ = v___x_6007_;
goto v_reusejp_6010_;
}
else
{
lean_object* v_reuseFailAlloc_6012_; 
v_reuseFailAlloc_6012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6012_, 0, v___x_6009_);
v___x_6011_ = v_reuseFailAlloc_6012_;
goto v_reusejp_6010_;
}
v_reusejp_6010_:
{
return v___x_6011_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg___boxed(lean_object* v_msg_6014_, lean_object* v___y_6015_, lean_object* v___y_6016_, lean_object* v___y_6017_, lean_object* v___y_6018_, lean_object* v___y_6019_){
_start:
{
lean_object* v_res_6020_; 
v_res_6020_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(v_msg_6014_, v___y_6015_, v___y_6016_, v___y_6017_, v___y_6018_);
lean_dec(v___y_6018_);
lean_dec_ref(v___y_6017_);
lean_dec(v___y_6016_);
lean_dec_ref(v___y_6015_);
return v_res_6020_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__1(void){
_start:
{
lean_object* v___x_6022_; lean_object* v___x_6023_; 
v___x_6022_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__0));
v___x_6023_ = l_Lean_stringToMessageData(v___x_6022_);
return v___x_6023_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__3(void){
_start:
{
lean_object* v___x_6025_; lean_object* v___x_6026_; 
v___x_6025_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__2));
v___x_6026_ = l_Lean_stringToMessageData(v___x_6025_);
return v___x_6026_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__6(void){
_start:
{
lean_object* v___x_6030_; lean_object* v___x_6031_; 
v___x_6030_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__5));
v___x_6031_ = l_Lean_stringToMessageData(v___x_6030_);
return v___x_6031_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__8(void){
_start:
{
lean_object* v___x_6033_; lean_object* v___x_6034_; 
v___x_6033_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__7));
v___x_6034_ = l_Lean_stringToMessageData(v___x_6033_);
return v___x_6034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2(lean_object* v_m_6035_, lean_object* v___x_6036_, lean_object* v_cls_6037_, lean_object* v___y_6038_, lean_object* v___y_6039_, lean_object* v___y_6040_, lean_object* v___y_6041_, lean_object* v___y_6042_, lean_object* v___y_6043_){
_start:
{
lean_object* v_e_6046_; lean_object* v_onTrue_6047_; lean_object* v___y_6048_; lean_object* v___y_6049_; lean_object* v___y_6050_; lean_object* v___y_6051_; lean_object* v___y_6052_; lean_object* v___y_6053_; lean_object* v___x_6083_; 
v___x_6083_ = l_Lean_Meta_Sym_preprocessMVar(v_m_6035_, v___y_6038_, v___y_6039_, v___y_6040_, v___y_6041_, v___y_6042_, v___y_6043_);
if (lean_obj_tag(v___x_6083_) == 0)
{
lean_object* v_a_6084_; lean_object* v___x_6085_; 
v_a_6084_ = lean_ctor_get(v___x_6083_, 0);
lean_inc_n(v_a_6084_, 2);
lean_dec_ref_known(v___x_6083_, 1);
v___x_6085_ = l_Lean_MVarId_getType(v_a_6084_, v___y_6040_, v___y_6041_, v___y_6042_, v___y_6043_);
if (lean_obj_tag(v___x_6085_) == 0)
{
lean_object* v_a_6086_; lean_object* v___x_6087_; lean_object* v___x_6088_; uint8_t v___x_6089_; 
v_a_6086_ = lean_ctor_get(v___x_6085_, 0);
lean_inc(v_a_6086_);
lean_dec_ref_known(v___x_6085_, 1);
v___x_6087_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__4));
v___x_6088_ = lean_unsigned_to_nat(3u);
v___x_6089_ = l_Lean_Expr_isAppOfArity(v_a_6086_, v___x_6087_, v___x_6088_);
if (v___x_6089_ == 0)
{
lean_object* v___x_6090_; lean_object* v___x_6091_; lean_object* v___x_6092_; lean_object* v___x_6093_; 
lean_dec(v_a_6084_);
lean_dec(v_cls_6037_);
lean_dec_ref(v___x_6036_);
v___x_6090_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__6, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__6);
v___x_6091_ = l_Lean_indentExpr(v_a_6086_);
v___x_6092_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6092_, 0, v___x_6090_);
lean_ctor_set(v___x_6092_, 1, v___x_6091_);
v___x_6093_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(v___x_6092_, v___y_6040_, v___y_6041_, v___y_6042_, v___y_6043_);
return v___x_6093_;
}
else
{
lean_object* v___x_6094_; lean_object* v___x_6095_; lean_object* v___x_6096_; 
v___x_6094_ = l_Lean_Expr_appFn_x21(v_a_6086_);
lean_dec(v_a_6086_);
v___x_6095_ = l_Lean_Expr_appArg_x21(v___x_6094_);
lean_dec_ref(v___x_6094_);
lean_inc_ref(v___x_6095_);
v___x_6096_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_6095_, v___x_6036_, v___y_6038_, v___y_6039_, v___y_6040_, v___y_6041_, v___y_6042_, v___y_6043_);
if (lean_obj_tag(v___x_6096_) == 0)
{
lean_object* v_options_6097_; lean_object* v_a_6098_; lean_object* v_inheritedTraceOptions_6099_; uint8_t v_hasTrace_6100_; lean_object* v___x_6101_; lean_object* v___f_6102_; lean_object* v___y_6104_; lean_object* v___y_6105_; lean_object* v___y_6106_; lean_object* v___y_6107_; lean_object* v___y_6108_; lean_object* v___y_6109_; 
v_options_6097_ = lean_ctor_get(v___y_6042_, 2);
v_a_6098_ = lean_ctor_get(v___x_6096_, 0);
lean_inc(v_a_6098_);
lean_dec_ref_known(v___x_6096_, 1);
v_inheritedTraceOptions_6099_ = lean_ctor_get(v___y_6042_, 13);
v_hasTrace_6100_ = lean_ctor_get_uint8(v_options_6097_, sizeof(void*)*1);
v___x_6101_ = lean_box(v___x_6089_);
lean_inc(v_a_6084_);
v___f_6102_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___boxed), 9, 2);
lean_closure_set(v___f_6102_, 0, v_a_6084_);
lean_closure_set(v___f_6102_, 1, v___x_6101_);
if (v_hasTrace_6100_ == 0)
{
lean_dec(v_cls_6037_);
v___y_6104_ = v___y_6038_;
v___y_6105_ = v___y_6039_;
v___y_6106_ = v___y_6040_;
v___y_6107_ = v___y_6041_;
v___y_6108_ = v___y_6042_;
v___y_6109_ = v___y_6043_;
goto v___jp_6103_;
}
else
{
lean_object* v___x_6113_; lean_object* v___x_6114_; uint8_t v___x_6115_; 
v___x_6113_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__3));
lean_inc(v_cls_6037_);
v___x_6114_ = l_Lean_Name_append(v___x_6113_, v_cls_6037_);
v___x_6115_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6099_, v_options_6097_, v___x_6114_);
lean_dec(v___x_6114_);
if (v___x_6115_ == 0)
{
lean_dec(v_cls_6037_);
v___y_6104_ = v___y_6038_;
v___y_6105_ = v___y_6039_;
v___y_6106_ = v___y_6040_;
v___y_6107_ = v___y_6041_;
v___y_6108_ = v___y_6042_;
v___y_6109_ = v___y_6043_;
goto v___jp_6103_;
}
else
{
lean_object* v___x_6116_; lean_object* v___x_6117_; lean_object* v___x_6118_; lean_object* v___x_6119_; lean_object* v___x_6120_; lean_object* v___x_6121_; lean_object* v___x_6122_; lean_object* v___x_6123_; lean_object* v___x_6124_; 
v___x_6116_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__8, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__8_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__8);
lean_inc_ref(v___x_6095_);
v___x_6117_ = l_Lean_indentExpr(v___x_6095_);
v___x_6118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6118_, 0, v___x_6116_);
lean_ctor_set(v___x_6118_, 1, v___x_6117_);
v___x_6119_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_6120_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6120_, 0, v___x_6118_);
lean_ctor_set(v___x_6120_, 1, v___x_6119_);
v___x_6121_ = l_Lean_Meta_Sym_Simp_Result_getResultExpr(v___x_6095_, v_a_6098_);
v___x_6122_ = l_Lean_indentExpr(v___x_6121_);
v___x_6123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6123_, 0, v___x_6120_);
lean_ctor_set(v___x_6123_, 1, v___x_6122_);
v___x_6124_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2___redArg(v_cls_6037_, v___x_6123_, v___y_6040_, v___y_6041_, v___y_6042_, v___y_6043_);
if (lean_obj_tag(v___x_6124_) == 0)
{
lean_dec_ref_known(v___x_6124_, 1);
v___y_6104_ = v___y_6038_;
v___y_6105_ = v___y_6039_;
v___y_6106_ = v___y_6040_;
v___y_6107_ = v___y_6041_;
v___y_6108_ = v___y_6042_;
v___y_6109_ = v___y_6043_;
goto v___jp_6103_;
}
else
{
lean_dec_ref(v___f_6102_);
lean_dec(v_a_6098_);
lean_dec_ref(v___x_6095_);
lean_dec(v_a_6084_);
return v___x_6124_;
}
}
}
v___jp_6103_:
{
if (lean_obj_tag(v_a_6098_) == 0)
{
lean_dec_ref_known(v_a_6098_, 0);
lean_dec(v_a_6084_);
v_e_6046_ = v___x_6095_;
v_onTrue_6047_ = v___f_6102_;
v___y_6048_ = v___y_6104_;
v___y_6049_ = v___y_6105_;
v___y_6050_ = v___y_6106_;
v___y_6051_ = v___y_6107_;
v___y_6052_ = v___y_6108_;
v___y_6053_ = v___y_6109_;
goto v___jp_6045_;
}
else
{
lean_object* v_e_x27_6110_; lean_object* v_proof_6111_; lean_object* v___x_6112_; 
lean_dec_ref(v___f_6102_);
lean_dec_ref(v___x_6095_);
v_e_x27_6110_ = lean_ctor_get(v_a_6098_, 0);
lean_inc_ref(v_e_x27_6110_);
v_proof_6111_ = lean_ctor_get(v_a_6098_, 1);
lean_inc_ref(v_proof_6111_);
lean_dec_ref_known(v_a_6098_, 2);
v___x_6112_ = lean_alloc_closure((void*)(l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___boxed), 9, 2);
lean_closure_set(v___x_6112_, 0, v_a_6084_);
lean_closure_set(v___x_6112_, 1, v_proof_6111_);
v_e_6046_ = v_e_x27_6110_;
v_onTrue_6047_ = v___x_6112_;
v___y_6048_ = v___y_6104_;
v___y_6049_ = v___y_6105_;
v___y_6050_ = v___y_6106_;
v___y_6051_ = v___y_6107_;
v___y_6052_ = v___y_6108_;
v___y_6053_ = v___y_6109_;
goto v___jp_6045_;
}
}
}
else
{
lean_object* v_a_6125_; lean_object* v___x_6127_; uint8_t v_isShared_6128_; uint8_t v_isSharedCheck_6132_; 
lean_dec_ref(v___x_6095_);
lean_dec(v_a_6084_);
lean_dec(v_cls_6037_);
v_a_6125_ = lean_ctor_get(v___x_6096_, 0);
v_isSharedCheck_6132_ = !lean_is_exclusive(v___x_6096_);
if (v_isSharedCheck_6132_ == 0)
{
v___x_6127_ = v___x_6096_;
v_isShared_6128_ = v_isSharedCheck_6132_;
goto v_resetjp_6126_;
}
else
{
lean_inc(v_a_6125_);
lean_dec(v___x_6096_);
v___x_6127_ = lean_box(0);
v_isShared_6128_ = v_isSharedCheck_6132_;
goto v_resetjp_6126_;
}
v_resetjp_6126_:
{
lean_object* v___x_6130_; 
if (v_isShared_6128_ == 0)
{
v___x_6130_ = v___x_6127_;
goto v_reusejp_6129_;
}
else
{
lean_object* v_reuseFailAlloc_6131_; 
v_reuseFailAlloc_6131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6131_, 0, v_a_6125_);
v___x_6130_ = v_reuseFailAlloc_6131_;
goto v_reusejp_6129_;
}
v_reusejp_6129_:
{
return v___x_6130_;
}
}
}
}
}
else
{
lean_object* v_a_6133_; lean_object* v___x_6135_; uint8_t v_isShared_6136_; uint8_t v_isSharedCheck_6140_; 
lean_dec(v_a_6084_);
lean_dec(v_cls_6037_);
lean_dec_ref(v___x_6036_);
v_a_6133_ = lean_ctor_get(v___x_6085_, 0);
v_isSharedCheck_6140_ = !lean_is_exclusive(v___x_6085_);
if (v_isSharedCheck_6140_ == 0)
{
v___x_6135_ = v___x_6085_;
v_isShared_6136_ = v_isSharedCheck_6140_;
goto v_resetjp_6134_;
}
else
{
lean_inc(v_a_6133_);
lean_dec(v___x_6085_);
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
lean_dec(v_cls_6037_);
lean_dec_ref(v___x_6036_);
v_a_6141_ = lean_ctor_get(v___x_6083_, 0);
v_isSharedCheck_6148_ = !lean_is_exclusive(v___x_6083_);
if (v_isSharedCheck_6148_ == 0)
{
v___x_6143_ = v___x_6083_;
v_isShared_6144_ = v_isSharedCheck_6148_;
goto v_resetjp_6142_;
}
else
{
lean_inc(v_a_6141_);
lean_dec(v___x_6083_);
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
v___jp_6045_:
{
lean_object* v___x_6054_; 
v___x_6054_ = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(v_e_6046_, v___y_6048_);
if (lean_obj_tag(v___x_6054_) == 0)
{
lean_object* v_a_6055_; uint8_t v___x_6056_; 
v_a_6055_ = lean_ctor_get(v___x_6054_, 0);
lean_inc(v_a_6055_);
lean_dec_ref_known(v___x_6054_, 1);
v___x_6056_ = lean_unbox(v_a_6055_);
lean_dec(v_a_6055_);
if (v___x_6056_ == 0)
{
lean_object* v___x_6057_; 
lean_dec_ref(v_onTrue_6047_);
v___x_6057_ = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(v_e_6046_, v___y_6048_);
if (lean_obj_tag(v___x_6057_) == 0)
{
lean_object* v_a_6058_; uint8_t v___x_6059_; 
v_a_6058_ = lean_ctor_get(v___x_6057_, 0);
lean_inc(v_a_6058_);
lean_dec_ref_known(v___x_6057_, 1);
v___x_6059_ = lean_unbox(v_a_6058_);
lean_dec(v_a_6058_);
if (v___x_6059_ == 0)
{
lean_object* v___x_6060_; lean_object* v___x_6061_; lean_object* v___x_6062_; lean_object* v___x_6063_; 
v___x_6060_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__1);
v___x_6061_ = l_Lean_indentExpr(v_e_6046_);
v___x_6062_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6062_, 0, v___x_6060_);
lean_ctor_set(v___x_6062_, 1, v___x_6061_);
v___x_6063_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(v___x_6062_, v___y_6050_, v___y_6051_, v___y_6052_, v___y_6053_);
return v___x_6063_;
}
else
{
lean_object* v___x_6064_; lean_object* v___x_6065_; 
lean_dec_ref(v_e_6046_);
v___x_6064_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__3, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__3);
v___x_6065_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(v___x_6064_, v___y_6050_, v___y_6051_, v___y_6052_, v___y_6053_);
return v___x_6065_;
}
}
else
{
lean_object* v_a_6066_; lean_object* v___x_6068_; uint8_t v_isShared_6069_; uint8_t v_isSharedCheck_6073_; 
lean_dec_ref(v_e_6046_);
v_a_6066_ = lean_ctor_get(v___x_6057_, 0);
v_isSharedCheck_6073_ = !lean_is_exclusive(v___x_6057_);
if (v_isSharedCheck_6073_ == 0)
{
v___x_6068_ = v___x_6057_;
v_isShared_6069_ = v_isSharedCheck_6073_;
goto v_resetjp_6067_;
}
else
{
lean_inc(v_a_6066_);
lean_dec(v___x_6057_);
v___x_6068_ = lean_box(0);
v_isShared_6069_ = v_isSharedCheck_6073_;
goto v_resetjp_6067_;
}
v_resetjp_6067_:
{
lean_object* v___x_6071_; 
if (v_isShared_6069_ == 0)
{
v___x_6071_ = v___x_6068_;
goto v_reusejp_6070_;
}
else
{
lean_object* v_reuseFailAlloc_6072_; 
v_reuseFailAlloc_6072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6072_, 0, v_a_6066_);
v___x_6071_ = v_reuseFailAlloc_6072_;
goto v_reusejp_6070_;
}
v_reusejp_6070_:
{
return v___x_6071_;
}
}
}
}
else
{
lean_object* v___x_6074_; 
lean_dec_ref(v_e_6046_);
lean_inc(v___y_6053_);
lean_inc_ref(v___y_6052_);
lean_inc(v___y_6051_);
lean_inc_ref(v___y_6050_);
lean_inc(v___y_6049_);
lean_inc_ref(v___y_6048_);
v___x_6074_ = lean_apply_7(v_onTrue_6047_, v___y_6048_, v___y_6049_, v___y_6050_, v___y_6051_, v___y_6052_, v___y_6053_, lean_box(0));
return v___x_6074_;
}
}
else
{
lean_object* v_a_6075_; lean_object* v___x_6077_; uint8_t v_isShared_6078_; uint8_t v_isSharedCheck_6082_; 
lean_dec_ref(v_onTrue_6047_);
lean_dec_ref(v_e_6046_);
v_a_6075_ = lean_ctor_get(v___x_6054_, 0);
v_isSharedCheck_6082_ = !lean_is_exclusive(v___x_6054_);
if (v_isSharedCheck_6082_ == 0)
{
v___x_6077_ = v___x_6054_;
v_isShared_6078_ = v_isSharedCheck_6082_;
goto v_resetjp_6076_;
}
else
{
lean_inc(v_a_6075_);
lean_dec(v___x_6054_);
v___x_6077_ = lean_box(0);
v_isShared_6078_ = v_isSharedCheck_6082_;
goto v_resetjp_6076_;
}
v_resetjp_6076_:
{
lean_object* v___x_6080_; 
if (v_isShared_6078_ == 0)
{
v___x_6080_ = v___x_6077_;
goto v_reusejp_6079_;
}
else
{
lean_object* v_reuseFailAlloc_6081_; 
v_reuseFailAlloc_6081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6081_, 0, v_a_6075_);
v___x_6080_ = v_reuseFailAlloc_6081_;
goto v_reusejp_6079_;
}
v_reusejp_6079_:
{
return v___x_6080_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___boxed(lean_object* v_m_6149_, lean_object* v___x_6150_, lean_object* v_cls_6151_, lean_object* v___y_6152_, lean_object* v___y_6153_, lean_object* v___y_6154_, lean_object* v___y_6155_, lean_object* v___y_6156_, lean_object* v___y_6157_, lean_object* v___y_6158_){
_start:
{
lean_object* v_res_6159_; 
v_res_6159_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2(v_m_6149_, v___x_6150_, v_cls_6151_, v___y_6152_, v___y_6153_, v___y_6154_, v___y_6155_, v___y_6156_, v___y_6157_);
lean_dec(v___y_6157_);
lean_dec_ref(v___y_6156_);
lean_dec(v___y_6155_);
lean_dec_ref(v___y_6154_);
lean_dec(v___y_6153_);
lean_dec_ref(v___y_6152_);
return v_res_6159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__4(lean_object* v_m_6160_, lean_object* v___x_6161_, uint8_t v___x_6162_, lean_object* v_cls_6163_, lean_object* v___y_6164_, lean_object* v___y_6165_, lean_object* v___y_6166_, lean_object* v___y_6167_, lean_object* v___y_6168_, lean_object* v___y_6169_){
_start:
{
lean_object* v_e_6172_; lean_object* v_onTrue_6173_; lean_object* v___y_6174_; lean_object* v___y_6175_; lean_object* v___y_6176_; lean_object* v___y_6177_; lean_object* v___y_6178_; lean_object* v___y_6179_; lean_object* v___x_6209_; 
v___x_6209_ = l_Lean_Meta_Sym_preprocessMVar(v_m_6160_, v___y_6164_, v___y_6165_, v___y_6166_, v___y_6167_, v___y_6168_, v___y_6169_);
if (lean_obj_tag(v___x_6209_) == 0)
{
lean_object* v_a_6210_; lean_object* v___x_6211_; 
v_a_6210_ = lean_ctor_get(v___x_6209_, 0);
lean_inc_n(v_a_6210_, 2);
lean_dec_ref_known(v___x_6209_, 1);
v___x_6211_ = l_Lean_MVarId_getType(v_a_6210_, v___y_6166_, v___y_6167_, v___y_6168_, v___y_6169_);
if (lean_obj_tag(v___x_6211_) == 0)
{
lean_object* v_a_6212_; lean_object* v___x_6213_; lean_object* v___x_6214_; uint8_t v___x_6215_; 
v_a_6212_ = lean_ctor_get(v___x_6211_, 0);
lean_inc(v_a_6212_);
lean_dec_ref_known(v___x_6211_, 1);
v___x_6213_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__4));
v___x_6214_ = lean_unsigned_to_nat(3u);
v___x_6215_ = l_Lean_Expr_isAppOfArity(v_a_6212_, v___x_6213_, v___x_6214_);
if (v___x_6215_ == 0)
{
lean_object* v___x_6216_; lean_object* v___x_6217_; lean_object* v___x_6218_; lean_object* v___x_6219_; 
lean_dec(v_a_6210_);
lean_dec(v_cls_6163_);
lean_dec_ref(v___x_6161_);
v___x_6216_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__6, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__6);
v___x_6217_ = l_Lean_indentExpr(v_a_6212_);
v___x_6218_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6218_, 0, v___x_6216_);
lean_ctor_set(v___x_6218_, 1, v___x_6217_);
v___x_6219_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(v___x_6218_, v___y_6166_, v___y_6167_, v___y_6168_, v___y_6169_);
return v___x_6219_;
}
else
{
lean_object* v___x_6220_; lean_object* v___x_6221_; lean_object* v___x_6222_; 
v___x_6220_ = l_Lean_Expr_appFn_x21(v_a_6212_);
lean_dec(v_a_6212_);
v___x_6221_ = l_Lean_Expr_appArg_x21(v___x_6220_);
lean_dec_ref(v___x_6220_);
lean_inc_ref(v___x_6221_);
v___x_6222_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_6221_, v___x_6161_, v___y_6164_, v___y_6165_, v___y_6166_, v___y_6167_, v___y_6168_, v___y_6169_);
if (lean_obj_tag(v___x_6222_) == 0)
{
lean_object* v_options_6223_; lean_object* v_a_6224_; lean_object* v_inheritedTraceOptions_6225_; uint8_t v_hasTrace_6226_; lean_object* v___x_6227_; lean_object* v___f_6228_; lean_object* v___y_6230_; lean_object* v___y_6231_; lean_object* v___y_6232_; lean_object* v___y_6233_; lean_object* v___y_6234_; lean_object* v___y_6235_; 
v_options_6223_ = lean_ctor_get(v___y_6168_, 2);
v_a_6224_ = lean_ctor_get(v___x_6222_, 0);
lean_inc(v_a_6224_);
lean_dec_ref_known(v___x_6222_, 1);
v_inheritedTraceOptions_6225_ = lean_ctor_get(v___y_6168_, 13);
v_hasTrace_6226_ = lean_ctor_get_uint8(v_options_6223_, sizeof(void*)*1);
v___x_6227_ = lean_box(v___x_6162_);
lean_inc(v_a_6210_);
v___f_6228_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___boxed), 9, 2);
lean_closure_set(v___f_6228_, 0, v_a_6210_);
lean_closure_set(v___f_6228_, 1, v___x_6227_);
if (v_hasTrace_6226_ == 0)
{
lean_dec(v_cls_6163_);
v___y_6230_ = v___y_6164_;
v___y_6231_ = v___y_6165_;
v___y_6232_ = v___y_6166_;
v___y_6233_ = v___y_6167_;
v___y_6234_ = v___y_6168_;
v___y_6235_ = v___y_6169_;
goto v___jp_6229_;
}
else
{
lean_object* v___x_6239_; lean_object* v___x_6240_; uint8_t v___x_6241_; 
v___x_6239_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__3));
lean_inc(v_cls_6163_);
v___x_6240_ = l_Lean_Name_append(v___x_6239_, v_cls_6163_);
v___x_6241_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6225_, v_options_6223_, v___x_6240_);
lean_dec(v___x_6240_);
if (v___x_6241_ == 0)
{
lean_dec(v_cls_6163_);
v___y_6230_ = v___y_6164_;
v___y_6231_ = v___y_6165_;
v___y_6232_ = v___y_6166_;
v___y_6233_ = v___y_6167_;
v___y_6234_ = v___y_6168_;
v___y_6235_ = v___y_6169_;
goto v___jp_6229_;
}
else
{
lean_object* v___x_6242_; lean_object* v___x_6243_; lean_object* v___x_6244_; lean_object* v___x_6245_; lean_object* v___x_6246_; lean_object* v___x_6247_; lean_object* v___x_6248_; lean_object* v___x_6249_; lean_object* v___x_6250_; 
v___x_6242_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__8, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__8_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__8);
lean_inc_ref(v___x_6221_);
v___x_6243_ = l_Lean_indentExpr(v___x_6221_);
v___x_6244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6244_, 0, v___x_6242_);
lean_ctor_set(v___x_6244_, 1, v___x_6243_);
v___x_6245_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_6246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6246_, 0, v___x_6244_);
lean_ctor_set(v___x_6246_, 1, v___x_6245_);
v___x_6247_ = l_Lean_Meta_Sym_Simp_Result_getResultExpr(v___x_6221_, v_a_6224_);
v___x_6248_ = l_Lean_indentExpr(v___x_6247_);
v___x_6249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6249_, 0, v___x_6246_);
lean_ctor_set(v___x_6249_, 1, v___x_6248_);
v___x_6250_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2___redArg(v_cls_6163_, v___x_6249_, v___y_6166_, v___y_6167_, v___y_6168_, v___y_6169_);
if (lean_obj_tag(v___x_6250_) == 0)
{
lean_dec_ref_known(v___x_6250_, 1);
v___y_6230_ = v___y_6164_;
v___y_6231_ = v___y_6165_;
v___y_6232_ = v___y_6166_;
v___y_6233_ = v___y_6167_;
v___y_6234_ = v___y_6168_;
v___y_6235_ = v___y_6169_;
goto v___jp_6229_;
}
else
{
lean_dec_ref(v___f_6228_);
lean_dec(v_a_6224_);
lean_dec_ref(v___x_6221_);
lean_dec(v_a_6210_);
return v___x_6250_;
}
}
}
v___jp_6229_:
{
if (lean_obj_tag(v_a_6224_) == 0)
{
lean_dec_ref_known(v_a_6224_, 0);
lean_dec(v_a_6210_);
v_e_6172_ = v___x_6221_;
v_onTrue_6173_ = v___f_6228_;
v___y_6174_ = v___y_6230_;
v___y_6175_ = v___y_6231_;
v___y_6176_ = v___y_6232_;
v___y_6177_ = v___y_6233_;
v___y_6178_ = v___y_6234_;
v___y_6179_ = v___y_6235_;
goto v___jp_6171_;
}
else
{
lean_object* v_e_x27_6236_; lean_object* v_proof_6237_; lean_object* v___x_6238_; 
lean_dec_ref(v___f_6228_);
lean_dec_ref(v___x_6221_);
v_e_x27_6236_ = lean_ctor_get(v_a_6224_, 0);
lean_inc_ref(v_e_x27_6236_);
v_proof_6237_ = lean_ctor_get(v_a_6224_, 1);
lean_inc_ref(v_proof_6237_);
lean_dec_ref_known(v_a_6224_, 2);
v___x_6238_ = lean_alloc_closure((void*)(l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___boxed), 9, 2);
lean_closure_set(v___x_6238_, 0, v_a_6210_);
lean_closure_set(v___x_6238_, 1, v_proof_6237_);
v_e_6172_ = v_e_x27_6236_;
v_onTrue_6173_ = v___x_6238_;
v___y_6174_ = v___y_6230_;
v___y_6175_ = v___y_6231_;
v___y_6176_ = v___y_6232_;
v___y_6177_ = v___y_6233_;
v___y_6178_ = v___y_6234_;
v___y_6179_ = v___y_6235_;
goto v___jp_6171_;
}
}
}
else
{
lean_object* v_a_6251_; lean_object* v___x_6253_; uint8_t v_isShared_6254_; uint8_t v_isSharedCheck_6258_; 
lean_dec_ref(v___x_6221_);
lean_dec(v_a_6210_);
lean_dec(v_cls_6163_);
v_a_6251_ = lean_ctor_get(v___x_6222_, 0);
v_isSharedCheck_6258_ = !lean_is_exclusive(v___x_6222_);
if (v_isSharedCheck_6258_ == 0)
{
v___x_6253_ = v___x_6222_;
v_isShared_6254_ = v_isSharedCheck_6258_;
goto v_resetjp_6252_;
}
else
{
lean_inc(v_a_6251_);
lean_dec(v___x_6222_);
v___x_6253_ = lean_box(0);
v_isShared_6254_ = v_isSharedCheck_6258_;
goto v_resetjp_6252_;
}
v_resetjp_6252_:
{
lean_object* v___x_6256_; 
if (v_isShared_6254_ == 0)
{
v___x_6256_ = v___x_6253_;
goto v_reusejp_6255_;
}
else
{
lean_object* v_reuseFailAlloc_6257_; 
v_reuseFailAlloc_6257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6257_, 0, v_a_6251_);
v___x_6256_ = v_reuseFailAlloc_6257_;
goto v_reusejp_6255_;
}
v_reusejp_6255_:
{
return v___x_6256_;
}
}
}
}
}
else
{
lean_object* v_a_6259_; lean_object* v___x_6261_; uint8_t v_isShared_6262_; uint8_t v_isSharedCheck_6266_; 
lean_dec(v_a_6210_);
lean_dec(v_cls_6163_);
lean_dec_ref(v___x_6161_);
v_a_6259_ = lean_ctor_get(v___x_6211_, 0);
v_isSharedCheck_6266_ = !lean_is_exclusive(v___x_6211_);
if (v_isSharedCheck_6266_ == 0)
{
v___x_6261_ = v___x_6211_;
v_isShared_6262_ = v_isSharedCheck_6266_;
goto v_resetjp_6260_;
}
else
{
lean_inc(v_a_6259_);
lean_dec(v___x_6211_);
v___x_6261_ = lean_box(0);
v_isShared_6262_ = v_isSharedCheck_6266_;
goto v_resetjp_6260_;
}
v_resetjp_6260_:
{
lean_object* v___x_6264_; 
if (v_isShared_6262_ == 0)
{
v___x_6264_ = v___x_6261_;
goto v_reusejp_6263_;
}
else
{
lean_object* v_reuseFailAlloc_6265_; 
v_reuseFailAlloc_6265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6265_, 0, v_a_6259_);
v___x_6264_ = v_reuseFailAlloc_6265_;
goto v_reusejp_6263_;
}
v_reusejp_6263_:
{
return v___x_6264_;
}
}
}
}
else
{
lean_object* v_a_6267_; lean_object* v___x_6269_; uint8_t v_isShared_6270_; uint8_t v_isSharedCheck_6274_; 
lean_dec(v_cls_6163_);
lean_dec_ref(v___x_6161_);
v_a_6267_ = lean_ctor_get(v___x_6209_, 0);
v_isSharedCheck_6274_ = !lean_is_exclusive(v___x_6209_);
if (v_isSharedCheck_6274_ == 0)
{
v___x_6269_ = v___x_6209_;
v_isShared_6270_ = v_isSharedCheck_6274_;
goto v_resetjp_6268_;
}
else
{
lean_inc(v_a_6267_);
lean_dec(v___x_6209_);
v___x_6269_ = lean_box(0);
v_isShared_6270_ = v_isSharedCheck_6274_;
goto v_resetjp_6268_;
}
v_resetjp_6268_:
{
lean_object* v___x_6272_; 
if (v_isShared_6270_ == 0)
{
v___x_6272_ = v___x_6269_;
goto v_reusejp_6271_;
}
else
{
lean_object* v_reuseFailAlloc_6273_; 
v_reuseFailAlloc_6273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6273_, 0, v_a_6267_);
v___x_6272_ = v_reuseFailAlloc_6273_;
goto v_reusejp_6271_;
}
v_reusejp_6271_:
{
return v___x_6272_;
}
}
}
v___jp_6171_:
{
lean_object* v___x_6180_; 
v___x_6180_ = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(v_e_6172_, v___y_6174_);
if (lean_obj_tag(v___x_6180_) == 0)
{
lean_object* v_a_6181_; uint8_t v___x_6182_; 
v_a_6181_ = lean_ctor_get(v___x_6180_, 0);
lean_inc(v_a_6181_);
lean_dec_ref_known(v___x_6180_, 1);
v___x_6182_ = lean_unbox(v_a_6181_);
lean_dec(v_a_6181_);
if (v___x_6182_ == 0)
{
lean_object* v___x_6183_; 
lean_dec_ref(v_onTrue_6173_);
v___x_6183_ = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(v_e_6172_, v___y_6174_);
if (lean_obj_tag(v___x_6183_) == 0)
{
lean_object* v_a_6184_; uint8_t v___x_6185_; 
v_a_6184_ = lean_ctor_get(v___x_6183_, 0);
lean_inc(v_a_6184_);
lean_dec_ref_known(v___x_6183_, 1);
v___x_6185_ = lean_unbox(v_a_6184_);
lean_dec(v_a_6184_);
if (v___x_6185_ == 0)
{
lean_object* v___x_6186_; lean_object* v___x_6187_; lean_object* v___x_6188_; lean_object* v___x_6189_; 
v___x_6186_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__1);
v___x_6187_ = l_Lean_indentExpr(v_e_6172_);
v___x_6188_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6188_, 0, v___x_6186_);
lean_ctor_set(v___x_6188_, 1, v___x_6187_);
v___x_6189_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(v___x_6188_, v___y_6176_, v___y_6177_, v___y_6178_, v___y_6179_);
return v___x_6189_;
}
else
{
lean_object* v___x_6190_; lean_object* v___x_6191_; 
lean_dec_ref(v_e_6172_);
v___x_6190_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__3, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__3);
v___x_6191_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(v___x_6190_, v___y_6176_, v___y_6177_, v___y_6178_, v___y_6179_);
return v___x_6191_;
}
}
else
{
lean_object* v_a_6192_; lean_object* v___x_6194_; uint8_t v_isShared_6195_; uint8_t v_isSharedCheck_6199_; 
lean_dec_ref(v_e_6172_);
v_a_6192_ = lean_ctor_get(v___x_6183_, 0);
v_isSharedCheck_6199_ = !lean_is_exclusive(v___x_6183_);
if (v_isSharedCheck_6199_ == 0)
{
v___x_6194_ = v___x_6183_;
v_isShared_6195_ = v_isSharedCheck_6199_;
goto v_resetjp_6193_;
}
else
{
lean_inc(v_a_6192_);
lean_dec(v___x_6183_);
v___x_6194_ = lean_box(0);
v_isShared_6195_ = v_isSharedCheck_6199_;
goto v_resetjp_6193_;
}
v_resetjp_6193_:
{
lean_object* v___x_6197_; 
if (v_isShared_6195_ == 0)
{
v___x_6197_ = v___x_6194_;
goto v_reusejp_6196_;
}
else
{
lean_object* v_reuseFailAlloc_6198_; 
v_reuseFailAlloc_6198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6198_, 0, v_a_6192_);
v___x_6197_ = v_reuseFailAlloc_6198_;
goto v_reusejp_6196_;
}
v_reusejp_6196_:
{
return v___x_6197_;
}
}
}
}
else
{
lean_object* v___x_6200_; 
lean_dec_ref(v_e_6172_);
lean_inc(v___y_6179_);
lean_inc_ref(v___y_6178_);
lean_inc(v___y_6177_);
lean_inc_ref(v___y_6176_);
lean_inc(v___y_6175_);
lean_inc_ref(v___y_6174_);
v___x_6200_ = lean_apply_7(v_onTrue_6173_, v___y_6174_, v___y_6175_, v___y_6176_, v___y_6177_, v___y_6178_, v___y_6179_, lean_box(0));
return v___x_6200_;
}
}
else
{
lean_object* v_a_6201_; lean_object* v___x_6203_; uint8_t v_isShared_6204_; uint8_t v_isSharedCheck_6208_; 
lean_dec_ref(v_onTrue_6173_);
lean_dec_ref(v_e_6172_);
v_a_6201_ = lean_ctor_get(v___x_6180_, 0);
v_isSharedCheck_6208_ = !lean_is_exclusive(v___x_6180_);
if (v_isSharedCheck_6208_ == 0)
{
v___x_6203_ = v___x_6180_;
v_isShared_6204_ = v_isSharedCheck_6208_;
goto v_resetjp_6202_;
}
else
{
lean_inc(v_a_6201_);
lean_dec(v___x_6180_);
v___x_6203_ = lean_box(0);
v_isShared_6204_ = v_isSharedCheck_6208_;
goto v_resetjp_6202_;
}
v_resetjp_6202_:
{
lean_object* v___x_6206_; 
if (v_isShared_6204_ == 0)
{
v___x_6206_ = v___x_6203_;
goto v_reusejp_6205_;
}
else
{
lean_object* v_reuseFailAlloc_6207_; 
v_reuseFailAlloc_6207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6207_, 0, v_a_6201_);
v___x_6206_ = v_reuseFailAlloc_6207_;
goto v_reusejp_6205_;
}
v_reusejp_6205_:
{
return v___x_6206_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__4___boxed(lean_object* v_m_6275_, lean_object* v___x_6276_, lean_object* v___x_6277_, lean_object* v_cls_6278_, lean_object* v___y_6279_, lean_object* v___y_6280_, lean_object* v___y_6281_, lean_object* v___y_6282_, lean_object* v___y_6283_, lean_object* v___y_6284_, lean_object* v___y_6285_){
_start:
{
uint8_t v___x_25423__boxed_6286_; lean_object* v_res_6287_; 
v___x_25423__boxed_6286_ = lean_unbox(v___x_6277_);
v_res_6287_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__4(v_m_6275_, v___x_6276_, v___x_25423__boxed_6286_, v_cls_6278_, v___y_6279_, v___y_6280_, v___y_6281_, v___y_6282_, v___y_6283_, v___y_6284_);
lean_dec(v___y_6284_);
lean_dec_ref(v___y_6283_);
lean_dec(v___y_6282_);
lean_dec_ref(v___y_6281_);
lean_dec(v___y_6280_);
lean_dec_ref(v___y_6279_);
return v_res_6287_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0_spec__0(lean_object* v_e_6288_){
_start:
{
if (lean_obj_tag(v_e_6288_) == 0)
{
uint8_t v___x_6289_; 
v___x_6289_ = 2;
return v___x_6289_;
}
else
{
uint8_t v___x_6290_; 
v___x_6290_ = 0;
return v___x_6290_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0_spec__0___boxed(lean_object* v_e_6291_){
_start:
{
uint8_t v_res_6292_; lean_object* v_r_6293_; 
v_res_6292_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0_spec__0(v_e_6291_);
lean_dec_ref(v_e_6291_);
v_r_6293_ = lean_box(v_res_6292_);
return v_r_6293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0(lean_object* v_cls_6294_, uint8_t v_collapsed_6295_, lean_object* v_tag_6296_, lean_object* v_opts_6297_, uint8_t v_clsEnabled_6298_, lean_object* v_oldTraces_6299_, lean_object* v_msg_6300_, lean_object* v_resStartStop_6301_, lean_object* v___y_6302_, lean_object* v___y_6303_, lean_object* v___y_6304_, lean_object* v___y_6305_){
_start:
{
lean_object* v_fst_6307_; lean_object* v_snd_6308_; lean_object* v___y_6310_; lean_object* v___y_6311_; lean_object* v_data_6312_; lean_object* v_fst_6315_; lean_object* v_snd_6316_; lean_object* v___x_6317_; uint8_t v___x_6318_; lean_object* v___y_6320_; lean_object* v_a_6321_; uint8_t v___y_6336_; double v___y_6367_; 
v_fst_6307_ = lean_ctor_get(v_resStartStop_6301_, 0);
lean_inc(v_fst_6307_);
v_snd_6308_ = lean_ctor_get(v_resStartStop_6301_, 1);
lean_inc(v_snd_6308_);
lean_dec_ref(v_resStartStop_6301_);
v_fst_6315_ = lean_ctor_get(v_snd_6308_, 0);
lean_inc(v_fst_6315_);
v_snd_6316_ = lean_ctor_get(v_snd_6308_, 1);
lean_inc(v_snd_6316_);
lean_dec(v_snd_6308_);
v___x_6317_ = l_Lean_trace_profiler;
v___x_6318_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_6297_, v___x_6317_);
if (v___x_6318_ == 0)
{
v___y_6336_ = v___x_6318_;
goto v___jp_6335_;
}
else
{
lean_object* v___x_6372_; uint8_t v___x_6373_; 
v___x_6372_ = l_Lean_trace_profiler_useHeartbeats;
v___x_6373_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_6297_, v___x_6372_);
if (v___x_6373_ == 0)
{
lean_object* v___x_6374_; lean_object* v___x_6375_; double v___x_6376_; double v___x_6377_; double v___x_6378_; 
v___x_6374_ = l_Lean_trace_profiler_threshold;
v___x_6375_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_6297_, v___x_6374_);
v___x_6376_ = lean_float_of_nat(v___x_6375_);
v___x_6377_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2);
v___x_6378_ = lean_float_div(v___x_6376_, v___x_6377_);
v___y_6367_ = v___x_6378_;
goto v___jp_6366_;
}
else
{
lean_object* v___x_6379_; lean_object* v___x_6380_; double v___x_6381_; 
v___x_6379_ = l_Lean_trace_profiler_threshold;
v___x_6380_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_6297_, v___x_6379_);
v___x_6381_ = lean_float_of_nat(v___x_6380_);
v___y_6367_ = v___x_6381_;
goto v___jp_6366_;
}
}
v___jp_6309_:
{
lean_object* v___x_6313_; 
lean_inc(v___y_6311_);
v___x_6313_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__1(v_oldTraces_6299_, v_data_6312_, v___y_6311_, v___y_6310_, v___y_6302_, v___y_6303_, v___y_6304_, v___y_6305_);
if (lean_obj_tag(v___x_6313_) == 0)
{
lean_object* v___x_6314_; 
lean_dec_ref_known(v___x_6313_, 1);
v___x_6314_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg(v_fst_6307_);
return v___x_6314_;
}
else
{
lean_dec(v_fst_6307_);
return v___x_6313_;
}
}
v___jp_6319_:
{
uint8_t v_result_6322_; lean_object* v___x_6323_; lean_object* v___x_6324_; double v___x_6325_; lean_object* v_data_6326_; 
v_result_6322_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0_spec__0(v_fst_6307_);
v___x_6323_ = lean_box(v_result_6322_);
v___x_6324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6324_, 0, v___x_6323_);
v___x_6325_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_6296_);
lean_inc_ref(v___x_6324_);
lean_inc(v_cls_6294_);
v_data_6326_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_6326_, 0, v_cls_6294_);
lean_ctor_set(v_data_6326_, 1, v___x_6324_);
lean_ctor_set(v_data_6326_, 2, v_tag_6296_);
lean_ctor_set_float(v_data_6326_, sizeof(void*)*3, v___x_6325_);
lean_ctor_set_float(v_data_6326_, sizeof(void*)*3 + 8, v___x_6325_);
lean_ctor_set_uint8(v_data_6326_, sizeof(void*)*3 + 16, v_collapsed_6295_);
if (v___x_6318_ == 0)
{
lean_dec_ref_known(v___x_6324_, 1);
lean_dec(v_snd_6316_);
lean_dec(v_fst_6315_);
lean_dec_ref(v_tag_6296_);
lean_dec(v_cls_6294_);
v___y_6310_ = v_a_6321_;
v___y_6311_ = v___y_6320_;
v_data_6312_ = v_data_6326_;
goto v___jp_6309_;
}
else
{
lean_object* v_data_6327_; double v___x_6328_; double v___x_6329_; 
lean_dec_ref_known(v_data_6326_, 3);
v_data_6327_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_6327_, 0, v_cls_6294_);
lean_ctor_set(v_data_6327_, 1, v___x_6324_);
lean_ctor_set(v_data_6327_, 2, v_tag_6296_);
v___x_6328_ = lean_unbox_float(v_fst_6315_);
lean_dec(v_fst_6315_);
lean_ctor_set_float(v_data_6327_, sizeof(void*)*3, v___x_6328_);
v___x_6329_ = lean_unbox_float(v_snd_6316_);
lean_dec(v_snd_6316_);
lean_ctor_set_float(v_data_6327_, sizeof(void*)*3 + 8, v___x_6329_);
lean_ctor_set_uint8(v_data_6327_, sizeof(void*)*3 + 16, v_collapsed_6295_);
v___y_6310_ = v_a_6321_;
v___y_6311_ = v___y_6320_;
v_data_6312_ = v_data_6327_;
goto v___jp_6309_;
}
}
v___jp_6330_:
{
lean_object* v_ref_6331_; lean_object* v___x_6332_; 
v_ref_6331_ = lean_ctor_get(v___y_6304_, 5);
lean_inc(v___y_6305_);
lean_inc_ref(v___y_6304_);
lean_inc(v___y_6303_);
lean_inc_ref(v___y_6302_);
lean_inc(v_fst_6307_);
v___x_6332_ = lean_apply_6(v_msg_6300_, v_fst_6307_, v___y_6302_, v___y_6303_, v___y_6304_, v___y_6305_, lean_box(0));
if (lean_obj_tag(v___x_6332_) == 0)
{
lean_object* v_a_6333_; 
v_a_6333_ = lean_ctor_get(v___x_6332_, 0);
lean_inc(v_a_6333_);
lean_dec_ref_known(v___x_6332_, 1);
v___y_6320_ = v_ref_6331_;
v_a_6321_ = v_a_6333_;
goto v___jp_6319_;
}
else
{
lean_object* v___x_6334_; 
lean_dec_ref_known(v___x_6332_, 1);
v___x_6334_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1);
v___y_6320_ = v_ref_6331_;
v_a_6321_ = v___x_6334_;
goto v___jp_6319_;
}
}
v___jp_6335_:
{
if (v_clsEnabled_6298_ == 0)
{
if (v___y_6336_ == 0)
{
lean_object* v___x_6337_; lean_object* v_traceState_6338_; lean_object* v_env_6339_; lean_object* v_nextMacroScope_6340_; lean_object* v_ngen_6341_; lean_object* v_auxDeclNGen_6342_; lean_object* v_cache_6343_; lean_object* v_messages_6344_; lean_object* v_infoState_6345_; lean_object* v_snapshotTasks_6346_; lean_object* v___x_6348_; uint8_t v_isShared_6349_; uint8_t v_isSharedCheck_6365_; 
lean_dec(v_snd_6316_);
lean_dec(v_fst_6315_);
lean_dec_ref(v_msg_6300_);
lean_dec_ref(v_tag_6296_);
lean_dec(v_cls_6294_);
v___x_6337_ = lean_st_ref_take(v___y_6305_);
v_traceState_6338_ = lean_ctor_get(v___x_6337_, 4);
v_env_6339_ = lean_ctor_get(v___x_6337_, 0);
v_nextMacroScope_6340_ = lean_ctor_get(v___x_6337_, 1);
v_ngen_6341_ = lean_ctor_get(v___x_6337_, 2);
v_auxDeclNGen_6342_ = lean_ctor_get(v___x_6337_, 3);
v_cache_6343_ = lean_ctor_get(v___x_6337_, 5);
v_messages_6344_ = lean_ctor_get(v___x_6337_, 6);
v_infoState_6345_ = lean_ctor_get(v___x_6337_, 7);
v_snapshotTasks_6346_ = lean_ctor_get(v___x_6337_, 8);
v_isSharedCheck_6365_ = !lean_is_exclusive(v___x_6337_);
if (v_isSharedCheck_6365_ == 0)
{
v___x_6348_ = v___x_6337_;
v_isShared_6349_ = v_isSharedCheck_6365_;
goto v_resetjp_6347_;
}
else
{
lean_inc(v_snapshotTasks_6346_);
lean_inc(v_infoState_6345_);
lean_inc(v_messages_6344_);
lean_inc(v_cache_6343_);
lean_inc(v_traceState_6338_);
lean_inc(v_auxDeclNGen_6342_);
lean_inc(v_ngen_6341_);
lean_inc(v_nextMacroScope_6340_);
lean_inc(v_env_6339_);
lean_dec(v___x_6337_);
v___x_6348_ = lean_box(0);
v_isShared_6349_ = v_isSharedCheck_6365_;
goto v_resetjp_6347_;
}
v_resetjp_6347_:
{
uint64_t v_tid_6350_; lean_object* v_traces_6351_; lean_object* v___x_6353_; uint8_t v_isShared_6354_; uint8_t v_isSharedCheck_6364_; 
v_tid_6350_ = lean_ctor_get_uint64(v_traceState_6338_, sizeof(void*)*1);
v_traces_6351_ = lean_ctor_get(v_traceState_6338_, 0);
v_isSharedCheck_6364_ = !lean_is_exclusive(v_traceState_6338_);
if (v_isSharedCheck_6364_ == 0)
{
v___x_6353_ = v_traceState_6338_;
v_isShared_6354_ = v_isSharedCheck_6364_;
goto v_resetjp_6352_;
}
else
{
lean_inc(v_traces_6351_);
lean_dec(v_traceState_6338_);
v___x_6353_ = lean_box(0);
v_isShared_6354_ = v_isSharedCheck_6364_;
goto v_resetjp_6352_;
}
v_resetjp_6352_:
{
lean_object* v___x_6355_; lean_object* v___x_6357_; 
v___x_6355_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_6299_, v_traces_6351_);
lean_dec_ref(v_traces_6351_);
if (v_isShared_6354_ == 0)
{
lean_ctor_set(v___x_6353_, 0, v___x_6355_);
v___x_6357_ = v___x_6353_;
goto v_reusejp_6356_;
}
else
{
lean_object* v_reuseFailAlloc_6363_; 
v_reuseFailAlloc_6363_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6363_, 0, v___x_6355_);
lean_ctor_set_uint64(v_reuseFailAlloc_6363_, sizeof(void*)*1, v_tid_6350_);
v___x_6357_ = v_reuseFailAlloc_6363_;
goto v_reusejp_6356_;
}
v_reusejp_6356_:
{
lean_object* v___x_6359_; 
if (v_isShared_6349_ == 0)
{
lean_ctor_set(v___x_6348_, 4, v___x_6357_);
v___x_6359_ = v___x_6348_;
goto v_reusejp_6358_;
}
else
{
lean_object* v_reuseFailAlloc_6362_; 
v_reuseFailAlloc_6362_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6362_, 0, v_env_6339_);
lean_ctor_set(v_reuseFailAlloc_6362_, 1, v_nextMacroScope_6340_);
lean_ctor_set(v_reuseFailAlloc_6362_, 2, v_ngen_6341_);
lean_ctor_set(v_reuseFailAlloc_6362_, 3, v_auxDeclNGen_6342_);
lean_ctor_set(v_reuseFailAlloc_6362_, 4, v___x_6357_);
lean_ctor_set(v_reuseFailAlloc_6362_, 5, v_cache_6343_);
lean_ctor_set(v_reuseFailAlloc_6362_, 6, v_messages_6344_);
lean_ctor_set(v_reuseFailAlloc_6362_, 7, v_infoState_6345_);
lean_ctor_set(v_reuseFailAlloc_6362_, 8, v_snapshotTasks_6346_);
v___x_6359_ = v_reuseFailAlloc_6362_;
goto v_reusejp_6358_;
}
v_reusejp_6358_:
{
lean_object* v___x_6360_; lean_object* v___x_6361_; 
v___x_6360_ = lean_st_ref_set(v___y_6305_, v___x_6359_);
v___x_6361_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg(v_fst_6307_);
return v___x_6361_;
}
}
}
}
}
else
{
goto v___jp_6330_;
}
}
else
{
goto v___jp_6330_;
}
}
v___jp_6366_:
{
double v___x_6368_; double v___x_6369_; double v___x_6370_; uint8_t v___x_6371_; 
v___x_6368_ = lean_unbox_float(v_snd_6316_);
v___x_6369_ = lean_unbox_float(v_fst_6315_);
v___x_6370_ = lean_float_sub(v___x_6368_, v___x_6369_);
v___x_6371_ = lean_float_decLt(v___y_6367_, v___x_6370_);
v___y_6336_ = v___x_6371_;
goto v___jp_6335_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___boxed(lean_object* v_cls_6382_, lean_object* v_collapsed_6383_, lean_object* v_tag_6384_, lean_object* v_opts_6385_, lean_object* v_clsEnabled_6386_, lean_object* v_oldTraces_6387_, lean_object* v_msg_6388_, lean_object* v_resStartStop_6389_, lean_object* v___y_6390_, lean_object* v___y_6391_, lean_object* v___y_6392_, lean_object* v___y_6393_, lean_object* v___y_6394_){
_start:
{
uint8_t v_collapsed_boxed_6395_; uint8_t v_clsEnabled_boxed_6396_; lean_object* v_res_6397_; 
v_collapsed_boxed_6395_ = lean_unbox(v_collapsed_6383_);
v_clsEnabled_boxed_6396_ = lean_unbox(v_clsEnabled_6386_);
v_res_6397_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0(v_cls_6382_, v_collapsed_boxed_6395_, v_tag_6384_, v_opts_6385_, v_clsEnabled_boxed_6396_, v_oldTraces_6387_, v_msg_6388_, v_resStartStop_6389_, v___y_6390_, v___y_6391_, v___y_6392_, v___y_6393_);
lean_dec(v___y_6393_);
lean_dec_ref(v___y_6392_);
lean_dec(v___y_6391_);
lean_dec_ref(v___y_6390_);
lean_dec_ref(v_opts_6385_);
return v_res_6397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal(lean_object* v_m_6399_, lean_object* v_a_6400_, lean_object* v_a_6401_, lean_object* v_a_6402_, lean_object* v_a_6403_){
_start:
{
lean_object* v_options_6405_; lean_object* v_inheritedTraceOptions_6406_; uint8_t v_hasTrace_6407_; lean_object* v_cls_6408_; uint8_t v___x_6409_; 
v_options_6405_ = lean_ctor_get(v_a_6402_, 2);
v_inheritedTraceOptions_6406_ = lean_ctor_get(v_a_6402_, 13);
v_hasTrace_6407_ = lean_ctor_get_uint8(v_options_6405_, sizeof(void*)*1);
v_cls_6408_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0));
v___x_6409_ = lean_bool_not(v_hasTrace_6407_);
if (v___x_6409_ == 0)
{
lean_object* v___f_6410_; uint8_t v___x_6411_; lean_object* v___x_6412_; lean_object* v___y_6414_; lean_object* v___y_6415_; uint8_t v___y_6416_; lean_object* v_a_6417_; lean_object* v___y_6430_; lean_object* v___y_6431_; uint8_t v___y_6432_; lean_object* v_a_6433_; uint8_t v___y_6443_; uint8_t v_a_6496_; 
v___f_6410_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___closed__0));
v___x_6411_ = 1;
v___x_6412_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__1));
if (v_hasTrace_6407_ == 0)
{
v_a_6496_ = v_hasTrace_6407_;
goto v___jp_6495_;
}
else
{
lean_object* v___x_6505_; uint8_t v___x_6506_; 
v___x_6505_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1);
v___x_6506_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6406_, v_options_6405_, v___x_6505_);
if (v___x_6506_ == 0)
{
v_a_6496_ = v___x_6506_;
goto v___jp_6495_;
}
else
{
v___y_6443_ = v___x_6506_;
goto v___jp_6442_;
}
}
v___jp_6413_:
{
lean_object* v___x_6418_; double v___x_6419_; double v___x_6420_; double v___x_6421_; double v___x_6422_; double v___x_6423_; lean_object* v___x_6424_; lean_object* v___x_6425_; lean_object* v___x_6426_; lean_object* v___x_6427_; lean_object* v___x_6428_; 
v___x_6418_ = lean_io_mono_nanos_now();
v___x_6419_ = lean_float_of_nat(v___y_6415_);
v___x_6420_ = lean_float_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9);
v___x_6421_ = lean_float_div(v___x_6419_, v___x_6420_);
v___x_6422_ = lean_float_of_nat(v___x_6418_);
v___x_6423_ = lean_float_div(v___x_6422_, v___x_6420_);
v___x_6424_ = lean_box_float(v___x_6421_);
v___x_6425_ = lean_box_float(v___x_6423_);
v___x_6426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6426_, 0, v___x_6424_);
lean_ctor_set(v___x_6426_, 1, v___x_6425_);
v___x_6427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6427_, 0, v_a_6417_);
lean_ctor_set(v___x_6427_, 1, v___x_6426_);
v___x_6428_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0(v_cls_6408_, v___x_6411_, v___x_6412_, v_options_6405_, v___y_6416_, v___y_6414_, v___f_6410_, v___x_6427_, v_a_6400_, v_a_6401_, v_a_6402_, v_a_6403_);
return v___x_6428_;
}
v___jp_6429_:
{
lean_object* v___x_6434_; double v___x_6435_; double v___x_6436_; lean_object* v___x_6437_; lean_object* v___x_6438_; lean_object* v___x_6439_; lean_object* v___x_6440_; lean_object* v___x_6441_; 
v___x_6434_ = lean_io_get_num_heartbeats();
v___x_6435_ = lean_float_of_nat(v___y_6431_);
v___x_6436_ = lean_float_of_nat(v___x_6434_);
v___x_6437_ = lean_box_float(v___x_6435_);
v___x_6438_ = lean_box_float(v___x_6436_);
v___x_6439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6439_, 0, v___x_6437_);
lean_ctor_set(v___x_6439_, 1, v___x_6438_);
v___x_6440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6440_, 0, v_a_6433_);
lean_ctor_set(v___x_6440_, 1, v___x_6439_);
v___x_6441_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0(v_cls_6408_, v___x_6411_, v___x_6412_, v_options_6405_, v___y_6432_, v___y_6430_, v___f_6410_, v___x_6440_, v_a_6400_, v_a_6401_, v_a_6402_, v_a_6403_);
return v___x_6441_;
}
v___jp_6442_:
{
lean_object* v___x_6444_; lean_object* v_a_6445_; lean_object* v___x_6446_; uint8_t v___x_6447_; 
v___x_6444_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg(v_a_6403_);
v_a_6445_ = lean_ctor_get(v___x_6444_, 0);
lean_inc(v_a_6445_);
lean_dec_ref(v___x_6444_);
v___x_6446_ = l_Lean_trace_profiler_useHeartbeats;
v___x_6447_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_6405_, v___x_6446_);
if (v___x_6447_ == 0)
{
lean_object* v___x_6448_; lean_object* v___x_6449_; lean_object* v___x_6450_; lean_object* v___x_6451_; lean_object* v___x_6452_; lean_object* v___f_6453_; lean_object* v___x_6454_; 
v___x_6448_ = lean_io_mono_nanos_now();
v___x_6449_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_6450_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_6405_, v___x_6449_);
v___x_6451_ = lean_unsigned_to_nat(2u);
v___x_6452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6452_, 0, v___x_6450_);
lean_ctor_set(v___x_6452_, 1, v___x_6451_);
v___f_6453_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___boxed), 10, 3);
lean_closure_set(v___f_6453_, 0, v_m_6399_);
lean_closure_set(v___f_6453_, 1, v___x_6452_);
lean_closure_set(v___f_6453_, 2, v_cls_6408_);
v___x_6454_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_6453_, v_a_6400_, v_a_6401_, v_a_6402_, v_a_6403_);
if (lean_obj_tag(v___x_6454_) == 0)
{
lean_object* v_a_6455_; lean_object* v___x_6457_; uint8_t v_isShared_6458_; uint8_t v_isSharedCheck_6462_; 
v_a_6455_ = lean_ctor_get(v___x_6454_, 0);
v_isSharedCheck_6462_ = !lean_is_exclusive(v___x_6454_);
if (v_isSharedCheck_6462_ == 0)
{
v___x_6457_ = v___x_6454_;
v_isShared_6458_ = v_isSharedCheck_6462_;
goto v_resetjp_6456_;
}
else
{
lean_inc(v_a_6455_);
lean_dec(v___x_6454_);
v___x_6457_ = lean_box(0);
v_isShared_6458_ = v_isSharedCheck_6462_;
goto v_resetjp_6456_;
}
v_resetjp_6456_:
{
lean_object* v___x_6460_; 
if (v_isShared_6458_ == 0)
{
lean_ctor_set_tag(v___x_6457_, 1);
v___x_6460_ = v___x_6457_;
goto v_reusejp_6459_;
}
else
{
lean_object* v_reuseFailAlloc_6461_; 
v_reuseFailAlloc_6461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6461_, 0, v_a_6455_);
v___x_6460_ = v_reuseFailAlloc_6461_;
goto v_reusejp_6459_;
}
v_reusejp_6459_:
{
v___y_6414_ = v_a_6445_;
v___y_6415_ = v___x_6448_;
v___y_6416_ = v___y_6443_;
v_a_6417_ = v___x_6460_;
goto v___jp_6413_;
}
}
}
else
{
lean_object* v_a_6463_; lean_object* v___x_6465_; uint8_t v_isShared_6466_; uint8_t v_isSharedCheck_6470_; 
v_a_6463_ = lean_ctor_get(v___x_6454_, 0);
v_isSharedCheck_6470_ = !lean_is_exclusive(v___x_6454_);
if (v_isSharedCheck_6470_ == 0)
{
v___x_6465_ = v___x_6454_;
v_isShared_6466_ = v_isSharedCheck_6470_;
goto v_resetjp_6464_;
}
else
{
lean_inc(v_a_6463_);
lean_dec(v___x_6454_);
v___x_6465_ = lean_box(0);
v_isShared_6466_ = v_isSharedCheck_6470_;
goto v_resetjp_6464_;
}
v_resetjp_6464_:
{
lean_object* v___x_6468_; 
if (v_isShared_6466_ == 0)
{
lean_ctor_set_tag(v___x_6465_, 0);
v___x_6468_ = v___x_6465_;
goto v_reusejp_6467_;
}
else
{
lean_object* v_reuseFailAlloc_6469_; 
v_reuseFailAlloc_6469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6469_, 0, v_a_6463_);
v___x_6468_ = v_reuseFailAlloc_6469_;
goto v_reusejp_6467_;
}
v_reusejp_6467_:
{
v___y_6414_ = v_a_6445_;
v___y_6415_ = v___x_6448_;
v___y_6416_ = v___y_6443_;
v_a_6417_ = v___x_6468_;
goto v___jp_6413_;
}
}
}
}
else
{
lean_object* v___x_6471_; lean_object* v___x_6472_; lean_object* v___x_6473_; lean_object* v___x_6474_; lean_object* v___x_6475_; lean_object* v___x_6476_; lean_object* v___f_6477_; lean_object* v___x_6478_; 
v___x_6471_ = lean_io_get_num_heartbeats();
v___x_6472_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_6473_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_6405_, v___x_6472_);
v___x_6474_ = lean_unsigned_to_nat(2u);
v___x_6475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6475_, 0, v___x_6473_);
lean_ctor_set(v___x_6475_, 1, v___x_6474_);
v___x_6476_ = lean_box(v___x_6447_);
v___f_6477_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__4___boxed), 11, 4);
lean_closure_set(v___f_6477_, 0, v_m_6399_);
lean_closure_set(v___f_6477_, 1, v___x_6475_);
lean_closure_set(v___f_6477_, 2, v___x_6476_);
lean_closure_set(v___f_6477_, 3, v_cls_6408_);
v___x_6478_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_6477_, v_a_6400_, v_a_6401_, v_a_6402_, v_a_6403_);
if (lean_obj_tag(v___x_6478_) == 0)
{
lean_object* v_a_6479_; lean_object* v___x_6481_; uint8_t v_isShared_6482_; uint8_t v_isSharedCheck_6486_; 
v_a_6479_ = lean_ctor_get(v___x_6478_, 0);
v_isSharedCheck_6486_ = !lean_is_exclusive(v___x_6478_);
if (v_isSharedCheck_6486_ == 0)
{
v___x_6481_ = v___x_6478_;
v_isShared_6482_ = v_isSharedCheck_6486_;
goto v_resetjp_6480_;
}
else
{
lean_inc(v_a_6479_);
lean_dec(v___x_6478_);
v___x_6481_ = lean_box(0);
v_isShared_6482_ = v_isSharedCheck_6486_;
goto v_resetjp_6480_;
}
v_resetjp_6480_:
{
lean_object* v___x_6484_; 
if (v_isShared_6482_ == 0)
{
lean_ctor_set_tag(v___x_6481_, 1);
v___x_6484_ = v___x_6481_;
goto v_reusejp_6483_;
}
else
{
lean_object* v_reuseFailAlloc_6485_; 
v_reuseFailAlloc_6485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6485_, 0, v_a_6479_);
v___x_6484_ = v_reuseFailAlloc_6485_;
goto v_reusejp_6483_;
}
v_reusejp_6483_:
{
v___y_6430_ = v_a_6445_;
v___y_6431_ = v___x_6471_;
v___y_6432_ = v___y_6443_;
v_a_6433_ = v___x_6484_;
goto v___jp_6429_;
}
}
}
else
{
lean_object* v_a_6487_; lean_object* v___x_6489_; uint8_t v_isShared_6490_; uint8_t v_isSharedCheck_6494_; 
v_a_6487_ = lean_ctor_get(v___x_6478_, 0);
v_isSharedCheck_6494_ = !lean_is_exclusive(v___x_6478_);
if (v_isSharedCheck_6494_ == 0)
{
v___x_6489_ = v___x_6478_;
v_isShared_6490_ = v_isSharedCheck_6494_;
goto v_resetjp_6488_;
}
else
{
lean_inc(v_a_6487_);
lean_dec(v___x_6478_);
v___x_6489_ = lean_box(0);
v_isShared_6490_ = v_isSharedCheck_6494_;
goto v_resetjp_6488_;
}
v_resetjp_6488_:
{
lean_object* v___x_6492_; 
if (v_isShared_6490_ == 0)
{
lean_ctor_set_tag(v___x_6489_, 0);
v___x_6492_ = v___x_6489_;
goto v_reusejp_6491_;
}
else
{
lean_object* v_reuseFailAlloc_6493_; 
v_reuseFailAlloc_6493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6493_, 0, v_a_6487_);
v___x_6492_ = v_reuseFailAlloc_6493_;
goto v_reusejp_6491_;
}
v_reusejp_6491_:
{
v___y_6430_ = v_a_6445_;
v___y_6431_ = v___x_6471_;
v___y_6432_ = v___y_6443_;
v_a_6433_ = v___x_6492_;
goto v___jp_6429_;
}
}
}
}
}
v___jp_6495_:
{
lean_object* v___x_6497_; uint8_t v___x_6498_; 
v___x_6497_ = l_Lean_trace_profiler;
v___x_6498_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_6405_, v___x_6497_);
if (v___x_6498_ == 0)
{
lean_object* v___x_6499_; lean_object* v___x_6500_; lean_object* v___x_6501_; lean_object* v___x_6502_; lean_object* v___f_6503_; lean_object* v___x_6504_; 
v___x_6499_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_6500_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_6405_, v___x_6499_);
v___x_6501_ = lean_unsigned_to_nat(2u);
v___x_6502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6502_, 0, v___x_6500_);
lean_ctor_set(v___x_6502_, 1, v___x_6501_);
v___f_6503_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___boxed), 10, 3);
lean_closure_set(v___f_6503_, 0, v_m_6399_);
lean_closure_set(v___f_6503_, 1, v___x_6502_);
lean_closure_set(v___f_6503_, 2, v_cls_6408_);
v___x_6504_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_6503_, v_a_6400_, v_a_6401_, v_a_6402_, v_a_6403_);
return v___x_6504_;
}
else
{
v___y_6443_ = v_a_6496_;
goto v___jp_6442_;
}
}
}
else
{
lean_object* v___x_6507_; lean_object* v___x_6508_; lean_object* v___x_6509_; lean_object* v___x_6510_; lean_object* v___x_6511_; lean_object* v___f_6512_; lean_object* v___x_6513_; 
v___x_6507_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_6508_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_6405_, v___x_6507_);
v___x_6509_ = lean_unsigned_to_nat(2u);
v___x_6510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6510_, 0, v___x_6508_);
lean_ctor_set(v___x_6510_, 1, v___x_6509_);
v___x_6511_ = lean_box(v___x_6409_);
v___f_6512_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__4___boxed), 11, 4);
lean_closure_set(v___f_6512_, 0, v_m_6399_);
lean_closure_set(v___f_6512_, 1, v___x_6510_);
lean_closure_set(v___f_6512_, 2, v___x_6511_);
lean_closure_set(v___f_6512_, 3, v_cls_6408_);
v___x_6513_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_6512_, v_a_6400_, v_a_6401_, v_a_6402_, v_a_6403_);
return v___x_6513_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___boxed(lean_object* v_m_6514_, lean_object* v_a_6515_, lean_object* v_a_6516_, lean_object* v_a_6517_, lean_object* v_a_6518_, lean_object* v_a_6519_){
_start:
{
lean_object* v_res_6520_; 
v_res_6520_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal(v_m_6514_, v_a_6515_, v_a_6516_, v_a_6517_, v_a_6518_);
lean_dec(v_a_6518_);
lean_dec_ref(v_a_6517_);
lean_dec(v_a_6516_);
lean_dec_ref(v_a_6515_);
return v_res_6520_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1(lean_object* v_00_u03b1_6521_, lean_object* v_msg_6522_, lean_object* v___y_6523_, lean_object* v___y_6524_, lean_object* v___y_6525_, lean_object* v___y_6526_, lean_object* v___y_6527_, lean_object* v___y_6528_){
_start:
{
lean_object* v___x_6530_; 
v___x_6530_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(v_msg_6522_, v___y_6525_, v___y_6526_, v___y_6527_, v___y_6528_);
return v___x_6530_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___boxed(lean_object* v_00_u03b1_6531_, lean_object* v_msg_6532_, lean_object* v___y_6533_, lean_object* v___y_6534_, lean_object* v___y_6535_, lean_object* v___y_6536_, lean_object* v___y_6537_, lean_object* v___y_6538_, lean_object* v___y_6539_){
_start:
{
lean_object* v_res_6540_; 
v_res_6540_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1(v_00_u03b1_6531_, v_msg_6532_, v___y_6533_, v___y_6534_, v___y_6535_, v___y_6536_, v___y_6537_, v___y_6538_);
lean_dec(v___y_6538_);
lean_dec_ref(v___y_6537_);
lean_dec(v___y_6536_);
lean_dec_ref(v___y_6535_);
lean_dec(v___y_6534_);
lean_dec_ref(v___y_6533_);
return v_res_6540_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2(lean_object* v_cls_6541_, lean_object* v_msg_6542_, lean_object* v___y_6543_, lean_object* v___y_6544_, lean_object* v___y_6545_, lean_object* v___y_6546_, lean_object* v___y_6547_, lean_object* v___y_6548_){
_start:
{
lean_object* v___x_6550_; 
v___x_6550_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2___redArg(v_cls_6541_, v_msg_6542_, v___y_6545_, v___y_6546_, v___y_6547_, v___y_6548_);
return v___x_6550_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2___boxed(lean_object* v_cls_6551_, lean_object* v_msg_6552_, lean_object* v___y_6553_, lean_object* v___y_6554_, lean_object* v___y_6555_, lean_object* v___y_6556_, lean_object* v___y_6557_, lean_object* v___y_6558_, lean_object* v___y_6559_){
_start:
{
lean_object* v_res_6560_; 
v_res_6560_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2(v_cls_6551_, v_msg_6552_, v___y_6553_, v___y_6554_, v___y_6555_, v___y_6556_, v___y_6557_, v___y_6558_);
lean_dec(v___y_6558_);
lean_dec_ref(v___y_6557_);
lean_dec(v___y_6556_);
lean_dec_ref(v___y_6555_);
lean_dec(v___y_6554_);
lean_dec_ref(v___y_6553_);
return v_res_6560_;
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

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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_isBoolTrueExpr___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_isBoolFalseExpr___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
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
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceProj_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_TraceResult_toEmoji(uint8_t);
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
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Result_getResultExpr(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_SymM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
uint8_t l_Lean_Expr_isFalse(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "proj `"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = ": stuck"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__5;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = ": no change"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__7;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__8_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__3;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__4;
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "target: "};
static const lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__1;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "target: no change"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__3;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "target:"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3_spec__7_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3_spec__7___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3_spec__8___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "hypothesis `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___lam__0___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___lam__0___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "`: "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___lam__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___lam__0___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___lam__0___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "`: no change"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___lam__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___lam__0___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___lam__0___closed__5;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mp"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___closed__2_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(183, 66, 254, 161, 210, 133, 94, 78)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___closed__3_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__2___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__2___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__2___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__2___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__2___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__2___boxed__const__1 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__2___boxed__const__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3_spec__8(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
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
lean_object* v_ref_152_; lean_object* v___x_153_; lean_object* v_a_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_199_; 
v_ref_152_ = lean_ctor_get(v___y_149_, 5);
v___x_153_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0_spec__0(v_msg_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_);
v_a_154_ = lean_ctor_get(v___x_153_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_199_ == 0)
{
v___x_156_ = v___x_153_;
v_isShared_157_ = v_isSharedCheck_199_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_a_154_);
lean_dec(v___x_153_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_199_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_158_; lean_object* v_traceState_159_; lean_object* v_env_160_; lean_object* v_nextMacroScope_161_; lean_object* v_ngen_162_; lean_object* v_auxDeclNGen_163_; lean_object* v_cache_164_; lean_object* v_messages_165_; lean_object* v_infoState_166_; lean_object* v_snapshotTasks_167_; lean_object* v_newDecls_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_198_; 
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
v_newDecls_168_ = lean_ctor_get(v___x_158_, 9);
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_198_ == 0)
{
v___x_170_ = v___x_158_;
v_isShared_171_ = v_isSharedCheck_198_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_newDecls_168_);
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
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_198_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
uint64_t v_tid_172_; lean_object* v_traces_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_197_; 
v_tid_172_ = lean_ctor_get_uint64(v_traceState_159_, sizeof(void*)*1);
v_traces_173_ = lean_ctor_get(v_traceState_159_, 0);
v_isSharedCheck_197_ = !lean_is_exclusive(v_traceState_159_);
if (v_isSharedCheck_197_ == 0)
{
v___x_175_ = v_traceState_159_;
v_isShared_176_ = v_isSharedCheck_197_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_traces_173_);
lean_dec(v_traceState_159_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_197_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_177_; double v___x_178_; uint8_t v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_187_; 
v___x_177_ = lean_box(0);
v___x_178_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0);
v___x_179_ = 0;
v___x_180_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__1));
v___x_181_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_181_, 0, v_cls_145_);
lean_ctor_set(v___x_181_, 1, v___x_177_);
lean_ctor_set(v___x_181_, 2, v___x_180_);
lean_ctor_set_float(v___x_181_, sizeof(void*)*3, v___x_178_);
lean_ctor_set_float(v___x_181_, sizeof(void*)*3 + 8, v___x_178_);
lean_ctor_set_uint8(v___x_181_, sizeof(void*)*3 + 16, v___x_179_);
v___x_182_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__2));
v___x_183_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_183_, 0, v___x_181_);
lean_ctor_set(v___x_183_, 1, v_a_154_);
lean_ctor_set(v___x_183_, 2, v___x_182_);
lean_inc(v_ref_152_);
v___x_184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_184_, 0, v_ref_152_);
lean_ctor_set(v___x_184_, 1, v___x_183_);
v___x_185_ = l_Lean_PersistentArray_push___redArg(v_traces_173_, v___x_184_);
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 0, v___x_185_);
v___x_187_ = v___x_175_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v___x_185_);
lean_ctor_set_uint64(v_reuseFailAlloc_196_, sizeof(void*)*1, v_tid_172_);
v___x_187_ = v_reuseFailAlloc_196_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
lean_object* v___x_189_; 
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 4, v___x_187_);
v___x_189_ = v___x_170_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_env_160_);
lean_ctor_set(v_reuseFailAlloc_195_, 1, v_nextMacroScope_161_);
lean_ctor_set(v_reuseFailAlloc_195_, 2, v_ngen_162_);
lean_ctor_set(v_reuseFailAlloc_195_, 3, v_auxDeclNGen_163_);
lean_ctor_set(v_reuseFailAlloc_195_, 4, v___x_187_);
lean_ctor_set(v_reuseFailAlloc_195_, 5, v_cache_164_);
lean_ctor_set(v_reuseFailAlloc_195_, 6, v_messages_165_);
lean_ctor_set(v_reuseFailAlloc_195_, 7, v_infoState_166_);
lean_ctor_set(v_reuseFailAlloc_195_, 8, v_snapshotTasks_167_);
lean_ctor_set(v_reuseFailAlloc_195_, 9, v_newDecls_168_);
v___x_189_ = v_reuseFailAlloc_195_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_193_; 
v___x_190_ = lean_st_ref_set(v___y_150_, v___x_189_);
v___x_191_ = lean_box(0);
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 0, v___x_191_);
v___x_193_ = v___x_156_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v___x_191_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___boxed(lean_object* v_cls_200_, lean_object* v_msg_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(v_cls_200_, v_msg_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_);
lean_dec(v___y_205_);
lean_dec_ref(v___y_204_);
lean_dec(v___y_203_);
lean_dec_ref(v___y_202_);
return v_res_207_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__4(void){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_217_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__1));
v___x_218_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__3));
v___x_219_ = l_Lean_Name_append(v___x_218_, v___x_217_);
return v___x_219_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__6(void){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__5));
v___x_222_ = l_Lean_stringToMessageData(v___x_221_);
return v___x_222_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8(void){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_224_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7));
v___x_225_ = l_Lean_stringToMessageData(v___x_224_);
return v___x_225_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10(void){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_227_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__9));
v___x_228_ = l_Lean_stringToMessageData(v___x_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations(lean_object* v_e_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_){
_start:
{
uint8_t v___x_243_; 
v___x_243_ = l_Lean_Expr_isApp(v_e_232_);
if (v___x_243_ == 0)
{
lean_object* v___x_244_; lean_object* v___x_245_; 
lean_dec_ref(v_e_232_);
v___x_244_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_244_, 0, v___x_243_);
lean_ctor_set_uint8(v___x_244_, 1, v___x_243_);
v___x_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
return v___x_245_;
}
else
{
lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_246_ = l_Lean_Expr_getAppFn(v_e_232_);
v___x_247_ = l_Lean_Expr_constName_x3f(v___x_246_);
lean_dec_ref(v___x_246_);
if (lean_obj_tag(v___x_247_) == 1)
{
lean_object* v_val_248_; lean_object* v___y_250_; lean_object* v___x_287_; 
v_val_248_ = lean_ctor_get(v___x_247_, 0);
lean_inc_n(v_val_248_, 2);
lean_dec_ref(v___x_247_);
v___x_287_ = l_Lean_Meta_Tactic_Cbv_getEqnTheorems(v_val_248_, v_a_238_, v_a_239_, v_a_240_, v_a_241_);
if (lean_obj_tag(v___x_287_) == 0)
{
lean_object* v_a_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v_a_288_ = lean_ctor_get(v___x_287_, 0);
lean_inc(v_a_288_);
lean_dec_ref(v___x_287_);
v___x_289_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__11));
lean_inc_ref(v_e_232_);
v___x_290_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_a_288_, v___x_289_, v_e_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_);
lean_dec(v_a_288_);
if (lean_obj_tag(v___x_290_) == 0)
{
v___y_250_ = v___x_290_;
goto v___jp_249_;
}
else
{
lean_object* v_a_291_; uint8_t v___y_293_; uint8_t v___x_303_; 
v_a_291_ = lean_ctor_get(v___x_290_, 0);
lean_inc(v_a_291_);
v___x_303_ = l_Lean_Exception_isInterrupt(v_a_291_);
if (v___x_303_ == 0)
{
uint8_t v___x_304_; 
v___x_304_ = l_Lean_Exception_isRuntime(v_a_291_);
v___y_293_ = v___x_304_;
goto v___jp_292_;
}
else
{
lean_dec(v_a_291_);
v___y_293_ = v___x_303_;
goto v___jp_292_;
}
v___jp_292_:
{
if (v___y_293_ == 0)
{
lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_301_; 
lean_dec(v_val_248_);
lean_dec_ref(v_e_232_);
v_isSharedCheck_301_ = !lean_is_exclusive(v___x_290_);
if (v_isSharedCheck_301_ == 0)
{
lean_object* v_unused_302_; 
v_unused_302_ = lean_ctor_get(v___x_290_, 0);
lean_dec(v_unused_302_);
v___x_295_ = v___x_290_;
v_isShared_296_ = v_isSharedCheck_301_;
goto v_resetjp_294_;
}
else
{
lean_dec(v___x_290_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_301_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_297_; lean_object* v___x_299_; 
v___x_297_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_297_, 0, v___y_293_);
lean_ctor_set_uint8(v___x_297_, 1, v___y_293_);
if (v_isShared_296_ == 0)
{
lean_ctor_set_tag(v___x_295_, 0);
lean_ctor_set(v___x_295_, 0, v___x_297_);
v___x_299_ = v___x_295_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v___x_297_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
}
else
{
v___y_250_ = v___x_290_;
goto v___jp_249_;
}
}
}
}
else
{
lean_object* v_a_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_312_; 
lean_dec(v_val_248_);
lean_dec_ref(v_e_232_);
v_a_305_ = lean_ctor_get(v___x_287_, 0);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_312_ == 0)
{
v___x_307_ = v___x_287_;
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_a_305_);
lean_dec(v___x_287_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_310_; 
if (v_isShared_308_ == 0)
{
v___x_310_ = v___x_307_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_a_305_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
v___jp_249_:
{
if (lean_obj_tag(v___y_250_) == 0)
{
lean_object* v_a_251_; 
v_a_251_ = lean_ctor_get(v___y_250_, 0);
if (lean_obj_tag(v_a_251_) == 1)
{
lean_object* v_options_252_; uint8_t v_hasTrace_253_; 
v_options_252_ = lean_ctor_get(v_a_240_, 2);
v_hasTrace_253_ = lean_ctor_get_uint8(v_options_252_, sizeof(void*)*1);
if (v_hasTrace_253_ == 0)
{
lean_dec(v_val_248_);
lean_dec_ref(v_e_232_);
return v___y_250_;
}
else
{
lean_object* v_e_x27_254_; lean_object* v_inheritedTraceOptions_255_; lean_object* v___x_256_; lean_object* v___x_257_; uint8_t v___x_258_; 
v_e_x27_254_ = lean_ctor_get(v_a_251_, 0);
v_inheritedTraceOptions_255_ = lean_ctor_get(v_a_240_, 13);
v___x_256_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__1));
v___x_257_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__4, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__4_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__4);
v___x_258_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_255_, v_options_252_, v___x_257_);
if (v___x_258_ == 0)
{
lean_dec(v_val_248_);
lean_dec_ref(v_e_232_);
return v___y_250_;
}
else
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
lean_inc_ref(v_a_251_);
lean_dec_ref(v___y_250_);
v___x_259_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__6, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__6_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__6);
v___x_260_ = l_Lean_MessageData_ofName(v_val_248_);
v___x_261_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_261_, 0, v___x_259_);
lean_ctor_set(v___x_261_, 1, v___x_260_);
v___x_262_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8);
v___x_263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_263_, 0, v___x_261_);
lean_ctor_set(v___x_263_, 1, v___x_262_);
v___x_264_ = l_Lean_indentExpr(v_e_232_);
v___x_265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_263_);
lean_ctor_set(v___x_265_, 1, v___x_264_);
v___x_266_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_267_, 0, v___x_265_);
lean_ctor_set(v___x_267_, 1, v___x_266_);
lean_inc_ref(v_e_x27_254_);
v___x_268_ = l_Lean_indentExpr(v_e_x27_254_);
v___x_269_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_267_);
lean_ctor_set(v___x_269_, 1, v___x_268_);
v___x_270_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(v___x_256_, v___x_269_, v_a_238_, v_a_239_, v_a_240_, v_a_241_);
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_277_; 
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_277_ == 0)
{
lean_object* v_unused_278_; 
v_unused_278_ = lean_ctor_get(v___x_270_, 0);
lean_dec(v_unused_278_);
v___x_272_ = v___x_270_;
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
else
{
lean_dec(v___x_270_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_275_; 
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 0, v_a_251_);
v___x_275_ = v___x_272_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_a_251_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
else
{
lean_object* v_a_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_286_; 
lean_dec_ref(v_a_251_);
v_a_279_ = lean_ctor_get(v___x_270_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_286_ == 0)
{
v___x_281_ = v___x_270_;
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_a_279_);
lean_dec(v___x_270_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_284_; 
if (v_isShared_282_ == 0)
{
v___x_284_ = v___x_281_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v_a_279_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
}
}
}
}
else
{
lean_dec(v_val_248_);
lean_dec_ref(v_e_232_);
return v___y_250_;
}
}
else
{
lean_dec(v_val_248_);
lean_dec_ref(v_e_232_);
return v___y_250_;
}
}
}
else
{
lean_object* v___x_313_; lean_object* v___x_314_; 
lean_dec(v___x_247_);
lean_dec_ref(v_e_232_);
v___x_313_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
v___x_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
return v___x_314_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___boxed(lean_object* v_e_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations(v_e_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
lean_dec(v_a_324_);
lean_dec_ref(v_a_323_);
lean_dec(v_a_322_);
lean_dec_ref(v_a_321_);
lean_dec(v_a_320_);
lean_dec_ref(v_a_319_);
lean_dec(v_a_318_);
lean_dec_ref(v_a_317_);
lean_dec(v_a_316_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0(lean_object* v_cls_327_, lean_object* v_msg_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(v_cls_327_, v_msg_328_, v___y_334_, v___y_335_, v___y_336_, v___y_337_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___boxed(lean_object* v_cls_340_, lean_object* v_msg_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0(v_cls_340_, v_msg_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_);
lean_dec(v___y_350_);
lean_dec_ref(v___y_349_);
lean_dec(v___y_348_);
lean_dec_ref(v___y_347_);
lean_dec(v___y_346_);
lean_dec_ref(v___y_345_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
lean_dec(v___y_342_);
return v_res_352_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__2(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_359_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__1));
v___x_360_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__3));
v___x_361_ = l_Lean_Name_append(v___x_360_, v___x_359_);
return v___x_361_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__4(void){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_363_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__3));
v___x_364_ = l_Lean_stringToMessageData(v___x_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold(lean_object* v_e_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_){
_start:
{
uint8_t v___x_376_; 
v___x_376_ = l_Lean_Expr_isApp(v_e_365_);
if (v___x_376_ == 0)
{
lean_object* v___x_377_; lean_object* v___x_378_; 
lean_dec_ref(v_e_365_);
v___x_377_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_377_, 0, v___x_376_);
lean_ctor_set_uint8(v___x_377_, 1, v___x_376_);
v___x_378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_378_, 0, v___x_377_);
return v___x_378_;
}
else
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = l_Lean_Expr_getAppFn(v_e_365_);
v___x_380_ = l_Lean_Expr_constName_x3f(v___x_379_);
lean_dec_ref(v___x_379_);
if (lean_obj_tag(v___x_380_) == 1)
{
lean_object* v_val_381_; lean_object* v___y_383_; lean_object* v___x_420_; 
v_val_381_ = lean_ctor_get(v___x_380_, 0);
lean_inc_n(v_val_381_, 2);
lean_dec_ref(v___x_380_);
v___x_420_ = l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem(v_val_381_, v_a_371_, v_a_372_, v_a_373_, v_a_374_);
if (lean_obj_tag(v___x_420_) == 0)
{
lean_object* v_a_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_446_; 
v_a_421_ = lean_ctor_get(v___x_420_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_446_ == 0)
{
v___x_423_ = v___x_420_;
v_isShared_424_ = v_isSharedCheck_446_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_a_421_);
lean_dec(v___x_420_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_446_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
if (lean_obj_tag(v_a_421_) == 1)
{
lean_object* v_val_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
lean_del_object(v___x_423_);
v_val_425_ = lean_ctor_get(v_a_421_, 0);
lean_inc(v_val_425_);
lean_dec_ref(v_a_421_);
v___x_426_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__11));
lean_inc_ref(v_e_365_);
v___x_427_ = l_Lean_Meta_Sym_Simp_Theorem_rewrite(v_val_425_, v_e_365_, v___x_426_, v_a_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_, v_a_374_);
if (lean_obj_tag(v___x_427_) == 0)
{
v___y_383_ = v___x_427_;
goto v___jp_382_;
}
else
{
lean_object* v_a_428_; uint8_t v___y_430_; uint8_t v___x_440_; 
v_a_428_ = lean_ctor_get(v___x_427_, 0);
lean_inc(v_a_428_);
v___x_440_ = l_Lean_Exception_isInterrupt(v_a_428_);
if (v___x_440_ == 0)
{
uint8_t v___x_441_; 
v___x_441_ = l_Lean_Exception_isRuntime(v_a_428_);
v___y_430_ = v___x_441_;
goto v___jp_429_;
}
else
{
lean_dec(v_a_428_);
v___y_430_ = v___x_440_;
goto v___jp_429_;
}
v___jp_429_:
{
if (v___y_430_ == 0)
{
lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_438_; 
lean_dec(v_val_381_);
lean_dec_ref(v_e_365_);
v_isSharedCheck_438_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_438_ == 0)
{
lean_object* v_unused_439_; 
v_unused_439_ = lean_ctor_get(v___x_427_, 0);
lean_dec(v_unused_439_);
v___x_432_ = v___x_427_;
v_isShared_433_ = v_isSharedCheck_438_;
goto v_resetjp_431_;
}
else
{
lean_dec(v___x_427_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_438_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_434_; lean_object* v___x_436_; 
v___x_434_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_434_, 0, v___y_430_);
lean_ctor_set_uint8(v___x_434_, 1, v___y_430_);
if (v_isShared_433_ == 0)
{
lean_ctor_set_tag(v___x_432_, 0);
lean_ctor_set(v___x_432_, 0, v___x_434_);
v___x_436_ = v___x_432_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v___x_434_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
}
else
{
v___y_383_ = v___x_427_;
goto v___jp_382_;
}
}
}
}
else
{
lean_object* v___x_442_; lean_object* v___x_444_; 
lean_dec(v_a_421_);
lean_dec(v_val_381_);
lean_dec_ref(v_e_365_);
v___x_442_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 0, v___x_442_);
v___x_444_ = v___x_423_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v___x_442_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
}
else
{
lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_454_; 
lean_dec(v_val_381_);
lean_dec_ref(v_e_365_);
v_a_447_ = lean_ctor_get(v___x_420_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_454_ == 0)
{
v___x_449_ = v___x_420_;
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v___x_420_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_452_; 
if (v_isShared_450_ == 0)
{
v___x_452_ = v___x_449_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_a_447_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
v___jp_382_:
{
if (lean_obj_tag(v___y_383_) == 0)
{
lean_object* v_a_384_; 
v_a_384_ = lean_ctor_get(v___y_383_, 0);
if (lean_obj_tag(v_a_384_) == 1)
{
lean_object* v_options_385_; uint8_t v_hasTrace_386_; 
v_options_385_ = lean_ctor_get(v_a_373_, 2);
v_hasTrace_386_ = lean_ctor_get_uint8(v_options_385_, sizeof(void*)*1);
if (v_hasTrace_386_ == 0)
{
lean_dec(v_val_381_);
lean_dec_ref(v_e_365_);
return v___y_383_;
}
else
{
lean_object* v_e_x27_387_; lean_object* v_inheritedTraceOptions_388_; lean_object* v___x_389_; lean_object* v___x_390_; uint8_t v___x_391_; 
v_e_x27_387_ = lean_ctor_get(v_a_384_, 0);
v_inheritedTraceOptions_388_ = lean_ctor_get(v_a_373_, 13);
v___x_389_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__1));
v___x_390_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__2, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__2);
v___x_391_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_388_, v_options_385_, v___x_390_);
if (v___x_391_ == 0)
{
lean_dec(v_val_381_);
lean_dec_ref(v_e_365_);
return v___y_383_;
}
else
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
lean_inc_ref(v_a_384_);
lean_dec_ref(v___y_383_);
v___x_392_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__4, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__4_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__4);
v___x_393_ = l_Lean_MessageData_ofName(v_val_381_);
v___x_394_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_394_, 0, v___x_392_);
lean_ctor_set(v___x_394_, 1, v___x_393_);
v___x_395_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8);
v___x_396_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_396_, 0, v___x_394_);
lean_ctor_set(v___x_396_, 1, v___x_395_);
v___x_397_ = l_Lean_indentExpr(v_e_365_);
v___x_398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_398_, 0, v___x_396_);
lean_ctor_set(v___x_398_, 1, v___x_397_);
v___x_399_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_400_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_400_, 0, v___x_398_);
lean_ctor_set(v___x_400_, 1, v___x_399_);
lean_inc_ref(v_e_x27_387_);
v___x_401_ = l_Lean_indentExpr(v_e_x27_387_);
v___x_402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_402_, 0, v___x_400_);
lean_ctor_set(v___x_402_, 1, v___x_401_);
v___x_403_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(v___x_389_, v___x_402_, v_a_371_, v_a_372_, v_a_373_, v_a_374_);
if (lean_obj_tag(v___x_403_) == 0)
{
lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_410_; 
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_410_ == 0)
{
lean_object* v_unused_411_; 
v_unused_411_ = lean_ctor_get(v___x_403_, 0);
lean_dec(v_unused_411_);
v___x_405_ = v___x_403_;
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
else
{
lean_dec(v___x_403_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_408_; 
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 0, v_a_384_);
v___x_408_ = v___x_405_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_a_384_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
else
{
lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_419_; 
lean_dec_ref(v_a_384_);
v_a_412_ = lean_ctor_get(v___x_403_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_419_ == 0)
{
v___x_414_ = v___x_403_;
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v___x_403_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_417_; 
if (v_isShared_415_ == 0)
{
v___x_417_ = v___x_414_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_a_412_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
}
}
}
else
{
lean_dec(v_val_381_);
lean_dec_ref(v_e_365_);
return v___y_383_;
}
}
else
{
lean_dec(v_val_381_);
lean_dec_ref(v_e_365_);
return v___y_383_;
}
}
}
else
{
lean_object* v___x_455_; lean_object* v___x_456_; 
lean_dec(v___x_380_);
lean_dec_ref(v_e_365_);
v___x_455_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
v___x_456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_456_, 0, v___x_455_);
return v___x_456_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___boxed(lean_object* v_e_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold(v_e_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_);
lean_dec(v_a_466_);
lean_dec_ref(v_a_465_);
lean_dec(v_a_464_);
lean_dec_ref(v_a_463_);
lean_dec(v_a_462_);
lean_dec_ref(v_a_461_);
lean_dec(v_a_460_);
lean_dec_ref(v_a_459_);
lean_dec(v_a_458_);
return v_res_468_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3(void){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_477_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2));
v___x_478_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__3));
v___x_479_ = l_Lean_Name_append(v___x_478_, v___x_477_);
return v___x_479_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__5(void){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__4));
v___x_482_ = l_Lean_stringToMessageData(v___x_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg(lean_object* v_e_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_){
_start:
{
lean_object* v_new_490_; lean_object* v___x_491_; 
lean_inc_ref(v_e_483_);
v_new_490_ = l_Lean_Expr_headBeta(v_e_483_);
v___x_491_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_new_490_, v_a_484_);
if (lean_obj_tag(v___x_491_) == 0)
{
lean_object* v_a_492_; lean_object* v___y_494_; lean_object* v___y_495_; lean_object* v___y_496_; lean_object* v___y_497_; lean_object* v___y_498_; lean_object* v_options_518_; uint8_t v_hasTrace_519_; 
v_a_492_ = lean_ctor_get(v___x_491_, 0);
lean_inc(v_a_492_);
lean_dec_ref(v___x_491_);
v_options_518_ = lean_ctor_get(v_a_487_, 2);
v_hasTrace_519_ = lean_ctor_get_uint8(v_options_518_, sizeof(void*)*1);
if (v_hasTrace_519_ == 0)
{
lean_dec_ref(v_e_483_);
v___y_494_ = v_a_484_;
v___y_495_ = v_a_485_;
v___y_496_ = v_a_486_;
v___y_497_ = v_a_487_;
v___y_498_ = v_a_488_;
goto v___jp_493_;
}
else
{
lean_object* v_inheritedTraceOptions_520_; lean_object* v___x_521_; lean_object* v___x_522_; uint8_t v___x_523_; 
v_inheritedTraceOptions_520_ = lean_ctor_get(v_a_487_, 13);
v___x_521_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2));
v___x_522_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3);
v___x_523_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_520_, v_options_518_, v___x_522_);
if (v___x_523_ == 0)
{
lean_dec_ref(v_e_483_);
v___y_494_ = v_a_484_;
v___y_495_ = v_a_485_;
v___y_496_ = v_a_486_;
v___y_497_ = v_a_487_;
v___y_498_ = v_a_488_;
goto v___jp_493_;
}
else
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_524_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__5, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__5_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__5);
v___x_525_ = l_Lean_indentExpr(v_e_483_);
v___x_526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_526_, 0, v___x_524_);
lean_ctor_set(v___x_526_, 1, v___x_525_);
v___x_527_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_528_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_528_, 0, v___x_526_);
lean_ctor_set(v___x_528_, 1, v___x_527_);
lean_inc(v_a_492_);
v___x_529_ = l_Lean_indentExpr(v_a_492_);
v___x_530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_530_, 0, v___x_528_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
v___x_531_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(v___x_521_, v___x_530_, v_a_485_, v_a_486_, v_a_487_, v_a_488_);
if (lean_obj_tag(v___x_531_) == 0)
{
lean_dec_ref(v___x_531_);
v___y_494_ = v_a_484_;
v___y_495_ = v_a_485_;
v___y_496_ = v_a_486_;
v___y_497_ = v_a_487_;
v___y_498_ = v_a_488_;
goto v___jp_493_;
}
else
{
lean_object* v_a_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_539_; 
lean_dec(v_a_492_);
v_a_532_ = lean_ctor_get(v___x_531_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_531_);
if (v_isSharedCheck_539_ == 0)
{
v___x_534_ = v___x_531_;
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_a_532_);
lean_dec(v___x_531_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_537_; 
if (v_isShared_535_ == 0)
{
v___x_537_ = v___x_534_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_a_532_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
}
v___jp_493_:
{
lean_object* v___x_499_; 
lean_inc(v_a_492_);
v___x_499_ = l_Lean_Meta_Sym_mkEqRefl___redArg(v_a_492_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_);
if (lean_obj_tag(v___x_499_) == 0)
{
lean_object* v_a_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_509_; 
v_a_500_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_509_ == 0)
{
v___x_502_ = v___x_499_;
v_isShared_503_ = v_isSharedCheck_509_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_a_500_);
lean_dec(v___x_499_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_509_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
uint8_t v___x_504_; lean_object* v___x_505_; lean_object* v___x_507_; 
v___x_504_ = 0;
v___x_505_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_505_, 0, v_a_492_);
lean_ctor_set(v___x_505_, 1, v_a_500_);
lean_ctor_set_uint8(v___x_505_, sizeof(void*)*2, v___x_504_);
lean_ctor_set_uint8(v___x_505_, sizeof(void*)*2 + 1, v___x_504_);
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 0, v___x_505_);
v___x_507_ = v___x_502_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v___x_505_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
else
{
lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_517_; 
lean_dec(v_a_492_);
v_a_510_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_517_ == 0)
{
v___x_512_ = v___x_499_;
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v___x_499_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_515_; 
if (v_isShared_513_ == 0)
{
v___x_515_ = v___x_512_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_a_510_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
}
}
else
{
lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_547_; 
lean_dec_ref(v_e_483_);
v_a_540_ = lean_ctor_get(v___x_491_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_491_);
if (v_isSharedCheck_547_ == 0)
{
v___x_542_ = v___x_491_;
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_dec(v___x_491_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_545_; 
if (v_isShared_543_ == 0)
{
v___x_545_ = v___x_542_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_a_540_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___boxed(lean_object* v_e_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg(v_e_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_);
lean_dec(v_a_553_);
lean_dec_ref(v_a_552_);
lean_dec(v_a_551_);
lean_dec_ref(v_a_550_);
lean_dec(v_a_549_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce(lean_object* v_e_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg(v_e_556_, v_a_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___boxed(lean_object* v_e_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce(v_e_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_);
lean_dec(v_a_577_);
lean_dec_ref(v_a_576_);
lean_dec(v_a_575_);
lean_dec_ref(v_a_574_);
lean_dec(v_a_573_);
lean_dec_ref(v_a_572_);
lean_dec(v_a_571_);
lean_dec_ref(v_a_570_);
lean_dec(v_a_569_);
return v_res_579_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems___closed__1(void){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_581_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems___closed__0));
v___x_582_ = l_Lean_stringToMessageData(v___x_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems(lean_object* v_e_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_594_ = l_Lean_Expr_getAppFn(v_e_583_);
v___x_595_ = l_Lean_Expr_constName_x3f(v___x_594_);
lean_dec_ref(v___x_594_);
if (lean_obj_tag(v___x_595_) == 1)
{
lean_object* v_val_596_; lean_object* v___y_598_; lean_object* v___x_635_; 
v_val_596_ = lean_ctor_get(v___x_595_, 0);
lean_inc(v_val_596_);
lean_dec_ref(v___x_595_);
v___x_635_ = l_Lean_Meta_Tactic_Cbv_getCbvEvalLemmas___redArg(v_val_596_, v_a_592_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v_a_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_661_; 
v_a_636_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_661_ == 0)
{
v___x_638_ = v___x_635_;
v_isShared_639_ = v_isSharedCheck_661_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_a_636_);
lean_dec(v___x_635_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_661_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
if (lean_obj_tag(v_a_636_) == 1)
{
lean_object* v_val_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
lean_del_object(v___x_638_);
v_val_640_ = lean_ctor_get(v_a_636_, 0);
lean_inc(v_val_640_);
lean_dec_ref(v_a_636_);
v___x_641_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__11));
lean_inc_ref(v_e_583_);
v___x_642_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_val_640_, v___x_641_, v_e_583_, v_a_584_, v_a_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_);
lean_dec(v_val_640_);
if (lean_obj_tag(v___x_642_) == 0)
{
v___y_598_ = v___x_642_;
goto v___jp_597_;
}
else
{
lean_object* v_a_643_; uint8_t v___y_645_; uint8_t v___x_655_; 
v_a_643_ = lean_ctor_get(v___x_642_, 0);
lean_inc(v_a_643_);
v___x_655_ = l_Lean_Exception_isInterrupt(v_a_643_);
if (v___x_655_ == 0)
{
uint8_t v___x_656_; 
v___x_656_ = l_Lean_Exception_isRuntime(v_a_643_);
v___y_645_ = v___x_656_;
goto v___jp_644_;
}
else
{
lean_dec(v_a_643_);
v___y_645_ = v___x_655_;
goto v___jp_644_;
}
v___jp_644_:
{
if (v___y_645_ == 0)
{
lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_653_; 
lean_dec(v_val_596_);
lean_dec_ref(v_e_583_);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_653_ == 0)
{
lean_object* v_unused_654_; 
v_unused_654_ = lean_ctor_get(v___x_642_, 0);
lean_dec(v_unused_654_);
v___x_647_ = v___x_642_;
v_isShared_648_ = v_isSharedCheck_653_;
goto v_resetjp_646_;
}
else
{
lean_dec(v___x_642_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_653_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_649_; lean_object* v___x_651_; 
v___x_649_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_649_, 0, v___y_645_);
lean_ctor_set_uint8(v___x_649_, 1, v___y_645_);
if (v_isShared_648_ == 0)
{
lean_ctor_set_tag(v___x_647_, 0);
lean_ctor_set(v___x_647_, 0, v___x_649_);
v___x_651_ = v___x_647_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_649_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
else
{
v___y_598_ = v___x_642_;
goto v___jp_597_;
}
}
}
}
else
{
lean_object* v___x_657_; lean_object* v___x_659_; 
lean_dec(v_a_636_);
lean_dec(v_val_596_);
lean_dec_ref(v_e_583_);
v___x_657_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 0, v___x_657_);
v___x_659_ = v___x_638_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v___x_657_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
}
else
{
lean_object* v_a_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_669_; 
lean_dec(v_val_596_);
lean_dec_ref(v_e_583_);
v_a_662_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_669_ == 0)
{
v___x_664_ = v___x_635_;
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_a_662_);
lean_dec(v___x_635_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_667_; 
if (v_isShared_665_ == 0)
{
v___x_667_ = v___x_664_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_a_662_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
v___jp_597_:
{
if (lean_obj_tag(v___y_598_) == 0)
{
lean_object* v_a_599_; 
v_a_599_ = lean_ctor_get(v___y_598_, 0);
if (lean_obj_tag(v_a_599_) == 1)
{
lean_object* v_options_600_; uint8_t v_hasTrace_601_; 
v_options_600_ = lean_ctor_get(v_a_591_, 2);
v_hasTrace_601_ = lean_ctor_get_uint8(v_options_600_, sizeof(void*)*1);
if (v_hasTrace_601_ == 0)
{
lean_dec(v_val_596_);
lean_dec_ref(v_e_583_);
return v___y_598_;
}
else
{
lean_object* v_e_x27_602_; lean_object* v_inheritedTraceOptions_603_; lean_object* v___x_604_; lean_object* v___x_605_; uint8_t v___x_606_; 
v_e_x27_602_ = lean_ctor_get(v_a_599_, 0);
v_inheritedTraceOptions_603_ = lean_ctor_get(v_a_591_, 13);
v___x_604_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__1));
v___x_605_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__4, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__4_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__4);
v___x_606_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_603_, v_options_600_, v___x_605_);
if (v___x_606_ == 0)
{
lean_dec(v_val_596_);
lean_dec_ref(v_e_583_);
return v___y_598_;
}
else
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
lean_inc_ref(v_a_599_);
lean_dec_ref(v___y_598_);
v___x_607_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems___closed__1, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems___closed__1);
v___x_608_ = l_Lean_MessageData_ofName(v_val_596_);
v___x_609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_609_, 0, v___x_607_);
lean_ctor_set(v___x_609_, 1, v___x_608_);
v___x_610_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8);
v___x_611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_611_, 0, v___x_609_);
lean_ctor_set(v___x_611_, 1, v___x_610_);
v___x_612_ = l_Lean_indentExpr(v_e_583_);
v___x_613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_613_, 0, v___x_611_);
lean_ctor_set(v___x_613_, 1, v___x_612_);
v___x_614_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_613_);
lean_ctor_set(v___x_615_, 1, v___x_614_);
lean_inc_ref(v_e_x27_602_);
v___x_616_ = l_Lean_indentExpr(v_e_x27_602_);
v___x_617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_617_, 0, v___x_615_);
lean_ctor_set(v___x_617_, 1, v___x_616_);
v___x_618_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(v___x_604_, v___x_617_, v_a_589_, v_a_590_, v_a_591_, v_a_592_);
if (lean_obj_tag(v___x_618_) == 0)
{
lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_625_; 
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_625_ == 0)
{
lean_object* v_unused_626_; 
v_unused_626_ = lean_ctor_get(v___x_618_, 0);
lean_dec(v_unused_626_);
v___x_620_ = v___x_618_;
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
else
{
lean_dec(v___x_618_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_623_; 
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 0, v_a_599_);
v___x_623_ = v___x_620_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_a_599_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
else
{
lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_634_; 
lean_dec_ref(v_a_599_);
v_a_627_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_634_ == 0)
{
v___x_629_ = v___x_618_;
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_dec(v___x_618_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_632_; 
if (v_isShared_630_ == 0)
{
v___x_632_ = v___x_629_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_a_627_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
}
}
else
{
lean_dec(v_val_596_);
lean_dec_ref(v_e_583_);
return v___y_598_;
}
}
else
{
lean_dec(v_val_596_);
lean_dec_ref(v_e_583_);
return v___y_598_;
}
}
}
else
{
lean_object* v___x_670_; lean_object* v___x_671_; 
lean_dec(v___x_595_);
lean_dec_ref(v_e_583_);
v___x_670_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
v___x_671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_671_, 0, v___x_670_);
return v___x_671_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems___boxed(lean_object* v_e_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems(v_e_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_);
lean_dec(v_a_681_);
lean_dec_ref(v_a_680_);
lean_dec(v_a_679_);
lean_dec_ref(v_a_678_);
lean_dec(v_a_677_);
lean_dec_ref(v_a_676_);
lean_dec(v_a_675_);
lean_dec_ref(v_a_674_);
lean_dec(v_a_673_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConstApp(lean_object* v_e_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_){
_start:
{
lean_object* v___x_695_; 
lean_inc_ref(v_e_684_);
v___x_695_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations(v_e_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_object* v_a_696_; 
v_a_696_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_a_696_);
if (lean_obj_tag(v_a_696_) == 0)
{
uint8_t v_done_697_; 
v_done_697_ = lean_ctor_get_uint8(v_a_696_, 0);
if (v_done_697_ == 0)
{
uint8_t v_contextDependent_698_; lean_object* v___x_699_; 
lean_dec_ref(v___x_695_);
v_contextDependent_698_ = lean_ctor_get_uint8(v_a_696_, 1);
lean_dec_ref(v_a_696_);
v___x_699_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold(v_e_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v_a_700_; uint8_t v___y_702_; 
v_a_700_ = lean_ctor_get(v___x_699_, 0);
lean_inc(v_a_700_);
if (v_contextDependent_698_ == 0)
{
lean_dec(v_a_700_);
return v___x_699_;
}
else
{
if (lean_obj_tag(v_a_700_) == 0)
{
uint8_t v_contextDependent_712_; 
v_contextDependent_712_ = lean_ctor_get_uint8(v_a_700_, 1);
v___y_702_ = v_contextDependent_712_;
goto v___jp_701_;
}
else
{
uint8_t v_contextDependent_713_; 
v_contextDependent_713_ = lean_ctor_get_uint8(v_a_700_, sizeof(void*)*2 + 1);
v___y_702_ = v_contextDependent_713_;
goto v___jp_701_;
}
}
v___jp_701_:
{
if (v___y_702_ == 0)
{
lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_710_; 
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_710_ == 0)
{
lean_object* v_unused_711_; 
v_unused_711_ = lean_ctor_get(v___x_699_, 0);
lean_dec(v_unused_711_);
v___x_704_ = v___x_699_;
v_isShared_705_ = v_isSharedCheck_710_;
goto v_resetjp_703_;
}
else
{
lean_dec(v___x_699_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_710_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_706_; lean_object* v___x_708_; 
v___x_706_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_700_);
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 0, v___x_706_);
v___x_708_ = v___x_704_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_706_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
else
{
lean_dec(v_a_700_);
return v___x_699_;
}
}
}
else
{
return v___x_699_;
}
}
else
{
lean_dec_ref(v_a_696_);
lean_dec_ref(v_e_684_);
return v___x_695_;
}
}
else
{
lean_dec_ref(v_a_696_);
lean_dec_ref(v_e_684_);
return v___x_695_;
}
}
else
{
lean_dec_ref(v_e_684_);
return v___x_695_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConstApp___boxed(lean_object* v_e_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConstApp(v_e_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_);
lean_dec(v_a_723_);
lean_dec_ref(v_a_722_);
lean_dec(v_a_721_);
lean_dec_ref(v_a_720_);
lean_dec(v_a_719_);
lean_dec_ref(v_a_718_);
lean_dec(v_a_717_);
lean_dec_ref(v_a_716_);
lean_dec(v_a_715_);
return v_res_725_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp___lam__0(lean_object* v_a_726_, uint8_t v_done_727_, lean_object* v_x_728_){
_start:
{
uint8_t v___x_729_; 
v___x_729_ = l_Lean_ConstantInfo_hasValue(v_a_726_, v_done_727_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp___lam__0___boxed(lean_object* v_a_730_, lean_object* v_done_731_, lean_object* v_x_732_){
_start:
{
uint8_t v_done_18199__boxed_733_; uint8_t v_res_734_; lean_object* v_r_735_; 
v_done_18199__boxed_733_ = lean_unbox(v_done_731_);
v_res_734_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp___lam__0(v_a_730_, v_done_18199__boxed_733_, v_x_732_);
lean_dec_ref(v_x_732_);
lean_dec_ref(v_a_730_);
v_r_735_ = lean_box(v_res_734_);
return v_r_735_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_736_; 
v___x_736_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_736_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_737_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_738_, 0, v___x_737_);
return v___x_738_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_739_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_740_ = lean_unsigned_to_nat(0u);
v___x_741_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_741_, 0, v___x_740_);
lean_ctor_set(v___x_741_, 1, v___x_740_);
lean_ctor_set(v___x_741_, 2, v___x_740_);
lean_ctor_set(v___x_741_, 3, v___x_740_);
lean_ctor_set(v___x_741_, 4, v___x_739_);
lean_ctor_set(v___x_741_, 5, v___x_739_);
lean_ctor_set(v___x_741_, 6, v___x_739_);
lean_ctor_set(v___x_741_, 7, v___x_739_);
lean_ctor_set(v___x_741_, 8, v___x_739_);
lean_ctor_set(v___x_741_, 9, v___x_739_);
return v___x_741_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_742_ = lean_unsigned_to_nat(32u);
v___x_743_ = lean_mk_empty_array_with_capacity(v___x_742_);
v___x_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_744_, 0, v___x_743_);
return v___x_744_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_745_ = ((size_t)5ULL);
v___x_746_ = lean_unsigned_to_nat(0u);
v___x_747_ = lean_unsigned_to_nat(32u);
v___x_748_ = lean_mk_empty_array_with_capacity(v___x_747_);
v___x_749_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_750_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_750_, 0, v___x_749_);
lean_ctor_set(v___x_750_, 1, v___x_748_);
lean_ctor_set(v___x_750_, 2, v___x_746_);
lean_ctor_set(v___x_750_, 3, v___x_746_);
lean_ctor_set_usize(v___x_750_, 4, v___x_745_);
return v___x_750_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_751_ = lean_box(1);
v___x_752_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_753_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_754_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
lean_ctor_set(v___x_754_, 1, v___x_752_);
lean_ctor_set(v___x_754_, 2, v___x_751_);
return v___x_754_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_756_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6));
v___x_757_ = l_Lean_stringToMessageData(v___x_756_);
return v___x_757_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_759_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8));
v___x_760_ = l_Lean_stringToMessageData(v___x_759_);
return v___x_760_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_762_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10));
v___x_763_ = l_Lean_stringToMessageData(v___x_762_);
return v___x_763_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_765_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12));
v___x_766_ = l_Lean_stringToMessageData(v___x_765_);
return v___x_766_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15(void){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_768_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14));
v___x_769_ = l_Lean_stringToMessageData(v___x_768_);
return v___x_769_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17(void){
_start:
{
lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_771_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16));
v___x_772_ = l_Lean_stringToMessageData(v___x_771_);
return v___x_772_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19(void){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_774_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18));
v___x_775_ = l_Lean_stringToMessageData(v___x_774_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_msg_776_, lean_object* v_declHint_777_, lean_object* v___y_778_){
_start:
{
lean_object* v___x_780_; lean_object* v_env_781_; uint8_t v___x_782_; 
v___x_780_ = lean_st_ref_get(v___y_778_);
v_env_781_ = lean_ctor_get(v___x_780_, 0);
lean_inc_ref(v_env_781_);
lean_dec(v___x_780_);
v___x_782_ = l_Lean_Name_isAnonymous(v_declHint_777_);
if (v___x_782_ == 0)
{
uint8_t v_isExporting_783_; 
v_isExporting_783_ = lean_ctor_get_uint8(v_env_781_, sizeof(void*)*8);
if (v_isExporting_783_ == 0)
{
lean_object* v___x_784_; 
lean_dec_ref(v_env_781_);
lean_dec(v_declHint_777_);
v___x_784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_784_, 0, v_msg_776_);
return v___x_784_;
}
else
{
lean_object* v___x_785_; uint8_t v___x_786_; 
lean_inc_ref(v_env_781_);
v___x_785_ = l_Lean_Environment_setExporting(v_env_781_, v___x_782_);
lean_inc(v_declHint_777_);
lean_inc_ref(v___x_785_);
v___x_786_ = l_Lean_Environment_contains(v___x_785_, v_declHint_777_, v_isExporting_783_);
if (v___x_786_ == 0)
{
lean_object* v___x_787_; 
lean_dec_ref(v___x_785_);
lean_dec_ref(v_env_781_);
lean_dec(v_declHint_777_);
v___x_787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_787_, 0, v_msg_776_);
return v___x_787_;
}
else
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v_c_793_; lean_object* v___x_794_; 
v___x_788_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_789_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_790_ = l_Lean_Options_empty;
v___x_791_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_791_, 0, v___x_785_);
lean_ctor_set(v___x_791_, 1, v___x_788_);
lean_ctor_set(v___x_791_, 2, v___x_789_);
lean_ctor_set(v___x_791_, 3, v___x_790_);
lean_inc(v_declHint_777_);
v___x_792_ = l_Lean_MessageData_ofConstName(v_declHint_777_, v___x_782_);
v_c_793_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_793_, 0, v___x_791_);
lean_ctor_set(v_c_793_, 1, v___x_792_);
v___x_794_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_781_, v_declHint_777_);
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
lean_dec_ref(v_env_781_);
lean_dec(v_declHint_777_);
v___x_795_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_796_, 0, v___x_795_);
lean_ctor_set(v___x_796_, 1, v_c_793_);
v___x_797_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_798_, 0, v___x_796_);
lean_ctor_set(v___x_798_, 1, v___x_797_);
v___x_799_ = l_Lean_MessageData_note(v___x_798_);
v___x_800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_800_, 0, v_msg_776_);
lean_ctor_set(v___x_800_, 1, v___x_799_);
v___x_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_801_, 0, v___x_800_);
return v___x_801_;
}
else
{
lean_object* v_val_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_837_; 
v_val_802_ = lean_ctor_get(v___x_794_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_837_ == 0)
{
v___x_804_ = v___x_794_;
v_isShared_805_ = v_isSharedCheck_837_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_val_802_);
lean_dec(v___x_794_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_837_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v_mod_809_; uint8_t v___x_810_; 
v___x_806_ = lean_box(0);
v___x_807_ = l_Lean_Environment_header(v_env_781_);
lean_dec_ref(v_env_781_);
v___x_808_ = l_Lean_EnvironmentHeader_moduleNames(v___x_807_);
v_mod_809_ = lean_array_get(v___x_806_, v___x_808_, v_val_802_);
lean_dec(v_val_802_);
lean_dec_ref(v___x_808_);
v___x_810_ = l_Lean_isPrivateName(v_declHint_777_);
lean_dec(v_declHint_777_);
if (v___x_810_ == 0)
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_822_; 
v___x_811_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
lean_ctor_set(v___x_812_, 1, v_c_793_);
v___x_813_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_814_, 0, v___x_812_);
lean_ctor_set(v___x_814_, 1, v___x_813_);
v___x_815_ = l_Lean_MessageData_ofName(v_mod_809_);
v___x_816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_816_, 0, v___x_814_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
v___x_817_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_818_, 0, v___x_816_);
lean_ctor_set(v___x_818_, 1, v___x_817_);
v___x_819_ = l_Lean_MessageData_note(v___x_818_);
v___x_820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_820_, 0, v_msg_776_);
lean_ctor_set(v___x_820_, 1, v___x_819_);
if (v_isShared_805_ == 0)
{
lean_ctor_set_tag(v___x_804_, 0);
lean_ctor_set(v___x_804_, 0, v___x_820_);
v___x_822_ = v___x_804_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_820_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
else
{
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_835_; 
v___x_824_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_825_, 0, v___x_824_);
lean_ctor_set(v___x_825_, 1, v_c_793_);
v___x_826_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_827_, 0, v___x_825_);
lean_ctor_set(v___x_827_, 1, v___x_826_);
v___x_828_ = l_Lean_MessageData_ofName(v_mod_809_);
v___x_829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_829_, 0, v___x_827_);
lean_ctor_set(v___x_829_, 1, v___x_828_);
v___x_830_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
v___x_831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_831_, 0, v___x_829_);
lean_ctor_set(v___x_831_, 1, v___x_830_);
v___x_832_ = l_Lean_MessageData_note(v___x_831_);
v___x_833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_833_, 0, v_msg_776_);
lean_ctor_set(v___x_833_, 1, v___x_832_);
if (v_isShared_805_ == 0)
{
lean_ctor_set_tag(v___x_804_, 0);
lean_ctor_set(v___x_804_, 0, v___x_833_);
v___x_835_ = v___x_804_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_833_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_838_; 
lean_dec_ref(v_env_781_);
lean_dec(v_declHint_777_);
v___x_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_838_, 0, v_msg_776_);
return v___x_838_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msg_839_, lean_object* v_declHint_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_839_, v_declHint_840_, v___y_841_);
lean_dec(v___y_841_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_msg_844_, lean_object* v_declHint_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
lean_object* v___x_856_; lean_object* v_a_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_866_; 
v___x_856_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_844_, v_declHint_845_, v___y_854_);
v_a_857_ = lean_ctor_get(v___x_856_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_866_ == 0)
{
v___x_859_ = v___x_856_;
v_isShared_860_ = v_isSharedCheck_866_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_a_857_);
lean_dec(v___x_856_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_866_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_864_; 
v___x_861_ = l_Lean_unknownIdentifierMessageTag;
v___x_862_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_862_, 0, v___x_861_);
lean_ctor_set(v___x_862_, 1, v_a_857_);
if (v_isShared_860_ == 0)
{
lean_ctor_set(v___x_859_, 0, v___x_862_);
v___x_864_ = v___x_859_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_862_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_msg_867_, lean_object* v_declHint_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_867_, v_declHint_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec(v___y_875_);
lean_dec_ref(v___y_874_);
lean_dec(v___y_873_);
lean_dec_ref(v___y_872_);
lean_dec(v___y_871_);
lean_dec_ref(v___y_870_);
lean_dec(v___y_869_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_msg_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
lean_object* v_ref_886_; lean_object* v___x_887_; lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_896_; 
v_ref_886_ = lean_ctor_get(v___y_883_, 5);
v___x_887_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0_spec__0(v_msg_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
v_a_888_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_896_ == 0)
{
v___x_890_ = v___x_887_;
v_isShared_891_ = v_isSharedCheck_896_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_887_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_896_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_892_; lean_object* v___x_894_; 
lean_inc(v_ref_886_);
v___x_892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_892_, 0, v_ref_886_);
lean_ctor_set(v___x_892_, 1, v_a_888_);
if (v_isShared_891_ == 0)
{
lean_ctor_set_tag(v___x_890_, 1);
lean_ctor_set(v___x_890_, 0, v___x_892_);
v___x_894_ = v___x_890_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_892_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_msg_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_904_, lean_object* v_msg_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v_fileName_916_; lean_object* v_fileMap_917_; lean_object* v_options_918_; lean_object* v_currRecDepth_919_; lean_object* v_maxRecDepth_920_; lean_object* v_ref_921_; lean_object* v_currNamespace_922_; lean_object* v_openDecls_923_; lean_object* v_initHeartbeats_924_; lean_object* v_maxHeartbeats_925_; lean_object* v_quotContext_926_; lean_object* v_currMacroScope_927_; uint8_t v_diag_928_; lean_object* v_cancelTk_x3f_929_; uint8_t v_suppressElabErrors_930_; lean_object* v_inheritedTraceOptions_931_; lean_object* v_ref_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v_fileName_916_ = lean_ctor_get(v___y_913_, 0);
v_fileMap_917_ = lean_ctor_get(v___y_913_, 1);
v_options_918_ = lean_ctor_get(v___y_913_, 2);
v_currRecDepth_919_ = lean_ctor_get(v___y_913_, 3);
v_maxRecDepth_920_ = lean_ctor_get(v___y_913_, 4);
v_ref_921_ = lean_ctor_get(v___y_913_, 5);
v_currNamespace_922_ = lean_ctor_get(v___y_913_, 6);
v_openDecls_923_ = lean_ctor_get(v___y_913_, 7);
v_initHeartbeats_924_ = lean_ctor_get(v___y_913_, 8);
v_maxHeartbeats_925_ = lean_ctor_get(v___y_913_, 9);
v_quotContext_926_ = lean_ctor_get(v___y_913_, 10);
v_currMacroScope_927_ = lean_ctor_get(v___y_913_, 11);
v_diag_928_ = lean_ctor_get_uint8(v___y_913_, sizeof(void*)*14);
v_cancelTk_x3f_929_ = lean_ctor_get(v___y_913_, 12);
v_suppressElabErrors_930_ = lean_ctor_get_uint8(v___y_913_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_931_ = lean_ctor_get(v___y_913_, 13);
v_ref_932_ = l_Lean_replaceRef(v_ref_904_, v_ref_921_);
lean_inc_ref(v_inheritedTraceOptions_931_);
lean_inc(v_cancelTk_x3f_929_);
lean_inc(v_currMacroScope_927_);
lean_inc(v_quotContext_926_);
lean_inc(v_maxHeartbeats_925_);
lean_inc(v_initHeartbeats_924_);
lean_inc(v_openDecls_923_);
lean_inc(v_currNamespace_922_);
lean_inc(v_maxRecDepth_920_);
lean_inc(v_currRecDepth_919_);
lean_inc_ref(v_options_918_);
lean_inc_ref(v_fileMap_917_);
lean_inc_ref(v_fileName_916_);
v___x_933_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_933_, 0, v_fileName_916_);
lean_ctor_set(v___x_933_, 1, v_fileMap_917_);
lean_ctor_set(v___x_933_, 2, v_options_918_);
lean_ctor_set(v___x_933_, 3, v_currRecDepth_919_);
lean_ctor_set(v___x_933_, 4, v_maxRecDepth_920_);
lean_ctor_set(v___x_933_, 5, v_ref_932_);
lean_ctor_set(v___x_933_, 6, v_currNamespace_922_);
lean_ctor_set(v___x_933_, 7, v_openDecls_923_);
lean_ctor_set(v___x_933_, 8, v_initHeartbeats_924_);
lean_ctor_set(v___x_933_, 9, v_maxHeartbeats_925_);
lean_ctor_set(v___x_933_, 10, v_quotContext_926_);
lean_ctor_set(v___x_933_, 11, v_currMacroScope_927_);
lean_ctor_set(v___x_933_, 12, v_cancelTk_x3f_929_);
lean_ctor_set(v___x_933_, 13, v_inheritedTraceOptions_931_);
lean_ctor_set_uint8(v___x_933_, sizeof(void*)*14, v_diag_928_);
lean_ctor_set_uint8(v___x_933_, sizeof(void*)*14 + 1, v_suppressElabErrors_930_);
v___x_934_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_905_, v___y_911_, v___y_912_, v___x_933_, v___y_914_);
lean_dec_ref(v___x_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_935_, lean_object* v_msg_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_935_, v_msg_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec(v___y_937_);
lean_dec(v_ref_935_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_948_, lean_object* v_msg_949_, lean_object* v_declHint_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
lean_object* v___x_961_; lean_object* v_a_962_; lean_object* v___x_963_; 
v___x_961_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_949_, v_declHint_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
v_a_962_ = lean_ctor_get(v___x_961_, 0);
lean_inc(v_a_962_);
lean_dec_ref(v___x_961_);
v___x_963_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_948_, v_a_962_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_964_, lean_object* v_msg_965_, lean_object* v_declHint_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_964_, v_msg_965_, v_declHint_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec(v___y_967_);
lean_dec(v_ref_964_);
return v_res_977_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_979_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_980_ = l_Lean_stringToMessageData(v___x_979_);
return v___x_980_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_982_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_983_ = l_Lean_stringToMessageData(v___x_982_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_984_, lean_object* v_constName_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
lean_object* v___x_996_; uint8_t v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_996_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_997_ = 0;
lean_inc(v_constName_985_);
v___x_998_ = l_Lean_MessageData_ofConstName(v_constName_985_, v___x_997_);
v___x_999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_996_);
lean_ctor_set(v___x_999_, 1, v___x_998_);
v___x_1000_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_1001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_999_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
v___x_1002_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_984_, v___x_1001_, v_constName_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1003_, lean_object* v_constName_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg(v_ref_1003_, v_constName_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec(v___y_1005_);
lean_dec(v_ref_1003_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0___redArg(lean_object* v_constName_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_){
_start:
{
lean_object* v_ref_1027_; lean_object* v___x_1028_; 
v_ref_1027_ = lean_ctor_get(v___y_1024_, 5);
v___x_1028_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg(v_ref_1027_, v_constName_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0___redArg(v_constName_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec(v___y_1030_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0(lean_object* v_constName_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v___x_1052_; lean_object* v_env_1053_; uint8_t v___x_1054_; lean_object* v___x_1055_; 
v___x_1052_ = lean_st_ref_get(v___y_1050_);
v_env_1053_ = lean_ctor_get(v___x_1052_, 0);
lean_inc_ref(v_env_1053_);
lean_dec(v___x_1052_);
v___x_1054_ = 0;
lean_inc(v_constName_1041_);
v___x_1055_ = l_Lean_Environment_find_x3f(v_env_1053_, v_constName_1041_, v___x_1054_);
if (lean_obj_tag(v___x_1055_) == 0)
{
lean_object* v___x_1056_; 
v___x_1056_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0___redArg(v_constName_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
return v___x_1056_;
}
else
{
lean_object* v_val_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1064_; 
lean_dec(v_constName_1041_);
v_val_1057_ = lean_ctor_get(v___x_1055_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_1055_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1059_ = v___x_1055_;
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_val_1057_);
lean_dec(v___x_1055_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1062_; 
if (v_isShared_1060_ == 0)
{
lean_ctor_set_tag(v___x_1059_, 0);
v___x_1062_ = v___x_1059_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_val_1057_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0___boxed(lean_object* v_constName_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0(v_constName_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
lean_dec(v___y_1066_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp(lean_object* v_e_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_){
_start:
{
lean_object* v___y_1089_; lean_object* v___y_1090_; uint8_t v___y_1091_; uint8_t v___x_1094_; 
v___x_1094_ = l_Lean_Expr_isApp(v_e_1077_);
if (v___x_1094_ == 0)
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
lean_dec_ref(v_e_1077_);
v___x_1095_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_1095_, 0, v___x_1094_);
lean_ctor_set_uint8(v___x_1095_, 1, v___x_1094_);
v___x_1096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1095_);
return v___x_1096_;
}
else
{
lean_object* v_fn_1097_; 
v_fn_1097_ = l_Lean_Expr_getAppFn(v_e_1077_);
switch(lean_obj_tag(v_fn_1097_))
{
case 4:
{
lean_object* v_declName_1098_; lean_object* v___x_1099_; 
v_declName_1098_ = lean_ctor_get(v_fn_1097_, 0);
lean_inc(v_declName_1098_);
lean_dec_ref(v_fn_1097_);
v___x_1099_ = l_Lean_Meta_Tactic_Cbv_isCbvOpaque___redArg(v_declName_1098_, v_a_1086_);
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_object* v_a_1100_; uint8_t v___x_1101_; 
v_a_1100_ = lean_ctor_get(v___x_1099_, 0);
lean_inc(v_a_1100_);
lean_dec_ref(v___x_1099_);
v___x_1101_ = lean_unbox(v_a_1100_);
lean_dec(v_a_1100_);
if (v___x_1101_ == 0)
{
lean_object* v___x_1102_; 
v___x_1102_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0(v_declName_1098_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_);
if (lean_obj_tag(v___x_1102_) == 0)
{
lean_object* v_a_1103_; lean_object* v___x_1104_; 
v_a_1103_ = lean_ctor_get(v___x_1102_, 0);
lean_inc(v_a_1103_);
lean_dec_ref(v___x_1102_);
lean_inc_ref(v_e_1077_);
v___x_1104_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems(v_e_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_);
if (lean_obj_tag(v___x_1104_) == 0)
{
lean_object* v_a_1105_; 
v_a_1105_ = lean_ctor_get(v___x_1104_, 0);
lean_inc(v_a_1105_);
if (lean_obj_tag(v_a_1105_) == 0)
{
uint8_t v_done_1106_; uint8_t v_contextDependent_1107_; lean_object* v___y_1109_; lean_object* v_a_1110_; lean_object* v___y_1114_; 
v_done_1106_ = lean_ctor_get_uint8(v_a_1105_, 0);
v_contextDependent_1107_ = lean_ctor_get_uint8(v_a_1105_, 1);
lean_dec_ref(v_a_1105_);
if (v_done_1106_ == 0)
{
lean_object* v___x_1116_; lean_object* v___f_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
lean_dec_ref(v___x_1104_);
v___x_1116_ = lean_box(v_done_1106_);
v___f_1117_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1117_, 0, v_a_1103_);
lean_closure_set(v___f_1117_, 1, v___x_1116_);
v___x_1118_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConstApp___boxed), 11, 0);
lean_inc_ref(v_e_1077_);
v___x_1119_ = l_Lean_Meta_Tactic_Cbv_guardSimproc(v___f_1117_, v___x_1118_, v_e_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_);
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v_a_1120_; 
v_a_1120_ = lean_ctor_get(v___x_1119_, 0);
lean_inc(v_a_1120_);
if (lean_obj_tag(v_a_1120_) == 0)
{
uint8_t v_done_1121_; 
v_done_1121_ = lean_ctor_get_uint8(v_a_1120_, 0);
if (v_done_1121_ == 0)
{
uint8_t v_contextDependent_1122_; lean_object* v___x_1123_; 
lean_dec_ref(v___x_1119_);
v_contextDependent_1122_ = lean_ctor_get_uint8(v_a_1120_, 1);
lean_dec_ref(v_a_1120_);
v___x_1123_ = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher(v_e_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_);
if (lean_obj_tag(v___x_1123_) == 0)
{
lean_object* v_a_1124_; uint8_t v___y_1126_; 
v_a_1124_ = lean_ctor_get(v___x_1123_, 0);
lean_inc(v_a_1124_);
if (v_contextDependent_1122_ == 0)
{
lean_dec(v_a_1124_);
v___y_1114_ = v___x_1123_;
goto v___jp_1113_;
}
else
{
if (lean_obj_tag(v_a_1124_) == 0)
{
uint8_t v_contextDependent_1136_; 
v_contextDependent_1136_ = lean_ctor_get_uint8(v_a_1124_, 1);
v___y_1126_ = v_contextDependent_1136_;
goto v___jp_1125_;
}
else
{
uint8_t v_contextDependent_1137_; 
v_contextDependent_1137_ = lean_ctor_get_uint8(v_a_1124_, sizeof(void*)*2 + 1);
v___y_1126_ = v_contextDependent_1137_;
goto v___jp_1125_;
}
}
v___jp_1125_:
{
if (v___y_1126_ == 0)
{
lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1134_; 
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1134_ == 0)
{
lean_object* v_unused_1135_; 
v_unused_1135_ = lean_ctor_get(v___x_1123_, 0);
lean_dec(v_unused_1135_);
v___x_1128_ = v___x_1123_;
v_isShared_1129_ = v_isSharedCheck_1134_;
goto v_resetjp_1127_;
}
else
{
lean_dec(v___x_1123_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1134_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1130_; lean_object* v___x_1132_; 
v___x_1130_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1124_);
lean_inc_ref(v___x_1130_);
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 0, v___x_1130_);
v___x_1132_ = v___x_1128_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v___x_1130_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
v___y_1109_ = v___x_1132_;
v_a_1110_ = v___x_1130_;
goto v___jp_1108_;
}
}
}
else
{
lean_dec(v_a_1124_);
v___y_1114_ = v___x_1123_;
goto v___jp_1113_;
}
}
}
else
{
v___y_1114_ = v___x_1123_;
goto v___jp_1113_;
}
}
else
{
lean_dec_ref(v_a_1120_);
lean_dec_ref(v_e_1077_);
v___y_1114_ = v___x_1119_;
goto v___jp_1113_;
}
}
else
{
lean_dec_ref(v_a_1120_);
lean_dec_ref(v_e_1077_);
v___y_1114_ = v___x_1119_;
goto v___jp_1113_;
}
}
else
{
lean_dec_ref(v_e_1077_);
v___y_1114_ = v___x_1119_;
goto v___jp_1113_;
}
}
else
{
lean_dec(v_a_1103_);
lean_dec_ref(v_e_1077_);
return v___x_1104_;
}
v___jp_1108_:
{
if (v_contextDependent_1107_ == 0)
{
lean_dec_ref(v_a_1110_);
return v___y_1109_;
}
else
{
if (lean_obj_tag(v_a_1110_) == 0)
{
uint8_t v_contextDependent_1111_; 
v_contextDependent_1111_ = lean_ctor_get_uint8(v_a_1110_, 1);
v___y_1089_ = v_a_1110_;
v___y_1090_ = v___y_1109_;
v___y_1091_ = v_contextDependent_1111_;
goto v___jp_1088_;
}
else
{
uint8_t v_contextDependent_1112_; 
v_contextDependent_1112_ = lean_ctor_get_uint8(v_a_1110_, sizeof(void*)*2 + 1);
v___y_1089_ = v_a_1110_;
v___y_1090_ = v___y_1109_;
v___y_1091_ = v_contextDependent_1112_;
goto v___jp_1088_;
}
}
}
v___jp_1113_:
{
if (lean_obj_tag(v___y_1114_) == 0)
{
lean_object* v_a_1115_; 
v_a_1115_ = lean_ctor_get(v___y_1114_, 0);
lean_inc(v_a_1115_);
v___y_1109_ = v___y_1114_;
v_a_1110_ = v_a_1115_;
goto v___jp_1108_;
}
else
{
return v___y_1114_;
}
}
}
else
{
lean_dec_ref(v_a_1105_);
lean_dec(v_a_1103_);
lean_dec_ref(v_e_1077_);
return v___x_1104_;
}
}
else
{
lean_dec(v_a_1103_);
lean_dec_ref(v_e_1077_);
return v___x_1104_;
}
}
else
{
lean_object* v_a_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1145_; 
lean_dec_ref(v_e_1077_);
v_a_1138_ = lean_ctor_get(v___x_1102_, 0);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1140_ = v___x_1102_;
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_a_1138_);
lean_dec(v___x_1102_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1143_; 
if (v_isShared_1141_ == 0)
{
v___x_1143_ = v___x_1140_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v_a_1138_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
}
else
{
lean_object* v___x_1146_; 
lean_dec(v_declName_1098_);
v___x_1146_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems(v_e_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_);
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v_a_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1155_; 
v_a_1147_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1149_ = v___x_1146_;
v_isShared_1150_ = v_isSharedCheck_1155_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_dec(v___x_1146_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1155_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1151_; lean_object* v___x_1153_; 
v___x_1151_ = l_Lean_Meta_Tactic_Cbv_markAsDoneIfFailed(v_a_1147_);
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 0, v___x_1151_);
v___x_1153_ = v___x_1149_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v___x_1151_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
else
{
return v___x_1146_;
}
}
}
else
{
lean_object* v_a_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1163_; 
lean_dec(v_declName_1098_);
lean_dec_ref(v_e_1077_);
v_a_1156_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1158_ = v___x_1099_;
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_a_1156_);
lean_dec(v___x_1099_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1161_; 
if (v_isShared_1159_ == 0)
{
v___x_1161_ = v___x_1158_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_a_1156_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
}
case 6:
{
lean_object* v___x_1164_; 
lean_dec_ref(v_fn_1097_);
v___x_1164_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg(v_e_1077_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_);
return v___x_1164_;
}
default: 
{
lean_object* v___x_1165_; lean_object* v___x_1166_; 
lean_dec_ref(v_fn_1097_);
lean_dec_ref(v_e_1077_);
v___x_1165_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
v___x_1166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1165_);
return v___x_1166_;
}
}
}
v___jp_1088_:
{
if (v___y_1091_ == 0)
{
lean_object* v___x_1092_; lean_object* v___x_1093_; 
lean_dec_ref(v___y_1090_);
v___x_1092_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_1089_);
v___x_1093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1092_);
return v___x_1093_;
}
else
{
lean_dec_ref(v___y_1089_);
return v___y_1090_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp___boxed(lean_object* v_e_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_){
_start:
{
lean_object* v_res_1178_; 
v_res_1178_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp(v_e_1167_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
lean_dec(v_a_1176_);
lean_dec_ref(v_a_1175_);
lean_dec(v_a_1174_);
lean_dec_ref(v_a_1173_);
lean_dec(v_a_1172_);
lean_dec_ref(v_a_1171_);
lean_dec(v_a_1170_);
lean_dec_ref(v_a_1169_);
lean_dec(v_a_1168_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0(lean_object* v_00_u03b1_1179_, lean_object* v_constName_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
lean_object* v___x_1191_; 
v___x_1191_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0___redArg(v_constName_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1192_, lean_object* v_constName_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_){
_start:
{
lean_object* v_res_1204_; 
v_res_1204_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0(v_00_u03b1_1192_, v_constName_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec(v___y_1194_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1205_, lean_object* v_ref_1206_, lean_object* v_constName_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
lean_object* v___x_1218_; 
v___x_1218_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg(v_ref_1206_, v_constName_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1219_, lean_object* v_ref_1220_, lean_object* v_constName_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1(v_00_u03b1_1219_, v_ref_1220_, v_constName_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec(v___y_1222_);
lean_dec(v_ref_1220_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1233_, lean_object* v_ref_1234_, lean_object* v_msg_1235_, lean_object* v_declHint_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
lean_object* v___x_1247_; 
v___x_1247_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1234_, v_msg_1235_, v_declHint_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
return v___x_1247_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1248_, lean_object* v_ref_1249_, lean_object* v_msg_1250_, lean_object* v_declHint_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_){
_start:
{
lean_object* v_res_1262_; 
v_res_1262_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1248_, v_ref_1249_, v_msg_1250_, v_declHint_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v___y_1252_);
lean_dec(v_ref_1249_);
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_1263_, lean_object* v_declHint_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v___x_1275_; 
v___x_1275_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1263_, v_declHint_1264_, v___y_1273_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_1276_, lean_object* v_declHint_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_){
_start:
{
lean_object* v_res_1288_; 
v_res_1288_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_1276_, v_declHint_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
lean_dec(v___y_1278_);
return v_res_1288_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_1289_, lean_object* v_ref_1290_, lean_object* v_msg_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_){
_start:
{
lean_object* v___x_1302_; 
v___x_1302_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1290_, v_msg_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_);
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_1303_, lean_object* v_ref_1304_, lean_object* v_msg_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_1303_, v_ref_1304_, v_msg_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1309_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
lean_dec(v___y_1306_);
lean_dec(v_ref_1304_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_1317_, lean_object* v_msg_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_){
_start:
{
lean_object* v___x_1329_; 
v___x_1329_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_1318_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1330_, lean_object* v_msg_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_){
_start:
{
lean_object* v_res_1342_; 
v_res_1342_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(v_00_u03b1_1330_, v_msg_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1337_);
lean_dec(v___y_1336_);
lean_dec_ref(v___y_1335_);
lean_dec(v___y_1334_);
lean_dec_ref(v___y_1333_);
lean_dec(v___y_1332_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleOpaqueConst(lean_object* v_e_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_){
_start:
{
if (lean_obj_tag(v_e_1343_) == 4)
{
lean_object* v_declName_1354_; lean_object* v___x_1355_; 
v_declName_1354_ = lean_ctor_get(v_e_1343_, 0);
v___x_1355_ = l_Lean_Meta_Tactic_Cbv_isCbvOpaque___redArg(v_declName_1354_, v_a_1352_);
if (lean_obj_tag(v___x_1355_) == 0)
{
lean_object* v_a_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1377_; 
v_a_1356_ = lean_ctor_get(v___x_1355_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1355_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1358_ = v___x_1355_;
v_isShared_1359_ = v_isSharedCheck_1377_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_a_1356_);
lean_dec(v___x_1355_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1377_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
uint8_t v___x_1360_; 
v___x_1360_ = lean_unbox(v_a_1356_);
if (v___x_1360_ == 0)
{
lean_object* v___x_1361_; uint8_t v___x_1362_; uint8_t v___x_1363_; lean_object* v___x_1365_; 
lean_dec_ref(v_e_1343_);
v___x_1361_ = lean_alloc_ctor(0, 0, 2);
v___x_1362_ = lean_unbox(v_a_1356_);
lean_ctor_set_uint8(v___x_1361_, 0, v___x_1362_);
v___x_1363_ = lean_unbox(v_a_1356_);
lean_dec(v_a_1356_);
lean_ctor_set_uint8(v___x_1361_, 1, v___x_1363_);
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 0, v___x_1361_);
v___x_1365_ = v___x_1358_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___x_1361_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
else
{
lean_object* v___x_1367_; 
lean_del_object(v___x_1358_);
lean_dec(v_a_1356_);
v___x_1367_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems(v_e_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
if (lean_obj_tag(v___x_1367_) == 0)
{
lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1376_; 
v_a_1368_ = lean_ctor_get(v___x_1367_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1367_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1370_ = v___x_1367_;
v_isShared_1371_ = v_isSharedCheck_1376_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1367_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1376_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1372_; lean_object* v___x_1374_; 
v___x_1372_ = l_Lean_Meta_Tactic_Cbv_markAsDoneIfFailed(v_a_1368_);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 0, v___x_1372_);
v___x_1374_ = v___x_1370_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v___x_1372_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
else
{
return v___x_1367_;
}
}
}
}
else
{
lean_object* v_a_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1385_; 
lean_dec_ref(v_e_1343_);
v_a_1378_ = lean_ctor_get(v___x_1355_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1355_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1380_ = v___x_1355_;
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_a_1378_);
lean_dec(v___x_1355_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1383_; 
if (v_isShared_1381_ == 0)
{
v___x_1383_ = v___x_1380_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_a_1378_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
}
}
else
{
lean_object* v___x_1386_; lean_object* v___x_1387_; 
lean_dec_ref(v_e_1343_);
v___x_1386_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
v___x_1387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1386_);
return v___x_1387_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleOpaqueConst___boxed(lean_object* v_e_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleOpaqueConst(v_e_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_);
lean_dec(v_a_1397_);
lean_dec_ref(v_a_1396_);
lean_dec(v_a_1395_);
lean_dec_ref(v_a_1394_);
lean_dec(v_a_1393_);
lean_dec_ref(v_a_1392_);
lean_dec(v_a_1391_);
lean_dec_ref(v_a_1390_);
lean_dec(v_a_1389_);
return v_res_1399_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__1(void){
_start:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1401_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__0));
v___x_1402_ = l_Lean_stringToMessageData(v___x_1401_);
return v___x_1402_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__3(void){
_start:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1404_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__2));
v___x_1405_ = l_Lean_stringToMessageData(v___x_1404_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg(lean_object* v_e_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_){
_start:
{
lean_object* v___x_1413_; 
lean_inc_ref(v_e_1406_);
v___x_1413_ = l_Lean_Expr_rawNatLit_x3f(v_e_1406_);
if (lean_obj_tag(v___x_1413_) == 1)
{
lean_object* v_val_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; 
v_val_1414_ = lean_ctor_get(v___x_1413_, 0);
lean_inc(v_val_1414_);
lean_dec_ref(v___x_1413_);
v___x_1415_ = l_Lean_mkNatLit(v_val_1414_);
v___x_1416_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_1415_, v_a_1407_);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_object* v_a_1417_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1423_; lean_object* v_options_1443_; uint8_t v_hasTrace_1444_; 
v_a_1417_ = lean_ctor_get(v___x_1416_, 0);
lean_inc(v_a_1417_);
lean_dec_ref(v___x_1416_);
v_options_1443_ = lean_ctor_get(v_a_1410_, 2);
v_hasTrace_1444_ = lean_ctor_get_uint8(v_options_1443_, sizeof(void*)*1);
if (v_hasTrace_1444_ == 0)
{
v___y_1419_ = v_a_1407_;
v___y_1420_ = v_a_1408_;
v___y_1421_ = v_a_1409_;
v___y_1422_ = v_a_1410_;
v___y_1423_ = v_a_1411_;
goto v___jp_1418_;
}
else
{
lean_object* v_inheritedTraceOptions_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; uint8_t v___x_1448_; 
v_inheritedTraceOptions_1445_ = lean_ctor_get(v_a_1410_, 13);
v___x_1446_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2));
v___x_1447_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3);
v___x_1448_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1445_, v_options_1443_, v___x_1447_);
if (v___x_1448_ == 0)
{
v___y_1419_ = v_a_1407_;
v___y_1420_ = v_a_1408_;
v___y_1421_ = v_a_1409_;
v___y_1422_ = v_a_1410_;
v___y_1423_ = v_a_1411_;
goto v___jp_1418_;
}
else
{
lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1449_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__1, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__1);
lean_inc_ref(v_e_1406_);
v___x_1450_ = l_Lean_MessageData_ofExpr(v_e_1406_);
v___x_1451_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1451_, 0, v___x_1449_);
lean_ctor_set(v___x_1451_, 1, v___x_1450_);
v___x_1452_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__3, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__3);
v___x_1453_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1453_, 0, v___x_1451_);
lean_ctor_set(v___x_1453_, 1, v___x_1452_);
lean_inc(v_a_1417_);
v___x_1454_ = l_Lean_MessageData_ofExpr(v_a_1417_);
v___x_1455_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1453_);
lean_ctor_set(v___x_1455_, 1, v___x_1454_);
v___x_1456_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(v___x_1446_, v___x_1455_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_);
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_dec_ref(v___x_1456_);
v___y_1419_ = v_a_1407_;
v___y_1420_ = v_a_1408_;
v___y_1421_ = v_a_1409_;
v___y_1422_ = v_a_1410_;
v___y_1423_ = v_a_1411_;
goto v___jp_1418_;
}
else
{
lean_object* v_a_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1464_; 
lean_dec(v_a_1417_);
lean_dec_ref(v_e_1406_);
v_a_1457_ = lean_ctor_get(v___x_1456_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1459_ = v___x_1456_;
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_a_1457_);
lean_dec(v___x_1456_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1462_; 
if (v_isShared_1460_ == 0)
{
v___x_1462_ = v___x_1459_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_a_1457_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
}
}
v___jp_1418_:
{
lean_object* v___x_1424_; 
v___x_1424_ = l_Lean_Meta_Sym_mkEqRefl___redArg(v_e_1406_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
if (lean_obj_tag(v___x_1424_) == 0)
{
lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1434_; 
v_a_1425_ = lean_ctor_get(v___x_1424_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v___x_1424_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1427_ = v___x_1424_;
v_isShared_1428_ = v_isSharedCheck_1434_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v___x_1424_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1434_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
uint8_t v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1432_; 
v___x_1429_ = 0;
v___x_1430_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1430_, 0, v_a_1417_);
lean_ctor_set(v___x_1430_, 1, v_a_1425_);
lean_ctor_set_uint8(v___x_1430_, sizeof(void*)*2, v___x_1429_);
lean_ctor_set_uint8(v___x_1430_, sizeof(void*)*2 + 1, v___x_1429_);
if (v_isShared_1428_ == 0)
{
lean_ctor_set(v___x_1427_, 0, v___x_1430_);
v___x_1432_ = v___x_1427_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v___x_1430_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
}
else
{
lean_object* v_a_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1442_; 
lean_dec(v_a_1417_);
v_a_1435_ = lean_ctor_get(v___x_1424_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1424_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1437_ = v___x_1424_;
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_a_1435_);
lean_dec(v___x_1424_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1440_; 
if (v_isShared_1438_ == 0)
{
v___x_1440_ = v___x_1437_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_a_1435_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
}
}
}
else
{
lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1472_; 
lean_dec_ref(v_e_1406_);
v_a_1465_ = lean_ctor_get(v___x_1416_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1467_ = v___x_1416_;
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v___x_1416_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1470_; 
if (v_isShared_1468_ == 0)
{
v___x_1470_ = v___x_1467_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_a_1465_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
}
}
else
{
lean_object* v___x_1473_; lean_object* v___x_1474_; 
lean_dec(v___x_1413_);
lean_dec_ref(v_e_1406_);
v___x_1473_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
v___x_1474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1473_);
return v___x_1474_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___boxed(lean_object* v_e_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_){
_start:
{
lean_object* v_res_1482_; 
v_res_1482_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg(v_e_1475_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_);
lean_dec(v_a_1480_);
lean_dec_ref(v_a_1479_);
lean_dec(v_a_1478_);
lean_dec_ref(v_a_1477_);
lean_dec(v_a_1476_);
return v_res_1482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit(lean_object* v_e_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_){
_start:
{
lean_object* v___x_1494_; 
v___x_1494_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg(v_e_1483_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___boxed(lean_object* v_e_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit(v_e_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_);
lean_dec(v_a_1504_);
lean_dec_ref(v_a_1503_);
lean_dec(v_a_1502_);
lean_dec_ref(v_a_1501_);
lean_dec(v_a_1500_);
lean_dec_ref(v_a_1499_);
lean_dec(v_a_1498_);
lean_dec_ref(v_a_1497_);
lean_dec(v_a_1496_);
return v_res_1506_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg___closed__1(void){
_start:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1508_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg___closed__0));
v___x_1509_ = l_Lean_stringToMessageData(v___x_1508_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg(lean_object* v_e_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_){
_start:
{
if (lean_obj_tag(v_e_1510_) == 8)
{
lean_object* v_value_1517_; lean_object* v_body_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; uint8_t v___x_1522_; lean_object* v_new_1523_; lean_object* v___x_1524_; 
v_value_1517_ = lean_ctor_get(v_e_1510_, 2);
v_body_1518_ = lean_ctor_get(v_e_1510_, 3);
v___x_1519_ = lean_unsigned_to_nat(1u);
v___x_1520_ = lean_mk_empty_array_with_capacity(v___x_1519_);
lean_inc_ref(v_value_1517_);
v___x_1521_ = lean_array_push(v___x_1520_, v_value_1517_);
v___x_1522_ = 1;
v_new_1523_ = l_Lean_Meta_expandLet(v_body_1518_, v___x_1521_, v___x_1522_);
v___x_1524_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_new_1523_, v_a_1511_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v_a_1525_; lean_object* v___y_1527_; lean_object* v___y_1528_; lean_object* v___y_1529_; lean_object* v___y_1530_; lean_object* v___y_1531_; lean_object* v_options_1551_; uint8_t v_hasTrace_1552_; 
v_a_1525_ = lean_ctor_get(v___x_1524_, 0);
lean_inc(v_a_1525_);
lean_dec_ref(v___x_1524_);
v_options_1551_ = lean_ctor_get(v_a_1514_, 2);
v_hasTrace_1552_ = lean_ctor_get_uint8(v_options_1551_, sizeof(void*)*1);
if (v_hasTrace_1552_ == 0)
{
lean_dec_ref(v_e_1510_);
v___y_1527_ = v_a_1511_;
v___y_1528_ = v_a_1512_;
v___y_1529_ = v_a_1513_;
v___y_1530_ = v_a_1514_;
v___y_1531_ = v_a_1515_;
goto v___jp_1526_;
}
else
{
lean_object* v_inheritedTraceOptions_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; uint8_t v___x_1556_; 
v_inheritedTraceOptions_1553_ = lean_ctor_get(v_a_1514_, 13);
v___x_1554_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2));
v___x_1555_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3);
v___x_1556_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1553_, v_options_1551_, v___x_1555_);
if (v___x_1556_ == 0)
{
lean_dec_ref(v_e_1510_);
v___y_1527_ = v_a_1511_;
v___y_1528_ = v_a_1512_;
v___y_1529_ = v_a_1513_;
v___y_1530_ = v_a_1514_;
v___y_1531_ = v_a_1515_;
goto v___jp_1526_;
}
else
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1557_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg___closed__1, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg___closed__1);
v___x_1558_ = l_Lean_indentExpr(v_e_1510_);
v___x_1559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1557_);
lean_ctor_set(v___x_1559_, 1, v___x_1558_);
v___x_1560_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_1561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1559_);
lean_ctor_set(v___x_1561_, 1, v___x_1560_);
lean_inc(v_a_1525_);
v___x_1562_ = l_Lean_indentExpr(v_a_1525_);
v___x_1563_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1561_);
lean_ctor_set(v___x_1563_, 1, v___x_1562_);
v___x_1564_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(v___x_1554_, v___x_1563_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_dec_ref(v___x_1564_);
v___y_1527_ = v_a_1511_;
v___y_1528_ = v_a_1512_;
v___y_1529_ = v_a_1513_;
v___y_1530_ = v_a_1514_;
v___y_1531_ = v_a_1515_;
goto v___jp_1526_;
}
else
{
lean_object* v_a_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1572_; 
lean_dec(v_a_1525_);
v_a_1565_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1567_ = v___x_1564_;
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_a_1565_);
lean_dec(v___x_1564_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___x_1570_; 
if (v_isShared_1568_ == 0)
{
v___x_1570_ = v___x_1567_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_a_1565_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
}
}
v___jp_1526_:
{
lean_object* v___x_1532_; 
lean_inc(v_a_1525_);
v___x_1532_ = l_Lean_Meta_Sym_mkEqRefl___redArg(v_a_1525_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_object* v_a_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1542_; 
v_a_1533_ = lean_ctor_get(v___x_1532_, 0);
v_isSharedCheck_1542_ = !lean_is_exclusive(v___x_1532_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1535_ = v___x_1532_;
v_isShared_1536_ = v_isSharedCheck_1542_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_a_1533_);
lean_dec(v___x_1532_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1542_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
uint8_t v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1540_; 
v___x_1537_ = 0;
v___x_1538_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1538_, 0, v_a_1525_);
lean_ctor_set(v___x_1538_, 1, v_a_1533_);
lean_ctor_set_uint8(v___x_1538_, sizeof(void*)*2, v___x_1537_);
lean_ctor_set_uint8(v___x_1538_, sizeof(void*)*2 + 1, v___x_1537_);
if (v_isShared_1536_ == 0)
{
lean_ctor_set(v___x_1535_, 0, v___x_1538_);
v___x_1540_ = v___x_1535_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v___x_1538_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
}
else
{
lean_object* v_a_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1550_; 
lean_dec(v_a_1525_);
v_a_1543_ = lean_ctor_get(v___x_1532_, 0);
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1532_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1545_ = v___x_1532_;
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_dec(v___x_1532_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1548_; 
if (v_isShared_1546_ == 0)
{
v___x_1548_ = v___x_1545_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_a_1543_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
}
}
}
else
{
lean_object* v_a_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1580_; 
lean_dec_ref(v_e_1510_);
v_a_1573_ = lean_ctor_get(v___x_1524_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1575_ = v___x_1524_;
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_a_1573_);
lean_dec(v___x_1524_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1578_; 
if (v_isShared_1576_ == 0)
{
v___x_1578_ = v___x_1575_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_a_1573_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
}
else
{
lean_object* v___x_1581_; lean_object* v___x_1582_; 
lean_dec_ref(v_e_1510_);
v___x_1581_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
v___x_1582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1581_);
return v___x_1582_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg___boxed(lean_object* v_e_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_){
_start:
{
lean_object* v_res_1590_; 
v_res_1590_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg(v_e_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_);
lean_dec(v_a_1588_);
lean_dec_ref(v_a_1587_);
lean_dec(v_a_1586_);
lean_dec_ref(v_a_1585_);
lean_dec(v_a_1584_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce(lean_object* v_e_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_){
_start:
{
lean_object* v___x_1602_; 
v___x_1602_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg(v_e_1591_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___boxed(lean_object* v_e_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_){
_start:
{
lean_object* v_res_1614_; 
v_res_1614_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce(v_e_1603_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_);
lean_dec(v_a_1612_);
lean_dec_ref(v_a_1611_);
lean_dec(v_a_1610_);
lean_dec_ref(v_a_1609_);
lean_dec(v_a_1608_);
lean_dec_ref(v_a_1607_);
lean_dec(v_a_1606_);
lean_dec_ref(v_a_1605_);
lean_dec(v_a_1604_);
return v_res_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(lean_object* v_structName_1615_, lean_object* v_idx_1616_, lean_object* v_struct_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_){
_start:
{
lean_object* v___y_1626_; lean_object* v___x_1629_; uint8_t v_debug_1630_; 
v___x_1629_ = lean_st_ref_get(v___y_1619_);
v_debug_1630_ = lean_ctor_get_uint8(v___x_1629_, sizeof(void*)*10);
lean_dec(v___x_1629_);
if (v_debug_1630_ == 0)
{
v___y_1626_ = v___y_1619_;
goto v___jp_1625_;
}
else
{
lean_object* v___x_1631_; 
lean_inc_ref(v_struct_1617_);
v___x_1631_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_struct_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_);
if (lean_obj_tag(v___x_1631_) == 0)
{
lean_dec_ref(v___x_1631_);
v___y_1626_ = v___y_1619_;
goto v___jp_1625_;
}
else
{
lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1639_; 
lean_dec_ref(v_struct_1617_);
lean_dec(v_idx_1616_);
lean_dec(v_structName_1615_);
v_a_1632_ = lean_ctor_get(v___x_1631_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1634_ = v___x_1631_;
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1631_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1637_; 
if (v_isShared_1635_ == 0)
{
v___x_1637_ = v___x_1634_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_a_1632_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
}
v___jp_1625_:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1627_ = l_Lean_Expr_proj___override(v_structName_1615_, v_idx_1616_, v_struct_1617_);
v___x_1628_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1627_, v___y_1626_);
return v___x_1628_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg___boxed(lean_object* v_structName_1640_, lean_object* v_idx_1641_, lean_object* v_struct_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_structName_1640_, v_idx_1641_, v_struct_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_);
lean_dec(v___y_1648_);
lean_dec_ref(v___y_1647_);
lean_dec(v___y_1646_);
lean_dec_ref(v___y_1645_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0(lean_object* v_structName_1651_, lean_object* v_idx_1652_, lean_object* v_struct_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_){
_start:
{
lean_object* v___x_1664_; 
v___x_1664_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_structName_1651_, v_idx_1652_, v_struct_1653_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___boxed(lean_object* v_structName_1665_, lean_object* v_idx_1666_, lean_object* v_struct_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0(v_structName_1665_, v_idx_1666_, v_struct_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
lean_dec(v___y_1670_);
lean_dec_ref(v___y_1669_);
lean_dec(v___y_1668_);
return v_res_1678_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1679_; 
v___x_1679_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM(lean_box(0));
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1(lean_object* v_msg_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_){
_start:
{
lean_object* v___x_1691_; lean_object* v___x_118506__overap_1692_; lean_object* v___x_1693_; 
v___x_1691_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___closed__0);
v___x_118506__overap_1692_ = lean_panic_fn_borrowed(v___x_1691_, v_msg_1680_);
lean_inc(v___y_1689_);
lean_inc_ref(v___y_1688_);
lean_inc(v___y_1687_);
lean_inc_ref(v___y_1686_);
lean_inc(v___y_1685_);
lean_inc_ref(v___y_1684_);
lean_inc(v___y_1683_);
lean_inc_ref(v___y_1682_);
lean_inc(v___y_1681_);
v___x_1693_ = lean_apply_10(v___x_118506__overap_1692_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, lean_box(0));
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___boxed(lean_object* v_msg_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_){
_start:
{
lean_object* v_res_1705_; 
v_res_1705_ = l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1(v_msg_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
lean_dec(v___y_1695_);
return v_res_1705_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1706_ = lean_unsigned_to_nat(32u);
v___x_1707_ = lean_mk_empty_array_with_capacity(v___x_1706_);
v___x_1708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1707_);
return v___x_1708_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1709_ = ((size_t)5ULL);
v___x_1710_ = lean_unsigned_to_nat(0u);
v___x_1711_ = lean_unsigned_to_nat(32u);
v___x_1712_ = lean_mk_empty_array_with_capacity(v___x_1711_);
v___x_1713_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__0);
v___x_1714_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1714_, 0, v___x_1713_);
lean_ctor_set(v___x_1714_, 1, v___x_1712_);
lean_ctor_set(v___x_1714_, 2, v___x_1710_);
lean_ctor_set(v___x_1714_, 3, v___x_1710_);
lean_ctor_set_usize(v___x_1714_, 4, v___x_1709_);
return v___x_1714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg(lean_object* v___y_1715_){
_start:
{
lean_object* v___x_1717_; lean_object* v_traceState_1718_; lean_object* v_traces_1719_; lean_object* v___x_1720_; lean_object* v_traceState_1721_; lean_object* v_env_1722_; lean_object* v_nextMacroScope_1723_; lean_object* v_ngen_1724_; lean_object* v_auxDeclNGen_1725_; lean_object* v_cache_1726_; lean_object* v_messages_1727_; lean_object* v_infoState_1728_; lean_object* v_snapshotTasks_1729_; lean_object* v_newDecls_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1749_; 
v___x_1717_ = lean_st_ref_get(v___y_1715_);
v_traceState_1718_ = lean_ctor_get(v___x_1717_, 4);
lean_inc_ref(v_traceState_1718_);
lean_dec(v___x_1717_);
v_traces_1719_ = lean_ctor_get(v_traceState_1718_, 0);
lean_inc_ref(v_traces_1719_);
lean_dec_ref(v_traceState_1718_);
v___x_1720_ = lean_st_ref_take(v___y_1715_);
v_traceState_1721_ = lean_ctor_get(v___x_1720_, 4);
v_env_1722_ = lean_ctor_get(v___x_1720_, 0);
v_nextMacroScope_1723_ = lean_ctor_get(v___x_1720_, 1);
v_ngen_1724_ = lean_ctor_get(v___x_1720_, 2);
v_auxDeclNGen_1725_ = lean_ctor_get(v___x_1720_, 3);
v_cache_1726_ = lean_ctor_get(v___x_1720_, 5);
v_messages_1727_ = lean_ctor_get(v___x_1720_, 6);
v_infoState_1728_ = lean_ctor_get(v___x_1720_, 7);
v_snapshotTasks_1729_ = lean_ctor_get(v___x_1720_, 8);
v_newDecls_1730_ = lean_ctor_get(v___x_1720_, 9);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1720_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1732_ = v___x_1720_;
v_isShared_1733_ = v_isSharedCheck_1749_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_newDecls_1730_);
lean_inc(v_snapshotTasks_1729_);
lean_inc(v_infoState_1728_);
lean_inc(v_messages_1727_);
lean_inc(v_cache_1726_);
lean_inc(v_traceState_1721_);
lean_inc(v_auxDeclNGen_1725_);
lean_inc(v_ngen_1724_);
lean_inc(v_nextMacroScope_1723_);
lean_inc(v_env_1722_);
lean_dec(v___x_1720_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1749_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
uint64_t v_tid_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1747_; 
v_tid_1734_ = lean_ctor_get_uint64(v_traceState_1721_, sizeof(void*)*1);
v_isSharedCheck_1747_ = !lean_is_exclusive(v_traceState_1721_);
if (v_isSharedCheck_1747_ == 0)
{
lean_object* v_unused_1748_; 
v_unused_1748_ = lean_ctor_get(v_traceState_1721_, 0);
lean_dec(v_unused_1748_);
v___x_1736_ = v_traceState_1721_;
v_isShared_1737_ = v_isSharedCheck_1747_;
goto v_resetjp_1735_;
}
else
{
lean_dec(v_traceState_1721_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1747_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v___x_1738_; lean_object* v___x_1740_; 
v___x_1738_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1);
if (v_isShared_1737_ == 0)
{
lean_ctor_set(v___x_1736_, 0, v___x_1738_);
v___x_1740_ = v___x_1736_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v___x_1738_);
lean_ctor_set_uint64(v_reuseFailAlloc_1746_, sizeof(void*)*1, v_tid_1734_);
v___x_1740_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
lean_object* v___x_1742_; 
if (v_isShared_1733_ == 0)
{
lean_ctor_set(v___x_1732_, 4, v___x_1740_);
v___x_1742_ = v___x_1732_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_env_1722_);
lean_ctor_set(v_reuseFailAlloc_1745_, 1, v_nextMacroScope_1723_);
lean_ctor_set(v_reuseFailAlloc_1745_, 2, v_ngen_1724_);
lean_ctor_set(v_reuseFailAlloc_1745_, 3, v_auxDeclNGen_1725_);
lean_ctor_set(v_reuseFailAlloc_1745_, 4, v___x_1740_);
lean_ctor_set(v_reuseFailAlloc_1745_, 5, v_cache_1726_);
lean_ctor_set(v_reuseFailAlloc_1745_, 6, v_messages_1727_);
lean_ctor_set(v_reuseFailAlloc_1745_, 7, v_infoState_1728_);
lean_ctor_set(v_reuseFailAlloc_1745_, 8, v_snapshotTasks_1729_);
lean_ctor_set(v_reuseFailAlloc_1745_, 9, v_newDecls_1730_);
v___x_1742_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1743_ = lean_st_ref_set(v___y_1715_, v___x_1742_);
v___x_1744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1744_, 0, v_traces_1719_);
return v___x_1744_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___boxed(lean_object* v___y_1750_, lean_object* v___y_1751_){
_start:
{
lean_object* v_res_1752_; 
v_res_1752_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg(v___y_1750_);
lean_dec(v___y_1750_);
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2(lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_){
_start:
{
lean_object* v___x_1763_; 
v___x_1763_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg(v___y_1761_);
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___boxed(lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2(v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_);
lean_dec(v___y_1772_);
lean_dec_ref(v___y_1771_);
lean_dec(v___y_1770_);
lean_dec_ref(v___y_1769_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
lean_dec(v___y_1764_);
return v_res_1774_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(lean_object* v_opts_1775_, lean_object* v_opt_1776_){
_start:
{
lean_object* v_name_1777_; lean_object* v_defValue_1778_; lean_object* v_map_1779_; lean_object* v___x_1780_; 
v_name_1777_ = lean_ctor_get(v_opt_1776_, 0);
v_defValue_1778_ = lean_ctor_get(v_opt_1776_, 1);
v_map_1779_ = lean_ctor_get(v_opts_1775_, 0);
v___x_1780_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1779_, v_name_1777_);
if (lean_obj_tag(v___x_1780_) == 0)
{
uint8_t v___x_1781_; 
v___x_1781_ = lean_unbox(v_defValue_1778_);
return v___x_1781_;
}
else
{
lean_object* v_val_1782_; 
v_val_1782_ = lean_ctor_get(v___x_1780_, 0);
lean_inc(v_val_1782_);
lean_dec_ref(v___x_1780_);
if (lean_obj_tag(v_val_1782_) == 1)
{
uint8_t v_v_1783_; 
v_v_1783_ = lean_ctor_get_uint8(v_val_1782_, 0);
lean_dec_ref(v_val_1782_);
return v_v_1783_;
}
else
{
uint8_t v___x_1784_; 
lean_dec(v_val_1782_);
v___x_1784_ = lean_unbox(v_defValue_1778_);
return v___x_1784_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___boxed(lean_object* v_opts_1785_, lean_object* v_opt_1786_){
_start:
{
uint8_t v_res_1787_; lean_object* v_r_1788_; 
v_res_1787_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_1785_, v_opt_1786_);
lean_dec_ref(v_opt_1786_);
lean_dec_ref(v_opts_1785_);
v_r_1788_ = lean_box(v_res_1787_);
return v_r_1788_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1790_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__0));
v___x_1791_ = l_Lean_stringToMessageData(v___x_1790_);
return v___x_1791_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1793_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__2));
v___x_1794_ = l_Lean_stringToMessageData(v___x_1793_);
return v___x_1794_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__5(void){
_start:
{
lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1796_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__4));
v___x_1797_ = l_Lean_stringToMessageData(v___x_1796_);
return v___x_1797_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__7(void){
_start:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1799_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__6));
v___x_1800_ = l_Lean_stringToMessageData(v___x_1799_);
return v___x_1800_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__9(void){
_start:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1802_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__8));
v___x_1803_ = l_Lean_stringToMessageData(v___x_1802_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0(lean_object* v_typeName_1804_, lean_object* v_idx_1805_, lean_object* v_e_1806_, lean_object* v_x_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_){
_start:
{
if (lean_obj_tag(v_x_1807_) == 0)
{
lean_object* v_a_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1838_; 
lean_dec_ref(v_e_1806_);
v_a_1818_ = lean_ctor_get(v_x_1807_, 0);
v_isSharedCheck_1838_ = !lean_is_exclusive(v_x_1807_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1820_ = v_x_1807_;
v_isShared_1821_ = v_isSharedCheck_1838_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_a_1818_);
lean_dec(v_x_1807_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1838_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1829_; 
v___x_1822_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__1);
v___x_1823_ = l_Lean_MessageData_ofName(v_typeName_1804_);
v___x_1824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1822_);
lean_ctor_set(v___x_1824_, 1, v___x_1823_);
v___x_1825_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_1826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1824_);
lean_ctor_set(v___x_1826_, 1, v___x_1825_);
v___x_1827_ = l_Nat_reprFast(v_idx_1805_);
if (v_isShared_1821_ == 0)
{
lean_ctor_set_tag(v___x_1820_, 3);
lean_ctor_set(v___x_1820_, 0, v___x_1827_);
v___x_1829_ = v___x_1820_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v___x_1827_);
v___x_1829_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___x_1830_ = l_Lean_MessageData_ofFormat(v___x_1829_);
v___x_1831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1826_);
lean_ctor_set(v___x_1831_, 1, v___x_1830_);
v___x_1832_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__3);
v___x_1833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1831_);
lean_ctor_set(v___x_1833_, 1, v___x_1832_);
v___x_1834_ = l_Lean_Exception_toMessageData(v_a_1818_);
v___x_1835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1833_);
lean_ctor_set(v___x_1835_, 1, v___x_1834_);
v___x_1836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1835_);
return v___x_1836_;
}
}
}
else
{
lean_object* v_a_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1895_; 
v_a_1839_ = lean_ctor_get(v_x_1807_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v_x_1807_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1841_ = v_x_1807_;
v_isShared_1842_ = v_isSharedCheck_1895_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_a_1839_);
lean_dec(v_x_1807_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1895_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
if (lean_obj_tag(v_a_1839_) == 0)
{
uint8_t v_done_1843_; 
v_done_1843_ = lean_ctor_get_uint8(v_a_1839_, 0);
lean_dec_ref(v_a_1839_);
if (v_done_1843_ == 1)
{
lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1851_; 
v___x_1844_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__1);
v___x_1845_ = l_Lean_MessageData_ofName(v_typeName_1804_);
v___x_1846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1844_);
lean_ctor_set(v___x_1846_, 1, v___x_1845_);
v___x_1847_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_1848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1846_);
lean_ctor_set(v___x_1848_, 1, v___x_1847_);
v___x_1849_ = l_Nat_reprFast(v_idx_1805_);
if (v_isShared_1842_ == 0)
{
lean_ctor_set_tag(v___x_1841_, 3);
lean_ctor_set(v___x_1841_, 0, v___x_1849_);
v___x_1851_ = v___x_1841_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v___x_1849_);
v___x_1851_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1852_ = l_Lean_MessageData_ofFormat(v___x_1851_);
v___x_1853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1848_);
lean_ctor_set(v___x_1853_, 1, v___x_1852_);
v___x_1854_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__5, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__5_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__5);
v___x_1855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1853_);
lean_ctor_set(v___x_1855_, 1, v___x_1854_);
v___x_1856_ = l_Lean_indentExpr(v_e_1806_);
v___x_1857_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1855_);
lean_ctor_set(v___x_1857_, 1, v___x_1856_);
v___x_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1857_);
return v___x_1858_;
}
}
else
{
lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1867_; 
lean_dec_ref(v_e_1806_);
v___x_1860_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__1);
v___x_1861_ = l_Lean_MessageData_ofName(v_typeName_1804_);
v___x_1862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1860_);
lean_ctor_set(v___x_1862_, 1, v___x_1861_);
v___x_1863_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_1864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1862_);
lean_ctor_set(v___x_1864_, 1, v___x_1863_);
v___x_1865_ = l_Nat_reprFast(v_idx_1805_);
if (v_isShared_1842_ == 0)
{
lean_ctor_set_tag(v___x_1841_, 3);
lean_ctor_set(v___x_1841_, 0, v___x_1865_);
v___x_1867_ = v___x_1841_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v___x_1865_);
v___x_1867_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1868_ = l_Lean_MessageData_ofFormat(v___x_1867_);
v___x_1869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1864_);
lean_ctor_set(v___x_1869_, 1, v___x_1868_);
v___x_1870_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__7, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__7_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__7);
v___x_1871_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1869_);
lean_ctor_set(v___x_1871_, 1, v___x_1870_);
v___x_1872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1871_);
return v___x_1872_;
}
}
}
else
{
lean_object* v_e_x27_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1882_; 
v_e_x27_1874_ = lean_ctor_get(v_a_1839_, 0);
lean_inc_ref(v_e_x27_1874_);
lean_dec_ref(v_a_1839_);
v___x_1875_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__1);
v___x_1876_ = l_Lean_MessageData_ofName(v_typeName_1804_);
v___x_1877_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1875_);
lean_ctor_set(v___x_1877_, 1, v___x_1876_);
v___x_1878_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_1879_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1879_, 0, v___x_1877_);
lean_ctor_set(v___x_1879_, 1, v___x_1878_);
v___x_1880_ = l_Nat_reprFast(v_idx_1805_);
if (v_isShared_1842_ == 0)
{
lean_ctor_set_tag(v___x_1841_, 3);
lean_ctor_set(v___x_1841_, 0, v___x_1880_);
v___x_1882_ = v___x_1841_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v___x_1880_);
v___x_1882_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1883_ = l_Lean_MessageData_ofFormat(v___x_1882_);
v___x_1884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1879_);
lean_ctor_set(v___x_1884_, 1, v___x_1883_);
v___x_1885_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__9, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__9_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__9);
v___x_1886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1884_);
lean_ctor_set(v___x_1886_, 1, v___x_1885_);
v___x_1887_ = l_Lean_indentExpr(v_e_1806_);
v___x_1888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1886_);
lean_ctor_set(v___x_1888_, 1, v___x_1887_);
v___x_1889_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_1890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1888_);
lean_ctor_set(v___x_1890_, 1, v___x_1889_);
v___x_1891_ = l_Lean_indentExpr(v_e_x27_1874_);
v___x_1892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1892_, 0, v___x_1890_);
lean_ctor_set(v___x_1892_, 1, v___x_1891_);
v___x_1893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1892_);
return v___x_1893_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___boxed(lean_object* v_typeName_1896_, lean_object* v_idx_1897_, lean_object* v_e_1898_, lean_object* v_x_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_){
_start:
{
lean_object* v_res_1910_; 
v_res_1910_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0(v_typeName_1896_, v_idx_1897_, v_e_1898_, v_x_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_);
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
lean_dec(v___y_1900_);
return v_res_1910_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__6___redArg(lean_object* v_x_1911_){
_start:
{
if (lean_obj_tag(v_x_1911_) == 0)
{
lean_object* v_a_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1920_; 
v_a_1913_ = lean_ctor_get(v_x_1911_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v_x_1911_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1915_ = v_x_1911_;
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_a_1913_);
lean_dec(v_x_1911_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1918_; 
if (v_isShared_1916_ == 0)
{
lean_ctor_set_tag(v___x_1915_, 1);
v___x_1918_ = v___x_1915_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_a_1913_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
else
{
lean_object* v_a_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1928_; 
v_a_1921_ = lean_ctor_get(v_x_1911_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v_x_1911_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1923_ = v_x_1911_;
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_a_1921_);
lean_dec(v_x_1911_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1926_; 
if (v_isShared_1924_ == 0)
{
lean_ctor_set_tag(v___x_1923_, 0);
v___x_1926_ = v___x_1923_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_a_1921_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__6___redArg___boxed(lean_object* v_x_1929_, lean_object* v___y_1930_){
_start:
{
lean_object* v_res_1931_; 
v_res_1931_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__6___redArg(v_x_1929_);
return v_res_1931_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5_spec__6(size_t v_sz_1932_, size_t v_i_1933_, lean_object* v_bs_1934_){
_start:
{
uint8_t v___x_1935_; 
v___x_1935_ = lean_usize_dec_lt(v_i_1933_, v_sz_1932_);
if (v___x_1935_ == 0)
{
return v_bs_1934_;
}
else
{
lean_object* v_v_1936_; lean_object* v_msg_1937_; lean_object* v___x_1938_; lean_object* v_bs_x27_1939_; size_t v___x_1940_; size_t v___x_1941_; lean_object* v___x_1942_; 
v_v_1936_ = lean_array_uget_borrowed(v_bs_1934_, v_i_1933_);
v_msg_1937_ = lean_ctor_get(v_v_1936_, 1);
lean_inc_ref(v_msg_1937_);
v___x_1938_ = lean_unsigned_to_nat(0u);
v_bs_x27_1939_ = lean_array_uset(v_bs_1934_, v_i_1933_, v___x_1938_);
v___x_1940_ = ((size_t)1ULL);
v___x_1941_ = lean_usize_add(v_i_1933_, v___x_1940_);
v___x_1942_ = lean_array_uset(v_bs_x27_1939_, v_i_1933_, v_msg_1937_);
v_i_1933_ = v___x_1941_;
v_bs_1934_ = v___x_1942_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5_spec__6___boxed(lean_object* v_sz_1944_, lean_object* v_i_1945_, lean_object* v_bs_1946_){
_start:
{
size_t v_sz_boxed_1947_; size_t v_i_boxed_1948_; lean_object* v_res_1949_; 
v_sz_boxed_1947_ = lean_unbox_usize(v_sz_1944_);
lean_dec(v_sz_1944_);
v_i_boxed_1948_ = lean_unbox_usize(v_i_1945_);
lean_dec(v_i_1945_);
v_res_1949_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5_spec__6(v_sz_boxed_1947_, v_i_boxed_1948_, v_bs_1946_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5___redArg(lean_object* v_oldTraces_1950_, lean_object* v_data_1951_, lean_object* v_ref_1952_, lean_object* v_msg_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_){
_start:
{
lean_object* v_fileName_1959_; lean_object* v_fileMap_1960_; lean_object* v_options_1961_; lean_object* v_currRecDepth_1962_; lean_object* v_maxRecDepth_1963_; lean_object* v_ref_1964_; lean_object* v_currNamespace_1965_; lean_object* v_openDecls_1966_; lean_object* v_initHeartbeats_1967_; lean_object* v_maxHeartbeats_1968_; lean_object* v_quotContext_1969_; lean_object* v_currMacroScope_1970_; uint8_t v_diag_1971_; lean_object* v_cancelTk_x3f_1972_; uint8_t v_suppressElabErrors_1973_; lean_object* v_inheritedTraceOptions_1974_; lean_object* v___x_1975_; lean_object* v_traceState_1976_; lean_object* v_traces_1977_; lean_object* v_ref_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; size_t v_sz_1981_; size_t v___x_1982_; lean_object* v___x_1983_; lean_object* v_msg_1984_; lean_object* v___x_1985_; lean_object* v_a_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_2024_; 
v_fileName_1959_ = lean_ctor_get(v___y_1956_, 0);
v_fileMap_1960_ = lean_ctor_get(v___y_1956_, 1);
v_options_1961_ = lean_ctor_get(v___y_1956_, 2);
v_currRecDepth_1962_ = lean_ctor_get(v___y_1956_, 3);
v_maxRecDepth_1963_ = lean_ctor_get(v___y_1956_, 4);
v_ref_1964_ = lean_ctor_get(v___y_1956_, 5);
v_currNamespace_1965_ = lean_ctor_get(v___y_1956_, 6);
v_openDecls_1966_ = lean_ctor_get(v___y_1956_, 7);
v_initHeartbeats_1967_ = lean_ctor_get(v___y_1956_, 8);
v_maxHeartbeats_1968_ = lean_ctor_get(v___y_1956_, 9);
v_quotContext_1969_ = lean_ctor_get(v___y_1956_, 10);
v_currMacroScope_1970_ = lean_ctor_get(v___y_1956_, 11);
v_diag_1971_ = lean_ctor_get_uint8(v___y_1956_, sizeof(void*)*14);
v_cancelTk_x3f_1972_ = lean_ctor_get(v___y_1956_, 12);
v_suppressElabErrors_1973_ = lean_ctor_get_uint8(v___y_1956_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1974_ = lean_ctor_get(v___y_1956_, 13);
v___x_1975_ = lean_st_ref_get(v___y_1957_);
v_traceState_1976_ = lean_ctor_get(v___x_1975_, 4);
lean_inc_ref(v_traceState_1976_);
lean_dec(v___x_1975_);
v_traces_1977_ = lean_ctor_get(v_traceState_1976_, 0);
lean_inc_ref(v_traces_1977_);
lean_dec_ref(v_traceState_1976_);
v_ref_1978_ = l_Lean_replaceRef(v_ref_1952_, v_ref_1964_);
lean_inc_ref(v_inheritedTraceOptions_1974_);
lean_inc(v_cancelTk_x3f_1972_);
lean_inc(v_currMacroScope_1970_);
lean_inc(v_quotContext_1969_);
lean_inc(v_maxHeartbeats_1968_);
lean_inc(v_initHeartbeats_1967_);
lean_inc(v_openDecls_1966_);
lean_inc(v_currNamespace_1965_);
lean_inc(v_maxRecDepth_1963_);
lean_inc(v_currRecDepth_1962_);
lean_inc_ref(v_options_1961_);
lean_inc_ref(v_fileMap_1960_);
lean_inc_ref(v_fileName_1959_);
v___x_1979_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1979_, 0, v_fileName_1959_);
lean_ctor_set(v___x_1979_, 1, v_fileMap_1960_);
lean_ctor_set(v___x_1979_, 2, v_options_1961_);
lean_ctor_set(v___x_1979_, 3, v_currRecDepth_1962_);
lean_ctor_set(v___x_1979_, 4, v_maxRecDepth_1963_);
lean_ctor_set(v___x_1979_, 5, v_ref_1978_);
lean_ctor_set(v___x_1979_, 6, v_currNamespace_1965_);
lean_ctor_set(v___x_1979_, 7, v_openDecls_1966_);
lean_ctor_set(v___x_1979_, 8, v_initHeartbeats_1967_);
lean_ctor_set(v___x_1979_, 9, v_maxHeartbeats_1968_);
lean_ctor_set(v___x_1979_, 10, v_quotContext_1969_);
lean_ctor_set(v___x_1979_, 11, v_currMacroScope_1970_);
lean_ctor_set(v___x_1979_, 12, v_cancelTk_x3f_1972_);
lean_ctor_set(v___x_1979_, 13, v_inheritedTraceOptions_1974_);
lean_ctor_set_uint8(v___x_1979_, sizeof(void*)*14, v_diag_1971_);
lean_ctor_set_uint8(v___x_1979_, sizeof(void*)*14 + 1, v_suppressElabErrors_1973_);
v___x_1980_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1977_);
lean_dec_ref(v_traces_1977_);
v_sz_1981_ = lean_array_size(v___x_1980_);
v___x_1982_ = ((size_t)0ULL);
v___x_1983_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5_spec__6(v_sz_1981_, v___x_1982_, v___x_1980_);
v_msg_1984_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1984_, 0, v_data_1951_);
lean_ctor_set(v_msg_1984_, 1, v_msg_1953_);
lean_ctor_set(v_msg_1984_, 2, v___x_1983_);
v___x_1985_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0_spec__0(v_msg_1984_, v___y_1954_, v___y_1955_, v___x_1979_, v___y_1957_);
lean_dec_ref(v___x_1979_);
v_a_1986_ = lean_ctor_get(v___x_1985_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_1985_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_1988_ = v___x_1985_;
v_isShared_1989_ = v_isSharedCheck_2024_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_a_1986_);
lean_dec(v___x_1985_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_2024_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1990_; lean_object* v_traceState_1991_; lean_object* v_env_1992_; lean_object* v_nextMacroScope_1993_; lean_object* v_ngen_1994_; lean_object* v_auxDeclNGen_1995_; lean_object* v_cache_1996_; lean_object* v_messages_1997_; lean_object* v_infoState_1998_; lean_object* v_snapshotTasks_1999_; lean_object* v_newDecls_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2023_; 
v___x_1990_ = lean_st_ref_take(v___y_1957_);
v_traceState_1991_ = lean_ctor_get(v___x_1990_, 4);
v_env_1992_ = lean_ctor_get(v___x_1990_, 0);
v_nextMacroScope_1993_ = lean_ctor_get(v___x_1990_, 1);
v_ngen_1994_ = lean_ctor_get(v___x_1990_, 2);
v_auxDeclNGen_1995_ = lean_ctor_get(v___x_1990_, 3);
v_cache_1996_ = lean_ctor_get(v___x_1990_, 5);
v_messages_1997_ = lean_ctor_get(v___x_1990_, 6);
v_infoState_1998_ = lean_ctor_get(v___x_1990_, 7);
v_snapshotTasks_1999_ = lean_ctor_get(v___x_1990_, 8);
v_newDecls_2000_ = lean_ctor_get(v___x_1990_, 9);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2002_ = v___x_1990_;
v_isShared_2003_ = v_isSharedCheck_2023_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_newDecls_2000_);
lean_inc(v_snapshotTasks_1999_);
lean_inc(v_infoState_1998_);
lean_inc(v_messages_1997_);
lean_inc(v_cache_1996_);
lean_inc(v_traceState_1991_);
lean_inc(v_auxDeclNGen_1995_);
lean_inc(v_ngen_1994_);
lean_inc(v_nextMacroScope_1993_);
lean_inc(v_env_1992_);
lean_dec(v___x_1990_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2023_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
uint64_t v_tid_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2021_; 
v_tid_2004_ = lean_ctor_get_uint64(v_traceState_1991_, sizeof(void*)*1);
v_isSharedCheck_2021_ = !lean_is_exclusive(v_traceState_1991_);
if (v_isSharedCheck_2021_ == 0)
{
lean_object* v_unused_2022_; 
v_unused_2022_ = lean_ctor_get(v_traceState_1991_, 0);
lean_dec(v_unused_2022_);
v___x_2006_ = v_traceState_1991_;
v_isShared_2007_ = v_isSharedCheck_2021_;
goto v_resetjp_2005_;
}
else
{
lean_dec(v_traceState_1991_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2021_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2011_; 
v___x_2008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2008_, 0, v_ref_1952_);
lean_ctor_set(v___x_2008_, 1, v_a_1986_);
v___x_2009_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1950_, v___x_2008_);
if (v_isShared_2007_ == 0)
{
lean_ctor_set(v___x_2006_, 0, v___x_2009_);
v___x_2011_ = v___x_2006_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v___x_2009_);
lean_ctor_set_uint64(v_reuseFailAlloc_2020_, sizeof(void*)*1, v_tid_2004_);
v___x_2011_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
lean_object* v___x_2013_; 
if (v_isShared_2003_ == 0)
{
lean_ctor_set(v___x_2002_, 4, v___x_2011_);
v___x_2013_ = v___x_2002_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_env_1992_);
lean_ctor_set(v_reuseFailAlloc_2019_, 1, v_nextMacroScope_1993_);
lean_ctor_set(v_reuseFailAlloc_2019_, 2, v_ngen_1994_);
lean_ctor_set(v_reuseFailAlloc_2019_, 3, v_auxDeclNGen_1995_);
lean_ctor_set(v_reuseFailAlloc_2019_, 4, v___x_2011_);
lean_ctor_set(v_reuseFailAlloc_2019_, 5, v_cache_1996_);
lean_ctor_set(v_reuseFailAlloc_2019_, 6, v_messages_1997_);
lean_ctor_set(v_reuseFailAlloc_2019_, 7, v_infoState_1998_);
lean_ctor_set(v_reuseFailAlloc_2019_, 8, v_snapshotTasks_1999_);
lean_ctor_set(v_reuseFailAlloc_2019_, 9, v_newDecls_2000_);
v___x_2013_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2017_; 
v___x_2014_ = lean_st_ref_set(v___y_1957_, v___x_2013_);
v___x_2015_ = lean_box(0);
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 0, v___x_2015_);
v___x_2017_ = v___x_1988_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v___x_2015_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
return v___x_2017_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5___redArg___boxed(lean_object* v_oldTraces_2025_, lean_object* v_data_2026_, lean_object* v_ref_2027_, lean_object* v_msg_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_){
_start:
{
lean_object* v_res_2034_; 
v_res_2034_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5___redArg(v_oldTraces_2025_, v_data_2026_, v_ref_2027_, v_msg_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_);
lean_dec(v___y_2032_);
lean_dec_ref(v___y_2031_);
lean_dec(v___y_2030_);
lean_dec_ref(v___y_2029_);
return v_res_2034_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4(lean_object* v_e_2035_){
_start:
{
if (lean_obj_tag(v_e_2035_) == 0)
{
uint8_t v___x_2036_; 
v___x_2036_ = 2;
return v___x_2036_;
}
else
{
uint8_t v___x_2037_; 
v___x_2037_ = 0;
return v___x_2037_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4___boxed(lean_object* v_e_2038_){
_start:
{
uint8_t v_res_2039_; lean_object* v_r_2040_; 
v_res_2039_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4(v_e_2038_);
lean_dec_ref(v_e_2038_);
v_r_2040_ = lean_box(v_res_2039_);
return v_r_2040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(lean_object* v_opts_2041_, lean_object* v_opt_2042_){
_start:
{
lean_object* v_name_2043_; lean_object* v_defValue_2044_; lean_object* v_map_2045_; lean_object* v___x_2046_; 
v_name_2043_ = lean_ctor_get(v_opt_2042_, 0);
v_defValue_2044_ = lean_ctor_get(v_opt_2042_, 1);
v_map_2045_ = lean_ctor_get(v_opts_2041_, 0);
v___x_2046_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2045_, v_name_2043_);
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_inc(v_defValue_2044_);
return v_defValue_2044_;
}
else
{
lean_object* v_val_2047_; 
v_val_2047_ = lean_ctor_get(v___x_2046_, 0);
lean_inc(v_val_2047_);
lean_dec_ref(v___x_2046_);
if (lean_obj_tag(v_val_2047_) == 3)
{
lean_object* v_v_2048_; 
v_v_2048_ = lean_ctor_get(v_val_2047_, 0);
lean_inc(v_v_2048_);
lean_dec_ref(v_val_2047_);
return v_v_2048_;
}
else
{
lean_dec(v_val_2047_);
lean_inc(v_defValue_2044_);
return v_defValue_2044_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7___boxed(lean_object* v_opts_2049_, lean_object* v_opt_2050_){
_start:
{
lean_object* v_res_2051_; 
v_res_2051_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_2049_, v_opt_2050_);
lean_dec_ref(v_opt_2050_);
lean_dec_ref(v_opts_2049_);
return v_res_2051_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1(void){
_start:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2053_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__0));
v___x_2054_ = l_Lean_stringToMessageData(v___x_2053_);
return v___x_2054_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__3(void){
_start:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2056_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2));
v___x_2057_ = l_Lean_stringToMessageData(v___x_2056_);
return v___x_2057_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__4(void){
_start:
{
lean_object* v___x_2058_; double v___x_2059_; 
v___x_2058_ = lean_unsigned_to_nat(1000u);
v___x_2059_ = lean_float_of_nat(v___x_2058_);
return v___x_2059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4(lean_object* v_cls_2060_, uint8_t v_collapsed_2061_, lean_object* v_tag_2062_, lean_object* v_opts_2063_, uint8_t v_clsEnabled_2064_, lean_object* v_oldTraces_2065_, lean_object* v_msg_2066_, lean_object* v_resStartStop_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_){
_start:
{
lean_object* v_fst_2078_; lean_object* v_snd_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2178_; 
v_fst_2078_ = lean_ctor_get(v_resStartStop_2067_, 0);
v_snd_2079_ = lean_ctor_get(v_resStartStop_2067_, 1);
v_isSharedCheck_2178_ = !lean_is_exclusive(v_resStartStop_2067_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2081_ = v_resStartStop_2067_;
v_isShared_2082_ = v_isSharedCheck_2178_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_snd_2079_);
lean_inc(v_fst_2078_);
lean_dec(v_resStartStop_2067_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2178_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___y_2084_; lean_object* v___y_2085_; lean_object* v_data_2086_; lean_object* v_fst_2097_; lean_object* v_snd_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2177_; 
v_fst_2097_ = lean_ctor_get(v_snd_2079_, 0);
v_snd_2098_ = lean_ctor_get(v_snd_2079_, 1);
v_isSharedCheck_2177_ = !lean_is_exclusive(v_snd_2079_);
if (v_isSharedCheck_2177_ == 0)
{
v___x_2100_ = v_snd_2079_;
v_isShared_2101_ = v_isSharedCheck_2177_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_snd_2098_);
lean_inc(v_fst_2097_);
lean_dec(v_snd_2079_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2177_;
goto v_resetjp_2099_;
}
v___jp_2083_:
{
lean_object* v___x_2087_; 
lean_inc(v___y_2085_);
v___x_2087_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5___redArg(v_oldTraces_2065_, v_data_2086_, v___y_2085_, v___y_2084_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v___x_2088_; 
lean_dec_ref(v___x_2087_);
v___x_2088_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__6___redArg(v_fst_2078_);
return v___x_2088_;
}
else
{
lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2096_; 
lean_dec(v_fst_2078_);
v_a_2089_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2091_ = v___x_2087_;
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___x_2087_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2094_; 
if (v_isShared_2092_ == 0)
{
v___x_2094_ = v___x_2091_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_a_2089_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
}
v_resetjp_2099_:
{
lean_object* v___x_2102_; uint8_t v___x_2103_; lean_object* v___y_2105_; lean_object* v_a_2106_; uint8_t v___y_2130_; double v___y_2162_; 
v___x_2102_ = l_Lean_trace_profiler;
v___x_2103_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_2063_, v___x_2102_);
if (v___x_2103_ == 0)
{
v___y_2130_ = v___x_2103_;
goto v___jp_2129_;
}
else
{
lean_object* v___x_2167_; uint8_t v___x_2168_; 
v___x_2167_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2168_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_2063_, v___x_2167_);
if (v___x_2168_ == 0)
{
lean_object* v___x_2169_; lean_object* v___x_2170_; double v___x_2171_; double v___x_2172_; double v___x_2173_; 
v___x_2169_ = l_Lean_trace_profiler_threshold;
v___x_2170_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_2063_, v___x_2169_);
v___x_2171_ = lean_float_of_nat(v___x_2170_);
v___x_2172_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__4);
v___x_2173_ = lean_float_div(v___x_2171_, v___x_2172_);
v___y_2162_ = v___x_2173_;
goto v___jp_2161_;
}
else
{
lean_object* v___x_2174_; lean_object* v___x_2175_; double v___x_2176_; 
v___x_2174_ = l_Lean_trace_profiler_threshold;
v___x_2175_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_2063_, v___x_2174_);
v___x_2176_ = lean_float_of_nat(v___x_2175_);
v___y_2162_ = v___x_2176_;
goto v___jp_2161_;
}
}
v___jp_2104_:
{
uint8_t v_result_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2112_; 
v_result_2107_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4(v_fst_2078_);
v___x_2108_ = l_Lean_TraceResult_toEmoji(v_result_2107_);
v___x_2109_ = l_Lean_stringToMessageData(v___x_2108_);
v___x_2110_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1);
if (v_isShared_2101_ == 0)
{
lean_ctor_set_tag(v___x_2100_, 7);
lean_ctor_set(v___x_2100_, 1, v___x_2110_);
lean_ctor_set(v___x_2100_, 0, v___x_2109_);
v___x_2112_ = v___x_2100_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v___x_2109_);
lean_ctor_set(v_reuseFailAlloc_2123_, 1, v___x_2110_);
v___x_2112_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
lean_object* v_m_2114_; 
if (v_isShared_2082_ == 0)
{
lean_ctor_set_tag(v___x_2081_, 7);
lean_ctor_set(v___x_2081_, 1, v_a_2106_);
lean_ctor_set(v___x_2081_, 0, v___x_2112_);
v_m_2114_ = v___x_2081_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v___x_2112_);
lean_ctor_set(v_reuseFailAlloc_2122_, 1, v_a_2106_);
v_m_2114_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; double v___x_2117_; lean_object* v_data_2118_; 
v___x_2115_ = lean_box(v_result_2107_);
v___x_2116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2115_);
v___x_2117_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_2062_);
lean_inc_ref(v___x_2116_);
lean_inc(v_cls_2060_);
v_data_2118_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2118_, 0, v_cls_2060_);
lean_ctor_set(v_data_2118_, 1, v___x_2116_);
lean_ctor_set(v_data_2118_, 2, v_tag_2062_);
lean_ctor_set_float(v_data_2118_, sizeof(void*)*3, v___x_2117_);
lean_ctor_set_float(v_data_2118_, sizeof(void*)*3 + 8, v___x_2117_);
lean_ctor_set_uint8(v_data_2118_, sizeof(void*)*3 + 16, v_collapsed_2061_);
if (v___x_2103_ == 0)
{
lean_dec_ref(v___x_2116_);
lean_dec(v_snd_2098_);
lean_dec(v_fst_2097_);
lean_dec_ref(v_tag_2062_);
lean_dec(v_cls_2060_);
v___y_2084_ = v_m_2114_;
v___y_2085_ = v___y_2105_;
v_data_2086_ = v_data_2118_;
goto v___jp_2083_;
}
else
{
lean_object* v_data_2119_; double v___x_2120_; double v___x_2121_; 
lean_dec_ref(v_data_2118_);
v_data_2119_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2119_, 0, v_cls_2060_);
lean_ctor_set(v_data_2119_, 1, v___x_2116_);
lean_ctor_set(v_data_2119_, 2, v_tag_2062_);
v___x_2120_ = lean_unbox_float(v_fst_2097_);
lean_dec(v_fst_2097_);
lean_ctor_set_float(v_data_2119_, sizeof(void*)*3, v___x_2120_);
v___x_2121_ = lean_unbox_float(v_snd_2098_);
lean_dec(v_snd_2098_);
lean_ctor_set_float(v_data_2119_, sizeof(void*)*3 + 8, v___x_2121_);
lean_ctor_set_uint8(v_data_2119_, sizeof(void*)*3 + 16, v_collapsed_2061_);
v___y_2084_ = v_m_2114_;
v___y_2085_ = v___y_2105_;
v_data_2086_ = v_data_2119_;
goto v___jp_2083_;
}
}
}
}
v___jp_2124_:
{
lean_object* v_ref_2125_; lean_object* v___x_2126_; 
v_ref_2125_ = lean_ctor_get(v___y_2075_, 5);
lean_inc(v___y_2076_);
lean_inc_ref(v___y_2075_);
lean_inc(v___y_2074_);
lean_inc_ref(v___y_2073_);
lean_inc(v___y_2072_);
lean_inc_ref(v___y_2071_);
lean_inc(v___y_2070_);
lean_inc_ref(v___y_2069_);
lean_inc(v___y_2068_);
lean_inc(v_fst_2078_);
v___x_2126_ = lean_apply_11(v_msg_2066_, v_fst_2078_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, lean_box(0));
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v_a_2127_; 
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
lean_inc(v_a_2127_);
lean_dec_ref(v___x_2126_);
v___y_2105_ = v_ref_2125_;
v_a_2106_ = v_a_2127_;
goto v___jp_2104_;
}
else
{
lean_object* v___x_2128_; 
lean_dec_ref(v___x_2126_);
v___x_2128_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__3);
v___y_2105_ = v_ref_2125_;
v_a_2106_ = v___x_2128_;
goto v___jp_2104_;
}
}
v___jp_2129_:
{
if (v_clsEnabled_2064_ == 0)
{
if (v___y_2130_ == 0)
{
lean_object* v___x_2131_; lean_object* v_traceState_2132_; lean_object* v_env_2133_; lean_object* v_nextMacroScope_2134_; lean_object* v_ngen_2135_; lean_object* v_auxDeclNGen_2136_; lean_object* v_cache_2137_; lean_object* v_messages_2138_; lean_object* v_infoState_2139_; lean_object* v_snapshotTasks_2140_; lean_object* v_newDecls_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2160_; 
lean_del_object(v___x_2100_);
lean_dec(v_snd_2098_);
lean_dec(v_fst_2097_);
lean_del_object(v___x_2081_);
lean_dec_ref(v_msg_2066_);
lean_dec_ref(v_tag_2062_);
lean_dec(v_cls_2060_);
v___x_2131_ = lean_st_ref_take(v___y_2076_);
v_traceState_2132_ = lean_ctor_get(v___x_2131_, 4);
v_env_2133_ = lean_ctor_get(v___x_2131_, 0);
v_nextMacroScope_2134_ = lean_ctor_get(v___x_2131_, 1);
v_ngen_2135_ = lean_ctor_get(v___x_2131_, 2);
v_auxDeclNGen_2136_ = lean_ctor_get(v___x_2131_, 3);
v_cache_2137_ = lean_ctor_get(v___x_2131_, 5);
v_messages_2138_ = lean_ctor_get(v___x_2131_, 6);
v_infoState_2139_ = lean_ctor_get(v___x_2131_, 7);
v_snapshotTasks_2140_ = lean_ctor_get(v___x_2131_, 8);
v_newDecls_2141_ = lean_ctor_get(v___x_2131_, 9);
v_isSharedCheck_2160_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2143_ = v___x_2131_;
v_isShared_2144_ = v_isSharedCheck_2160_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_newDecls_2141_);
lean_inc(v_snapshotTasks_2140_);
lean_inc(v_infoState_2139_);
lean_inc(v_messages_2138_);
lean_inc(v_cache_2137_);
lean_inc(v_traceState_2132_);
lean_inc(v_auxDeclNGen_2136_);
lean_inc(v_ngen_2135_);
lean_inc(v_nextMacroScope_2134_);
lean_inc(v_env_2133_);
lean_dec(v___x_2131_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2160_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
uint64_t v_tid_2145_; lean_object* v_traces_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2159_; 
v_tid_2145_ = lean_ctor_get_uint64(v_traceState_2132_, sizeof(void*)*1);
v_traces_2146_ = lean_ctor_get(v_traceState_2132_, 0);
v_isSharedCheck_2159_ = !lean_is_exclusive(v_traceState_2132_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2148_ = v_traceState_2132_;
v_isShared_2149_ = v_isSharedCheck_2159_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_traces_2146_);
lean_dec(v_traceState_2132_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2159_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2150_; lean_object* v___x_2152_; 
v___x_2150_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2065_, v_traces_2146_);
lean_dec_ref(v_traces_2146_);
if (v_isShared_2149_ == 0)
{
lean_ctor_set(v___x_2148_, 0, v___x_2150_);
v___x_2152_ = v___x_2148_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v___x_2150_);
lean_ctor_set_uint64(v_reuseFailAlloc_2158_, sizeof(void*)*1, v_tid_2145_);
v___x_2152_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
lean_object* v___x_2154_; 
if (v_isShared_2144_ == 0)
{
lean_ctor_set(v___x_2143_, 4, v___x_2152_);
v___x_2154_ = v___x_2143_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_env_2133_);
lean_ctor_set(v_reuseFailAlloc_2157_, 1, v_nextMacroScope_2134_);
lean_ctor_set(v_reuseFailAlloc_2157_, 2, v_ngen_2135_);
lean_ctor_set(v_reuseFailAlloc_2157_, 3, v_auxDeclNGen_2136_);
lean_ctor_set(v_reuseFailAlloc_2157_, 4, v___x_2152_);
lean_ctor_set(v_reuseFailAlloc_2157_, 5, v_cache_2137_);
lean_ctor_set(v_reuseFailAlloc_2157_, 6, v_messages_2138_);
lean_ctor_set(v_reuseFailAlloc_2157_, 7, v_infoState_2139_);
lean_ctor_set(v_reuseFailAlloc_2157_, 8, v_snapshotTasks_2140_);
lean_ctor_set(v_reuseFailAlloc_2157_, 9, v_newDecls_2141_);
v___x_2154_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; 
v___x_2155_ = lean_st_ref_set(v___y_2076_, v___x_2154_);
v___x_2156_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__6___redArg(v_fst_2078_);
return v___x_2156_;
}
}
}
}
}
else
{
goto v___jp_2124_;
}
}
else
{
goto v___jp_2124_;
}
}
v___jp_2161_:
{
double v___x_2163_; double v___x_2164_; double v___x_2165_; uint8_t v___x_2166_; 
v___x_2163_ = lean_unbox_float(v_snd_2098_);
v___x_2164_ = lean_unbox_float(v_fst_2097_);
v___x_2165_ = lean_float_sub(v___x_2163_, v___x_2164_);
v___x_2166_ = lean_float_decLt(v___y_2162_, v___x_2165_);
v___y_2130_ = v___x_2166_;
goto v___jp_2129_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___boxed(lean_object** _args){
lean_object* v_cls_2179_ = _args[0];
lean_object* v_collapsed_2180_ = _args[1];
lean_object* v_tag_2181_ = _args[2];
lean_object* v_opts_2182_ = _args[3];
lean_object* v_clsEnabled_2183_ = _args[4];
lean_object* v_oldTraces_2184_ = _args[5];
lean_object* v_msg_2185_ = _args[6];
lean_object* v_resStartStop_2186_ = _args[7];
lean_object* v___y_2187_ = _args[8];
lean_object* v___y_2188_ = _args[9];
lean_object* v___y_2189_ = _args[10];
lean_object* v___y_2190_ = _args[11];
lean_object* v___y_2191_ = _args[12];
lean_object* v___y_2192_ = _args[13];
lean_object* v___y_2193_ = _args[14];
lean_object* v___y_2194_ = _args[15];
lean_object* v___y_2195_ = _args[16];
lean_object* v___y_2196_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_2197_; uint8_t v_clsEnabled_boxed_2198_; lean_object* v_res_2199_; 
v_collapsed_boxed_2197_ = lean_unbox(v_collapsed_2180_);
v_clsEnabled_boxed_2198_ = lean_unbox(v_clsEnabled_2183_);
v_res_2199_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4(v_cls_2179_, v_collapsed_boxed_2197_, v_tag_2181_, v_opts_2182_, v_clsEnabled_boxed_2198_, v_oldTraces_2184_, v_msg_2185_, v_resStartStop_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_);
lean_dec(v___y_2195_);
lean_dec_ref(v___y_2194_);
lean_dec(v___y_2193_);
lean_dec_ref(v___y_2192_);
lean_dec(v___y_2191_);
lean_dec_ref(v___y_2190_);
lean_dec(v___y_2189_);
lean_dec_ref(v___y_2188_);
lean_dec(v___y_2187_);
lean_dec_ref(v_opts_2182_);
return v_res_2199_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2(void){
_start:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2203_ = lean_unsigned_to_nat(0u);
v___x_2204_ = l_Lean_Expr_bvar___override(v___x_2203_);
return v___x_2204_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8(void){
_start:
{
lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2211_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__7));
v___x_2212_ = lean_unsigned_to_nat(48u);
v___x_2213_ = lean_unsigned_to_nat(219u);
v___x_2214_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__6));
v___x_2215_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__5));
v___x_2216_ = l_mkPanicMessageWithDecl(v___x_2215_, v___x_2214_, v___x_2213_, v___x_2212_, v___x_2211_);
return v___x_2216_;
}
}
static double _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9(void){
_start:
{
lean_object* v___x_2217_; double v___x_2218_; 
v___x_2217_ = lean_unsigned_to_nat(1000000000u);
v___x_2218_ = lean_float_of_nat(v___x_2217_);
return v___x_2218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj(lean_object* v_e_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_){
_start:
{
uint8_t v___y_2231_; uint8_t v___y_2232_; lean_object* v___y_2233_; lean_object* v_a_2234_; uint8_t v___y_2238_; lean_object* v___y_2239_; lean_object* v_a_2240_; 
if (lean_obj_tag(v_e_2219_) == 11)
{
lean_object* v_typeName_2244_; lean_object* v_idx_2245_; lean_object* v_struct_2246_; lean_object* v_res_2248_; lean_object* v___y_2249_; lean_object* v___y_2250_; lean_object* v___y_2251_; lean_object* v___y_2252_; lean_object* v___y_2253_; lean_object* v___y_2254_; lean_object* v___y_2255_; lean_object* v___y_2256_; lean_object* v___y_2257_; lean_object* v_options_2484_; uint8_t v_hasTrace_2485_; 
v_typeName_2244_ = lean_ctor_get(v_e_2219_, 0);
v_idx_2245_ = lean_ctor_get(v_e_2219_, 1);
v_struct_2246_ = lean_ctor_get(v_e_2219_, 2);
v_options_2484_ = lean_ctor_get(v_a_2227_, 2);
v_hasTrace_2485_ = lean_ctor_get_uint8(v_options_2484_, sizeof(void*)*1);
if (v_hasTrace_2485_ == 0)
{
lean_object* v___x_2486_; 
lean_inc(v_a_2228_);
lean_inc_ref(v_a_2227_);
lean_inc(v_a_2226_);
lean_inc_ref(v_a_2225_);
lean_inc(v_a_2224_);
lean_inc_ref(v_a_2223_);
lean_inc(v_a_2222_);
lean_inc_ref(v_a_2221_);
lean_inc(v_a_2220_);
lean_inc_ref(v_struct_2246_);
v___x_2486_ = lean_sym_simp(v_struct_2246_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
if (lean_obj_tag(v___x_2486_) == 0)
{
lean_object* v_a_2487_; 
v_a_2487_ = lean_ctor_get(v___x_2486_, 0);
lean_inc(v_a_2487_);
lean_dec_ref(v___x_2486_);
v_res_2248_ = v_a_2487_;
v___y_2249_ = v_a_2220_;
v___y_2250_ = v_a_2221_;
v___y_2251_ = v_a_2222_;
v___y_2252_ = v_a_2223_;
v___y_2253_ = v_a_2224_;
v___y_2254_ = v_a_2225_;
v___y_2255_ = v_a_2226_;
v___y_2256_ = v_a_2227_;
v___y_2257_ = v_a_2228_;
goto v___jp_2247_;
}
else
{
lean_dec_ref(v_e_2219_);
return v___x_2486_;
}
}
else
{
lean_object* v_inheritedTraceOptions_2488_; lean_object* v___f_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; uint8_t v___x_2493_; lean_object* v___y_2495_; lean_object* v___y_2496_; lean_object* v_a_2497_; lean_object* v___y_2510_; lean_object* v___y_2511_; lean_object* v_a_2512_; lean_object* v___y_2515_; lean_object* v___y_2516_; lean_object* v_a_2517_; lean_object* v___y_2520_; lean_object* v___y_2521_; lean_object* v___y_2522_; uint8_t v___y_2526_; lean_object* v___y_2527_; lean_object* v___y_2528_; uint8_t v___y_2529_; lean_object* v___y_2530_; lean_object* v_a_2531_; uint8_t v___y_2534_; lean_object* v___y_2535_; uint8_t v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v_a_2539_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v_a_2544_; lean_object* v___y_2554_; lean_object* v___y_2555_; lean_object* v_a_2556_; lean_object* v___y_2559_; lean_object* v___y_2560_; lean_object* v_a_2561_; lean_object* v___y_2564_; lean_object* v___y_2565_; lean_object* v___y_2566_; uint8_t v___y_2570_; uint8_t v___y_2571_; lean_object* v___y_2572_; lean_object* v___y_2573_; lean_object* v___y_2574_; lean_object* v_a_2575_; uint8_t v___y_2578_; lean_object* v___y_2579_; lean_object* v___y_2580_; lean_object* v___y_2581_; lean_object* v_a_2582_; 
v_inheritedTraceOptions_2488_ = lean_ctor_get(v_a_2227_, 13);
lean_inc_ref(v_e_2219_);
lean_inc(v_idx_2245_);
lean_inc(v_typeName_2244_);
v___f_2489_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___boxed), 14, 3);
lean_closure_set(v___f_2489_, 0, v_typeName_2244_);
lean_closure_set(v___f_2489_, 1, v_idx_2245_);
lean_closure_set(v___f_2489_, 2, v_e_2219_);
v___x_2490_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2));
v___x_2491_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__1));
v___x_2492_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3);
v___x_2493_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2488_, v_options_2484_, v___x_2492_);
if (v___x_2493_ == 0)
{
lean_object* v___x_2777_; uint8_t v___x_2778_; 
v___x_2777_ = l_Lean_trace_profiler;
v___x_2778_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_2484_, v___x_2777_);
if (v___x_2778_ == 0)
{
lean_object* v___x_2779_; 
lean_dec_ref(v___f_2489_);
lean_inc(v_a_2228_);
lean_inc_ref(v_a_2227_);
lean_inc(v_a_2226_);
lean_inc_ref(v_a_2225_);
lean_inc(v_a_2224_);
lean_inc_ref(v_a_2223_);
lean_inc(v_a_2222_);
lean_inc_ref(v_a_2221_);
lean_inc(v_a_2220_);
lean_inc_ref(v_struct_2246_);
v___x_2779_ = lean_sym_simp(v_struct_2246_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
if (lean_obj_tag(v___x_2779_) == 0)
{
lean_object* v_a_2780_; 
v_a_2780_ = lean_ctor_get(v___x_2779_, 0);
lean_inc(v_a_2780_);
lean_dec_ref(v___x_2779_);
v_res_2248_ = v_a_2780_;
v___y_2249_ = v_a_2220_;
v___y_2250_ = v_a_2221_;
v___y_2251_ = v_a_2222_;
v___y_2252_ = v_a_2223_;
v___y_2253_ = v_a_2224_;
v___y_2254_ = v_a_2225_;
v___y_2255_ = v_a_2226_;
v___y_2256_ = v_a_2227_;
v___y_2257_ = v_a_2228_;
goto v___jp_2247_;
}
else
{
lean_dec_ref(v_e_2219_);
return v___x_2779_;
}
}
else
{
goto v___jp_2585_;
}
}
else
{
goto v___jp_2585_;
}
v___jp_2494_:
{
lean_object* v___x_2498_; double v___x_2499_; double v___x_2500_; double v___x_2501_; double v___x_2502_; double v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; 
v___x_2498_ = lean_io_mono_nanos_now();
v___x_2499_ = lean_float_of_nat(v___y_2495_);
v___x_2500_ = lean_float_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9);
v___x_2501_ = lean_float_div(v___x_2499_, v___x_2500_);
v___x_2502_ = lean_float_of_nat(v___x_2498_);
v___x_2503_ = lean_float_div(v___x_2502_, v___x_2500_);
v___x_2504_ = lean_box_float(v___x_2501_);
v___x_2505_ = lean_box_float(v___x_2503_);
v___x_2506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2506_, 0, v___x_2504_);
lean_ctor_set(v___x_2506_, 1, v___x_2505_);
v___x_2507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2507_, 0, v_a_2497_);
lean_ctor_set(v___x_2507_, 1, v___x_2506_);
v___x_2508_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4(v___x_2490_, v_hasTrace_2485_, v___x_2491_, v_options_2484_, v___x_2493_, v___y_2496_, v___f_2489_, v___x_2507_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
return v___x_2508_;
}
v___jp_2509_:
{
lean_object* v___x_2513_; 
v___x_2513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2513_, 0, v_a_2512_);
v___y_2495_ = v___y_2510_;
v___y_2496_ = v___y_2511_;
v_a_2497_ = v___x_2513_;
goto v___jp_2494_;
}
v___jp_2514_:
{
lean_object* v___x_2518_; 
v___x_2518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2518_, 0, v_a_2517_);
v___y_2495_ = v___y_2515_;
v___y_2496_ = v___y_2516_;
v_a_2497_ = v___x_2518_;
goto v___jp_2494_;
}
v___jp_2519_:
{
if (lean_obj_tag(v___y_2522_) == 0)
{
lean_object* v_a_2523_; 
v_a_2523_ = lean_ctor_get(v___y_2522_, 0);
lean_inc(v_a_2523_);
lean_dec_ref(v___y_2522_);
v___y_2515_ = v___y_2520_;
v___y_2516_ = v___y_2521_;
v_a_2517_ = v_a_2523_;
goto v___jp_2514_;
}
else
{
lean_object* v_a_2524_; 
v_a_2524_ = lean_ctor_get(v___y_2522_, 0);
lean_inc(v_a_2524_);
lean_dec_ref(v___y_2522_);
v___y_2510_ = v___y_2520_;
v___y_2511_ = v___y_2521_;
v_a_2512_ = v_a_2524_;
goto v___jp_2509_;
}
}
v___jp_2525_:
{
lean_object* v___x_2532_; 
v___x_2532_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2532_, 0, v_a_2531_);
lean_ctor_set(v___x_2532_, 1, v___y_2528_);
lean_ctor_set_uint8(v___x_2532_, sizeof(void*)*2, v___y_2529_);
lean_ctor_set_uint8(v___x_2532_, sizeof(void*)*2 + 1, v___y_2526_);
v___y_2515_ = v___y_2527_;
v___y_2516_ = v___y_2530_;
v_a_2517_ = v___x_2532_;
goto v___jp_2514_;
}
v___jp_2533_:
{
lean_object* v___x_2540_; 
v___x_2540_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2540_, 0, v_a_2539_);
lean_ctor_set(v___x_2540_, 1, v___y_2538_);
lean_ctor_set_uint8(v___x_2540_, sizeof(void*)*2, v___y_2536_);
lean_ctor_set_uint8(v___x_2540_, sizeof(void*)*2 + 1, v___y_2534_);
v___y_2515_ = v___y_2535_;
v___y_2516_ = v___y_2537_;
v_a_2517_ = v___x_2540_;
goto v___jp_2514_;
}
v___jp_2541_:
{
lean_object* v___x_2545_; double v___x_2546_; double v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2545_ = lean_io_get_num_heartbeats();
v___x_2546_ = lean_float_of_nat(v___y_2543_);
v___x_2547_ = lean_float_of_nat(v___x_2545_);
v___x_2548_ = lean_box_float(v___x_2546_);
v___x_2549_ = lean_box_float(v___x_2547_);
v___x_2550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2548_);
lean_ctor_set(v___x_2550_, 1, v___x_2549_);
v___x_2551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2551_, 0, v_a_2544_);
lean_ctor_set(v___x_2551_, 1, v___x_2550_);
v___x_2552_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4(v___x_2490_, v_hasTrace_2485_, v___x_2491_, v_options_2484_, v___x_2493_, v___y_2542_, v___f_2489_, v___x_2551_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
return v___x_2552_;
}
v___jp_2553_:
{
lean_object* v___x_2557_; 
v___x_2557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2557_, 0, v_a_2556_);
v___y_2542_ = v___y_2555_;
v___y_2543_ = v___y_2554_;
v_a_2544_ = v___x_2557_;
goto v___jp_2541_;
}
v___jp_2558_:
{
lean_object* v___x_2562_; 
v___x_2562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2562_, 0, v_a_2561_);
v___y_2542_ = v___y_2560_;
v___y_2543_ = v___y_2559_;
v_a_2544_ = v___x_2562_;
goto v___jp_2541_;
}
v___jp_2563_:
{
if (lean_obj_tag(v___y_2566_) == 0)
{
lean_object* v_a_2567_; 
v_a_2567_ = lean_ctor_get(v___y_2566_, 0);
lean_inc(v_a_2567_);
lean_dec_ref(v___y_2566_);
v___y_2559_ = v___y_2565_;
v___y_2560_ = v___y_2564_;
v_a_2561_ = v_a_2567_;
goto v___jp_2558_;
}
else
{
lean_object* v_a_2568_; 
v_a_2568_ = lean_ctor_get(v___y_2566_, 0);
lean_inc(v_a_2568_);
lean_dec_ref(v___y_2566_);
v___y_2554_ = v___y_2565_;
v___y_2555_ = v___y_2564_;
v_a_2556_ = v_a_2568_;
goto v___jp_2553_;
}
}
v___jp_2569_:
{
lean_object* v___x_2576_; 
v___x_2576_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2576_, 0, v_a_2575_);
lean_ctor_set(v___x_2576_, 1, v___y_2572_);
lean_ctor_set_uint8(v___x_2576_, sizeof(void*)*2, v___y_2570_);
lean_ctor_set_uint8(v___x_2576_, sizeof(void*)*2 + 1, v___y_2571_);
v___y_2559_ = v___y_2574_;
v___y_2560_ = v___y_2573_;
v_a_2561_ = v___x_2576_;
goto v___jp_2558_;
}
v___jp_2577_:
{
uint8_t v___x_2583_; lean_object* v___x_2584_; 
v___x_2583_ = 0;
v___x_2584_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2584_, 0, v_a_2582_);
lean_ctor_set(v___x_2584_, 1, v___y_2579_);
lean_ctor_set_uint8(v___x_2584_, sizeof(void*)*2, v___y_2578_);
lean_ctor_set_uint8(v___x_2584_, sizeof(void*)*2 + 1, v___x_2583_);
v___y_2559_ = v___y_2581_;
v___y_2560_ = v___y_2580_;
v_a_2561_ = v___x_2584_;
goto v___jp_2558_;
}
v___jp_2585_:
{
lean_object* v___x_2586_; lean_object* v_a_2587_; lean_object* v___x_2588_; uint8_t v___x_2589_; 
v___x_2586_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg(v_a_2228_);
v_a_2587_ = lean_ctor_get(v___x_2586_, 0);
lean_inc(v_a_2587_);
lean_dec_ref(v___x_2586_);
v___x_2588_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2589_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_2484_, v___x_2588_);
if (v___x_2589_ == 0)
{
lean_object* v___x_2590_; lean_object* v___x_2591_; 
v___x_2590_ = lean_io_mono_nanos_now();
lean_inc(v_a_2228_);
lean_inc_ref(v_a_2227_);
lean_inc(v_a_2226_);
lean_inc_ref(v_a_2225_);
lean_inc(v_a_2224_);
lean_inc_ref(v_a_2223_);
lean_inc(v_a_2222_);
lean_inc_ref(v_a_2221_);
lean_inc(v_a_2220_);
lean_inc_ref(v_struct_2246_);
v___x_2591_ = lean_sym_simp(v_struct_2246_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_object* v_a_2592_; 
v_a_2592_ = lean_ctor_get(v___x_2591_, 0);
lean_inc(v_a_2592_);
lean_dec_ref(v___x_2591_);
if (lean_obj_tag(v_a_2592_) == 0)
{
uint8_t v_contextDependent_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2612_; 
v_contextDependent_2593_ = lean_ctor_get_uint8(v_a_2592_, 1);
v_isSharedCheck_2612_ = !lean_is_exclusive(v_a_2592_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2595_ = v_a_2592_;
v_isShared_2596_ = v_isSharedCheck_2612_;
goto v_resetjp_2594_;
}
else
{
lean_dec(v_a_2592_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2612_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v___x_2597_; lean_object* v___x_2598_; 
v___x_2597_ = lean_alloc_closure((void*)(l_Lean_Meta_reduceProj_x3f___boxed), 6, 1);
lean_closure_set(v___x_2597_, 0, v_e_2219_);
v___x_2598_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___x_2597_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
if (lean_obj_tag(v___x_2598_) == 0)
{
lean_object* v_a_2599_; 
v_a_2599_ = lean_ctor_get(v___x_2598_, 0);
lean_inc(v_a_2599_);
lean_dec_ref(v___x_2598_);
if (lean_obj_tag(v_a_2599_) == 1)
{
lean_object* v_val_2600_; lean_object* v___x_2601_; 
lean_del_object(v___x_2595_);
v_val_2600_ = lean_ctor_get(v_a_2599_, 0);
lean_inc(v_val_2600_);
lean_dec_ref(v_a_2599_);
v___x_2601_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_val_2600_, v_a_2224_);
if (lean_obj_tag(v___x_2601_) == 0)
{
lean_object* v_a_2602_; lean_object* v___x_2603_; 
v_a_2602_ = lean_ctor_get(v___x_2601_, 0);
lean_inc_n(v_a_2602_, 2);
lean_dec_ref(v___x_2601_);
v___x_2603_ = l_Lean_Meta_Sym_mkEqRefl___redArg(v_a_2602_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
if (lean_obj_tag(v___x_2603_) == 0)
{
lean_object* v_a_2604_; lean_object* v___x_2605_; 
v_a_2604_ = lean_ctor_get(v___x_2603_, 0);
lean_inc(v_a_2604_);
lean_dec_ref(v___x_2603_);
v___x_2605_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2605_, 0, v_a_2602_);
lean_ctor_set(v___x_2605_, 1, v_a_2604_);
lean_ctor_set_uint8(v___x_2605_, sizeof(void*)*2, v_contextDependent_2593_);
lean_ctor_set_uint8(v___x_2605_, sizeof(void*)*2 + 1, v___x_2589_);
v___y_2515_ = v___x_2590_;
v___y_2516_ = v_a_2587_;
v_a_2517_ = v___x_2605_;
goto v___jp_2514_;
}
else
{
lean_object* v_a_2606_; 
lean_dec(v_a_2602_);
v_a_2606_ = lean_ctor_get(v___x_2603_, 0);
lean_inc(v_a_2606_);
lean_dec_ref(v___x_2603_);
v___y_2510_ = v___x_2590_;
v___y_2511_ = v_a_2587_;
v_a_2512_ = v_a_2606_;
goto v___jp_2509_;
}
}
else
{
lean_object* v_a_2607_; 
v_a_2607_ = lean_ctor_get(v___x_2601_, 0);
lean_inc(v_a_2607_);
lean_dec_ref(v___x_2601_);
v___y_2510_ = v___x_2590_;
v___y_2511_ = v_a_2587_;
v_a_2512_ = v_a_2607_;
goto v___jp_2509_;
}
}
else
{
lean_object* v___x_2609_; 
lean_dec(v_a_2599_);
if (v_isShared_2596_ == 0)
{
v___x_2609_ = v___x_2595_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v_reuseFailAlloc_2610_, 1, v_contextDependent_2593_);
v___x_2609_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
lean_ctor_set_uint8(v___x_2609_, 0, v_hasTrace_2485_);
v___y_2515_ = v___x_2590_;
v___y_2516_ = v_a_2587_;
v_a_2517_ = v___x_2609_;
goto v___jp_2514_;
}
}
}
else
{
lean_object* v_a_2611_; 
lean_del_object(v___x_2595_);
v_a_2611_ = lean_ctor_get(v___x_2598_, 0);
lean_inc(v_a_2611_);
lean_dec_ref(v___x_2598_);
v___y_2510_ = v___x_2590_;
v___y_2511_ = v_a_2587_;
v_a_2512_ = v_a_2611_;
goto v___jp_2509_;
}
}
}
else
{
lean_object* v_e_x27_2613_; lean_object* v_proof_2614_; uint8_t v_contextDependent_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2682_; 
v_e_x27_2613_ = lean_ctor_get(v_a_2592_, 0);
v_proof_2614_ = lean_ctor_get(v_a_2592_, 1);
v_contextDependent_2615_ = lean_ctor_get_uint8(v_a_2592_, sizeof(void*)*2 + 1);
v_isSharedCheck_2682_ = !lean_is_exclusive(v_a_2592_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2617_ = v_a_2592_;
v_isShared_2618_ = v_isSharedCheck_2682_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_proof_2614_);
lean_inc(v_e_x27_2613_);
lean_dec(v_a_2592_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2682_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2619_; 
lean_inc_ref(v_e_x27_2613_);
v___x_2619_ = l_Lean_Meta_Sym_inferType___redArg(v_e_x27_2613_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
if (lean_obj_tag(v___x_2619_) == 0)
{
lean_object* v_a_2620_; lean_object* v___x_2621_; uint8_t v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; 
v_a_2620_ = lean_ctor_get(v___x_2619_, 0);
lean_inc(v_a_2620_);
lean_dec_ref(v___x_2619_);
v___x_2621_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__1));
v___x_2622_ = 0;
v___x_2623_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2);
lean_inc(v_idx_2245_);
lean_inc(v_typeName_2244_);
v___x_2624_ = l_Lean_Expr_proj___override(v_typeName_2244_, v_idx_2245_, v___x_2623_);
v___x_2625_ = l_Lean_mkLambda(v___x_2621_, v___x_2622_, v_a_2620_, v___x_2624_);
lean_inc_ref(v___x_2625_);
v___x_2626_ = l_Lean_Meta_Sym_inferType___redArg(v___x_2625_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
if (lean_obj_tag(v___x_2626_) == 0)
{
lean_object* v_a_2627_; uint8_t v___x_2628_; 
v_a_2627_ = lean_ctor_get(v___x_2626_, 0);
lean_inc(v_a_2627_);
lean_dec_ref(v___x_2626_);
v___x_2628_ = l_Lean_Expr_isArrow(v_a_2627_);
if (v___x_2628_ == 0)
{
lean_object* v___x_2629_; lean_object* v___x_2630_; 
lean_dec(v_a_2627_);
lean_inc_ref(v_e_2219_);
v___x_2629_ = lean_alloc_closure((void*)(l_Lean_Meta_reduceProj_x3f___boxed), 6, 1);
lean_closure_set(v___x_2629_, 0, v_e_2219_);
v___x_2630_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___x_2629_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
if (lean_obj_tag(v___x_2630_) == 0)
{
lean_object* v_a_2631_; 
v_a_2631_ = lean_ctor_get(v___x_2630_, 0);
lean_inc(v_a_2631_);
lean_dec_ref(v___x_2630_);
if (lean_obj_tag(v_a_2631_) == 0)
{
lean_object* v___x_2632_; 
lean_del_object(v___x_2617_);
lean_inc_ref(v_e_x27_2613_);
lean_inc_ref(v_struct_2246_);
v___x_2632_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_struct_2246_, v_e_x27_2613_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
if (lean_obj_tag(v___x_2632_) == 0)
{
lean_object* v_a_2633_; uint8_t v___x_2634_; 
v_a_2633_ = lean_ctor_get(v___x_2632_, 0);
lean_inc(v_a_2633_);
lean_dec_ref(v___x_2632_);
v___x_2634_ = lean_unbox(v_a_2633_);
lean_dec(v_a_2633_);
if (v___x_2634_ == 0)
{
lean_object* v___x_2635_; 
lean_dec_ref(v___x_2625_);
lean_dec_ref(v_proof_2614_);
lean_dec_ref(v_e_x27_2613_);
lean_dec_ref(v_e_2219_);
v___x_2635_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2635_, 0, v_hasTrace_2485_);
lean_ctor_set_uint8(v___x_2635_, 1, v_contextDependent_2615_);
v___y_2515_ = v___x_2590_;
v___y_2516_ = v_a_2587_;
v_a_2517_ = v___x_2635_;
goto v___jp_2514_;
}
else
{
lean_object* v___x_2636_; 
v___x_2636_ = l_Lean_Meta_mkHCongr(v___x_2625_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
if (lean_obj_tag(v___x_2636_) == 0)
{
lean_object* v_a_2637_; lean_object* v_proof_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; 
v_a_2637_ = lean_ctor_get(v___x_2636_, 0);
lean_inc(v_a_2637_);
lean_dec_ref(v___x_2636_);
v_proof_2638_ = lean_ctor_get(v_a_2637_, 1);
lean_inc_ref(v_proof_2638_);
lean_dec(v_a_2637_);
lean_inc_ref(v_e_x27_2613_);
lean_inc_ref(v_struct_2246_);
v___x_2639_ = l_Lean_mkApp3(v_proof_2638_, v_struct_2246_, v_e_x27_2613_, v_proof_2614_);
v___x_2640_ = l_Lean_Meta_mkEqOfHEq(v___x_2639_, v___x_2589_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
if (lean_obj_tag(v___x_2640_) == 0)
{
lean_object* v_a_2641_; uint8_t v___x_2642_; 
v_a_2641_ = lean_ctor_get(v___x_2640_, 0);
lean_inc(v_a_2641_);
lean_dec_ref(v___x_2640_);
v___x_2642_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_2246_, v_e_x27_2613_);
if (v___x_2642_ == 0)
{
lean_object* v___x_2643_; 
lean_inc(v_idx_2245_);
lean_inc(v_typeName_2244_);
lean_dec_ref(v_e_2219_);
v___x_2643_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_typeName_2244_, v_idx_2245_, v_e_x27_2613_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
if (lean_obj_tag(v___x_2643_) == 0)
{
lean_object* v_a_2644_; 
v_a_2644_ = lean_ctor_get(v___x_2643_, 0);
lean_inc(v_a_2644_);
lean_dec_ref(v___x_2643_);
v___y_2526_ = v___x_2589_;
v___y_2527_ = v___x_2590_;
v___y_2528_ = v_a_2641_;
v___y_2529_ = v_contextDependent_2615_;
v___y_2530_ = v_a_2587_;
v_a_2531_ = v_a_2644_;
goto v___jp_2525_;
}
else
{
lean_object* v_a_2645_; 
lean_dec(v_a_2641_);
v_a_2645_ = lean_ctor_get(v___x_2643_, 0);
lean_inc(v_a_2645_);
lean_dec_ref(v___x_2643_);
v___y_2510_ = v___x_2590_;
v___y_2511_ = v_a_2587_;
v_a_2512_ = v_a_2645_;
goto v___jp_2509_;
}
}
else
{
lean_dec_ref(v_e_x27_2613_);
v___y_2526_ = v___x_2589_;
v___y_2527_ = v___x_2590_;
v___y_2528_ = v_a_2641_;
v___y_2529_ = v_contextDependent_2615_;
v___y_2530_ = v_a_2587_;
v_a_2531_ = v_e_2219_;
goto v___jp_2525_;
}
}
else
{
lean_object* v_a_2646_; 
lean_dec_ref(v_e_x27_2613_);
lean_dec_ref(v_e_2219_);
v_a_2646_ = lean_ctor_get(v___x_2640_, 0);
lean_inc(v_a_2646_);
lean_dec_ref(v___x_2640_);
v___y_2510_ = v___x_2590_;
v___y_2511_ = v_a_2587_;
v_a_2512_ = v_a_2646_;
goto v___jp_2509_;
}
}
else
{
lean_object* v_a_2647_; 
lean_dec_ref(v_proof_2614_);
lean_dec_ref(v_e_x27_2613_);
lean_dec_ref(v_e_2219_);
v_a_2647_ = lean_ctor_get(v___x_2636_, 0);
lean_inc(v_a_2647_);
lean_dec_ref(v___x_2636_);
v___y_2510_ = v___x_2590_;
v___y_2511_ = v_a_2587_;
v_a_2512_ = v_a_2647_;
goto v___jp_2509_;
}
}
}
else
{
lean_object* v_a_2648_; 
lean_dec_ref(v___x_2625_);
lean_dec_ref(v_proof_2614_);
lean_dec_ref(v_e_x27_2613_);
lean_dec_ref(v_e_2219_);
v_a_2648_ = lean_ctor_get(v___x_2632_, 0);
lean_inc(v_a_2648_);
lean_dec_ref(v___x_2632_);
v___y_2510_ = v___x_2590_;
v___y_2511_ = v_a_2587_;
v_a_2512_ = v_a_2648_;
goto v___jp_2509_;
}
}
else
{
lean_object* v_val_2649_; lean_object* v___x_2650_; 
lean_dec_ref(v___x_2625_);
lean_dec_ref(v_proof_2614_);
lean_dec_ref(v_e_x27_2613_);
lean_dec_ref(v_e_2219_);
v_val_2649_ = lean_ctor_get(v_a_2631_, 0);
lean_inc(v_val_2649_);
lean_dec_ref(v_a_2631_);
v___x_2650_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_val_2649_, v_a_2224_);
if (lean_obj_tag(v___x_2650_) == 0)
{
lean_object* v_a_2651_; lean_object* v___x_2652_; 
v_a_2651_ = lean_ctor_get(v___x_2650_, 0);
lean_inc_n(v_a_2651_, 2);
lean_dec_ref(v___x_2650_);
v___x_2652_ = l_Lean_Meta_Sym_mkEqRefl___redArg(v_a_2651_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
if (lean_obj_tag(v___x_2652_) == 0)
{
lean_object* v_a_2653_; lean_object* v___x_2655_; 
v_a_2653_ = lean_ctor_get(v___x_2652_, 0);
lean_inc(v_a_2653_);
lean_dec_ref(v___x_2652_);
if (v_isShared_2618_ == 0)
{
lean_ctor_set(v___x_2617_, 1, v_a_2653_);
lean_ctor_set(v___x_2617_, 0, v_a_2651_);
v___x_2655_ = v___x_2617_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v_a_2651_);
lean_ctor_set(v_reuseFailAlloc_2656_, 1, v_a_2653_);
v___x_2655_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
lean_ctor_set_uint8(v___x_2655_, sizeof(void*)*2, v_contextDependent_2615_);
lean_ctor_set_uint8(v___x_2655_, sizeof(void*)*2 + 1, v___x_2589_);
v___y_2515_ = v___x_2590_;
v___y_2516_ = v_a_2587_;
v_a_2517_ = v___x_2655_;
goto v___jp_2514_;
}
}
else
{
lean_object* v_a_2657_; 
lean_dec(v_a_2651_);
lean_del_object(v___x_2617_);
v_a_2657_ = lean_ctor_get(v___x_2652_, 0);
lean_inc(v_a_2657_);
lean_dec_ref(v___x_2652_);
v___y_2510_ = v___x_2590_;
v___y_2511_ = v_a_2587_;
v_a_2512_ = v_a_2657_;
goto v___jp_2509_;
}
}
else
{
lean_object* v_a_2658_; 
lean_del_object(v___x_2617_);
v_a_2658_ = lean_ctor_get(v___x_2650_, 0);
lean_inc(v_a_2658_);
lean_dec_ref(v___x_2650_);
v___y_2510_ = v___x_2590_;
v___y_2511_ = v_a_2587_;
v_a_2512_ = v_a_2658_;
goto v___jp_2509_;
}
}
}
else
{
lean_object* v_a_2659_; 
lean_dec_ref(v___x_2625_);
lean_del_object(v___x_2617_);
lean_dec_ref(v_proof_2614_);
lean_dec_ref(v_e_x27_2613_);
lean_dec_ref(v_e_2219_);
v_a_2659_ = lean_ctor_get(v___x_2630_, 0);
lean_inc(v_a_2659_);
lean_dec_ref(v___x_2630_);
v___y_2510_ = v___x_2590_;
v___y_2511_ = v_a_2587_;
v_a_2512_ = v_a_2659_;
goto v___jp_2509_;
}
}
else
{
lean_del_object(v___x_2617_);
if (lean_obj_tag(v_a_2627_) == 7)
{
lean_object* v_binderType_2660_; lean_object* v_body_2661_; lean_object* v___x_2662_; 
v_binderType_2660_ = lean_ctor_get(v_a_2627_, 1);
lean_inc_ref_n(v_binderType_2660_, 2);
v_body_2661_ = lean_ctor_get(v_a_2627_, 2);
lean_inc_ref(v_body_2661_);
lean_dec_ref(v_a_2627_);
v___x_2662_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_2660_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
if (lean_obj_tag(v___x_2662_) == 0)
{
lean_object* v_a_2663_; lean_object* v___x_2664_; 
v_a_2663_ = lean_ctor_get(v___x_2662_, 0);
lean_inc(v_a_2663_);
lean_dec_ref(v___x_2662_);
lean_inc_ref(v_body_2661_);
v___x_2664_ = l_Lean_Meta_Sym_getLevel___redArg(v_body_2661_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
if (lean_obj_tag(v___x_2664_) == 0)
{
lean_object* v_a_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; uint8_t v___x_2672_; 
v_a_2665_ = lean_ctor_get(v___x_2664_, 0);
lean_inc(v_a_2665_);
lean_dec_ref(v___x_2664_);
v___x_2666_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4));
v___x_2667_ = lean_box(0);
v___x_2668_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2668_, 0, v_a_2665_);
lean_ctor_set(v___x_2668_, 1, v___x_2667_);
v___x_2669_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2669_, 0, v_a_2663_);
lean_ctor_set(v___x_2669_, 1, v___x_2668_);
v___x_2670_ = l_Lean_mkConst(v___x_2666_, v___x_2669_);
lean_inc_ref(v_e_x27_2613_);
lean_inc_ref(v_struct_2246_);
v___x_2671_ = l_Lean_mkApp6(v___x_2670_, v_binderType_2660_, v_body_2661_, v_struct_2246_, v_e_x27_2613_, v___x_2625_, v_proof_2614_);
v___x_2672_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_2246_, v_e_x27_2613_);
if (v___x_2672_ == 0)
{
lean_object* v___x_2673_; 
lean_inc(v_idx_2245_);
lean_inc(v_typeName_2244_);
lean_dec_ref(v_e_2219_);
v___x_2673_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_typeName_2244_, v_idx_2245_, v_e_x27_2613_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
if (lean_obj_tag(v___x_2673_) == 0)
{
lean_object* v_a_2674_; 
v_a_2674_ = lean_ctor_get(v___x_2673_, 0);
lean_inc(v_a_2674_);
lean_dec_ref(v___x_2673_);
v___y_2534_ = v___x_2589_;
v___y_2535_ = v___x_2590_;
v___y_2536_ = v_contextDependent_2615_;
v___y_2537_ = v_a_2587_;
v___y_2538_ = v___x_2671_;
v_a_2539_ = v_a_2674_;
goto v___jp_2533_;
}
else
{
lean_object* v_a_2675_; 
lean_dec_ref(v___x_2671_);
v_a_2675_ = lean_ctor_get(v___x_2673_, 0);
lean_inc(v_a_2675_);
lean_dec_ref(v___x_2673_);
v___y_2510_ = v___x_2590_;
v___y_2511_ = v_a_2587_;
v_a_2512_ = v_a_2675_;
goto v___jp_2509_;
}
}
else
{
lean_dec_ref(v_e_x27_2613_);
v___y_2534_ = v___x_2589_;
v___y_2535_ = v___x_2590_;
v___y_2536_ = v_contextDependent_2615_;
v___y_2537_ = v_a_2587_;
v___y_2538_ = v___x_2671_;
v_a_2539_ = v_e_2219_;
goto v___jp_2533_;
}
}
else
{
lean_object* v_a_2676_; 
lean_dec(v_a_2663_);
lean_dec_ref(v_body_2661_);
lean_dec_ref(v_binderType_2660_);
lean_dec_ref(v___x_2625_);
lean_dec_ref(v_proof_2614_);
lean_dec_ref(v_e_x27_2613_);
lean_dec_ref(v_e_2219_);
v_a_2676_ = lean_ctor_get(v___x_2664_, 0);
lean_inc(v_a_2676_);
lean_dec_ref(v___x_2664_);
v___y_2510_ = v___x_2590_;
v___y_2511_ = v_a_2587_;
v_a_2512_ = v_a_2676_;
goto v___jp_2509_;
}
}
else
{
lean_object* v_a_2677_; 
lean_dec_ref(v_body_2661_);
lean_dec_ref(v_binderType_2660_);
lean_dec_ref(v___x_2625_);
lean_dec_ref(v_proof_2614_);
lean_dec_ref(v_e_x27_2613_);
lean_dec_ref(v_e_2219_);
v_a_2677_ = lean_ctor_get(v___x_2662_, 0);
lean_inc(v_a_2677_);
lean_dec_ref(v___x_2662_);
v___y_2510_ = v___x_2590_;
v___y_2511_ = v_a_2587_;
v_a_2512_ = v_a_2677_;
goto v___jp_2509_;
}
}
else
{
lean_object* v___x_2678_; lean_object* v___x_2679_; 
lean_dec(v_a_2627_);
lean_dec_ref(v___x_2625_);
lean_dec_ref(v_proof_2614_);
lean_dec_ref(v_e_x27_2613_);
lean_dec_ref(v_e_2219_);
v___x_2678_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8);
v___x_2679_ = l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1(v___x_2678_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
v___y_2520_ = v___x_2590_;
v___y_2521_ = v_a_2587_;
v___y_2522_ = v___x_2679_;
goto v___jp_2519_;
}
}
}
else
{
lean_object* v_a_2680_; 
lean_dec_ref(v___x_2625_);
lean_del_object(v___x_2617_);
lean_dec_ref(v_proof_2614_);
lean_dec_ref(v_e_x27_2613_);
lean_dec_ref(v_e_2219_);
v_a_2680_ = lean_ctor_get(v___x_2626_, 0);
lean_inc(v_a_2680_);
lean_dec_ref(v___x_2626_);
v___y_2510_ = v___x_2590_;
v___y_2511_ = v_a_2587_;
v_a_2512_ = v_a_2680_;
goto v___jp_2509_;
}
}
else
{
lean_object* v_a_2681_; 
lean_del_object(v___x_2617_);
lean_dec_ref(v_proof_2614_);
lean_dec_ref(v_e_x27_2613_);
lean_dec_ref(v_e_2219_);
v_a_2681_ = lean_ctor_get(v___x_2619_, 0);
lean_inc(v_a_2681_);
lean_dec_ref(v___x_2619_);
v___y_2510_ = v___x_2590_;
v___y_2511_ = v_a_2587_;
v_a_2512_ = v_a_2681_;
goto v___jp_2509_;
}
}
}
}
else
{
lean_dec_ref(v_e_2219_);
v___y_2520_ = v___x_2590_;
v___y_2521_ = v_a_2587_;
v___y_2522_ = v___x_2591_;
goto v___jp_2519_;
}
}
else
{
lean_object* v___x_2683_; lean_object* v___x_2684_; 
v___x_2683_ = lean_io_get_num_heartbeats();
lean_inc(v_a_2228_);
lean_inc_ref(v_a_2227_);
lean_inc(v_a_2226_);
lean_inc_ref(v_a_2225_);
lean_inc(v_a_2224_);
lean_inc_ref(v_a_2223_);
lean_inc(v_a_2222_);
lean_inc_ref(v_a_2221_);
lean_inc(v_a_2220_);
lean_inc_ref(v_struct_2246_);
v___x_2684_ = lean_sym_simp(v_struct_2246_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
if (lean_obj_tag(v___x_2684_) == 0)
{
lean_object* v_a_2685_; 
v_a_2685_ = lean_ctor_get(v___x_2684_, 0);
lean_inc(v_a_2685_);
lean_dec_ref(v___x_2684_);
if (lean_obj_tag(v_a_2685_) == 0)
{
uint8_t v_contextDependent_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2706_; 
v_contextDependent_2686_ = lean_ctor_get_uint8(v_a_2685_, 1);
v_isSharedCheck_2706_ = !lean_is_exclusive(v_a_2685_);
if (v_isSharedCheck_2706_ == 0)
{
v___x_2688_ = v_a_2685_;
v_isShared_2689_ = v_isSharedCheck_2706_;
goto v_resetjp_2687_;
}
else
{
lean_dec(v_a_2685_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2706_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2690_; lean_object* v___x_2691_; 
v___x_2690_ = lean_alloc_closure((void*)(l_Lean_Meta_reduceProj_x3f___boxed), 6, 1);
lean_closure_set(v___x_2690_, 0, v_e_2219_);
v___x_2691_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___x_2690_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
if (lean_obj_tag(v___x_2691_) == 0)
{
lean_object* v_a_2692_; 
v_a_2692_ = lean_ctor_get(v___x_2691_, 0);
lean_inc(v_a_2692_);
lean_dec_ref(v___x_2691_);
if (lean_obj_tag(v_a_2692_) == 1)
{
lean_object* v_val_2693_; lean_object* v___x_2694_; 
lean_del_object(v___x_2688_);
v_val_2693_ = lean_ctor_get(v_a_2692_, 0);
lean_inc(v_val_2693_);
lean_dec_ref(v_a_2692_);
v___x_2694_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_val_2693_, v_a_2224_);
if (lean_obj_tag(v___x_2694_) == 0)
{
lean_object* v_a_2695_; lean_object* v___x_2696_; 
v_a_2695_ = lean_ctor_get(v___x_2694_, 0);
lean_inc_n(v_a_2695_, 2);
lean_dec_ref(v___x_2694_);
v___x_2696_ = l_Lean_Meta_Sym_mkEqRefl___redArg(v_a_2695_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
if (lean_obj_tag(v___x_2696_) == 0)
{
lean_object* v_a_2697_; uint8_t v___x_2698_; lean_object* v___x_2699_; 
v_a_2697_ = lean_ctor_get(v___x_2696_, 0);
lean_inc(v_a_2697_);
lean_dec_ref(v___x_2696_);
v___x_2698_ = 0;
v___x_2699_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2699_, 0, v_a_2695_);
lean_ctor_set(v___x_2699_, 1, v_a_2697_);
lean_ctor_set_uint8(v___x_2699_, sizeof(void*)*2, v_contextDependent_2686_);
lean_ctor_set_uint8(v___x_2699_, sizeof(void*)*2 + 1, v___x_2698_);
v___y_2559_ = v___x_2683_;
v___y_2560_ = v_a_2587_;
v_a_2561_ = v___x_2699_;
goto v___jp_2558_;
}
else
{
lean_object* v_a_2700_; 
lean_dec(v_a_2695_);
v_a_2700_ = lean_ctor_get(v___x_2696_, 0);
lean_inc(v_a_2700_);
lean_dec_ref(v___x_2696_);
v___y_2554_ = v___x_2683_;
v___y_2555_ = v_a_2587_;
v_a_2556_ = v_a_2700_;
goto v___jp_2553_;
}
}
else
{
lean_object* v_a_2701_; 
v_a_2701_ = lean_ctor_get(v___x_2694_, 0);
lean_inc(v_a_2701_);
lean_dec_ref(v___x_2694_);
v___y_2554_ = v___x_2683_;
v___y_2555_ = v_a_2587_;
v_a_2556_ = v_a_2701_;
goto v___jp_2553_;
}
}
else
{
lean_object* v___x_2703_; 
lean_dec(v_a_2692_);
if (v_isShared_2689_ == 0)
{
v___x_2703_ = v___x_2688_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v_reuseFailAlloc_2704_, 1, v_contextDependent_2686_);
v___x_2703_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
lean_ctor_set_uint8(v___x_2703_, 0, v___x_2589_);
v___y_2559_ = v___x_2683_;
v___y_2560_ = v_a_2587_;
v_a_2561_ = v___x_2703_;
goto v___jp_2558_;
}
}
}
else
{
lean_object* v_a_2705_; 
lean_del_object(v___x_2688_);
v_a_2705_ = lean_ctor_get(v___x_2691_, 0);
lean_inc(v_a_2705_);
lean_dec_ref(v___x_2691_);
v___y_2554_ = v___x_2683_;
v___y_2555_ = v_a_2587_;
v_a_2556_ = v_a_2705_;
goto v___jp_2553_;
}
}
}
else
{
lean_object* v_e_x27_2707_; lean_object* v_proof_2708_; uint8_t v_contextDependent_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2776_; 
v_e_x27_2707_ = lean_ctor_get(v_a_2685_, 0);
v_proof_2708_ = lean_ctor_get(v_a_2685_, 1);
v_contextDependent_2709_ = lean_ctor_get_uint8(v_a_2685_, sizeof(void*)*2 + 1);
v_isSharedCheck_2776_ = !lean_is_exclusive(v_a_2685_);
if (v_isSharedCheck_2776_ == 0)
{
v___x_2711_ = v_a_2685_;
v_isShared_2712_ = v_isSharedCheck_2776_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_proof_2708_);
lean_inc(v_e_x27_2707_);
lean_dec(v_a_2685_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2776_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2713_; 
lean_inc_ref(v_e_x27_2707_);
v___x_2713_ = l_Lean_Meta_Sym_inferType___redArg(v_e_x27_2707_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
if (lean_obj_tag(v___x_2713_) == 0)
{
lean_object* v_a_2714_; lean_object* v___x_2715_; uint8_t v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; 
v_a_2714_ = lean_ctor_get(v___x_2713_, 0);
lean_inc(v_a_2714_);
lean_dec_ref(v___x_2713_);
v___x_2715_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__1));
v___x_2716_ = 0;
v___x_2717_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2);
lean_inc(v_idx_2245_);
lean_inc(v_typeName_2244_);
v___x_2718_ = l_Lean_Expr_proj___override(v_typeName_2244_, v_idx_2245_, v___x_2717_);
v___x_2719_ = l_Lean_mkLambda(v___x_2715_, v___x_2716_, v_a_2714_, v___x_2718_);
lean_inc_ref(v___x_2719_);
v___x_2720_ = l_Lean_Meta_Sym_inferType___redArg(v___x_2719_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
if (lean_obj_tag(v___x_2720_) == 0)
{
lean_object* v_a_2721_; uint8_t v___x_2722_; 
v_a_2721_ = lean_ctor_get(v___x_2720_, 0);
lean_inc(v_a_2721_);
lean_dec_ref(v___x_2720_);
v___x_2722_ = l_Lean_Expr_isArrow(v_a_2721_);
if (v___x_2722_ == 0)
{
lean_object* v___x_2723_; lean_object* v___x_2724_; 
lean_dec(v_a_2721_);
lean_inc_ref(v_e_2219_);
v___x_2723_ = lean_alloc_closure((void*)(l_Lean_Meta_reduceProj_x3f___boxed), 6, 1);
lean_closure_set(v___x_2723_, 0, v_e_2219_);
v___x_2724_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___x_2723_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
if (lean_obj_tag(v___x_2724_) == 0)
{
lean_object* v_a_2725_; 
v_a_2725_ = lean_ctor_get(v___x_2724_, 0);
lean_inc(v_a_2725_);
lean_dec_ref(v___x_2724_);
if (lean_obj_tag(v_a_2725_) == 0)
{
lean_object* v___x_2726_; 
lean_del_object(v___x_2711_);
lean_inc_ref(v_e_x27_2707_);
lean_inc_ref(v_struct_2246_);
v___x_2726_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_struct_2246_, v_e_x27_2707_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
if (lean_obj_tag(v___x_2726_) == 0)
{
lean_object* v_a_2727_; uint8_t v___x_2728_; 
v_a_2727_ = lean_ctor_get(v___x_2726_, 0);
lean_inc(v_a_2727_);
lean_dec_ref(v___x_2726_);
v___x_2728_ = lean_unbox(v_a_2727_);
lean_dec(v_a_2727_);
if (v___x_2728_ == 0)
{
lean_object* v___x_2729_; 
lean_dec_ref(v___x_2719_);
lean_dec_ref(v_proof_2708_);
lean_dec_ref(v_e_x27_2707_);
lean_dec_ref(v_e_2219_);
v___x_2729_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2729_, 0, v___x_2589_);
lean_ctor_set_uint8(v___x_2729_, 1, v_contextDependent_2709_);
v___y_2559_ = v___x_2683_;
v___y_2560_ = v_a_2587_;
v_a_2561_ = v___x_2729_;
goto v___jp_2558_;
}
else
{
lean_object* v___x_2730_; 
v___x_2730_ = l_Lean_Meta_mkHCongr(v___x_2719_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
if (lean_obj_tag(v___x_2730_) == 0)
{
lean_object* v_a_2731_; lean_object* v_proof_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; 
v_a_2731_ = lean_ctor_get(v___x_2730_, 0);
lean_inc(v_a_2731_);
lean_dec_ref(v___x_2730_);
v_proof_2732_ = lean_ctor_get(v_a_2731_, 1);
lean_inc_ref(v_proof_2732_);
lean_dec(v_a_2731_);
lean_inc_ref(v_e_x27_2707_);
lean_inc_ref(v_struct_2246_);
v___x_2733_ = l_Lean_mkApp3(v_proof_2732_, v_struct_2246_, v_e_x27_2707_, v_proof_2708_);
v___x_2734_ = l_Lean_Meta_mkEqOfHEq(v___x_2733_, v___x_2722_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
if (lean_obj_tag(v___x_2734_) == 0)
{
lean_object* v_a_2735_; uint8_t v___x_2736_; 
v_a_2735_ = lean_ctor_get(v___x_2734_, 0);
lean_inc(v_a_2735_);
lean_dec_ref(v___x_2734_);
v___x_2736_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_2246_, v_e_x27_2707_);
if (v___x_2736_ == 0)
{
lean_object* v___x_2737_; 
lean_inc(v_idx_2245_);
lean_inc(v_typeName_2244_);
lean_dec_ref(v_e_2219_);
v___x_2737_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_typeName_2244_, v_idx_2245_, v_e_x27_2707_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
if (lean_obj_tag(v___x_2737_) == 0)
{
lean_object* v_a_2738_; 
v_a_2738_ = lean_ctor_get(v___x_2737_, 0);
lean_inc(v_a_2738_);
lean_dec_ref(v___x_2737_);
v___y_2570_ = v_contextDependent_2709_;
v___y_2571_ = v___x_2722_;
v___y_2572_ = v_a_2735_;
v___y_2573_ = v_a_2587_;
v___y_2574_ = v___x_2683_;
v_a_2575_ = v_a_2738_;
goto v___jp_2569_;
}
else
{
lean_object* v_a_2739_; 
lean_dec(v_a_2735_);
v_a_2739_ = lean_ctor_get(v___x_2737_, 0);
lean_inc(v_a_2739_);
lean_dec_ref(v___x_2737_);
v___y_2554_ = v___x_2683_;
v___y_2555_ = v_a_2587_;
v_a_2556_ = v_a_2739_;
goto v___jp_2553_;
}
}
else
{
lean_dec_ref(v_e_x27_2707_);
v___y_2570_ = v_contextDependent_2709_;
v___y_2571_ = v___x_2722_;
v___y_2572_ = v_a_2735_;
v___y_2573_ = v_a_2587_;
v___y_2574_ = v___x_2683_;
v_a_2575_ = v_e_2219_;
goto v___jp_2569_;
}
}
else
{
lean_object* v_a_2740_; 
lean_dec_ref(v_e_x27_2707_);
lean_dec_ref(v_e_2219_);
v_a_2740_ = lean_ctor_get(v___x_2734_, 0);
lean_inc(v_a_2740_);
lean_dec_ref(v___x_2734_);
v___y_2554_ = v___x_2683_;
v___y_2555_ = v_a_2587_;
v_a_2556_ = v_a_2740_;
goto v___jp_2553_;
}
}
else
{
lean_object* v_a_2741_; 
lean_dec_ref(v_proof_2708_);
lean_dec_ref(v_e_x27_2707_);
lean_dec_ref(v_e_2219_);
v_a_2741_ = lean_ctor_get(v___x_2730_, 0);
lean_inc(v_a_2741_);
lean_dec_ref(v___x_2730_);
v___y_2554_ = v___x_2683_;
v___y_2555_ = v_a_2587_;
v_a_2556_ = v_a_2741_;
goto v___jp_2553_;
}
}
}
else
{
lean_object* v_a_2742_; 
lean_dec_ref(v___x_2719_);
lean_dec_ref(v_proof_2708_);
lean_dec_ref(v_e_x27_2707_);
lean_dec_ref(v_e_2219_);
v_a_2742_ = lean_ctor_get(v___x_2726_, 0);
lean_inc(v_a_2742_);
lean_dec_ref(v___x_2726_);
v___y_2554_ = v___x_2683_;
v___y_2555_ = v_a_2587_;
v_a_2556_ = v_a_2742_;
goto v___jp_2553_;
}
}
else
{
lean_object* v_val_2743_; lean_object* v___x_2744_; 
lean_dec_ref(v___x_2719_);
lean_dec_ref(v_proof_2708_);
lean_dec_ref(v_e_x27_2707_);
lean_dec_ref(v_e_2219_);
v_val_2743_ = lean_ctor_get(v_a_2725_, 0);
lean_inc(v_val_2743_);
lean_dec_ref(v_a_2725_);
v___x_2744_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_val_2743_, v_a_2224_);
if (lean_obj_tag(v___x_2744_) == 0)
{
lean_object* v_a_2745_; lean_object* v___x_2746_; 
v_a_2745_ = lean_ctor_get(v___x_2744_, 0);
lean_inc_n(v_a_2745_, 2);
lean_dec_ref(v___x_2744_);
v___x_2746_ = l_Lean_Meta_Sym_mkEqRefl___redArg(v_a_2745_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
if (lean_obj_tag(v___x_2746_) == 0)
{
lean_object* v_a_2747_; lean_object* v___x_2749_; 
v_a_2747_ = lean_ctor_get(v___x_2746_, 0);
lean_inc(v_a_2747_);
lean_dec_ref(v___x_2746_);
if (v_isShared_2712_ == 0)
{
lean_ctor_set(v___x_2711_, 1, v_a_2747_);
lean_ctor_set(v___x_2711_, 0, v_a_2745_);
v___x_2749_ = v___x_2711_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_a_2745_);
lean_ctor_set(v_reuseFailAlloc_2750_, 1, v_a_2747_);
v___x_2749_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
lean_ctor_set_uint8(v___x_2749_, sizeof(void*)*2, v_contextDependent_2709_);
lean_ctor_set_uint8(v___x_2749_, sizeof(void*)*2 + 1, v___x_2722_);
v___y_2559_ = v___x_2683_;
v___y_2560_ = v_a_2587_;
v_a_2561_ = v___x_2749_;
goto v___jp_2558_;
}
}
else
{
lean_object* v_a_2751_; 
lean_dec(v_a_2745_);
lean_del_object(v___x_2711_);
v_a_2751_ = lean_ctor_get(v___x_2746_, 0);
lean_inc(v_a_2751_);
lean_dec_ref(v___x_2746_);
v___y_2554_ = v___x_2683_;
v___y_2555_ = v_a_2587_;
v_a_2556_ = v_a_2751_;
goto v___jp_2553_;
}
}
else
{
lean_object* v_a_2752_; 
lean_del_object(v___x_2711_);
v_a_2752_ = lean_ctor_get(v___x_2744_, 0);
lean_inc(v_a_2752_);
lean_dec_ref(v___x_2744_);
v___y_2554_ = v___x_2683_;
v___y_2555_ = v_a_2587_;
v_a_2556_ = v_a_2752_;
goto v___jp_2553_;
}
}
}
else
{
lean_object* v_a_2753_; 
lean_dec_ref(v___x_2719_);
lean_del_object(v___x_2711_);
lean_dec_ref(v_proof_2708_);
lean_dec_ref(v_e_x27_2707_);
lean_dec_ref(v_e_2219_);
v_a_2753_ = lean_ctor_get(v___x_2724_, 0);
lean_inc(v_a_2753_);
lean_dec_ref(v___x_2724_);
v___y_2554_ = v___x_2683_;
v___y_2555_ = v_a_2587_;
v_a_2556_ = v_a_2753_;
goto v___jp_2553_;
}
}
else
{
lean_del_object(v___x_2711_);
if (lean_obj_tag(v_a_2721_) == 7)
{
lean_object* v_binderType_2754_; lean_object* v_body_2755_; lean_object* v___x_2756_; 
v_binderType_2754_ = lean_ctor_get(v_a_2721_, 1);
lean_inc_ref_n(v_binderType_2754_, 2);
v_body_2755_ = lean_ctor_get(v_a_2721_, 2);
lean_inc_ref(v_body_2755_);
lean_dec_ref(v_a_2721_);
v___x_2756_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_2754_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
if (lean_obj_tag(v___x_2756_) == 0)
{
lean_object* v_a_2757_; lean_object* v___x_2758_; 
v_a_2757_ = lean_ctor_get(v___x_2756_, 0);
lean_inc(v_a_2757_);
lean_dec_ref(v___x_2756_);
lean_inc_ref(v_body_2755_);
v___x_2758_ = l_Lean_Meta_Sym_getLevel___redArg(v_body_2755_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
if (lean_obj_tag(v___x_2758_) == 0)
{
lean_object* v_a_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; uint8_t v___x_2766_; 
v_a_2759_ = lean_ctor_get(v___x_2758_, 0);
lean_inc(v_a_2759_);
lean_dec_ref(v___x_2758_);
v___x_2760_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4));
v___x_2761_ = lean_box(0);
v___x_2762_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2762_, 0, v_a_2759_);
lean_ctor_set(v___x_2762_, 1, v___x_2761_);
v___x_2763_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2763_, 0, v_a_2757_);
lean_ctor_set(v___x_2763_, 1, v___x_2762_);
v___x_2764_ = l_Lean_mkConst(v___x_2760_, v___x_2763_);
lean_inc_ref(v_e_x27_2707_);
lean_inc_ref(v_struct_2246_);
v___x_2765_ = l_Lean_mkApp6(v___x_2764_, v_binderType_2754_, v_body_2755_, v_struct_2246_, v_e_x27_2707_, v___x_2719_, v_proof_2708_);
v___x_2766_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_2246_, v_e_x27_2707_);
if (v___x_2766_ == 0)
{
lean_object* v___x_2767_; 
lean_inc(v_idx_2245_);
lean_inc(v_typeName_2244_);
lean_dec_ref(v_e_2219_);
v___x_2767_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_typeName_2244_, v_idx_2245_, v_e_x27_2707_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
if (lean_obj_tag(v___x_2767_) == 0)
{
lean_object* v_a_2768_; 
v_a_2768_ = lean_ctor_get(v___x_2767_, 0);
lean_inc(v_a_2768_);
lean_dec_ref(v___x_2767_);
v___y_2578_ = v_contextDependent_2709_;
v___y_2579_ = v___x_2765_;
v___y_2580_ = v_a_2587_;
v___y_2581_ = v___x_2683_;
v_a_2582_ = v_a_2768_;
goto v___jp_2577_;
}
else
{
lean_object* v_a_2769_; 
lean_dec_ref(v___x_2765_);
v_a_2769_ = lean_ctor_get(v___x_2767_, 0);
lean_inc(v_a_2769_);
lean_dec_ref(v___x_2767_);
v___y_2554_ = v___x_2683_;
v___y_2555_ = v_a_2587_;
v_a_2556_ = v_a_2769_;
goto v___jp_2553_;
}
}
else
{
lean_dec_ref(v_e_x27_2707_);
v___y_2578_ = v_contextDependent_2709_;
v___y_2579_ = v___x_2765_;
v___y_2580_ = v_a_2587_;
v___y_2581_ = v___x_2683_;
v_a_2582_ = v_e_2219_;
goto v___jp_2577_;
}
}
else
{
lean_object* v_a_2770_; 
lean_dec(v_a_2757_);
lean_dec_ref(v_body_2755_);
lean_dec_ref(v_binderType_2754_);
lean_dec_ref(v___x_2719_);
lean_dec_ref(v_proof_2708_);
lean_dec_ref(v_e_x27_2707_);
lean_dec_ref(v_e_2219_);
v_a_2770_ = lean_ctor_get(v___x_2758_, 0);
lean_inc(v_a_2770_);
lean_dec_ref(v___x_2758_);
v___y_2554_ = v___x_2683_;
v___y_2555_ = v_a_2587_;
v_a_2556_ = v_a_2770_;
goto v___jp_2553_;
}
}
else
{
lean_object* v_a_2771_; 
lean_dec_ref(v_body_2755_);
lean_dec_ref(v_binderType_2754_);
lean_dec_ref(v___x_2719_);
lean_dec_ref(v_proof_2708_);
lean_dec_ref(v_e_x27_2707_);
lean_dec_ref(v_e_2219_);
v_a_2771_ = lean_ctor_get(v___x_2756_, 0);
lean_inc(v_a_2771_);
lean_dec_ref(v___x_2756_);
v___y_2554_ = v___x_2683_;
v___y_2555_ = v_a_2587_;
v_a_2556_ = v_a_2771_;
goto v___jp_2553_;
}
}
else
{
lean_object* v___x_2772_; lean_object* v___x_2773_; 
lean_dec(v_a_2721_);
lean_dec_ref(v___x_2719_);
lean_dec_ref(v_proof_2708_);
lean_dec_ref(v_e_x27_2707_);
lean_dec_ref(v_e_2219_);
v___x_2772_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8);
v___x_2773_ = l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1(v___x_2772_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
v___y_2564_ = v_a_2587_;
v___y_2565_ = v___x_2683_;
v___y_2566_ = v___x_2773_;
goto v___jp_2563_;
}
}
}
else
{
lean_object* v_a_2774_; 
lean_dec_ref(v___x_2719_);
lean_del_object(v___x_2711_);
lean_dec_ref(v_proof_2708_);
lean_dec_ref(v_e_x27_2707_);
lean_dec_ref(v_e_2219_);
v_a_2774_ = lean_ctor_get(v___x_2720_, 0);
lean_inc(v_a_2774_);
lean_dec_ref(v___x_2720_);
v___y_2554_ = v___x_2683_;
v___y_2555_ = v_a_2587_;
v_a_2556_ = v_a_2774_;
goto v___jp_2553_;
}
}
else
{
lean_object* v_a_2775_; 
lean_del_object(v___x_2711_);
lean_dec_ref(v_proof_2708_);
lean_dec_ref(v_e_x27_2707_);
lean_dec_ref(v_e_2219_);
v_a_2775_ = lean_ctor_get(v___x_2713_, 0);
lean_inc(v_a_2775_);
lean_dec_ref(v___x_2713_);
v___y_2554_ = v___x_2683_;
v___y_2555_ = v_a_2587_;
v_a_2556_ = v_a_2775_;
goto v___jp_2553_;
}
}
}
}
else
{
lean_dec_ref(v_e_2219_);
v___y_2564_ = v_a_2587_;
v___y_2565_ = v___x_2683_;
v___y_2566_ = v___x_2684_;
goto v___jp_2563_;
}
}
}
}
v___jp_2247_:
{
if (lean_obj_tag(v_res_2248_) == 0)
{
uint8_t v_contextDependent_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2314_; 
v_contextDependent_2258_ = lean_ctor_get_uint8(v_res_2248_, 1);
v_isSharedCheck_2314_ = !lean_is_exclusive(v_res_2248_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2260_ = v_res_2248_;
v_isShared_2261_ = v_isSharedCheck_2314_;
goto v_resetjp_2259_;
}
else
{
lean_dec(v_res_2248_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2314_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
lean_object* v___x_2262_; lean_object* v___x_2263_; 
v___x_2262_ = lean_alloc_closure((void*)(l_Lean_Meta_reduceProj_x3f___boxed), 6, 1);
lean_closure_set(v___x_2262_, 0, v_e_2219_);
v___x_2263_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___x_2262_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
if (lean_obj_tag(v___x_2263_) == 0)
{
lean_object* v_a_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2305_; 
v_a_2264_ = lean_ctor_get(v___x_2263_, 0);
v_isSharedCheck_2305_ = !lean_is_exclusive(v___x_2263_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2266_ = v___x_2263_;
v_isShared_2267_ = v_isSharedCheck_2305_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_a_2264_);
lean_dec(v___x_2263_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2305_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
if (lean_obj_tag(v_a_2264_) == 1)
{
lean_object* v_val_2268_; lean_object* v___x_2269_; 
lean_del_object(v___x_2266_);
lean_del_object(v___x_2260_);
v_val_2268_ = lean_ctor_get(v_a_2264_, 0);
lean_inc(v_val_2268_);
lean_dec_ref(v_a_2264_);
v___x_2269_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_val_2268_, v___y_2253_);
if (lean_obj_tag(v___x_2269_) == 0)
{
lean_object* v_a_2270_; lean_object* v___x_2271_; 
v_a_2270_ = lean_ctor_get(v___x_2269_, 0);
lean_inc_n(v_a_2270_, 2);
lean_dec_ref(v___x_2269_);
v___x_2271_ = l_Lean_Meta_Sym_mkEqRefl___redArg(v_a_2270_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
if (lean_obj_tag(v___x_2271_) == 0)
{
lean_object* v_a_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2281_; 
v_a_2272_ = lean_ctor_get(v___x_2271_, 0);
v_isSharedCheck_2281_ = !lean_is_exclusive(v___x_2271_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2274_ = v___x_2271_;
v_isShared_2275_ = v_isSharedCheck_2281_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_a_2272_);
lean_dec(v___x_2271_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2281_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
uint8_t v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2279_; 
v___x_2276_ = 0;
v___x_2277_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2277_, 0, v_a_2270_);
lean_ctor_set(v___x_2277_, 1, v_a_2272_);
lean_ctor_set_uint8(v___x_2277_, sizeof(void*)*2, v_contextDependent_2258_);
lean_ctor_set_uint8(v___x_2277_, sizeof(void*)*2 + 1, v___x_2276_);
if (v_isShared_2275_ == 0)
{
lean_ctor_set(v___x_2274_, 0, v___x_2277_);
v___x_2279_ = v___x_2274_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v___x_2277_);
v___x_2279_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
return v___x_2279_;
}
}
}
else
{
lean_object* v_a_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2289_; 
lean_dec(v_a_2270_);
v_a_2282_ = lean_ctor_get(v___x_2271_, 0);
v_isSharedCheck_2289_ = !lean_is_exclusive(v___x_2271_);
if (v_isSharedCheck_2289_ == 0)
{
v___x_2284_ = v___x_2271_;
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_a_2282_);
lean_dec(v___x_2271_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v___x_2287_; 
if (v_isShared_2285_ == 0)
{
v___x_2287_ = v___x_2284_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v_a_2282_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
}
}
else
{
lean_object* v_a_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2297_; 
v_a_2290_ = lean_ctor_get(v___x_2269_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2292_ = v___x_2269_;
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_a_2290_);
lean_dec(v___x_2269_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v___x_2295_; 
if (v_isShared_2293_ == 0)
{
v___x_2295_ = v___x_2292_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_a_2290_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
return v___x_2295_;
}
}
}
}
else
{
uint8_t v___x_2298_; lean_object* v___x_2300_; 
lean_dec(v_a_2264_);
v___x_2298_ = 1;
if (v_isShared_2261_ == 0)
{
v___x_2300_ = v___x_2260_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v_reuseFailAlloc_2304_, 1, v_contextDependent_2258_);
v___x_2300_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
lean_object* v___x_2302_; 
lean_ctor_set_uint8(v___x_2300_, 0, v___x_2298_);
if (v_isShared_2267_ == 0)
{
lean_ctor_set(v___x_2266_, 0, v___x_2300_);
v___x_2302_ = v___x_2266_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v___x_2300_);
v___x_2302_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
return v___x_2302_;
}
}
}
}
}
else
{
lean_object* v_a_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2313_; 
lean_del_object(v___x_2260_);
v_a_2306_ = lean_ctor_get(v___x_2263_, 0);
v_isSharedCheck_2313_ = !lean_is_exclusive(v___x_2263_);
if (v_isSharedCheck_2313_ == 0)
{
v___x_2308_ = v___x_2263_;
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_a_2306_);
lean_dec(v___x_2263_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
lean_object* v___x_2311_; 
if (v_isShared_2309_ == 0)
{
v___x_2311_ = v___x_2308_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v_a_2306_);
v___x_2311_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
return v___x_2311_;
}
}
}
}
}
else
{
lean_object* v_e_x27_2315_; lean_object* v_proof_2316_; uint8_t v_contextDependent_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2483_; 
v_e_x27_2315_ = lean_ctor_get(v_res_2248_, 0);
v_proof_2316_ = lean_ctor_get(v_res_2248_, 1);
v_contextDependent_2317_ = lean_ctor_get_uint8(v_res_2248_, sizeof(void*)*2 + 1);
v_isSharedCheck_2483_ = !lean_is_exclusive(v_res_2248_);
if (v_isSharedCheck_2483_ == 0)
{
v___x_2319_ = v_res_2248_;
v_isShared_2320_ = v_isSharedCheck_2483_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_proof_2316_);
lean_inc(v_e_x27_2315_);
lean_dec(v_res_2248_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2483_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v___x_2321_; 
lean_inc_ref(v_e_x27_2315_);
v___x_2321_ = l_Lean_Meta_Sym_inferType___redArg(v_e_x27_2315_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
if (lean_obj_tag(v___x_2321_) == 0)
{
lean_object* v_a_2322_; lean_object* v___x_2323_; uint8_t v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; 
v_a_2322_ = lean_ctor_get(v___x_2321_, 0);
lean_inc(v_a_2322_);
lean_dec_ref(v___x_2321_);
v___x_2323_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__1));
v___x_2324_ = 0;
v___x_2325_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2);
lean_inc(v_idx_2245_);
lean_inc(v_typeName_2244_);
v___x_2326_ = l_Lean_Expr_proj___override(v_typeName_2244_, v_idx_2245_, v___x_2325_);
v___x_2327_ = l_Lean_mkLambda(v___x_2323_, v___x_2324_, v_a_2322_, v___x_2326_);
lean_inc_ref(v___x_2327_);
v___x_2328_ = l_Lean_Meta_Sym_inferType___redArg(v___x_2327_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
if (lean_obj_tag(v___x_2328_) == 0)
{
lean_object* v_a_2329_; uint8_t v___x_2330_; 
v_a_2329_ = lean_ctor_get(v___x_2328_, 0);
lean_inc(v_a_2329_);
lean_dec_ref(v___x_2328_);
v___x_2330_ = l_Lean_Expr_isArrow(v_a_2329_);
if (v___x_2330_ == 0)
{
lean_object* v___x_2331_; lean_object* v___x_2332_; 
lean_dec(v_a_2329_);
lean_inc_ref(v_e_2219_);
v___x_2331_ = lean_alloc_closure((void*)(l_Lean_Meta_reduceProj_x3f___boxed), 6, 1);
lean_closure_set(v___x_2331_, 0, v_e_2219_);
v___x_2332_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___x_2331_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
if (lean_obj_tag(v___x_2332_) == 0)
{
lean_object* v_a_2333_; 
v_a_2333_ = lean_ctor_get(v___x_2332_, 0);
lean_inc(v_a_2333_);
lean_dec_ref(v___x_2332_);
if (lean_obj_tag(v_a_2333_) == 0)
{
lean_object* v___x_2334_; 
lean_del_object(v___x_2319_);
lean_inc_ref(v_e_x27_2315_);
lean_inc_ref(v_struct_2246_);
v___x_2334_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_struct_2246_, v_e_x27_2315_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_object* v_a_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2378_; 
v_a_2335_ = lean_ctor_get(v___x_2334_, 0);
v_isSharedCheck_2378_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2337_ = v___x_2334_;
v_isShared_2338_ = v_isSharedCheck_2378_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_a_2335_);
lean_dec(v___x_2334_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2378_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
uint8_t v___x_2339_; 
v___x_2339_ = lean_unbox(v_a_2335_);
lean_dec(v_a_2335_);
if (v___x_2339_ == 0)
{
uint8_t v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2343_; 
lean_dec_ref(v___x_2327_);
lean_dec_ref(v_proof_2316_);
lean_dec_ref(v_e_x27_2315_);
lean_dec_ref(v_e_2219_);
v___x_2340_ = 1;
v___x_2341_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2341_, 0, v___x_2340_);
lean_ctor_set_uint8(v___x_2341_, 1, v_contextDependent_2317_);
if (v_isShared_2338_ == 0)
{
lean_ctor_set(v___x_2337_, 0, v___x_2341_);
v___x_2343_ = v___x_2337_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v___x_2341_);
v___x_2343_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
return v___x_2343_;
}
}
else
{
lean_object* v___x_2345_; 
lean_del_object(v___x_2337_);
v___x_2345_ = l_Lean_Meta_mkHCongr(v___x_2327_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
if (lean_obj_tag(v___x_2345_) == 0)
{
lean_object* v_a_2346_; lean_object* v_proof_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; 
v_a_2346_ = lean_ctor_get(v___x_2345_, 0);
lean_inc(v_a_2346_);
lean_dec_ref(v___x_2345_);
v_proof_2347_ = lean_ctor_get(v_a_2346_, 1);
lean_inc_ref(v_proof_2347_);
lean_dec(v_a_2346_);
lean_inc_ref(v_e_x27_2315_);
lean_inc_ref(v_struct_2246_);
v___x_2348_ = l_Lean_mkApp3(v_proof_2347_, v_struct_2246_, v_e_x27_2315_, v_proof_2316_);
v___x_2349_ = l_Lean_Meta_mkEqOfHEq(v___x_2348_, v___x_2330_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
if (lean_obj_tag(v___x_2349_) == 0)
{
lean_object* v_a_2350_; uint8_t v___x_2351_; 
v_a_2350_ = lean_ctor_get(v___x_2349_, 0);
lean_inc(v_a_2350_);
lean_dec_ref(v___x_2349_);
v___x_2351_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_2246_, v_e_x27_2315_);
if (v___x_2351_ == 0)
{
lean_object* v___x_2352_; 
lean_inc(v_idx_2245_);
lean_inc(v_typeName_2244_);
lean_dec_ref(v_e_2219_);
v___x_2352_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_typeName_2244_, v_idx_2245_, v_e_x27_2315_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
if (lean_obj_tag(v___x_2352_) == 0)
{
lean_object* v_a_2353_; 
v_a_2353_ = lean_ctor_get(v___x_2352_, 0);
lean_inc(v_a_2353_);
lean_dec_ref(v___x_2352_);
v___y_2231_ = v___x_2330_;
v___y_2232_ = v_contextDependent_2317_;
v___y_2233_ = v_a_2350_;
v_a_2234_ = v_a_2353_;
goto v___jp_2230_;
}
else
{
lean_object* v_a_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2361_; 
lean_dec(v_a_2350_);
v_a_2354_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2356_ = v___x_2352_;
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_a_2354_);
lean_dec(v___x_2352_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___x_2359_; 
if (v_isShared_2357_ == 0)
{
v___x_2359_ = v___x_2356_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_a_2354_);
v___x_2359_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
return v___x_2359_;
}
}
}
}
else
{
lean_dec_ref(v_e_x27_2315_);
v___y_2231_ = v___x_2330_;
v___y_2232_ = v_contextDependent_2317_;
v___y_2233_ = v_a_2350_;
v_a_2234_ = v_e_2219_;
goto v___jp_2230_;
}
}
else
{
lean_object* v_a_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2369_; 
lean_dec_ref(v_e_x27_2315_);
lean_dec_ref(v_e_2219_);
v_a_2362_ = lean_ctor_get(v___x_2349_, 0);
v_isSharedCheck_2369_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2364_ = v___x_2349_;
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_dec(v___x_2349_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2367_; 
if (v_isShared_2365_ == 0)
{
v___x_2367_ = v___x_2364_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v_a_2362_);
v___x_2367_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
return v___x_2367_;
}
}
}
}
else
{
lean_object* v_a_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2377_; 
lean_dec_ref(v_proof_2316_);
lean_dec_ref(v_e_x27_2315_);
lean_dec_ref(v_e_2219_);
v_a_2370_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2377_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2377_ == 0)
{
v___x_2372_ = v___x_2345_;
v_isShared_2373_ = v_isSharedCheck_2377_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_a_2370_);
lean_dec(v___x_2345_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2377_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
lean_object* v___x_2375_; 
if (v_isShared_2373_ == 0)
{
v___x_2375_ = v___x_2372_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v_a_2370_);
v___x_2375_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
return v___x_2375_;
}
}
}
}
}
}
else
{
lean_object* v_a_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2386_; 
lean_dec_ref(v___x_2327_);
lean_dec_ref(v_proof_2316_);
lean_dec_ref(v_e_x27_2315_);
lean_dec_ref(v_e_2219_);
v_a_2379_ = lean_ctor_get(v___x_2334_, 0);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2381_ = v___x_2334_;
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_a_2379_);
lean_dec(v___x_2334_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v___x_2384_; 
if (v_isShared_2382_ == 0)
{
v___x_2384_ = v___x_2381_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v_a_2379_);
v___x_2384_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
return v___x_2384_;
}
}
}
}
else
{
lean_object* v_val_2387_; lean_object* v___x_2388_; 
lean_dec_ref(v___x_2327_);
lean_dec_ref(v_proof_2316_);
lean_dec_ref(v_e_x27_2315_);
lean_dec_ref(v_e_2219_);
v_val_2387_ = lean_ctor_get(v_a_2333_, 0);
lean_inc(v_val_2387_);
lean_dec_ref(v_a_2333_);
v___x_2388_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_val_2387_, v___y_2253_);
if (lean_obj_tag(v___x_2388_) == 0)
{
lean_object* v_a_2389_; lean_object* v___x_2390_; 
v_a_2389_ = lean_ctor_get(v___x_2388_, 0);
lean_inc_n(v_a_2389_, 2);
lean_dec_ref(v___x_2388_);
v___x_2390_ = l_Lean_Meta_Sym_mkEqRefl___redArg(v_a_2389_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
if (lean_obj_tag(v___x_2390_) == 0)
{
lean_object* v_a_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2401_; 
v_a_2391_ = lean_ctor_get(v___x_2390_, 0);
v_isSharedCheck_2401_ = !lean_is_exclusive(v___x_2390_);
if (v_isSharedCheck_2401_ == 0)
{
v___x_2393_ = v___x_2390_;
v_isShared_2394_ = v_isSharedCheck_2401_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_a_2391_);
lean_dec(v___x_2390_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2401_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2396_; 
if (v_isShared_2320_ == 0)
{
lean_ctor_set(v___x_2319_, 1, v_a_2391_);
lean_ctor_set(v___x_2319_, 0, v_a_2389_);
v___x_2396_ = v___x_2319_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v_a_2389_);
lean_ctor_set(v_reuseFailAlloc_2400_, 1, v_a_2391_);
v___x_2396_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
lean_object* v___x_2398_; 
lean_ctor_set_uint8(v___x_2396_, sizeof(void*)*2, v_contextDependent_2317_);
lean_ctor_set_uint8(v___x_2396_, sizeof(void*)*2 + 1, v___x_2330_);
if (v_isShared_2394_ == 0)
{
lean_ctor_set(v___x_2393_, 0, v___x_2396_);
v___x_2398_ = v___x_2393_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v___x_2396_);
v___x_2398_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
return v___x_2398_;
}
}
}
}
else
{
lean_object* v_a_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2409_; 
lean_dec(v_a_2389_);
lean_del_object(v___x_2319_);
v_a_2402_ = lean_ctor_get(v___x_2390_, 0);
v_isSharedCheck_2409_ = !lean_is_exclusive(v___x_2390_);
if (v_isSharedCheck_2409_ == 0)
{
v___x_2404_ = v___x_2390_;
v_isShared_2405_ = v_isSharedCheck_2409_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_a_2402_);
lean_dec(v___x_2390_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2409_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
lean_object* v___x_2407_; 
if (v_isShared_2405_ == 0)
{
v___x_2407_ = v___x_2404_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v_a_2402_);
v___x_2407_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
return v___x_2407_;
}
}
}
}
else
{
lean_object* v_a_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2417_; 
lean_del_object(v___x_2319_);
v_a_2410_ = lean_ctor_get(v___x_2388_, 0);
v_isSharedCheck_2417_ = !lean_is_exclusive(v___x_2388_);
if (v_isSharedCheck_2417_ == 0)
{
v___x_2412_ = v___x_2388_;
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_a_2410_);
lean_dec(v___x_2388_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2415_; 
if (v_isShared_2413_ == 0)
{
v___x_2415_ = v___x_2412_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v_a_2410_);
v___x_2415_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
return v___x_2415_;
}
}
}
}
}
else
{
lean_object* v_a_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2425_; 
lean_dec_ref(v___x_2327_);
lean_del_object(v___x_2319_);
lean_dec_ref(v_proof_2316_);
lean_dec_ref(v_e_x27_2315_);
lean_dec_ref(v_e_2219_);
v_a_2418_ = lean_ctor_get(v___x_2332_, 0);
v_isSharedCheck_2425_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2420_ = v___x_2332_;
v_isShared_2421_ = v_isSharedCheck_2425_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_a_2418_);
lean_dec(v___x_2332_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2425_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v___x_2423_; 
if (v_isShared_2421_ == 0)
{
v___x_2423_ = v___x_2420_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v_a_2418_);
v___x_2423_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
return v___x_2423_;
}
}
}
}
else
{
lean_del_object(v___x_2319_);
if (lean_obj_tag(v_a_2329_) == 7)
{
lean_object* v_binderType_2426_; lean_object* v_body_2427_; lean_object* v___x_2428_; 
v_binderType_2426_ = lean_ctor_get(v_a_2329_, 1);
lean_inc_ref_n(v_binderType_2426_, 2);
v_body_2427_ = lean_ctor_get(v_a_2329_, 2);
lean_inc_ref(v_body_2427_);
lean_dec_ref(v_a_2329_);
v___x_2428_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_2426_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
if (lean_obj_tag(v___x_2428_) == 0)
{
lean_object* v_a_2429_; lean_object* v___x_2430_; 
v_a_2429_ = lean_ctor_get(v___x_2428_, 0);
lean_inc(v_a_2429_);
lean_dec_ref(v___x_2428_);
lean_inc_ref(v_body_2427_);
v___x_2430_ = l_Lean_Meta_Sym_getLevel___redArg(v_body_2427_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
if (lean_obj_tag(v___x_2430_) == 0)
{
lean_object* v_a_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; uint8_t v___x_2438_; 
v_a_2431_ = lean_ctor_get(v___x_2430_, 0);
lean_inc(v_a_2431_);
lean_dec_ref(v___x_2430_);
v___x_2432_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4));
v___x_2433_ = lean_box(0);
v___x_2434_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2434_, 0, v_a_2431_);
lean_ctor_set(v___x_2434_, 1, v___x_2433_);
v___x_2435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2435_, 0, v_a_2429_);
lean_ctor_set(v___x_2435_, 1, v___x_2434_);
v___x_2436_ = l_Lean_mkConst(v___x_2432_, v___x_2435_);
lean_inc_ref(v_e_x27_2315_);
lean_inc_ref(v_struct_2246_);
v___x_2437_ = l_Lean_mkApp6(v___x_2436_, v_binderType_2426_, v_body_2427_, v_struct_2246_, v_e_x27_2315_, v___x_2327_, v_proof_2316_);
v___x_2438_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_2246_, v_e_x27_2315_);
if (v___x_2438_ == 0)
{
lean_object* v___x_2439_; 
lean_inc(v_idx_2245_);
lean_inc(v_typeName_2244_);
lean_dec_ref(v_e_2219_);
v___x_2439_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_typeName_2244_, v_idx_2245_, v_e_x27_2315_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
if (lean_obj_tag(v___x_2439_) == 0)
{
lean_object* v_a_2440_; 
v_a_2440_ = lean_ctor_get(v___x_2439_, 0);
lean_inc(v_a_2440_);
lean_dec_ref(v___x_2439_);
v___y_2238_ = v_contextDependent_2317_;
v___y_2239_ = v___x_2437_;
v_a_2240_ = v_a_2440_;
goto v___jp_2237_;
}
else
{
lean_object* v_a_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2448_; 
lean_dec_ref(v___x_2437_);
v_a_2441_ = lean_ctor_get(v___x_2439_, 0);
v_isSharedCheck_2448_ = !lean_is_exclusive(v___x_2439_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2443_ = v___x_2439_;
v_isShared_2444_ = v_isSharedCheck_2448_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_a_2441_);
lean_dec(v___x_2439_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2448_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
lean_object* v___x_2446_; 
if (v_isShared_2444_ == 0)
{
v___x_2446_ = v___x_2443_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v_a_2441_);
v___x_2446_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
return v___x_2446_;
}
}
}
}
else
{
lean_dec_ref(v_e_x27_2315_);
v___y_2238_ = v_contextDependent_2317_;
v___y_2239_ = v___x_2437_;
v_a_2240_ = v_e_2219_;
goto v___jp_2237_;
}
}
else
{
lean_object* v_a_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2456_; 
lean_dec(v_a_2429_);
lean_dec_ref(v_body_2427_);
lean_dec_ref(v_binderType_2426_);
lean_dec_ref(v___x_2327_);
lean_dec_ref(v_proof_2316_);
lean_dec_ref(v_e_x27_2315_);
lean_dec_ref(v_e_2219_);
v_a_2449_ = lean_ctor_get(v___x_2430_, 0);
v_isSharedCheck_2456_ = !lean_is_exclusive(v___x_2430_);
if (v_isSharedCheck_2456_ == 0)
{
v___x_2451_ = v___x_2430_;
v_isShared_2452_ = v_isSharedCheck_2456_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_a_2449_);
lean_dec(v___x_2430_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2456_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v___x_2454_; 
if (v_isShared_2452_ == 0)
{
v___x_2454_ = v___x_2451_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_a_2449_);
v___x_2454_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
return v___x_2454_;
}
}
}
}
else
{
lean_object* v_a_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2464_; 
lean_dec_ref(v_body_2427_);
lean_dec_ref(v_binderType_2426_);
lean_dec_ref(v___x_2327_);
lean_dec_ref(v_proof_2316_);
lean_dec_ref(v_e_x27_2315_);
lean_dec_ref(v_e_2219_);
v_a_2457_ = lean_ctor_get(v___x_2428_, 0);
v_isSharedCheck_2464_ = !lean_is_exclusive(v___x_2428_);
if (v_isSharedCheck_2464_ == 0)
{
v___x_2459_ = v___x_2428_;
v_isShared_2460_ = v_isSharedCheck_2464_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_a_2457_);
lean_dec(v___x_2428_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2464_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v___x_2462_; 
if (v_isShared_2460_ == 0)
{
v___x_2462_ = v___x_2459_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v_a_2457_);
v___x_2462_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
return v___x_2462_;
}
}
}
}
else
{
lean_object* v___x_2465_; lean_object* v___x_2466_; 
lean_dec(v_a_2329_);
lean_dec_ref(v___x_2327_);
lean_dec_ref(v_proof_2316_);
lean_dec_ref(v_e_x27_2315_);
lean_dec_ref(v_e_2219_);
v___x_2465_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8);
v___x_2466_ = l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1(v___x_2465_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
return v___x_2466_;
}
}
}
else
{
lean_object* v_a_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2474_; 
lean_dec_ref(v___x_2327_);
lean_del_object(v___x_2319_);
lean_dec_ref(v_proof_2316_);
lean_dec_ref(v_e_x27_2315_);
lean_dec_ref(v_e_2219_);
v_a_2467_ = lean_ctor_get(v___x_2328_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2328_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2469_ = v___x_2328_;
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_a_2467_);
lean_dec(v___x_2328_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2472_; 
if (v_isShared_2470_ == 0)
{
v___x_2472_ = v___x_2469_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_a_2467_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
return v___x_2472_;
}
}
}
}
else
{
lean_object* v_a_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2482_; 
lean_del_object(v___x_2319_);
lean_dec_ref(v_proof_2316_);
lean_dec_ref(v_e_x27_2315_);
lean_dec_ref(v_e_2219_);
v_a_2475_ = lean_ctor_get(v___x_2321_, 0);
v_isSharedCheck_2482_ = !lean_is_exclusive(v___x_2321_);
if (v_isSharedCheck_2482_ == 0)
{
v___x_2477_ = v___x_2321_;
v_isShared_2478_ = v_isSharedCheck_2482_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_a_2475_);
lean_dec(v___x_2321_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2482_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v___x_2480_; 
if (v_isShared_2478_ == 0)
{
v___x_2480_ = v___x_2477_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v_a_2475_);
v___x_2480_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
return v___x_2480_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2781_; lean_object* v___x_2782_; 
lean_dec_ref(v_e_2219_);
v___x_2781_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
v___x_2782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2782_, 0, v___x_2781_);
return v___x_2782_;
}
v___jp_2230_:
{
lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2235_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2235_, 0, v_a_2234_);
lean_ctor_set(v___x_2235_, 1, v___y_2233_);
lean_ctor_set_uint8(v___x_2235_, sizeof(void*)*2, v___y_2232_);
lean_ctor_set_uint8(v___x_2235_, sizeof(void*)*2 + 1, v___y_2231_);
v___x_2236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2236_, 0, v___x_2235_);
return v___x_2236_;
}
v___jp_2237_:
{
uint8_t v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2241_ = 0;
v___x_2242_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2242_, 0, v_a_2240_);
lean_ctor_set(v___x_2242_, 1, v___y_2239_);
lean_ctor_set_uint8(v___x_2242_, sizeof(void*)*2, v___y_2238_);
lean_ctor_set_uint8(v___x_2242_, sizeof(void*)*2 + 1, v___x_2241_);
v___x_2243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2243_, 0, v___x_2242_);
return v___x_2243_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___boxed(lean_object* v_e_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_){
_start:
{
lean_object* v_res_2794_; 
v_res_2794_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj(v_e_2783_, v_a_2784_, v_a_2785_, v_a_2786_, v_a_2787_, v_a_2788_, v_a_2789_, v_a_2790_, v_a_2791_, v_a_2792_);
lean_dec(v_a_2792_);
lean_dec_ref(v_a_2791_);
lean_dec(v_a_2790_);
lean_dec_ref(v_a_2789_);
lean_dec(v_a_2788_);
lean_dec_ref(v_a_2787_);
lean_dec(v_a_2786_);
lean_dec_ref(v_a_2785_);
lean_dec(v_a_2784_);
return v_res_2794_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__6(lean_object* v_00_u03b1_2795_, lean_object* v_x_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_){
_start:
{
lean_object* v___x_2807_; 
v___x_2807_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__6___redArg(v_x_2796_);
return v___x_2807_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__6___boxed(lean_object* v_00_u03b1_2808_, lean_object* v_x_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_){
_start:
{
lean_object* v_res_2820_; 
v_res_2820_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__6(v_00_u03b1_2808_, v_x_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_);
lean_dec(v___y_2818_);
lean_dec_ref(v___y_2817_);
lean_dec(v___y_2816_);
lean_dec_ref(v___y_2815_);
lean_dec(v___y_2814_);
lean_dec_ref(v___y_2813_);
lean_dec(v___y_2812_);
lean_dec_ref(v___y_2811_);
lean_dec(v___y_2810_);
return v_res_2820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5(lean_object* v_oldTraces_2821_, lean_object* v_data_2822_, lean_object* v_ref_2823_, lean_object* v_msg_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_){
_start:
{
lean_object* v___x_2835_; 
v___x_2835_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5___redArg(v_oldTraces_2821_, v_data_2822_, v_ref_2823_, v_msg_2824_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_);
return v___x_2835_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5___boxed(lean_object* v_oldTraces_2836_, lean_object* v_data_2837_, lean_object* v_ref_2838_, lean_object* v_msg_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_){
_start:
{
lean_object* v_res_2850_; 
v_res_2850_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5(v_oldTraces_2836_, v_data_2837_, v_ref_2838_, v_msg_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2847_);
lean_dec(v___y_2846_);
lean_dec_ref(v___y_2845_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec(v___y_2840_);
return v_res_2850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0_spec__1___redArg(lean_object* v_f_2851_, lean_object* v_a_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_){
_start:
{
lean_object* v___y_2861_; lean_object* v___x_2864_; uint8_t v_debug_2865_; 
v___x_2864_ = lean_st_ref_get(v___y_2854_);
v_debug_2865_ = lean_ctor_get_uint8(v___x_2864_, sizeof(void*)*10);
lean_dec(v___x_2864_);
if (v_debug_2865_ == 0)
{
v___y_2861_ = v___y_2854_;
goto v___jp_2860_;
}
else
{
lean_object* v___x_2866_; 
lean_inc_ref(v_f_2851_);
v___x_2866_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_2851_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_);
if (lean_obj_tag(v___x_2866_) == 0)
{
lean_object* v___x_2867_; 
lean_dec_ref(v___x_2866_);
lean_inc_ref(v_a_2852_);
v___x_2867_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_);
if (lean_obj_tag(v___x_2867_) == 0)
{
lean_dec_ref(v___x_2867_);
v___y_2861_ = v___y_2854_;
goto v___jp_2860_;
}
else
{
lean_object* v_a_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2875_; 
lean_dec_ref(v_a_2852_);
lean_dec_ref(v_f_2851_);
v_a_2868_ = lean_ctor_get(v___x_2867_, 0);
v_isSharedCheck_2875_ = !lean_is_exclusive(v___x_2867_);
if (v_isSharedCheck_2875_ == 0)
{
v___x_2870_ = v___x_2867_;
v_isShared_2871_ = v_isSharedCheck_2875_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_a_2868_);
lean_dec(v___x_2867_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2875_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
lean_object* v___x_2873_; 
if (v_isShared_2871_ == 0)
{
v___x_2873_ = v___x_2870_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v_a_2868_);
v___x_2873_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
return v___x_2873_;
}
}
}
}
else
{
lean_object* v_a_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2883_; 
lean_dec_ref(v_a_2852_);
lean_dec_ref(v_f_2851_);
v_a_2876_ = lean_ctor_get(v___x_2866_, 0);
v_isSharedCheck_2883_ = !lean_is_exclusive(v___x_2866_);
if (v_isSharedCheck_2883_ == 0)
{
v___x_2878_ = v___x_2866_;
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_a_2876_);
lean_dec(v___x_2866_);
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
v___jp_2860_:
{
lean_object* v___x_2862_; lean_object* v___x_2863_; 
v___x_2862_ = l_Lean_Expr_app___override(v_f_2851_, v_a_2852_);
v___x_2863_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2862_, v___y_2861_);
return v___x_2863_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_2884_, lean_object* v_a_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_){
_start:
{
lean_object* v_res_2893_; 
v_res_2893_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0_spec__1___redArg(v_f_2884_, v_a_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_);
lean_dec(v___y_2891_);
lean_dec_ref(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec(v___y_2887_);
lean_dec_ref(v___y_2886_);
return v_res_2893_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0(lean_object* v_args_2894_, lean_object* v_endIdx_2895_, lean_object* v_b_2896_, lean_object* v_i_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_){
_start:
{
uint8_t v___x_2908_; 
v___x_2908_ = lean_nat_dec_le(v_endIdx_2895_, v_i_2897_);
if (v___x_2908_ == 0)
{
lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; 
v___x_2909_ = l_Lean_instInhabitedExpr;
v___x_2910_ = lean_array_get_borrowed(v___x_2909_, v_args_2894_, v_i_2897_);
lean_inc(v___x_2910_);
v___x_2911_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0_spec__1___redArg(v_b_2896_, v___x_2910_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_);
if (lean_obj_tag(v___x_2911_) == 0)
{
lean_object* v_a_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; 
v_a_2912_ = lean_ctor_get(v___x_2911_, 0);
lean_inc(v_a_2912_);
lean_dec_ref(v___x_2911_);
v___x_2913_ = lean_unsigned_to_nat(1u);
v___x_2914_ = lean_nat_add(v_i_2897_, v___x_2913_);
lean_dec(v_i_2897_);
v_b_2896_ = v_a_2912_;
v_i_2897_ = v___x_2914_;
goto _start;
}
else
{
lean_dec(v_i_2897_);
return v___x_2911_;
}
}
else
{
lean_object* v___x_2916_; 
lean_dec(v_i_2897_);
v___x_2916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2916_, 0, v_b_2896_);
return v___x_2916_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0___boxed(lean_object* v_args_2917_, lean_object* v_endIdx_2918_, lean_object* v_b_2919_, lean_object* v_i_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_){
_start:
{
lean_object* v_res_2931_; 
v_res_2931_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0(v_args_2917_, v_endIdx_2918_, v_b_2919_, v_i_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v___y_2927_);
lean_dec_ref(v___y_2926_);
lean_dec(v___y_2925_);
lean_dec_ref(v___y_2924_);
lean_dec(v___y_2923_);
lean_dec_ref(v___y_2922_);
lean_dec(v___y_2921_);
lean_dec(v_endIdx_2918_);
lean_dec_ref(v_args_2917_);
return v_res_2931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0(lean_object* v_f_2932_, lean_object* v_args_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_){
_start:
{
lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; 
v___x_2944_ = lean_unsigned_to_nat(0u);
v___x_2945_ = lean_array_get_size(v_args_2933_);
v___x_2946_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0(v_args_2933_, v___x_2945_, v_f_2932_, v___x_2944_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_);
return v___x_2946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0___boxed(lean_object* v_f_2947_, lean_object* v_args_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_){
_start:
{
lean_object* v_res_2959_; 
v_res_2959_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0(v_f_2947_, v_args_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_);
lean_dec(v___y_2957_);
lean_dec_ref(v___y_2956_);
lean_dec(v___y_2955_);
lean_dec_ref(v___y_2954_);
lean_dec(v___y_2953_);
lean_dec_ref(v___y_2952_);
lean_dec(v___y_2951_);
lean_dec_ref(v___y_2950_);
lean_dec(v___y_2949_);
lean_dec_ref(v_args_2948_);
return v_res_2959_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__0(void){
_start:
{
lean_object* v___x_2960_; lean_object* v_dummy_2961_; 
v___x_2960_ = lean_box(0);
v_dummy_2961_ = l_Lean_Expr_sort___override(v___x_2960_);
return v_dummy_2961_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__2(void){
_start:
{
lean_object* v___x_2963_; lean_object* v___x_2964_; 
v___x_2963_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__1));
v___x_2964_ = l_Lean_stringToMessageData(v___x_2963_);
return v___x_2964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn(lean_object* v_e_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_){
_start:
{
uint8_t v___x_2979_; 
v___x_2979_ = l_Lean_Expr_isApp(v_e_2965_);
if (v___x_2979_ == 0)
{
lean_object* v___x_2980_; lean_object* v___x_2981_; 
lean_dec_ref(v_e_2965_);
v___x_2980_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2980_, 0, v___x_2979_);
lean_ctor_set_uint8(v___x_2980_, 1, v___x_2979_);
v___x_2981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2981_, 0, v___x_2980_);
return v___x_2981_;
}
else
{
lean_object* v_fn_2982_; uint8_t v___x_2983_; 
v_fn_2982_ = l_Lean_Expr_getAppFn(v_e_2965_);
v___x_2983_ = l_Lean_Expr_isLambda(v_fn_2982_);
if (v___x_2983_ == 0)
{
uint8_t v___x_2984_; 
v___x_2984_ = l_Lean_Expr_isConst(v_fn_2982_);
if (v___x_2984_ == 0)
{
lean_object* v___x_2985_; 
lean_inc(v_a_2974_);
lean_inc_ref(v_a_2973_);
lean_inc(v_a_2972_);
lean_inc_ref(v_a_2971_);
lean_inc(v_a_2970_);
lean_inc_ref(v_a_2969_);
lean_inc(v_a_2968_);
lean_inc_ref(v_a_2967_);
lean_inc(v_a_2966_);
lean_inc_ref(v_fn_2982_);
v___x_2985_ = lean_sym_simp(v_fn_2982_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_2985_) == 0)
{
lean_object* v_a_2986_; 
v_a_2986_ = lean_ctor_get(v___x_2985_, 0);
lean_inc(v_a_2986_);
if (lean_obj_tag(v_a_2986_) == 0)
{
lean_dec_ref(v_a_2986_);
lean_dec_ref(v_fn_2982_);
lean_dec_ref(v_e_2965_);
return v___x_2985_;
}
else
{
lean_object* v_e_x27_2987_; lean_object* v_proof_2988_; uint8_t v_contextDependent_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_3093_; 
lean_dec_ref(v___x_2985_);
v_e_x27_2987_ = lean_ctor_get(v_a_2986_, 0);
v_proof_2988_ = lean_ctor_get(v_a_2986_, 1);
v_contextDependent_2989_ = lean_ctor_get_uint8(v_a_2986_, sizeof(void*)*2 + 1);
v_isSharedCheck_3093_ = !lean_is_exclusive(v_a_2986_);
if (v_isSharedCheck_3093_ == 0)
{
v___x_2991_ = v_a_2986_;
v_isShared_2992_ = v_isSharedCheck_3093_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_proof_2988_);
lean_inc(v_e_x27_2987_);
lean_dec(v_a_2986_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_3093_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2993_; 
lean_inc_ref(v_e_x27_2987_);
v___x_2993_ = l_Lean_Meta_Sym_inferType___redArg(v_e_x27_2987_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_2993_) == 0)
{
lean_object* v_a_2994_; lean_object* v___x_2995_; lean_object* v_dummy_2996_; lean_object* v_nargs_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; 
v_a_2994_ = lean_ctor_get(v___x_2993_, 0);
lean_inc(v_a_2994_);
lean_dec_ref(v___x_2993_);
v___x_2995_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2);
v_dummy_2996_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__0, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__0_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__0);
v_nargs_2997_ = l_Lean_Expr_getAppNumArgs(v_e_2965_);
lean_inc(v_nargs_2997_);
v___x_2998_ = lean_mk_array(v_nargs_2997_, v_dummy_2996_);
v___x_2999_ = lean_unsigned_to_nat(1u);
v___x_3000_ = lean_nat_sub(v_nargs_2997_, v___x_2999_);
lean_dec(v_nargs_2997_);
lean_inc_ref(v_e_2965_);
v___x_3001_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2965_, v___x_2998_, v___x_3000_);
v___x_3002_ = l_Lean_mkAppN(v___x_2995_, v___x_3001_);
lean_inc_ref(v_e_x27_2987_);
v___x_3003_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0(v_e_x27_2987_, v___x_3001_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
lean_dec_ref(v___x_3001_);
if (lean_obj_tag(v___x_3003_) == 0)
{
lean_object* v_a_3004_; lean_object* v___x_3005_; 
v_a_3004_ = lean_ctor_get(v___x_3003_, 0);
lean_inc(v_a_3004_);
lean_dec_ref(v___x_3003_);
lean_inc_ref(v_e_2965_);
v___x_3005_ = l_Lean_Meta_Sym_inferType___redArg(v_e_2965_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3005_) == 0)
{
lean_object* v_a_3006_; lean_object* v___x_3007_; uint8_t v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; 
v_a_3006_ = lean_ctor_get(v___x_3005_, 0);
lean_inc(v_a_3006_);
lean_dec_ref(v___x_3005_);
v___x_3007_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__1));
v___x_3008_ = 0;
lean_inc_n(v_a_2994_, 2);
v___x_3009_ = l_Lean_mkLambda(v___x_3007_, v___x_3008_, v_a_2994_, v___x_3002_);
v___x_3010_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_2994_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3010_) == 0)
{
lean_object* v_a_3011_; lean_object* v___x_3012_; 
v_a_3011_ = lean_ctor_get(v___x_3010_, 0);
lean_inc(v_a_3011_);
lean_dec_ref(v___x_3010_);
lean_inc(v_a_3006_);
v___x_3012_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_3006_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3012_) == 0)
{
lean_object* v_options_3013_; lean_object* v_a_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3052_; 
v_options_3013_ = lean_ctor_get(v_a_2973_, 2);
v_a_3014_ = lean_ctor_get(v___x_3012_, 0);
v_isSharedCheck_3052_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3052_ == 0)
{
v___x_3016_ = v___x_3012_;
v_isShared_3017_ = v_isSharedCheck_3052_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_a_3014_);
lean_dec(v___x_3012_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3052_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v_inheritedTraceOptions_3018_; uint8_t v_hasTrace_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; 
v_inheritedTraceOptions_3018_ = lean_ctor_get(v_a_2973_, 13);
v_hasTrace_3019_ = lean_ctor_get_uint8(v_options_3013_, sizeof(void*)*1);
v___x_3020_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4));
v___x_3021_ = lean_box(0);
v___x_3022_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3022_, 0, v_a_3014_);
lean_ctor_set(v___x_3022_, 1, v___x_3021_);
v___x_3023_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3023_, 0, v_a_3011_);
lean_ctor_set(v___x_3023_, 1, v___x_3022_);
v___x_3024_ = l_Lean_mkConst(v___x_3020_, v___x_3023_);
v___x_3025_ = l_Lean_mkApp6(v___x_3024_, v_a_2994_, v_a_3006_, v_fn_2982_, v_e_x27_2987_, v___x_3009_, v_proof_2988_);
if (v_hasTrace_3019_ == 0)
{
lean_dec_ref(v_e_2965_);
goto v___jp_3026_;
}
else
{
lean_object* v___x_3033_; lean_object* v___x_3034_; uint8_t v___x_3035_; 
v___x_3033_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2));
v___x_3034_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3);
v___x_3035_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3018_, v_options_3013_, v___x_3034_);
if (v___x_3035_ == 0)
{
lean_dec_ref(v_e_2965_);
goto v___jp_3026_;
}
else
{
lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; 
v___x_3036_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__2, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__2);
v___x_3037_ = l_Lean_indentExpr(v_e_2965_);
v___x_3038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3038_, 0, v___x_3036_);
lean_ctor_set(v___x_3038_, 1, v___x_3037_);
v___x_3039_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_3040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3040_, 0, v___x_3038_);
lean_ctor_set(v___x_3040_, 1, v___x_3039_);
lean_inc(v_a_3004_);
v___x_3041_ = l_Lean_indentExpr(v_a_3004_);
v___x_3042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3042_, 0, v___x_3040_);
lean_ctor_set(v___x_3042_, 1, v___x_3041_);
v___x_3043_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(v___x_3033_, v___x_3042_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
if (lean_obj_tag(v___x_3043_) == 0)
{
lean_dec_ref(v___x_3043_);
goto v___jp_3026_;
}
else
{
lean_object* v_a_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3051_; 
lean_dec_ref(v___x_3025_);
lean_del_object(v___x_3016_);
lean_dec(v_a_3004_);
lean_del_object(v___x_2991_);
v_a_3044_ = lean_ctor_get(v___x_3043_, 0);
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_3043_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3046_ = v___x_3043_;
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_a_3044_);
lean_dec(v___x_3043_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v___x_3049_; 
if (v_isShared_3047_ == 0)
{
v___x_3049_ = v___x_3046_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_a_3044_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
}
}
}
}
}
v___jp_3026_:
{
lean_object* v___x_3028_; 
if (v_isShared_2992_ == 0)
{
lean_ctor_set(v___x_2991_, 1, v___x_3025_);
lean_ctor_set(v___x_2991_, 0, v_a_3004_);
v___x_3028_ = v___x_2991_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v_a_3004_);
lean_ctor_set(v_reuseFailAlloc_3032_, 1, v___x_3025_);
v___x_3028_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
lean_object* v___x_3030_; 
lean_ctor_set_uint8(v___x_3028_, sizeof(void*)*2, v_contextDependent_2989_);
lean_ctor_set_uint8(v___x_3028_, sizeof(void*)*2 + 1, v___x_2984_);
if (v_isShared_3017_ == 0)
{
lean_ctor_set(v___x_3016_, 0, v___x_3028_);
v___x_3030_ = v___x_3016_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v___x_3028_);
v___x_3030_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
return v___x_3030_;
}
}
}
}
}
else
{
lean_object* v_a_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3060_; 
lean_dec(v_a_3011_);
lean_dec_ref(v___x_3009_);
lean_dec(v_a_3006_);
lean_dec(v_a_3004_);
lean_dec(v_a_2994_);
lean_del_object(v___x_2991_);
lean_dec_ref(v_proof_2988_);
lean_dec_ref(v_e_x27_2987_);
lean_dec_ref(v_fn_2982_);
lean_dec_ref(v_e_2965_);
v_a_3053_ = lean_ctor_get(v___x_3012_, 0);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_3055_ = v___x_3012_;
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_a_3053_);
lean_dec(v___x_3012_);
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
lean_dec_ref(v___x_3009_);
lean_dec(v_a_3006_);
lean_dec(v_a_3004_);
lean_dec(v_a_2994_);
lean_del_object(v___x_2991_);
lean_dec_ref(v_proof_2988_);
lean_dec_ref(v_e_x27_2987_);
lean_dec_ref(v_fn_2982_);
lean_dec_ref(v_e_2965_);
v_a_3061_ = lean_ctor_get(v___x_3010_, 0);
v_isSharedCheck_3068_ = !lean_is_exclusive(v___x_3010_);
if (v_isSharedCheck_3068_ == 0)
{
v___x_3063_ = v___x_3010_;
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_a_3061_);
lean_dec(v___x_3010_);
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
else
{
lean_object* v_a_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3076_; 
lean_dec(v_a_3004_);
lean_dec_ref(v___x_3002_);
lean_dec(v_a_2994_);
lean_del_object(v___x_2991_);
lean_dec_ref(v_proof_2988_);
lean_dec_ref(v_e_x27_2987_);
lean_dec_ref(v_fn_2982_);
lean_dec_ref(v_e_2965_);
v_a_3069_ = lean_ctor_get(v___x_3005_, 0);
v_isSharedCheck_3076_ = !lean_is_exclusive(v___x_3005_);
if (v_isSharedCheck_3076_ == 0)
{
v___x_3071_ = v___x_3005_;
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_a_3069_);
lean_dec(v___x_3005_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3076_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
lean_object* v___x_3074_; 
if (v_isShared_3072_ == 0)
{
v___x_3074_ = v___x_3071_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v_a_3069_);
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
else
{
lean_object* v_a_3077_; lean_object* v___x_3079_; uint8_t v_isShared_3080_; uint8_t v_isSharedCheck_3084_; 
lean_dec_ref(v___x_3002_);
lean_dec(v_a_2994_);
lean_del_object(v___x_2991_);
lean_dec_ref(v_proof_2988_);
lean_dec_ref(v_e_x27_2987_);
lean_dec_ref(v_fn_2982_);
lean_dec_ref(v_e_2965_);
v_a_3077_ = lean_ctor_get(v___x_3003_, 0);
v_isSharedCheck_3084_ = !lean_is_exclusive(v___x_3003_);
if (v_isSharedCheck_3084_ == 0)
{
v___x_3079_ = v___x_3003_;
v_isShared_3080_ = v_isSharedCheck_3084_;
goto v_resetjp_3078_;
}
else
{
lean_inc(v_a_3077_);
lean_dec(v___x_3003_);
v___x_3079_ = lean_box(0);
v_isShared_3080_ = v_isSharedCheck_3084_;
goto v_resetjp_3078_;
}
v_resetjp_3078_:
{
lean_object* v___x_3082_; 
if (v_isShared_3080_ == 0)
{
v___x_3082_ = v___x_3079_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v_a_3077_);
v___x_3082_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
return v___x_3082_;
}
}
}
}
else
{
lean_object* v_a_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3092_; 
lean_del_object(v___x_2991_);
lean_dec_ref(v_proof_2988_);
lean_dec_ref(v_e_x27_2987_);
lean_dec_ref(v_fn_2982_);
lean_dec_ref(v_e_2965_);
v_a_3085_ = lean_ctor_get(v___x_2993_, 0);
v_isSharedCheck_3092_ = !lean_is_exclusive(v___x_2993_);
if (v_isSharedCheck_3092_ == 0)
{
v___x_3087_ = v___x_2993_;
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_a_3085_);
lean_dec(v___x_2993_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v___x_3090_; 
if (v_isShared_3088_ == 0)
{
v___x_3090_ = v___x_3087_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v_a_3085_);
v___x_3090_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
return v___x_3090_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_fn_2982_);
lean_dec_ref(v_e_2965_);
return v___x_2985_;
}
}
else
{
lean_dec_ref(v_fn_2982_);
lean_dec_ref(v_e_2965_);
goto v___jp_2976_;
}
}
else
{
lean_dec_ref(v_fn_2982_);
lean_dec_ref(v_e_2965_);
goto v___jp_2976_;
}
}
v___jp_2976_:
{
lean_object* v___x_2977_; lean_object* v___x_2978_; 
v___x_2977_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
v___x_2978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2978_, 0, v___x_2977_);
return v___x_2978_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___boxed(lean_object* v_e_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_, lean_object* v_a_3102_, lean_object* v_a_3103_, lean_object* v_a_3104_){
_start:
{
lean_object* v_res_3105_; 
v_res_3105_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn(v_e_3094_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_, v_a_3101_, v_a_3102_, v_a_3103_);
lean_dec(v_a_3103_);
lean_dec_ref(v_a_3102_);
lean_dec(v_a_3101_);
lean_dec_ref(v_a_3100_);
lean_dec(v_a_3099_);
lean_dec_ref(v_a_3098_);
lean_dec(v_a_3097_);
lean_dec_ref(v_a_3096_);
lean_dec(v_a_3095_);
return v_res_3105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0_spec__1(lean_object* v_f_3106_, lean_object* v_a_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_){
_start:
{
lean_object* v___x_3118_; 
v___x_3118_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0_spec__1___redArg(v_f_3106_, v_a_3107_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_);
return v___x_3118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0_spec__1___boxed(lean_object* v_f_3119_, lean_object* v_a_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_){
_start:
{
lean_object* v_res_3131_; 
v_res_3131_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0_spec__1(v_f_3119_, v_a_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_);
lean_dec(v___y_3129_);
lean_dec_ref(v___y_3128_);
lean_dec(v___y_3127_);
lean_dec_ref(v___y_3126_);
lean_dec(v___y_3125_);
lean_dec_ref(v___y_3124_);
lean_dec(v___y_3123_);
lean_dec_ref(v___y_3122_);
lean_dec(v___y_3121_);
return v_res_3131_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___closed__1(void){
_start:
{
lean_object* v___x_3133_; lean_object* v___x_3134_; 
v___x_3133_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___closed__0));
v___x_3134_ = l_Lean_stringToMessageData(v___x_3133_);
return v___x_3134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst(lean_object* v_e_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_, lean_object* v_a_3138_, lean_object* v_a_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_){
_start:
{
if (lean_obj_tag(v_e_3135_) == 4)
{
lean_object* v_declName_3146_; lean_object* v_us_3147_; lean_object* v___x_3148_; 
v_declName_3146_ = lean_ctor_get(v_e_3135_, 0);
v_us_3147_ = lean_ctor_get(v_e_3135_, 1);
lean_inc(v_declName_3146_);
v___x_3148_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0(v_declName_3146_, v_a_3136_, v_a_3137_, v_a_3138_, v_a_3139_, v_a_3140_, v_a_3141_, v_a_3142_, v_a_3143_, v_a_3144_);
if (lean_obj_tag(v___x_3148_) == 0)
{
lean_object* v_a_3149_; lean_object* v___x_3151_; uint8_t v_isShared_3152_; uint8_t v_isSharedCheck_3280_; 
v_a_3149_ = lean_ctor_get(v___x_3148_, 0);
v_isSharedCheck_3280_ = !lean_is_exclusive(v___x_3148_);
if (v_isSharedCheck_3280_ == 0)
{
v___x_3151_ = v___x_3148_;
v_isShared_3152_ = v_isSharedCheck_3280_;
goto v_resetjp_3150_;
}
else
{
lean_inc(v_a_3149_);
lean_dec(v___x_3148_);
v___x_3151_ = lean_box(0);
v_isShared_3152_ = v_isSharedCheck_3280_;
goto v_resetjp_3150_;
}
v_resetjp_3150_:
{
uint8_t v___x_3153_; 
v___x_3153_ = l_Lean_ConstantInfo_isDefinition(v_a_3149_);
if (v___x_3153_ == 0)
{
lean_object* v___x_3154_; lean_object* v___x_3156_; 
lean_dec(v_a_3149_);
lean_dec_ref(v_e_3135_);
v___x_3154_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_3154_, 0, v___x_3153_);
lean_ctor_set_uint8(v___x_3154_, 1, v___x_3153_);
if (v_isShared_3152_ == 0)
{
lean_ctor_set(v___x_3151_, 0, v___x_3154_);
v___x_3156_ = v___x_3151_;
goto v_reusejp_3155_;
}
else
{
lean_object* v_reuseFailAlloc_3157_; 
v_reuseFailAlloc_3157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3157_, 0, v___x_3154_);
v___x_3156_ = v_reuseFailAlloc_3157_;
goto v_reusejp_3155_;
}
v_reusejp_3155_:
{
return v___x_3156_;
}
}
else
{
lean_object* v___x_3158_; 
lean_del_object(v___x_3151_);
lean_inc_ref(v_e_3135_);
v___x_3158_ = l_Lean_Meta_Sym_inferType___redArg(v_e_3135_, v_a_3140_, v_a_3141_, v_a_3142_, v_a_3143_, v_a_3144_);
if (lean_obj_tag(v___x_3158_) == 0)
{
lean_object* v_a_3159_; lean_object* v___x_3160_; 
v_a_3159_ = lean_ctor_get(v___x_3158_, 0);
lean_inc(v_a_3159_);
lean_dec_ref(v___x_3158_);
v___x_3160_ = l_Lean_Meta_whnfD(v_a_3159_, v_a_3141_, v_a_3142_, v_a_3143_, v_a_3144_);
if (lean_obj_tag(v___x_3160_) == 0)
{
lean_object* v_a_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3263_; 
v_a_3161_ = lean_ctor_get(v___x_3160_, 0);
v_isSharedCheck_3263_ = !lean_is_exclusive(v___x_3160_);
if (v_isSharedCheck_3263_ == 0)
{
v___x_3163_ = v___x_3160_;
v_isShared_3164_ = v_isSharedCheck_3263_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_a_3161_);
lean_dec(v___x_3160_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3263_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
if (lean_obj_tag(v_a_3161_) == 7)
{
lean_object* v___x_3165_; lean_object* v___x_3167_; 
lean_dec_ref(v_a_3161_);
lean_dec(v_a_3149_);
lean_dec_ref(v_e_3135_);
v___x_3165_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
if (v_isShared_3164_ == 0)
{
lean_ctor_set(v___x_3163_, 0, v___x_3165_);
v___x_3167_ = v___x_3163_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v___x_3165_);
v___x_3167_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
return v___x_3167_;
}
}
else
{
uint8_t v___x_3169_; lean_object* v___y_3171_; lean_object* v___y_3172_; lean_object* v___y_3173_; lean_object* v___y_3174_; lean_object* v___y_3175_; lean_object* v___y_3176_; uint8_t v___y_3196_; uint8_t v___x_3258_; 
lean_dec(v_a_3161_);
v___x_3169_ = 0;
v___x_3258_ = l_Lean_ConstantInfo_hasValue(v_a_3149_, v___x_3169_);
if (v___x_3258_ == 0)
{
v___y_3196_ = v___x_3258_;
goto v___jp_3195_;
}
else
{
lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; uint8_t v___x_3262_; 
v___x_3259_ = l_Lean_ConstantInfo_levelParams(v_a_3149_);
v___x_3260_ = l_List_lengthTR___redArg(v___x_3259_);
lean_dec(v___x_3259_);
v___x_3261_ = l_List_lengthTR___redArg(v_us_3147_);
v___x_3262_ = lean_nat_dec_eq(v___x_3260_, v___x_3261_);
lean_dec(v___x_3261_);
lean_dec(v___x_3260_);
v___y_3196_ = v___x_3262_;
goto v___jp_3195_;
}
v___jp_3170_:
{
lean_object* v___x_3177_; 
lean_inc_ref(v___y_3171_);
v___x_3177_ = l_Lean_Meta_Sym_mkEqRefl___redArg(v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_);
if (lean_obj_tag(v___x_3177_) == 0)
{
lean_object* v_a_3178_; lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3186_; 
v_a_3178_ = lean_ctor_get(v___x_3177_, 0);
v_isSharedCheck_3186_ = !lean_is_exclusive(v___x_3177_);
if (v_isSharedCheck_3186_ == 0)
{
v___x_3180_ = v___x_3177_;
v_isShared_3181_ = v_isSharedCheck_3186_;
goto v_resetjp_3179_;
}
else
{
lean_inc(v_a_3178_);
lean_dec(v___x_3177_);
v___x_3180_ = lean_box(0);
v_isShared_3181_ = v_isSharedCheck_3186_;
goto v_resetjp_3179_;
}
v_resetjp_3179_:
{
lean_object* v___x_3182_; lean_object* v___x_3184_; 
v___x_3182_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3182_, 0, v___y_3171_);
lean_ctor_set(v___x_3182_, 1, v_a_3178_);
lean_ctor_set_uint8(v___x_3182_, sizeof(void*)*2, v___x_3169_);
lean_ctor_set_uint8(v___x_3182_, sizeof(void*)*2 + 1, v___x_3169_);
if (v_isShared_3181_ == 0)
{
lean_ctor_set(v___x_3180_, 0, v___x_3182_);
v___x_3184_ = v___x_3180_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v___x_3182_);
v___x_3184_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3183_;
}
v_reusejp_3183_:
{
return v___x_3184_;
}
}
}
else
{
lean_object* v_a_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3194_; 
lean_dec_ref(v___y_3171_);
v_a_3187_ = lean_ctor_get(v___x_3177_, 0);
v_isSharedCheck_3194_ = !lean_is_exclusive(v___x_3177_);
if (v_isSharedCheck_3194_ == 0)
{
v___x_3189_ = v___x_3177_;
v_isShared_3190_ = v_isSharedCheck_3194_;
goto v_resetjp_3188_;
}
else
{
lean_inc(v_a_3187_);
lean_dec(v___x_3177_);
v___x_3189_ = lean_box(0);
v_isShared_3190_ = v_isSharedCheck_3194_;
goto v_resetjp_3188_;
}
v_resetjp_3188_:
{
lean_object* v___x_3192_; 
if (v_isShared_3190_ == 0)
{
v___x_3192_ = v___x_3189_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v_a_3187_);
v___x_3192_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
return v___x_3192_;
}
}
}
}
v___jp_3195_:
{
if (v___y_3196_ == 0)
{
lean_object* v___x_3197_; lean_object* v___x_3199_; 
lean_dec(v_a_3149_);
lean_dec_ref(v_e_3135_);
v___x_3197_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
if (v_isShared_3164_ == 0)
{
lean_ctor_set(v___x_3163_, 0, v___x_3197_);
v___x_3199_ = v___x_3163_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v___x_3197_);
v___x_3199_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
return v___x_3199_;
}
}
else
{
lean_object* v___x_3201_; 
lean_del_object(v___x_3163_);
lean_inc(v_us_3147_);
v___x_3201_ = l_Lean_Core_instantiateValueLevelParams(v_a_3149_, v_us_3147_, v___x_3169_, v_a_3143_, v_a_3144_);
lean_dec(v_a_3149_);
if (lean_obj_tag(v___x_3201_) == 0)
{
lean_object* v_a_3202_; lean_object* v___x_3203_; 
v_a_3202_ = lean_ctor_get(v___x_3201_, 0);
lean_inc(v_a_3202_);
lean_dec_ref(v___x_3201_);
v___x_3203_ = l_Lean_Meta_Sym_unfoldReducible(v_a_3202_, v_a_3141_, v_a_3142_, v_a_3143_, v_a_3144_);
if (lean_obj_tag(v___x_3203_) == 0)
{
lean_object* v_a_3204_; lean_object* v___x_3205_; 
v_a_3204_ = lean_ctor_get(v___x_3203_, 0);
lean_inc(v_a_3204_);
lean_dec_ref(v___x_3203_);
v___x_3205_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_a_3204_, v_a_3140_);
if (lean_obj_tag(v___x_3205_) == 0)
{
lean_object* v_options_3206_; uint8_t v_hasTrace_3207_; 
v_options_3206_ = lean_ctor_get(v_a_3143_, 2);
v_hasTrace_3207_ = lean_ctor_get_uint8(v_options_3206_, sizeof(void*)*1);
if (v_hasTrace_3207_ == 0)
{
lean_object* v_a_3208_; 
lean_dec_ref(v_e_3135_);
v_a_3208_ = lean_ctor_get(v___x_3205_, 0);
lean_inc(v_a_3208_);
lean_dec_ref(v___x_3205_);
v___y_3171_ = v_a_3208_;
v___y_3172_ = v_a_3140_;
v___y_3173_ = v_a_3141_;
v___y_3174_ = v_a_3142_;
v___y_3175_ = v_a_3143_;
v___y_3176_ = v_a_3144_;
goto v___jp_3170_;
}
else
{
lean_object* v_a_3209_; lean_object* v_inheritedTraceOptions_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; uint8_t v___x_3213_; 
v_a_3209_ = lean_ctor_get(v___x_3205_, 0);
lean_inc(v_a_3209_);
lean_dec_ref(v___x_3205_);
v_inheritedTraceOptions_3210_ = lean_ctor_get(v_a_3143_, 13);
v___x_3211_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__1));
v___x_3212_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__2, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__2);
v___x_3213_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3210_, v_options_3206_, v___x_3212_);
if (v___x_3213_ == 0)
{
lean_dec_ref(v_e_3135_);
v___y_3171_ = v_a_3209_;
v___y_3172_ = v_a_3140_;
v___y_3173_ = v_a_3141_;
v___y_3174_ = v_a_3142_;
v___y_3175_ = v_a_3143_;
v___y_3176_ = v_a_3144_;
goto v___jp_3170_;
}
else
{
lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; 
v___x_3214_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___closed__1, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___closed__1);
lean_inc(v_declName_3146_);
v___x_3215_ = l_Lean_MessageData_ofName(v_declName_3146_);
v___x_3216_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3216_, 0, v___x_3214_);
lean_ctor_set(v___x_3216_, 1, v___x_3215_);
v___x_3217_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8);
v___x_3218_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3218_, 0, v___x_3216_);
lean_ctor_set(v___x_3218_, 1, v___x_3217_);
v___x_3219_ = l_Lean_indentExpr(v_e_3135_);
v___x_3220_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3220_, 0, v___x_3218_);
lean_ctor_set(v___x_3220_, 1, v___x_3219_);
v___x_3221_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_3222_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3222_, 0, v___x_3220_);
lean_ctor_set(v___x_3222_, 1, v___x_3221_);
lean_inc(v_a_3209_);
v___x_3223_ = l_Lean_indentExpr(v_a_3209_);
v___x_3224_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3224_, 0, v___x_3222_);
lean_ctor_set(v___x_3224_, 1, v___x_3223_);
v___x_3225_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(v___x_3211_, v___x_3224_, v_a_3141_, v_a_3142_, v_a_3143_, v_a_3144_);
if (lean_obj_tag(v___x_3225_) == 0)
{
lean_dec_ref(v___x_3225_);
v___y_3171_ = v_a_3209_;
v___y_3172_ = v_a_3140_;
v___y_3173_ = v_a_3141_;
v___y_3174_ = v_a_3142_;
v___y_3175_ = v_a_3143_;
v___y_3176_ = v_a_3144_;
goto v___jp_3170_;
}
else
{
lean_object* v_a_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3233_; 
lean_dec(v_a_3209_);
v_a_3226_ = lean_ctor_get(v___x_3225_, 0);
v_isSharedCheck_3233_ = !lean_is_exclusive(v___x_3225_);
if (v_isSharedCheck_3233_ == 0)
{
v___x_3228_ = v___x_3225_;
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_a_3226_);
lean_dec(v___x_3225_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v___x_3231_; 
if (v_isShared_3229_ == 0)
{
v___x_3231_ = v___x_3228_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v_a_3226_);
v___x_3231_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
return v___x_3231_;
}
}
}
}
}
}
else
{
lean_object* v_a_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3241_; 
lean_dec_ref(v_e_3135_);
v_a_3234_ = lean_ctor_get(v___x_3205_, 0);
v_isSharedCheck_3241_ = !lean_is_exclusive(v___x_3205_);
if (v_isSharedCheck_3241_ == 0)
{
v___x_3236_ = v___x_3205_;
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_a_3234_);
lean_dec(v___x_3205_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
lean_object* v___x_3239_; 
if (v_isShared_3237_ == 0)
{
v___x_3239_ = v___x_3236_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v_a_3234_);
v___x_3239_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
return v___x_3239_;
}
}
}
}
else
{
lean_object* v_a_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3249_; 
lean_dec_ref(v_e_3135_);
v_a_3242_ = lean_ctor_get(v___x_3203_, 0);
v_isSharedCheck_3249_ = !lean_is_exclusive(v___x_3203_);
if (v_isSharedCheck_3249_ == 0)
{
v___x_3244_ = v___x_3203_;
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_a_3242_);
lean_dec(v___x_3203_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
lean_object* v___x_3247_; 
if (v_isShared_3245_ == 0)
{
v___x_3247_ = v___x_3244_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v_a_3242_);
v___x_3247_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
return v___x_3247_;
}
}
}
}
else
{
lean_object* v_a_3250_; lean_object* v___x_3252_; uint8_t v_isShared_3253_; uint8_t v_isSharedCheck_3257_; 
lean_dec_ref(v_e_3135_);
v_a_3250_ = lean_ctor_get(v___x_3201_, 0);
v_isSharedCheck_3257_ = !lean_is_exclusive(v___x_3201_);
if (v_isSharedCheck_3257_ == 0)
{
v___x_3252_ = v___x_3201_;
v_isShared_3253_ = v_isSharedCheck_3257_;
goto v_resetjp_3251_;
}
else
{
lean_inc(v_a_3250_);
lean_dec(v___x_3201_);
v___x_3252_ = lean_box(0);
v_isShared_3253_ = v_isSharedCheck_3257_;
goto v_resetjp_3251_;
}
v_resetjp_3251_:
{
lean_object* v___x_3255_; 
if (v_isShared_3253_ == 0)
{
v___x_3255_ = v___x_3252_;
goto v_reusejp_3254_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v_a_3250_);
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
}
}
}
}
else
{
lean_object* v_a_3264_; lean_object* v___x_3266_; uint8_t v_isShared_3267_; uint8_t v_isSharedCheck_3271_; 
lean_dec(v_a_3149_);
lean_dec_ref(v_e_3135_);
v_a_3264_ = lean_ctor_get(v___x_3160_, 0);
v_isSharedCheck_3271_ = !lean_is_exclusive(v___x_3160_);
if (v_isSharedCheck_3271_ == 0)
{
v___x_3266_ = v___x_3160_;
v_isShared_3267_ = v_isSharedCheck_3271_;
goto v_resetjp_3265_;
}
else
{
lean_inc(v_a_3264_);
lean_dec(v___x_3160_);
v___x_3266_ = lean_box(0);
v_isShared_3267_ = v_isSharedCheck_3271_;
goto v_resetjp_3265_;
}
v_resetjp_3265_:
{
lean_object* v___x_3269_; 
if (v_isShared_3267_ == 0)
{
v___x_3269_ = v___x_3266_;
goto v_reusejp_3268_;
}
else
{
lean_object* v_reuseFailAlloc_3270_; 
v_reuseFailAlloc_3270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3270_, 0, v_a_3264_);
v___x_3269_ = v_reuseFailAlloc_3270_;
goto v_reusejp_3268_;
}
v_reusejp_3268_:
{
return v___x_3269_;
}
}
}
}
else
{
lean_object* v_a_3272_; lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3279_; 
lean_dec(v_a_3149_);
lean_dec_ref(v_e_3135_);
v_a_3272_ = lean_ctor_get(v___x_3158_, 0);
v_isSharedCheck_3279_ = !lean_is_exclusive(v___x_3158_);
if (v_isSharedCheck_3279_ == 0)
{
v___x_3274_ = v___x_3158_;
v_isShared_3275_ = v_isSharedCheck_3279_;
goto v_resetjp_3273_;
}
else
{
lean_inc(v_a_3272_);
lean_dec(v___x_3158_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3279_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
lean_object* v___x_3277_; 
if (v_isShared_3275_ == 0)
{
v___x_3277_ = v___x_3274_;
goto v_reusejp_3276_;
}
else
{
lean_object* v_reuseFailAlloc_3278_; 
v_reuseFailAlloc_3278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3278_, 0, v_a_3272_);
v___x_3277_ = v_reuseFailAlloc_3278_;
goto v_reusejp_3276_;
}
v_reusejp_3276_:
{
return v___x_3277_;
}
}
}
}
}
}
else
{
lean_object* v_a_3281_; lean_object* v___x_3283_; uint8_t v_isShared_3284_; uint8_t v_isSharedCheck_3288_; 
lean_dec_ref(v_e_3135_);
v_a_3281_ = lean_ctor_get(v___x_3148_, 0);
v_isSharedCheck_3288_ = !lean_is_exclusive(v___x_3148_);
if (v_isSharedCheck_3288_ == 0)
{
v___x_3283_ = v___x_3148_;
v_isShared_3284_ = v_isSharedCheck_3288_;
goto v_resetjp_3282_;
}
else
{
lean_inc(v_a_3281_);
lean_dec(v___x_3148_);
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
else
{
lean_object* v___x_3289_; lean_object* v___x_3290_; 
lean_dec_ref(v_e_3135_);
v___x_3289_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
v___x_3290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3290_, 0, v___x_3289_);
return v___x_3290_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___boxed(lean_object* v_e_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_){
_start:
{
lean_object* v_res_3302_; 
v_res_3302_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst(v_e_3291_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_, v_a_3300_);
lean_dec(v_a_3300_);
lean_dec_ref(v_a_3299_);
lean_dec(v_a_3298_);
lean_dec_ref(v_a_3297_);
lean_dec(v_a_3296_);
lean_dec_ref(v_a_3295_);
lean_dec(v_a_3294_);
lean_dec_ref(v_a_3293_);
lean_dec(v_a_3292_);
return v_res_3302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___lam__0(lean_object* v_x_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_){
_start:
{
lean_object* v___x_3315_; 
lean_inc_ref(v___y_3304_);
v___x_3315_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems(v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_);
if (lean_obj_tag(v___x_3315_) == 0)
{
lean_object* v_a_3316_; 
v_a_3316_ = lean_ctor_get(v___x_3315_, 0);
lean_inc(v_a_3316_);
if (lean_obj_tag(v_a_3316_) == 0)
{
uint8_t v_done_3317_; 
v_done_3317_ = lean_ctor_get_uint8(v_a_3316_, 0);
if (v_done_3317_ == 0)
{
uint8_t v_contextDependent_3318_; lean_object* v___x_3319_; 
lean_dec_ref(v___x_3315_);
v_contextDependent_3318_ = lean_ctor_get_uint8(v_a_3316_, 1);
lean_dec_ref(v_a_3316_);
v___x_3319_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst(v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_);
if (lean_obj_tag(v___x_3319_) == 0)
{
lean_object* v_a_3320_; uint8_t v___y_3322_; 
v_a_3320_ = lean_ctor_get(v___x_3319_, 0);
lean_inc(v_a_3320_);
if (v_contextDependent_3318_ == 0)
{
lean_dec(v_a_3320_);
return v___x_3319_;
}
else
{
if (lean_obj_tag(v_a_3320_) == 0)
{
uint8_t v_contextDependent_3332_; 
v_contextDependent_3332_ = lean_ctor_get_uint8(v_a_3320_, 1);
v___y_3322_ = v_contextDependent_3332_;
goto v___jp_3321_;
}
else
{
uint8_t v___x_3333_; 
v___x_3333_ = 0;
v___y_3322_ = v___x_3333_;
goto v___jp_3321_;
}
}
v___jp_3321_:
{
if (v___y_3322_ == 0)
{
lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3330_; 
v_isSharedCheck_3330_ = !lean_is_exclusive(v___x_3319_);
if (v_isSharedCheck_3330_ == 0)
{
lean_object* v_unused_3331_; 
v_unused_3331_ = lean_ctor_get(v___x_3319_, 0);
lean_dec(v_unused_3331_);
v___x_3324_ = v___x_3319_;
v_isShared_3325_ = v_isSharedCheck_3330_;
goto v_resetjp_3323_;
}
else
{
lean_dec(v___x_3319_);
v___x_3324_ = lean_box(0);
v_isShared_3325_ = v_isSharedCheck_3330_;
goto v_resetjp_3323_;
}
v_resetjp_3323_:
{
lean_object* v___x_3326_; lean_object* v___x_3328_; 
v___x_3326_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3320_);
if (v_isShared_3325_ == 0)
{
lean_ctor_set(v___x_3324_, 0, v___x_3326_);
v___x_3328_ = v___x_3324_;
goto v_reusejp_3327_;
}
else
{
lean_object* v_reuseFailAlloc_3329_; 
v_reuseFailAlloc_3329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3329_, 0, v___x_3326_);
v___x_3328_ = v_reuseFailAlloc_3329_;
goto v_reusejp_3327_;
}
v_reusejp_3327_:
{
return v___x_3328_;
}
}
}
else
{
lean_dec(v_a_3320_);
return v___x_3319_;
}
}
}
else
{
return v___x_3319_;
}
}
else
{
lean_dec_ref(v_a_3316_);
lean_dec_ref(v___y_3304_);
return v___x_3315_;
}
}
else
{
lean_dec_ref(v_a_3316_);
lean_dec_ref(v___y_3304_);
return v___x_3315_;
}
}
else
{
lean_dec_ref(v___y_3304_);
return v___x_3315_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___lam__0___boxed(lean_object* v_x_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_){
_start:
{
lean_object* v_res_3346_; 
v_res_3346_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___lam__0(v_x_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
lean_dec(v___y_3344_);
lean_dec_ref(v___y_3343_);
lean_dec(v___y_3342_);
lean_dec_ref(v___y_3341_);
lean_dec(v___y_3340_);
lean_dec_ref(v___y_3339_);
lean_dec(v___y_3338_);
lean_dec_ref(v___y_3337_);
lean_dec(v___y_3336_);
return v_res_3346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep(lean_object* v_e_3350_, lean_object* v_a_3351_, lean_object* v_a_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_, lean_object* v_a_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_){
_start:
{
switch(lean_obj_tag(v_e_3350_))
{
case 9:
{
lean_object* v___x_3364_; 
v___x_3364_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg(v_e_3350_, v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
return v___x_3364_;
}
case 11:
{
lean_object* v___x_3365_; 
v___x_3365_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj(v_e_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_, v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
return v___x_3365_;
}
case 4:
{
lean_object* v___x_3366_; 
lean_inc_ref(v_e_3350_);
v___x_3366_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleOpaqueConst(v_e_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_, v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
if (lean_obj_tag(v___x_3366_) == 0)
{
lean_object* v_a_3367_; lean_object* v___x_3368_; 
v_a_3367_ = lean_ctor_get(v___x_3366_, 0);
lean_inc(v_a_3367_);
v___x_3368_ = lean_box(0);
if (lean_obj_tag(v_a_3367_) == 0)
{
uint8_t v_done_3369_; 
v_done_3369_ = lean_ctor_get_uint8(v_a_3367_, 0);
if (v_done_3369_ == 0)
{
uint8_t v_contextDependent_3370_; lean_object* v___x_3371_; 
lean_dec_ref(v___x_3366_);
v_contextDependent_3370_ = lean_ctor_get_uint8(v_a_3367_, 1);
lean_dec_ref(v_a_3367_);
v___x_3371_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___lam__0(v___x_3368_, v_e_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_, v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
if (lean_obj_tag(v___x_3371_) == 0)
{
lean_object* v_a_3372_; uint8_t v___y_3374_; 
v_a_3372_ = lean_ctor_get(v___x_3371_, 0);
lean_inc(v_a_3372_);
if (v_contextDependent_3370_ == 0)
{
lean_dec(v_a_3372_);
return v___x_3371_;
}
else
{
if (lean_obj_tag(v_a_3372_) == 0)
{
uint8_t v_contextDependent_3384_; 
v_contextDependent_3384_ = lean_ctor_get_uint8(v_a_3372_, 1);
v___y_3374_ = v_contextDependent_3384_;
goto v___jp_3373_;
}
else
{
uint8_t v_contextDependent_3385_; 
v_contextDependent_3385_ = lean_ctor_get_uint8(v_a_3372_, sizeof(void*)*2 + 1);
v___y_3374_ = v_contextDependent_3385_;
goto v___jp_3373_;
}
}
v___jp_3373_:
{
if (v___y_3374_ == 0)
{
lean_object* v___x_3376_; uint8_t v_isShared_3377_; uint8_t v_isSharedCheck_3382_; 
v_isSharedCheck_3382_ = !lean_is_exclusive(v___x_3371_);
if (v_isSharedCheck_3382_ == 0)
{
lean_object* v_unused_3383_; 
v_unused_3383_ = lean_ctor_get(v___x_3371_, 0);
lean_dec(v_unused_3383_);
v___x_3376_ = v___x_3371_;
v_isShared_3377_ = v_isSharedCheck_3382_;
goto v_resetjp_3375_;
}
else
{
lean_dec(v___x_3371_);
v___x_3376_ = lean_box(0);
v_isShared_3377_ = v_isSharedCheck_3382_;
goto v_resetjp_3375_;
}
v_resetjp_3375_:
{
lean_object* v___x_3378_; lean_object* v___x_3380_; 
v___x_3378_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3372_);
if (v_isShared_3377_ == 0)
{
lean_ctor_set(v___x_3376_, 0, v___x_3378_);
v___x_3380_ = v___x_3376_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v___x_3378_);
v___x_3380_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
return v___x_3380_;
}
}
}
else
{
lean_dec(v_a_3372_);
return v___x_3371_;
}
}
}
else
{
return v___x_3371_;
}
}
else
{
lean_dec_ref(v_a_3367_);
lean_dec_ref(v_e_3350_);
return v___x_3366_;
}
}
else
{
uint8_t v_done_3386_; 
v_done_3386_ = lean_ctor_get_uint8(v_a_3367_, sizeof(void*)*2);
if (v_done_3386_ == 0)
{
lean_object* v_e_x27_3387_; lean_object* v_proof_3388_; uint8_t v_contextDependent_3389_; lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3439_; 
lean_dec_ref(v___x_3366_);
v_e_x27_3387_ = lean_ctor_get(v_a_3367_, 0);
v_proof_3388_ = lean_ctor_get(v_a_3367_, 1);
v_contextDependent_3389_ = lean_ctor_get_uint8(v_a_3367_, sizeof(void*)*2 + 1);
v_isSharedCheck_3439_ = !lean_is_exclusive(v_a_3367_);
if (v_isSharedCheck_3439_ == 0)
{
v___x_3391_ = v_a_3367_;
v_isShared_3392_ = v_isSharedCheck_3439_;
goto v_resetjp_3390_;
}
else
{
lean_inc(v_proof_3388_);
lean_inc(v_e_x27_3387_);
lean_dec(v_a_3367_);
v___x_3391_ = lean_box(0);
v_isShared_3392_ = v_isSharedCheck_3439_;
goto v_resetjp_3390_;
}
v_resetjp_3390_:
{
lean_object* v___x_3393_; 
lean_inc_ref(v_e_x27_3387_);
v___x_3393_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___lam__0(v___x_3368_, v_e_x27_3387_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_, v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
if (lean_obj_tag(v___x_3393_) == 0)
{
lean_object* v_a_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3438_; 
v_a_3394_ = lean_ctor_get(v___x_3393_, 0);
v_isSharedCheck_3438_ = !lean_is_exclusive(v___x_3393_);
if (v_isSharedCheck_3438_ == 0)
{
v___x_3396_ = v___x_3393_;
v_isShared_3397_ = v_isSharedCheck_3438_;
goto v_resetjp_3395_;
}
else
{
lean_inc(v_a_3394_);
lean_dec(v___x_3393_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3438_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
if (lean_obj_tag(v_a_3394_) == 0)
{
uint8_t v_done_3398_; uint8_t v_contextDependent_3399_; uint8_t v___y_3401_; 
lean_dec_ref(v_e_3350_);
v_done_3398_ = lean_ctor_get_uint8(v_a_3394_, 0);
v_contextDependent_3399_ = lean_ctor_get_uint8(v_a_3394_, 1);
lean_dec_ref(v_a_3394_);
if (v_contextDependent_3389_ == 0)
{
v___y_3401_ = v_contextDependent_3399_;
goto v___jp_3400_;
}
else
{
v___y_3401_ = v_contextDependent_3389_;
goto v___jp_3400_;
}
v___jp_3400_:
{
lean_object* v___x_3403_; 
if (v_isShared_3392_ == 0)
{
v___x_3403_ = v___x_3391_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3407_; 
v_reuseFailAlloc_3407_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3407_, 0, v_e_x27_3387_);
lean_ctor_set(v_reuseFailAlloc_3407_, 1, v_proof_3388_);
v___x_3403_ = v_reuseFailAlloc_3407_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
lean_object* v___x_3405_; 
lean_ctor_set_uint8(v___x_3403_, sizeof(void*)*2, v_done_3398_);
lean_ctor_set_uint8(v___x_3403_, sizeof(void*)*2 + 1, v___y_3401_);
if (v_isShared_3397_ == 0)
{
lean_ctor_set(v___x_3396_, 0, v___x_3403_);
v___x_3405_ = v___x_3396_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v___x_3403_);
v___x_3405_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
return v___x_3405_;
}
}
}
}
else
{
lean_object* v_e_x27_3408_; lean_object* v_proof_3409_; uint8_t v_done_3410_; uint8_t v_contextDependent_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3437_; 
lean_del_object(v___x_3396_);
lean_del_object(v___x_3391_);
v_e_x27_3408_ = lean_ctor_get(v_a_3394_, 0);
v_proof_3409_ = lean_ctor_get(v_a_3394_, 1);
v_done_3410_ = lean_ctor_get_uint8(v_a_3394_, sizeof(void*)*2);
v_contextDependent_3411_ = lean_ctor_get_uint8(v_a_3394_, sizeof(void*)*2 + 1);
v_isSharedCheck_3437_ = !lean_is_exclusive(v_a_3394_);
if (v_isSharedCheck_3437_ == 0)
{
v___x_3413_ = v_a_3394_;
v_isShared_3414_ = v_isSharedCheck_3437_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_proof_3409_);
lean_inc(v_e_x27_3408_);
lean_dec(v_a_3394_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3437_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v___x_3415_; 
lean_inc_ref(v_e_x27_3408_);
v___x_3415_ = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(v_e_3350_, v_e_x27_3387_, v_proof_3388_, v_e_x27_3408_, v_proof_3409_, v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
if (lean_obj_tag(v___x_3415_) == 0)
{
lean_object* v_a_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3428_; 
v_a_3416_ = lean_ctor_get(v___x_3415_, 0);
v_isSharedCheck_3428_ = !lean_is_exclusive(v___x_3415_);
if (v_isSharedCheck_3428_ == 0)
{
v___x_3418_ = v___x_3415_;
v_isShared_3419_ = v_isSharedCheck_3428_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_a_3416_);
lean_dec(v___x_3415_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3428_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
uint8_t v___y_3421_; 
if (v_contextDependent_3389_ == 0)
{
v___y_3421_ = v_contextDependent_3411_;
goto v___jp_3420_;
}
else
{
v___y_3421_ = v_contextDependent_3389_;
goto v___jp_3420_;
}
v___jp_3420_:
{
lean_object* v___x_3423_; 
if (v_isShared_3414_ == 0)
{
lean_ctor_set(v___x_3413_, 1, v_a_3416_);
v___x_3423_ = v___x_3413_;
goto v_reusejp_3422_;
}
else
{
lean_object* v_reuseFailAlloc_3427_; 
v_reuseFailAlloc_3427_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3427_, 0, v_e_x27_3408_);
lean_ctor_set(v_reuseFailAlloc_3427_, 1, v_a_3416_);
lean_ctor_set_uint8(v_reuseFailAlloc_3427_, sizeof(void*)*2, v_done_3410_);
v___x_3423_ = v_reuseFailAlloc_3427_;
goto v_reusejp_3422_;
}
v_reusejp_3422_:
{
lean_object* v___x_3425_; 
lean_ctor_set_uint8(v___x_3423_, sizeof(void*)*2 + 1, v___y_3421_);
if (v_isShared_3419_ == 0)
{
lean_ctor_set(v___x_3418_, 0, v___x_3423_);
v___x_3425_ = v___x_3418_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v___x_3423_);
v___x_3425_ = v_reuseFailAlloc_3426_;
goto v_reusejp_3424_;
}
v_reusejp_3424_:
{
return v___x_3425_;
}
}
}
}
}
else
{
lean_object* v_a_3429_; lean_object* v___x_3431_; uint8_t v_isShared_3432_; uint8_t v_isSharedCheck_3436_; 
lean_del_object(v___x_3413_);
lean_dec_ref(v_e_x27_3408_);
v_a_3429_ = lean_ctor_get(v___x_3415_, 0);
v_isSharedCheck_3436_ = !lean_is_exclusive(v___x_3415_);
if (v_isSharedCheck_3436_ == 0)
{
v___x_3431_ = v___x_3415_;
v_isShared_3432_ = v_isSharedCheck_3436_;
goto v_resetjp_3430_;
}
else
{
lean_inc(v_a_3429_);
lean_dec(v___x_3415_);
v___x_3431_ = lean_box(0);
v_isShared_3432_ = v_isSharedCheck_3436_;
goto v_resetjp_3430_;
}
v_resetjp_3430_:
{
lean_object* v___x_3434_; 
if (v_isShared_3432_ == 0)
{
v___x_3434_ = v___x_3431_;
goto v_reusejp_3433_;
}
else
{
lean_object* v_reuseFailAlloc_3435_; 
v_reuseFailAlloc_3435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3435_, 0, v_a_3429_);
v___x_3434_ = v_reuseFailAlloc_3435_;
goto v_reusejp_3433_;
}
v_reusejp_3433_:
{
return v___x_3434_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_3391_);
lean_dec_ref(v_proof_3388_);
lean_dec_ref(v_e_x27_3387_);
lean_dec_ref(v_e_3350_);
return v___x_3393_;
}
}
}
else
{
lean_dec_ref(v_a_3367_);
lean_dec_ref(v_e_3350_);
return v___x_3366_;
}
}
}
else
{
lean_dec_ref(v_e_3350_);
return v___x_3366_;
}
}
case 5:
{
lean_object* v___x_3440_; 
lean_inc_ref(v_e_3350_);
v___x_3440_ = l_Lean_Meta_Tactic_Cbv_tryMatcher(v_e_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_, v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
if (lean_obj_tag(v___x_3440_) == 0)
{
lean_object* v_a_3441_; 
v_a_3441_ = lean_ctor_get(v___x_3440_, 0);
lean_inc(v_a_3441_);
if (lean_obj_tag(v_a_3441_) == 0)
{
uint8_t v_done_3442_; 
v_done_3442_ = lean_ctor_get_uint8(v_a_3441_, 0);
if (v_done_3442_ == 0)
{
uint8_t v_contextDependent_3443_; lean_object* v___x_3444_; 
lean_dec_ref(v___x_3440_);
v_contextDependent_3443_ = lean_ctor_get_uint8(v_a_3441_, 1);
lean_dec_ref(v_a_3441_);
v___x_3444_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn(v_e_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_, v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
if (lean_obj_tag(v___x_3444_) == 0)
{
lean_object* v_a_3445_; uint8_t v___y_3447_; 
v_a_3445_ = lean_ctor_get(v___x_3444_, 0);
lean_inc(v_a_3445_);
if (v_contextDependent_3443_ == 0)
{
lean_dec(v_a_3445_);
return v___x_3444_;
}
else
{
if (lean_obj_tag(v_a_3445_) == 0)
{
uint8_t v_contextDependent_3457_; 
v_contextDependent_3457_ = lean_ctor_get_uint8(v_a_3445_, 1);
v___y_3447_ = v_contextDependent_3457_;
goto v___jp_3446_;
}
else
{
uint8_t v_contextDependent_3458_; 
v_contextDependent_3458_ = lean_ctor_get_uint8(v_a_3445_, sizeof(void*)*2 + 1);
v___y_3447_ = v_contextDependent_3458_;
goto v___jp_3446_;
}
}
v___jp_3446_:
{
if (v___y_3447_ == 0)
{
lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3455_; 
v_isSharedCheck_3455_ = !lean_is_exclusive(v___x_3444_);
if (v_isSharedCheck_3455_ == 0)
{
lean_object* v_unused_3456_; 
v_unused_3456_ = lean_ctor_get(v___x_3444_, 0);
lean_dec(v_unused_3456_);
v___x_3449_ = v___x_3444_;
v_isShared_3450_ = v_isSharedCheck_3455_;
goto v_resetjp_3448_;
}
else
{
lean_dec(v___x_3444_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3455_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v___x_3451_; lean_object* v___x_3453_; 
v___x_3451_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3445_);
if (v_isShared_3450_ == 0)
{
lean_ctor_set(v___x_3449_, 0, v___x_3451_);
v___x_3453_ = v___x_3449_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v___x_3451_);
v___x_3453_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
return v___x_3453_;
}
}
}
else
{
lean_dec(v_a_3445_);
return v___x_3444_;
}
}
}
else
{
return v___x_3444_;
}
}
else
{
lean_dec_ref(v_a_3441_);
lean_dec_ref(v_e_3350_);
return v___x_3440_;
}
}
else
{
lean_dec_ref(v_a_3441_);
lean_dec_ref(v_e_3350_);
return v___x_3440_;
}
}
else
{
lean_dec_ref(v_e_3350_);
return v___x_3440_;
}
}
case 8:
{
uint8_t v___x_3459_; 
v___x_3459_ = l_Lean_Expr_letNondep_x21(v_e_3350_);
if (v___x_3459_ == 0)
{
lean_object* v___x_3460_; 
v___x_3460_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg(v_e_3350_, v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
return v___x_3460_;
}
else
{
lean_object* v___x_3461_; 
v___x_3461_ = l_Lean_Meta_Sym_Simp_toBetaApp(v_e_3350_, v_a_3354_, v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
if (lean_obj_tag(v___x_3461_) == 0)
{
lean_object* v_a_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3473_; 
v_a_3462_ = lean_ctor_get(v___x_3461_, 0);
v_isSharedCheck_3473_ = !lean_is_exclusive(v___x_3461_);
if (v_isSharedCheck_3473_ == 0)
{
v___x_3464_ = v___x_3461_;
v_isShared_3465_ = v_isSharedCheck_3473_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_a_3462_);
lean_dec(v___x_3461_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3473_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
lean_object* v_e_3466_; lean_object* v_h_3467_; uint8_t v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3471_; 
v_e_3466_ = lean_ctor_get(v_a_3462_, 2);
lean_inc_ref(v_e_3466_);
v_h_3467_ = lean_ctor_get(v_a_3462_, 3);
lean_inc_ref(v_h_3467_);
lean_dec(v_a_3462_);
v___x_3468_ = 0;
v___x_3469_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3469_, 0, v_e_3466_);
lean_ctor_set(v___x_3469_, 1, v_h_3467_);
lean_ctor_set_uint8(v___x_3469_, sizeof(void*)*2, v___x_3468_);
lean_ctor_set_uint8(v___x_3469_, sizeof(void*)*2 + 1, v___x_3468_);
if (v_isShared_3465_ == 0)
{
lean_ctor_set(v___x_3464_, 0, v___x_3469_);
v___x_3471_ = v___x_3464_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v___x_3469_);
v___x_3471_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
return v___x_3471_;
}
}
}
else
{
lean_object* v_a_3474_; lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3481_; 
v_a_3474_ = lean_ctor_get(v___x_3461_, 0);
v_isSharedCheck_3481_ = !lean_is_exclusive(v___x_3461_);
if (v_isSharedCheck_3481_ == 0)
{
v___x_3476_ = v___x_3461_;
v_isShared_3477_ = v_isSharedCheck_3481_;
goto v_resetjp_3475_;
}
else
{
lean_inc(v_a_3474_);
lean_dec(v___x_3461_);
v___x_3476_ = lean_box(0);
v_isShared_3477_ = v_isSharedCheck_3481_;
goto v_resetjp_3475_;
}
v_resetjp_3475_:
{
lean_object* v___x_3479_; 
if (v_isShared_3477_ == 0)
{
v___x_3479_ = v___x_3476_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v_a_3474_);
v___x_3479_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
return v___x_3479_;
}
}
}
}
}
case 7:
{
lean_dec_ref(v_e_3350_);
goto v___jp_3361_;
}
case 6:
{
lean_dec_ref(v_e_3350_);
goto v___jp_3361_;
}
case 1:
{
lean_object* v___x_3482_; lean_object* v___x_3483_; 
lean_dec_ref(v_e_3350_);
v___x_3482_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___closed__0));
v___x_3483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3483_, 0, v___x_3482_);
return v___x_3483_;
}
case 2:
{
lean_object* v___x_3484_; lean_object* v___x_3485_; 
lean_dec_ref(v_e_3350_);
v___x_3484_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___closed__0));
v___x_3485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3485_, 0, v___x_3484_);
return v___x_3485_;
}
case 0:
{
lean_object* v___x_3486_; lean_object* v___x_3487_; 
lean_dec_ref(v_e_3350_);
v___x_3486_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___closed__0));
v___x_3487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3487_, 0, v___x_3486_);
return v___x_3487_;
}
case 3:
{
lean_object* v___x_3488_; lean_object* v___x_3489_; 
lean_dec_ref(v_e_3350_);
v___x_3488_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___closed__0));
v___x_3489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3489_, 0, v___x_3488_);
return v___x_3489_;
}
default: 
{
lean_object* v___x_3490_; lean_object* v___x_3491_; 
lean_dec_ref(v_e_3350_);
v___x_3490_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
v___x_3491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3491_, 0, v___x_3490_);
return v___x_3491_;
}
}
v___jp_3361_:
{
lean_object* v___x_3362_; lean_object* v___x_3363_; 
v___x_3362_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___closed__0));
v___x_3363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3363_, 0, v___x_3362_);
return v___x_3363_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___boxed(lean_object* v_e_3492_, lean_object* v_a_3493_, lean_object* v_a_3494_, lean_object* v_a_3495_, lean_object* v_a_3496_, lean_object* v_a_3497_, lean_object* v_a_3498_, lean_object* v_a_3499_, lean_object* v_a_3500_, lean_object* v_a_3501_, lean_object* v_a_3502_){
_start:
{
lean_object* v_res_3503_; 
v_res_3503_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep(v_e_3492_, v_a_3493_, v_a_3494_, v_a_3495_, v_a_3496_, v_a_3497_, v_a_3498_, v_a_3499_, v_a_3500_, v_a_3501_);
lean_dec(v_a_3501_);
lean_dec_ref(v_a_3500_);
lean_dec(v_a_3499_);
lean_dec_ref(v_a_3498_);
lean_dec(v_a_3497_);
lean_dec_ref(v_a_3496_);
lean_dec(v_a_3495_);
lean_dec_ref(v_a_3494_);
lean_dec(v_a_3493_);
return v_res_3503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPre(lean_object* v_simprocs_3504_, lean_object* v_a_3505_, lean_object* v_a_3506_, lean_object* v_a_3507_, lean_object* v_a_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_){
_start:
{
lean_object* v___y_3517_; lean_object* v___y_3518_; uint8_t v___y_3519_; lean_object* v___x_3522_; 
lean_inc_ref(v_a_3505_);
v___x_3522_ = l_Lean_Meta_Tactic_Cbv_isBuiltinValue___redArg(v_a_3505_);
if (lean_obj_tag(v___x_3522_) == 0)
{
lean_object* v_a_3523_; 
v_a_3523_ = lean_ctor_get(v___x_3522_, 0);
lean_inc(v_a_3523_);
if (lean_obj_tag(v_a_3523_) == 0)
{
uint8_t v_done_3524_; uint8_t v_contextDependent_3525_; lean_object* v___y_3527_; lean_object* v_a_3528_; lean_object* v___y_3532_; lean_object* v___y_3533_; uint8_t v___y_3534_; lean_object* v___y_3538_; 
v_done_3524_ = lean_ctor_get_uint8(v_a_3523_, 0);
v_contextDependent_3525_ = lean_ctor_get_uint8(v_a_3523_, 1);
lean_dec_ref(v_a_3523_);
if (v_done_3524_ == 0)
{
lean_object* v___x_3540_; 
lean_dec_ref(v___x_3522_);
lean_inc_ref(v_a_3505_);
v___x_3540_ = l_Lean_Meta_Tactic_Cbv_isProofTerm___redArg(v_a_3505_, v_a_3509_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_);
if (lean_obj_tag(v___x_3540_) == 0)
{
lean_object* v_a_3541_; 
v_a_3541_ = lean_ctor_get(v___x_3540_, 0);
lean_inc(v_a_3541_);
if (lean_obj_tag(v_a_3541_) == 0)
{
uint8_t v_done_3542_; uint8_t v_contextDependent_3543_; lean_object* v___y_3545_; lean_object* v_a_3546_; lean_object* v___y_3550_; 
v_done_3542_ = lean_ctor_get_uint8(v_a_3541_, 0);
v_contextDependent_3543_ = lean_ctor_get_uint8(v_a_3541_, 1);
lean_dec_ref(v_a_3541_);
if (v_done_3542_ == 0)
{
lean_object* v_pre_3552_; lean_object* v_erased_3553_; lean_object* v___x_3554_; 
lean_dec_ref(v___x_3540_);
v_pre_3552_ = lean_ctor_get(v_simprocs_3504_, 0);
v_erased_3553_ = lean_ctor_get(v_simprocs_3504_, 4);
lean_inc_ref(v_a_3505_);
v___x_3554_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch(v_pre_3552_, v_erased_3553_, v_a_3505_, v_a_3506_, v_a_3507_, v_a_3508_, v_a_3509_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_);
if (lean_obj_tag(v___x_3554_) == 0)
{
lean_object* v_a_3555_; 
v_a_3555_ = lean_ctor_get(v___x_3554_, 0);
lean_inc(v_a_3555_);
if (lean_obj_tag(v_a_3555_) == 0)
{
uint8_t v_done_3556_; 
v_done_3556_ = lean_ctor_get_uint8(v_a_3555_, 0);
if (v_done_3556_ == 0)
{
uint8_t v_contextDependent_3557_; lean_object* v___x_3558_; 
lean_dec_ref(v___x_3554_);
v_contextDependent_3557_ = lean_ctor_get_uint8(v_a_3555_, 1);
lean_dec_ref(v_a_3555_);
v___x_3558_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep(v_a_3505_, v_a_3506_, v_a_3507_, v_a_3508_, v_a_3509_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_);
if (lean_obj_tag(v___x_3558_) == 0)
{
lean_object* v_a_3559_; uint8_t v___y_3561_; 
v_a_3559_ = lean_ctor_get(v___x_3558_, 0);
lean_inc(v_a_3559_);
if (v_contextDependent_3557_ == 0)
{
lean_dec(v_a_3559_);
v___y_3550_ = v___x_3558_;
goto v___jp_3549_;
}
else
{
if (lean_obj_tag(v_a_3559_) == 0)
{
uint8_t v_contextDependent_3571_; 
v_contextDependent_3571_ = lean_ctor_get_uint8(v_a_3559_, 1);
v___y_3561_ = v_contextDependent_3571_;
goto v___jp_3560_;
}
else
{
uint8_t v_contextDependent_3572_; 
v_contextDependent_3572_ = lean_ctor_get_uint8(v_a_3559_, sizeof(void*)*2 + 1);
v___y_3561_ = v_contextDependent_3572_;
goto v___jp_3560_;
}
}
v___jp_3560_:
{
if (v___y_3561_ == 0)
{
lean_object* v___x_3563_; uint8_t v_isShared_3564_; uint8_t v_isSharedCheck_3569_; 
v_isSharedCheck_3569_ = !lean_is_exclusive(v___x_3558_);
if (v_isSharedCheck_3569_ == 0)
{
lean_object* v_unused_3570_; 
v_unused_3570_ = lean_ctor_get(v___x_3558_, 0);
lean_dec(v_unused_3570_);
v___x_3563_ = v___x_3558_;
v_isShared_3564_ = v_isSharedCheck_3569_;
goto v_resetjp_3562_;
}
else
{
lean_dec(v___x_3558_);
v___x_3563_ = lean_box(0);
v_isShared_3564_ = v_isSharedCheck_3569_;
goto v_resetjp_3562_;
}
v_resetjp_3562_:
{
lean_object* v___x_3565_; lean_object* v___x_3567_; 
v___x_3565_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3559_);
lean_inc_ref(v___x_3565_);
if (v_isShared_3564_ == 0)
{
lean_ctor_set(v___x_3563_, 0, v___x_3565_);
v___x_3567_ = v___x_3563_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v___x_3565_);
v___x_3567_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3566_;
}
v_reusejp_3566_:
{
v___y_3545_ = v___x_3567_;
v_a_3546_ = v___x_3565_;
goto v___jp_3544_;
}
}
}
else
{
lean_dec(v_a_3559_);
v___y_3550_ = v___x_3558_;
goto v___jp_3549_;
}
}
}
else
{
v___y_3550_ = v___x_3558_;
goto v___jp_3549_;
}
}
else
{
lean_dec_ref(v_a_3555_);
lean_dec_ref(v_a_3505_);
v___y_3550_ = v___x_3554_;
goto v___jp_3549_;
}
}
else
{
lean_dec_ref(v_a_3555_);
lean_dec_ref(v_a_3505_);
v___y_3550_ = v___x_3554_;
goto v___jp_3549_;
}
}
else
{
lean_dec_ref(v_a_3505_);
v___y_3550_ = v___x_3554_;
goto v___jp_3549_;
}
}
else
{
lean_dec_ref(v_a_3505_);
v___y_3538_ = v___x_3540_;
goto v___jp_3537_;
}
v___jp_3544_:
{
if (v_contextDependent_3543_ == 0)
{
v___y_3527_ = v___y_3545_;
v_a_3528_ = v_a_3546_;
goto v___jp_3526_;
}
else
{
if (lean_obj_tag(v_a_3546_) == 0)
{
uint8_t v_contextDependent_3547_; 
v_contextDependent_3547_ = lean_ctor_get_uint8(v_a_3546_, 1);
v___y_3532_ = v_a_3546_;
v___y_3533_ = v___y_3545_;
v___y_3534_ = v_contextDependent_3547_;
goto v___jp_3531_;
}
else
{
uint8_t v_contextDependent_3548_; 
v_contextDependent_3548_ = lean_ctor_get_uint8(v_a_3546_, sizeof(void*)*2 + 1);
v___y_3532_ = v_a_3546_;
v___y_3533_ = v___y_3545_;
v___y_3534_ = v_contextDependent_3548_;
goto v___jp_3531_;
}
}
}
v___jp_3549_:
{
if (lean_obj_tag(v___y_3550_) == 0)
{
lean_object* v_a_3551_; 
v_a_3551_ = lean_ctor_get(v___y_3550_, 0);
lean_inc(v_a_3551_);
v___y_3545_ = v___y_3550_;
v_a_3546_ = v_a_3551_;
goto v___jp_3544_;
}
else
{
return v___y_3550_;
}
}
}
else
{
lean_dec_ref(v_a_3541_);
lean_dec_ref(v_a_3505_);
v___y_3538_ = v___x_3540_;
goto v___jp_3537_;
}
}
else
{
lean_dec_ref(v_a_3505_);
v___y_3538_ = v___x_3540_;
goto v___jp_3537_;
}
}
else
{
lean_dec_ref(v_a_3505_);
return v___x_3522_;
}
v___jp_3526_:
{
if (v_contextDependent_3525_ == 0)
{
lean_dec_ref(v_a_3528_);
return v___y_3527_;
}
else
{
if (lean_obj_tag(v_a_3528_) == 0)
{
uint8_t v_contextDependent_3529_; 
v_contextDependent_3529_ = lean_ctor_get_uint8(v_a_3528_, 1);
v___y_3517_ = v___y_3527_;
v___y_3518_ = v_a_3528_;
v___y_3519_ = v_contextDependent_3529_;
goto v___jp_3516_;
}
else
{
uint8_t v_contextDependent_3530_; 
v_contextDependent_3530_ = lean_ctor_get_uint8(v_a_3528_, sizeof(void*)*2 + 1);
v___y_3517_ = v___y_3527_;
v___y_3518_ = v_a_3528_;
v___y_3519_ = v_contextDependent_3530_;
goto v___jp_3516_;
}
}
}
v___jp_3531_:
{
if (v___y_3534_ == 0)
{
lean_object* v___x_3535_; lean_object* v___x_3536_; 
lean_dec_ref(v___y_3533_);
v___x_3535_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_3532_);
lean_inc_ref(v___x_3535_);
v___x_3536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3536_, 0, v___x_3535_);
v___y_3527_ = v___x_3536_;
v_a_3528_ = v___x_3535_;
goto v___jp_3526_;
}
else
{
v___y_3527_ = v___y_3533_;
v_a_3528_ = v___y_3532_;
goto v___jp_3526_;
}
}
v___jp_3537_:
{
if (lean_obj_tag(v___y_3538_) == 0)
{
lean_object* v_a_3539_; 
v_a_3539_ = lean_ctor_get(v___y_3538_, 0);
lean_inc(v_a_3539_);
v___y_3527_ = v___y_3538_;
v_a_3528_ = v_a_3539_;
goto v___jp_3526_;
}
else
{
return v___y_3538_;
}
}
}
else
{
lean_dec_ref(v_a_3523_);
lean_dec_ref(v_a_3505_);
return v___x_3522_;
}
}
else
{
lean_dec_ref(v_a_3505_);
return v___x_3522_;
}
v___jp_3516_:
{
if (v___y_3519_ == 0)
{
lean_object* v___x_3520_; lean_object* v___x_3521_; 
lean_dec_ref(v___y_3517_);
v___x_3520_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_3518_);
v___x_3521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3521_, 0, v___x_3520_);
return v___x_3521_;
}
else
{
lean_dec_ref(v___y_3518_);
return v___y_3517_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPre___boxed(lean_object* v_simprocs_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_, lean_object* v_a_3583_, lean_object* v_a_3584_){
_start:
{
lean_object* v_res_3585_; 
v_res_3585_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPre(v_simprocs_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_);
lean_dec(v_a_3583_);
lean_dec_ref(v_a_3582_);
lean_dec(v_a_3581_);
lean_dec_ref(v_a_3580_);
lean_dec(v_a_3579_);
lean_dec_ref(v_a_3578_);
lean_dec(v_a_3577_);
lean_dec_ref(v_a_3576_);
lean_dec(v_a_3575_);
lean_dec_ref(v_simprocs_3573_);
return v_res_3585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPost(lean_object* v_simprocs_3586_, lean_object* v_a_3587_, lean_object* v_a_3588_, lean_object* v_a_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_, lean_object* v_a_3596_){
_start:
{
lean_object* v___y_3599_; lean_object* v___y_3600_; uint8_t v___y_3601_; lean_object* v___x_3604_; lean_object* v___x_3605_; 
v___x_3604_ = lean_unsigned_to_nat(255u);
lean_inc_ref(v_a_3587_);
v___x_3605_ = l_Lean_Meta_Sym_Simp_evalGround___redArg(v___x_3604_, v_a_3587_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_);
if (lean_obj_tag(v___x_3605_) == 0)
{
lean_object* v_a_3606_; 
v_a_3606_ = lean_ctor_get(v___x_3605_, 0);
lean_inc(v_a_3606_);
if (lean_obj_tag(v_a_3606_) == 0)
{
uint8_t v_done_3607_; uint8_t v_contextDependent_3608_; lean_object* v___y_3610_; lean_object* v_a_3611_; lean_object* v___y_3615_; lean_object* v___y_3616_; uint8_t v___y_3617_; lean_object* v___y_3621_; 
v_done_3607_ = lean_ctor_get_uint8(v_a_3606_, 0);
v_contextDependent_3608_ = lean_ctor_get_uint8(v_a_3606_, 1);
lean_dec_ref(v_a_3606_);
if (v_done_3607_ == 0)
{
lean_object* v_eval_3623_; lean_object* v_post_3624_; lean_object* v_erased_3625_; lean_object* v___x_3626_; 
lean_dec_ref(v___x_3605_);
v_eval_3623_ = lean_ctor_get(v_simprocs_3586_, 1);
v_post_3624_ = lean_ctor_get(v_simprocs_3586_, 2);
v_erased_3625_ = lean_ctor_get(v_simprocs_3586_, 4);
lean_inc_ref(v_a_3587_);
v___x_3626_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch(v_eval_3623_, v_erased_3625_, v_a_3587_, v_a_3588_, v_a_3589_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_);
if (lean_obj_tag(v___x_3626_) == 0)
{
lean_object* v_a_3627_; 
v_a_3627_ = lean_ctor_get(v___x_3626_, 0);
lean_inc(v_a_3627_);
if (lean_obj_tag(v_a_3627_) == 0)
{
uint8_t v_done_3628_; uint8_t v_contextDependent_3629_; lean_object* v___y_3631_; lean_object* v_a_3632_; lean_object* v___y_3636_; 
v_done_3628_ = lean_ctor_get_uint8(v_a_3627_, 0);
v_contextDependent_3629_ = lean_ctor_get_uint8(v_a_3627_, 1);
lean_dec_ref(v_a_3627_);
if (v_done_3628_ == 0)
{
lean_object* v___x_3638_; 
lean_dec_ref(v___x_3626_);
lean_inc_ref(v_a_3587_);
v___x_3638_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp(v_a_3587_, v_a_3588_, v_a_3589_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_);
if (lean_obj_tag(v___x_3638_) == 0)
{
lean_object* v_a_3639_; 
v_a_3639_ = lean_ctor_get(v___x_3638_, 0);
lean_inc(v_a_3639_);
if (lean_obj_tag(v_a_3639_) == 0)
{
uint8_t v_done_3640_; 
v_done_3640_ = lean_ctor_get_uint8(v_a_3639_, 0);
if (v_done_3640_ == 0)
{
uint8_t v_contextDependent_3641_; lean_object* v___x_3642_; 
lean_dec_ref(v___x_3638_);
v_contextDependent_3641_ = lean_ctor_get_uint8(v_a_3639_, 1);
lean_dec_ref(v_a_3639_);
v___x_3642_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch(v_post_3624_, v_erased_3625_, v_a_3587_, v_a_3588_, v_a_3589_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_);
if (lean_obj_tag(v___x_3642_) == 0)
{
lean_object* v_a_3643_; uint8_t v___y_3645_; 
v_a_3643_ = lean_ctor_get(v___x_3642_, 0);
lean_inc(v_a_3643_);
if (v_contextDependent_3641_ == 0)
{
lean_dec(v_a_3643_);
v___y_3636_ = v___x_3642_;
goto v___jp_3635_;
}
else
{
if (lean_obj_tag(v_a_3643_) == 0)
{
uint8_t v_contextDependent_3655_; 
v_contextDependent_3655_ = lean_ctor_get_uint8(v_a_3643_, 1);
v___y_3645_ = v_contextDependent_3655_;
goto v___jp_3644_;
}
else
{
uint8_t v_contextDependent_3656_; 
v_contextDependent_3656_ = lean_ctor_get_uint8(v_a_3643_, sizeof(void*)*2 + 1);
v___y_3645_ = v_contextDependent_3656_;
goto v___jp_3644_;
}
}
v___jp_3644_:
{
if (v___y_3645_ == 0)
{
lean_object* v___x_3647_; uint8_t v_isShared_3648_; uint8_t v_isSharedCheck_3653_; 
v_isSharedCheck_3653_ = !lean_is_exclusive(v___x_3642_);
if (v_isSharedCheck_3653_ == 0)
{
lean_object* v_unused_3654_; 
v_unused_3654_ = lean_ctor_get(v___x_3642_, 0);
lean_dec(v_unused_3654_);
v___x_3647_ = v___x_3642_;
v_isShared_3648_ = v_isSharedCheck_3653_;
goto v_resetjp_3646_;
}
else
{
lean_dec(v___x_3642_);
v___x_3647_ = lean_box(0);
v_isShared_3648_ = v_isSharedCheck_3653_;
goto v_resetjp_3646_;
}
v_resetjp_3646_:
{
lean_object* v___x_3649_; lean_object* v___x_3651_; 
v___x_3649_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3643_);
lean_inc_ref(v___x_3649_);
if (v_isShared_3648_ == 0)
{
lean_ctor_set(v___x_3647_, 0, v___x_3649_);
v___x_3651_ = v___x_3647_;
goto v_reusejp_3650_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v___x_3649_);
v___x_3651_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3650_;
}
v_reusejp_3650_:
{
v___y_3631_ = v___x_3651_;
v_a_3632_ = v___x_3649_;
goto v___jp_3630_;
}
}
}
else
{
lean_dec(v_a_3643_);
v___y_3636_ = v___x_3642_;
goto v___jp_3635_;
}
}
}
else
{
v___y_3636_ = v___x_3642_;
goto v___jp_3635_;
}
}
else
{
lean_dec_ref(v_a_3639_);
lean_dec_ref(v_a_3587_);
v___y_3636_ = v___x_3638_;
goto v___jp_3635_;
}
}
else
{
lean_dec_ref(v_a_3639_);
lean_dec_ref(v_a_3587_);
v___y_3636_ = v___x_3638_;
goto v___jp_3635_;
}
}
else
{
lean_dec_ref(v_a_3587_);
v___y_3636_ = v___x_3638_;
goto v___jp_3635_;
}
}
else
{
lean_dec_ref(v_a_3587_);
v___y_3621_ = v___x_3626_;
goto v___jp_3620_;
}
v___jp_3630_:
{
if (v_contextDependent_3629_ == 0)
{
v___y_3610_ = v___y_3631_;
v_a_3611_ = v_a_3632_;
goto v___jp_3609_;
}
else
{
if (lean_obj_tag(v_a_3632_) == 0)
{
uint8_t v_contextDependent_3633_; 
v_contextDependent_3633_ = lean_ctor_get_uint8(v_a_3632_, 1);
v___y_3615_ = v_a_3632_;
v___y_3616_ = v___y_3631_;
v___y_3617_ = v_contextDependent_3633_;
goto v___jp_3614_;
}
else
{
uint8_t v_contextDependent_3634_; 
v_contextDependent_3634_ = lean_ctor_get_uint8(v_a_3632_, sizeof(void*)*2 + 1);
v___y_3615_ = v_a_3632_;
v___y_3616_ = v___y_3631_;
v___y_3617_ = v_contextDependent_3634_;
goto v___jp_3614_;
}
}
}
v___jp_3635_:
{
if (lean_obj_tag(v___y_3636_) == 0)
{
lean_object* v_a_3637_; 
v_a_3637_ = lean_ctor_get(v___y_3636_, 0);
lean_inc(v_a_3637_);
v___y_3631_ = v___y_3636_;
v_a_3632_ = v_a_3637_;
goto v___jp_3630_;
}
else
{
return v___y_3636_;
}
}
}
else
{
lean_dec_ref(v_a_3627_);
lean_dec_ref(v_a_3587_);
v___y_3621_ = v___x_3626_;
goto v___jp_3620_;
}
}
else
{
lean_dec_ref(v_a_3587_);
v___y_3621_ = v___x_3626_;
goto v___jp_3620_;
}
}
else
{
lean_dec_ref(v_a_3587_);
return v___x_3605_;
}
v___jp_3609_:
{
if (v_contextDependent_3608_ == 0)
{
lean_dec_ref(v_a_3611_);
return v___y_3610_;
}
else
{
if (lean_obj_tag(v_a_3611_) == 0)
{
uint8_t v_contextDependent_3612_; 
v_contextDependent_3612_ = lean_ctor_get_uint8(v_a_3611_, 1);
v___y_3599_ = v___y_3610_;
v___y_3600_ = v_a_3611_;
v___y_3601_ = v_contextDependent_3612_;
goto v___jp_3598_;
}
else
{
uint8_t v_contextDependent_3613_; 
v_contextDependent_3613_ = lean_ctor_get_uint8(v_a_3611_, sizeof(void*)*2 + 1);
v___y_3599_ = v___y_3610_;
v___y_3600_ = v_a_3611_;
v___y_3601_ = v_contextDependent_3613_;
goto v___jp_3598_;
}
}
}
v___jp_3614_:
{
if (v___y_3617_ == 0)
{
lean_object* v___x_3618_; lean_object* v___x_3619_; 
lean_dec_ref(v___y_3616_);
v___x_3618_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_3615_);
lean_inc_ref(v___x_3618_);
v___x_3619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3619_, 0, v___x_3618_);
v___y_3610_ = v___x_3619_;
v_a_3611_ = v___x_3618_;
goto v___jp_3609_;
}
else
{
v___y_3610_ = v___y_3616_;
v_a_3611_ = v___y_3615_;
goto v___jp_3609_;
}
}
v___jp_3620_:
{
if (lean_obj_tag(v___y_3621_) == 0)
{
lean_object* v_a_3622_; 
v_a_3622_ = lean_ctor_get(v___y_3621_, 0);
lean_inc(v_a_3622_);
v___y_3610_ = v___y_3621_;
v_a_3611_ = v_a_3622_;
goto v___jp_3609_;
}
else
{
return v___y_3621_;
}
}
}
else
{
lean_dec_ref(v_a_3606_);
lean_dec_ref(v_a_3587_);
return v___x_3605_;
}
}
else
{
lean_dec_ref(v_a_3587_);
return v___x_3605_;
}
v___jp_3598_:
{
if (v___y_3601_ == 0)
{
lean_object* v___x_3602_; lean_object* v___x_3603_; 
lean_dec_ref(v___y_3599_);
v___x_3602_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_3600_);
v___x_3603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3603_, 0, v___x_3602_);
return v___x_3603_;
}
else
{
lean_dec_ref(v___y_3600_);
return v___y_3599_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPost___boxed(lean_object* v_simprocs_3657_, lean_object* v_a_3658_, lean_object* v_a_3659_, lean_object* v_a_3660_, lean_object* v_a_3661_, lean_object* v_a_3662_, lean_object* v_a_3663_, lean_object* v_a_3664_, lean_object* v_a_3665_, lean_object* v_a_3666_, lean_object* v_a_3667_, lean_object* v_a_3668_){
_start:
{
lean_object* v_res_3669_; 
v_res_3669_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPost(v_simprocs_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_);
lean_dec(v_a_3667_);
lean_dec_ref(v_a_3666_);
lean_dec(v_a_3665_);
lean_dec_ref(v_a_3664_);
lean_dec(v_a_3663_);
lean_dec_ref(v_a_3662_);
lean_dec(v_a_3661_);
lean_dec_ref(v_a_3660_);
lean_dec(v_a_3659_);
lean_dec_ref(v_simprocs_3657_);
return v_res_3669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(lean_object* v_simprocs_3670_){
_start:
{
lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; 
lean_inc_ref(v_simprocs_3670_);
v___x_3671_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPre___boxed), 12, 1);
lean_closure_set(v___x_3671_, 0, v_simprocs_3670_);
v___x_3672_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPost___boxed), 12, 1);
lean_closure_set(v___x_3672_, 0, v_simprocs_3670_);
v___x_3673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3673_, 0, v___x_3671_);
lean_ctor_set(v___x_3673_, 1, v___x_3672_);
return v___x_3673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(lean_object* v_e_3674_, lean_object* v_config_3675_, lean_object* v_a_3676_, lean_object* v_a_3677_, lean_object* v_a_3678_, lean_object* v_a_3679_, lean_object* v_a_3680_, lean_object* v_a_3681_){
_start:
{
lean_object* v___x_3683_; 
v___x_3683_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_3681_);
if (lean_obj_tag(v___x_3683_) == 0)
{
lean_object* v_a_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; 
v_a_3684_ = lean_ctor_get(v___x_3683_, 0);
lean_inc(v_a_3684_);
lean_dec_ref(v___x_3683_);
v___x_3685_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(v_a_3684_);
v___x_3686_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_3686_, 0, v_e_3674_);
v___x_3687_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v___x_3686_, v___x_3685_, v_config_3675_, v_a_3676_, v_a_3677_, v_a_3678_, v_a_3679_, v_a_3680_, v_a_3681_);
return v___x_3687_;
}
else
{
lean_object* v_a_3688_; lean_object* v___x_3690_; uint8_t v_isShared_3691_; uint8_t v_isSharedCheck_3695_; 
lean_dec_ref(v_config_3675_);
lean_dec_ref(v_e_3674_);
v_a_3688_ = lean_ctor_get(v___x_3683_, 0);
v_isSharedCheck_3695_ = !lean_is_exclusive(v___x_3683_);
if (v_isSharedCheck_3695_ == 0)
{
v___x_3690_ = v___x_3683_;
v_isShared_3691_ = v_isSharedCheck_3695_;
goto v_resetjp_3689_;
}
else
{
lean_inc(v_a_3688_);
lean_dec(v___x_3683_);
v___x_3690_ = lean_box(0);
v_isShared_3691_ = v_isSharedCheck_3695_;
goto v_resetjp_3689_;
}
v_resetjp_3689_:
{
lean_object* v___x_3693_; 
if (v_isShared_3691_ == 0)
{
v___x_3693_ = v___x_3690_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3694_; 
v_reuseFailAlloc_3694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3694_, 0, v_a_3688_);
v___x_3693_ = v_reuseFailAlloc_3694_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
return v___x_3693_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore___boxed(lean_object* v_e_3696_, lean_object* v_config_3697_, lean_object* v_a_3698_, lean_object* v_a_3699_, lean_object* v_a_3700_, lean_object* v_a_3701_, lean_object* v_a_3702_, lean_object* v_a_3703_, lean_object* v_a_3704_){
_start:
{
lean_object* v_res_3705_; 
v_res_3705_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v_e_3696_, v_config_3697_, v_a_3698_, v_a_3699_, v_a_3700_, v_a_3701_, v_a_3702_, v_a_3703_);
lean_dec(v_a_3703_);
lean_dec_ref(v_a_3702_);
lean_dec(v_a_3701_);
lean_dec_ref(v_a_3700_);
lean_dec(v_a_3699_);
lean_dec_ref(v_a_3698_);
return v_res_3705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg(lean_object* v___y_3706_){
_start:
{
lean_object* v___x_3708_; lean_object* v_traceState_3709_; lean_object* v_traces_3710_; lean_object* v___x_3711_; lean_object* v_traceState_3712_; lean_object* v_env_3713_; lean_object* v_nextMacroScope_3714_; lean_object* v_ngen_3715_; lean_object* v_auxDeclNGen_3716_; lean_object* v_cache_3717_; lean_object* v_messages_3718_; lean_object* v_infoState_3719_; lean_object* v_snapshotTasks_3720_; lean_object* v_newDecls_3721_; lean_object* v___x_3723_; uint8_t v_isShared_3724_; uint8_t v_isSharedCheck_3742_; 
v___x_3708_ = lean_st_ref_get(v___y_3706_);
v_traceState_3709_ = lean_ctor_get(v___x_3708_, 4);
lean_inc_ref(v_traceState_3709_);
lean_dec(v___x_3708_);
v_traces_3710_ = lean_ctor_get(v_traceState_3709_, 0);
lean_inc_ref(v_traces_3710_);
lean_dec_ref(v_traceState_3709_);
v___x_3711_ = lean_st_ref_take(v___y_3706_);
v_traceState_3712_ = lean_ctor_get(v___x_3711_, 4);
v_env_3713_ = lean_ctor_get(v___x_3711_, 0);
v_nextMacroScope_3714_ = lean_ctor_get(v___x_3711_, 1);
v_ngen_3715_ = lean_ctor_get(v___x_3711_, 2);
v_auxDeclNGen_3716_ = lean_ctor_get(v___x_3711_, 3);
v_cache_3717_ = lean_ctor_get(v___x_3711_, 5);
v_messages_3718_ = lean_ctor_get(v___x_3711_, 6);
v_infoState_3719_ = lean_ctor_get(v___x_3711_, 7);
v_snapshotTasks_3720_ = lean_ctor_get(v___x_3711_, 8);
v_newDecls_3721_ = lean_ctor_get(v___x_3711_, 9);
v_isSharedCheck_3742_ = !lean_is_exclusive(v___x_3711_);
if (v_isSharedCheck_3742_ == 0)
{
v___x_3723_ = v___x_3711_;
v_isShared_3724_ = v_isSharedCheck_3742_;
goto v_resetjp_3722_;
}
else
{
lean_inc(v_newDecls_3721_);
lean_inc(v_snapshotTasks_3720_);
lean_inc(v_infoState_3719_);
lean_inc(v_messages_3718_);
lean_inc(v_cache_3717_);
lean_inc(v_traceState_3712_);
lean_inc(v_auxDeclNGen_3716_);
lean_inc(v_ngen_3715_);
lean_inc(v_nextMacroScope_3714_);
lean_inc(v_env_3713_);
lean_dec(v___x_3711_);
v___x_3723_ = lean_box(0);
v_isShared_3724_ = v_isSharedCheck_3742_;
goto v_resetjp_3722_;
}
v_resetjp_3722_:
{
uint64_t v_tid_3725_; lean_object* v___x_3727_; uint8_t v_isShared_3728_; uint8_t v_isSharedCheck_3740_; 
v_tid_3725_ = lean_ctor_get_uint64(v_traceState_3712_, sizeof(void*)*1);
v_isSharedCheck_3740_ = !lean_is_exclusive(v_traceState_3712_);
if (v_isSharedCheck_3740_ == 0)
{
lean_object* v_unused_3741_; 
v_unused_3741_ = lean_ctor_get(v_traceState_3712_, 0);
lean_dec(v_unused_3741_);
v___x_3727_ = v_traceState_3712_;
v_isShared_3728_ = v_isSharedCheck_3740_;
goto v_resetjp_3726_;
}
else
{
lean_dec(v_traceState_3712_);
v___x_3727_ = lean_box(0);
v_isShared_3728_ = v_isSharedCheck_3740_;
goto v_resetjp_3726_;
}
v_resetjp_3726_:
{
lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3733_; 
v___x_3729_ = lean_unsigned_to_nat(32u);
v___x_3730_ = lean_mk_empty_array_with_capacity(v___x_3729_);
lean_dec_ref(v___x_3730_);
v___x_3731_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1);
if (v_isShared_3728_ == 0)
{
lean_ctor_set(v___x_3727_, 0, v___x_3731_);
v___x_3733_ = v___x_3727_;
goto v_reusejp_3732_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v___x_3731_);
lean_ctor_set_uint64(v_reuseFailAlloc_3739_, sizeof(void*)*1, v_tid_3725_);
v___x_3733_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3732_;
}
v_reusejp_3732_:
{
lean_object* v___x_3735_; 
if (v_isShared_3724_ == 0)
{
lean_ctor_set(v___x_3723_, 4, v___x_3733_);
v___x_3735_ = v___x_3723_;
goto v_reusejp_3734_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v_env_3713_);
lean_ctor_set(v_reuseFailAlloc_3738_, 1, v_nextMacroScope_3714_);
lean_ctor_set(v_reuseFailAlloc_3738_, 2, v_ngen_3715_);
lean_ctor_set(v_reuseFailAlloc_3738_, 3, v_auxDeclNGen_3716_);
lean_ctor_set(v_reuseFailAlloc_3738_, 4, v___x_3733_);
lean_ctor_set(v_reuseFailAlloc_3738_, 5, v_cache_3717_);
lean_ctor_set(v_reuseFailAlloc_3738_, 6, v_messages_3718_);
lean_ctor_set(v_reuseFailAlloc_3738_, 7, v_infoState_3719_);
lean_ctor_set(v_reuseFailAlloc_3738_, 8, v_snapshotTasks_3720_);
lean_ctor_set(v_reuseFailAlloc_3738_, 9, v_newDecls_3721_);
v___x_3735_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3734_;
}
v_reusejp_3734_:
{
lean_object* v___x_3736_; lean_object* v___x_3737_; 
v___x_3736_ = lean_st_ref_set(v___y_3706_, v___x_3735_);
v___x_3737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3737_, 0, v_traces_3710_);
return v___x_3737_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg___boxed(lean_object* v___y_3743_, lean_object* v___y_3744_){
_start:
{
lean_object* v_res_3745_; 
v_res_3745_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg(v___y_3743_);
lean_dec(v___y_3743_);
return v_res_3745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0(lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_){
_start:
{
lean_object* v___x_3751_; 
v___x_3751_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg(v___y_3749_);
return v___x_3751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___boxed(lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_){
_start:
{
lean_object* v_res_3757_; 
v_res_3757_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0(v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_);
lean_dec(v___y_3755_);
lean_dec_ref(v___y_3754_);
lean_dec(v___y_3753_);
lean_dec_ref(v___y_3752_);
return v_res_3757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0(lean_object* v_a_3758_, lean_object* v___x_3759_, lean_object* v___x_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_){
_start:
{
lean_object* v___x_3768_; 
v___x_3768_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_3758_, v___y_3762_);
if (lean_obj_tag(v___x_3768_) == 0)
{
lean_object* v_a_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; 
v_a_3769_ = lean_ctor_get(v___x_3768_, 0);
lean_inc(v_a_3769_);
lean_dec_ref(v___x_3768_);
v___x_3770_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_3770_, 0, v_a_3769_);
v___x_3771_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v___x_3770_, v___x_3759_, v___x_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_);
return v___x_3771_;
}
else
{
lean_object* v_a_3772_; lean_object* v___x_3774_; uint8_t v_isShared_3775_; uint8_t v_isSharedCheck_3779_; 
lean_dec_ref(v___x_3760_);
lean_dec_ref(v___x_3759_);
v_a_3772_ = lean_ctor_get(v___x_3768_, 0);
v_isSharedCheck_3779_ = !lean_is_exclusive(v___x_3768_);
if (v_isSharedCheck_3779_ == 0)
{
v___x_3774_ = v___x_3768_;
v_isShared_3775_ = v_isSharedCheck_3779_;
goto v_resetjp_3773_;
}
else
{
lean_inc(v_a_3772_);
lean_dec(v___x_3768_);
v___x_3774_ = lean_box(0);
v_isShared_3775_ = v_isSharedCheck_3779_;
goto v_resetjp_3773_;
}
v_resetjp_3773_:
{
lean_object* v___x_3777_; 
if (v_isShared_3775_ == 0)
{
v___x_3777_ = v___x_3774_;
goto v_reusejp_3776_;
}
else
{
lean_object* v_reuseFailAlloc_3778_; 
v_reuseFailAlloc_3778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3778_, 0, v_a_3772_);
v___x_3777_ = v_reuseFailAlloc_3778_;
goto v_reusejp_3776_;
}
v_reusejp_3776_:
{
return v___x_3777_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___boxed(lean_object* v_a_3780_, lean_object* v___x_3781_, lean_object* v___x_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_){
_start:
{
lean_object* v_res_3790_; 
v_res_3790_ = l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0(v_a_3780_, v___x_3781_, v___x_3782_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_);
lean_dec(v___y_3788_);
lean_dec_ref(v___y_3787_);
lean_dec(v___y_3786_);
lean_dec_ref(v___y_3785_);
lean_dec(v___y_3784_);
lean_dec_ref(v___y_3783_);
return v_res_3790_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3792_; lean_object* v___x_3793_; 
v___x_3792_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__0));
v___x_3793_ = l_Lean_stringToMessageData(v___x_3792_);
return v___x_3793_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3795_; lean_object* v___x_3796_; 
v___x_3795_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__2));
v___x_3796_ = l_Lean_stringToMessageData(v___x_3795_);
return v___x_3796_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__5(void){
_start:
{
lean_object* v___x_3798_; lean_object* v___x_3799_; 
v___x_3798_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__4));
v___x_3799_ = l_Lean_stringToMessageData(v___x_3798_);
return v___x_3799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1(lean_object* v_e_3800_, lean_object* v_x_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_){
_start:
{
if (lean_obj_tag(v_x_3801_) == 0)
{
lean_object* v_a_3807_; lean_object* v___x_3809_; uint8_t v_isShared_3810_; uint8_t v_isSharedCheck_3817_; 
lean_dec_ref(v_e_3800_);
v_a_3807_ = lean_ctor_get(v_x_3801_, 0);
v_isSharedCheck_3817_ = !lean_is_exclusive(v_x_3801_);
if (v_isSharedCheck_3817_ == 0)
{
v___x_3809_ = v_x_3801_;
v_isShared_3810_ = v_isSharedCheck_3817_;
goto v_resetjp_3808_;
}
else
{
lean_inc(v_a_3807_);
lean_dec(v_x_3801_);
v___x_3809_ = lean_box(0);
v_isShared_3810_ = v_isSharedCheck_3817_;
goto v_resetjp_3808_;
}
v_resetjp_3808_:
{
lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3815_; 
v___x_3811_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__1);
v___x_3812_ = l_Lean_Exception_toMessageData(v_a_3807_);
v___x_3813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3813_, 0, v___x_3811_);
lean_ctor_set(v___x_3813_, 1, v___x_3812_);
if (v_isShared_3810_ == 0)
{
lean_ctor_set(v___x_3809_, 0, v___x_3813_);
v___x_3815_ = v___x_3809_;
goto v_reusejp_3814_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v___x_3813_);
v___x_3815_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3814_;
}
v_reusejp_3814_:
{
return v___x_3815_;
}
}
}
else
{
lean_object* v_a_3818_; lean_object* v___x_3820_; uint8_t v_isShared_3821_; uint8_t v_isSharedCheck_3839_; 
v_a_3818_ = lean_ctor_get(v_x_3801_, 0);
v_isSharedCheck_3839_ = !lean_is_exclusive(v_x_3801_);
if (v_isSharedCheck_3839_ == 0)
{
v___x_3820_ = v_x_3801_;
v_isShared_3821_ = v_isSharedCheck_3839_;
goto v_resetjp_3819_;
}
else
{
lean_inc(v_a_3818_);
lean_dec(v_x_3801_);
v___x_3820_ = lean_box(0);
v_isShared_3821_ = v_isSharedCheck_3839_;
goto v_resetjp_3819_;
}
v_resetjp_3819_:
{
if (lean_obj_tag(v_a_3818_) == 0)
{
lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3826_; 
lean_dec_ref(v_a_3818_);
v___x_3822_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__3, &l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__3);
v___x_3823_ = l_Lean_indentExpr(v_e_3800_);
v___x_3824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3824_, 0, v___x_3822_);
lean_ctor_set(v___x_3824_, 1, v___x_3823_);
if (v_isShared_3821_ == 0)
{
lean_ctor_set_tag(v___x_3820_, 0);
lean_ctor_set(v___x_3820_, 0, v___x_3824_);
v___x_3826_ = v___x_3820_;
goto v_reusejp_3825_;
}
else
{
lean_object* v_reuseFailAlloc_3827_; 
v_reuseFailAlloc_3827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3827_, 0, v___x_3824_);
v___x_3826_ = v_reuseFailAlloc_3827_;
goto v_reusejp_3825_;
}
v_reusejp_3825_:
{
return v___x_3826_;
}
}
else
{
lean_object* v_e_x27_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3837_; 
v_e_x27_3828_ = lean_ctor_get(v_a_3818_, 0);
lean_inc_ref(v_e_x27_3828_);
lean_dec_ref(v_a_3818_);
v___x_3829_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__5, &l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__5_once, _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__5);
v___x_3830_ = l_Lean_indentExpr(v_e_3800_);
v___x_3831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3831_, 0, v___x_3829_);
lean_ctor_set(v___x_3831_, 1, v___x_3830_);
v___x_3832_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_3833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3833_, 0, v___x_3831_);
lean_ctor_set(v___x_3833_, 1, v___x_3832_);
v___x_3834_ = l_Lean_indentExpr(v_e_x27_3828_);
v___x_3835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3835_, 0, v___x_3833_);
lean_ctor_set(v___x_3835_, 1, v___x_3834_);
if (v_isShared_3821_ == 0)
{
lean_ctor_set_tag(v___x_3820_, 0);
lean_ctor_set(v___x_3820_, 0, v___x_3835_);
v___x_3837_ = v___x_3820_;
goto v_reusejp_3836_;
}
else
{
lean_object* v_reuseFailAlloc_3838_; 
v_reuseFailAlloc_3838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3838_, 0, v___x_3835_);
v___x_3837_ = v_reuseFailAlloc_3838_;
goto v_reusejp_3836_;
}
v_reusejp_3836_:
{
return v___x_3837_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___boxed(lean_object* v_e_3840_, lean_object* v_x_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_){
_start:
{
lean_object* v_res_3847_; 
v_res_3847_ = l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1(v_e_3840_, v_x_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_);
lean_dec(v___y_3845_);
lean_dec_ref(v___y_3844_);
lean_dec(v___y_3843_);
lean_dec_ref(v___y_3842_);
return v_res_3847_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg(lean_object* v_x_3848_){
_start:
{
if (lean_obj_tag(v_x_3848_) == 0)
{
lean_object* v_a_3850_; lean_object* v___x_3852_; uint8_t v_isShared_3853_; uint8_t v_isSharedCheck_3857_; 
v_a_3850_ = lean_ctor_get(v_x_3848_, 0);
v_isSharedCheck_3857_ = !lean_is_exclusive(v_x_3848_);
if (v_isSharedCheck_3857_ == 0)
{
v___x_3852_ = v_x_3848_;
v_isShared_3853_ = v_isSharedCheck_3857_;
goto v_resetjp_3851_;
}
else
{
lean_inc(v_a_3850_);
lean_dec(v_x_3848_);
v___x_3852_ = lean_box(0);
v_isShared_3853_ = v_isSharedCheck_3857_;
goto v_resetjp_3851_;
}
v_resetjp_3851_:
{
lean_object* v___x_3855_; 
if (v_isShared_3853_ == 0)
{
lean_ctor_set_tag(v___x_3852_, 1);
v___x_3855_ = v___x_3852_;
goto v_reusejp_3854_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v_a_3850_);
v___x_3855_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3854_;
}
v_reusejp_3854_:
{
return v___x_3855_;
}
}
}
else
{
lean_object* v_a_3858_; lean_object* v___x_3860_; uint8_t v_isShared_3861_; uint8_t v_isSharedCheck_3865_; 
v_a_3858_ = lean_ctor_get(v_x_3848_, 0);
v_isSharedCheck_3865_ = !lean_is_exclusive(v_x_3848_);
if (v_isSharedCheck_3865_ == 0)
{
v___x_3860_ = v_x_3848_;
v_isShared_3861_ = v_isSharedCheck_3865_;
goto v_resetjp_3859_;
}
else
{
lean_inc(v_a_3858_);
lean_dec(v_x_3848_);
v___x_3860_ = lean_box(0);
v_isShared_3861_ = v_isSharedCheck_3865_;
goto v_resetjp_3859_;
}
v_resetjp_3859_:
{
lean_object* v___x_3863_; 
if (v_isShared_3861_ == 0)
{
lean_ctor_set_tag(v___x_3860_, 0);
v___x_3863_ = v___x_3860_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3864_; 
v_reuseFailAlloc_3864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3864_, 0, v_a_3858_);
v___x_3863_ = v_reuseFailAlloc_3864_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
return v___x_3863_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg___boxed(lean_object* v_x_3866_, lean_object* v___y_3867_){
_start:
{
lean_object* v_res_3868_; 
v_res_3868_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg(v_x_3866_);
return v_res_3868_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__1(lean_object* v_oldTraces_3869_, lean_object* v_data_3870_, lean_object* v_ref_3871_, lean_object* v_msg_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_){
_start:
{
lean_object* v_fileName_3878_; lean_object* v_fileMap_3879_; lean_object* v_options_3880_; lean_object* v_currRecDepth_3881_; lean_object* v_maxRecDepth_3882_; lean_object* v_ref_3883_; lean_object* v_currNamespace_3884_; lean_object* v_openDecls_3885_; lean_object* v_initHeartbeats_3886_; lean_object* v_maxHeartbeats_3887_; lean_object* v_quotContext_3888_; lean_object* v_currMacroScope_3889_; uint8_t v_diag_3890_; lean_object* v_cancelTk_x3f_3891_; uint8_t v_suppressElabErrors_3892_; lean_object* v_inheritedTraceOptions_3893_; lean_object* v___x_3894_; lean_object* v_traceState_3895_; lean_object* v_traces_3896_; lean_object* v_ref_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; size_t v_sz_3900_; size_t v___x_3901_; lean_object* v___x_3902_; lean_object* v_msg_3903_; lean_object* v___x_3904_; lean_object* v_a_3905_; lean_object* v___x_3907_; uint8_t v_isShared_3908_; uint8_t v_isSharedCheck_3943_; 
v_fileName_3878_ = lean_ctor_get(v___y_3875_, 0);
v_fileMap_3879_ = lean_ctor_get(v___y_3875_, 1);
v_options_3880_ = lean_ctor_get(v___y_3875_, 2);
v_currRecDepth_3881_ = lean_ctor_get(v___y_3875_, 3);
v_maxRecDepth_3882_ = lean_ctor_get(v___y_3875_, 4);
v_ref_3883_ = lean_ctor_get(v___y_3875_, 5);
v_currNamespace_3884_ = lean_ctor_get(v___y_3875_, 6);
v_openDecls_3885_ = lean_ctor_get(v___y_3875_, 7);
v_initHeartbeats_3886_ = lean_ctor_get(v___y_3875_, 8);
v_maxHeartbeats_3887_ = lean_ctor_get(v___y_3875_, 9);
v_quotContext_3888_ = lean_ctor_get(v___y_3875_, 10);
v_currMacroScope_3889_ = lean_ctor_get(v___y_3875_, 11);
v_diag_3890_ = lean_ctor_get_uint8(v___y_3875_, sizeof(void*)*14);
v_cancelTk_x3f_3891_ = lean_ctor_get(v___y_3875_, 12);
v_suppressElabErrors_3892_ = lean_ctor_get_uint8(v___y_3875_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3893_ = lean_ctor_get(v___y_3875_, 13);
v___x_3894_ = lean_st_ref_get(v___y_3876_);
v_traceState_3895_ = lean_ctor_get(v___x_3894_, 4);
lean_inc_ref(v_traceState_3895_);
lean_dec(v___x_3894_);
v_traces_3896_ = lean_ctor_get(v_traceState_3895_, 0);
lean_inc_ref(v_traces_3896_);
lean_dec_ref(v_traceState_3895_);
v_ref_3897_ = l_Lean_replaceRef(v_ref_3871_, v_ref_3883_);
lean_inc_ref(v_inheritedTraceOptions_3893_);
lean_inc(v_cancelTk_x3f_3891_);
lean_inc(v_currMacroScope_3889_);
lean_inc(v_quotContext_3888_);
lean_inc(v_maxHeartbeats_3887_);
lean_inc(v_initHeartbeats_3886_);
lean_inc(v_openDecls_3885_);
lean_inc(v_currNamespace_3884_);
lean_inc(v_maxRecDepth_3882_);
lean_inc(v_currRecDepth_3881_);
lean_inc_ref(v_options_3880_);
lean_inc_ref(v_fileMap_3879_);
lean_inc_ref(v_fileName_3878_);
v___x_3898_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3898_, 0, v_fileName_3878_);
lean_ctor_set(v___x_3898_, 1, v_fileMap_3879_);
lean_ctor_set(v___x_3898_, 2, v_options_3880_);
lean_ctor_set(v___x_3898_, 3, v_currRecDepth_3881_);
lean_ctor_set(v___x_3898_, 4, v_maxRecDepth_3882_);
lean_ctor_set(v___x_3898_, 5, v_ref_3897_);
lean_ctor_set(v___x_3898_, 6, v_currNamespace_3884_);
lean_ctor_set(v___x_3898_, 7, v_openDecls_3885_);
lean_ctor_set(v___x_3898_, 8, v_initHeartbeats_3886_);
lean_ctor_set(v___x_3898_, 9, v_maxHeartbeats_3887_);
lean_ctor_set(v___x_3898_, 10, v_quotContext_3888_);
lean_ctor_set(v___x_3898_, 11, v_currMacroScope_3889_);
lean_ctor_set(v___x_3898_, 12, v_cancelTk_x3f_3891_);
lean_ctor_set(v___x_3898_, 13, v_inheritedTraceOptions_3893_);
lean_ctor_set_uint8(v___x_3898_, sizeof(void*)*14, v_diag_3890_);
lean_ctor_set_uint8(v___x_3898_, sizeof(void*)*14 + 1, v_suppressElabErrors_3892_);
v___x_3899_ = l_Lean_PersistentArray_toArray___redArg(v_traces_3896_);
lean_dec_ref(v_traces_3896_);
v_sz_3900_ = lean_array_size(v___x_3899_);
v___x_3901_ = ((size_t)0ULL);
v___x_3902_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5_spec__6(v_sz_3900_, v___x_3901_, v___x_3899_);
v_msg_3903_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_3903_, 0, v_data_3870_);
lean_ctor_set(v_msg_3903_, 1, v_msg_3872_);
lean_ctor_set(v_msg_3903_, 2, v___x_3902_);
v___x_3904_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0_spec__0(v_msg_3903_, v___y_3873_, v___y_3874_, v___x_3898_, v___y_3876_);
lean_dec_ref(v___x_3898_);
v_a_3905_ = lean_ctor_get(v___x_3904_, 0);
v_isSharedCheck_3943_ = !lean_is_exclusive(v___x_3904_);
if (v_isSharedCheck_3943_ == 0)
{
v___x_3907_ = v___x_3904_;
v_isShared_3908_ = v_isSharedCheck_3943_;
goto v_resetjp_3906_;
}
else
{
lean_inc(v_a_3905_);
lean_dec(v___x_3904_);
v___x_3907_ = lean_box(0);
v_isShared_3908_ = v_isSharedCheck_3943_;
goto v_resetjp_3906_;
}
v_resetjp_3906_:
{
lean_object* v___x_3909_; lean_object* v_traceState_3910_; lean_object* v_env_3911_; lean_object* v_nextMacroScope_3912_; lean_object* v_ngen_3913_; lean_object* v_auxDeclNGen_3914_; lean_object* v_cache_3915_; lean_object* v_messages_3916_; lean_object* v_infoState_3917_; lean_object* v_snapshotTasks_3918_; lean_object* v_newDecls_3919_; lean_object* v___x_3921_; uint8_t v_isShared_3922_; uint8_t v_isSharedCheck_3942_; 
v___x_3909_ = lean_st_ref_take(v___y_3876_);
v_traceState_3910_ = lean_ctor_get(v___x_3909_, 4);
v_env_3911_ = lean_ctor_get(v___x_3909_, 0);
v_nextMacroScope_3912_ = lean_ctor_get(v___x_3909_, 1);
v_ngen_3913_ = lean_ctor_get(v___x_3909_, 2);
v_auxDeclNGen_3914_ = lean_ctor_get(v___x_3909_, 3);
v_cache_3915_ = lean_ctor_get(v___x_3909_, 5);
v_messages_3916_ = lean_ctor_get(v___x_3909_, 6);
v_infoState_3917_ = lean_ctor_get(v___x_3909_, 7);
v_snapshotTasks_3918_ = lean_ctor_get(v___x_3909_, 8);
v_newDecls_3919_ = lean_ctor_get(v___x_3909_, 9);
v_isSharedCheck_3942_ = !lean_is_exclusive(v___x_3909_);
if (v_isSharedCheck_3942_ == 0)
{
v___x_3921_ = v___x_3909_;
v_isShared_3922_ = v_isSharedCheck_3942_;
goto v_resetjp_3920_;
}
else
{
lean_inc(v_newDecls_3919_);
lean_inc(v_snapshotTasks_3918_);
lean_inc(v_infoState_3917_);
lean_inc(v_messages_3916_);
lean_inc(v_cache_3915_);
lean_inc(v_traceState_3910_);
lean_inc(v_auxDeclNGen_3914_);
lean_inc(v_ngen_3913_);
lean_inc(v_nextMacroScope_3912_);
lean_inc(v_env_3911_);
lean_dec(v___x_3909_);
v___x_3921_ = lean_box(0);
v_isShared_3922_ = v_isSharedCheck_3942_;
goto v_resetjp_3920_;
}
v_resetjp_3920_:
{
uint64_t v_tid_3923_; lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3940_; 
v_tid_3923_ = lean_ctor_get_uint64(v_traceState_3910_, sizeof(void*)*1);
v_isSharedCheck_3940_ = !lean_is_exclusive(v_traceState_3910_);
if (v_isSharedCheck_3940_ == 0)
{
lean_object* v_unused_3941_; 
v_unused_3941_ = lean_ctor_get(v_traceState_3910_, 0);
lean_dec(v_unused_3941_);
v___x_3925_ = v_traceState_3910_;
v_isShared_3926_ = v_isSharedCheck_3940_;
goto v_resetjp_3924_;
}
else
{
lean_dec(v_traceState_3910_);
v___x_3925_ = lean_box(0);
v_isShared_3926_ = v_isSharedCheck_3940_;
goto v_resetjp_3924_;
}
v_resetjp_3924_:
{
lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3930_; 
v___x_3927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3927_, 0, v_ref_3871_);
lean_ctor_set(v___x_3927_, 1, v_a_3905_);
v___x_3928_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_3869_, v___x_3927_);
if (v_isShared_3926_ == 0)
{
lean_ctor_set(v___x_3925_, 0, v___x_3928_);
v___x_3930_ = v___x_3925_;
goto v_reusejp_3929_;
}
else
{
lean_object* v_reuseFailAlloc_3939_; 
v_reuseFailAlloc_3939_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3939_, 0, v___x_3928_);
lean_ctor_set_uint64(v_reuseFailAlloc_3939_, sizeof(void*)*1, v_tid_3923_);
v___x_3930_ = v_reuseFailAlloc_3939_;
goto v_reusejp_3929_;
}
v_reusejp_3929_:
{
lean_object* v___x_3932_; 
if (v_isShared_3922_ == 0)
{
lean_ctor_set(v___x_3921_, 4, v___x_3930_);
v___x_3932_ = v___x_3921_;
goto v_reusejp_3931_;
}
else
{
lean_object* v_reuseFailAlloc_3938_; 
v_reuseFailAlloc_3938_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3938_, 0, v_env_3911_);
lean_ctor_set(v_reuseFailAlloc_3938_, 1, v_nextMacroScope_3912_);
lean_ctor_set(v_reuseFailAlloc_3938_, 2, v_ngen_3913_);
lean_ctor_set(v_reuseFailAlloc_3938_, 3, v_auxDeclNGen_3914_);
lean_ctor_set(v_reuseFailAlloc_3938_, 4, v___x_3930_);
lean_ctor_set(v_reuseFailAlloc_3938_, 5, v_cache_3915_);
lean_ctor_set(v_reuseFailAlloc_3938_, 6, v_messages_3916_);
lean_ctor_set(v_reuseFailAlloc_3938_, 7, v_infoState_3917_);
lean_ctor_set(v_reuseFailAlloc_3938_, 8, v_snapshotTasks_3918_);
lean_ctor_set(v_reuseFailAlloc_3938_, 9, v_newDecls_3919_);
v___x_3932_ = v_reuseFailAlloc_3938_;
goto v_reusejp_3931_;
}
v_reusejp_3931_:
{
lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3936_; 
v___x_3933_ = lean_st_ref_set(v___y_3876_, v___x_3932_);
v___x_3934_ = lean_box(0);
if (v_isShared_3908_ == 0)
{
lean_ctor_set(v___x_3907_, 0, v___x_3934_);
v___x_3936_ = v___x_3907_;
goto v_reusejp_3935_;
}
else
{
lean_object* v_reuseFailAlloc_3937_; 
v_reuseFailAlloc_3937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3937_, 0, v___x_3934_);
v___x_3936_ = v_reuseFailAlloc_3937_;
goto v_reusejp_3935_;
}
v_reusejp_3935_:
{
return v___x_3936_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__1___boxed(lean_object* v_oldTraces_3944_, lean_object* v_data_3945_, lean_object* v_ref_3946_, lean_object* v_msg_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_){
_start:
{
lean_object* v_res_3953_; 
v_res_3953_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__1(v_oldTraces_3944_, v_data_3945_, v_ref_3946_, v_msg_3947_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_);
lean_dec(v___y_3951_);
lean_dec_ref(v___y_3950_);
lean_dec(v___y_3949_);
lean_dec_ref(v___y_3948_);
return v_res_3953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1(lean_object* v_cls_3954_, uint8_t v_collapsed_3955_, lean_object* v_tag_3956_, lean_object* v_opts_3957_, uint8_t v_clsEnabled_3958_, lean_object* v_oldTraces_3959_, lean_object* v_msg_3960_, lean_object* v_resStartStop_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_){
_start:
{
lean_object* v_fst_3967_; lean_object* v_snd_3968_; lean_object* v___x_3970_; uint8_t v_isShared_3971_; uint8_t v_isSharedCheck_4067_; 
v_fst_3967_ = lean_ctor_get(v_resStartStop_3961_, 0);
v_snd_3968_ = lean_ctor_get(v_resStartStop_3961_, 1);
v_isSharedCheck_4067_ = !lean_is_exclusive(v_resStartStop_3961_);
if (v_isSharedCheck_4067_ == 0)
{
v___x_3970_ = v_resStartStop_3961_;
v_isShared_3971_ = v_isSharedCheck_4067_;
goto v_resetjp_3969_;
}
else
{
lean_inc(v_snd_3968_);
lean_inc(v_fst_3967_);
lean_dec(v_resStartStop_3961_);
v___x_3970_ = lean_box(0);
v_isShared_3971_ = v_isSharedCheck_4067_;
goto v_resetjp_3969_;
}
v_resetjp_3969_:
{
lean_object* v___y_3973_; lean_object* v___y_3974_; lean_object* v_data_3975_; lean_object* v_fst_3986_; lean_object* v_snd_3987_; lean_object* v___x_3989_; uint8_t v_isShared_3990_; uint8_t v_isSharedCheck_4066_; 
v_fst_3986_ = lean_ctor_get(v_snd_3968_, 0);
v_snd_3987_ = lean_ctor_get(v_snd_3968_, 1);
v_isSharedCheck_4066_ = !lean_is_exclusive(v_snd_3968_);
if (v_isSharedCheck_4066_ == 0)
{
v___x_3989_ = v_snd_3968_;
v_isShared_3990_ = v_isSharedCheck_4066_;
goto v_resetjp_3988_;
}
else
{
lean_inc(v_snd_3987_);
lean_inc(v_fst_3986_);
lean_dec(v_snd_3968_);
v___x_3989_ = lean_box(0);
v_isShared_3990_ = v_isSharedCheck_4066_;
goto v_resetjp_3988_;
}
v___jp_3972_:
{
lean_object* v___x_3976_; 
lean_inc(v___y_3974_);
v___x_3976_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__1(v_oldTraces_3959_, v_data_3975_, v___y_3974_, v___y_3973_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_);
if (lean_obj_tag(v___x_3976_) == 0)
{
lean_object* v___x_3977_; 
lean_dec_ref(v___x_3976_);
v___x_3977_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg(v_fst_3967_);
return v___x_3977_;
}
else
{
lean_object* v_a_3978_; lean_object* v___x_3980_; uint8_t v_isShared_3981_; uint8_t v_isSharedCheck_3985_; 
lean_dec(v_fst_3967_);
v_a_3978_ = lean_ctor_get(v___x_3976_, 0);
v_isSharedCheck_3985_ = !lean_is_exclusive(v___x_3976_);
if (v_isSharedCheck_3985_ == 0)
{
v___x_3980_ = v___x_3976_;
v_isShared_3981_ = v_isSharedCheck_3985_;
goto v_resetjp_3979_;
}
else
{
lean_inc(v_a_3978_);
lean_dec(v___x_3976_);
v___x_3980_ = lean_box(0);
v_isShared_3981_ = v_isSharedCheck_3985_;
goto v_resetjp_3979_;
}
v_resetjp_3979_:
{
lean_object* v___x_3983_; 
if (v_isShared_3981_ == 0)
{
v___x_3983_ = v___x_3980_;
goto v_reusejp_3982_;
}
else
{
lean_object* v_reuseFailAlloc_3984_; 
v_reuseFailAlloc_3984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3984_, 0, v_a_3978_);
v___x_3983_ = v_reuseFailAlloc_3984_;
goto v_reusejp_3982_;
}
v_reusejp_3982_:
{
return v___x_3983_;
}
}
}
}
v_resetjp_3988_:
{
lean_object* v___x_3991_; uint8_t v___x_3992_; lean_object* v___y_3994_; lean_object* v_a_3995_; uint8_t v___y_4019_; double v___y_4051_; 
v___x_3991_ = l_Lean_trace_profiler;
v___x_3992_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_3957_, v___x_3991_);
if (v___x_3992_ == 0)
{
v___y_4019_ = v___x_3992_;
goto v___jp_4018_;
}
else
{
lean_object* v___x_4056_; uint8_t v___x_4057_; 
v___x_4056_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4057_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_3957_, v___x_4056_);
if (v___x_4057_ == 0)
{
lean_object* v___x_4058_; lean_object* v___x_4059_; double v___x_4060_; double v___x_4061_; double v___x_4062_; 
v___x_4058_ = l_Lean_trace_profiler_threshold;
v___x_4059_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_3957_, v___x_4058_);
v___x_4060_ = lean_float_of_nat(v___x_4059_);
v___x_4061_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__4);
v___x_4062_ = lean_float_div(v___x_4060_, v___x_4061_);
v___y_4051_ = v___x_4062_;
goto v___jp_4050_;
}
else
{
lean_object* v___x_4063_; lean_object* v___x_4064_; double v___x_4065_; 
v___x_4063_ = l_Lean_trace_profiler_threshold;
v___x_4064_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_3957_, v___x_4063_);
v___x_4065_ = lean_float_of_nat(v___x_4064_);
v___y_4051_ = v___x_4065_;
goto v___jp_4050_;
}
}
v___jp_3993_:
{
uint8_t v_result_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4001_; 
v_result_3996_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4(v_fst_3967_);
v___x_3997_ = l_Lean_TraceResult_toEmoji(v_result_3996_);
v___x_3998_ = l_Lean_stringToMessageData(v___x_3997_);
v___x_3999_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1);
if (v_isShared_3990_ == 0)
{
lean_ctor_set_tag(v___x_3989_, 7);
lean_ctor_set(v___x_3989_, 1, v___x_3999_);
lean_ctor_set(v___x_3989_, 0, v___x_3998_);
v___x_4001_ = v___x_3989_;
goto v_reusejp_4000_;
}
else
{
lean_object* v_reuseFailAlloc_4012_; 
v_reuseFailAlloc_4012_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4012_, 0, v___x_3998_);
lean_ctor_set(v_reuseFailAlloc_4012_, 1, v___x_3999_);
v___x_4001_ = v_reuseFailAlloc_4012_;
goto v_reusejp_4000_;
}
v_reusejp_4000_:
{
lean_object* v_m_4003_; 
if (v_isShared_3971_ == 0)
{
lean_ctor_set_tag(v___x_3970_, 7);
lean_ctor_set(v___x_3970_, 1, v_a_3995_);
lean_ctor_set(v___x_3970_, 0, v___x_4001_);
v_m_4003_ = v___x_3970_;
goto v_reusejp_4002_;
}
else
{
lean_object* v_reuseFailAlloc_4011_; 
v_reuseFailAlloc_4011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4011_, 0, v___x_4001_);
lean_ctor_set(v_reuseFailAlloc_4011_, 1, v_a_3995_);
v_m_4003_ = v_reuseFailAlloc_4011_;
goto v_reusejp_4002_;
}
v_reusejp_4002_:
{
lean_object* v___x_4004_; lean_object* v___x_4005_; double v___x_4006_; lean_object* v_data_4007_; 
v___x_4004_ = lean_box(v_result_3996_);
v___x_4005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4005_, 0, v___x_4004_);
v___x_4006_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_3956_);
lean_inc_ref(v___x_4005_);
lean_inc(v_cls_3954_);
v_data_4007_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4007_, 0, v_cls_3954_);
lean_ctor_set(v_data_4007_, 1, v___x_4005_);
lean_ctor_set(v_data_4007_, 2, v_tag_3956_);
lean_ctor_set_float(v_data_4007_, sizeof(void*)*3, v___x_4006_);
lean_ctor_set_float(v_data_4007_, sizeof(void*)*3 + 8, v___x_4006_);
lean_ctor_set_uint8(v_data_4007_, sizeof(void*)*3 + 16, v_collapsed_3955_);
if (v___x_3992_ == 0)
{
lean_dec_ref(v___x_4005_);
lean_dec(v_snd_3987_);
lean_dec(v_fst_3986_);
lean_dec_ref(v_tag_3956_);
lean_dec(v_cls_3954_);
v___y_3973_ = v_m_4003_;
v___y_3974_ = v___y_3994_;
v_data_3975_ = v_data_4007_;
goto v___jp_3972_;
}
else
{
lean_object* v_data_4008_; double v___x_4009_; double v___x_4010_; 
lean_dec_ref(v_data_4007_);
v_data_4008_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4008_, 0, v_cls_3954_);
lean_ctor_set(v_data_4008_, 1, v___x_4005_);
lean_ctor_set(v_data_4008_, 2, v_tag_3956_);
v___x_4009_ = lean_unbox_float(v_fst_3986_);
lean_dec(v_fst_3986_);
lean_ctor_set_float(v_data_4008_, sizeof(void*)*3, v___x_4009_);
v___x_4010_ = lean_unbox_float(v_snd_3987_);
lean_dec(v_snd_3987_);
lean_ctor_set_float(v_data_4008_, sizeof(void*)*3 + 8, v___x_4010_);
lean_ctor_set_uint8(v_data_4008_, sizeof(void*)*3 + 16, v_collapsed_3955_);
v___y_3973_ = v_m_4003_;
v___y_3974_ = v___y_3994_;
v_data_3975_ = v_data_4008_;
goto v___jp_3972_;
}
}
}
}
v___jp_4013_:
{
lean_object* v_ref_4014_; lean_object* v___x_4015_; 
v_ref_4014_ = lean_ctor_get(v___y_3964_, 5);
lean_inc(v___y_3965_);
lean_inc_ref(v___y_3964_);
lean_inc(v___y_3963_);
lean_inc_ref(v___y_3962_);
lean_inc(v_fst_3967_);
v___x_4015_ = lean_apply_6(v_msg_3960_, v_fst_3967_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_, lean_box(0));
if (lean_obj_tag(v___x_4015_) == 0)
{
lean_object* v_a_4016_; 
v_a_4016_ = lean_ctor_get(v___x_4015_, 0);
lean_inc(v_a_4016_);
lean_dec_ref(v___x_4015_);
v___y_3994_ = v_ref_4014_;
v_a_3995_ = v_a_4016_;
goto v___jp_3993_;
}
else
{
lean_object* v___x_4017_; 
lean_dec_ref(v___x_4015_);
v___x_4017_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__3);
v___y_3994_ = v_ref_4014_;
v_a_3995_ = v___x_4017_;
goto v___jp_3993_;
}
}
v___jp_4018_:
{
if (v_clsEnabled_3958_ == 0)
{
if (v___y_4019_ == 0)
{
lean_object* v___x_4020_; lean_object* v_traceState_4021_; lean_object* v_env_4022_; lean_object* v_nextMacroScope_4023_; lean_object* v_ngen_4024_; lean_object* v_auxDeclNGen_4025_; lean_object* v_cache_4026_; lean_object* v_messages_4027_; lean_object* v_infoState_4028_; lean_object* v_snapshotTasks_4029_; lean_object* v_newDecls_4030_; lean_object* v___x_4032_; uint8_t v_isShared_4033_; uint8_t v_isSharedCheck_4049_; 
lean_del_object(v___x_3989_);
lean_dec(v_snd_3987_);
lean_dec(v_fst_3986_);
lean_del_object(v___x_3970_);
lean_dec_ref(v_msg_3960_);
lean_dec_ref(v_tag_3956_);
lean_dec(v_cls_3954_);
v___x_4020_ = lean_st_ref_take(v___y_3965_);
v_traceState_4021_ = lean_ctor_get(v___x_4020_, 4);
v_env_4022_ = lean_ctor_get(v___x_4020_, 0);
v_nextMacroScope_4023_ = lean_ctor_get(v___x_4020_, 1);
v_ngen_4024_ = lean_ctor_get(v___x_4020_, 2);
v_auxDeclNGen_4025_ = lean_ctor_get(v___x_4020_, 3);
v_cache_4026_ = lean_ctor_get(v___x_4020_, 5);
v_messages_4027_ = lean_ctor_get(v___x_4020_, 6);
v_infoState_4028_ = lean_ctor_get(v___x_4020_, 7);
v_snapshotTasks_4029_ = lean_ctor_get(v___x_4020_, 8);
v_newDecls_4030_ = lean_ctor_get(v___x_4020_, 9);
v_isSharedCheck_4049_ = !lean_is_exclusive(v___x_4020_);
if (v_isSharedCheck_4049_ == 0)
{
v___x_4032_ = v___x_4020_;
v_isShared_4033_ = v_isSharedCheck_4049_;
goto v_resetjp_4031_;
}
else
{
lean_inc(v_newDecls_4030_);
lean_inc(v_snapshotTasks_4029_);
lean_inc(v_infoState_4028_);
lean_inc(v_messages_4027_);
lean_inc(v_cache_4026_);
lean_inc(v_traceState_4021_);
lean_inc(v_auxDeclNGen_4025_);
lean_inc(v_ngen_4024_);
lean_inc(v_nextMacroScope_4023_);
lean_inc(v_env_4022_);
lean_dec(v___x_4020_);
v___x_4032_ = lean_box(0);
v_isShared_4033_ = v_isSharedCheck_4049_;
goto v_resetjp_4031_;
}
v_resetjp_4031_:
{
uint64_t v_tid_4034_; lean_object* v_traces_4035_; lean_object* v___x_4037_; uint8_t v_isShared_4038_; uint8_t v_isSharedCheck_4048_; 
v_tid_4034_ = lean_ctor_get_uint64(v_traceState_4021_, sizeof(void*)*1);
v_traces_4035_ = lean_ctor_get(v_traceState_4021_, 0);
v_isSharedCheck_4048_ = !lean_is_exclusive(v_traceState_4021_);
if (v_isSharedCheck_4048_ == 0)
{
v___x_4037_ = v_traceState_4021_;
v_isShared_4038_ = v_isSharedCheck_4048_;
goto v_resetjp_4036_;
}
else
{
lean_inc(v_traces_4035_);
lean_dec(v_traceState_4021_);
v___x_4037_ = lean_box(0);
v_isShared_4038_ = v_isSharedCheck_4048_;
goto v_resetjp_4036_;
}
v_resetjp_4036_:
{
lean_object* v___x_4039_; lean_object* v___x_4041_; 
v___x_4039_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3959_, v_traces_4035_);
lean_dec_ref(v_traces_4035_);
if (v_isShared_4038_ == 0)
{
lean_ctor_set(v___x_4037_, 0, v___x_4039_);
v___x_4041_ = v___x_4037_;
goto v_reusejp_4040_;
}
else
{
lean_object* v_reuseFailAlloc_4047_; 
v_reuseFailAlloc_4047_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4047_, 0, v___x_4039_);
lean_ctor_set_uint64(v_reuseFailAlloc_4047_, sizeof(void*)*1, v_tid_4034_);
v___x_4041_ = v_reuseFailAlloc_4047_;
goto v_reusejp_4040_;
}
v_reusejp_4040_:
{
lean_object* v___x_4043_; 
if (v_isShared_4033_ == 0)
{
lean_ctor_set(v___x_4032_, 4, v___x_4041_);
v___x_4043_ = v___x_4032_;
goto v_reusejp_4042_;
}
else
{
lean_object* v_reuseFailAlloc_4046_; 
v_reuseFailAlloc_4046_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4046_, 0, v_env_4022_);
lean_ctor_set(v_reuseFailAlloc_4046_, 1, v_nextMacroScope_4023_);
lean_ctor_set(v_reuseFailAlloc_4046_, 2, v_ngen_4024_);
lean_ctor_set(v_reuseFailAlloc_4046_, 3, v_auxDeclNGen_4025_);
lean_ctor_set(v_reuseFailAlloc_4046_, 4, v___x_4041_);
lean_ctor_set(v_reuseFailAlloc_4046_, 5, v_cache_4026_);
lean_ctor_set(v_reuseFailAlloc_4046_, 6, v_messages_4027_);
lean_ctor_set(v_reuseFailAlloc_4046_, 7, v_infoState_4028_);
lean_ctor_set(v_reuseFailAlloc_4046_, 8, v_snapshotTasks_4029_);
lean_ctor_set(v_reuseFailAlloc_4046_, 9, v_newDecls_4030_);
v___x_4043_ = v_reuseFailAlloc_4046_;
goto v_reusejp_4042_;
}
v_reusejp_4042_:
{
lean_object* v___x_4044_; lean_object* v___x_4045_; 
v___x_4044_ = lean_st_ref_set(v___y_3965_, v___x_4043_);
v___x_4045_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg(v_fst_3967_);
return v___x_4045_;
}
}
}
}
}
else
{
goto v___jp_4013_;
}
}
else
{
goto v___jp_4013_;
}
}
v___jp_4050_:
{
double v___x_4052_; double v___x_4053_; double v___x_4054_; uint8_t v___x_4055_; 
v___x_4052_ = lean_unbox_float(v_snd_3987_);
v___x_4053_ = lean_unbox_float(v_fst_3986_);
v___x_4054_ = lean_float_sub(v___x_4052_, v___x_4053_);
v___x_4055_ = lean_float_decLt(v___y_4051_, v___x_4054_);
v___y_4019_ = v___x_4055_;
goto v___jp_4018_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1___boxed(lean_object* v_cls_4068_, lean_object* v_collapsed_4069_, lean_object* v_tag_4070_, lean_object* v_opts_4071_, lean_object* v_clsEnabled_4072_, lean_object* v_oldTraces_4073_, lean_object* v_msg_4074_, lean_object* v_resStartStop_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_){
_start:
{
uint8_t v_collapsed_boxed_4081_; uint8_t v_clsEnabled_boxed_4082_; lean_object* v_res_4083_; 
v_collapsed_boxed_4081_ = lean_unbox(v_collapsed_4069_);
v_clsEnabled_boxed_4082_ = lean_unbox(v_clsEnabled_4072_);
v_res_4083_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1(v_cls_4068_, v_collapsed_boxed_4081_, v_tag_4070_, v_opts_4071_, v_clsEnabled_boxed_4082_, v_oldTraces_4073_, v_msg_4074_, v_resStartStop_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_);
lean_dec(v___y_4079_);
lean_dec_ref(v___y_4078_);
lean_dec(v___y_4077_);
lean_dec_ref(v___y_4076_);
lean_dec_ref(v_opts_4071_);
return v_res_4083_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1(void){
_start:
{
lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; 
v___x_4088_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0));
v___x_4089_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__3));
v___x_4090_ = l_Lean_Name_append(v___x_4089_, v___x_4088_);
return v___x_4090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry(lean_object* v_e_4091_, lean_object* v_a_4092_, lean_object* v_a_4093_, lean_object* v_a_4094_, lean_object* v_a_4095_){
_start:
{
lean_object* v_options_4097_; uint8_t v_hasTrace_4098_; 
v_options_4097_ = lean_ctor_get(v_a_4094_, 2);
v_hasTrace_4098_ = lean_ctor_get_uint8(v_options_4097_, sizeof(void*)*1);
if (v_hasTrace_4098_ == 0)
{
lean_object* v___x_4099_; 
v___x_4099_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_4095_);
if (lean_obj_tag(v___x_4099_) == 0)
{
lean_object* v_a_4100_; lean_object* v___x_4101_; 
v_a_4100_ = lean_ctor_get(v___x_4099_, 0);
lean_inc(v_a_4100_);
lean_dec_ref(v___x_4099_);
v___x_4101_ = l_Lean_Meta_Sym_unfoldReducible(v_e_4091_, v_a_4092_, v_a_4093_, v_a_4094_, v_a_4095_);
if (lean_obj_tag(v___x_4101_) == 0)
{
lean_object* v_a_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___f_4108_; lean_object* v___x_4109_; 
v_a_4102_ = lean_ctor_get(v___x_4101_, 0);
lean_inc(v_a_4102_);
lean_dec_ref(v___x_4101_);
v___x_4103_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_4104_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_4097_, v___x_4103_);
v___x_4105_ = lean_unsigned_to_nat(2u);
v___x_4106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4106_, 0, v___x_4104_);
lean_ctor_set(v___x_4106_, 1, v___x_4105_);
v___x_4107_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(v_a_4100_);
v___f_4108_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4108_, 0, v_a_4102_);
lean_closure_set(v___f_4108_, 1, v___x_4107_);
lean_closure_set(v___f_4108_, 2, v___x_4106_);
v___x_4109_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_4108_, v_a_4092_, v_a_4093_, v_a_4094_, v_a_4095_);
return v___x_4109_;
}
else
{
lean_object* v_a_4110_; lean_object* v___x_4112_; uint8_t v_isShared_4113_; uint8_t v_isSharedCheck_4117_; 
lean_dec(v_a_4100_);
v_a_4110_ = lean_ctor_get(v___x_4101_, 0);
v_isSharedCheck_4117_ = !lean_is_exclusive(v___x_4101_);
if (v_isSharedCheck_4117_ == 0)
{
v___x_4112_ = v___x_4101_;
v_isShared_4113_ = v_isSharedCheck_4117_;
goto v_resetjp_4111_;
}
else
{
lean_inc(v_a_4110_);
lean_dec(v___x_4101_);
v___x_4112_ = lean_box(0);
v_isShared_4113_ = v_isSharedCheck_4117_;
goto v_resetjp_4111_;
}
v_resetjp_4111_:
{
lean_object* v___x_4115_; 
if (v_isShared_4113_ == 0)
{
v___x_4115_ = v___x_4112_;
goto v_reusejp_4114_;
}
else
{
lean_object* v_reuseFailAlloc_4116_; 
v_reuseFailAlloc_4116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4116_, 0, v_a_4110_);
v___x_4115_ = v_reuseFailAlloc_4116_;
goto v_reusejp_4114_;
}
v_reusejp_4114_:
{
return v___x_4115_;
}
}
}
}
else
{
lean_object* v_a_4118_; lean_object* v___x_4120_; uint8_t v_isShared_4121_; uint8_t v_isSharedCheck_4125_; 
lean_dec_ref(v_e_4091_);
v_a_4118_ = lean_ctor_get(v___x_4099_, 0);
v_isSharedCheck_4125_ = !lean_is_exclusive(v___x_4099_);
if (v_isSharedCheck_4125_ == 0)
{
v___x_4120_ = v___x_4099_;
v_isShared_4121_ = v_isSharedCheck_4125_;
goto v_resetjp_4119_;
}
else
{
lean_inc(v_a_4118_);
lean_dec(v___x_4099_);
v___x_4120_ = lean_box(0);
v_isShared_4121_ = v_isSharedCheck_4125_;
goto v_resetjp_4119_;
}
v_resetjp_4119_:
{
lean_object* v___x_4123_; 
if (v_isShared_4121_ == 0)
{
v___x_4123_ = v___x_4120_;
goto v_reusejp_4122_;
}
else
{
lean_object* v_reuseFailAlloc_4124_; 
v_reuseFailAlloc_4124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4124_, 0, v_a_4118_);
v___x_4123_ = v_reuseFailAlloc_4124_;
goto v_reusejp_4122_;
}
v_reusejp_4122_:
{
return v___x_4123_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_4126_; lean_object* v___f_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; uint8_t v___x_4131_; lean_object* v___y_4133_; lean_object* v___y_4134_; lean_object* v_a_4135_; lean_object* v___y_4148_; lean_object* v___y_4149_; lean_object* v_a_4150_; lean_object* v___y_4153_; lean_object* v___y_4154_; lean_object* v_a_4155_; lean_object* v___y_4165_; lean_object* v___y_4166_; lean_object* v_a_4167_; 
v_inheritedTraceOptions_4126_ = lean_ctor_get(v_a_4094_, 13);
lean_inc_ref(v_e_4091_);
v___f_4127_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___boxed), 7, 1);
lean_closure_set(v___f_4127_, 0, v_e_4091_);
v___x_4128_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0));
v___x_4129_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__1));
v___x_4130_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1);
v___x_4131_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4126_, v_options_4097_, v___x_4130_);
if (v___x_4131_ == 0)
{
lean_object* v___x_4220_; uint8_t v___x_4221_; 
v___x_4220_ = l_Lean_trace_profiler;
v___x_4221_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_4097_, v___x_4220_);
if (v___x_4221_ == 0)
{
lean_object* v___x_4222_; 
lean_dec_ref(v___f_4127_);
v___x_4222_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_4095_);
if (lean_obj_tag(v___x_4222_) == 0)
{
lean_object* v_a_4223_; lean_object* v___x_4224_; 
v_a_4223_ = lean_ctor_get(v___x_4222_, 0);
lean_inc(v_a_4223_);
lean_dec_ref(v___x_4222_);
v___x_4224_ = l_Lean_Meta_Sym_unfoldReducible(v_e_4091_, v_a_4092_, v_a_4093_, v_a_4094_, v_a_4095_);
if (lean_obj_tag(v___x_4224_) == 0)
{
lean_object* v_a_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___f_4231_; lean_object* v___x_4232_; 
v_a_4225_ = lean_ctor_get(v___x_4224_, 0);
lean_inc(v_a_4225_);
lean_dec_ref(v___x_4224_);
v___x_4226_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_4227_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_4097_, v___x_4226_);
v___x_4228_ = lean_unsigned_to_nat(2u);
v___x_4229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4229_, 0, v___x_4227_);
lean_ctor_set(v___x_4229_, 1, v___x_4228_);
v___x_4230_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(v_a_4223_);
v___f_4231_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4231_, 0, v_a_4225_);
lean_closure_set(v___f_4231_, 1, v___x_4230_);
lean_closure_set(v___f_4231_, 2, v___x_4229_);
v___x_4232_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_4231_, v_a_4092_, v_a_4093_, v_a_4094_, v_a_4095_);
return v___x_4232_;
}
else
{
lean_object* v_a_4233_; lean_object* v___x_4235_; uint8_t v_isShared_4236_; uint8_t v_isSharedCheck_4240_; 
lean_dec(v_a_4223_);
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
v___x_4238_ = v___x_4235_;
goto v_reusejp_4237_;
}
else
{
lean_object* v_reuseFailAlloc_4239_; 
v_reuseFailAlloc_4239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4239_, 0, v_a_4233_);
v___x_4238_ = v_reuseFailAlloc_4239_;
goto v_reusejp_4237_;
}
v_reusejp_4237_:
{
return v___x_4238_;
}
}
}
}
else
{
lean_object* v_a_4241_; lean_object* v___x_4243_; uint8_t v_isShared_4244_; uint8_t v_isSharedCheck_4248_; 
lean_dec_ref(v_e_4091_);
v_a_4241_ = lean_ctor_get(v___x_4222_, 0);
v_isSharedCheck_4248_ = !lean_is_exclusive(v___x_4222_);
if (v_isSharedCheck_4248_ == 0)
{
v___x_4243_ = v___x_4222_;
v_isShared_4244_ = v_isSharedCheck_4248_;
goto v_resetjp_4242_;
}
else
{
lean_inc(v_a_4241_);
lean_dec(v___x_4222_);
v___x_4243_ = lean_box(0);
v_isShared_4244_ = v_isSharedCheck_4248_;
goto v_resetjp_4242_;
}
v_resetjp_4242_:
{
lean_object* v___x_4246_; 
if (v_isShared_4244_ == 0)
{
v___x_4246_ = v___x_4243_;
goto v_reusejp_4245_;
}
else
{
lean_object* v_reuseFailAlloc_4247_; 
v_reuseFailAlloc_4247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4247_, 0, v_a_4241_);
v___x_4246_ = v_reuseFailAlloc_4247_;
goto v_reusejp_4245_;
}
v_reusejp_4245_:
{
return v___x_4246_;
}
}
}
}
else
{
goto v___jp_4169_;
}
}
else
{
goto v___jp_4169_;
}
v___jp_4132_:
{
lean_object* v___x_4136_; double v___x_4137_; double v___x_4138_; double v___x_4139_; double v___x_4140_; double v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; 
v___x_4136_ = lean_io_mono_nanos_now();
v___x_4137_ = lean_float_of_nat(v___y_4133_);
v___x_4138_ = lean_float_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9);
v___x_4139_ = lean_float_div(v___x_4137_, v___x_4138_);
v___x_4140_ = lean_float_of_nat(v___x_4136_);
v___x_4141_ = lean_float_div(v___x_4140_, v___x_4138_);
v___x_4142_ = lean_box_float(v___x_4139_);
v___x_4143_ = lean_box_float(v___x_4141_);
v___x_4144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4144_, 0, v___x_4142_);
lean_ctor_set(v___x_4144_, 1, v___x_4143_);
v___x_4145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4145_, 0, v_a_4135_);
lean_ctor_set(v___x_4145_, 1, v___x_4144_);
v___x_4146_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1(v___x_4128_, v_hasTrace_4098_, v___x_4129_, v_options_4097_, v___x_4131_, v___y_4134_, v___f_4127_, v___x_4145_, v_a_4092_, v_a_4093_, v_a_4094_, v_a_4095_);
return v___x_4146_;
}
v___jp_4147_:
{
lean_object* v___x_4151_; 
v___x_4151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4151_, 0, v_a_4150_);
v___y_4133_ = v___y_4148_;
v___y_4134_ = v___y_4149_;
v_a_4135_ = v___x_4151_;
goto v___jp_4132_;
}
v___jp_4152_:
{
lean_object* v___x_4156_; double v___x_4157_; double v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; 
v___x_4156_ = lean_io_get_num_heartbeats();
v___x_4157_ = lean_float_of_nat(v___y_4153_);
v___x_4158_ = lean_float_of_nat(v___x_4156_);
v___x_4159_ = lean_box_float(v___x_4157_);
v___x_4160_ = lean_box_float(v___x_4158_);
v___x_4161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4161_, 0, v___x_4159_);
lean_ctor_set(v___x_4161_, 1, v___x_4160_);
v___x_4162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4162_, 0, v_a_4155_);
lean_ctor_set(v___x_4162_, 1, v___x_4161_);
v___x_4163_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1(v___x_4128_, v_hasTrace_4098_, v___x_4129_, v_options_4097_, v___x_4131_, v___y_4154_, v___f_4127_, v___x_4162_, v_a_4092_, v_a_4093_, v_a_4094_, v_a_4095_);
return v___x_4163_;
}
v___jp_4164_:
{
lean_object* v___x_4168_; 
v___x_4168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4168_, 0, v_a_4167_);
v___y_4153_ = v___y_4165_;
v___y_4154_ = v___y_4166_;
v_a_4155_ = v___x_4168_;
goto v___jp_4152_;
}
v___jp_4169_:
{
lean_object* v___x_4170_; lean_object* v_a_4171_; lean_object* v___x_4172_; uint8_t v___x_4173_; 
v___x_4170_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg(v_a_4095_);
v_a_4171_ = lean_ctor_get(v___x_4170_, 0);
lean_inc(v_a_4171_);
lean_dec_ref(v___x_4170_);
v___x_4172_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4173_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_4097_, v___x_4172_);
if (v___x_4173_ == 0)
{
lean_object* v___x_4174_; lean_object* v___x_4175_; 
v___x_4174_ = lean_io_mono_nanos_now();
v___x_4175_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_4095_);
if (lean_obj_tag(v___x_4175_) == 0)
{
lean_object* v_a_4176_; lean_object* v___x_4177_; 
v_a_4176_ = lean_ctor_get(v___x_4175_, 0);
lean_inc(v_a_4176_);
lean_dec_ref(v___x_4175_);
v___x_4177_ = l_Lean_Meta_Sym_unfoldReducible(v_e_4091_, v_a_4092_, v_a_4093_, v_a_4094_, v_a_4095_);
if (lean_obj_tag(v___x_4177_) == 0)
{
lean_object* v_a_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___f_4184_; lean_object* v___x_4185_; 
v_a_4178_ = lean_ctor_get(v___x_4177_, 0);
lean_inc(v_a_4178_);
lean_dec_ref(v___x_4177_);
v___x_4179_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_4180_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_4097_, v___x_4179_);
v___x_4181_ = lean_unsigned_to_nat(2u);
v___x_4182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4182_, 0, v___x_4180_);
lean_ctor_set(v___x_4182_, 1, v___x_4181_);
v___x_4183_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(v_a_4176_);
v___f_4184_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4184_, 0, v_a_4178_);
lean_closure_set(v___f_4184_, 1, v___x_4183_);
lean_closure_set(v___f_4184_, 2, v___x_4182_);
v___x_4185_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_4184_, v_a_4092_, v_a_4093_, v_a_4094_, v_a_4095_);
if (lean_obj_tag(v___x_4185_) == 0)
{
lean_object* v_a_4186_; lean_object* v___x_4188_; uint8_t v_isShared_4189_; uint8_t v_isSharedCheck_4193_; 
v_a_4186_ = lean_ctor_get(v___x_4185_, 0);
v_isSharedCheck_4193_ = !lean_is_exclusive(v___x_4185_);
if (v_isSharedCheck_4193_ == 0)
{
v___x_4188_ = v___x_4185_;
v_isShared_4189_ = v_isSharedCheck_4193_;
goto v_resetjp_4187_;
}
else
{
lean_inc(v_a_4186_);
lean_dec(v___x_4185_);
v___x_4188_ = lean_box(0);
v_isShared_4189_ = v_isSharedCheck_4193_;
goto v_resetjp_4187_;
}
v_resetjp_4187_:
{
lean_object* v___x_4191_; 
if (v_isShared_4189_ == 0)
{
lean_ctor_set_tag(v___x_4188_, 1);
v___x_4191_ = v___x_4188_;
goto v_reusejp_4190_;
}
else
{
lean_object* v_reuseFailAlloc_4192_; 
v_reuseFailAlloc_4192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4192_, 0, v_a_4186_);
v___x_4191_ = v_reuseFailAlloc_4192_;
goto v_reusejp_4190_;
}
v_reusejp_4190_:
{
v___y_4133_ = v___x_4174_;
v___y_4134_ = v_a_4171_;
v_a_4135_ = v___x_4191_;
goto v___jp_4132_;
}
}
}
else
{
lean_object* v_a_4194_; 
v_a_4194_ = lean_ctor_get(v___x_4185_, 0);
lean_inc(v_a_4194_);
lean_dec_ref(v___x_4185_);
v___y_4148_ = v___x_4174_;
v___y_4149_ = v_a_4171_;
v_a_4150_ = v_a_4194_;
goto v___jp_4147_;
}
}
else
{
lean_object* v_a_4195_; 
lean_dec(v_a_4176_);
v_a_4195_ = lean_ctor_get(v___x_4177_, 0);
lean_inc(v_a_4195_);
lean_dec_ref(v___x_4177_);
v___y_4148_ = v___x_4174_;
v___y_4149_ = v_a_4171_;
v_a_4150_ = v_a_4195_;
goto v___jp_4147_;
}
}
else
{
lean_object* v_a_4196_; 
lean_dec_ref(v_e_4091_);
v_a_4196_ = lean_ctor_get(v___x_4175_, 0);
lean_inc(v_a_4196_);
lean_dec_ref(v___x_4175_);
v___y_4148_ = v___x_4174_;
v___y_4149_ = v_a_4171_;
v_a_4150_ = v_a_4196_;
goto v___jp_4147_;
}
}
else
{
lean_object* v___x_4197_; lean_object* v___x_4198_; 
v___x_4197_ = lean_io_get_num_heartbeats();
v___x_4198_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_4095_);
if (lean_obj_tag(v___x_4198_) == 0)
{
lean_object* v_a_4199_; lean_object* v___x_4200_; 
v_a_4199_ = lean_ctor_get(v___x_4198_, 0);
lean_inc(v_a_4199_);
lean_dec_ref(v___x_4198_);
v___x_4200_ = l_Lean_Meta_Sym_unfoldReducible(v_e_4091_, v_a_4092_, v_a_4093_, v_a_4094_, v_a_4095_);
if (lean_obj_tag(v___x_4200_) == 0)
{
lean_object* v_a_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___f_4207_; lean_object* v___x_4208_; 
v_a_4201_ = lean_ctor_get(v___x_4200_, 0);
lean_inc(v_a_4201_);
lean_dec_ref(v___x_4200_);
v___x_4202_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_4203_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_4097_, v___x_4202_);
v___x_4204_ = lean_unsigned_to_nat(2u);
v___x_4205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4205_, 0, v___x_4203_);
lean_ctor_set(v___x_4205_, 1, v___x_4204_);
v___x_4206_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(v_a_4199_);
v___f_4207_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4207_, 0, v_a_4201_);
lean_closure_set(v___f_4207_, 1, v___x_4206_);
lean_closure_set(v___f_4207_, 2, v___x_4205_);
v___x_4208_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_4207_, v_a_4092_, v_a_4093_, v_a_4094_, v_a_4095_);
if (lean_obj_tag(v___x_4208_) == 0)
{
lean_object* v_a_4209_; lean_object* v___x_4211_; uint8_t v_isShared_4212_; uint8_t v_isSharedCheck_4216_; 
v_a_4209_ = lean_ctor_get(v___x_4208_, 0);
v_isSharedCheck_4216_ = !lean_is_exclusive(v___x_4208_);
if (v_isSharedCheck_4216_ == 0)
{
v___x_4211_ = v___x_4208_;
v_isShared_4212_ = v_isSharedCheck_4216_;
goto v_resetjp_4210_;
}
else
{
lean_inc(v_a_4209_);
lean_dec(v___x_4208_);
v___x_4211_ = lean_box(0);
v_isShared_4212_ = v_isSharedCheck_4216_;
goto v_resetjp_4210_;
}
v_resetjp_4210_:
{
lean_object* v___x_4214_; 
if (v_isShared_4212_ == 0)
{
lean_ctor_set_tag(v___x_4211_, 1);
v___x_4214_ = v___x_4211_;
goto v_reusejp_4213_;
}
else
{
lean_object* v_reuseFailAlloc_4215_; 
v_reuseFailAlloc_4215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4215_, 0, v_a_4209_);
v___x_4214_ = v_reuseFailAlloc_4215_;
goto v_reusejp_4213_;
}
v_reusejp_4213_:
{
v___y_4153_ = v___x_4197_;
v___y_4154_ = v_a_4171_;
v_a_4155_ = v___x_4214_;
goto v___jp_4152_;
}
}
}
else
{
lean_object* v_a_4217_; 
v_a_4217_ = lean_ctor_get(v___x_4208_, 0);
lean_inc(v_a_4217_);
lean_dec_ref(v___x_4208_);
v___y_4165_ = v___x_4197_;
v___y_4166_ = v_a_4171_;
v_a_4167_ = v_a_4217_;
goto v___jp_4164_;
}
}
else
{
lean_object* v_a_4218_; 
lean_dec(v_a_4199_);
v_a_4218_ = lean_ctor_get(v___x_4200_, 0);
lean_inc(v_a_4218_);
lean_dec_ref(v___x_4200_);
v___y_4165_ = v___x_4197_;
v___y_4166_ = v_a_4171_;
v_a_4167_ = v_a_4218_;
goto v___jp_4164_;
}
}
else
{
lean_object* v_a_4219_; 
lean_dec_ref(v_e_4091_);
v_a_4219_ = lean_ctor_get(v___x_4198_, 0);
lean_inc(v_a_4219_);
lean_dec_ref(v___x_4198_);
v___y_4165_ = v___x_4197_;
v___y_4166_ = v_a_4171_;
v_a_4167_ = v_a_4219_;
goto v___jp_4164_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___boxed(lean_object* v_e_4249_, lean_object* v_a_4250_, lean_object* v_a_4251_, lean_object* v_a_4252_, lean_object* v_a_4253_, lean_object* v_a_4254_){
_start:
{
lean_object* v_res_4255_; 
v_res_4255_ = l_Lean_Meta_Tactic_Cbv_cbvEntry(v_e_4249_, v_a_4250_, v_a_4251_, v_a_4252_, v_a_4253_);
lean_dec(v_a_4253_);
lean_dec_ref(v_a_4252_);
lean_dec(v_a_4251_);
lean_dec_ref(v_a_4250_);
return v_res_4255_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2(lean_object* v_00_u03b1_4256_, lean_object* v_x_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_){
_start:
{
lean_object* v___x_4263_; 
v___x_4263_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg(v_x_4257_);
return v___x_4263_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___boxed(lean_object* v_00_u03b1_4264_, lean_object* v_x_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_){
_start:
{
lean_object* v_res_4271_; 
v_res_4271_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2(v_00_u03b1_4264_, v_x_4265_, v___y_4266_, v___y_4267_, v___y_4268_, v___y_4269_);
lean_dec(v___y_4269_);
lean_dec_ref(v___y_4268_);
lean_dec(v___y_4267_);
lean_dec_ref(v___y_4266_);
return v_res_4271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__1___redArg(lean_object* v___y_4272_){
_start:
{
lean_object* v___x_4274_; lean_object* v_traceState_4275_; lean_object* v_traces_4276_; lean_object* v___x_4277_; lean_object* v_traceState_4278_; lean_object* v_env_4279_; lean_object* v_nextMacroScope_4280_; lean_object* v_ngen_4281_; lean_object* v_auxDeclNGen_4282_; lean_object* v_cache_4283_; lean_object* v_messages_4284_; lean_object* v_infoState_4285_; lean_object* v_snapshotTasks_4286_; lean_object* v_newDecls_4287_; lean_object* v___x_4289_; uint8_t v_isShared_4290_; uint8_t v_isSharedCheck_4308_; 
v___x_4274_ = lean_st_ref_get(v___y_4272_);
v_traceState_4275_ = lean_ctor_get(v___x_4274_, 4);
lean_inc_ref(v_traceState_4275_);
lean_dec(v___x_4274_);
v_traces_4276_ = lean_ctor_get(v_traceState_4275_, 0);
lean_inc_ref(v_traces_4276_);
lean_dec_ref(v_traceState_4275_);
v___x_4277_ = lean_st_ref_take(v___y_4272_);
v_traceState_4278_ = lean_ctor_get(v___x_4277_, 4);
v_env_4279_ = lean_ctor_get(v___x_4277_, 0);
v_nextMacroScope_4280_ = lean_ctor_get(v___x_4277_, 1);
v_ngen_4281_ = lean_ctor_get(v___x_4277_, 2);
v_auxDeclNGen_4282_ = lean_ctor_get(v___x_4277_, 3);
v_cache_4283_ = lean_ctor_get(v___x_4277_, 5);
v_messages_4284_ = lean_ctor_get(v___x_4277_, 6);
v_infoState_4285_ = lean_ctor_get(v___x_4277_, 7);
v_snapshotTasks_4286_ = lean_ctor_get(v___x_4277_, 8);
v_newDecls_4287_ = lean_ctor_get(v___x_4277_, 9);
v_isSharedCheck_4308_ = !lean_is_exclusive(v___x_4277_);
if (v_isSharedCheck_4308_ == 0)
{
v___x_4289_ = v___x_4277_;
v_isShared_4290_ = v_isSharedCheck_4308_;
goto v_resetjp_4288_;
}
else
{
lean_inc(v_newDecls_4287_);
lean_inc(v_snapshotTasks_4286_);
lean_inc(v_infoState_4285_);
lean_inc(v_messages_4284_);
lean_inc(v_cache_4283_);
lean_inc(v_traceState_4278_);
lean_inc(v_auxDeclNGen_4282_);
lean_inc(v_ngen_4281_);
lean_inc(v_nextMacroScope_4280_);
lean_inc(v_env_4279_);
lean_dec(v___x_4277_);
v___x_4289_ = lean_box(0);
v_isShared_4290_ = v_isSharedCheck_4308_;
goto v_resetjp_4288_;
}
v_resetjp_4288_:
{
uint64_t v_tid_4291_; lean_object* v___x_4293_; uint8_t v_isShared_4294_; uint8_t v_isSharedCheck_4306_; 
v_tid_4291_ = lean_ctor_get_uint64(v_traceState_4278_, sizeof(void*)*1);
v_isSharedCheck_4306_ = !lean_is_exclusive(v_traceState_4278_);
if (v_isSharedCheck_4306_ == 0)
{
lean_object* v_unused_4307_; 
v_unused_4307_ = lean_ctor_get(v_traceState_4278_, 0);
lean_dec(v_unused_4307_);
v___x_4293_ = v_traceState_4278_;
v_isShared_4294_ = v_isSharedCheck_4306_;
goto v_resetjp_4292_;
}
else
{
lean_dec(v_traceState_4278_);
v___x_4293_ = lean_box(0);
v_isShared_4294_ = v_isSharedCheck_4306_;
goto v_resetjp_4292_;
}
v_resetjp_4292_:
{
lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4299_; 
v___x_4295_ = lean_unsigned_to_nat(32u);
v___x_4296_ = lean_mk_empty_array_with_capacity(v___x_4295_);
lean_dec_ref(v___x_4296_);
v___x_4297_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1);
if (v_isShared_4294_ == 0)
{
lean_ctor_set(v___x_4293_, 0, v___x_4297_);
v___x_4299_ = v___x_4293_;
goto v_reusejp_4298_;
}
else
{
lean_object* v_reuseFailAlloc_4305_; 
v_reuseFailAlloc_4305_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4305_, 0, v___x_4297_);
lean_ctor_set_uint64(v_reuseFailAlloc_4305_, sizeof(void*)*1, v_tid_4291_);
v___x_4299_ = v_reuseFailAlloc_4305_;
goto v_reusejp_4298_;
}
v_reusejp_4298_:
{
lean_object* v___x_4301_; 
if (v_isShared_4290_ == 0)
{
lean_ctor_set(v___x_4289_, 4, v___x_4299_);
v___x_4301_ = v___x_4289_;
goto v_reusejp_4300_;
}
else
{
lean_object* v_reuseFailAlloc_4304_; 
v_reuseFailAlloc_4304_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4304_, 0, v_env_4279_);
lean_ctor_set(v_reuseFailAlloc_4304_, 1, v_nextMacroScope_4280_);
lean_ctor_set(v_reuseFailAlloc_4304_, 2, v_ngen_4281_);
lean_ctor_set(v_reuseFailAlloc_4304_, 3, v_auxDeclNGen_4282_);
lean_ctor_set(v_reuseFailAlloc_4304_, 4, v___x_4299_);
lean_ctor_set(v_reuseFailAlloc_4304_, 5, v_cache_4283_);
lean_ctor_set(v_reuseFailAlloc_4304_, 6, v_messages_4284_);
lean_ctor_set(v_reuseFailAlloc_4304_, 7, v_infoState_4285_);
lean_ctor_set(v_reuseFailAlloc_4304_, 8, v_snapshotTasks_4286_);
lean_ctor_set(v_reuseFailAlloc_4304_, 9, v_newDecls_4287_);
v___x_4301_ = v_reuseFailAlloc_4304_;
goto v_reusejp_4300_;
}
v_reusejp_4300_:
{
lean_object* v___x_4302_; lean_object* v___x_4303_; 
v___x_4302_ = lean_st_ref_set(v___y_4272_, v___x_4301_);
v___x_4303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4303_, 0, v_traces_4276_);
return v___x_4303_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__1___redArg___boxed(lean_object* v___y_4309_, lean_object* v___y_4310_){
_start:
{
lean_object* v_res_4311_; 
v_res_4311_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__1___redArg(v___y_4309_);
lean_dec(v___y_4309_);
return v_res_4311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__1(lean_object* v___y_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_){
_start:
{
lean_object* v___x_4319_; 
v___x_4319_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__1___redArg(v___y_4317_);
return v___x_4319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__1___boxed(lean_object* v___y_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_){
_start:
{
lean_object* v_res_4327_; 
v_res_4327_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__1(v___y_4320_, v___y_4321_, v___y_4322_, v___y_4323_, v___y_4324_, v___y_4325_);
lean_dec(v___y_4325_);
lean_dec_ref(v___y_4324_);
lean_dec(v___y_4323_);
lean_dec_ref(v___y_4322_);
lean_dec(v___y_4321_);
lean_dec_ref(v___y_4320_);
return v_res_4327_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___redArg___lam__0(lean_object* v_x_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_){
_start:
{
lean_object* v___x_4336_; 
lean_inc(v___y_4330_);
lean_inc_ref(v___y_4329_);
v___x_4336_ = lean_apply_7(v_x_4328_, v___y_4329_, v___y_4330_, v___y_4331_, v___y_4332_, v___y_4333_, v___y_4334_, lean_box(0));
return v___x_4336_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___redArg___lam__0___boxed(lean_object* v_x_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_){
_start:
{
lean_object* v_res_4345_; 
v_res_4345_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___redArg___lam__0(v_x_4337_, v___y_4338_, v___y_4339_, v___y_4340_, v___y_4341_, v___y_4342_, v___y_4343_);
lean_dec(v___y_4339_);
lean_dec_ref(v___y_4338_);
return v_res_4345_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___redArg(lean_object* v_mvarId_4346_, lean_object* v_x_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_){
_start:
{
lean_object* v___f_4355_; lean_object* v___x_4356_; 
lean_inc(v___y_4349_);
lean_inc_ref(v___y_4348_);
v___f_4355_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4355_, 0, v_x_4347_);
lean_closure_set(v___f_4355_, 1, v___y_4348_);
lean_closure_set(v___f_4355_, 2, v___y_4349_);
v___x_4356_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_4346_, v___f_4355_, v___y_4350_, v___y_4351_, v___y_4352_, v___y_4353_);
if (lean_obj_tag(v___x_4356_) == 0)
{
return v___x_4356_;
}
else
{
lean_object* v_a_4357_; lean_object* v___x_4359_; uint8_t v_isShared_4360_; uint8_t v_isSharedCheck_4364_; 
v_a_4357_ = lean_ctor_get(v___x_4356_, 0);
v_isSharedCheck_4364_ = !lean_is_exclusive(v___x_4356_);
if (v_isSharedCheck_4364_ == 0)
{
v___x_4359_ = v___x_4356_;
v_isShared_4360_ = v_isSharedCheck_4364_;
goto v_resetjp_4358_;
}
else
{
lean_inc(v_a_4357_);
lean_dec(v___x_4356_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___redArg___boxed(lean_object* v_mvarId_4365_, lean_object* v_x_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_){
_start:
{
lean_object* v_res_4374_; 
v_res_4374_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___redArg(v_mvarId_4365_, v_x_4366_, v___y_4367_, v___y_4368_, v___y_4369_, v___y_4370_, v___y_4371_, v___y_4372_);
lean_dec(v___y_4372_);
lean_dec_ref(v___y_4371_);
lean_dec(v___y_4370_);
lean_dec_ref(v___y_4369_);
lean_dec(v___y_4368_);
lean_dec_ref(v___y_4367_);
return v_res_4374_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4(lean_object* v_00_u03b1_4375_, lean_object* v_mvarId_4376_, lean_object* v_x_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_){
_start:
{
lean_object* v___x_4385_; 
v___x_4385_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___redArg(v_mvarId_4376_, v_x_4377_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_);
return v___x_4385_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___boxed(lean_object* v_00_u03b1_4386_, lean_object* v_mvarId_4387_, lean_object* v_x_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_){
_start:
{
lean_object* v_res_4396_; 
v_res_4396_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4(v_00_u03b1_4386_, v_mvarId_4387_, v_x_4388_, v___y_4389_, v___y_4390_, v___y_4391_, v___y_4392_, v___y_4393_, v___y_4394_);
lean_dec(v___y_4394_);
lean_dec_ref(v___y_4393_);
lean_dec(v___y_4392_);
lean_dec_ref(v___y_4391_);
lean_dec(v___y_4390_);
lean_dec_ref(v___y_4389_);
return v_res_4396_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4398_; lean_object* v___x_4399_; 
v___x_4398_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__0));
v___x_4399_ = l_Lean_stringToMessageData(v___x_4398_);
return v___x_4399_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4401_; lean_object* v___x_4402_; 
v___x_4401_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__2));
v___x_4402_ = l_Lean_stringToMessageData(v___x_4401_);
return v___x_4402_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4404_; lean_object* v___x_4405_; 
v___x_4404_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__4));
v___x_4405_ = l_Lean_stringToMessageData(v___x_4404_);
return v___x_4405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0(lean_object* v_a_4406_, lean_object* v_x_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_){
_start:
{
if (lean_obj_tag(v_x_4407_) == 0)
{
lean_object* v_a_4415_; lean_object* v___x_4417_; uint8_t v_isShared_4418_; uint8_t v_isSharedCheck_4425_; 
lean_dec_ref(v_a_4406_);
v_a_4415_ = lean_ctor_get(v_x_4407_, 0);
v_isSharedCheck_4425_ = !lean_is_exclusive(v_x_4407_);
if (v_isSharedCheck_4425_ == 0)
{
v___x_4417_ = v_x_4407_;
v_isShared_4418_ = v_isSharedCheck_4425_;
goto v_resetjp_4416_;
}
else
{
lean_inc(v_a_4415_);
lean_dec(v_x_4407_);
v___x_4417_ = lean_box(0);
v_isShared_4418_ = v_isSharedCheck_4425_;
goto v_resetjp_4416_;
}
v_resetjp_4416_:
{
lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4423_; 
v___x_4419_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__1);
v___x_4420_ = l_Lean_Exception_toMessageData(v_a_4415_);
v___x_4421_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4421_, 0, v___x_4419_);
lean_ctor_set(v___x_4421_, 1, v___x_4420_);
if (v_isShared_4418_ == 0)
{
lean_ctor_set(v___x_4417_, 0, v___x_4421_);
v___x_4423_ = v___x_4417_;
goto v_reusejp_4422_;
}
else
{
lean_object* v_reuseFailAlloc_4424_; 
v_reuseFailAlloc_4424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4424_, 0, v___x_4421_);
v___x_4423_ = v_reuseFailAlloc_4424_;
goto v_reusejp_4422_;
}
v_reusejp_4422_:
{
return v___x_4423_;
}
}
}
else
{
lean_object* v_a_4426_; lean_object* v___x_4428_; uint8_t v_isShared_4429_; uint8_t v_isSharedCheck_4445_; 
v_a_4426_ = lean_ctor_get(v_x_4407_, 0);
v_isSharedCheck_4445_ = !lean_is_exclusive(v_x_4407_);
if (v_isSharedCheck_4445_ == 0)
{
v___x_4428_ = v_x_4407_;
v_isShared_4429_ = v_isSharedCheck_4445_;
goto v_resetjp_4427_;
}
else
{
lean_inc(v_a_4426_);
lean_dec(v_x_4407_);
v___x_4428_ = lean_box(0);
v_isShared_4429_ = v_isSharedCheck_4445_;
goto v_resetjp_4427_;
}
v_resetjp_4427_:
{
if (lean_obj_tag(v_a_4426_) == 0)
{
lean_object* v___x_4430_; lean_object* v___x_4432_; 
lean_dec_ref(v_a_4426_);
lean_dec_ref(v_a_4406_);
v___x_4430_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__3, &l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__3);
if (v_isShared_4429_ == 0)
{
lean_ctor_set_tag(v___x_4428_, 0);
lean_ctor_set(v___x_4428_, 0, v___x_4430_);
v___x_4432_ = v___x_4428_;
goto v_reusejp_4431_;
}
else
{
lean_object* v_reuseFailAlloc_4433_; 
v_reuseFailAlloc_4433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4433_, 0, v___x_4430_);
v___x_4432_ = v_reuseFailAlloc_4433_;
goto v_reusejp_4431_;
}
v_reusejp_4431_:
{
return v___x_4432_;
}
}
else
{
lean_object* v_e_x27_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4443_; 
v_e_x27_4434_ = lean_ctor_get(v_a_4426_, 0);
lean_inc_ref(v_e_x27_4434_);
lean_dec_ref(v_a_4426_);
v___x_4435_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__5, &l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__5_once, _init_l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__5);
v___x_4436_ = l_Lean_indentExpr(v_a_4406_);
v___x_4437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4437_, 0, v___x_4435_);
lean_ctor_set(v___x_4437_, 1, v___x_4436_);
v___x_4438_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_4439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4439_, 0, v___x_4437_);
lean_ctor_set(v___x_4439_, 1, v___x_4438_);
v___x_4440_ = l_Lean_indentExpr(v_e_x27_4434_);
v___x_4441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4441_, 0, v___x_4439_);
lean_ctor_set(v___x_4441_, 1, v___x_4440_);
if (v_isShared_4429_ == 0)
{
lean_ctor_set_tag(v___x_4428_, 0);
lean_ctor_set(v___x_4428_, 0, v___x_4441_);
v___x_4443_ = v___x_4428_;
goto v_reusejp_4442_;
}
else
{
lean_object* v_reuseFailAlloc_4444_; 
v_reuseFailAlloc_4444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4444_, 0, v___x_4441_);
v___x_4443_ = v_reuseFailAlloc_4444_;
goto v_reusejp_4442_;
}
v_reusejp_4442_:
{
return v___x_4443_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___boxed(lean_object* v_a_4446_, lean_object* v_x_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_){
_start:
{
lean_object* v_res_4455_; 
v_res_4455_ = l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0(v_a_4446_, v_x_4447_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_);
lean_dec(v___y_4453_);
lean_dec_ref(v___y_4452_);
lean_dec(v___y_4451_);
lean_dec_ref(v___y_4450_);
lean_dec(v___y_4449_);
lean_dec_ref(v___y_4448_);
return v_res_4455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2_spec__3___redArg(lean_object* v_oldTraces_4456_, lean_object* v_data_4457_, lean_object* v_ref_4458_, lean_object* v_msg_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_){
_start:
{
lean_object* v_fileName_4465_; lean_object* v_fileMap_4466_; lean_object* v_options_4467_; lean_object* v_currRecDepth_4468_; lean_object* v_maxRecDepth_4469_; lean_object* v_ref_4470_; lean_object* v_currNamespace_4471_; lean_object* v_openDecls_4472_; lean_object* v_initHeartbeats_4473_; lean_object* v_maxHeartbeats_4474_; lean_object* v_quotContext_4475_; lean_object* v_currMacroScope_4476_; uint8_t v_diag_4477_; lean_object* v_cancelTk_x3f_4478_; uint8_t v_suppressElabErrors_4479_; lean_object* v_inheritedTraceOptions_4480_; lean_object* v___x_4481_; lean_object* v_traceState_4482_; lean_object* v_traces_4483_; lean_object* v_ref_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; size_t v_sz_4487_; size_t v___x_4488_; lean_object* v___x_4489_; lean_object* v_msg_4490_; lean_object* v___x_4491_; lean_object* v_a_4492_; lean_object* v___x_4494_; uint8_t v_isShared_4495_; uint8_t v_isSharedCheck_4530_; 
v_fileName_4465_ = lean_ctor_get(v___y_4462_, 0);
v_fileMap_4466_ = lean_ctor_get(v___y_4462_, 1);
v_options_4467_ = lean_ctor_get(v___y_4462_, 2);
v_currRecDepth_4468_ = lean_ctor_get(v___y_4462_, 3);
v_maxRecDepth_4469_ = lean_ctor_get(v___y_4462_, 4);
v_ref_4470_ = lean_ctor_get(v___y_4462_, 5);
v_currNamespace_4471_ = lean_ctor_get(v___y_4462_, 6);
v_openDecls_4472_ = lean_ctor_get(v___y_4462_, 7);
v_initHeartbeats_4473_ = lean_ctor_get(v___y_4462_, 8);
v_maxHeartbeats_4474_ = lean_ctor_get(v___y_4462_, 9);
v_quotContext_4475_ = lean_ctor_get(v___y_4462_, 10);
v_currMacroScope_4476_ = lean_ctor_get(v___y_4462_, 11);
v_diag_4477_ = lean_ctor_get_uint8(v___y_4462_, sizeof(void*)*14);
v_cancelTk_x3f_4478_ = lean_ctor_get(v___y_4462_, 12);
v_suppressElabErrors_4479_ = lean_ctor_get_uint8(v___y_4462_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_4480_ = lean_ctor_get(v___y_4462_, 13);
v___x_4481_ = lean_st_ref_get(v___y_4463_);
v_traceState_4482_ = lean_ctor_get(v___x_4481_, 4);
lean_inc_ref(v_traceState_4482_);
lean_dec(v___x_4481_);
v_traces_4483_ = lean_ctor_get(v_traceState_4482_, 0);
lean_inc_ref(v_traces_4483_);
lean_dec_ref(v_traceState_4482_);
v_ref_4484_ = l_Lean_replaceRef(v_ref_4458_, v_ref_4470_);
lean_inc_ref(v_inheritedTraceOptions_4480_);
lean_inc(v_cancelTk_x3f_4478_);
lean_inc(v_currMacroScope_4476_);
lean_inc(v_quotContext_4475_);
lean_inc(v_maxHeartbeats_4474_);
lean_inc(v_initHeartbeats_4473_);
lean_inc(v_openDecls_4472_);
lean_inc(v_currNamespace_4471_);
lean_inc(v_maxRecDepth_4469_);
lean_inc(v_currRecDepth_4468_);
lean_inc_ref(v_options_4467_);
lean_inc_ref(v_fileMap_4466_);
lean_inc_ref(v_fileName_4465_);
v___x_4485_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_4485_, 0, v_fileName_4465_);
lean_ctor_set(v___x_4485_, 1, v_fileMap_4466_);
lean_ctor_set(v___x_4485_, 2, v_options_4467_);
lean_ctor_set(v___x_4485_, 3, v_currRecDepth_4468_);
lean_ctor_set(v___x_4485_, 4, v_maxRecDepth_4469_);
lean_ctor_set(v___x_4485_, 5, v_ref_4484_);
lean_ctor_set(v___x_4485_, 6, v_currNamespace_4471_);
lean_ctor_set(v___x_4485_, 7, v_openDecls_4472_);
lean_ctor_set(v___x_4485_, 8, v_initHeartbeats_4473_);
lean_ctor_set(v___x_4485_, 9, v_maxHeartbeats_4474_);
lean_ctor_set(v___x_4485_, 10, v_quotContext_4475_);
lean_ctor_set(v___x_4485_, 11, v_currMacroScope_4476_);
lean_ctor_set(v___x_4485_, 12, v_cancelTk_x3f_4478_);
lean_ctor_set(v___x_4485_, 13, v_inheritedTraceOptions_4480_);
lean_ctor_set_uint8(v___x_4485_, sizeof(void*)*14, v_diag_4477_);
lean_ctor_set_uint8(v___x_4485_, sizeof(void*)*14 + 1, v_suppressElabErrors_4479_);
v___x_4486_ = l_Lean_PersistentArray_toArray___redArg(v_traces_4483_);
lean_dec_ref(v_traces_4483_);
v_sz_4487_ = lean_array_size(v___x_4486_);
v___x_4488_ = ((size_t)0ULL);
v___x_4489_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5_spec__6(v_sz_4487_, v___x_4488_, v___x_4486_);
v_msg_4490_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_4490_, 0, v_data_4457_);
lean_ctor_set(v_msg_4490_, 1, v_msg_4459_);
lean_ctor_set(v_msg_4490_, 2, v___x_4489_);
v___x_4491_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0_spec__0(v_msg_4490_, v___y_4460_, v___y_4461_, v___x_4485_, v___y_4463_);
lean_dec_ref(v___x_4485_);
v_a_4492_ = lean_ctor_get(v___x_4491_, 0);
v_isSharedCheck_4530_ = !lean_is_exclusive(v___x_4491_);
if (v_isSharedCheck_4530_ == 0)
{
v___x_4494_ = v___x_4491_;
v_isShared_4495_ = v_isSharedCheck_4530_;
goto v_resetjp_4493_;
}
else
{
lean_inc(v_a_4492_);
lean_dec(v___x_4491_);
v___x_4494_ = lean_box(0);
v_isShared_4495_ = v_isSharedCheck_4530_;
goto v_resetjp_4493_;
}
v_resetjp_4493_:
{
lean_object* v___x_4496_; lean_object* v_traceState_4497_; lean_object* v_env_4498_; lean_object* v_nextMacroScope_4499_; lean_object* v_ngen_4500_; lean_object* v_auxDeclNGen_4501_; lean_object* v_cache_4502_; lean_object* v_messages_4503_; lean_object* v_infoState_4504_; lean_object* v_snapshotTasks_4505_; lean_object* v_newDecls_4506_; lean_object* v___x_4508_; uint8_t v_isShared_4509_; uint8_t v_isSharedCheck_4529_; 
v___x_4496_ = lean_st_ref_take(v___y_4463_);
v_traceState_4497_ = lean_ctor_get(v___x_4496_, 4);
v_env_4498_ = lean_ctor_get(v___x_4496_, 0);
v_nextMacroScope_4499_ = lean_ctor_get(v___x_4496_, 1);
v_ngen_4500_ = lean_ctor_get(v___x_4496_, 2);
v_auxDeclNGen_4501_ = lean_ctor_get(v___x_4496_, 3);
v_cache_4502_ = lean_ctor_get(v___x_4496_, 5);
v_messages_4503_ = lean_ctor_get(v___x_4496_, 6);
v_infoState_4504_ = lean_ctor_get(v___x_4496_, 7);
v_snapshotTasks_4505_ = lean_ctor_get(v___x_4496_, 8);
v_newDecls_4506_ = lean_ctor_get(v___x_4496_, 9);
v_isSharedCheck_4529_ = !lean_is_exclusive(v___x_4496_);
if (v_isSharedCheck_4529_ == 0)
{
v___x_4508_ = v___x_4496_;
v_isShared_4509_ = v_isSharedCheck_4529_;
goto v_resetjp_4507_;
}
else
{
lean_inc(v_newDecls_4506_);
lean_inc(v_snapshotTasks_4505_);
lean_inc(v_infoState_4504_);
lean_inc(v_messages_4503_);
lean_inc(v_cache_4502_);
lean_inc(v_traceState_4497_);
lean_inc(v_auxDeclNGen_4501_);
lean_inc(v_ngen_4500_);
lean_inc(v_nextMacroScope_4499_);
lean_inc(v_env_4498_);
lean_dec(v___x_4496_);
v___x_4508_ = lean_box(0);
v_isShared_4509_ = v_isSharedCheck_4529_;
goto v_resetjp_4507_;
}
v_resetjp_4507_:
{
uint64_t v_tid_4510_; lean_object* v___x_4512_; uint8_t v_isShared_4513_; uint8_t v_isSharedCheck_4527_; 
v_tid_4510_ = lean_ctor_get_uint64(v_traceState_4497_, sizeof(void*)*1);
v_isSharedCheck_4527_ = !lean_is_exclusive(v_traceState_4497_);
if (v_isSharedCheck_4527_ == 0)
{
lean_object* v_unused_4528_; 
v_unused_4528_ = lean_ctor_get(v_traceState_4497_, 0);
lean_dec(v_unused_4528_);
v___x_4512_ = v_traceState_4497_;
v_isShared_4513_ = v_isSharedCheck_4527_;
goto v_resetjp_4511_;
}
else
{
lean_dec(v_traceState_4497_);
v___x_4512_ = lean_box(0);
v_isShared_4513_ = v_isSharedCheck_4527_;
goto v_resetjp_4511_;
}
v_resetjp_4511_:
{
lean_object* v___x_4514_; lean_object* v___x_4515_; lean_object* v___x_4517_; 
v___x_4514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4514_, 0, v_ref_4458_);
lean_ctor_set(v___x_4514_, 1, v_a_4492_);
v___x_4515_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_4456_, v___x_4514_);
if (v_isShared_4513_ == 0)
{
lean_ctor_set(v___x_4512_, 0, v___x_4515_);
v___x_4517_ = v___x_4512_;
goto v_reusejp_4516_;
}
else
{
lean_object* v_reuseFailAlloc_4526_; 
v_reuseFailAlloc_4526_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4526_, 0, v___x_4515_);
lean_ctor_set_uint64(v_reuseFailAlloc_4526_, sizeof(void*)*1, v_tid_4510_);
v___x_4517_ = v_reuseFailAlloc_4526_;
goto v_reusejp_4516_;
}
v_reusejp_4516_:
{
lean_object* v___x_4519_; 
if (v_isShared_4509_ == 0)
{
lean_ctor_set(v___x_4508_, 4, v___x_4517_);
v___x_4519_ = v___x_4508_;
goto v_reusejp_4518_;
}
else
{
lean_object* v_reuseFailAlloc_4525_; 
v_reuseFailAlloc_4525_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4525_, 0, v_env_4498_);
lean_ctor_set(v_reuseFailAlloc_4525_, 1, v_nextMacroScope_4499_);
lean_ctor_set(v_reuseFailAlloc_4525_, 2, v_ngen_4500_);
lean_ctor_set(v_reuseFailAlloc_4525_, 3, v_auxDeclNGen_4501_);
lean_ctor_set(v_reuseFailAlloc_4525_, 4, v___x_4517_);
lean_ctor_set(v_reuseFailAlloc_4525_, 5, v_cache_4502_);
lean_ctor_set(v_reuseFailAlloc_4525_, 6, v_messages_4503_);
lean_ctor_set(v_reuseFailAlloc_4525_, 7, v_infoState_4504_);
lean_ctor_set(v_reuseFailAlloc_4525_, 8, v_snapshotTasks_4505_);
lean_ctor_set(v_reuseFailAlloc_4525_, 9, v_newDecls_4506_);
v___x_4519_ = v_reuseFailAlloc_4525_;
goto v_reusejp_4518_;
}
v_reusejp_4518_:
{
lean_object* v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_4523_; 
v___x_4520_ = lean_st_ref_set(v___y_4463_, v___x_4519_);
v___x_4521_ = lean_box(0);
if (v_isShared_4495_ == 0)
{
lean_ctor_set(v___x_4494_, 0, v___x_4521_);
v___x_4523_ = v___x_4494_;
goto v_reusejp_4522_;
}
else
{
lean_object* v_reuseFailAlloc_4524_; 
v_reuseFailAlloc_4524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4524_, 0, v___x_4521_);
v___x_4523_ = v_reuseFailAlloc_4524_;
goto v_reusejp_4522_;
}
v_reusejp_4522_:
{
return v___x_4523_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2_spec__3___redArg___boxed(lean_object* v_oldTraces_4531_, lean_object* v_data_4532_, lean_object* v_ref_4533_, lean_object* v_msg_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_){
_start:
{
lean_object* v_res_4540_; 
v_res_4540_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2_spec__3___redArg(v_oldTraces_4531_, v_data_4532_, v_ref_4533_, v_msg_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_);
lean_dec(v___y_4538_);
lean_dec_ref(v___y_4537_);
lean_dec(v___y_4536_);
lean_dec_ref(v___y_4535_);
return v_res_4540_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2_spec__4___redArg(lean_object* v_x_4541_){
_start:
{
if (lean_obj_tag(v_x_4541_) == 0)
{
lean_object* v_a_4543_; lean_object* v___x_4545_; uint8_t v_isShared_4546_; uint8_t v_isSharedCheck_4550_; 
v_a_4543_ = lean_ctor_get(v_x_4541_, 0);
v_isSharedCheck_4550_ = !lean_is_exclusive(v_x_4541_);
if (v_isSharedCheck_4550_ == 0)
{
v___x_4545_ = v_x_4541_;
v_isShared_4546_ = v_isSharedCheck_4550_;
goto v_resetjp_4544_;
}
else
{
lean_inc(v_a_4543_);
lean_dec(v_x_4541_);
v___x_4545_ = lean_box(0);
v_isShared_4546_ = v_isSharedCheck_4550_;
goto v_resetjp_4544_;
}
v_resetjp_4544_:
{
lean_object* v___x_4548_; 
if (v_isShared_4546_ == 0)
{
lean_ctor_set_tag(v___x_4545_, 1);
v___x_4548_ = v___x_4545_;
goto v_reusejp_4547_;
}
else
{
lean_object* v_reuseFailAlloc_4549_; 
v_reuseFailAlloc_4549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4549_, 0, v_a_4543_);
v___x_4548_ = v_reuseFailAlloc_4549_;
goto v_reusejp_4547_;
}
v_reusejp_4547_:
{
return v___x_4548_;
}
}
}
else
{
lean_object* v_a_4551_; lean_object* v___x_4553_; uint8_t v_isShared_4554_; uint8_t v_isSharedCheck_4558_; 
v_a_4551_ = lean_ctor_get(v_x_4541_, 0);
v_isSharedCheck_4558_ = !lean_is_exclusive(v_x_4541_);
if (v_isSharedCheck_4558_ == 0)
{
v___x_4553_ = v_x_4541_;
v_isShared_4554_ = v_isSharedCheck_4558_;
goto v_resetjp_4552_;
}
else
{
lean_inc(v_a_4551_);
lean_dec(v_x_4541_);
v___x_4553_ = lean_box(0);
v_isShared_4554_ = v_isSharedCheck_4558_;
goto v_resetjp_4552_;
}
v_resetjp_4552_:
{
lean_object* v___x_4556_; 
if (v_isShared_4554_ == 0)
{
lean_ctor_set_tag(v___x_4553_, 0);
v___x_4556_ = v___x_4553_;
goto v_reusejp_4555_;
}
else
{
lean_object* v_reuseFailAlloc_4557_; 
v_reuseFailAlloc_4557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4557_, 0, v_a_4551_);
v___x_4556_ = v_reuseFailAlloc_4557_;
goto v_reusejp_4555_;
}
v_reusejp_4555_:
{
return v___x_4556_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2_spec__4___redArg___boxed(lean_object* v_x_4559_, lean_object* v___y_4560_){
_start:
{
lean_object* v_res_4561_; 
v_res_4561_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2_spec__4___redArg(v_x_4559_);
return v_res_4561_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2(lean_object* v_cls_4562_, uint8_t v_collapsed_4563_, lean_object* v_tag_4564_, lean_object* v_opts_4565_, uint8_t v_clsEnabled_4566_, lean_object* v_oldTraces_4567_, lean_object* v_msg_4568_, lean_object* v_resStartStop_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_){
_start:
{
lean_object* v_fst_4577_; lean_object* v_snd_4578_; lean_object* v___x_4580_; uint8_t v_isShared_4581_; uint8_t v_isSharedCheck_4677_; 
v_fst_4577_ = lean_ctor_get(v_resStartStop_4569_, 0);
v_snd_4578_ = lean_ctor_get(v_resStartStop_4569_, 1);
v_isSharedCheck_4677_ = !lean_is_exclusive(v_resStartStop_4569_);
if (v_isSharedCheck_4677_ == 0)
{
v___x_4580_ = v_resStartStop_4569_;
v_isShared_4581_ = v_isSharedCheck_4677_;
goto v_resetjp_4579_;
}
else
{
lean_inc(v_snd_4578_);
lean_inc(v_fst_4577_);
lean_dec(v_resStartStop_4569_);
v___x_4580_ = lean_box(0);
v_isShared_4581_ = v_isSharedCheck_4677_;
goto v_resetjp_4579_;
}
v_resetjp_4579_:
{
lean_object* v___y_4583_; lean_object* v___y_4584_; lean_object* v_data_4585_; lean_object* v_fst_4596_; lean_object* v_snd_4597_; lean_object* v___x_4599_; uint8_t v_isShared_4600_; uint8_t v_isSharedCheck_4676_; 
v_fst_4596_ = lean_ctor_get(v_snd_4578_, 0);
v_snd_4597_ = lean_ctor_get(v_snd_4578_, 1);
v_isSharedCheck_4676_ = !lean_is_exclusive(v_snd_4578_);
if (v_isSharedCheck_4676_ == 0)
{
v___x_4599_ = v_snd_4578_;
v_isShared_4600_ = v_isSharedCheck_4676_;
goto v_resetjp_4598_;
}
else
{
lean_inc(v_snd_4597_);
lean_inc(v_fst_4596_);
lean_dec(v_snd_4578_);
v___x_4599_ = lean_box(0);
v_isShared_4600_ = v_isSharedCheck_4676_;
goto v_resetjp_4598_;
}
v___jp_4582_:
{
lean_object* v___x_4586_; 
lean_inc(v___y_4584_);
v___x_4586_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2_spec__3___redArg(v_oldTraces_4567_, v_data_4585_, v___y_4584_, v___y_4583_, v___y_4572_, v___y_4573_, v___y_4574_, v___y_4575_);
if (lean_obj_tag(v___x_4586_) == 0)
{
lean_object* v___x_4587_; 
lean_dec_ref(v___x_4586_);
v___x_4587_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2_spec__4___redArg(v_fst_4577_);
return v___x_4587_;
}
else
{
lean_object* v_a_4588_; lean_object* v___x_4590_; uint8_t v_isShared_4591_; uint8_t v_isSharedCheck_4595_; 
lean_dec(v_fst_4577_);
v_a_4588_ = lean_ctor_get(v___x_4586_, 0);
v_isSharedCheck_4595_ = !lean_is_exclusive(v___x_4586_);
if (v_isSharedCheck_4595_ == 0)
{
v___x_4590_ = v___x_4586_;
v_isShared_4591_ = v_isSharedCheck_4595_;
goto v_resetjp_4589_;
}
else
{
lean_inc(v_a_4588_);
lean_dec(v___x_4586_);
v___x_4590_ = lean_box(0);
v_isShared_4591_ = v_isSharedCheck_4595_;
goto v_resetjp_4589_;
}
v_resetjp_4589_:
{
lean_object* v___x_4593_; 
if (v_isShared_4591_ == 0)
{
v___x_4593_ = v___x_4590_;
goto v_reusejp_4592_;
}
else
{
lean_object* v_reuseFailAlloc_4594_; 
v_reuseFailAlloc_4594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4594_, 0, v_a_4588_);
v___x_4593_ = v_reuseFailAlloc_4594_;
goto v_reusejp_4592_;
}
v_reusejp_4592_:
{
return v___x_4593_;
}
}
}
}
v_resetjp_4598_:
{
lean_object* v___x_4601_; uint8_t v___x_4602_; lean_object* v___y_4604_; lean_object* v_a_4605_; uint8_t v___y_4629_; double v___y_4661_; 
v___x_4601_ = l_Lean_trace_profiler;
v___x_4602_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_4565_, v___x_4601_);
if (v___x_4602_ == 0)
{
v___y_4629_ = v___x_4602_;
goto v___jp_4628_;
}
else
{
lean_object* v___x_4666_; uint8_t v___x_4667_; 
v___x_4666_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4667_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_4565_, v___x_4666_);
if (v___x_4667_ == 0)
{
lean_object* v___x_4668_; lean_object* v___x_4669_; double v___x_4670_; double v___x_4671_; double v___x_4672_; 
v___x_4668_ = l_Lean_trace_profiler_threshold;
v___x_4669_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_4565_, v___x_4668_);
v___x_4670_ = lean_float_of_nat(v___x_4669_);
v___x_4671_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__4);
v___x_4672_ = lean_float_div(v___x_4670_, v___x_4671_);
v___y_4661_ = v___x_4672_;
goto v___jp_4660_;
}
else
{
lean_object* v___x_4673_; lean_object* v___x_4674_; double v___x_4675_; 
v___x_4673_ = l_Lean_trace_profiler_threshold;
v___x_4674_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_4565_, v___x_4673_);
v___x_4675_ = lean_float_of_nat(v___x_4674_);
v___y_4661_ = v___x_4675_;
goto v___jp_4660_;
}
}
v___jp_4603_:
{
uint8_t v_result_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4611_; 
v_result_4606_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4(v_fst_4577_);
v___x_4607_ = l_Lean_TraceResult_toEmoji(v_result_4606_);
v___x_4608_ = l_Lean_stringToMessageData(v___x_4607_);
v___x_4609_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1);
if (v_isShared_4600_ == 0)
{
lean_ctor_set_tag(v___x_4599_, 7);
lean_ctor_set(v___x_4599_, 1, v___x_4609_);
lean_ctor_set(v___x_4599_, 0, v___x_4608_);
v___x_4611_ = v___x_4599_;
goto v_reusejp_4610_;
}
else
{
lean_object* v_reuseFailAlloc_4622_; 
v_reuseFailAlloc_4622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4622_, 0, v___x_4608_);
lean_ctor_set(v_reuseFailAlloc_4622_, 1, v___x_4609_);
v___x_4611_ = v_reuseFailAlloc_4622_;
goto v_reusejp_4610_;
}
v_reusejp_4610_:
{
lean_object* v_m_4613_; 
if (v_isShared_4581_ == 0)
{
lean_ctor_set_tag(v___x_4580_, 7);
lean_ctor_set(v___x_4580_, 1, v_a_4605_);
lean_ctor_set(v___x_4580_, 0, v___x_4611_);
v_m_4613_ = v___x_4580_;
goto v_reusejp_4612_;
}
else
{
lean_object* v_reuseFailAlloc_4621_; 
v_reuseFailAlloc_4621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4621_, 0, v___x_4611_);
lean_ctor_set(v_reuseFailAlloc_4621_, 1, v_a_4605_);
v_m_4613_ = v_reuseFailAlloc_4621_;
goto v_reusejp_4612_;
}
v_reusejp_4612_:
{
lean_object* v___x_4614_; lean_object* v___x_4615_; double v___x_4616_; lean_object* v_data_4617_; 
v___x_4614_ = lean_box(v_result_4606_);
v___x_4615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4615_, 0, v___x_4614_);
v___x_4616_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_4564_);
lean_inc_ref(v___x_4615_);
lean_inc(v_cls_4562_);
v_data_4617_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4617_, 0, v_cls_4562_);
lean_ctor_set(v_data_4617_, 1, v___x_4615_);
lean_ctor_set(v_data_4617_, 2, v_tag_4564_);
lean_ctor_set_float(v_data_4617_, sizeof(void*)*3, v___x_4616_);
lean_ctor_set_float(v_data_4617_, sizeof(void*)*3 + 8, v___x_4616_);
lean_ctor_set_uint8(v_data_4617_, sizeof(void*)*3 + 16, v_collapsed_4563_);
if (v___x_4602_ == 0)
{
lean_dec_ref(v___x_4615_);
lean_dec(v_snd_4597_);
lean_dec(v_fst_4596_);
lean_dec_ref(v_tag_4564_);
lean_dec(v_cls_4562_);
v___y_4583_ = v_m_4613_;
v___y_4584_ = v___y_4604_;
v_data_4585_ = v_data_4617_;
goto v___jp_4582_;
}
else
{
lean_object* v_data_4618_; double v___x_4619_; double v___x_4620_; 
lean_dec_ref(v_data_4617_);
v_data_4618_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4618_, 0, v_cls_4562_);
lean_ctor_set(v_data_4618_, 1, v___x_4615_);
lean_ctor_set(v_data_4618_, 2, v_tag_4564_);
v___x_4619_ = lean_unbox_float(v_fst_4596_);
lean_dec(v_fst_4596_);
lean_ctor_set_float(v_data_4618_, sizeof(void*)*3, v___x_4619_);
v___x_4620_ = lean_unbox_float(v_snd_4597_);
lean_dec(v_snd_4597_);
lean_ctor_set_float(v_data_4618_, sizeof(void*)*3 + 8, v___x_4620_);
lean_ctor_set_uint8(v_data_4618_, sizeof(void*)*3 + 16, v_collapsed_4563_);
v___y_4583_ = v_m_4613_;
v___y_4584_ = v___y_4604_;
v_data_4585_ = v_data_4618_;
goto v___jp_4582_;
}
}
}
}
v___jp_4623_:
{
lean_object* v_ref_4624_; lean_object* v___x_4625_; 
v_ref_4624_ = lean_ctor_get(v___y_4574_, 5);
lean_inc(v___y_4575_);
lean_inc_ref(v___y_4574_);
lean_inc(v___y_4573_);
lean_inc_ref(v___y_4572_);
lean_inc(v___y_4571_);
lean_inc_ref(v___y_4570_);
lean_inc(v_fst_4577_);
v___x_4625_ = lean_apply_8(v_msg_4568_, v_fst_4577_, v___y_4570_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4574_, v___y_4575_, lean_box(0));
if (lean_obj_tag(v___x_4625_) == 0)
{
lean_object* v_a_4626_; 
v_a_4626_ = lean_ctor_get(v___x_4625_, 0);
lean_inc(v_a_4626_);
lean_dec_ref(v___x_4625_);
v___y_4604_ = v_ref_4624_;
v_a_4605_ = v_a_4626_;
goto v___jp_4603_;
}
else
{
lean_object* v___x_4627_; 
lean_dec_ref(v___x_4625_);
v___x_4627_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__3);
v___y_4604_ = v_ref_4624_;
v_a_4605_ = v___x_4627_;
goto v___jp_4603_;
}
}
v___jp_4628_:
{
if (v_clsEnabled_4566_ == 0)
{
if (v___y_4629_ == 0)
{
lean_object* v___x_4630_; lean_object* v_traceState_4631_; lean_object* v_env_4632_; lean_object* v_nextMacroScope_4633_; lean_object* v_ngen_4634_; lean_object* v_auxDeclNGen_4635_; lean_object* v_cache_4636_; lean_object* v_messages_4637_; lean_object* v_infoState_4638_; lean_object* v_snapshotTasks_4639_; lean_object* v_newDecls_4640_; lean_object* v___x_4642_; uint8_t v_isShared_4643_; uint8_t v_isSharedCheck_4659_; 
lean_del_object(v___x_4599_);
lean_dec(v_snd_4597_);
lean_dec(v_fst_4596_);
lean_del_object(v___x_4580_);
lean_dec_ref(v_msg_4568_);
lean_dec_ref(v_tag_4564_);
lean_dec(v_cls_4562_);
v___x_4630_ = lean_st_ref_take(v___y_4575_);
v_traceState_4631_ = lean_ctor_get(v___x_4630_, 4);
v_env_4632_ = lean_ctor_get(v___x_4630_, 0);
v_nextMacroScope_4633_ = lean_ctor_get(v___x_4630_, 1);
v_ngen_4634_ = lean_ctor_get(v___x_4630_, 2);
v_auxDeclNGen_4635_ = lean_ctor_get(v___x_4630_, 3);
v_cache_4636_ = lean_ctor_get(v___x_4630_, 5);
v_messages_4637_ = lean_ctor_get(v___x_4630_, 6);
v_infoState_4638_ = lean_ctor_get(v___x_4630_, 7);
v_snapshotTasks_4639_ = lean_ctor_get(v___x_4630_, 8);
v_newDecls_4640_ = lean_ctor_get(v___x_4630_, 9);
v_isSharedCheck_4659_ = !lean_is_exclusive(v___x_4630_);
if (v_isSharedCheck_4659_ == 0)
{
v___x_4642_ = v___x_4630_;
v_isShared_4643_ = v_isSharedCheck_4659_;
goto v_resetjp_4641_;
}
else
{
lean_inc(v_newDecls_4640_);
lean_inc(v_snapshotTasks_4639_);
lean_inc(v_infoState_4638_);
lean_inc(v_messages_4637_);
lean_inc(v_cache_4636_);
lean_inc(v_traceState_4631_);
lean_inc(v_auxDeclNGen_4635_);
lean_inc(v_ngen_4634_);
lean_inc(v_nextMacroScope_4633_);
lean_inc(v_env_4632_);
lean_dec(v___x_4630_);
v___x_4642_ = lean_box(0);
v_isShared_4643_ = v_isSharedCheck_4659_;
goto v_resetjp_4641_;
}
v_resetjp_4641_:
{
uint64_t v_tid_4644_; lean_object* v_traces_4645_; lean_object* v___x_4647_; uint8_t v_isShared_4648_; uint8_t v_isSharedCheck_4658_; 
v_tid_4644_ = lean_ctor_get_uint64(v_traceState_4631_, sizeof(void*)*1);
v_traces_4645_ = lean_ctor_get(v_traceState_4631_, 0);
v_isSharedCheck_4658_ = !lean_is_exclusive(v_traceState_4631_);
if (v_isSharedCheck_4658_ == 0)
{
v___x_4647_ = v_traceState_4631_;
v_isShared_4648_ = v_isSharedCheck_4658_;
goto v_resetjp_4646_;
}
else
{
lean_inc(v_traces_4645_);
lean_dec(v_traceState_4631_);
v___x_4647_ = lean_box(0);
v_isShared_4648_ = v_isSharedCheck_4658_;
goto v_resetjp_4646_;
}
v_resetjp_4646_:
{
lean_object* v___x_4649_; lean_object* v___x_4651_; 
v___x_4649_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_4567_, v_traces_4645_);
lean_dec_ref(v_traces_4645_);
if (v_isShared_4648_ == 0)
{
lean_ctor_set(v___x_4647_, 0, v___x_4649_);
v___x_4651_ = v___x_4647_;
goto v_reusejp_4650_;
}
else
{
lean_object* v_reuseFailAlloc_4657_; 
v_reuseFailAlloc_4657_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4657_, 0, v___x_4649_);
lean_ctor_set_uint64(v_reuseFailAlloc_4657_, sizeof(void*)*1, v_tid_4644_);
v___x_4651_ = v_reuseFailAlloc_4657_;
goto v_reusejp_4650_;
}
v_reusejp_4650_:
{
lean_object* v___x_4653_; 
if (v_isShared_4643_ == 0)
{
lean_ctor_set(v___x_4642_, 4, v___x_4651_);
v___x_4653_ = v___x_4642_;
goto v_reusejp_4652_;
}
else
{
lean_object* v_reuseFailAlloc_4656_; 
v_reuseFailAlloc_4656_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4656_, 0, v_env_4632_);
lean_ctor_set(v_reuseFailAlloc_4656_, 1, v_nextMacroScope_4633_);
lean_ctor_set(v_reuseFailAlloc_4656_, 2, v_ngen_4634_);
lean_ctor_set(v_reuseFailAlloc_4656_, 3, v_auxDeclNGen_4635_);
lean_ctor_set(v_reuseFailAlloc_4656_, 4, v___x_4651_);
lean_ctor_set(v_reuseFailAlloc_4656_, 5, v_cache_4636_);
lean_ctor_set(v_reuseFailAlloc_4656_, 6, v_messages_4637_);
lean_ctor_set(v_reuseFailAlloc_4656_, 7, v_infoState_4638_);
lean_ctor_set(v_reuseFailAlloc_4656_, 8, v_snapshotTasks_4639_);
lean_ctor_set(v_reuseFailAlloc_4656_, 9, v_newDecls_4640_);
v___x_4653_ = v_reuseFailAlloc_4656_;
goto v_reusejp_4652_;
}
v_reusejp_4652_:
{
lean_object* v___x_4654_; lean_object* v___x_4655_; 
v___x_4654_ = lean_st_ref_set(v___y_4575_, v___x_4653_);
v___x_4655_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2_spec__4___redArg(v_fst_4577_);
return v___x_4655_;
}
}
}
}
}
else
{
goto v___jp_4623_;
}
}
else
{
goto v___jp_4623_;
}
}
v___jp_4660_:
{
double v___x_4662_; double v___x_4663_; double v___x_4664_; uint8_t v___x_4665_; 
v___x_4662_ = lean_unbox_float(v_snd_4597_);
v___x_4663_ = lean_unbox_float(v_fst_4596_);
v___x_4664_ = lean_float_sub(v___x_4662_, v___x_4663_);
v___x_4665_ = lean_float_decLt(v___y_4661_, v___x_4664_);
v___y_4629_ = v___x_4665_;
goto v___jp_4628_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2___boxed(lean_object* v_cls_4678_, lean_object* v_collapsed_4679_, lean_object* v_tag_4680_, lean_object* v_opts_4681_, lean_object* v_clsEnabled_4682_, lean_object* v_oldTraces_4683_, lean_object* v_msg_4684_, lean_object* v_resStartStop_4685_, lean_object* v___y_4686_, lean_object* v___y_4687_, lean_object* v___y_4688_, lean_object* v___y_4689_, lean_object* v___y_4690_, lean_object* v___y_4691_, lean_object* v___y_4692_){
_start:
{
uint8_t v_collapsed_boxed_4693_; uint8_t v_clsEnabled_boxed_4694_; lean_object* v_res_4695_; 
v_collapsed_boxed_4693_ = lean_unbox(v_collapsed_4679_);
v_clsEnabled_boxed_4694_ = lean_unbox(v_clsEnabled_4682_);
v_res_4695_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2(v_cls_4678_, v_collapsed_boxed_4693_, v_tag_4680_, v_opts_4681_, v_clsEnabled_boxed_4694_, v_oldTraces_4683_, v_msg_4684_, v_resStartStop_4685_, v___y_4686_, v___y_4687_, v___y_4688_, v___y_4689_, v___y_4690_, v___y_4691_);
lean_dec(v___y_4691_);
lean_dec_ref(v___y_4690_);
lean_dec(v___y_4689_);
lean_dec_ref(v___y_4688_);
lean_dec(v___y_4687_);
lean_dec_ref(v___y_4686_);
lean_dec_ref(v_opts_4681_);
return v_res_4695_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3_spec__7_spec__9___redArg(lean_object* v_x_4696_, lean_object* v_x_4697_, lean_object* v_x_4698_, lean_object* v_x_4699_){
_start:
{
lean_object* v_ks_4700_; lean_object* v_vs_4701_; lean_object* v___x_4703_; uint8_t v_isShared_4704_; uint8_t v_isSharedCheck_4725_; 
v_ks_4700_ = lean_ctor_get(v_x_4696_, 0);
v_vs_4701_ = lean_ctor_get(v_x_4696_, 1);
v_isSharedCheck_4725_ = !lean_is_exclusive(v_x_4696_);
if (v_isSharedCheck_4725_ == 0)
{
v___x_4703_ = v_x_4696_;
v_isShared_4704_ = v_isSharedCheck_4725_;
goto v_resetjp_4702_;
}
else
{
lean_inc(v_vs_4701_);
lean_inc(v_ks_4700_);
lean_dec(v_x_4696_);
v___x_4703_ = lean_box(0);
v_isShared_4704_ = v_isSharedCheck_4725_;
goto v_resetjp_4702_;
}
v_resetjp_4702_:
{
lean_object* v___x_4705_; uint8_t v___x_4706_; 
v___x_4705_ = lean_array_get_size(v_ks_4700_);
v___x_4706_ = lean_nat_dec_lt(v_x_4697_, v___x_4705_);
if (v___x_4706_ == 0)
{
lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4710_; 
lean_dec(v_x_4697_);
v___x_4707_ = lean_array_push(v_ks_4700_, v_x_4698_);
v___x_4708_ = lean_array_push(v_vs_4701_, v_x_4699_);
if (v_isShared_4704_ == 0)
{
lean_ctor_set(v___x_4703_, 1, v___x_4708_);
lean_ctor_set(v___x_4703_, 0, v___x_4707_);
v___x_4710_ = v___x_4703_;
goto v_reusejp_4709_;
}
else
{
lean_object* v_reuseFailAlloc_4711_; 
v_reuseFailAlloc_4711_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4711_, 0, v___x_4707_);
lean_ctor_set(v_reuseFailAlloc_4711_, 1, v___x_4708_);
v___x_4710_ = v_reuseFailAlloc_4711_;
goto v_reusejp_4709_;
}
v_reusejp_4709_:
{
return v___x_4710_;
}
}
else
{
lean_object* v_k_x27_4712_; uint8_t v___x_4713_; 
v_k_x27_4712_ = lean_array_fget_borrowed(v_ks_4700_, v_x_4697_);
v___x_4713_ = l_Lean_instBEqMVarId_beq(v_x_4698_, v_k_x27_4712_);
if (v___x_4713_ == 0)
{
lean_object* v___x_4715_; 
if (v_isShared_4704_ == 0)
{
v___x_4715_ = v___x_4703_;
goto v_reusejp_4714_;
}
else
{
lean_object* v_reuseFailAlloc_4719_; 
v_reuseFailAlloc_4719_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4719_, 0, v_ks_4700_);
lean_ctor_set(v_reuseFailAlloc_4719_, 1, v_vs_4701_);
v___x_4715_ = v_reuseFailAlloc_4719_;
goto v_reusejp_4714_;
}
v_reusejp_4714_:
{
lean_object* v___x_4716_; lean_object* v___x_4717_; 
v___x_4716_ = lean_unsigned_to_nat(1u);
v___x_4717_ = lean_nat_add(v_x_4697_, v___x_4716_);
lean_dec(v_x_4697_);
v_x_4696_ = v___x_4715_;
v_x_4697_ = v___x_4717_;
goto _start;
}
}
else
{
lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4723_; 
v___x_4720_ = lean_array_fset(v_ks_4700_, v_x_4697_, v_x_4698_);
v___x_4721_ = lean_array_fset(v_vs_4701_, v_x_4697_, v_x_4699_);
lean_dec(v_x_4697_);
if (v_isShared_4704_ == 0)
{
lean_ctor_set(v___x_4703_, 1, v___x_4721_);
lean_ctor_set(v___x_4703_, 0, v___x_4720_);
v___x_4723_ = v___x_4703_;
goto v_reusejp_4722_;
}
else
{
lean_object* v_reuseFailAlloc_4724_; 
v_reuseFailAlloc_4724_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4724_, 0, v___x_4720_);
lean_ctor_set(v_reuseFailAlloc_4724_, 1, v___x_4721_);
v___x_4723_ = v_reuseFailAlloc_4724_;
goto v_reusejp_4722_;
}
v_reusejp_4722_:
{
return v___x_4723_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3_spec__7___redArg(lean_object* v_n_4726_, lean_object* v_k_4727_, lean_object* v_v_4728_){
_start:
{
lean_object* v___x_4729_; lean_object* v___x_4730_; 
v___x_4729_ = lean_unsigned_to_nat(0u);
v___x_4730_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3_spec__7_spec__9___redArg(v_n_4726_, v___x_4729_, v_k_4727_, v_v_4728_);
return v___x_4730_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3___redArg___closed__0(void){
_start:
{
size_t v___x_4731_; size_t v___x_4732_; size_t v___x_4733_; 
v___x_4731_ = ((size_t)5ULL);
v___x_4732_ = ((size_t)1ULL);
v___x_4733_ = lean_usize_shift_left(v___x_4732_, v___x_4731_);
return v___x_4733_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_4734_; size_t v___x_4735_; size_t v___x_4736_; 
v___x_4734_ = ((size_t)1ULL);
v___x_4735_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3___redArg___closed__0);
v___x_4736_ = lean_usize_sub(v___x_4735_, v___x_4734_);
return v___x_4736_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_4737_; 
v___x_4737_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_4737_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3___redArg(lean_object* v_x_4738_, size_t v_x_4739_, size_t v_x_4740_, lean_object* v_x_4741_, lean_object* v_x_4742_){
_start:
{
if (lean_obj_tag(v_x_4738_) == 0)
{
lean_object* v_es_4743_; size_t v___x_4744_; size_t v___x_4745_; size_t v___x_4746_; size_t v___x_4747_; lean_object* v_j_4748_; lean_object* v___x_4749_; uint8_t v___x_4750_; 
v_es_4743_ = lean_ctor_get(v_x_4738_, 0);
v___x_4744_ = ((size_t)5ULL);
v___x_4745_ = ((size_t)1ULL);
v___x_4746_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3___redArg___closed__1);
v___x_4747_ = lean_usize_land(v_x_4739_, v___x_4746_);
v_j_4748_ = lean_usize_to_nat(v___x_4747_);
v___x_4749_ = lean_array_get_size(v_es_4743_);
v___x_4750_ = lean_nat_dec_lt(v_j_4748_, v___x_4749_);
if (v___x_4750_ == 0)
{
lean_dec(v_j_4748_);
lean_dec(v_x_4742_);
lean_dec(v_x_4741_);
return v_x_4738_;
}
else
{
lean_object* v___x_4752_; uint8_t v_isShared_4753_; uint8_t v_isSharedCheck_4787_; 
lean_inc_ref(v_es_4743_);
v_isSharedCheck_4787_ = !lean_is_exclusive(v_x_4738_);
if (v_isSharedCheck_4787_ == 0)
{
lean_object* v_unused_4788_; 
v_unused_4788_ = lean_ctor_get(v_x_4738_, 0);
lean_dec(v_unused_4788_);
v___x_4752_ = v_x_4738_;
v_isShared_4753_ = v_isSharedCheck_4787_;
goto v_resetjp_4751_;
}
else
{
lean_dec(v_x_4738_);
v___x_4752_ = lean_box(0);
v_isShared_4753_ = v_isSharedCheck_4787_;
goto v_resetjp_4751_;
}
v_resetjp_4751_:
{
lean_object* v_v_4754_; lean_object* v___x_4755_; lean_object* v_xs_x27_4756_; lean_object* v___y_4758_; 
v_v_4754_ = lean_array_fget(v_es_4743_, v_j_4748_);
v___x_4755_ = lean_box(0);
v_xs_x27_4756_ = lean_array_fset(v_es_4743_, v_j_4748_, v___x_4755_);
switch(lean_obj_tag(v_v_4754_))
{
case 0:
{
lean_object* v_key_4763_; lean_object* v_val_4764_; lean_object* v___x_4766_; uint8_t v_isShared_4767_; uint8_t v_isSharedCheck_4774_; 
v_key_4763_ = lean_ctor_get(v_v_4754_, 0);
v_val_4764_ = lean_ctor_get(v_v_4754_, 1);
v_isSharedCheck_4774_ = !lean_is_exclusive(v_v_4754_);
if (v_isSharedCheck_4774_ == 0)
{
v___x_4766_ = v_v_4754_;
v_isShared_4767_ = v_isSharedCheck_4774_;
goto v_resetjp_4765_;
}
else
{
lean_inc(v_val_4764_);
lean_inc(v_key_4763_);
lean_dec(v_v_4754_);
v___x_4766_ = lean_box(0);
v_isShared_4767_ = v_isSharedCheck_4774_;
goto v_resetjp_4765_;
}
v_resetjp_4765_:
{
uint8_t v___x_4768_; 
v___x_4768_ = l_Lean_instBEqMVarId_beq(v_x_4741_, v_key_4763_);
if (v___x_4768_ == 0)
{
lean_object* v___x_4769_; lean_object* v___x_4770_; 
lean_del_object(v___x_4766_);
v___x_4769_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_4763_, v_val_4764_, v_x_4741_, v_x_4742_);
v___x_4770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4770_, 0, v___x_4769_);
v___y_4758_ = v___x_4770_;
goto v___jp_4757_;
}
else
{
lean_object* v___x_4772_; 
lean_dec(v_val_4764_);
lean_dec(v_key_4763_);
if (v_isShared_4767_ == 0)
{
lean_ctor_set(v___x_4766_, 1, v_x_4742_);
lean_ctor_set(v___x_4766_, 0, v_x_4741_);
v___x_4772_ = v___x_4766_;
goto v_reusejp_4771_;
}
else
{
lean_object* v_reuseFailAlloc_4773_; 
v_reuseFailAlloc_4773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4773_, 0, v_x_4741_);
lean_ctor_set(v_reuseFailAlloc_4773_, 1, v_x_4742_);
v___x_4772_ = v_reuseFailAlloc_4773_;
goto v_reusejp_4771_;
}
v_reusejp_4771_:
{
v___y_4758_ = v___x_4772_;
goto v___jp_4757_;
}
}
}
}
case 1:
{
lean_object* v_node_4775_; lean_object* v___x_4777_; uint8_t v_isShared_4778_; uint8_t v_isSharedCheck_4785_; 
v_node_4775_ = lean_ctor_get(v_v_4754_, 0);
v_isSharedCheck_4785_ = !lean_is_exclusive(v_v_4754_);
if (v_isSharedCheck_4785_ == 0)
{
v___x_4777_ = v_v_4754_;
v_isShared_4778_ = v_isSharedCheck_4785_;
goto v_resetjp_4776_;
}
else
{
lean_inc(v_node_4775_);
lean_dec(v_v_4754_);
v___x_4777_ = lean_box(0);
v_isShared_4778_ = v_isSharedCheck_4785_;
goto v_resetjp_4776_;
}
v_resetjp_4776_:
{
size_t v___x_4779_; size_t v___x_4780_; lean_object* v___x_4781_; lean_object* v___x_4783_; 
v___x_4779_ = lean_usize_shift_right(v_x_4739_, v___x_4744_);
v___x_4780_ = lean_usize_add(v_x_4740_, v___x_4745_);
v___x_4781_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3___redArg(v_node_4775_, v___x_4779_, v___x_4780_, v_x_4741_, v_x_4742_);
if (v_isShared_4778_ == 0)
{
lean_ctor_set(v___x_4777_, 0, v___x_4781_);
v___x_4783_ = v___x_4777_;
goto v_reusejp_4782_;
}
else
{
lean_object* v_reuseFailAlloc_4784_; 
v_reuseFailAlloc_4784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4784_, 0, v___x_4781_);
v___x_4783_ = v_reuseFailAlloc_4784_;
goto v_reusejp_4782_;
}
v_reusejp_4782_:
{
v___y_4758_ = v___x_4783_;
goto v___jp_4757_;
}
}
}
default: 
{
lean_object* v___x_4786_; 
v___x_4786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4786_, 0, v_x_4741_);
lean_ctor_set(v___x_4786_, 1, v_x_4742_);
v___y_4758_ = v___x_4786_;
goto v___jp_4757_;
}
}
v___jp_4757_:
{
lean_object* v___x_4759_; lean_object* v___x_4761_; 
v___x_4759_ = lean_array_fset(v_xs_x27_4756_, v_j_4748_, v___y_4758_);
lean_dec(v_j_4748_);
if (v_isShared_4753_ == 0)
{
lean_ctor_set(v___x_4752_, 0, v___x_4759_);
v___x_4761_ = v___x_4752_;
goto v_reusejp_4760_;
}
else
{
lean_object* v_reuseFailAlloc_4762_; 
v_reuseFailAlloc_4762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4762_, 0, v___x_4759_);
v___x_4761_ = v_reuseFailAlloc_4762_;
goto v_reusejp_4760_;
}
v_reusejp_4760_:
{
return v___x_4761_;
}
}
}
}
}
else
{
lean_object* v_ks_4789_; lean_object* v_vs_4790_; lean_object* v___x_4792_; uint8_t v_isShared_4793_; uint8_t v_isSharedCheck_4810_; 
v_ks_4789_ = lean_ctor_get(v_x_4738_, 0);
v_vs_4790_ = lean_ctor_get(v_x_4738_, 1);
v_isSharedCheck_4810_ = !lean_is_exclusive(v_x_4738_);
if (v_isSharedCheck_4810_ == 0)
{
v___x_4792_ = v_x_4738_;
v_isShared_4793_ = v_isSharedCheck_4810_;
goto v_resetjp_4791_;
}
else
{
lean_inc(v_vs_4790_);
lean_inc(v_ks_4789_);
lean_dec(v_x_4738_);
v___x_4792_ = lean_box(0);
v_isShared_4793_ = v_isSharedCheck_4810_;
goto v_resetjp_4791_;
}
v_resetjp_4791_:
{
lean_object* v___x_4795_; 
if (v_isShared_4793_ == 0)
{
v___x_4795_ = v___x_4792_;
goto v_reusejp_4794_;
}
else
{
lean_object* v_reuseFailAlloc_4809_; 
v_reuseFailAlloc_4809_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4809_, 0, v_ks_4789_);
lean_ctor_set(v_reuseFailAlloc_4809_, 1, v_vs_4790_);
v___x_4795_ = v_reuseFailAlloc_4809_;
goto v_reusejp_4794_;
}
v_reusejp_4794_:
{
lean_object* v_newNode_4796_; uint8_t v___y_4798_; size_t v___x_4804_; uint8_t v___x_4805_; 
v_newNode_4796_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3_spec__7___redArg(v___x_4795_, v_x_4741_, v_x_4742_);
v___x_4804_ = ((size_t)7ULL);
v___x_4805_ = lean_usize_dec_le(v___x_4804_, v_x_4740_);
if (v___x_4805_ == 0)
{
lean_object* v___x_4806_; lean_object* v___x_4807_; uint8_t v___x_4808_; 
v___x_4806_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4796_);
v___x_4807_ = lean_unsigned_to_nat(4u);
v___x_4808_ = lean_nat_dec_lt(v___x_4806_, v___x_4807_);
lean_dec(v___x_4806_);
v___y_4798_ = v___x_4808_;
goto v___jp_4797_;
}
else
{
v___y_4798_ = v___x_4805_;
goto v___jp_4797_;
}
v___jp_4797_:
{
if (v___y_4798_ == 0)
{
lean_object* v_ks_4799_; lean_object* v_vs_4800_; lean_object* v___x_4801_; lean_object* v___x_4802_; lean_object* v___x_4803_; 
v_ks_4799_ = lean_ctor_get(v_newNode_4796_, 0);
lean_inc_ref(v_ks_4799_);
v_vs_4800_ = lean_ctor_get(v_newNode_4796_, 1);
lean_inc_ref(v_vs_4800_);
lean_dec_ref(v_newNode_4796_);
v___x_4801_ = lean_unsigned_to_nat(0u);
v___x_4802_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3___redArg___closed__2);
v___x_4803_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3_spec__8___redArg(v_x_4740_, v_ks_4799_, v_vs_4800_, v___x_4801_, v___x_4802_);
lean_dec_ref(v_vs_4800_);
lean_dec_ref(v_ks_4799_);
return v___x_4803_;
}
else
{
return v_newNode_4796_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3_spec__8___redArg(size_t v_depth_4811_, lean_object* v_keys_4812_, lean_object* v_vals_4813_, lean_object* v_i_4814_, lean_object* v_entries_4815_){
_start:
{
lean_object* v___x_4816_; uint8_t v___x_4817_; 
v___x_4816_ = lean_array_get_size(v_keys_4812_);
v___x_4817_ = lean_nat_dec_lt(v_i_4814_, v___x_4816_);
if (v___x_4817_ == 0)
{
lean_dec(v_i_4814_);
return v_entries_4815_;
}
else
{
lean_object* v_k_4818_; lean_object* v_v_4819_; uint64_t v___x_4820_; size_t v_h_4821_; size_t v___x_4822_; lean_object* v___x_4823_; size_t v___x_4824_; size_t v___x_4825_; size_t v___x_4826_; size_t v_h_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; 
v_k_4818_ = lean_array_fget_borrowed(v_keys_4812_, v_i_4814_);
v_v_4819_ = lean_array_fget_borrowed(v_vals_4813_, v_i_4814_);
v___x_4820_ = l_Lean_instHashableMVarId_hash(v_k_4818_);
v_h_4821_ = lean_uint64_to_usize(v___x_4820_);
v___x_4822_ = ((size_t)5ULL);
v___x_4823_ = lean_unsigned_to_nat(1u);
v___x_4824_ = ((size_t)1ULL);
v___x_4825_ = lean_usize_sub(v_depth_4811_, v___x_4824_);
v___x_4826_ = lean_usize_mul(v___x_4822_, v___x_4825_);
v_h_4827_ = lean_usize_shift_right(v_h_4821_, v___x_4826_);
v___x_4828_ = lean_nat_add(v_i_4814_, v___x_4823_);
lean_dec(v_i_4814_);
lean_inc(v_v_4819_);
lean_inc(v_k_4818_);
v___x_4829_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3___redArg(v_entries_4815_, v_h_4827_, v_depth_4811_, v_k_4818_, v_v_4819_);
v_i_4814_ = v___x_4828_;
v_entries_4815_ = v___x_4829_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3_spec__8___redArg___boxed(lean_object* v_depth_4831_, lean_object* v_keys_4832_, lean_object* v_vals_4833_, lean_object* v_i_4834_, lean_object* v_entries_4835_){
_start:
{
size_t v_depth_boxed_4836_; lean_object* v_res_4837_; 
v_depth_boxed_4836_ = lean_unbox_usize(v_depth_4831_);
lean_dec(v_depth_4831_);
v_res_4837_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3_spec__8___redArg(v_depth_boxed_4836_, v_keys_4832_, v_vals_4833_, v_i_4834_, v_entries_4835_);
lean_dec_ref(v_vals_4833_);
lean_dec_ref(v_keys_4832_);
return v_res_4837_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_x_4838_, lean_object* v_x_4839_, lean_object* v_x_4840_, lean_object* v_x_4841_, lean_object* v_x_4842_){
_start:
{
size_t v_x_48813__boxed_4843_; size_t v_x_48814__boxed_4844_; lean_object* v_res_4845_; 
v_x_48813__boxed_4843_ = lean_unbox_usize(v_x_4839_);
lean_dec(v_x_4839_);
v_x_48814__boxed_4844_ = lean_unbox_usize(v_x_4840_);
lean_dec(v_x_4840_);
v_res_4845_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3___redArg(v_x_4838_, v_x_48813__boxed_4843_, v_x_48814__boxed_4844_, v_x_4841_, v_x_4842_);
return v_res_4845_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0___redArg(lean_object* v_x_4846_, lean_object* v_x_4847_, lean_object* v_x_4848_){
_start:
{
uint64_t v___x_4849_; size_t v___x_4850_; size_t v___x_4851_; lean_object* v___x_4852_; 
v___x_4849_ = l_Lean_instHashableMVarId_hash(v_x_4847_);
v___x_4850_ = lean_uint64_to_usize(v___x_4849_);
v___x_4851_ = ((size_t)1ULL);
v___x_4852_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3___redArg(v_x_4846_, v___x_4850_, v___x_4851_, v_x_4847_, v_x_4848_);
return v___x_4852_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0___redArg(lean_object* v_mvarId_4853_, lean_object* v_val_4854_, lean_object* v___y_4855_){
_start:
{
lean_object* v___x_4857_; lean_object* v_mctx_4858_; lean_object* v_cache_4859_; lean_object* v_zetaDeltaFVarIds_4860_; lean_object* v_postponed_4861_; lean_object* v_diag_4862_; lean_object* v___x_4864_; uint8_t v_isShared_4865_; uint8_t v_isSharedCheck_4890_; 
v___x_4857_ = lean_st_ref_take(v___y_4855_);
v_mctx_4858_ = lean_ctor_get(v___x_4857_, 0);
v_cache_4859_ = lean_ctor_get(v___x_4857_, 1);
v_zetaDeltaFVarIds_4860_ = lean_ctor_get(v___x_4857_, 2);
v_postponed_4861_ = lean_ctor_get(v___x_4857_, 3);
v_diag_4862_ = lean_ctor_get(v___x_4857_, 4);
v_isSharedCheck_4890_ = !lean_is_exclusive(v___x_4857_);
if (v_isSharedCheck_4890_ == 0)
{
v___x_4864_ = v___x_4857_;
v_isShared_4865_ = v_isSharedCheck_4890_;
goto v_resetjp_4863_;
}
else
{
lean_inc(v_diag_4862_);
lean_inc(v_postponed_4861_);
lean_inc(v_zetaDeltaFVarIds_4860_);
lean_inc(v_cache_4859_);
lean_inc(v_mctx_4858_);
lean_dec(v___x_4857_);
v___x_4864_ = lean_box(0);
v_isShared_4865_ = v_isSharedCheck_4890_;
goto v_resetjp_4863_;
}
v_resetjp_4863_:
{
lean_object* v_depth_4866_; lean_object* v_levelAssignDepth_4867_; lean_object* v_lmvarCounter_4868_; lean_object* v_mvarCounter_4869_; lean_object* v_lDecls_4870_; lean_object* v_decls_4871_; lean_object* v_userNames_4872_; lean_object* v_lAssignment_4873_; lean_object* v_eAssignment_4874_; lean_object* v_dAssignment_4875_; lean_object* v___x_4877_; uint8_t v_isShared_4878_; uint8_t v_isSharedCheck_4889_; 
v_depth_4866_ = lean_ctor_get(v_mctx_4858_, 0);
v_levelAssignDepth_4867_ = lean_ctor_get(v_mctx_4858_, 1);
v_lmvarCounter_4868_ = lean_ctor_get(v_mctx_4858_, 2);
v_mvarCounter_4869_ = lean_ctor_get(v_mctx_4858_, 3);
v_lDecls_4870_ = lean_ctor_get(v_mctx_4858_, 4);
v_decls_4871_ = lean_ctor_get(v_mctx_4858_, 5);
v_userNames_4872_ = lean_ctor_get(v_mctx_4858_, 6);
v_lAssignment_4873_ = lean_ctor_get(v_mctx_4858_, 7);
v_eAssignment_4874_ = lean_ctor_get(v_mctx_4858_, 8);
v_dAssignment_4875_ = lean_ctor_get(v_mctx_4858_, 9);
v_isSharedCheck_4889_ = !lean_is_exclusive(v_mctx_4858_);
if (v_isSharedCheck_4889_ == 0)
{
v___x_4877_ = v_mctx_4858_;
v_isShared_4878_ = v_isSharedCheck_4889_;
goto v_resetjp_4876_;
}
else
{
lean_inc(v_dAssignment_4875_);
lean_inc(v_eAssignment_4874_);
lean_inc(v_lAssignment_4873_);
lean_inc(v_userNames_4872_);
lean_inc(v_decls_4871_);
lean_inc(v_lDecls_4870_);
lean_inc(v_mvarCounter_4869_);
lean_inc(v_lmvarCounter_4868_);
lean_inc(v_levelAssignDepth_4867_);
lean_inc(v_depth_4866_);
lean_dec(v_mctx_4858_);
v___x_4877_ = lean_box(0);
v_isShared_4878_ = v_isSharedCheck_4889_;
goto v_resetjp_4876_;
}
v_resetjp_4876_:
{
lean_object* v___x_4879_; lean_object* v___x_4881_; 
v___x_4879_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0___redArg(v_eAssignment_4874_, v_mvarId_4853_, v_val_4854_);
if (v_isShared_4878_ == 0)
{
lean_ctor_set(v___x_4877_, 8, v___x_4879_);
v___x_4881_ = v___x_4877_;
goto v_reusejp_4880_;
}
else
{
lean_object* v_reuseFailAlloc_4888_; 
v_reuseFailAlloc_4888_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4888_, 0, v_depth_4866_);
lean_ctor_set(v_reuseFailAlloc_4888_, 1, v_levelAssignDepth_4867_);
lean_ctor_set(v_reuseFailAlloc_4888_, 2, v_lmvarCounter_4868_);
lean_ctor_set(v_reuseFailAlloc_4888_, 3, v_mvarCounter_4869_);
lean_ctor_set(v_reuseFailAlloc_4888_, 4, v_lDecls_4870_);
lean_ctor_set(v_reuseFailAlloc_4888_, 5, v_decls_4871_);
lean_ctor_set(v_reuseFailAlloc_4888_, 6, v_userNames_4872_);
lean_ctor_set(v_reuseFailAlloc_4888_, 7, v_lAssignment_4873_);
lean_ctor_set(v_reuseFailAlloc_4888_, 8, v___x_4879_);
lean_ctor_set(v_reuseFailAlloc_4888_, 9, v_dAssignment_4875_);
v___x_4881_ = v_reuseFailAlloc_4888_;
goto v_reusejp_4880_;
}
v_reusejp_4880_:
{
lean_object* v___x_4883_; 
if (v_isShared_4865_ == 0)
{
lean_ctor_set(v___x_4864_, 0, v___x_4881_);
v___x_4883_ = v___x_4864_;
goto v_reusejp_4882_;
}
else
{
lean_object* v_reuseFailAlloc_4887_; 
v_reuseFailAlloc_4887_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4887_, 0, v___x_4881_);
lean_ctor_set(v_reuseFailAlloc_4887_, 1, v_cache_4859_);
lean_ctor_set(v_reuseFailAlloc_4887_, 2, v_zetaDeltaFVarIds_4860_);
lean_ctor_set(v_reuseFailAlloc_4887_, 3, v_postponed_4861_);
lean_ctor_set(v_reuseFailAlloc_4887_, 4, v_diag_4862_);
v___x_4883_ = v_reuseFailAlloc_4887_;
goto v_reusejp_4882_;
}
v_reusejp_4882_:
{
lean_object* v___x_4884_; lean_object* v___x_4885_; lean_object* v___x_4886_; 
v___x_4884_ = lean_st_ref_set(v___y_4855_, v___x_4883_);
v___x_4885_ = lean_box(0);
v___x_4886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4886_, 0, v___x_4885_);
return v___x_4886_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0___redArg___boxed(lean_object* v_mvarId_4891_, lean_object* v_val_4892_, lean_object* v___y_4893_, lean_object* v___y_4894_){
_start:
{
lean_object* v_res_4895_; 
v_res_4895_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0___redArg(v_mvarId_4891_, v_val_4892_, v___y_4893_);
lean_dec(v___y_4893_);
return v_res_4895_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4897_; lean_object* v___x_4898_; 
v___x_4897_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___lam__0___closed__0));
v___x_4898_ = l_Lean_stringToMessageData(v___x_4897_);
return v___x_4898_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4900_; lean_object* v___x_4901_; 
v___x_4900_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___lam__0___closed__2));
v___x_4901_ = l_Lean_stringToMessageData(v___x_4900_);
return v___x_4901_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4903_; lean_object* v___x_4904_; 
v___x_4903_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___lam__0___closed__4));
v___x_4904_ = l_Lean_stringToMessageData(v___x_4903_);
return v___x_4904_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___lam__0(lean_object* v_a_4905_, lean_object* v___x_4906_, lean_object* v_x_4907_, lean_object* v___y_4908_, lean_object* v___y_4909_, lean_object* v___y_4910_, lean_object* v___y_4911_, lean_object* v___y_4912_, lean_object* v___y_4913_){
_start:
{
if (lean_obj_tag(v_x_4907_) == 0)
{
lean_object* v_a_4915_; lean_object* v___x_4917_; uint8_t v_isShared_4918_; uint8_t v_isSharedCheck_4930_; 
lean_dec_ref(v___x_4906_);
v_a_4915_ = lean_ctor_get(v_x_4907_, 0);
v_isSharedCheck_4930_ = !lean_is_exclusive(v_x_4907_);
if (v_isSharedCheck_4930_ == 0)
{
v___x_4917_ = v_x_4907_;
v_isShared_4918_ = v_isSharedCheck_4930_;
goto v_resetjp_4916_;
}
else
{
lean_inc(v_a_4915_);
lean_dec(v_x_4907_);
v___x_4917_ = lean_box(0);
v_isShared_4918_ = v_isSharedCheck_4930_;
goto v_resetjp_4916_;
}
v_resetjp_4916_:
{
lean_object* v___x_4919_; lean_object* v___x_4920_; lean_object* v___x_4921_; lean_object* v___x_4922_; lean_object* v___x_4923_; lean_object* v___x_4924_; lean_object* v___x_4925_; lean_object* v___x_4926_; lean_object* v___x_4928_; 
v___x_4919_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___lam__0___closed__1);
v___x_4920_ = l_Lean_LocalDecl_userName(v_a_4905_);
v___x_4921_ = l_Lean_MessageData_ofName(v___x_4920_);
v___x_4922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4922_, 0, v___x_4919_);
lean_ctor_set(v___x_4922_, 1, v___x_4921_);
v___x_4923_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___lam__0___closed__3);
v___x_4924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4924_, 0, v___x_4922_);
lean_ctor_set(v___x_4924_, 1, v___x_4923_);
v___x_4925_ = l_Lean_Exception_toMessageData(v_a_4915_);
v___x_4926_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4926_, 0, v___x_4924_);
lean_ctor_set(v___x_4926_, 1, v___x_4925_);
if (v_isShared_4918_ == 0)
{
lean_ctor_set(v___x_4917_, 0, v___x_4926_);
v___x_4928_ = v___x_4917_;
goto v_reusejp_4927_;
}
else
{
lean_object* v_reuseFailAlloc_4929_; 
v_reuseFailAlloc_4929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4929_, 0, v___x_4926_);
v___x_4928_ = v_reuseFailAlloc_4929_;
goto v_reusejp_4927_;
}
v_reusejp_4927_:
{
return v___x_4928_;
}
}
}
else
{
lean_object* v_a_4931_; lean_object* v___x_4933_; uint8_t v_isShared_4934_; uint8_t v_isSharedCheck_4960_; 
v_a_4931_ = lean_ctor_get(v_x_4907_, 0);
v_isSharedCheck_4960_ = !lean_is_exclusive(v_x_4907_);
if (v_isSharedCheck_4960_ == 0)
{
v___x_4933_ = v_x_4907_;
v_isShared_4934_ = v_isSharedCheck_4960_;
goto v_resetjp_4932_;
}
else
{
lean_inc(v_a_4931_);
lean_dec(v_x_4907_);
v___x_4933_ = lean_box(0);
v_isShared_4934_ = v_isSharedCheck_4960_;
goto v_resetjp_4932_;
}
v_resetjp_4932_:
{
if (lean_obj_tag(v_a_4931_) == 0)
{
lean_object* v___x_4935_; lean_object* v___x_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; lean_object* v___x_4939_; lean_object* v___x_4940_; lean_object* v___x_4942_; 
lean_dec_ref(v_a_4931_);
lean_dec_ref(v___x_4906_);
v___x_4935_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___lam__0___closed__1);
v___x_4936_ = l_Lean_LocalDecl_userName(v_a_4905_);
v___x_4937_ = l_Lean_MessageData_ofName(v___x_4936_);
v___x_4938_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4938_, 0, v___x_4935_);
lean_ctor_set(v___x_4938_, 1, v___x_4937_);
v___x_4939_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___lam__0___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___lam__0___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___lam__0___closed__5);
v___x_4940_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4940_, 0, v___x_4938_);
lean_ctor_set(v___x_4940_, 1, v___x_4939_);
if (v_isShared_4934_ == 0)
{
lean_ctor_set_tag(v___x_4933_, 0);
lean_ctor_set(v___x_4933_, 0, v___x_4940_);
v___x_4942_ = v___x_4933_;
goto v_reusejp_4941_;
}
else
{
lean_object* v_reuseFailAlloc_4943_; 
v_reuseFailAlloc_4943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4943_, 0, v___x_4940_);
v___x_4942_ = v_reuseFailAlloc_4943_;
goto v_reusejp_4941_;
}
v_reusejp_4941_:
{
return v___x_4942_;
}
}
else
{
lean_object* v_e_x27_4944_; lean_object* v___x_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; lean_object* v___x_4949_; lean_object* v___x_4950_; lean_object* v___x_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; lean_object* v___x_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; lean_object* v___x_4958_; 
v_e_x27_4944_ = lean_ctor_get(v_a_4931_, 0);
lean_inc_ref(v_e_x27_4944_);
lean_dec_ref(v_a_4931_);
v___x_4945_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___lam__0___closed__1);
v___x_4946_ = l_Lean_LocalDecl_userName(v_a_4905_);
v___x_4947_ = l_Lean_MessageData_ofName(v___x_4946_);
v___x_4948_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4948_, 0, v___x_4945_);
lean_ctor_set(v___x_4948_, 1, v___x_4947_);
v___x_4949_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8);
v___x_4950_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4950_, 0, v___x_4948_);
lean_ctor_set(v___x_4950_, 1, v___x_4949_);
v___x_4951_ = l_Lean_indentExpr(v___x_4906_);
v___x_4952_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4952_, 0, v___x_4950_);
lean_ctor_set(v___x_4952_, 1, v___x_4951_);
v___x_4953_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_4954_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4954_, 0, v___x_4952_);
lean_ctor_set(v___x_4954_, 1, v___x_4953_);
v___x_4955_ = l_Lean_indentExpr(v_e_x27_4944_);
v___x_4956_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4956_, 0, v___x_4954_);
lean_ctor_set(v___x_4956_, 1, v___x_4955_);
if (v_isShared_4934_ == 0)
{
lean_ctor_set_tag(v___x_4933_, 0);
lean_ctor_set(v___x_4933_, 0, v___x_4956_);
v___x_4958_ = v___x_4933_;
goto v_reusejp_4957_;
}
else
{
lean_object* v_reuseFailAlloc_4959_; 
v_reuseFailAlloc_4959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4959_, 0, v___x_4956_);
v___x_4958_ = v_reuseFailAlloc_4959_;
goto v_reusejp_4957_;
}
v_reusejp_4957_:
{
return v___x_4958_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___lam__0___boxed(lean_object* v_a_4961_, lean_object* v___x_4962_, lean_object* v_x_4963_, lean_object* v___y_4964_, lean_object* v___y_4965_, lean_object* v___y_4966_, lean_object* v___y_4967_, lean_object* v___y_4968_, lean_object* v___y_4969_, lean_object* v___y_4970_){
_start:
{
lean_object* v_res_4971_; 
v_res_4971_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___lam__0(v_a_4961_, v___x_4962_, v_x_4963_, v___y_4964_, v___y_4965_, v___y_4966_, v___y_4967_, v___y_4968_, v___y_4969_);
lean_dec(v___y_4969_);
lean_dec_ref(v___y_4968_);
lean_dec(v___y_4967_);
lean_dec_ref(v___y_4966_);
lean_dec(v___y_4965_);
lean_dec_ref(v___y_4964_);
lean_dec_ref(v_a_4961_);
return v_res_4971_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3(lean_object* v_a_4979_, lean_object* v___x_4980_, lean_object* v_as_4981_, size_t v_sz_4982_, size_t v_i_4983_, lean_object* v_b_4984_, lean_object* v___y_4985_, lean_object* v___y_4986_, lean_object* v___y_4987_, lean_object* v___y_4988_, lean_object* v___y_4989_, lean_object* v___y_4990_){
_start:
{
lean_object* v_a_4993_; uint8_t v___x_4997_; 
v___x_4997_ = lean_usize_dec_lt(v_i_4983_, v_sz_4982_);
if (v___x_4997_ == 0)
{
lean_object* v___x_4998_; 
lean_dec_ref(v___x_4980_);
lean_dec(v_a_4979_);
v___x_4998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4998_, 0, v_b_4984_);
return v___x_4998_;
}
else
{
lean_object* v_a_4999_; lean_object* v___x_5000_; 
v_a_4999_ = lean_array_uget_borrowed(v_as_4981_, v_i_4983_);
lean_inc(v_a_4999_);
v___x_5000_ = l_Lean_FVarId_getDecl___redArg(v_a_4999_, v___y_4987_, v___y_4989_, v___y_4990_);
if (lean_obj_tag(v___x_5000_) == 0)
{
lean_object* v_options_5001_; lean_object* v_a_5002_; lean_object* v_snd_5003_; lean_object* v___x_5005_; uint8_t v_isShared_5006_; uint8_t v_isSharedCheck_5194_; 
v_options_5001_ = lean_ctor_get(v___y_4989_, 2);
v_a_5002_ = lean_ctor_get(v___x_5000_, 0);
lean_inc(v_a_5002_);
lean_dec_ref(v___x_5000_);
v_snd_5003_ = lean_ctor_get(v_b_4984_, 1);
v_isSharedCheck_5194_ = !lean_is_exclusive(v_b_4984_);
if (v_isSharedCheck_5194_ == 0)
{
lean_object* v_unused_5195_; 
v_unused_5195_ = lean_ctor_get(v_b_4984_, 0);
lean_dec(v_unused_5195_);
v___x_5005_ = v_b_4984_;
v_isShared_5006_ = v_isSharedCheck_5194_;
goto v_resetjp_5004_;
}
else
{
lean_inc(v_snd_5003_);
lean_dec(v_b_4984_);
v___x_5005_ = lean_box(0);
v_isShared_5006_ = v_isSharedCheck_5194_;
goto v_resetjp_5004_;
}
v_resetjp_5004_:
{
lean_object* v_inheritedTraceOptions_5007_; uint8_t v_hasTrace_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; lean_object* v___y_5012_; 
v_inheritedTraceOptions_5007_ = lean_ctor_get(v___y_4989_, 13);
v_hasTrace_5008_ = lean_ctor_get_uint8(v_options_5001_, sizeof(void*)*1);
v___x_5009_ = lean_box(0);
v___x_5010_ = l_Lean_LocalDecl_type(v_a_5002_);
if (v_hasTrace_5008_ == 0)
{
lean_object* v___x_5109_; 
lean_inc_ref(v___x_4980_);
lean_inc_ref(v___x_5010_);
v___x_5109_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_5010_, v___x_4980_, v___y_4985_, v___y_4986_, v___y_4987_, v___y_4988_, v___y_4989_, v___y_4990_);
v___y_5012_ = v___x_5109_;
goto v___jp_5011_;
}
else
{
lean_object* v___f_5110_; lean_object* v___x_5111_; lean_object* v___x_5112_; lean_object* v___x_5113_; uint8_t v___x_5114_; lean_object* v___y_5116_; lean_object* v___y_5117_; lean_object* v_a_5118_; lean_object* v___y_5131_; lean_object* v___y_5132_; lean_object* v_a_5133_; 
lean_inc_ref(v___x_5010_);
lean_inc(v_a_5002_);
v___f_5110_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___lam__0___boxed), 10, 2);
lean_closure_set(v___f_5110_, 0, v_a_5002_);
lean_closure_set(v___f_5110_, 1, v___x_5010_);
v___x_5111_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0));
v___x_5112_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__1));
v___x_5113_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1);
v___x_5114_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5007_, v_options_5001_, v___x_5113_);
if (v___x_5114_ == 0)
{
lean_object* v___x_5191_; uint8_t v___x_5192_; 
v___x_5191_ = l_Lean_trace_profiler;
v___x_5192_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_5001_, v___x_5191_);
if (v___x_5192_ == 0)
{
lean_object* v___x_5193_; 
lean_dec_ref(v___f_5110_);
lean_inc_ref(v___x_4980_);
lean_inc_ref(v___x_5010_);
v___x_5193_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_5010_, v___x_4980_, v___y_4985_, v___y_4986_, v___y_4987_, v___y_4988_, v___y_4989_, v___y_4990_);
v___y_5012_ = v___x_5193_;
goto v___jp_5011_;
}
else
{
goto v___jp_5142_;
}
}
else
{
goto v___jp_5142_;
}
v___jp_5115_:
{
lean_object* v___x_5119_; double v___x_5120_; double v___x_5121_; double v___x_5122_; double v___x_5123_; double v___x_5124_; lean_object* v___x_5125_; lean_object* v___x_5126_; lean_object* v___x_5127_; lean_object* v___x_5128_; lean_object* v___x_5129_; 
v___x_5119_ = lean_io_mono_nanos_now();
v___x_5120_ = lean_float_of_nat(v___y_5117_);
v___x_5121_ = lean_float_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9);
v___x_5122_ = lean_float_div(v___x_5120_, v___x_5121_);
v___x_5123_ = lean_float_of_nat(v___x_5119_);
v___x_5124_ = lean_float_div(v___x_5123_, v___x_5121_);
v___x_5125_ = lean_box_float(v___x_5122_);
v___x_5126_ = lean_box_float(v___x_5124_);
v___x_5127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5127_, 0, v___x_5125_);
lean_ctor_set(v___x_5127_, 1, v___x_5126_);
v___x_5128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5128_, 0, v_a_5118_);
lean_ctor_set(v___x_5128_, 1, v___x_5127_);
v___x_5129_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2(v___x_5111_, v_hasTrace_5008_, v___x_5112_, v_options_5001_, v___x_5114_, v___y_5116_, v___f_5110_, v___x_5128_, v___y_4985_, v___y_4986_, v___y_4987_, v___y_4988_, v___y_4989_, v___y_4990_);
v___y_5012_ = v___x_5129_;
goto v___jp_5011_;
}
v___jp_5130_:
{
lean_object* v___x_5134_; double v___x_5135_; double v___x_5136_; lean_object* v___x_5137_; lean_object* v___x_5138_; lean_object* v___x_5139_; lean_object* v___x_5140_; lean_object* v___x_5141_; 
v___x_5134_ = lean_io_get_num_heartbeats();
v___x_5135_ = lean_float_of_nat(v___y_5132_);
v___x_5136_ = lean_float_of_nat(v___x_5134_);
v___x_5137_ = lean_box_float(v___x_5135_);
v___x_5138_ = lean_box_float(v___x_5136_);
v___x_5139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5139_, 0, v___x_5137_);
lean_ctor_set(v___x_5139_, 1, v___x_5138_);
v___x_5140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5140_, 0, v_a_5133_);
lean_ctor_set(v___x_5140_, 1, v___x_5139_);
v___x_5141_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2(v___x_5111_, v_hasTrace_5008_, v___x_5112_, v_options_5001_, v___x_5114_, v___y_5131_, v___f_5110_, v___x_5140_, v___y_4985_, v___y_4986_, v___y_4987_, v___y_4988_, v___y_4989_, v___y_4990_);
v___y_5012_ = v___x_5141_;
goto v___jp_5011_;
}
v___jp_5142_:
{
lean_object* v___x_5143_; 
v___x_5143_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__1___redArg(v___y_4990_);
if (lean_obj_tag(v___x_5143_) == 0)
{
lean_object* v_a_5144_; lean_object* v___x_5145_; uint8_t v___x_5146_; 
v_a_5144_ = lean_ctor_get(v___x_5143_, 0);
lean_inc(v_a_5144_);
lean_dec_ref(v___x_5143_);
v___x_5145_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5146_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_5001_, v___x_5145_);
if (v___x_5146_ == 0)
{
lean_object* v___x_5147_; lean_object* v___x_5148_; 
v___x_5147_ = lean_io_mono_nanos_now();
lean_inc_ref(v___x_4980_);
lean_inc_ref(v___x_5010_);
v___x_5148_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_5010_, v___x_4980_, v___y_4985_, v___y_4986_, v___y_4987_, v___y_4988_, v___y_4989_, v___y_4990_);
if (lean_obj_tag(v___x_5148_) == 0)
{
lean_object* v_a_5149_; lean_object* v___x_5151_; uint8_t v_isShared_5152_; uint8_t v_isSharedCheck_5156_; 
v_a_5149_ = lean_ctor_get(v___x_5148_, 0);
v_isSharedCheck_5156_ = !lean_is_exclusive(v___x_5148_);
if (v_isSharedCheck_5156_ == 0)
{
v___x_5151_ = v___x_5148_;
v_isShared_5152_ = v_isSharedCheck_5156_;
goto v_resetjp_5150_;
}
else
{
lean_inc(v_a_5149_);
lean_dec(v___x_5148_);
v___x_5151_ = lean_box(0);
v_isShared_5152_ = v_isSharedCheck_5156_;
goto v_resetjp_5150_;
}
v_resetjp_5150_:
{
lean_object* v___x_5154_; 
if (v_isShared_5152_ == 0)
{
lean_ctor_set_tag(v___x_5151_, 1);
v___x_5154_ = v___x_5151_;
goto v_reusejp_5153_;
}
else
{
lean_object* v_reuseFailAlloc_5155_; 
v_reuseFailAlloc_5155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5155_, 0, v_a_5149_);
v___x_5154_ = v_reuseFailAlloc_5155_;
goto v_reusejp_5153_;
}
v_reusejp_5153_:
{
v___y_5116_ = v_a_5144_;
v___y_5117_ = v___x_5147_;
v_a_5118_ = v___x_5154_;
goto v___jp_5115_;
}
}
}
else
{
lean_object* v_a_5157_; lean_object* v___x_5159_; uint8_t v_isShared_5160_; uint8_t v_isSharedCheck_5164_; 
v_a_5157_ = lean_ctor_get(v___x_5148_, 0);
v_isSharedCheck_5164_ = !lean_is_exclusive(v___x_5148_);
if (v_isSharedCheck_5164_ == 0)
{
v___x_5159_ = v___x_5148_;
v_isShared_5160_ = v_isSharedCheck_5164_;
goto v_resetjp_5158_;
}
else
{
lean_inc(v_a_5157_);
lean_dec(v___x_5148_);
v___x_5159_ = lean_box(0);
v_isShared_5160_ = v_isSharedCheck_5164_;
goto v_resetjp_5158_;
}
v_resetjp_5158_:
{
lean_object* v___x_5162_; 
if (v_isShared_5160_ == 0)
{
lean_ctor_set_tag(v___x_5159_, 0);
v___x_5162_ = v___x_5159_;
goto v_reusejp_5161_;
}
else
{
lean_object* v_reuseFailAlloc_5163_; 
v_reuseFailAlloc_5163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5163_, 0, v_a_5157_);
v___x_5162_ = v_reuseFailAlloc_5163_;
goto v_reusejp_5161_;
}
v_reusejp_5161_:
{
v___y_5116_ = v_a_5144_;
v___y_5117_ = v___x_5147_;
v_a_5118_ = v___x_5162_;
goto v___jp_5115_;
}
}
}
}
else
{
lean_object* v___x_5165_; lean_object* v___x_5166_; 
v___x_5165_ = lean_io_get_num_heartbeats();
lean_inc_ref(v___x_4980_);
lean_inc_ref(v___x_5010_);
v___x_5166_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_5010_, v___x_4980_, v___y_4985_, v___y_4986_, v___y_4987_, v___y_4988_, v___y_4989_, v___y_4990_);
if (lean_obj_tag(v___x_5166_) == 0)
{
lean_object* v_a_5167_; lean_object* v___x_5169_; uint8_t v_isShared_5170_; uint8_t v_isSharedCheck_5174_; 
v_a_5167_ = lean_ctor_get(v___x_5166_, 0);
v_isSharedCheck_5174_ = !lean_is_exclusive(v___x_5166_);
if (v_isSharedCheck_5174_ == 0)
{
v___x_5169_ = v___x_5166_;
v_isShared_5170_ = v_isSharedCheck_5174_;
goto v_resetjp_5168_;
}
else
{
lean_inc(v_a_5167_);
lean_dec(v___x_5166_);
v___x_5169_ = lean_box(0);
v_isShared_5170_ = v_isSharedCheck_5174_;
goto v_resetjp_5168_;
}
v_resetjp_5168_:
{
lean_object* v___x_5172_; 
if (v_isShared_5170_ == 0)
{
lean_ctor_set_tag(v___x_5169_, 1);
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
v___y_5131_ = v_a_5144_;
v___y_5132_ = v___x_5165_;
v_a_5133_ = v___x_5172_;
goto v___jp_5130_;
}
}
}
else
{
lean_object* v_a_5175_; lean_object* v___x_5177_; uint8_t v_isShared_5178_; uint8_t v_isSharedCheck_5182_; 
v_a_5175_ = lean_ctor_get(v___x_5166_, 0);
v_isSharedCheck_5182_ = !lean_is_exclusive(v___x_5166_);
if (v_isSharedCheck_5182_ == 0)
{
v___x_5177_ = v___x_5166_;
v_isShared_5178_ = v_isSharedCheck_5182_;
goto v_resetjp_5176_;
}
else
{
lean_inc(v_a_5175_);
lean_dec(v___x_5166_);
v___x_5177_ = lean_box(0);
v_isShared_5178_ = v_isSharedCheck_5182_;
goto v_resetjp_5176_;
}
v_resetjp_5176_:
{
lean_object* v___x_5180_; 
if (v_isShared_5178_ == 0)
{
lean_ctor_set_tag(v___x_5177_, 0);
v___x_5180_ = v___x_5177_;
goto v_reusejp_5179_;
}
else
{
lean_object* v_reuseFailAlloc_5181_; 
v_reuseFailAlloc_5181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5181_, 0, v_a_5175_);
v___x_5180_ = v_reuseFailAlloc_5181_;
goto v_reusejp_5179_;
}
v_reusejp_5179_:
{
v___y_5131_ = v_a_5144_;
v___y_5132_ = v___x_5165_;
v_a_5133_ = v___x_5180_;
goto v___jp_5130_;
}
}
}
}
}
else
{
lean_object* v_a_5183_; lean_object* v___x_5185_; uint8_t v_isShared_5186_; uint8_t v_isSharedCheck_5190_; 
lean_dec_ref(v___f_5110_);
lean_dec_ref(v___x_5010_);
lean_del_object(v___x_5005_);
lean_dec(v_snd_5003_);
lean_dec(v_a_5002_);
lean_dec_ref(v___x_4980_);
lean_dec(v_a_4979_);
v_a_5183_ = lean_ctor_get(v___x_5143_, 0);
v_isSharedCheck_5190_ = !lean_is_exclusive(v___x_5143_);
if (v_isSharedCheck_5190_ == 0)
{
v___x_5185_ = v___x_5143_;
v_isShared_5186_ = v_isSharedCheck_5190_;
goto v_resetjp_5184_;
}
else
{
lean_inc(v_a_5183_);
lean_dec(v___x_5143_);
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
v___jp_5011_:
{
if (lean_obj_tag(v___y_5012_) == 0)
{
lean_object* v_a_5013_; 
v_a_5013_ = lean_ctor_get(v___y_5012_, 0);
lean_inc(v_a_5013_);
lean_dec_ref(v___y_5012_);
if (lean_obj_tag(v_a_5013_) == 0)
{
lean_object* v___x_5015_; 
lean_dec_ref(v_a_5013_);
lean_dec_ref(v___x_5010_);
lean_dec(v_a_5002_);
if (v_isShared_5006_ == 0)
{
lean_ctor_set(v___x_5005_, 0, v___x_5009_);
v___x_5015_ = v___x_5005_;
goto v_reusejp_5014_;
}
else
{
lean_object* v_reuseFailAlloc_5016_; 
v_reuseFailAlloc_5016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5016_, 0, v___x_5009_);
lean_ctor_set(v_reuseFailAlloc_5016_, 1, v_snd_5003_);
v___x_5015_ = v_reuseFailAlloc_5016_;
goto v_reusejp_5014_;
}
v_reusejp_5014_:
{
v_a_4993_ = v___x_5015_;
goto v___jp_4992_;
}
}
else
{
lean_object* v_e_x27_5017_; lean_object* v_proof_5018_; uint8_t v___x_5019_; 
v_e_x27_5017_ = lean_ctor_get(v_a_5013_, 0);
lean_inc_ref_n(v_e_x27_5017_, 2);
v_proof_5018_ = lean_ctor_get(v_a_5013_, 1);
lean_inc_ref(v_proof_5018_);
lean_dec_ref(v_a_5013_);
v___x_5019_ = l_Lean_Expr_isFalse(v_e_x27_5017_);
if (v___x_5019_ == 0)
{
lean_object* v___x_5020_; 
lean_inc_ref(v___x_5010_);
v___x_5020_ = l_Lean_Meta_Sym_getLevel___redArg(v___x_5010_, v___y_4986_, v___y_4987_, v___y_4988_, v___y_4989_, v___y_4990_);
if (lean_obj_tag(v___x_5020_) == 0)
{
lean_object* v_a_5021_; lean_object* v___x_5022_; lean_object* v___x_5023_; lean_object* v___x_5024_; lean_object* v___x_5025_; lean_object* v___x_5026_; lean_object* v___x_5027_; lean_object* v___x_5028_; uint8_t v___x_5029_; uint8_t v___x_5030_; lean_object* v___x_5031_; lean_object* v___x_5032_; lean_object* v___x_5034_; 
v_a_5021_ = lean_ctor_get(v___x_5020_, 0);
lean_inc(v_a_5021_);
lean_dec_ref(v___x_5020_);
v___x_5022_ = l_Lean_LocalDecl_userName(v_a_5002_);
lean_dec(v_a_5002_);
v___x_5023_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___closed__2));
v___x_5024_ = lean_box(0);
v___x_5025_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5025_, 0, v_a_5021_);
lean_ctor_set(v___x_5025_, 1, v___x_5024_);
v___x_5026_ = l_Lean_mkConst(v___x_5023_, v___x_5025_);
lean_inc(v_a_4999_);
v___x_5027_ = l_Lean_mkFVar(v_a_4999_);
lean_inc_ref(v_e_x27_5017_);
v___x_5028_ = l_Lean_mkApp4(v___x_5026_, v___x_5010_, v_e_x27_5017_, v_proof_5018_, v___x_5027_);
v___x_5029_ = 0;
v___x_5030_ = 0;
v___x_5031_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5031_, 0, v___x_5022_);
lean_ctor_set(v___x_5031_, 1, v_e_x27_5017_);
lean_ctor_set(v___x_5031_, 2, v___x_5028_);
lean_ctor_set_uint8(v___x_5031_, sizeof(void*)*3, v___x_5029_);
lean_ctor_set_uint8(v___x_5031_, sizeof(void*)*3 + 1, v___x_5030_);
v___x_5032_ = lean_array_push(v_snd_5003_, v___x_5031_);
if (v_isShared_5006_ == 0)
{
lean_ctor_set(v___x_5005_, 1, v___x_5032_);
lean_ctor_set(v___x_5005_, 0, v___x_5009_);
v___x_5034_ = v___x_5005_;
goto v_reusejp_5033_;
}
else
{
lean_object* v_reuseFailAlloc_5035_; 
v_reuseFailAlloc_5035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5035_, 0, v___x_5009_);
lean_ctor_set(v_reuseFailAlloc_5035_, 1, v___x_5032_);
v___x_5034_ = v_reuseFailAlloc_5035_;
goto v_reusejp_5033_;
}
v_reusejp_5033_:
{
v_a_4993_ = v___x_5034_;
goto v___jp_4992_;
}
}
else
{
lean_object* v_a_5036_; lean_object* v___x_5038_; uint8_t v_isShared_5039_; uint8_t v_isSharedCheck_5043_; 
lean_dec_ref(v_proof_5018_);
lean_dec_ref(v_e_x27_5017_);
lean_dec_ref(v___x_5010_);
lean_del_object(v___x_5005_);
lean_dec(v_snd_5003_);
lean_dec(v_a_5002_);
lean_dec_ref(v___x_4980_);
lean_dec(v_a_4979_);
v_a_5036_ = lean_ctor_get(v___x_5020_, 0);
v_isSharedCheck_5043_ = !lean_is_exclusive(v___x_5020_);
if (v_isSharedCheck_5043_ == 0)
{
v___x_5038_ = v___x_5020_;
v_isShared_5039_ = v_isSharedCheck_5043_;
goto v_resetjp_5037_;
}
else
{
lean_inc(v_a_5036_);
lean_dec(v___x_5020_);
v___x_5038_ = lean_box(0);
v_isShared_5039_ = v_isSharedCheck_5043_;
goto v_resetjp_5037_;
}
v_resetjp_5037_:
{
lean_object* v___x_5041_; 
if (v_isShared_5039_ == 0)
{
v___x_5041_ = v___x_5038_;
goto v_reusejp_5040_;
}
else
{
lean_object* v_reuseFailAlloc_5042_; 
v_reuseFailAlloc_5042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5042_, 0, v_a_5036_);
v___x_5041_ = v_reuseFailAlloc_5042_;
goto v_reusejp_5040_;
}
v_reusejp_5040_:
{
return v___x_5041_;
}
}
}
}
else
{
lean_object* v___x_5044_; 
lean_dec(v_a_5002_);
lean_dec_ref(v___x_4980_);
lean_inc_ref(v___x_5010_);
v___x_5044_ = l_Lean_Meta_Sym_getLevel___redArg(v___x_5010_, v___y_4986_, v___y_4987_, v___y_4988_, v___y_4989_, v___y_4990_);
if (lean_obj_tag(v___x_5044_) == 0)
{
lean_object* v_a_5045_; lean_object* v___x_5046_; 
v_a_5045_ = lean_ctor_get(v___x_5044_, 0);
lean_inc(v_a_5045_);
lean_dec_ref(v___x_5044_);
lean_inc(v_a_4979_);
v___x_5046_ = l_Lean_MVarId_getType(v_a_4979_, v___y_4987_, v___y_4988_, v___y_4989_, v___y_4990_);
if (lean_obj_tag(v___x_5046_) == 0)
{
lean_object* v_a_5047_; lean_object* v___x_5048_; lean_object* v___x_5049_; lean_object* v___x_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; 
v_a_5047_ = lean_ctor_get(v___x_5046_, 0);
lean_inc(v_a_5047_);
lean_dec_ref(v___x_5046_);
v___x_5048_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___closed__2));
v___x_5049_ = lean_box(0);
v___x_5050_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5050_, 0, v_a_5045_);
lean_ctor_set(v___x_5050_, 1, v___x_5049_);
v___x_5051_ = l_Lean_mkConst(v___x_5048_, v___x_5050_);
lean_inc(v_a_4999_);
v___x_5052_ = l_Lean_mkFVar(v_a_4999_);
v___x_5053_ = l_Lean_mkApp4(v___x_5051_, v___x_5010_, v_e_x27_5017_, v_proof_5018_, v___x_5052_);
v___x_5054_ = l_Lean_Meta_mkFalseElim(v_a_5047_, v___x_5053_, v___y_4987_, v___y_4988_, v___y_4989_, v___y_4990_);
if (lean_obj_tag(v___x_5054_) == 0)
{
lean_object* v_a_5055_; lean_object* v___x_5056_; 
v_a_5055_ = lean_ctor_get(v___x_5054_, 0);
lean_inc(v_a_5055_);
lean_dec_ref(v___x_5054_);
v___x_5056_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0___redArg(v_a_4979_, v_a_5055_, v___y_4988_);
if (lean_obj_tag(v___x_5056_) == 0)
{
lean_object* v___x_5058_; uint8_t v_isShared_5059_; uint8_t v_isSharedCheck_5067_; 
v_isSharedCheck_5067_ = !lean_is_exclusive(v___x_5056_);
if (v_isSharedCheck_5067_ == 0)
{
lean_object* v_unused_5068_; 
v_unused_5068_ = lean_ctor_get(v___x_5056_, 0);
lean_dec(v_unused_5068_);
v___x_5058_ = v___x_5056_;
v_isShared_5059_ = v_isSharedCheck_5067_;
goto v_resetjp_5057_;
}
else
{
lean_dec(v___x_5056_);
v___x_5058_ = lean_box(0);
v_isShared_5059_ = v_isSharedCheck_5067_;
goto v_resetjp_5057_;
}
v_resetjp_5057_:
{
lean_object* v___x_5060_; lean_object* v___x_5062_; 
v___x_5060_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___closed__3));
if (v_isShared_5006_ == 0)
{
lean_ctor_set(v___x_5005_, 0, v___x_5060_);
v___x_5062_ = v___x_5005_;
goto v_reusejp_5061_;
}
else
{
lean_object* v_reuseFailAlloc_5066_; 
v_reuseFailAlloc_5066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5066_, 0, v___x_5060_);
lean_ctor_set(v_reuseFailAlloc_5066_, 1, v_snd_5003_);
v___x_5062_ = v_reuseFailAlloc_5066_;
goto v_reusejp_5061_;
}
v_reusejp_5061_:
{
lean_object* v___x_5064_; 
if (v_isShared_5059_ == 0)
{
lean_ctor_set(v___x_5058_, 0, v___x_5062_);
v___x_5064_ = v___x_5058_;
goto v_reusejp_5063_;
}
else
{
lean_object* v_reuseFailAlloc_5065_; 
v_reuseFailAlloc_5065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5065_, 0, v___x_5062_);
v___x_5064_ = v_reuseFailAlloc_5065_;
goto v_reusejp_5063_;
}
v_reusejp_5063_:
{
return v___x_5064_;
}
}
}
}
else
{
lean_object* v_a_5069_; lean_object* v___x_5071_; uint8_t v_isShared_5072_; uint8_t v_isSharedCheck_5076_; 
lean_del_object(v___x_5005_);
lean_dec(v_snd_5003_);
v_a_5069_ = lean_ctor_get(v___x_5056_, 0);
v_isSharedCheck_5076_ = !lean_is_exclusive(v___x_5056_);
if (v_isSharedCheck_5076_ == 0)
{
v___x_5071_ = v___x_5056_;
v_isShared_5072_ = v_isSharedCheck_5076_;
goto v_resetjp_5070_;
}
else
{
lean_inc(v_a_5069_);
lean_dec(v___x_5056_);
v___x_5071_ = lean_box(0);
v_isShared_5072_ = v_isSharedCheck_5076_;
goto v_resetjp_5070_;
}
v_resetjp_5070_:
{
lean_object* v___x_5074_; 
if (v_isShared_5072_ == 0)
{
v___x_5074_ = v___x_5071_;
goto v_reusejp_5073_;
}
else
{
lean_object* v_reuseFailAlloc_5075_; 
v_reuseFailAlloc_5075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5075_, 0, v_a_5069_);
v___x_5074_ = v_reuseFailAlloc_5075_;
goto v_reusejp_5073_;
}
v_reusejp_5073_:
{
return v___x_5074_;
}
}
}
}
else
{
lean_object* v_a_5077_; lean_object* v___x_5079_; uint8_t v_isShared_5080_; uint8_t v_isSharedCheck_5084_; 
lean_del_object(v___x_5005_);
lean_dec(v_snd_5003_);
lean_dec(v_a_4979_);
v_a_5077_ = lean_ctor_get(v___x_5054_, 0);
v_isSharedCheck_5084_ = !lean_is_exclusive(v___x_5054_);
if (v_isSharedCheck_5084_ == 0)
{
v___x_5079_ = v___x_5054_;
v_isShared_5080_ = v_isSharedCheck_5084_;
goto v_resetjp_5078_;
}
else
{
lean_inc(v_a_5077_);
lean_dec(v___x_5054_);
v___x_5079_ = lean_box(0);
v_isShared_5080_ = v_isSharedCheck_5084_;
goto v_resetjp_5078_;
}
v_resetjp_5078_:
{
lean_object* v___x_5082_; 
if (v_isShared_5080_ == 0)
{
v___x_5082_ = v___x_5079_;
goto v_reusejp_5081_;
}
else
{
lean_object* v_reuseFailAlloc_5083_; 
v_reuseFailAlloc_5083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5083_, 0, v_a_5077_);
v___x_5082_ = v_reuseFailAlloc_5083_;
goto v_reusejp_5081_;
}
v_reusejp_5081_:
{
return v___x_5082_;
}
}
}
}
else
{
lean_object* v_a_5085_; lean_object* v___x_5087_; uint8_t v_isShared_5088_; uint8_t v_isSharedCheck_5092_; 
lean_dec(v_a_5045_);
lean_dec_ref(v_proof_5018_);
lean_dec_ref(v_e_x27_5017_);
lean_dec_ref(v___x_5010_);
lean_del_object(v___x_5005_);
lean_dec(v_snd_5003_);
lean_dec(v_a_4979_);
v_a_5085_ = lean_ctor_get(v___x_5046_, 0);
v_isSharedCheck_5092_ = !lean_is_exclusive(v___x_5046_);
if (v_isSharedCheck_5092_ == 0)
{
v___x_5087_ = v___x_5046_;
v_isShared_5088_ = v_isSharedCheck_5092_;
goto v_resetjp_5086_;
}
else
{
lean_inc(v_a_5085_);
lean_dec(v___x_5046_);
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
lean_dec_ref(v_proof_5018_);
lean_dec_ref(v_e_x27_5017_);
lean_dec_ref(v___x_5010_);
lean_del_object(v___x_5005_);
lean_dec(v_snd_5003_);
lean_dec(v_a_4979_);
v_a_5093_ = lean_ctor_get(v___x_5044_, 0);
v_isSharedCheck_5100_ = !lean_is_exclusive(v___x_5044_);
if (v_isSharedCheck_5100_ == 0)
{
v___x_5095_ = v___x_5044_;
v_isShared_5096_ = v_isSharedCheck_5100_;
goto v_resetjp_5094_;
}
else
{
lean_inc(v_a_5093_);
lean_dec(v___x_5044_);
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
}
}
else
{
lean_object* v_a_5101_; lean_object* v___x_5103_; uint8_t v_isShared_5104_; uint8_t v_isSharedCheck_5108_; 
lean_dec_ref(v___x_5010_);
lean_del_object(v___x_5005_);
lean_dec(v_snd_5003_);
lean_dec(v_a_5002_);
lean_dec_ref(v___x_4980_);
lean_dec(v_a_4979_);
v_a_5101_ = lean_ctor_get(v___y_5012_, 0);
v_isSharedCheck_5108_ = !lean_is_exclusive(v___y_5012_);
if (v_isSharedCheck_5108_ == 0)
{
v___x_5103_ = v___y_5012_;
v_isShared_5104_ = v_isSharedCheck_5108_;
goto v_resetjp_5102_;
}
else
{
lean_inc(v_a_5101_);
lean_dec(v___y_5012_);
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
}
}
else
{
lean_object* v_a_5196_; lean_object* v___x_5198_; uint8_t v_isShared_5199_; uint8_t v_isSharedCheck_5203_; 
lean_dec_ref(v_b_4984_);
lean_dec_ref(v___x_4980_);
lean_dec(v_a_4979_);
v_a_5196_ = lean_ctor_get(v___x_5000_, 0);
v_isSharedCheck_5203_ = !lean_is_exclusive(v___x_5000_);
if (v_isSharedCheck_5203_ == 0)
{
v___x_5198_ = v___x_5000_;
v_isShared_5199_ = v_isSharedCheck_5203_;
goto v_resetjp_5197_;
}
else
{
lean_inc(v_a_5196_);
lean_dec(v___x_5000_);
v___x_5198_ = lean_box(0);
v_isShared_5199_ = v_isSharedCheck_5203_;
goto v_resetjp_5197_;
}
v_resetjp_5197_:
{
lean_object* v___x_5201_; 
if (v_isShared_5199_ == 0)
{
v___x_5201_ = v___x_5198_;
goto v_reusejp_5200_;
}
else
{
lean_object* v_reuseFailAlloc_5202_; 
v_reuseFailAlloc_5202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5202_, 0, v_a_5196_);
v___x_5201_ = v_reuseFailAlloc_5202_;
goto v_reusejp_5200_;
}
v_reusejp_5200_:
{
return v___x_5201_;
}
}
}
}
v___jp_4992_:
{
size_t v___x_4994_; size_t v___x_4995_; 
v___x_4994_ = ((size_t)1ULL);
v___x_4995_ = lean_usize_add(v_i_4983_, v___x_4994_);
v_i_4983_ = v___x_4995_;
v_b_4984_ = v_a_4993_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___boxed(lean_object* v_a_5204_, lean_object* v___x_5205_, lean_object* v_as_5206_, lean_object* v_sz_5207_, lean_object* v_i_5208_, lean_object* v_b_5209_, lean_object* v___y_5210_, lean_object* v___y_5211_, lean_object* v___y_5212_, lean_object* v___y_5213_, lean_object* v___y_5214_, lean_object* v___y_5215_, lean_object* v___y_5216_){
_start:
{
size_t v_sz_boxed_5217_; size_t v_i_boxed_5218_; lean_object* v_res_5219_; 
v_sz_boxed_5217_ = lean_unbox_usize(v_sz_5207_);
lean_dec(v_sz_5207_);
v_i_boxed_5218_ = lean_unbox_usize(v_i_5208_);
lean_dec(v_i_5208_);
v_res_5219_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3(v_a_5204_, v___x_5205_, v_as_5206_, v_sz_boxed_5217_, v_i_boxed_5218_, v_b_5209_, v___y_5210_, v___y_5211_, v___y_5212_, v___y_5213_, v___y_5214_, v___y_5215_);
lean_dec(v___y_5215_);
lean_dec_ref(v___y_5214_);
lean_dec(v___y_5213_);
lean_dec_ref(v___y_5212_);
lean_dec(v___y_5211_);
lean_dec_ref(v___y_5210_);
lean_dec_ref(v_as_5206_);
return v_res_5219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__1(lean_object* v_a_5220_, lean_object* v___x_5221_, lean_object* v_fvarIdsToSimp_5222_, size_t v_sz_5223_, size_t v___x_5224_, lean_object* v___x_5225_, uint8_t v_simplifyTarget_5226_, lean_object* v___y_5227_, lean_object* v___y_5228_, lean_object* v___y_5229_, lean_object* v___y_5230_, lean_object* v___y_5231_, lean_object* v___y_5232_){
_start:
{
lean_object* v___y_5235_; lean_object* v___y_5236_; lean_object* v___y_5237_; lean_object* v___y_5238_; lean_object* v___y_5239_; uint8_t v___y_5240_; lean_object* v___x_5260_; 
lean_inc_ref(v___x_5221_);
lean_inc(v_a_5220_);
v___x_5260_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3(v_a_5220_, v___x_5221_, v_fvarIdsToSimp_5222_, v_sz_5223_, v___x_5224_, v___x_5225_, v___y_5227_, v___y_5228_, v___y_5229_, v___y_5230_, v___y_5231_, v___y_5232_);
if (lean_obj_tag(v___x_5260_) == 0)
{
lean_object* v_a_5261_; lean_object* v___x_5263_; uint8_t v_isShared_5264_; uint8_t v_isSharedCheck_5463_; 
v_a_5261_ = lean_ctor_get(v___x_5260_, 0);
v_isSharedCheck_5463_ = !lean_is_exclusive(v___x_5260_);
if (v_isSharedCheck_5463_ == 0)
{
v___x_5263_ = v___x_5260_;
v_isShared_5264_ = v_isSharedCheck_5463_;
goto v_resetjp_5262_;
}
else
{
lean_inc(v_a_5261_);
lean_dec(v___x_5260_);
v___x_5263_ = lean_box(0);
v_isShared_5264_ = v_isSharedCheck_5463_;
goto v_resetjp_5262_;
}
v_resetjp_5262_:
{
lean_object* v_fst_5265_; lean_object* v_snd_5266_; lean_object* v___x_5268_; uint8_t v_isShared_5269_; uint8_t v_isSharedCheck_5462_; 
v_fst_5265_ = lean_ctor_get(v_a_5261_, 0);
v_snd_5266_ = lean_ctor_get(v_a_5261_, 1);
v_isSharedCheck_5462_ = !lean_is_exclusive(v_a_5261_);
if (v_isSharedCheck_5462_ == 0)
{
v___x_5268_ = v_a_5261_;
v_isShared_5269_ = v_isSharedCheck_5462_;
goto v_resetjp_5267_;
}
else
{
lean_inc(v_snd_5266_);
lean_inc(v_fst_5265_);
lean_dec(v_a_5261_);
v___x_5268_ = lean_box(0);
v_isShared_5269_ = v_isSharedCheck_5462_;
goto v_resetjp_5267_;
}
v_resetjp_5267_:
{
lean_object* v_mvarIdNew_5271_; lean_object* v___y_5272_; lean_object* v___y_5273_; lean_object* v___y_5274_; lean_object* v___y_5275_; lean_object* v___y_5322_; 
if (lean_obj_tag(v_fst_5265_) == 0)
{
lean_del_object(v___x_5263_);
if (v_simplifyTarget_5226_ == 0)
{
lean_del_object(v___x_5268_);
lean_dec_ref(v___x_5221_);
v_mvarIdNew_5271_ = v_a_5220_;
v___y_5272_ = v___y_5229_;
v___y_5273_ = v___y_5230_;
v___y_5274_ = v___y_5231_;
v___y_5275_ = v___y_5232_;
goto v___jp_5270_;
}
else
{
lean_object* v___x_5365_; 
lean_inc(v_a_5220_);
v___x_5365_ = l_Lean_MVarId_getType(v_a_5220_, v___y_5229_, v___y_5230_, v___y_5231_, v___y_5232_);
if (lean_obj_tag(v___x_5365_) == 0)
{
lean_object* v_options_5366_; uint8_t v_hasTrace_5367_; 
v_options_5366_ = lean_ctor_get(v___y_5231_, 2);
v_hasTrace_5367_ = lean_ctor_get_uint8(v_options_5366_, sizeof(void*)*1);
if (v_hasTrace_5367_ == 0)
{
lean_object* v_a_5368_; lean_object* v___x_5369_; 
lean_del_object(v___x_5268_);
v_a_5368_ = lean_ctor_get(v___x_5365_, 0);
lean_inc(v_a_5368_);
lean_dec_ref(v___x_5365_);
v___x_5369_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v_a_5368_, v___x_5221_, v___y_5227_, v___y_5228_, v___y_5229_, v___y_5230_, v___y_5231_, v___y_5232_);
v___y_5322_ = v___x_5369_;
goto v___jp_5321_;
}
else
{
lean_object* v_a_5370_; lean_object* v_inheritedTraceOptions_5371_; lean_object* v___f_5372_; lean_object* v___x_5373_; lean_object* v___x_5374_; lean_object* v___x_5375_; uint8_t v___x_5376_; lean_object* v___y_5378_; lean_object* v___y_5379_; lean_object* v_a_5380_; lean_object* v___y_5395_; lean_object* v___y_5396_; lean_object* v_a_5397_; 
v_a_5370_ = lean_ctor_get(v___x_5365_, 0);
lean_inc_n(v_a_5370_, 2);
lean_dec_ref(v___x_5365_);
v_inheritedTraceOptions_5371_ = lean_ctor_get(v___y_5231_, 13);
v___f_5372_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___boxed), 9, 1);
lean_closure_set(v___f_5372_, 0, v_a_5370_);
v___x_5373_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0));
v___x_5374_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__1));
v___x_5375_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1);
v___x_5376_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5371_, v_options_5366_, v___x_5375_);
if (v___x_5376_ == 0)
{
lean_object* v___x_5447_; uint8_t v___x_5448_; 
v___x_5447_ = l_Lean_trace_profiler;
v___x_5448_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_5366_, v___x_5447_);
if (v___x_5448_ == 0)
{
lean_object* v___x_5449_; 
lean_dec_ref(v___f_5372_);
lean_del_object(v___x_5268_);
v___x_5449_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v_a_5370_, v___x_5221_, v___y_5227_, v___y_5228_, v___y_5229_, v___y_5230_, v___y_5231_, v___y_5232_);
v___y_5322_ = v___x_5449_;
goto v___jp_5321_;
}
else
{
goto v___jp_5406_;
}
}
else
{
goto v___jp_5406_;
}
v___jp_5377_:
{
lean_object* v___x_5381_; double v___x_5382_; double v___x_5383_; double v___x_5384_; double v___x_5385_; double v___x_5386_; lean_object* v___x_5387_; lean_object* v___x_5388_; lean_object* v___x_5390_; 
v___x_5381_ = lean_io_mono_nanos_now();
v___x_5382_ = lean_float_of_nat(v___y_5378_);
v___x_5383_ = lean_float_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9);
v___x_5384_ = lean_float_div(v___x_5382_, v___x_5383_);
v___x_5385_ = lean_float_of_nat(v___x_5381_);
v___x_5386_ = lean_float_div(v___x_5385_, v___x_5383_);
v___x_5387_ = lean_box_float(v___x_5384_);
v___x_5388_ = lean_box_float(v___x_5386_);
if (v_isShared_5269_ == 0)
{
lean_ctor_set(v___x_5268_, 1, v___x_5388_);
lean_ctor_set(v___x_5268_, 0, v___x_5387_);
v___x_5390_ = v___x_5268_;
goto v_reusejp_5389_;
}
else
{
lean_object* v_reuseFailAlloc_5393_; 
v_reuseFailAlloc_5393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5393_, 0, v___x_5387_);
lean_ctor_set(v_reuseFailAlloc_5393_, 1, v___x_5388_);
v___x_5390_ = v_reuseFailAlloc_5393_;
goto v_reusejp_5389_;
}
v_reusejp_5389_:
{
lean_object* v___x_5391_; lean_object* v___x_5392_; 
v___x_5391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5391_, 0, v_a_5380_);
lean_ctor_set(v___x_5391_, 1, v___x_5390_);
v___x_5392_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2(v___x_5373_, v_hasTrace_5367_, v___x_5374_, v_options_5366_, v___x_5376_, v___y_5379_, v___f_5372_, v___x_5391_, v___y_5227_, v___y_5228_, v___y_5229_, v___y_5230_, v___y_5231_, v___y_5232_);
v___y_5322_ = v___x_5392_;
goto v___jp_5321_;
}
}
v___jp_5394_:
{
lean_object* v___x_5398_; double v___x_5399_; double v___x_5400_; lean_object* v___x_5401_; lean_object* v___x_5402_; lean_object* v___x_5403_; lean_object* v___x_5404_; lean_object* v___x_5405_; 
v___x_5398_ = lean_io_get_num_heartbeats();
v___x_5399_ = lean_float_of_nat(v___y_5396_);
v___x_5400_ = lean_float_of_nat(v___x_5398_);
v___x_5401_ = lean_box_float(v___x_5399_);
v___x_5402_ = lean_box_float(v___x_5400_);
v___x_5403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5403_, 0, v___x_5401_);
lean_ctor_set(v___x_5403_, 1, v___x_5402_);
v___x_5404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5404_, 0, v_a_5397_);
lean_ctor_set(v___x_5404_, 1, v___x_5403_);
v___x_5405_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2(v___x_5373_, v_hasTrace_5367_, v___x_5374_, v_options_5366_, v___x_5376_, v___y_5395_, v___f_5372_, v___x_5404_, v___y_5227_, v___y_5228_, v___y_5229_, v___y_5230_, v___y_5231_, v___y_5232_);
v___y_5322_ = v___x_5405_;
goto v___jp_5321_;
}
v___jp_5406_:
{
lean_object* v___x_5407_; lean_object* v_a_5408_; lean_object* v___x_5409_; uint8_t v___x_5410_; 
v___x_5407_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__1___redArg(v___y_5232_);
v_a_5408_ = lean_ctor_get(v___x_5407_, 0);
lean_inc(v_a_5408_);
lean_dec_ref(v___x_5407_);
v___x_5409_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5410_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_5366_, v___x_5409_);
if (v___x_5410_ == 0)
{
lean_object* v___x_5411_; lean_object* v___x_5412_; 
v___x_5411_ = lean_io_mono_nanos_now();
v___x_5412_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v_a_5370_, v___x_5221_, v___y_5227_, v___y_5228_, v___y_5229_, v___y_5230_, v___y_5231_, v___y_5232_);
if (lean_obj_tag(v___x_5412_) == 0)
{
lean_object* v_a_5413_; lean_object* v___x_5415_; uint8_t v_isShared_5416_; uint8_t v_isSharedCheck_5420_; 
v_a_5413_ = lean_ctor_get(v___x_5412_, 0);
v_isSharedCheck_5420_ = !lean_is_exclusive(v___x_5412_);
if (v_isSharedCheck_5420_ == 0)
{
v___x_5415_ = v___x_5412_;
v_isShared_5416_ = v_isSharedCheck_5420_;
goto v_resetjp_5414_;
}
else
{
lean_inc(v_a_5413_);
lean_dec(v___x_5412_);
v___x_5415_ = lean_box(0);
v_isShared_5416_ = v_isSharedCheck_5420_;
goto v_resetjp_5414_;
}
v_resetjp_5414_:
{
lean_object* v___x_5418_; 
if (v_isShared_5416_ == 0)
{
lean_ctor_set_tag(v___x_5415_, 1);
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
v___y_5378_ = v___x_5411_;
v___y_5379_ = v_a_5408_;
v_a_5380_ = v___x_5418_;
goto v___jp_5377_;
}
}
}
else
{
lean_object* v_a_5421_; lean_object* v___x_5423_; uint8_t v_isShared_5424_; uint8_t v_isSharedCheck_5428_; 
v_a_5421_ = lean_ctor_get(v___x_5412_, 0);
v_isSharedCheck_5428_ = !lean_is_exclusive(v___x_5412_);
if (v_isSharedCheck_5428_ == 0)
{
v___x_5423_ = v___x_5412_;
v_isShared_5424_ = v_isSharedCheck_5428_;
goto v_resetjp_5422_;
}
else
{
lean_inc(v_a_5421_);
lean_dec(v___x_5412_);
v___x_5423_ = lean_box(0);
v_isShared_5424_ = v_isSharedCheck_5428_;
goto v_resetjp_5422_;
}
v_resetjp_5422_:
{
lean_object* v___x_5426_; 
if (v_isShared_5424_ == 0)
{
lean_ctor_set_tag(v___x_5423_, 0);
v___x_5426_ = v___x_5423_;
goto v_reusejp_5425_;
}
else
{
lean_object* v_reuseFailAlloc_5427_; 
v_reuseFailAlloc_5427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5427_, 0, v_a_5421_);
v___x_5426_ = v_reuseFailAlloc_5427_;
goto v_reusejp_5425_;
}
v_reusejp_5425_:
{
v___y_5378_ = v___x_5411_;
v___y_5379_ = v_a_5408_;
v_a_5380_ = v___x_5426_;
goto v___jp_5377_;
}
}
}
}
else
{
lean_object* v___x_5429_; lean_object* v___x_5430_; 
lean_del_object(v___x_5268_);
v___x_5429_ = lean_io_get_num_heartbeats();
v___x_5430_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v_a_5370_, v___x_5221_, v___y_5227_, v___y_5228_, v___y_5229_, v___y_5230_, v___y_5231_, v___y_5232_);
if (lean_obj_tag(v___x_5430_) == 0)
{
lean_object* v_a_5431_; lean_object* v___x_5433_; uint8_t v_isShared_5434_; uint8_t v_isSharedCheck_5438_; 
v_a_5431_ = lean_ctor_get(v___x_5430_, 0);
v_isSharedCheck_5438_ = !lean_is_exclusive(v___x_5430_);
if (v_isSharedCheck_5438_ == 0)
{
v___x_5433_ = v___x_5430_;
v_isShared_5434_ = v_isSharedCheck_5438_;
goto v_resetjp_5432_;
}
else
{
lean_inc(v_a_5431_);
lean_dec(v___x_5430_);
v___x_5433_ = lean_box(0);
v_isShared_5434_ = v_isSharedCheck_5438_;
goto v_resetjp_5432_;
}
v_resetjp_5432_:
{
lean_object* v___x_5436_; 
if (v_isShared_5434_ == 0)
{
lean_ctor_set_tag(v___x_5433_, 1);
v___x_5436_ = v___x_5433_;
goto v_reusejp_5435_;
}
else
{
lean_object* v_reuseFailAlloc_5437_; 
v_reuseFailAlloc_5437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5437_, 0, v_a_5431_);
v___x_5436_ = v_reuseFailAlloc_5437_;
goto v_reusejp_5435_;
}
v_reusejp_5435_:
{
v___y_5395_ = v_a_5408_;
v___y_5396_ = v___x_5429_;
v_a_5397_ = v___x_5436_;
goto v___jp_5394_;
}
}
}
else
{
lean_object* v_a_5439_; lean_object* v___x_5441_; uint8_t v_isShared_5442_; uint8_t v_isSharedCheck_5446_; 
v_a_5439_ = lean_ctor_get(v___x_5430_, 0);
v_isSharedCheck_5446_ = !lean_is_exclusive(v___x_5430_);
if (v_isSharedCheck_5446_ == 0)
{
v___x_5441_ = v___x_5430_;
v_isShared_5442_ = v_isSharedCheck_5446_;
goto v_resetjp_5440_;
}
else
{
lean_inc(v_a_5439_);
lean_dec(v___x_5430_);
v___x_5441_ = lean_box(0);
v_isShared_5442_ = v_isSharedCheck_5446_;
goto v_resetjp_5440_;
}
v_resetjp_5440_:
{
lean_object* v___x_5444_; 
if (v_isShared_5442_ == 0)
{
lean_ctor_set_tag(v___x_5441_, 0);
v___x_5444_ = v___x_5441_;
goto v_reusejp_5443_;
}
else
{
lean_object* v_reuseFailAlloc_5445_; 
v_reuseFailAlloc_5445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5445_, 0, v_a_5439_);
v___x_5444_ = v_reuseFailAlloc_5445_;
goto v_reusejp_5443_;
}
v_reusejp_5443_:
{
v___y_5395_ = v_a_5408_;
v___y_5396_ = v___x_5429_;
v_a_5397_ = v___x_5444_;
goto v___jp_5394_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5450_; lean_object* v___x_5452_; uint8_t v_isShared_5453_; uint8_t v_isSharedCheck_5457_; 
lean_del_object(v___x_5268_);
lean_dec(v_snd_5266_);
lean_dec_ref(v___x_5221_);
lean_dec(v_a_5220_);
v_a_5450_ = lean_ctor_get(v___x_5365_, 0);
v_isSharedCheck_5457_ = !lean_is_exclusive(v___x_5365_);
if (v_isSharedCheck_5457_ == 0)
{
v___x_5452_ = v___x_5365_;
v_isShared_5453_ = v_isSharedCheck_5457_;
goto v_resetjp_5451_;
}
else
{
lean_inc(v_a_5450_);
lean_dec(v___x_5365_);
v___x_5452_ = lean_box(0);
v_isShared_5453_ = v_isSharedCheck_5457_;
goto v_resetjp_5451_;
}
v_resetjp_5451_:
{
lean_object* v___x_5455_; 
if (v_isShared_5453_ == 0)
{
v___x_5455_ = v___x_5452_;
goto v_reusejp_5454_;
}
else
{
lean_object* v_reuseFailAlloc_5456_; 
v_reuseFailAlloc_5456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5456_, 0, v_a_5450_);
v___x_5455_ = v_reuseFailAlloc_5456_;
goto v_reusejp_5454_;
}
v_reusejp_5454_:
{
return v___x_5455_;
}
}
}
}
}
else
{
lean_object* v_val_5458_; lean_object* v___x_5460_; 
lean_del_object(v___x_5268_);
lean_dec(v_snd_5266_);
lean_dec_ref(v___x_5221_);
lean_dec(v_a_5220_);
v_val_5458_ = lean_ctor_get(v_fst_5265_, 0);
lean_inc(v_val_5458_);
lean_dec_ref(v_fst_5265_);
if (v_isShared_5264_ == 0)
{
lean_ctor_set(v___x_5263_, 0, v_val_5458_);
v___x_5460_ = v___x_5263_;
goto v_reusejp_5459_;
}
else
{
lean_object* v_reuseFailAlloc_5461_; 
v_reuseFailAlloc_5461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5461_, 0, v_val_5458_);
v___x_5460_ = v_reuseFailAlloc_5461_;
goto v_reusejp_5459_;
}
v_reusejp_5459_:
{
return v___x_5460_;
}
}
v___jp_5270_:
{
lean_object* v___x_5276_; 
v___x_5276_ = l_Lean_MVarId_assertHypotheses(v_mvarIdNew_5271_, v_snd_5266_, v___y_5272_, v___y_5273_, v___y_5274_, v___y_5275_);
if (lean_obj_tag(v___x_5276_) == 0)
{
lean_object* v_a_5277_; lean_object* v_snd_5278_; lean_object* v___x_5279_; 
v_a_5277_ = lean_ctor_get(v___x_5276_, 0);
lean_inc(v_a_5277_);
lean_dec_ref(v___x_5276_);
v_snd_5278_ = lean_ctor_get(v_a_5277_, 1);
lean_inc(v_snd_5278_);
lean_dec(v_a_5277_);
v___x_5279_ = l_Lean_MVarId_tryClearMany(v_snd_5278_, v_fvarIdsToSimp_5222_, v___y_5272_, v___y_5273_, v___y_5274_, v___y_5275_);
if (lean_obj_tag(v___x_5279_) == 0)
{
lean_object* v_a_5280_; lean_object* v___x_5281_; 
v_a_5280_ = lean_ctor_get(v___x_5279_, 0);
lean_inc(v_a_5280_);
lean_dec_ref(v___x_5279_);
v___x_5281_ = l_Lean_Meta_saveState___redArg(v___y_5273_, v___y_5275_);
if (lean_obj_tag(v___x_5281_) == 0)
{
lean_object* v_a_5282_; uint8_t v___x_5283_; lean_object* v___x_5284_; 
v_a_5282_ = lean_ctor_get(v___x_5281_, 0);
lean_inc(v_a_5282_);
lean_dec_ref(v___x_5281_);
v___x_5283_ = 1;
lean_inc(v_a_5280_);
v___x_5284_ = l_Lean_MVarId_refl(v_a_5280_, v___x_5283_, v___y_5272_, v___y_5273_, v___y_5274_, v___y_5275_);
if (lean_obj_tag(v___x_5284_) == 0)
{
lean_object* v___x_5286_; uint8_t v_isShared_5287_; uint8_t v_isSharedCheck_5292_; 
lean_dec(v_a_5282_);
lean_dec(v_a_5280_);
v_isSharedCheck_5292_ = !lean_is_exclusive(v___x_5284_);
if (v_isSharedCheck_5292_ == 0)
{
lean_object* v_unused_5293_; 
v_unused_5293_ = lean_ctor_get(v___x_5284_, 0);
lean_dec(v_unused_5293_);
v___x_5286_ = v___x_5284_;
v_isShared_5287_ = v_isSharedCheck_5292_;
goto v_resetjp_5285_;
}
else
{
lean_dec(v___x_5284_);
v___x_5286_ = lean_box(0);
v_isShared_5287_ = v_isSharedCheck_5292_;
goto v_resetjp_5285_;
}
v_resetjp_5285_:
{
lean_object* v___x_5288_; lean_object* v___x_5290_; 
v___x_5288_ = lean_box(0);
if (v_isShared_5287_ == 0)
{
lean_ctor_set(v___x_5286_, 0, v___x_5288_);
v___x_5290_ = v___x_5286_;
goto v_reusejp_5289_;
}
else
{
lean_object* v_reuseFailAlloc_5291_; 
v_reuseFailAlloc_5291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5291_, 0, v___x_5288_);
v___x_5290_ = v_reuseFailAlloc_5291_;
goto v_reusejp_5289_;
}
v_reusejp_5289_:
{
return v___x_5290_;
}
}
}
else
{
lean_object* v_a_5294_; uint8_t v___x_5295_; 
v_a_5294_ = lean_ctor_get(v___x_5284_, 0);
lean_inc(v_a_5294_);
lean_dec_ref(v___x_5284_);
v___x_5295_ = l_Lean_Exception_isInterrupt(v_a_5294_);
if (v___x_5295_ == 0)
{
uint8_t v___x_5296_; 
lean_inc(v_a_5294_);
v___x_5296_ = l_Lean_Exception_isRuntime(v_a_5294_);
v___y_5235_ = v_a_5280_;
v___y_5236_ = v___y_5273_;
v___y_5237_ = v_a_5294_;
v___y_5238_ = v_a_5282_;
v___y_5239_ = v___y_5275_;
v___y_5240_ = v___x_5296_;
goto v___jp_5234_;
}
else
{
v___y_5235_ = v_a_5280_;
v___y_5236_ = v___y_5273_;
v___y_5237_ = v_a_5294_;
v___y_5238_ = v_a_5282_;
v___y_5239_ = v___y_5275_;
v___y_5240_ = v___x_5295_;
goto v___jp_5234_;
}
}
}
else
{
lean_object* v_a_5297_; lean_object* v___x_5299_; uint8_t v_isShared_5300_; uint8_t v_isSharedCheck_5304_; 
lean_dec(v_a_5280_);
v_a_5297_ = lean_ctor_get(v___x_5281_, 0);
v_isSharedCheck_5304_ = !lean_is_exclusive(v___x_5281_);
if (v_isSharedCheck_5304_ == 0)
{
v___x_5299_ = v___x_5281_;
v_isShared_5300_ = v_isSharedCheck_5304_;
goto v_resetjp_5298_;
}
else
{
lean_inc(v_a_5297_);
lean_dec(v___x_5281_);
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
lean_object* v_a_5305_; lean_object* v___x_5307_; uint8_t v_isShared_5308_; uint8_t v_isSharedCheck_5312_; 
v_a_5305_ = lean_ctor_get(v___x_5279_, 0);
v_isSharedCheck_5312_ = !lean_is_exclusive(v___x_5279_);
if (v_isSharedCheck_5312_ == 0)
{
v___x_5307_ = v___x_5279_;
v_isShared_5308_ = v_isSharedCheck_5312_;
goto v_resetjp_5306_;
}
else
{
lean_inc(v_a_5305_);
lean_dec(v___x_5279_);
v___x_5307_ = lean_box(0);
v_isShared_5308_ = v_isSharedCheck_5312_;
goto v_resetjp_5306_;
}
v_resetjp_5306_:
{
lean_object* v___x_5310_; 
if (v_isShared_5308_ == 0)
{
v___x_5310_ = v___x_5307_;
goto v_reusejp_5309_;
}
else
{
lean_object* v_reuseFailAlloc_5311_; 
v_reuseFailAlloc_5311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5311_, 0, v_a_5305_);
v___x_5310_ = v_reuseFailAlloc_5311_;
goto v_reusejp_5309_;
}
v_reusejp_5309_:
{
return v___x_5310_;
}
}
}
}
else
{
lean_object* v_a_5313_; lean_object* v___x_5315_; uint8_t v_isShared_5316_; uint8_t v_isSharedCheck_5320_; 
v_a_5313_ = lean_ctor_get(v___x_5276_, 0);
v_isSharedCheck_5320_ = !lean_is_exclusive(v___x_5276_);
if (v_isSharedCheck_5320_ == 0)
{
v___x_5315_ = v___x_5276_;
v_isShared_5316_ = v_isSharedCheck_5320_;
goto v_resetjp_5314_;
}
else
{
lean_inc(v_a_5313_);
lean_dec(v___x_5276_);
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
v___jp_5321_:
{
if (lean_obj_tag(v___y_5322_) == 0)
{
lean_object* v_a_5323_; 
v_a_5323_ = lean_ctor_get(v___y_5322_, 0);
lean_inc(v_a_5323_);
lean_dec_ref(v___y_5322_);
if (lean_obj_tag(v_a_5323_) == 0)
{
lean_dec_ref(v_a_5323_);
v_mvarIdNew_5271_ = v_a_5220_;
v___y_5272_ = v___y_5229_;
v___y_5273_ = v___y_5230_;
v___y_5274_ = v___y_5231_;
v___y_5275_ = v___y_5232_;
goto v___jp_5270_;
}
else
{
lean_object* v_e_x27_5324_; lean_object* v_proof_5325_; uint8_t v___x_5326_; 
v_e_x27_5324_ = lean_ctor_get(v_a_5323_, 0);
lean_inc_ref_n(v_e_x27_5324_, 2);
v_proof_5325_ = lean_ctor_get(v_a_5323_, 1);
lean_inc_ref(v_proof_5325_);
lean_dec_ref(v_a_5323_);
v___x_5326_ = l_Lean_Expr_isTrue(v_e_x27_5324_);
if (v___x_5326_ == 0)
{
lean_object* v___x_5327_; 
v___x_5327_ = l_Lean_MVarId_replaceTargetEq(v_a_5220_, v_e_x27_5324_, v_proof_5325_, v___y_5229_, v___y_5230_, v___y_5231_, v___y_5232_);
if (lean_obj_tag(v___x_5327_) == 0)
{
lean_object* v_a_5328_; 
v_a_5328_ = lean_ctor_get(v___x_5327_, 0);
lean_inc(v_a_5328_);
lean_dec_ref(v___x_5327_);
v_mvarIdNew_5271_ = v_a_5328_;
v___y_5272_ = v___y_5229_;
v___y_5273_ = v___y_5230_;
v___y_5274_ = v___y_5231_;
v___y_5275_ = v___y_5232_;
goto v___jp_5270_;
}
else
{
lean_object* v_a_5329_; lean_object* v___x_5331_; uint8_t v_isShared_5332_; uint8_t v_isSharedCheck_5336_; 
lean_dec(v_snd_5266_);
v_a_5329_ = lean_ctor_get(v___x_5327_, 0);
v_isSharedCheck_5336_ = !lean_is_exclusive(v___x_5327_);
if (v_isSharedCheck_5336_ == 0)
{
v___x_5331_ = v___x_5327_;
v_isShared_5332_ = v_isSharedCheck_5336_;
goto v_resetjp_5330_;
}
else
{
lean_inc(v_a_5329_);
lean_dec(v___x_5327_);
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
else
{
lean_object* v___x_5337_; 
lean_dec_ref(v_e_x27_5324_);
lean_dec(v_snd_5266_);
v___x_5337_ = l_Lean_Meta_mkOfEqTrue(v_proof_5325_, v___y_5229_, v___y_5230_, v___y_5231_, v___y_5232_);
if (lean_obj_tag(v___x_5337_) == 0)
{
lean_object* v_a_5338_; lean_object* v___x_5339_; lean_object* v___x_5341_; uint8_t v_isShared_5342_; uint8_t v_isSharedCheck_5347_; 
v_a_5338_ = lean_ctor_get(v___x_5337_, 0);
lean_inc(v_a_5338_);
lean_dec_ref(v___x_5337_);
v___x_5339_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0___redArg(v_a_5220_, v_a_5338_, v___y_5230_);
v_isSharedCheck_5347_ = !lean_is_exclusive(v___x_5339_);
if (v_isSharedCheck_5347_ == 0)
{
lean_object* v_unused_5348_; 
v_unused_5348_ = lean_ctor_get(v___x_5339_, 0);
lean_dec(v_unused_5348_);
v___x_5341_ = v___x_5339_;
v_isShared_5342_ = v_isSharedCheck_5347_;
goto v_resetjp_5340_;
}
else
{
lean_dec(v___x_5339_);
v___x_5341_ = lean_box(0);
v_isShared_5342_ = v_isSharedCheck_5347_;
goto v_resetjp_5340_;
}
v_resetjp_5340_:
{
lean_object* v___x_5343_; lean_object* v___x_5345_; 
v___x_5343_ = lean_box(0);
if (v_isShared_5342_ == 0)
{
lean_ctor_set(v___x_5341_, 0, v___x_5343_);
v___x_5345_ = v___x_5341_;
goto v_reusejp_5344_;
}
else
{
lean_object* v_reuseFailAlloc_5346_; 
v_reuseFailAlloc_5346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5346_, 0, v___x_5343_);
v___x_5345_ = v_reuseFailAlloc_5346_;
goto v_reusejp_5344_;
}
v_reusejp_5344_:
{
return v___x_5345_;
}
}
}
else
{
lean_object* v_a_5349_; lean_object* v___x_5351_; uint8_t v_isShared_5352_; uint8_t v_isSharedCheck_5356_; 
lean_dec(v_a_5220_);
v_a_5349_ = lean_ctor_get(v___x_5337_, 0);
v_isSharedCheck_5356_ = !lean_is_exclusive(v___x_5337_);
if (v_isSharedCheck_5356_ == 0)
{
v___x_5351_ = v___x_5337_;
v_isShared_5352_ = v_isSharedCheck_5356_;
goto v_resetjp_5350_;
}
else
{
lean_inc(v_a_5349_);
lean_dec(v___x_5337_);
v___x_5351_ = lean_box(0);
v_isShared_5352_ = v_isSharedCheck_5356_;
goto v_resetjp_5350_;
}
v_resetjp_5350_:
{
lean_object* v___x_5354_; 
if (v_isShared_5352_ == 0)
{
v___x_5354_ = v___x_5351_;
goto v_reusejp_5353_;
}
else
{
lean_object* v_reuseFailAlloc_5355_; 
v_reuseFailAlloc_5355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5355_, 0, v_a_5349_);
v___x_5354_ = v_reuseFailAlloc_5355_;
goto v_reusejp_5353_;
}
v_reusejp_5353_:
{
return v___x_5354_;
}
}
}
}
}
}
else
{
lean_object* v_a_5357_; lean_object* v___x_5359_; uint8_t v_isShared_5360_; uint8_t v_isSharedCheck_5364_; 
lean_dec(v_snd_5266_);
lean_dec(v_a_5220_);
v_a_5357_ = lean_ctor_get(v___y_5322_, 0);
v_isSharedCheck_5364_ = !lean_is_exclusive(v___y_5322_);
if (v_isSharedCheck_5364_ == 0)
{
v___x_5359_ = v___y_5322_;
v_isShared_5360_ = v_isSharedCheck_5364_;
goto v_resetjp_5358_;
}
else
{
lean_inc(v_a_5357_);
lean_dec(v___y_5322_);
v___x_5359_ = lean_box(0);
v_isShared_5360_ = v_isSharedCheck_5364_;
goto v_resetjp_5358_;
}
v_resetjp_5358_:
{
lean_object* v___x_5362_; 
if (v_isShared_5360_ == 0)
{
v___x_5362_ = v___x_5359_;
goto v_reusejp_5361_;
}
else
{
lean_object* v_reuseFailAlloc_5363_; 
v_reuseFailAlloc_5363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5363_, 0, v_a_5357_);
v___x_5362_ = v_reuseFailAlloc_5363_;
goto v_reusejp_5361_;
}
v_reusejp_5361_:
{
return v___x_5362_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5464_; lean_object* v___x_5466_; uint8_t v_isShared_5467_; uint8_t v_isSharedCheck_5471_; 
lean_dec_ref(v___x_5221_);
lean_dec(v_a_5220_);
v_a_5464_ = lean_ctor_get(v___x_5260_, 0);
v_isSharedCheck_5471_ = !lean_is_exclusive(v___x_5260_);
if (v_isSharedCheck_5471_ == 0)
{
v___x_5466_ = v___x_5260_;
v_isShared_5467_ = v_isSharedCheck_5471_;
goto v_resetjp_5465_;
}
else
{
lean_inc(v_a_5464_);
lean_dec(v___x_5260_);
v___x_5466_ = lean_box(0);
v_isShared_5467_ = v_isSharedCheck_5471_;
goto v_resetjp_5465_;
}
v_resetjp_5465_:
{
lean_object* v___x_5469_; 
if (v_isShared_5467_ == 0)
{
v___x_5469_ = v___x_5466_;
goto v_reusejp_5468_;
}
else
{
lean_object* v_reuseFailAlloc_5470_; 
v_reuseFailAlloc_5470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5470_, 0, v_a_5464_);
v___x_5469_ = v_reuseFailAlloc_5470_;
goto v_reusejp_5468_;
}
v_reusejp_5468_:
{
return v___x_5469_;
}
}
}
v___jp_5234_:
{
if (v___y_5240_ == 0)
{
lean_object* v___x_5241_; 
lean_dec_ref(v___y_5237_);
v___x_5241_ = l_Lean_Meta_SavedState_restore___redArg(v___y_5238_, v___y_5236_, v___y_5239_);
lean_dec_ref(v___y_5238_);
if (lean_obj_tag(v___x_5241_) == 0)
{
lean_object* v___x_5243_; uint8_t v_isShared_5244_; uint8_t v_isSharedCheck_5249_; 
v_isSharedCheck_5249_ = !lean_is_exclusive(v___x_5241_);
if (v_isSharedCheck_5249_ == 0)
{
lean_object* v_unused_5250_; 
v_unused_5250_ = lean_ctor_get(v___x_5241_, 0);
lean_dec(v_unused_5250_);
v___x_5243_ = v___x_5241_;
v_isShared_5244_ = v_isSharedCheck_5249_;
goto v_resetjp_5242_;
}
else
{
lean_dec(v___x_5241_);
v___x_5243_ = lean_box(0);
v_isShared_5244_ = v_isSharedCheck_5249_;
goto v_resetjp_5242_;
}
v_resetjp_5242_:
{
lean_object* v___x_5245_; lean_object* v___x_5247_; 
v___x_5245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5245_, 0, v___y_5235_);
if (v_isShared_5244_ == 0)
{
lean_ctor_set(v___x_5243_, 0, v___x_5245_);
v___x_5247_ = v___x_5243_;
goto v_reusejp_5246_;
}
else
{
lean_object* v_reuseFailAlloc_5248_; 
v_reuseFailAlloc_5248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5248_, 0, v___x_5245_);
v___x_5247_ = v_reuseFailAlloc_5248_;
goto v_reusejp_5246_;
}
v_reusejp_5246_:
{
return v___x_5247_;
}
}
}
else
{
lean_object* v_a_5251_; lean_object* v___x_5253_; uint8_t v_isShared_5254_; uint8_t v_isSharedCheck_5258_; 
lean_dec(v___y_5235_);
v_a_5251_ = lean_ctor_get(v___x_5241_, 0);
v_isSharedCheck_5258_ = !lean_is_exclusive(v___x_5241_);
if (v_isSharedCheck_5258_ == 0)
{
v___x_5253_ = v___x_5241_;
v_isShared_5254_ = v_isSharedCheck_5258_;
goto v_resetjp_5252_;
}
else
{
lean_inc(v_a_5251_);
lean_dec(v___x_5241_);
v___x_5253_ = lean_box(0);
v_isShared_5254_ = v_isSharedCheck_5258_;
goto v_resetjp_5252_;
}
v_resetjp_5252_:
{
lean_object* v___x_5256_; 
if (v_isShared_5254_ == 0)
{
v___x_5256_ = v___x_5253_;
goto v_reusejp_5255_;
}
else
{
lean_object* v_reuseFailAlloc_5257_; 
v_reuseFailAlloc_5257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5257_, 0, v_a_5251_);
v___x_5256_ = v_reuseFailAlloc_5257_;
goto v_reusejp_5255_;
}
v_reusejp_5255_:
{
return v___x_5256_;
}
}
}
}
else
{
lean_object* v___x_5259_; 
lean_dec_ref(v___y_5238_);
lean_dec(v___y_5235_);
v___x_5259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5259_, 0, v___y_5237_);
return v___x_5259_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__1___boxed(lean_object* v_a_5472_, lean_object* v___x_5473_, lean_object* v_fvarIdsToSimp_5474_, lean_object* v_sz_5475_, lean_object* v___x_5476_, lean_object* v___x_5477_, lean_object* v_simplifyTarget_5478_, lean_object* v___y_5479_, lean_object* v___y_5480_, lean_object* v___y_5481_, lean_object* v___y_5482_, lean_object* v___y_5483_, lean_object* v___y_5484_, lean_object* v___y_5485_){
_start:
{
size_t v_sz_boxed_5486_; size_t v___x_49704__boxed_5487_; uint8_t v_simplifyTarget_boxed_5488_; lean_object* v_res_5489_; 
v_sz_boxed_5486_ = lean_unbox_usize(v_sz_5475_);
lean_dec(v_sz_5475_);
v___x_49704__boxed_5487_ = lean_unbox_usize(v___x_5476_);
lean_dec(v___x_5476_);
v_simplifyTarget_boxed_5488_ = lean_unbox(v_simplifyTarget_5478_);
v_res_5489_ = l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__1(v_a_5472_, v___x_5473_, v_fvarIdsToSimp_5474_, v_sz_boxed_5486_, v___x_49704__boxed_5487_, v___x_5477_, v_simplifyTarget_boxed_5488_, v___y_5479_, v___y_5480_, v___y_5481_, v___y_5482_, v___y_5483_, v___y_5484_);
lean_dec(v___y_5484_);
lean_dec_ref(v___y_5483_);
lean_dec(v___y_5482_);
lean_dec_ref(v___y_5481_);
lean_dec(v___y_5480_);
lean_dec_ref(v___y_5479_);
lean_dec_ref(v_fvarIdsToSimp_5474_);
return v_res_5489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__2(lean_object* v_mvarId_5497_, lean_object* v_fvarIdsToSimp_5498_, lean_object* v___x_5499_, uint8_t v_simplifyTarget_5500_, lean_object* v___y_5501_, lean_object* v___y_5502_, lean_object* v___y_5503_, lean_object* v___y_5504_, lean_object* v___y_5505_, lean_object* v___y_5506_){
_start:
{
lean_object* v___x_5508_; 
v___x_5508_ = l_Lean_Meta_Sym_preprocessMVar(v_mvarId_5497_, v___y_5501_, v___y_5502_, v___y_5503_, v___y_5504_, v___y_5505_, v___y_5506_);
if (lean_obj_tag(v___x_5508_) == 0)
{
lean_object* v_a_5509_; lean_object* v___x_5510_; size_t v_sz_5511_; lean_object* v___x_5512_; lean_object* v___x_5513_; lean_object* v___x_5514_; lean_object* v___f_5515_; lean_object* v___x_5516_; 
v_a_5509_ = lean_ctor_get(v___x_5508_, 0);
lean_inc_n(v_a_5509_, 2);
lean_dec_ref(v___x_5508_);
v___x_5510_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__2___closed__1));
v_sz_5511_ = lean_array_size(v_fvarIdsToSimp_5498_);
v___x_5512_ = lean_box_usize(v_sz_5511_);
v___x_5513_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__2___boxed__const__1));
v___x_5514_ = lean_box(v_simplifyTarget_5500_);
v___f_5515_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__1___boxed), 14, 7);
lean_closure_set(v___f_5515_, 0, v_a_5509_);
lean_closure_set(v___f_5515_, 1, v___x_5499_);
lean_closure_set(v___f_5515_, 2, v_fvarIdsToSimp_5498_);
lean_closure_set(v___f_5515_, 3, v___x_5512_);
lean_closure_set(v___f_5515_, 4, v___x_5513_);
lean_closure_set(v___f_5515_, 5, v___x_5510_);
lean_closure_set(v___f_5515_, 6, v___x_5514_);
v___x_5516_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___redArg(v_a_5509_, v___f_5515_, v___y_5501_, v___y_5502_, v___y_5503_, v___y_5504_, v___y_5505_, v___y_5506_);
return v___x_5516_;
}
else
{
lean_object* v_a_5517_; lean_object* v___x_5519_; uint8_t v_isShared_5520_; uint8_t v_isSharedCheck_5524_; 
lean_dec_ref(v___x_5499_);
lean_dec_ref(v_fvarIdsToSimp_5498_);
v_a_5517_ = lean_ctor_get(v___x_5508_, 0);
v_isSharedCheck_5524_ = !lean_is_exclusive(v___x_5508_);
if (v_isSharedCheck_5524_ == 0)
{
v___x_5519_ = v___x_5508_;
v_isShared_5520_ = v_isSharedCheck_5524_;
goto v_resetjp_5518_;
}
else
{
lean_inc(v_a_5517_);
lean_dec(v___x_5508_);
v___x_5519_ = lean_box(0);
v_isShared_5520_ = v_isSharedCheck_5524_;
goto v_resetjp_5518_;
}
v_resetjp_5518_:
{
lean_object* v___x_5522_; 
if (v_isShared_5520_ == 0)
{
v___x_5522_ = v___x_5519_;
goto v_reusejp_5521_;
}
else
{
lean_object* v_reuseFailAlloc_5523_; 
v_reuseFailAlloc_5523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5523_, 0, v_a_5517_);
v___x_5522_ = v_reuseFailAlloc_5523_;
goto v_reusejp_5521_;
}
v_reusejp_5521_:
{
return v___x_5522_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__2___boxed(lean_object* v_mvarId_5525_, lean_object* v_fvarIdsToSimp_5526_, lean_object* v___x_5527_, lean_object* v_simplifyTarget_5528_, lean_object* v___y_5529_, lean_object* v___y_5530_, lean_object* v___y_5531_, lean_object* v___y_5532_, lean_object* v___y_5533_, lean_object* v___y_5534_, lean_object* v___y_5535_){
_start:
{
uint8_t v_simplifyTarget_boxed_5536_; lean_object* v_res_5537_; 
v_simplifyTarget_boxed_5536_ = lean_unbox(v_simplifyTarget_5528_);
v_res_5537_ = l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__2(v_mvarId_5525_, v_fvarIdsToSimp_5526_, v___x_5527_, v_simplifyTarget_boxed_5536_, v___y_5529_, v___y_5530_, v___y_5531_, v___y_5532_, v___y_5533_, v___y_5534_);
lean_dec(v___y_5534_);
lean_dec_ref(v___y_5533_);
lean_dec(v___y_5532_);
lean_dec_ref(v___y_5531_);
lean_dec(v___y_5530_);
lean_dec_ref(v___y_5529_);
return v_res_5537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal(lean_object* v_mvarId_5538_, uint8_t v_simplifyTarget_5539_, lean_object* v_fvarIdsToSimp_5540_, lean_object* v_a_5541_, lean_object* v_a_5542_, lean_object* v_a_5543_, lean_object* v_a_5544_){
_start:
{
lean_object* v_options_5546_; lean_object* v___x_5547_; lean_object* v___x_5548_; lean_object* v___x_5549_; lean_object* v___x_5550_; lean_object* v___x_5551_; lean_object* v___f_5552_; lean_object* v___x_5553_; 
v_options_5546_ = lean_ctor_get(v_a_5543_, 2);
v___x_5547_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_5548_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_5546_, v___x_5547_);
v___x_5549_ = lean_unsigned_to_nat(2u);
v___x_5550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5550_, 0, v___x_5548_);
lean_ctor_set(v___x_5550_, 1, v___x_5549_);
v___x_5551_ = lean_box(v_simplifyTarget_5539_);
v___f_5552_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__2___boxed), 11, 4);
lean_closure_set(v___f_5552_, 0, v_mvarId_5538_);
lean_closure_set(v___f_5552_, 1, v_fvarIdsToSimp_5540_);
lean_closure_set(v___f_5552_, 2, v___x_5550_);
lean_closure_set(v___f_5552_, 3, v___x_5551_);
v___x_5553_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_5552_, v_a_5541_, v_a_5542_, v_a_5543_, v_a_5544_);
return v___x_5553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___boxed(lean_object* v_mvarId_5554_, lean_object* v_simplifyTarget_5555_, lean_object* v_fvarIdsToSimp_5556_, lean_object* v_a_5557_, lean_object* v_a_5558_, lean_object* v_a_5559_, lean_object* v_a_5560_, lean_object* v_a_5561_){
_start:
{
uint8_t v_simplifyTarget_boxed_5562_; lean_object* v_res_5563_; 
v_simplifyTarget_boxed_5562_ = lean_unbox(v_simplifyTarget_5555_);
v_res_5563_ = l_Lean_Meta_Tactic_Cbv_cbvGoal(v_mvarId_5554_, v_simplifyTarget_boxed_5562_, v_fvarIdsToSimp_5556_, v_a_5557_, v_a_5558_, v_a_5559_, v_a_5560_);
lean_dec(v_a_5560_);
lean_dec_ref(v_a_5559_);
lean_dec(v_a_5558_);
lean_dec_ref(v_a_5557_);
return v_res_5563_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0(lean_object* v_mvarId_5564_, lean_object* v_val_5565_, lean_object* v___y_5566_, lean_object* v___y_5567_, lean_object* v___y_5568_, lean_object* v___y_5569_, lean_object* v___y_5570_, lean_object* v___y_5571_){
_start:
{
lean_object* v___x_5573_; 
v___x_5573_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0___redArg(v_mvarId_5564_, v_val_5565_, v___y_5569_);
return v___x_5573_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0___boxed(lean_object* v_mvarId_5574_, lean_object* v_val_5575_, lean_object* v___y_5576_, lean_object* v___y_5577_, lean_object* v___y_5578_, lean_object* v___y_5579_, lean_object* v___y_5580_, lean_object* v___y_5581_, lean_object* v___y_5582_){
_start:
{
lean_object* v_res_5583_; 
v_res_5583_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0(v_mvarId_5574_, v_val_5575_, v___y_5576_, v___y_5577_, v___y_5578_, v___y_5579_, v___y_5580_, v___y_5581_);
lean_dec(v___y_5581_);
lean_dec_ref(v___y_5580_);
lean_dec(v___y_5579_);
lean_dec_ref(v___y_5578_);
lean_dec(v___y_5577_);
lean_dec_ref(v___y_5576_);
return v_res_5583_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2_spec__4(lean_object* v_00_u03b1_5584_, lean_object* v_x_5585_, lean_object* v___y_5586_, lean_object* v___y_5587_, lean_object* v___y_5588_, lean_object* v___y_5589_, lean_object* v___y_5590_, lean_object* v___y_5591_){
_start:
{
lean_object* v___x_5593_; 
v___x_5593_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2_spec__4___redArg(v_x_5585_);
return v___x_5593_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2_spec__4___boxed(lean_object* v_00_u03b1_5594_, lean_object* v_x_5595_, lean_object* v___y_5596_, lean_object* v___y_5597_, lean_object* v___y_5598_, lean_object* v___y_5599_, lean_object* v___y_5600_, lean_object* v___y_5601_, lean_object* v___y_5602_){
_start:
{
lean_object* v_res_5603_; 
v_res_5603_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2_spec__4(v_00_u03b1_5594_, v_x_5595_, v___y_5596_, v___y_5597_, v___y_5598_, v___y_5599_, v___y_5600_, v___y_5601_);
lean_dec(v___y_5601_);
lean_dec_ref(v___y_5600_);
lean_dec(v___y_5599_);
lean_dec_ref(v___y_5598_);
lean_dec(v___y_5597_);
lean_dec_ref(v___y_5596_);
return v_res_5603_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0(lean_object* v_00_u03b2_5604_, lean_object* v_x_5605_, lean_object* v_x_5606_, lean_object* v_x_5607_){
_start:
{
lean_object* v___x_5608_; 
v___x_5608_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0___redArg(v_x_5605_, v_x_5606_, v_x_5607_);
return v___x_5608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2_spec__3(lean_object* v_oldTraces_5609_, lean_object* v_data_5610_, lean_object* v_ref_5611_, lean_object* v_msg_5612_, lean_object* v___y_5613_, lean_object* v___y_5614_, lean_object* v___y_5615_, lean_object* v___y_5616_, lean_object* v___y_5617_, lean_object* v___y_5618_){
_start:
{
lean_object* v___x_5620_; 
v___x_5620_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2_spec__3___redArg(v_oldTraces_5609_, v_data_5610_, v_ref_5611_, v_msg_5612_, v___y_5615_, v___y_5616_, v___y_5617_, v___y_5618_);
return v___x_5620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2_spec__3___boxed(lean_object* v_oldTraces_5621_, lean_object* v_data_5622_, lean_object* v_ref_5623_, lean_object* v_msg_5624_, lean_object* v___y_5625_, lean_object* v___y_5626_, lean_object* v___y_5627_, lean_object* v___y_5628_, lean_object* v___y_5629_, lean_object* v___y_5630_, lean_object* v___y_5631_){
_start:
{
lean_object* v_res_5632_; 
v_res_5632_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2_spec__3(v_oldTraces_5621_, v_data_5622_, v_ref_5623_, v_msg_5624_, v___y_5625_, v___y_5626_, v___y_5627_, v___y_5628_, v___y_5629_, v___y_5630_);
lean_dec(v___y_5630_);
lean_dec_ref(v___y_5629_);
lean_dec(v___y_5628_);
lean_dec_ref(v___y_5627_);
lean_dec(v___y_5626_);
lean_dec_ref(v___y_5625_);
return v_res_5632_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_5633_, lean_object* v_x_5634_, size_t v_x_5635_, size_t v_x_5636_, lean_object* v_x_5637_, lean_object* v_x_5638_){
_start:
{
lean_object* v___x_5639_; 
v___x_5639_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3___redArg(v_x_5634_, v_x_5635_, v_x_5636_, v_x_5637_, v_x_5638_);
return v___x_5639_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_5640_, lean_object* v_x_5641_, lean_object* v_x_5642_, lean_object* v_x_5643_, lean_object* v_x_5644_, lean_object* v_x_5645_){
_start:
{
size_t v_x_50389__boxed_5646_; size_t v_x_50390__boxed_5647_; lean_object* v_res_5648_; 
v_x_50389__boxed_5646_ = lean_unbox_usize(v_x_5642_);
lean_dec(v_x_5642_);
v_x_50390__boxed_5647_ = lean_unbox_usize(v_x_5643_);
lean_dec(v_x_5643_);
v_res_5648_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3(v_00_u03b2_5640_, v_x_5641_, v_x_50389__boxed_5646_, v_x_50390__boxed_5647_, v_x_5644_, v_x_5645_);
return v_res_5648_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3_spec__7(lean_object* v_00_u03b2_5649_, lean_object* v_n_5650_, lean_object* v_k_5651_, lean_object* v_v_5652_){
_start:
{
lean_object* v___x_5653_; 
v___x_5653_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3_spec__7___redArg(v_n_5650_, v_k_5651_, v_v_5652_);
return v___x_5653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3_spec__8(lean_object* v_00_u03b2_5654_, size_t v_depth_5655_, lean_object* v_keys_5656_, lean_object* v_vals_5657_, lean_object* v_heq_5658_, lean_object* v_i_5659_, lean_object* v_entries_5660_){
_start:
{
lean_object* v___x_5661_; 
v___x_5661_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3_spec__8___redArg(v_depth_5655_, v_keys_5656_, v_vals_5657_, v_i_5659_, v_entries_5660_);
return v___x_5661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3_spec__8___boxed(lean_object* v_00_u03b2_5662_, lean_object* v_depth_5663_, lean_object* v_keys_5664_, lean_object* v_vals_5665_, lean_object* v_heq_5666_, lean_object* v_i_5667_, lean_object* v_entries_5668_){
_start:
{
size_t v_depth_boxed_5669_; lean_object* v_res_5670_; 
v_depth_boxed_5669_ = lean_unbox_usize(v_depth_5663_);
lean_dec(v_depth_5663_);
v_res_5670_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3_spec__8(v_00_u03b2_5662_, v_depth_boxed_5669_, v_keys_5664_, v_vals_5665_, v_heq_5666_, v_i_5667_, v_entries_5668_);
lean_dec_ref(v_vals_5665_);
lean_dec_ref(v_keys_5664_);
return v_res_5670_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3_spec__7_spec__9(lean_object* v_00_u03b2_5671_, lean_object* v_x_5672_, lean_object* v_x_5673_, lean_object* v_x_5674_, lean_object* v_x_5675_){
_start:
{
lean_object* v___x_5676_; 
v___x_5676_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__3_spec__7_spec__9___redArg(v_x_5672_, v_x_5673_, v_x_5674_, v_x_5675_);
return v___x_5676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0(lean_object* v_a_5677_, uint8_t v___x_5678_, lean_object* v___y_5679_, lean_object* v___y_5680_, lean_object* v___y_5681_, lean_object* v___y_5682_, lean_object* v___y_5683_, lean_object* v___y_5684_){
_start:
{
lean_object* v___x_5686_; 
v___x_5686_ = l_Lean_MVarId_refl(v_a_5677_, v___x_5678_, v___y_5681_, v___y_5682_, v___y_5683_, v___y_5684_);
return v___x_5686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0___boxed(lean_object* v_a_5687_, lean_object* v___x_5688_, lean_object* v___y_5689_, lean_object* v___y_5690_, lean_object* v___y_5691_, lean_object* v___y_5692_, lean_object* v___y_5693_, lean_object* v___y_5694_, lean_object* v___y_5695_){
_start:
{
uint8_t v___x_25219__boxed_5696_; lean_object* v_res_5697_; 
v___x_25219__boxed_5696_ = lean_unbox(v___x_5688_);
v_res_5697_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0(v_a_5687_, v___x_25219__boxed_5696_, v___y_5689_, v___y_5690_, v___y_5691_, v___y_5692_, v___y_5693_, v___y_5694_);
lean_dec(v___y_5694_);
lean_dec_ref(v___y_5693_);
lean_dec(v___y_5692_);
lean_dec_ref(v___y_5691_);
lean_dec(v___y_5690_);
lean_dec_ref(v___y_5689_);
return v_res_5697_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(lean_object* v_cls_5698_, lean_object* v_msg_5699_, lean_object* v___y_5700_, lean_object* v___y_5701_, lean_object* v___y_5702_, lean_object* v___y_5703_){
_start:
{
lean_object* v_ref_5705_; lean_object* v___x_5706_; lean_object* v_a_5707_; lean_object* v___x_5709_; uint8_t v_isShared_5710_; uint8_t v_isSharedCheck_5752_; 
v_ref_5705_ = lean_ctor_get(v___y_5702_, 5);
v___x_5706_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0_spec__0(v_msg_5699_, v___y_5700_, v___y_5701_, v___y_5702_, v___y_5703_);
v_a_5707_ = lean_ctor_get(v___x_5706_, 0);
v_isSharedCheck_5752_ = !lean_is_exclusive(v___x_5706_);
if (v_isSharedCheck_5752_ == 0)
{
v___x_5709_ = v___x_5706_;
v_isShared_5710_ = v_isSharedCheck_5752_;
goto v_resetjp_5708_;
}
else
{
lean_inc(v_a_5707_);
lean_dec(v___x_5706_);
v___x_5709_ = lean_box(0);
v_isShared_5710_ = v_isSharedCheck_5752_;
goto v_resetjp_5708_;
}
v_resetjp_5708_:
{
lean_object* v___x_5711_; lean_object* v_traceState_5712_; lean_object* v_env_5713_; lean_object* v_nextMacroScope_5714_; lean_object* v_ngen_5715_; lean_object* v_auxDeclNGen_5716_; lean_object* v_cache_5717_; lean_object* v_messages_5718_; lean_object* v_infoState_5719_; lean_object* v_snapshotTasks_5720_; lean_object* v_newDecls_5721_; lean_object* v___x_5723_; uint8_t v_isShared_5724_; uint8_t v_isSharedCheck_5751_; 
v___x_5711_ = lean_st_ref_take(v___y_5703_);
v_traceState_5712_ = lean_ctor_get(v___x_5711_, 4);
v_env_5713_ = lean_ctor_get(v___x_5711_, 0);
v_nextMacroScope_5714_ = lean_ctor_get(v___x_5711_, 1);
v_ngen_5715_ = lean_ctor_get(v___x_5711_, 2);
v_auxDeclNGen_5716_ = lean_ctor_get(v___x_5711_, 3);
v_cache_5717_ = lean_ctor_get(v___x_5711_, 5);
v_messages_5718_ = lean_ctor_get(v___x_5711_, 6);
v_infoState_5719_ = lean_ctor_get(v___x_5711_, 7);
v_snapshotTasks_5720_ = lean_ctor_get(v___x_5711_, 8);
v_newDecls_5721_ = lean_ctor_get(v___x_5711_, 9);
v_isSharedCheck_5751_ = !lean_is_exclusive(v___x_5711_);
if (v_isSharedCheck_5751_ == 0)
{
v___x_5723_ = v___x_5711_;
v_isShared_5724_ = v_isSharedCheck_5751_;
goto v_resetjp_5722_;
}
else
{
lean_inc(v_newDecls_5721_);
lean_inc(v_snapshotTasks_5720_);
lean_inc(v_infoState_5719_);
lean_inc(v_messages_5718_);
lean_inc(v_cache_5717_);
lean_inc(v_traceState_5712_);
lean_inc(v_auxDeclNGen_5716_);
lean_inc(v_ngen_5715_);
lean_inc(v_nextMacroScope_5714_);
lean_inc(v_env_5713_);
lean_dec(v___x_5711_);
v___x_5723_ = lean_box(0);
v_isShared_5724_ = v_isSharedCheck_5751_;
goto v_resetjp_5722_;
}
v_resetjp_5722_:
{
uint64_t v_tid_5725_; lean_object* v_traces_5726_; lean_object* v___x_5728_; uint8_t v_isShared_5729_; uint8_t v_isSharedCheck_5750_; 
v_tid_5725_ = lean_ctor_get_uint64(v_traceState_5712_, sizeof(void*)*1);
v_traces_5726_ = lean_ctor_get(v_traceState_5712_, 0);
v_isSharedCheck_5750_ = !lean_is_exclusive(v_traceState_5712_);
if (v_isSharedCheck_5750_ == 0)
{
v___x_5728_ = v_traceState_5712_;
v_isShared_5729_ = v_isSharedCheck_5750_;
goto v_resetjp_5727_;
}
else
{
lean_inc(v_traces_5726_);
lean_dec(v_traceState_5712_);
v___x_5728_ = lean_box(0);
v_isShared_5729_ = v_isSharedCheck_5750_;
goto v_resetjp_5727_;
}
v_resetjp_5727_:
{
lean_object* v___x_5730_; double v___x_5731_; uint8_t v___x_5732_; lean_object* v___x_5733_; lean_object* v___x_5734_; lean_object* v___x_5735_; lean_object* v___x_5736_; lean_object* v___x_5737_; lean_object* v___x_5738_; lean_object* v___x_5740_; 
v___x_5730_ = lean_box(0);
v___x_5731_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0);
v___x_5732_ = 0;
v___x_5733_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__1));
v___x_5734_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_5734_, 0, v_cls_5698_);
lean_ctor_set(v___x_5734_, 1, v___x_5730_);
lean_ctor_set(v___x_5734_, 2, v___x_5733_);
lean_ctor_set_float(v___x_5734_, sizeof(void*)*3, v___x_5731_);
lean_ctor_set_float(v___x_5734_, sizeof(void*)*3 + 8, v___x_5731_);
lean_ctor_set_uint8(v___x_5734_, sizeof(void*)*3 + 16, v___x_5732_);
v___x_5735_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__2));
v___x_5736_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_5736_, 0, v___x_5734_);
lean_ctor_set(v___x_5736_, 1, v_a_5707_);
lean_ctor_set(v___x_5736_, 2, v___x_5735_);
lean_inc(v_ref_5705_);
v___x_5737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5737_, 0, v_ref_5705_);
lean_ctor_set(v___x_5737_, 1, v___x_5736_);
v___x_5738_ = l_Lean_PersistentArray_push___redArg(v_traces_5726_, v___x_5737_);
if (v_isShared_5729_ == 0)
{
lean_ctor_set(v___x_5728_, 0, v___x_5738_);
v___x_5740_ = v___x_5728_;
goto v_reusejp_5739_;
}
else
{
lean_object* v_reuseFailAlloc_5749_; 
v_reuseFailAlloc_5749_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5749_, 0, v___x_5738_);
lean_ctor_set_uint64(v_reuseFailAlloc_5749_, sizeof(void*)*1, v_tid_5725_);
v___x_5740_ = v_reuseFailAlloc_5749_;
goto v_reusejp_5739_;
}
v_reusejp_5739_:
{
lean_object* v___x_5742_; 
if (v_isShared_5724_ == 0)
{
lean_ctor_set(v___x_5723_, 4, v___x_5740_);
v___x_5742_ = v___x_5723_;
goto v_reusejp_5741_;
}
else
{
lean_object* v_reuseFailAlloc_5748_; 
v_reuseFailAlloc_5748_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5748_, 0, v_env_5713_);
lean_ctor_set(v_reuseFailAlloc_5748_, 1, v_nextMacroScope_5714_);
lean_ctor_set(v_reuseFailAlloc_5748_, 2, v_ngen_5715_);
lean_ctor_set(v_reuseFailAlloc_5748_, 3, v_auxDeclNGen_5716_);
lean_ctor_set(v_reuseFailAlloc_5748_, 4, v___x_5740_);
lean_ctor_set(v_reuseFailAlloc_5748_, 5, v_cache_5717_);
lean_ctor_set(v_reuseFailAlloc_5748_, 6, v_messages_5718_);
lean_ctor_set(v_reuseFailAlloc_5748_, 7, v_infoState_5719_);
lean_ctor_set(v_reuseFailAlloc_5748_, 8, v_snapshotTasks_5720_);
lean_ctor_set(v_reuseFailAlloc_5748_, 9, v_newDecls_5721_);
v___x_5742_ = v_reuseFailAlloc_5748_;
goto v_reusejp_5741_;
}
v_reusejp_5741_:
{
lean_object* v___x_5743_; lean_object* v___x_5744_; lean_object* v___x_5746_; 
v___x_5743_ = lean_st_ref_set(v___y_5703_, v___x_5742_);
v___x_5744_ = lean_box(0);
if (v_isShared_5710_ == 0)
{
lean_ctor_set(v___x_5709_, 0, v___x_5744_);
v___x_5746_ = v___x_5709_;
goto v_reusejp_5745_;
}
else
{
lean_object* v_reuseFailAlloc_5747_; 
v_reuseFailAlloc_5747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5747_, 0, v___x_5744_);
v___x_5746_ = v_reuseFailAlloc_5747_;
goto v_reusejp_5745_;
}
v_reusejp_5745_:
{
return v___x_5746_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg___boxed(lean_object* v_cls_5753_, lean_object* v_msg_5754_, lean_object* v___y_5755_, lean_object* v___y_5756_, lean_object* v___y_5757_, lean_object* v___y_5758_, lean_object* v___y_5759_){
_start:
{
lean_object* v_res_5760_; 
v_res_5760_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(v_cls_5753_, v_msg_5754_, v___y_5755_, v___y_5756_, v___y_5757_, v___y_5758_);
lean_dec(v___y_5758_);
lean_dec_ref(v___y_5757_);
lean_dec(v___y_5756_);
lean_dec_ref(v___y_5755_);
return v_res_5760_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(lean_object* v_msg_5761_, lean_object* v___y_5762_, lean_object* v___y_5763_, lean_object* v___y_5764_, lean_object* v___y_5765_){
_start:
{
lean_object* v_ref_5767_; lean_object* v___x_5768_; lean_object* v_a_5769_; lean_object* v___x_5771_; uint8_t v_isShared_5772_; uint8_t v_isSharedCheck_5777_; 
v_ref_5767_ = lean_ctor_get(v___y_5764_, 5);
v___x_5768_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0_spec__0(v_msg_5761_, v___y_5762_, v___y_5763_, v___y_5764_, v___y_5765_);
v_a_5769_ = lean_ctor_get(v___x_5768_, 0);
v_isSharedCheck_5777_ = !lean_is_exclusive(v___x_5768_);
if (v_isSharedCheck_5777_ == 0)
{
v___x_5771_ = v___x_5768_;
v_isShared_5772_ = v_isSharedCheck_5777_;
goto v_resetjp_5770_;
}
else
{
lean_inc(v_a_5769_);
lean_dec(v___x_5768_);
v___x_5771_ = lean_box(0);
v_isShared_5772_ = v_isSharedCheck_5777_;
goto v_resetjp_5770_;
}
v_resetjp_5770_:
{
lean_object* v___x_5773_; lean_object* v___x_5775_; 
lean_inc(v_ref_5767_);
v___x_5773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5773_, 0, v_ref_5767_);
lean_ctor_set(v___x_5773_, 1, v_a_5769_);
if (v_isShared_5772_ == 0)
{
lean_ctor_set_tag(v___x_5771_, 1);
lean_ctor_set(v___x_5771_, 0, v___x_5773_);
v___x_5775_ = v___x_5771_;
goto v_reusejp_5774_;
}
else
{
lean_object* v_reuseFailAlloc_5776_; 
v_reuseFailAlloc_5776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5776_, 0, v___x_5773_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg___boxed(lean_object* v_msg_5778_, lean_object* v___y_5779_, lean_object* v___y_5780_, lean_object* v___y_5781_, lean_object* v___y_5782_, lean_object* v___y_5783_){
_start:
{
lean_object* v_res_5784_; 
v_res_5784_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v_msg_5778_, v___y_5779_, v___y_5780_, v___y_5781_, v___y_5782_);
lean_dec(v___y_5782_);
lean_dec_ref(v___y_5781_);
lean_dec(v___y_5780_);
lean_dec_ref(v___y_5779_);
return v_res_5784_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1(void){
_start:
{
lean_object* v___x_5786_; lean_object* v___x_5787_; 
v___x_5786_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__0));
v___x_5787_ = l_Lean_stringToMessageData(v___x_5786_);
return v___x_5787_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3(void){
_start:
{
lean_object* v___x_5789_; lean_object* v___x_5790_; 
v___x_5789_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__2));
v___x_5790_ = l_Lean_stringToMessageData(v___x_5789_);
return v___x_5790_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6(void){
_start:
{
lean_object* v___x_5794_; lean_object* v___x_5795_; 
v___x_5794_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__5));
v___x_5795_ = l_Lean_stringToMessageData(v___x_5794_);
return v___x_5795_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8(void){
_start:
{
lean_object* v___x_5797_; lean_object* v___x_5798_; 
v___x_5797_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__7));
v___x_5798_ = l_Lean_stringToMessageData(v___x_5797_);
return v___x_5798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1(lean_object* v_m_5799_, lean_object* v___x_5800_, lean_object* v_cls_5801_, lean_object* v___y_5802_, lean_object* v___y_5803_, lean_object* v___y_5804_, lean_object* v___y_5805_, lean_object* v___y_5806_, lean_object* v___y_5807_){
_start:
{
lean_object* v_e_5810_; lean_object* v_onTrue_5811_; lean_object* v___y_5812_; lean_object* v___y_5813_; lean_object* v___y_5814_; lean_object* v___y_5815_; lean_object* v___y_5816_; lean_object* v___y_5817_; lean_object* v___x_5847_; 
v___x_5847_ = l_Lean_Meta_Sym_preprocessMVar(v_m_5799_, v___y_5802_, v___y_5803_, v___y_5804_, v___y_5805_, v___y_5806_, v___y_5807_);
if (lean_obj_tag(v___x_5847_) == 0)
{
lean_object* v_a_5848_; lean_object* v___x_5849_; 
v_a_5848_ = lean_ctor_get(v___x_5847_, 0);
lean_inc_n(v_a_5848_, 2);
lean_dec_ref(v___x_5847_);
v___x_5849_ = l_Lean_MVarId_getType(v_a_5848_, v___y_5804_, v___y_5805_, v___y_5806_, v___y_5807_);
if (lean_obj_tag(v___x_5849_) == 0)
{
lean_object* v_a_5850_; lean_object* v___x_5851_; lean_object* v___x_5852_; uint8_t v___x_5853_; 
v_a_5850_ = lean_ctor_get(v___x_5849_, 0);
lean_inc(v_a_5850_);
lean_dec_ref(v___x_5849_);
v___x_5851_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__4));
v___x_5852_ = lean_unsigned_to_nat(3u);
v___x_5853_ = l_Lean_Expr_isAppOfArity(v_a_5850_, v___x_5851_, v___x_5852_);
if (v___x_5853_ == 0)
{
lean_object* v___x_5854_; lean_object* v___x_5855_; lean_object* v___x_5856_; lean_object* v___x_5857_; 
lean_dec(v_a_5848_);
lean_dec(v_cls_5801_);
lean_dec_ref(v___x_5800_);
v___x_5854_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6);
v___x_5855_ = l_Lean_indentExpr(v_a_5850_);
v___x_5856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5856_, 0, v___x_5854_);
lean_ctor_set(v___x_5856_, 1, v___x_5855_);
v___x_5857_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_5856_, v___y_5804_, v___y_5805_, v___y_5806_, v___y_5807_);
return v___x_5857_;
}
else
{
lean_object* v___x_5858_; lean_object* v___x_5859_; lean_object* v___x_5860_; 
v___x_5858_ = l_Lean_Expr_appFn_x21(v_a_5850_);
lean_dec(v_a_5850_);
v___x_5859_ = l_Lean_Expr_appArg_x21(v___x_5858_);
lean_dec_ref(v___x_5858_);
lean_inc_ref(v___x_5859_);
v___x_5860_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_5859_, v___x_5800_, v___y_5802_, v___y_5803_, v___y_5804_, v___y_5805_, v___y_5806_, v___y_5807_);
if (lean_obj_tag(v___x_5860_) == 0)
{
lean_object* v_options_5861_; lean_object* v_a_5862_; lean_object* v_inheritedTraceOptions_5863_; uint8_t v_hasTrace_5864_; lean_object* v___x_5865_; lean_object* v___f_5866_; lean_object* v___y_5868_; lean_object* v___y_5869_; lean_object* v___y_5870_; lean_object* v___y_5871_; lean_object* v___y_5872_; lean_object* v___y_5873_; 
v_options_5861_ = lean_ctor_get(v___y_5806_, 2);
v_a_5862_ = lean_ctor_get(v___x_5860_, 0);
lean_inc(v_a_5862_);
lean_dec_ref(v___x_5860_);
v_inheritedTraceOptions_5863_ = lean_ctor_get(v___y_5806_, 13);
v_hasTrace_5864_ = lean_ctor_get_uint8(v_options_5861_, sizeof(void*)*1);
v___x_5865_ = lean_box(v___x_5853_);
lean_inc(v_a_5848_);
v___f_5866_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5866_, 0, v_a_5848_);
lean_closure_set(v___f_5866_, 1, v___x_5865_);
if (v_hasTrace_5864_ == 0)
{
lean_dec(v_cls_5801_);
v___y_5868_ = v___y_5802_;
v___y_5869_ = v___y_5803_;
v___y_5870_ = v___y_5804_;
v___y_5871_ = v___y_5805_;
v___y_5872_ = v___y_5806_;
v___y_5873_ = v___y_5807_;
goto v___jp_5867_;
}
else
{
lean_object* v___x_5877_; lean_object* v___x_5878_; uint8_t v___x_5879_; 
v___x_5877_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__3));
lean_inc(v_cls_5801_);
v___x_5878_ = l_Lean_Name_append(v___x_5877_, v_cls_5801_);
v___x_5879_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5863_, v_options_5861_, v___x_5878_);
lean_dec(v___x_5878_);
if (v___x_5879_ == 0)
{
lean_dec(v_cls_5801_);
v___y_5868_ = v___y_5802_;
v___y_5869_ = v___y_5803_;
v___y_5870_ = v___y_5804_;
v___y_5871_ = v___y_5805_;
v___y_5872_ = v___y_5806_;
v___y_5873_ = v___y_5807_;
goto v___jp_5867_;
}
else
{
lean_object* v___x_5880_; lean_object* v___x_5881_; lean_object* v___x_5882_; lean_object* v___x_5883_; lean_object* v___x_5884_; lean_object* v___x_5885_; lean_object* v___x_5886_; lean_object* v___x_5887_; lean_object* v___x_5888_; 
v___x_5880_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8);
lean_inc_ref(v___x_5859_);
v___x_5881_ = l_Lean_indentExpr(v___x_5859_);
v___x_5882_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5882_, 0, v___x_5880_);
lean_ctor_set(v___x_5882_, 1, v___x_5881_);
v___x_5883_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_5884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5884_, 0, v___x_5882_);
lean_ctor_set(v___x_5884_, 1, v___x_5883_);
v___x_5885_ = l_Lean_Meta_Sym_Simp_Result_getResultExpr(v___x_5859_, v_a_5862_);
v___x_5886_ = l_Lean_indentExpr(v___x_5885_);
v___x_5887_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5887_, 0, v___x_5884_);
lean_ctor_set(v___x_5887_, 1, v___x_5886_);
v___x_5888_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(v_cls_5801_, v___x_5887_, v___y_5804_, v___y_5805_, v___y_5806_, v___y_5807_);
if (lean_obj_tag(v___x_5888_) == 0)
{
lean_dec_ref(v___x_5888_);
v___y_5868_ = v___y_5802_;
v___y_5869_ = v___y_5803_;
v___y_5870_ = v___y_5804_;
v___y_5871_ = v___y_5805_;
v___y_5872_ = v___y_5806_;
v___y_5873_ = v___y_5807_;
goto v___jp_5867_;
}
else
{
lean_dec_ref(v___f_5866_);
lean_dec(v_a_5862_);
lean_dec_ref(v___x_5859_);
lean_dec(v_a_5848_);
return v___x_5888_;
}
}
}
v___jp_5867_:
{
if (lean_obj_tag(v_a_5862_) == 0)
{
lean_dec_ref(v_a_5862_);
lean_dec(v_a_5848_);
v_e_5810_ = v___x_5859_;
v_onTrue_5811_ = v___f_5866_;
v___y_5812_ = v___y_5868_;
v___y_5813_ = v___y_5869_;
v___y_5814_ = v___y_5870_;
v___y_5815_ = v___y_5871_;
v___y_5816_ = v___y_5872_;
v___y_5817_ = v___y_5873_;
goto v___jp_5809_;
}
else
{
lean_object* v_e_x27_5874_; lean_object* v_proof_5875_; lean_object* v___x_5876_; 
lean_dec_ref(v___f_5866_);
lean_dec_ref(v___x_5859_);
v_e_x27_5874_ = lean_ctor_get(v_a_5862_, 0);
lean_inc_ref(v_e_x27_5874_);
v_proof_5875_ = lean_ctor_get(v_a_5862_, 1);
lean_inc_ref(v_proof_5875_);
lean_dec_ref(v_a_5862_);
v___x_5876_ = lean_alloc_closure((void*)(l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0___boxed), 9, 2);
lean_closure_set(v___x_5876_, 0, v_a_5848_);
lean_closure_set(v___x_5876_, 1, v_proof_5875_);
v_e_5810_ = v_e_x27_5874_;
v_onTrue_5811_ = v___x_5876_;
v___y_5812_ = v___y_5868_;
v___y_5813_ = v___y_5869_;
v___y_5814_ = v___y_5870_;
v___y_5815_ = v___y_5871_;
v___y_5816_ = v___y_5872_;
v___y_5817_ = v___y_5873_;
goto v___jp_5809_;
}
}
}
else
{
lean_object* v_a_5889_; lean_object* v___x_5891_; uint8_t v_isShared_5892_; uint8_t v_isSharedCheck_5896_; 
lean_dec_ref(v___x_5859_);
lean_dec(v_a_5848_);
lean_dec(v_cls_5801_);
v_a_5889_ = lean_ctor_get(v___x_5860_, 0);
v_isSharedCheck_5896_ = !lean_is_exclusive(v___x_5860_);
if (v_isSharedCheck_5896_ == 0)
{
v___x_5891_ = v___x_5860_;
v_isShared_5892_ = v_isSharedCheck_5896_;
goto v_resetjp_5890_;
}
else
{
lean_inc(v_a_5889_);
lean_dec(v___x_5860_);
v___x_5891_ = lean_box(0);
v_isShared_5892_ = v_isSharedCheck_5896_;
goto v_resetjp_5890_;
}
v_resetjp_5890_:
{
lean_object* v___x_5894_; 
if (v_isShared_5892_ == 0)
{
v___x_5894_ = v___x_5891_;
goto v_reusejp_5893_;
}
else
{
lean_object* v_reuseFailAlloc_5895_; 
v_reuseFailAlloc_5895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5895_, 0, v_a_5889_);
v___x_5894_ = v_reuseFailAlloc_5895_;
goto v_reusejp_5893_;
}
v_reusejp_5893_:
{
return v___x_5894_;
}
}
}
}
}
else
{
lean_object* v_a_5897_; lean_object* v___x_5899_; uint8_t v_isShared_5900_; uint8_t v_isSharedCheck_5904_; 
lean_dec(v_a_5848_);
lean_dec(v_cls_5801_);
lean_dec_ref(v___x_5800_);
v_a_5897_ = lean_ctor_get(v___x_5849_, 0);
v_isSharedCheck_5904_ = !lean_is_exclusive(v___x_5849_);
if (v_isSharedCheck_5904_ == 0)
{
v___x_5899_ = v___x_5849_;
v_isShared_5900_ = v_isSharedCheck_5904_;
goto v_resetjp_5898_;
}
else
{
lean_inc(v_a_5897_);
lean_dec(v___x_5849_);
v___x_5899_ = lean_box(0);
v_isShared_5900_ = v_isSharedCheck_5904_;
goto v_resetjp_5898_;
}
v_resetjp_5898_:
{
lean_object* v___x_5902_; 
if (v_isShared_5900_ == 0)
{
v___x_5902_ = v___x_5899_;
goto v_reusejp_5901_;
}
else
{
lean_object* v_reuseFailAlloc_5903_; 
v_reuseFailAlloc_5903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5903_, 0, v_a_5897_);
v___x_5902_ = v_reuseFailAlloc_5903_;
goto v_reusejp_5901_;
}
v_reusejp_5901_:
{
return v___x_5902_;
}
}
}
}
else
{
lean_object* v_a_5905_; lean_object* v___x_5907_; uint8_t v_isShared_5908_; uint8_t v_isSharedCheck_5912_; 
lean_dec(v_cls_5801_);
lean_dec_ref(v___x_5800_);
v_a_5905_ = lean_ctor_get(v___x_5847_, 0);
v_isSharedCheck_5912_ = !lean_is_exclusive(v___x_5847_);
if (v_isSharedCheck_5912_ == 0)
{
v___x_5907_ = v___x_5847_;
v_isShared_5908_ = v_isSharedCheck_5912_;
goto v_resetjp_5906_;
}
else
{
lean_inc(v_a_5905_);
lean_dec(v___x_5847_);
v___x_5907_ = lean_box(0);
v_isShared_5908_ = v_isSharedCheck_5912_;
goto v_resetjp_5906_;
}
v_resetjp_5906_:
{
lean_object* v___x_5910_; 
if (v_isShared_5908_ == 0)
{
v___x_5910_ = v___x_5907_;
goto v_reusejp_5909_;
}
else
{
lean_object* v_reuseFailAlloc_5911_; 
v_reuseFailAlloc_5911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5911_, 0, v_a_5905_);
v___x_5910_ = v_reuseFailAlloc_5911_;
goto v_reusejp_5909_;
}
v_reusejp_5909_:
{
return v___x_5910_;
}
}
}
v___jp_5809_:
{
lean_object* v___x_5818_; 
v___x_5818_ = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(v_e_5810_, v___y_5812_);
if (lean_obj_tag(v___x_5818_) == 0)
{
lean_object* v_a_5819_; uint8_t v___x_5820_; 
v_a_5819_ = lean_ctor_get(v___x_5818_, 0);
lean_inc(v_a_5819_);
lean_dec_ref(v___x_5818_);
v___x_5820_ = lean_unbox(v_a_5819_);
lean_dec(v_a_5819_);
if (v___x_5820_ == 0)
{
lean_object* v___x_5821_; 
lean_dec_ref(v_onTrue_5811_);
v___x_5821_ = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(v_e_5810_, v___y_5812_);
if (lean_obj_tag(v___x_5821_) == 0)
{
lean_object* v_a_5822_; uint8_t v___x_5823_; 
v_a_5822_ = lean_ctor_get(v___x_5821_, 0);
lean_inc(v_a_5822_);
lean_dec_ref(v___x_5821_);
v___x_5823_ = lean_unbox(v_a_5822_);
lean_dec(v_a_5822_);
if (v___x_5823_ == 0)
{
lean_object* v___x_5824_; lean_object* v___x_5825_; lean_object* v___x_5826_; lean_object* v___x_5827_; 
v___x_5824_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1);
v___x_5825_ = l_Lean_indentExpr(v_e_5810_);
v___x_5826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5826_, 0, v___x_5824_);
lean_ctor_set(v___x_5826_, 1, v___x_5825_);
v___x_5827_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_5826_, v___y_5814_, v___y_5815_, v___y_5816_, v___y_5817_);
return v___x_5827_;
}
else
{
lean_object* v___x_5828_; lean_object* v___x_5829_; 
lean_dec_ref(v_e_5810_);
v___x_5828_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3);
v___x_5829_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_5828_, v___y_5814_, v___y_5815_, v___y_5816_, v___y_5817_);
return v___x_5829_;
}
}
else
{
lean_object* v_a_5830_; lean_object* v___x_5832_; uint8_t v_isShared_5833_; uint8_t v_isSharedCheck_5837_; 
lean_dec_ref(v_e_5810_);
v_a_5830_ = lean_ctor_get(v___x_5821_, 0);
v_isSharedCheck_5837_ = !lean_is_exclusive(v___x_5821_);
if (v_isSharedCheck_5837_ == 0)
{
v___x_5832_ = v___x_5821_;
v_isShared_5833_ = v_isSharedCheck_5837_;
goto v_resetjp_5831_;
}
else
{
lean_inc(v_a_5830_);
lean_dec(v___x_5821_);
v___x_5832_ = lean_box(0);
v_isShared_5833_ = v_isSharedCheck_5837_;
goto v_resetjp_5831_;
}
v_resetjp_5831_:
{
lean_object* v___x_5835_; 
if (v_isShared_5833_ == 0)
{
v___x_5835_ = v___x_5832_;
goto v_reusejp_5834_;
}
else
{
lean_object* v_reuseFailAlloc_5836_; 
v_reuseFailAlloc_5836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5836_, 0, v_a_5830_);
v___x_5835_ = v_reuseFailAlloc_5836_;
goto v_reusejp_5834_;
}
v_reusejp_5834_:
{
return v___x_5835_;
}
}
}
}
else
{
lean_object* v___x_5838_; 
lean_dec_ref(v_e_5810_);
lean_inc(v___y_5817_);
lean_inc_ref(v___y_5816_);
lean_inc(v___y_5815_);
lean_inc_ref(v___y_5814_);
lean_inc(v___y_5813_);
lean_inc_ref(v___y_5812_);
v___x_5838_ = lean_apply_7(v_onTrue_5811_, v___y_5812_, v___y_5813_, v___y_5814_, v___y_5815_, v___y_5816_, v___y_5817_, lean_box(0));
return v___x_5838_;
}
}
else
{
lean_object* v_a_5839_; lean_object* v___x_5841_; uint8_t v_isShared_5842_; uint8_t v_isSharedCheck_5846_; 
lean_dec_ref(v_onTrue_5811_);
lean_dec_ref(v_e_5810_);
v_a_5839_ = lean_ctor_get(v___x_5818_, 0);
v_isSharedCheck_5846_ = !lean_is_exclusive(v___x_5818_);
if (v_isSharedCheck_5846_ == 0)
{
v___x_5841_ = v___x_5818_;
v_isShared_5842_ = v_isSharedCheck_5846_;
goto v_resetjp_5840_;
}
else
{
lean_inc(v_a_5839_);
lean_dec(v___x_5818_);
v___x_5841_ = lean_box(0);
v_isShared_5842_ = v_isSharedCheck_5846_;
goto v_resetjp_5840_;
}
v_resetjp_5840_:
{
lean_object* v___x_5844_; 
if (v_isShared_5842_ == 0)
{
v___x_5844_ = v___x_5841_;
goto v_reusejp_5843_;
}
else
{
lean_object* v_reuseFailAlloc_5845_; 
v_reuseFailAlloc_5845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5845_, 0, v_a_5839_);
v___x_5844_ = v_reuseFailAlloc_5845_;
goto v_reusejp_5843_;
}
v_reusejp_5843_:
{
return v___x_5844_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___boxed(lean_object* v_m_5913_, lean_object* v___x_5914_, lean_object* v_cls_5915_, lean_object* v___y_5916_, lean_object* v___y_5917_, lean_object* v___y_5918_, lean_object* v___y_5919_, lean_object* v___y_5920_, lean_object* v___y_5921_, lean_object* v___y_5922_){
_start:
{
lean_object* v_res_5923_; 
v_res_5923_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1(v_m_5913_, v___x_5914_, v_cls_5915_, v___y_5916_, v___y_5917_, v___y_5918_, v___y_5919_, v___y_5920_, v___y_5921_);
lean_dec(v___y_5921_);
lean_dec_ref(v___y_5920_);
lean_dec(v___y_5919_);
lean_dec_ref(v___y_5918_);
lean_dec(v___y_5917_);
lean_dec_ref(v___y_5916_);
return v_res_5923_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__1(void){
_start:
{
lean_object* v___x_5925_; lean_object* v___x_5926_; 
v___x_5925_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__0));
v___x_5926_ = l_Lean_stringToMessageData(v___x_5925_);
return v___x_5926_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__3(void){
_start:
{
lean_object* v___x_5928_; lean_object* v___x_5929_; 
v___x_5928_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__2));
v___x_5929_ = l_Lean_stringToMessageData(v___x_5928_);
return v___x_5929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2(lean_object* v_x_5930_, lean_object* v___y_5931_, lean_object* v___y_5932_, lean_object* v___y_5933_, lean_object* v___y_5934_){
_start:
{
if (lean_obj_tag(v_x_5930_) == 0)
{
lean_object* v_a_5936_; lean_object* v___x_5938_; uint8_t v_isShared_5939_; uint8_t v_isSharedCheck_5946_; 
v_a_5936_ = lean_ctor_get(v_x_5930_, 0);
v_isSharedCheck_5946_ = !lean_is_exclusive(v_x_5930_);
if (v_isSharedCheck_5946_ == 0)
{
v___x_5938_ = v_x_5930_;
v_isShared_5939_ = v_isSharedCheck_5946_;
goto v_resetjp_5937_;
}
else
{
lean_inc(v_a_5936_);
lean_dec(v_x_5930_);
v___x_5938_ = lean_box(0);
v_isShared_5939_ = v_isSharedCheck_5946_;
goto v_resetjp_5937_;
}
v_resetjp_5937_:
{
lean_object* v___x_5940_; lean_object* v___x_5941_; lean_object* v___x_5942_; lean_object* v___x_5944_; 
v___x_5940_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__1);
v___x_5941_ = l_Lean_Exception_toMessageData(v_a_5936_);
v___x_5942_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5942_, 0, v___x_5940_);
lean_ctor_set(v___x_5942_, 1, v___x_5941_);
if (v_isShared_5939_ == 0)
{
lean_ctor_set(v___x_5938_, 0, v___x_5942_);
v___x_5944_ = v___x_5938_;
goto v_reusejp_5943_;
}
else
{
lean_object* v_reuseFailAlloc_5945_; 
v_reuseFailAlloc_5945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5945_, 0, v___x_5942_);
v___x_5944_ = v_reuseFailAlloc_5945_;
goto v_reusejp_5943_;
}
v_reusejp_5943_:
{
return v___x_5944_;
}
}
}
else
{
lean_object* v___x_5948_; uint8_t v_isShared_5949_; uint8_t v_isSharedCheck_5954_; 
v_isSharedCheck_5954_ = !lean_is_exclusive(v_x_5930_);
if (v_isSharedCheck_5954_ == 0)
{
lean_object* v_unused_5955_; 
v_unused_5955_ = lean_ctor_get(v_x_5930_, 0);
lean_dec(v_unused_5955_);
v___x_5948_ = v_x_5930_;
v_isShared_5949_ = v_isSharedCheck_5954_;
goto v_resetjp_5947_;
}
else
{
lean_dec(v_x_5930_);
v___x_5948_ = lean_box(0);
v_isShared_5949_ = v_isSharedCheck_5954_;
goto v_resetjp_5947_;
}
v_resetjp_5947_:
{
lean_object* v___x_5950_; lean_object* v___x_5952_; 
v___x_5950_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__3, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__3);
if (v_isShared_5949_ == 0)
{
lean_ctor_set_tag(v___x_5948_, 0);
lean_ctor_set(v___x_5948_, 0, v___x_5950_);
v___x_5952_ = v___x_5948_;
goto v_reusejp_5951_;
}
else
{
lean_object* v_reuseFailAlloc_5953_; 
v_reuseFailAlloc_5953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5953_, 0, v___x_5950_);
v___x_5952_ = v_reuseFailAlloc_5953_;
goto v_reusejp_5951_;
}
v_reusejp_5951_:
{
return v___x_5952_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___boxed(lean_object* v_x_5956_, lean_object* v___y_5957_, lean_object* v___y_5958_, lean_object* v___y_5959_, lean_object* v___y_5960_, lean_object* v___y_5961_){
_start:
{
lean_object* v_res_5962_; 
v_res_5962_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2(v_x_5956_, v___y_5957_, v___y_5958_, v___y_5959_, v___y_5960_);
lean_dec(v___y_5960_);
lean_dec_ref(v___y_5959_);
lean_dec(v___y_5958_);
lean_dec_ref(v___y_5957_);
return v_res_5962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__3(lean_object* v_a_5963_, uint8_t v_hasTrace_5964_, lean_object* v___y_5965_, lean_object* v___y_5966_, lean_object* v___y_5967_, lean_object* v___y_5968_, lean_object* v___y_5969_, lean_object* v___y_5970_){
_start:
{
lean_object* v___x_5972_; 
v___x_5972_ = l_Lean_MVarId_refl(v_a_5963_, v_hasTrace_5964_, v___y_5967_, v___y_5968_, v___y_5969_, v___y_5970_);
return v___x_5972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__3___boxed(lean_object* v_a_5973_, lean_object* v_hasTrace_5974_, lean_object* v___y_5975_, lean_object* v___y_5976_, lean_object* v___y_5977_, lean_object* v___y_5978_, lean_object* v___y_5979_, lean_object* v___y_5980_, lean_object* v___y_5981_){
_start:
{
uint8_t v_hasTrace_boxed_5982_; lean_object* v_res_5983_; 
v_hasTrace_boxed_5982_ = lean_unbox(v_hasTrace_5974_);
v_res_5983_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__3(v_a_5973_, v_hasTrace_boxed_5982_, v___y_5975_, v___y_5976_, v___y_5977_, v___y_5978_, v___y_5979_, v___y_5980_);
lean_dec(v___y_5980_);
lean_dec_ref(v___y_5979_);
lean_dec(v___y_5978_);
lean_dec_ref(v___y_5977_);
lean_dec(v___y_5976_);
lean_dec_ref(v___y_5975_);
return v_res_5983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__4(lean_object* v_m_5984_, lean_object* v___x_5985_, uint8_t v_hasTrace_5986_, lean_object* v_cls_5987_, lean_object* v___y_5988_, lean_object* v___y_5989_, lean_object* v___y_5990_, lean_object* v___y_5991_, lean_object* v___y_5992_, lean_object* v___y_5993_){
_start:
{
lean_object* v_e_5996_; lean_object* v_onTrue_5997_; lean_object* v___y_5998_; lean_object* v___y_5999_; lean_object* v___y_6000_; lean_object* v___y_6001_; lean_object* v___y_6002_; lean_object* v___y_6003_; lean_object* v___x_6033_; 
v___x_6033_ = l_Lean_Meta_Sym_preprocessMVar(v_m_5984_, v___y_5988_, v___y_5989_, v___y_5990_, v___y_5991_, v___y_5992_, v___y_5993_);
if (lean_obj_tag(v___x_6033_) == 0)
{
lean_object* v_a_6034_; lean_object* v___x_6035_; 
v_a_6034_ = lean_ctor_get(v___x_6033_, 0);
lean_inc_n(v_a_6034_, 2);
lean_dec_ref(v___x_6033_);
v___x_6035_ = l_Lean_MVarId_getType(v_a_6034_, v___y_5990_, v___y_5991_, v___y_5992_, v___y_5993_);
if (lean_obj_tag(v___x_6035_) == 0)
{
lean_object* v_a_6036_; lean_object* v___x_6037_; lean_object* v___x_6038_; uint8_t v___x_6039_; 
v_a_6036_ = lean_ctor_get(v___x_6035_, 0);
lean_inc(v_a_6036_);
lean_dec_ref(v___x_6035_);
v___x_6037_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__4));
v___x_6038_ = lean_unsigned_to_nat(3u);
v___x_6039_ = l_Lean_Expr_isAppOfArity(v_a_6036_, v___x_6037_, v___x_6038_);
if (v___x_6039_ == 0)
{
lean_object* v___x_6040_; lean_object* v___x_6041_; lean_object* v___x_6042_; lean_object* v___x_6043_; 
lean_dec(v_a_6034_);
lean_dec(v_cls_5987_);
lean_dec_ref(v___x_5985_);
v___x_6040_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6);
v___x_6041_ = l_Lean_indentExpr(v_a_6036_);
v___x_6042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6042_, 0, v___x_6040_);
lean_ctor_set(v___x_6042_, 1, v___x_6041_);
v___x_6043_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_6042_, v___y_5990_, v___y_5991_, v___y_5992_, v___y_5993_);
return v___x_6043_;
}
else
{
lean_object* v___x_6044_; lean_object* v___x_6045_; lean_object* v___x_6046_; 
v___x_6044_ = l_Lean_Expr_appFn_x21(v_a_6036_);
lean_dec(v_a_6036_);
v___x_6045_ = l_Lean_Expr_appArg_x21(v___x_6044_);
lean_dec_ref(v___x_6044_);
lean_inc_ref(v___x_6045_);
v___x_6046_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_6045_, v___x_5985_, v___y_5988_, v___y_5989_, v___y_5990_, v___y_5991_, v___y_5992_, v___y_5993_);
if (lean_obj_tag(v___x_6046_) == 0)
{
lean_object* v_options_6047_; lean_object* v_a_6048_; lean_object* v_inheritedTraceOptions_6049_; uint8_t v_hasTrace_6050_; lean_object* v___x_6051_; lean_object* v___f_6052_; lean_object* v___y_6054_; lean_object* v___y_6055_; lean_object* v___y_6056_; lean_object* v___y_6057_; lean_object* v___y_6058_; lean_object* v___y_6059_; 
v_options_6047_ = lean_ctor_get(v___y_5992_, 2);
v_a_6048_ = lean_ctor_get(v___x_6046_, 0);
lean_inc(v_a_6048_);
lean_dec_ref(v___x_6046_);
v_inheritedTraceOptions_6049_ = lean_ctor_get(v___y_5992_, 13);
v_hasTrace_6050_ = lean_ctor_get_uint8(v_options_6047_, sizeof(void*)*1);
v___x_6051_ = lean_box(v_hasTrace_5986_);
lean_inc(v_a_6034_);
v___f_6052_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__3___boxed), 9, 2);
lean_closure_set(v___f_6052_, 0, v_a_6034_);
lean_closure_set(v___f_6052_, 1, v___x_6051_);
if (v_hasTrace_6050_ == 0)
{
lean_dec(v_cls_5987_);
v___y_6054_ = v___y_5988_;
v___y_6055_ = v___y_5989_;
v___y_6056_ = v___y_5990_;
v___y_6057_ = v___y_5991_;
v___y_6058_ = v___y_5992_;
v___y_6059_ = v___y_5993_;
goto v___jp_6053_;
}
else
{
lean_object* v___x_6063_; lean_object* v___x_6064_; uint8_t v___x_6065_; 
v___x_6063_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__3));
lean_inc(v_cls_5987_);
v___x_6064_ = l_Lean_Name_append(v___x_6063_, v_cls_5987_);
v___x_6065_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6049_, v_options_6047_, v___x_6064_);
lean_dec(v___x_6064_);
if (v___x_6065_ == 0)
{
lean_dec(v_cls_5987_);
v___y_6054_ = v___y_5988_;
v___y_6055_ = v___y_5989_;
v___y_6056_ = v___y_5990_;
v___y_6057_ = v___y_5991_;
v___y_6058_ = v___y_5992_;
v___y_6059_ = v___y_5993_;
goto v___jp_6053_;
}
else
{
lean_object* v___x_6066_; lean_object* v___x_6067_; lean_object* v___x_6068_; lean_object* v___x_6069_; lean_object* v___x_6070_; lean_object* v___x_6071_; lean_object* v___x_6072_; lean_object* v___x_6073_; lean_object* v___x_6074_; 
v___x_6066_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8);
lean_inc_ref(v___x_6045_);
v___x_6067_ = l_Lean_indentExpr(v___x_6045_);
v___x_6068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6068_, 0, v___x_6066_);
lean_ctor_set(v___x_6068_, 1, v___x_6067_);
v___x_6069_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_6070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6070_, 0, v___x_6068_);
lean_ctor_set(v___x_6070_, 1, v___x_6069_);
v___x_6071_ = l_Lean_Meta_Sym_Simp_Result_getResultExpr(v___x_6045_, v_a_6048_);
v___x_6072_ = l_Lean_indentExpr(v___x_6071_);
v___x_6073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6073_, 0, v___x_6070_);
lean_ctor_set(v___x_6073_, 1, v___x_6072_);
v___x_6074_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(v_cls_5987_, v___x_6073_, v___y_5990_, v___y_5991_, v___y_5992_, v___y_5993_);
if (lean_obj_tag(v___x_6074_) == 0)
{
lean_dec_ref(v___x_6074_);
v___y_6054_ = v___y_5988_;
v___y_6055_ = v___y_5989_;
v___y_6056_ = v___y_5990_;
v___y_6057_ = v___y_5991_;
v___y_6058_ = v___y_5992_;
v___y_6059_ = v___y_5993_;
goto v___jp_6053_;
}
else
{
lean_dec_ref(v___f_6052_);
lean_dec(v_a_6048_);
lean_dec_ref(v___x_6045_);
lean_dec(v_a_6034_);
return v___x_6074_;
}
}
}
v___jp_6053_:
{
if (lean_obj_tag(v_a_6048_) == 0)
{
lean_dec_ref(v_a_6048_);
lean_dec(v_a_6034_);
v_e_5996_ = v___x_6045_;
v_onTrue_5997_ = v___f_6052_;
v___y_5998_ = v___y_6054_;
v___y_5999_ = v___y_6055_;
v___y_6000_ = v___y_6056_;
v___y_6001_ = v___y_6057_;
v___y_6002_ = v___y_6058_;
v___y_6003_ = v___y_6059_;
goto v___jp_5995_;
}
else
{
lean_object* v_e_x27_6060_; lean_object* v_proof_6061_; lean_object* v___x_6062_; 
lean_dec_ref(v___f_6052_);
lean_dec_ref(v___x_6045_);
v_e_x27_6060_ = lean_ctor_get(v_a_6048_, 0);
lean_inc_ref(v_e_x27_6060_);
v_proof_6061_ = lean_ctor_get(v_a_6048_, 1);
lean_inc_ref(v_proof_6061_);
lean_dec_ref(v_a_6048_);
v___x_6062_ = lean_alloc_closure((void*)(l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0___boxed), 9, 2);
lean_closure_set(v___x_6062_, 0, v_a_6034_);
lean_closure_set(v___x_6062_, 1, v_proof_6061_);
v_e_5996_ = v_e_x27_6060_;
v_onTrue_5997_ = v___x_6062_;
v___y_5998_ = v___y_6054_;
v___y_5999_ = v___y_6055_;
v___y_6000_ = v___y_6056_;
v___y_6001_ = v___y_6057_;
v___y_6002_ = v___y_6058_;
v___y_6003_ = v___y_6059_;
goto v___jp_5995_;
}
}
}
else
{
lean_object* v_a_6075_; lean_object* v___x_6077_; uint8_t v_isShared_6078_; uint8_t v_isSharedCheck_6082_; 
lean_dec_ref(v___x_6045_);
lean_dec(v_a_6034_);
lean_dec(v_cls_5987_);
v_a_6075_ = lean_ctor_get(v___x_6046_, 0);
v_isSharedCheck_6082_ = !lean_is_exclusive(v___x_6046_);
if (v_isSharedCheck_6082_ == 0)
{
v___x_6077_ = v___x_6046_;
v_isShared_6078_ = v_isSharedCheck_6082_;
goto v_resetjp_6076_;
}
else
{
lean_inc(v_a_6075_);
lean_dec(v___x_6046_);
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
else
{
lean_object* v_a_6083_; lean_object* v___x_6085_; uint8_t v_isShared_6086_; uint8_t v_isSharedCheck_6090_; 
lean_dec(v_a_6034_);
lean_dec(v_cls_5987_);
lean_dec_ref(v___x_5985_);
v_a_6083_ = lean_ctor_get(v___x_6035_, 0);
v_isSharedCheck_6090_ = !lean_is_exclusive(v___x_6035_);
if (v_isSharedCheck_6090_ == 0)
{
v___x_6085_ = v___x_6035_;
v_isShared_6086_ = v_isSharedCheck_6090_;
goto v_resetjp_6084_;
}
else
{
lean_inc(v_a_6083_);
lean_dec(v___x_6035_);
v___x_6085_ = lean_box(0);
v_isShared_6086_ = v_isSharedCheck_6090_;
goto v_resetjp_6084_;
}
v_resetjp_6084_:
{
lean_object* v___x_6088_; 
if (v_isShared_6086_ == 0)
{
v___x_6088_ = v___x_6085_;
goto v_reusejp_6087_;
}
else
{
lean_object* v_reuseFailAlloc_6089_; 
v_reuseFailAlloc_6089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6089_, 0, v_a_6083_);
v___x_6088_ = v_reuseFailAlloc_6089_;
goto v_reusejp_6087_;
}
v_reusejp_6087_:
{
return v___x_6088_;
}
}
}
}
else
{
lean_object* v_a_6091_; lean_object* v___x_6093_; uint8_t v_isShared_6094_; uint8_t v_isSharedCheck_6098_; 
lean_dec(v_cls_5987_);
lean_dec_ref(v___x_5985_);
v_a_6091_ = lean_ctor_get(v___x_6033_, 0);
v_isSharedCheck_6098_ = !lean_is_exclusive(v___x_6033_);
if (v_isSharedCheck_6098_ == 0)
{
v___x_6093_ = v___x_6033_;
v_isShared_6094_ = v_isSharedCheck_6098_;
goto v_resetjp_6092_;
}
else
{
lean_inc(v_a_6091_);
lean_dec(v___x_6033_);
v___x_6093_ = lean_box(0);
v_isShared_6094_ = v_isSharedCheck_6098_;
goto v_resetjp_6092_;
}
v_resetjp_6092_:
{
lean_object* v___x_6096_; 
if (v_isShared_6094_ == 0)
{
v___x_6096_ = v___x_6093_;
goto v_reusejp_6095_;
}
else
{
lean_object* v_reuseFailAlloc_6097_; 
v_reuseFailAlloc_6097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6097_, 0, v_a_6091_);
v___x_6096_ = v_reuseFailAlloc_6097_;
goto v_reusejp_6095_;
}
v_reusejp_6095_:
{
return v___x_6096_;
}
}
}
v___jp_5995_:
{
lean_object* v___x_6004_; 
v___x_6004_ = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(v_e_5996_, v___y_5998_);
if (lean_obj_tag(v___x_6004_) == 0)
{
lean_object* v_a_6005_; uint8_t v___x_6006_; 
v_a_6005_ = lean_ctor_get(v___x_6004_, 0);
lean_inc(v_a_6005_);
lean_dec_ref(v___x_6004_);
v___x_6006_ = lean_unbox(v_a_6005_);
lean_dec(v_a_6005_);
if (v___x_6006_ == 0)
{
lean_object* v___x_6007_; 
lean_dec_ref(v_onTrue_5997_);
v___x_6007_ = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(v_e_5996_, v___y_5998_);
if (lean_obj_tag(v___x_6007_) == 0)
{
lean_object* v_a_6008_; uint8_t v___x_6009_; 
v_a_6008_ = lean_ctor_get(v___x_6007_, 0);
lean_inc(v_a_6008_);
lean_dec_ref(v___x_6007_);
v___x_6009_ = lean_unbox(v_a_6008_);
lean_dec(v_a_6008_);
if (v___x_6009_ == 0)
{
lean_object* v___x_6010_; lean_object* v___x_6011_; lean_object* v___x_6012_; lean_object* v___x_6013_; 
v___x_6010_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1);
v___x_6011_ = l_Lean_indentExpr(v_e_5996_);
v___x_6012_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6012_, 0, v___x_6010_);
lean_ctor_set(v___x_6012_, 1, v___x_6011_);
v___x_6013_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_6012_, v___y_6000_, v___y_6001_, v___y_6002_, v___y_6003_);
return v___x_6013_;
}
else
{
lean_object* v___x_6014_; lean_object* v___x_6015_; 
lean_dec_ref(v_e_5996_);
v___x_6014_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3);
v___x_6015_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_6014_, v___y_6000_, v___y_6001_, v___y_6002_, v___y_6003_);
return v___x_6015_;
}
}
else
{
lean_object* v_a_6016_; lean_object* v___x_6018_; uint8_t v_isShared_6019_; uint8_t v_isSharedCheck_6023_; 
lean_dec_ref(v_e_5996_);
v_a_6016_ = lean_ctor_get(v___x_6007_, 0);
v_isSharedCheck_6023_ = !lean_is_exclusive(v___x_6007_);
if (v_isSharedCheck_6023_ == 0)
{
v___x_6018_ = v___x_6007_;
v_isShared_6019_ = v_isSharedCheck_6023_;
goto v_resetjp_6017_;
}
else
{
lean_inc(v_a_6016_);
lean_dec(v___x_6007_);
v___x_6018_ = lean_box(0);
v_isShared_6019_ = v_isSharedCheck_6023_;
goto v_resetjp_6017_;
}
v_resetjp_6017_:
{
lean_object* v___x_6021_; 
if (v_isShared_6019_ == 0)
{
v___x_6021_ = v___x_6018_;
goto v_reusejp_6020_;
}
else
{
lean_object* v_reuseFailAlloc_6022_; 
v_reuseFailAlloc_6022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6022_, 0, v_a_6016_);
v___x_6021_ = v_reuseFailAlloc_6022_;
goto v_reusejp_6020_;
}
v_reusejp_6020_:
{
return v___x_6021_;
}
}
}
}
else
{
lean_object* v___x_6024_; 
lean_dec_ref(v_e_5996_);
lean_inc(v___y_6003_);
lean_inc_ref(v___y_6002_);
lean_inc(v___y_6001_);
lean_inc_ref(v___y_6000_);
lean_inc(v___y_5999_);
lean_inc_ref(v___y_5998_);
v___x_6024_ = lean_apply_7(v_onTrue_5997_, v___y_5998_, v___y_5999_, v___y_6000_, v___y_6001_, v___y_6002_, v___y_6003_, lean_box(0));
return v___x_6024_;
}
}
else
{
lean_object* v_a_6025_; lean_object* v___x_6027_; uint8_t v_isShared_6028_; uint8_t v_isSharedCheck_6032_; 
lean_dec_ref(v_onTrue_5997_);
lean_dec_ref(v_e_5996_);
v_a_6025_ = lean_ctor_get(v___x_6004_, 0);
v_isSharedCheck_6032_ = !lean_is_exclusive(v___x_6004_);
if (v_isSharedCheck_6032_ == 0)
{
v___x_6027_ = v___x_6004_;
v_isShared_6028_ = v_isSharedCheck_6032_;
goto v_resetjp_6026_;
}
else
{
lean_inc(v_a_6025_);
lean_dec(v___x_6004_);
v___x_6027_ = lean_box(0);
v_isShared_6028_ = v_isSharedCheck_6032_;
goto v_resetjp_6026_;
}
v_resetjp_6026_:
{
lean_object* v___x_6030_; 
if (v_isShared_6028_ == 0)
{
v___x_6030_ = v___x_6027_;
goto v_reusejp_6029_;
}
else
{
lean_object* v_reuseFailAlloc_6031_; 
v_reuseFailAlloc_6031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6031_, 0, v_a_6025_);
v___x_6030_ = v_reuseFailAlloc_6031_;
goto v_reusejp_6029_;
}
v_reusejp_6029_:
{
return v___x_6030_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__4___boxed(lean_object* v_m_6099_, lean_object* v___x_6100_, lean_object* v_hasTrace_6101_, lean_object* v_cls_6102_, lean_object* v___y_6103_, lean_object* v___y_6104_, lean_object* v___y_6105_, lean_object* v___y_6106_, lean_object* v___y_6107_, lean_object* v___y_6108_, lean_object* v___y_6109_){
_start:
{
uint8_t v_hasTrace_boxed_6110_; lean_object* v_res_6111_; 
v_hasTrace_boxed_6110_ = lean_unbox(v_hasTrace_6101_);
v_res_6111_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__4(v_m_6099_, v___x_6100_, v_hasTrace_boxed_6110_, v_cls_6102_, v___y_6103_, v___y_6104_, v___y_6105_, v___y_6106_, v___y_6107_, v___y_6108_);
lean_dec(v___y_6108_);
lean_dec_ref(v___y_6107_);
lean_dec(v___y_6106_);
lean_dec_ref(v___y_6105_);
lean_dec(v___y_6104_);
lean_dec_ref(v___y_6103_);
return v_res_6111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__6(lean_object* v_m_6112_, lean_object* v___x_6113_, uint8_t v___x_6114_, lean_object* v_cls_6115_, lean_object* v___y_6116_, lean_object* v___y_6117_, lean_object* v___y_6118_, lean_object* v___y_6119_, lean_object* v___y_6120_, lean_object* v___y_6121_){
_start:
{
lean_object* v_e_6124_; lean_object* v_onTrue_6125_; lean_object* v___y_6126_; lean_object* v___y_6127_; lean_object* v___y_6128_; lean_object* v___y_6129_; lean_object* v___y_6130_; lean_object* v___y_6131_; lean_object* v___x_6161_; 
v___x_6161_ = l_Lean_Meta_Sym_preprocessMVar(v_m_6112_, v___y_6116_, v___y_6117_, v___y_6118_, v___y_6119_, v___y_6120_, v___y_6121_);
if (lean_obj_tag(v___x_6161_) == 0)
{
lean_object* v_a_6162_; lean_object* v___x_6163_; 
v_a_6162_ = lean_ctor_get(v___x_6161_, 0);
lean_inc_n(v_a_6162_, 2);
lean_dec_ref(v___x_6161_);
v___x_6163_ = l_Lean_MVarId_getType(v_a_6162_, v___y_6118_, v___y_6119_, v___y_6120_, v___y_6121_);
if (lean_obj_tag(v___x_6163_) == 0)
{
lean_object* v_a_6164_; lean_object* v___x_6165_; lean_object* v___x_6166_; uint8_t v___x_6167_; 
v_a_6164_ = lean_ctor_get(v___x_6163_, 0);
lean_inc(v_a_6164_);
lean_dec_ref(v___x_6163_);
v___x_6165_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__4));
v___x_6166_ = lean_unsigned_to_nat(3u);
v___x_6167_ = l_Lean_Expr_isAppOfArity(v_a_6164_, v___x_6165_, v___x_6166_);
if (v___x_6167_ == 0)
{
lean_object* v___x_6168_; lean_object* v___x_6169_; lean_object* v___x_6170_; lean_object* v___x_6171_; 
lean_dec(v_a_6162_);
lean_dec(v_cls_6115_);
lean_dec_ref(v___x_6113_);
v___x_6168_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6);
v___x_6169_ = l_Lean_indentExpr(v_a_6164_);
v___x_6170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6170_, 0, v___x_6168_);
lean_ctor_set(v___x_6170_, 1, v___x_6169_);
v___x_6171_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_6170_, v___y_6118_, v___y_6119_, v___y_6120_, v___y_6121_);
return v___x_6171_;
}
else
{
lean_object* v___x_6172_; lean_object* v___x_6173_; lean_object* v___x_6174_; 
v___x_6172_ = l_Lean_Expr_appFn_x21(v_a_6164_);
lean_dec(v_a_6164_);
v___x_6173_ = l_Lean_Expr_appArg_x21(v___x_6172_);
lean_dec_ref(v___x_6172_);
lean_inc_ref(v___x_6173_);
v___x_6174_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_6173_, v___x_6113_, v___y_6116_, v___y_6117_, v___y_6118_, v___y_6119_, v___y_6120_, v___y_6121_);
if (lean_obj_tag(v___x_6174_) == 0)
{
lean_object* v_options_6175_; lean_object* v_a_6176_; lean_object* v_inheritedTraceOptions_6177_; uint8_t v_hasTrace_6178_; lean_object* v___x_6179_; lean_object* v___f_6180_; lean_object* v___y_6182_; lean_object* v___y_6183_; lean_object* v___y_6184_; lean_object* v___y_6185_; lean_object* v___y_6186_; lean_object* v___y_6187_; 
v_options_6175_ = lean_ctor_get(v___y_6120_, 2);
v_a_6176_ = lean_ctor_get(v___x_6174_, 0);
lean_inc(v_a_6176_);
lean_dec_ref(v___x_6174_);
v_inheritedTraceOptions_6177_ = lean_ctor_get(v___y_6120_, 13);
v_hasTrace_6178_ = lean_ctor_get_uint8(v_options_6175_, sizeof(void*)*1);
v___x_6179_ = lean_box(v___x_6114_);
lean_inc(v_a_6162_);
v___f_6180_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0___boxed), 9, 2);
lean_closure_set(v___f_6180_, 0, v_a_6162_);
lean_closure_set(v___f_6180_, 1, v___x_6179_);
if (v_hasTrace_6178_ == 0)
{
lean_dec(v_cls_6115_);
v___y_6182_ = v___y_6116_;
v___y_6183_ = v___y_6117_;
v___y_6184_ = v___y_6118_;
v___y_6185_ = v___y_6119_;
v___y_6186_ = v___y_6120_;
v___y_6187_ = v___y_6121_;
goto v___jp_6181_;
}
else
{
lean_object* v___x_6191_; lean_object* v___x_6192_; uint8_t v___x_6193_; 
v___x_6191_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__3));
lean_inc(v_cls_6115_);
v___x_6192_ = l_Lean_Name_append(v___x_6191_, v_cls_6115_);
v___x_6193_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6177_, v_options_6175_, v___x_6192_);
lean_dec(v___x_6192_);
if (v___x_6193_ == 0)
{
lean_dec(v_cls_6115_);
v___y_6182_ = v___y_6116_;
v___y_6183_ = v___y_6117_;
v___y_6184_ = v___y_6118_;
v___y_6185_ = v___y_6119_;
v___y_6186_ = v___y_6120_;
v___y_6187_ = v___y_6121_;
goto v___jp_6181_;
}
else
{
lean_object* v___x_6194_; lean_object* v___x_6195_; lean_object* v___x_6196_; lean_object* v___x_6197_; lean_object* v___x_6198_; lean_object* v___x_6199_; lean_object* v___x_6200_; lean_object* v___x_6201_; lean_object* v___x_6202_; 
v___x_6194_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8);
lean_inc_ref(v___x_6173_);
v___x_6195_ = l_Lean_indentExpr(v___x_6173_);
v___x_6196_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6196_, 0, v___x_6194_);
lean_ctor_set(v___x_6196_, 1, v___x_6195_);
v___x_6197_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_6198_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6198_, 0, v___x_6196_);
lean_ctor_set(v___x_6198_, 1, v___x_6197_);
v___x_6199_ = l_Lean_Meta_Sym_Simp_Result_getResultExpr(v___x_6173_, v_a_6176_);
v___x_6200_ = l_Lean_indentExpr(v___x_6199_);
v___x_6201_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6201_, 0, v___x_6198_);
lean_ctor_set(v___x_6201_, 1, v___x_6200_);
v___x_6202_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(v_cls_6115_, v___x_6201_, v___y_6118_, v___y_6119_, v___y_6120_, v___y_6121_);
if (lean_obj_tag(v___x_6202_) == 0)
{
lean_dec_ref(v___x_6202_);
v___y_6182_ = v___y_6116_;
v___y_6183_ = v___y_6117_;
v___y_6184_ = v___y_6118_;
v___y_6185_ = v___y_6119_;
v___y_6186_ = v___y_6120_;
v___y_6187_ = v___y_6121_;
goto v___jp_6181_;
}
else
{
lean_dec_ref(v___f_6180_);
lean_dec(v_a_6176_);
lean_dec_ref(v___x_6173_);
lean_dec(v_a_6162_);
return v___x_6202_;
}
}
}
v___jp_6181_:
{
if (lean_obj_tag(v_a_6176_) == 0)
{
lean_dec_ref(v_a_6176_);
lean_dec(v_a_6162_);
v_e_6124_ = v___x_6173_;
v_onTrue_6125_ = v___f_6180_;
v___y_6126_ = v___y_6182_;
v___y_6127_ = v___y_6183_;
v___y_6128_ = v___y_6184_;
v___y_6129_ = v___y_6185_;
v___y_6130_ = v___y_6186_;
v___y_6131_ = v___y_6187_;
goto v___jp_6123_;
}
else
{
lean_object* v_e_x27_6188_; lean_object* v_proof_6189_; lean_object* v___x_6190_; 
lean_dec_ref(v___f_6180_);
lean_dec_ref(v___x_6173_);
v_e_x27_6188_ = lean_ctor_get(v_a_6176_, 0);
lean_inc_ref(v_e_x27_6188_);
v_proof_6189_ = lean_ctor_get(v_a_6176_, 1);
lean_inc_ref(v_proof_6189_);
lean_dec_ref(v_a_6176_);
v___x_6190_ = lean_alloc_closure((void*)(l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0___boxed), 9, 2);
lean_closure_set(v___x_6190_, 0, v_a_6162_);
lean_closure_set(v___x_6190_, 1, v_proof_6189_);
v_e_6124_ = v_e_x27_6188_;
v_onTrue_6125_ = v___x_6190_;
v___y_6126_ = v___y_6182_;
v___y_6127_ = v___y_6183_;
v___y_6128_ = v___y_6184_;
v___y_6129_ = v___y_6185_;
v___y_6130_ = v___y_6186_;
v___y_6131_ = v___y_6187_;
goto v___jp_6123_;
}
}
}
else
{
lean_object* v_a_6203_; lean_object* v___x_6205_; uint8_t v_isShared_6206_; uint8_t v_isSharedCheck_6210_; 
lean_dec_ref(v___x_6173_);
lean_dec(v_a_6162_);
lean_dec(v_cls_6115_);
v_a_6203_ = lean_ctor_get(v___x_6174_, 0);
v_isSharedCheck_6210_ = !lean_is_exclusive(v___x_6174_);
if (v_isSharedCheck_6210_ == 0)
{
v___x_6205_ = v___x_6174_;
v_isShared_6206_ = v_isSharedCheck_6210_;
goto v_resetjp_6204_;
}
else
{
lean_inc(v_a_6203_);
lean_dec(v___x_6174_);
v___x_6205_ = lean_box(0);
v_isShared_6206_ = v_isSharedCheck_6210_;
goto v_resetjp_6204_;
}
v_resetjp_6204_:
{
lean_object* v___x_6208_; 
if (v_isShared_6206_ == 0)
{
v___x_6208_ = v___x_6205_;
goto v_reusejp_6207_;
}
else
{
lean_object* v_reuseFailAlloc_6209_; 
v_reuseFailAlloc_6209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6209_, 0, v_a_6203_);
v___x_6208_ = v_reuseFailAlloc_6209_;
goto v_reusejp_6207_;
}
v_reusejp_6207_:
{
return v___x_6208_;
}
}
}
}
}
else
{
lean_object* v_a_6211_; lean_object* v___x_6213_; uint8_t v_isShared_6214_; uint8_t v_isSharedCheck_6218_; 
lean_dec(v_a_6162_);
lean_dec(v_cls_6115_);
lean_dec_ref(v___x_6113_);
v_a_6211_ = lean_ctor_get(v___x_6163_, 0);
v_isSharedCheck_6218_ = !lean_is_exclusive(v___x_6163_);
if (v_isSharedCheck_6218_ == 0)
{
v___x_6213_ = v___x_6163_;
v_isShared_6214_ = v_isSharedCheck_6218_;
goto v_resetjp_6212_;
}
else
{
lean_inc(v_a_6211_);
lean_dec(v___x_6163_);
v___x_6213_ = lean_box(0);
v_isShared_6214_ = v_isSharedCheck_6218_;
goto v_resetjp_6212_;
}
v_resetjp_6212_:
{
lean_object* v___x_6216_; 
if (v_isShared_6214_ == 0)
{
v___x_6216_ = v___x_6213_;
goto v_reusejp_6215_;
}
else
{
lean_object* v_reuseFailAlloc_6217_; 
v_reuseFailAlloc_6217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6217_, 0, v_a_6211_);
v___x_6216_ = v_reuseFailAlloc_6217_;
goto v_reusejp_6215_;
}
v_reusejp_6215_:
{
return v___x_6216_;
}
}
}
}
else
{
lean_object* v_a_6219_; lean_object* v___x_6221_; uint8_t v_isShared_6222_; uint8_t v_isSharedCheck_6226_; 
lean_dec(v_cls_6115_);
lean_dec_ref(v___x_6113_);
v_a_6219_ = lean_ctor_get(v___x_6161_, 0);
v_isSharedCheck_6226_ = !lean_is_exclusive(v___x_6161_);
if (v_isSharedCheck_6226_ == 0)
{
v___x_6221_ = v___x_6161_;
v_isShared_6222_ = v_isSharedCheck_6226_;
goto v_resetjp_6220_;
}
else
{
lean_inc(v_a_6219_);
lean_dec(v___x_6161_);
v___x_6221_ = lean_box(0);
v_isShared_6222_ = v_isSharedCheck_6226_;
goto v_resetjp_6220_;
}
v_resetjp_6220_:
{
lean_object* v___x_6224_; 
if (v_isShared_6222_ == 0)
{
v___x_6224_ = v___x_6221_;
goto v_reusejp_6223_;
}
else
{
lean_object* v_reuseFailAlloc_6225_; 
v_reuseFailAlloc_6225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6225_, 0, v_a_6219_);
v___x_6224_ = v_reuseFailAlloc_6225_;
goto v_reusejp_6223_;
}
v_reusejp_6223_:
{
return v___x_6224_;
}
}
}
v___jp_6123_:
{
lean_object* v___x_6132_; 
v___x_6132_ = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(v_e_6124_, v___y_6126_);
if (lean_obj_tag(v___x_6132_) == 0)
{
lean_object* v_a_6133_; uint8_t v___x_6134_; 
v_a_6133_ = lean_ctor_get(v___x_6132_, 0);
lean_inc(v_a_6133_);
lean_dec_ref(v___x_6132_);
v___x_6134_ = lean_unbox(v_a_6133_);
lean_dec(v_a_6133_);
if (v___x_6134_ == 0)
{
lean_object* v___x_6135_; 
lean_dec_ref(v_onTrue_6125_);
v___x_6135_ = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(v_e_6124_, v___y_6126_);
if (lean_obj_tag(v___x_6135_) == 0)
{
lean_object* v_a_6136_; uint8_t v___x_6137_; 
v_a_6136_ = lean_ctor_get(v___x_6135_, 0);
lean_inc(v_a_6136_);
lean_dec_ref(v___x_6135_);
v___x_6137_ = lean_unbox(v_a_6136_);
lean_dec(v_a_6136_);
if (v___x_6137_ == 0)
{
lean_object* v___x_6138_; lean_object* v___x_6139_; lean_object* v___x_6140_; lean_object* v___x_6141_; 
v___x_6138_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1);
v___x_6139_ = l_Lean_indentExpr(v_e_6124_);
v___x_6140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6140_, 0, v___x_6138_);
lean_ctor_set(v___x_6140_, 1, v___x_6139_);
v___x_6141_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_6140_, v___y_6128_, v___y_6129_, v___y_6130_, v___y_6131_);
return v___x_6141_;
}
else
{
lean_object* v___x_6142_; lean_object* v___x_6143_; 
lean_dec_ref(v_e_6124_);
v___x_6142_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3);
v___x_6143_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_6142_, v___y_6128_, v___y_6129_, v___y_6130_, v___y_6131_);
return v___x_6143_;
}
}
else
{
lean_object* v_a_6144_; lean_object* v___x_6146_; uint8_t v_isShared_6147_; uint8_t v_isSharedCheck_6151_; 
lean_dec_ref(v_e_6124_);
v_a_6144_ = lean_ctor_get(v___x_6135_, 0);
v_isSharedCheck_6151_ = !lean_is_exclusive(v___x_6135_);
if (v_isSharedCheck_6151_ == 0)
{
v___x_6146_ = v___x_6135_;
v_isShared_6147_ = v_isSharedCheck_6151_;
goto v_resetjp_6145_;
}
else
{
lean_inc(v_a_6144_);
lean_dec(v___x_6135_);
v___x_6146_ = lean_box(0);
v_isShared_6147_ = v_isSharedCheck_6151_;
goto v_resetjp_6145_;
}
v_resetjp_6145_:
{
lean_object* v___x_6149_; 
if (v_isShared_6147_ == 0)
{
v___x_6149_ = v___x_6146_;
goto v_reusejp_6148_;
}
else
{
lean_object* v_reuseFailAlloc_6150_; 
v_reuseFailAlloc_6150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6150_, 0, v_a_6144_);
v___x_6149_ = v_reuseFailAlloc_6150_;
goto v_reusejp_6148_;
}
v_reusejp_6148_:
{
return v___x_6149_;
}
}
}
}
else
{
lean_object* v___x_6152_; 
lean_dec_ref(v_e_6124_);
lean_inc(v___y_6131_);
lean_inc_ref(v___y_6130_);
lean_inc(v___y_6129_);
lean_inc_ref(v___y_6128_);
lean_inc(v___y_6127_);
lean_inc_ref(v___y_6126_);
v___x_6152_ = lean_apply_7(v_onTrue_6125_, v___y_6126_, v___y_6127_, v___y_6128_, v___y_6129_, v___y_6130_, v___y_6131_, lean_box(0));
return v___x_6152_;
}
}
else
{
lean_object* v_a_6153_; lean_object* v___x_6155_; uint8_t v_isShared_6156_; uint8_t v_isSharedCheck_6160_; 
lean_dec_ref(v_onTrue_6125_);
lean_dec_ref(v_e_6124_);
v_a_6153_ = lean_ctor_get(v___x_6132_, 0);
v_isSharedCheck_6160_ = !lean_is_exclusive(v___x_6132_);
if (v_isSharedCheck_6160_ == 0)
{
v___x_6155_ = v___x_6132_;
v_isShared_6156_ = v_isSharedCheck_6160_;
goto v_resetjp_6154_;
}
else
{
lean_inc(v_a_6153_);
lean_dec(v___x_6132_);
v___x_6155_ = lean_box(0);
v_isShared_6156_ = v_isSharedCheck_6160_;
goto v_resetjp_6154_;
}
v_resetjp_6154_:
{
lean_object* v___x_6158_; 
if (v_isShared_6156_ == 0)
{
v___x_6158_ = v___x_6155_;
goto v_reusejp_6157_;
}
else
{
lean_object* v_reuseFailAlloc_6159_; 
v_reuseFailAlloc_6159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6159_, 0, v_a_6153_);
v___x_6158_ = v_reuseFailAlloc_6159_;
goto v_reusejp_6157_;
}
v_reusejp_6157_:
{
return v___x_6158_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__6___boxed(lean_object* v_m_6227_, lean_object* v___x_6228_, lean_object* v___x_6229_, lean_object* v_cls_6230_, lean_object* v___y_6231_, lean_object* v___y_6232_, lean_object* v___y_6233_, lean_object* v___y_6234_, lean_object* v___y_6235_, lean_object* v___y_6236_, lean_object* v___y_6237_){
_start:
{
uint8_t v___x_26039__boxed_6238_; lean_object* v_res_6239_; 
v___x_26039__boxed_6238_ = lean_unbox(v___x_6229_);
v_res_6239_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__6(v_m_6227_, v___x_6228_, v___x_26039__boxed_6238_, v_cls_6230_, v___y_6231_, v___y_6232_, v___y_6233_, v___y_6234_, v___y_6235_, v___y_6236_);
lean_dec(v___y_6236_);
lean_dec_ref(v___y_6235_);
lean_dec(v___y_6234_);
lean_dec_ref(v___y_6233_);
lean_dec(v___y_6232_);
lean_dec_ref(v___y_6231_);
return v_res_6239_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2_spec__2(lean_object* v_e_6240_){
_start:
{
if (lean_obj_tag(v_e_6240_) == 0)
{
uint8_t v___x_6241_; 
v___x_6241_ = 2;
return v___x_6241_;
}
else
{
uint8_t v___x_6242_; 
v___x_6242_ = 0;
return v___x_6242_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2_spec__2___boxed(lean_object* v_e_6243_){
_start:
{
uint8_t v_res_6244_; lean_object* v_r_6245_; 
v_res_6244_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2_spec__2(v_e_6243_);
lean_dec_ref(v_e_6243_);
v_r_6245_ = lean_box(v_res_6244_);
return v_r_6245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2(lean_object* v_cls_6246_, uint8_t v_collapsed_6247_, lean_object* v_tag_6248_, lean_object* v_opts_6249_, uint8_t v_clsEnabled_6250_, lean_object* v_oldTraces_6251_, lean_object* v_msg_6252_, lean_object* v_resStartStop_6253_, lean_object* v___y_6254_, lean_object* v___y_6255_, lean_object* v___y_6256_, lean_object* v___y_6257_){
_start:
{
lean_object* v_fst_6259_; lean_object* v_snd_6260_; lean_object* v___x_6262_; uint8_t v_isShared_6263_; uint8_t v_isSharedCheck_6351_; 
v_fst_6259_ = lean_ctor_get(v_resStartStop_6253_, 0);
v_snd_6260_ = lean_ctor_get(v_resStartStop_6253_, 1);
v_isSharedCheck_6351_ = !lean_is_exclusive(v_resStartStop_6253_);
if (v_isSharedCheck_6351_ == 0)
{
v___x_6262_ = v_resStartStop_6253_;
v_isShared_6263_ = v_isSharedCheck_6351_;
goto v_resetjp_6261_;
}
else
{
lean_inc(v_snd_6260_);
lean_inc(v_fst_6259_);
lean_dec(v_resStartStop_6253_);
v___x_6262_ = lean_box(0);
v_isShared_6263_ = v_isSharedCheck_6351_;
goto v_resetjp_6261_;
}
v_resetjp_6261_:
{
lean_object* v___y_6265_; lean_object* v___y_6266_; lean_object* v_data_6267_; lean_object* v_fst_6270_; lean_object* v_snd_6271_; lean_object* v___x_6273_; uint8_t v_isShared_6274_; uint8_t v_isSharedCheck_6350_; 
v_fst_6270_ = lean_ctor_get(v_snd_6260_, 0);
v_snd_6271_ = lean_ctor_get(v_snd_6260_, 1);
v_isSharedCheck_6350_ = !lean_is_exclusive(v_snd_6260_);
if (v_isSharedCheck_6350_ == 0)
{
v___x_6273_ = v_snd_6260_;
v_isShared_6274_ = v_isSharedCheck_6350_;
goto v_resetjp_6272_;
}
else
{
lean_inc(v_snd_6271_);
lean_inc(v_fst_6270_);
lean_dec(v_snd_6260_);
v___x_6273_ = lean_box(0);
v_isShared_6274_ = v_isSharedCheck_6350_;
goto v_resetjp_6272_;
}
v___jp_6264_:
{
lean_object* v___x_6268_; 
lean_inc(v___y_6265_);
v___x_6268_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__1(v_oldTraces_6251_, v_data_6267_, v___y_6265_, v___y_6266_, v___y_6254_, v___y_6255_, v___y_6256_, v___y_6257_);
if (lean_obj_tag(v___x_6268_) == 0)
{
lean_object* v___x_6269_; 
lean_dec_ref(v___x_6268_);
v___x_6269_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg(v_fst_6259_);
return v___x_6269_;
}
else
{
lean_dec(v_fst_6259_);
return v___x_6268_;
}
}
v_resetjp_6272_:
{
lean_object* v___x_6275_; uint8_t v___x_6276_; lean_object* v___y_6278_; lean_object* v_a_6279_; uint8_t v___y_6303_; double v___y_6335_; 
v___x_6275_ = l_Lean_trace_profiler;
v___x_6276_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_6249_, v___x_6275_);
if (v___x_6276_ == 0)
{
v___y_6303_ = v___x_6276_;
goto v___jp_6302_;
}
else
{
lean_object* v___x_6340_; uint8_t v___x_6341_; 
v___x_6340_ = l_Lean_trace_profiler_useHeartbeats;
v___x_6341_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_6249_, v___x_6340_);
if (v___x_6341_ == 0)
{
lean_object* v___x_6342_; lean_object* v___x_6343_; double v___x_6344_; double v___x_6345_; double v___x_6346_; 
v___x_6342_ = l_Lean_trace_profiler_threshold;
v___x_6343_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_6249_, v___x_6342_);
v___x_6344_ = lean_float_of_nat(v___x_6343_);
v___x_6345_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__4);
v___x_6346_ = lean_float_div(v___x_6344_, v___x_6345_);
v___y_6335_ = v___x_6346_;
goto v___jp_6334_;
}
else
{
lean_object* v___x_6347_; lean_object* v___x_6348_; double v___x_6349_; 
v___x_6347_ = l_Lean_trace_profiler_threshold;
v___x_6348_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_6249_, v___x_6347_);
v___x_6349_ = lean_float_of_nat(v___x_6348_);
v___y_6335_ = v___x_6349_;
goto v___jp_6334_;
}
}
v___jp_6277_:
{
uint8_t v_result_6280_; lean_object* v___x_6281_; lean_object* v___x_6282_; lean_object* v___x_6283_; lean_object* v___x_6285_; 
v_result_6280_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2_spec__2(v_fst_6259_);
v___x_6281_ = l_Lean_TraceResult_toEmoji(v_result_6280_);
v___x_6282_ = l_Lean_stringToMessageData(v___x_6281_);
v___x_6283_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1);
if (v_isShared_6274_ == 0)
{
lean_ctor_set_tag(v___x_6273_, 7);
lean_ctor_set(v___x_6273_, 1, v___x_6283_);
lean_ctor_set(v___x_6273_, 0, v___x_6282_);
v___x_6285_ = v___x_6273_;
goto v_reusejp_6284_;
}
else
{
lean_object* v_reuseFailAlloc_6296_; 
v_reuseFailAlloc_6296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6296_, 0, v___x_6282_);
lean_ctor_set(v_reuseFailAlloc_6296_, 1, v___x_6283_);
v___x_6285_ = v_reuseFailAlloc_6296_;
goto v_reusejp_6284_;
}
v_reusejp_6284_:
{
lean_object* v_m_6287_; 
if (v_isShared_6263_ == 0)
{
lean_ctor_set_tag(v___x_6262_, 7);
lean_ctor_set(v___x_6262_, 1, v_a_6279_);
lean_ctor_set(v___x_6262_, 0, v___x_6285_);
v_m_6287_ = v___x_6262_;
goto v_reusejp_6286_;
}
else
{
lean_object* v_reuseFailAlloc_6295_; 
v_reuseFailAlloc_6295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6295_, 0, v___x_6285_);
lean_ctor_set(v_reuseFailAlloc_6295_, 1, v_a_6279_);
v_m_6287_ = v_reuseFailAlloc_6295_;
goto v_reusejp_6286_;
}
v_reusejp_6286_:
{
lean_object* v___x_6288_; lean_object* v___x_6289_; double v___x_6290_; lean_object* v_data_6291_; 
v___x_6288_ = lean_box(v_result_6280_);
v___x_6289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6289_, 0, v___x_6288_);
v___x_6290_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_6248_);
lean_inc_ref(v___x_6289_);
lean_inc(v_cls_6246_);
v_data_6291_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_6291_, 0, v_cls_6246_);
lean_ctor_set(v_data_6291_, 1, v___x_6289_);
lean_ctor_set(v_data_6291_, 2, v_tag_6248_);
lean_ctor_set_float(v_data_6291_, sizeof(void*)*3, v___x_6290_);
lean_ctor_set_float(v_data_6291_, sizeof(void*)*3 + 8, v___x_6290_);
lean_ctor_set_uint8(v_data_6291_, sizeof(void*)*3 + 16, v_collapsed_6247_);
if (v___x_6276_ == 0)
{
lean_dec_ref(v___x_6289_);
lean_dec(v_snd_6271_);
lean_dec(v_fst_6270_);
lean_dec_ref(v_tag_6248_);
lean_dec(v_cls_6246_);
v___y_6265_ = v___y_6278_;
v___y_6266_ = v_m_6287_;
v_data_6267_ = v_data_6291_;
goto v___jp_6264_;
}
else
{
lean_object* v_data_6292_; double v___x_6293_; double v___x_6294_; 
lean_dec_ref(v_data_6291_);
v_data_6292_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_6292_, 0, v_cls_6246_);
lean_ctor_set(v_data_6292_, 1, v___x_6289_);
lean_ctor_set(v_data_6292_, 2, v_tag_6248_);
v___x_6293_ = lean_unbox_float(v_fst_6270_);
lean_dec(v_fst_6270_);
lean_ctor_set_float(v_data_6292_, sizeof(void*)*3, v___x_6293_);
v___x_6294_ = lean_unbox_float(v_snd_6271_);
lean_dec(v_snd_6271_);
lean_ctor_set_float(v_data_6292_, sizeof(void*)*3 + 8, v___x_6294_);
lean_ctor_set_uint8(v_data_6292_, sizeof(void*)*3 + 16, v_collapsed_6247_);
v___y_6265_ = v___y_6278_;
v___y_6266_ = v_m_6287_;
v_data_6267_ = v_data_6292_;
goto v___jp_6264_;
}
}
}
}
v___jp_6297_:
{
lean_object* v_ref_6298_; lean_object* v___x_6299_; 
v_ref_6298_ = lean_ctor_get(v___y_6256_, 5);
lean_inc(v___y_6257_);
lean_inc_ref(v___y_6256_);
lean_inc(v___y_6255_);
lean_inc_ref(v___y_6254_);
lean_inc(v_fst_6259_);
v___x_6299_ = lean_apply_6(v_msg_6252_, v_fst_6259_, v___y_6254_, v___y_6255_, v___y_6256_, v___y_6257_, lean_box(0));
if (lean_obj_tag(v___x_6299_) == 0)
{
lean_object* v_a_6300_; 
v_a_6300_ = lean_ctor_get(v___x_6299_, 0);
lean_inc(v_a_6300_);
lean_dec_ref(v___x_6299_);
v___y_6278_ = v_ref_6298_;
v_a_6279_ = v_a_6300_;
goto v___jp_6277_;
}
else
{
lean_object* v___x_6301_; 
lean_dec_ref(v___x_6299_);
v___x_6301_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__3);
v___y_6278_ = v_ref_6298_;
v_a_6279_ = v___x_6301_;
goto v___jp_6277_;
}
}
v___jp_6302_:
{
if (v_clsEnabled_6250_ == 0)
{
if (v___y_6303_ == 0)
{
lean_object* v___x_6304_; lean_object* v_traceState_6305_; lean_object* v_env_6306_; lean_object* v_nextMacroScope_6307_; lean_object* v_ngen_6308_; lean_object* v_auxDeclNGen_6309_; lean_object* v_cache_6310_; lean_object* v_messages_6311_; lean_object* v_infoState_6312_; lean_object* v_snapshotTasks_6313_; lean_object* v_newDecls_6314_; lean_object* v___x_6316_; uint8_t v_isShared_6317_; uint8_t v_isSharedCheck_6333_; 
lean_del_object(v___x_6273_);
lean_dec(v_snd_6271_);
lean_dec(v_fst_6270_);
lean_del_object(v___x_6262_);
lean_dec_ref(v_msg_6252_);
lean_dec_ref(v_tag_6248_);
lean_dec(v_cls_6246_);
v___x_6304_ = lean_st_ref_take(v___y_6257_);
v_traceState_6305_ = lean_ctor_get(v___x_6304_, 4);
v_env_6306_ = lean_ctor_get(v___x_6304_, 0);
v_nextMacroScope_6307_ = lean_ctor_get(v___x_6304_, 1);
v_ngen_6308_ = lean_ctor_get(v___x_6304_, 2);
v_auxDeclNGen_6309_ = lean_ctor_get(v___x_6304_, 3);
v_cache_6310_ = lean_ctor_get(v___x_6304_, 5);
v_messages_6311_ = lean_ctor_get(v___x_6304_, 6);
v_infoState_6312_ = lean_ctor_get(v___x_6304_, 7);
v_snapshotTasks_6313_ = lean_ctor_get(v___x_6304_, 8);
v_newDecls_6314_ = lean_ctor_get(v___x_6304_, 9);
v_isSharedCheck_6333_ = !lean_is_exclusive(v___x_6304_);
if (v_isSharedCheck_6333_ == 0)
{
v___x_6316_ = v___x_6304_;
v_isShared_6317_ = v_isSharedCheck_6333_;
goto v_resetjp_6315_;
}
else
{
lean_inc(v_newDecls_6314_);
lean_inc(v_snapshotTasks_6313_);
lean_inc(v_infoState_6312_);
lean_inc(v_messages_6311_);
lean_inc(v_cache_6310_);
lean_inc(v_traceState_6305_);
lean_inc(v_auxDeclNGen_6309_);
lean_inc(v_ngen_6308_);
lean_inc(v_nextMacroScope_6307_);
lean_inc(v_env_6306_);
lean_dec(v___x_6304_);
v___x_6316_ = lean_box(0);
v_isShared_6317_ = v_isSharedCheck_6333_;
goto v_resetjp_6315_;
}
v_resetjp_6315_:
{
uint64_t v_tid_6318_; lean_object* v_traces_6319_; lean_object* v___x_6321_; uint8_t v_isShared_6322_; uint8_t v_isSharedCheck_6332_; 
v_tid_6318_ = lean_ctor_get_uint64(v_traceState_6305_, sizeof(void*)*1);
v_traces_6319_ = lean_ctor_get(v_traceState_6305_, 0);
v_isSharedCheck_6332_ = !lean_is_exclusive(v_traceState_6305_);
if (v_isSharedCheck_6332_ == 0)
{
v___x_6321_ = v_traceState_6305_;
v_isShared_6322_ = v_isSharedCheck_6332_;
goto v_resetjp_6320_;
}
else
{
lean_inc(v_traces_6319_);
lean_dec(v_traceState_6305_);
v___x_6321_ = lean_box(0);
v_isShared_6322_ = v_isSharedCheck_6332_;
goto v_resetjp_6320_;
}
v_resetjp_6320_:
{
lean_object* v___x_6323_; lean_object* v___x_6325_; 
v___x_6323_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_6251_, v_traces_6319_);
lean_dec_ref(v_traces_6319_);
if (v_isShared_6322_ == 0)
{
lean_ctor_set(v___x_6321_, 0, v___x_6323_);
v___x_6325_ = v___x_6321_;
goto v_reusejp_6324_;
}
else
{
lean_object* v_reuseFailAlloc_6331_; 
v_reuseFailAlloc_6331_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6331_, 0, v___x_6323_);
lean_ctor_set_uint64(v_reuseFailAlloc_6331_, sizeof(void*)*1, v_tid_6318_);
v___x_6325_ = v_reuseFailAlloc_6331_;
goto v_reusejp_6324_;
}
v_reusejp_6324_:
{
lean_object* v___x_6327_; 
if (v_isShared_6317_ == 0)
{
lean_ctor_set(v___x_6316_, 4, v___x_6325_);
v___x_6327_ = v___x_6316_;
goto v_reusejp_6326_;
}
else
{
lean_object* v_reuseFailAlloc_6330_; 
v_reuseFailAlloc_6330_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6330_, 0, v_env_6306_);
lean_ctor_set(v_reuseFailAlloc_6330_, 1, v_nextMacroScope_6307_);
lean_ctor_set(v_reuseFailAlloc_6330_, 2, v_ngen_6308_);
lean_ctor_set(v_reuseFailAlloc_6330_, 3, v_auxDeclNGen_6309_);
lean_ctor_set(v_reuseFailAlloc_6330_, 4, v___x_6325_);
lean_ctor_set(v_reuseFailAlloc_6330_, 5, v_cache_6310_);
lean_ctor_set(v_reuseFailAlloc_6330_, 6, v_messages_6311_);
lean_ctor_set(v_reuseFailAlloc_6330_, 7, v_infoState_6312_);
lean_ctor_set(v_reuseFailAlloc_6330_, 8, v_snapshotTasks_6313_);
lean_ctor_set(v_reuseFailAlloc_6330_, 9, v_newDecls_6314_);
v___x_6327_ = v_reuseFailAlloc_6330_;
goto v_reusejp_6326_;
}
v_reusejp_6326_:
{
lean_object* v___x_6328_; lean_object* v___x_6329_; 
v___x_6328_ = lean_st_ref_set(v___y_6257_, v___x_6327_);
v___x_6329_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg(v_fst_6259_);
return v___x_6329_;
}
}
}
}
}
else
{
goto v___jp_6297_;
}
}
else
{
goto v___jp_6297_;
}
}
v___jp_6334_:
{
double v___x_6336_; double v___x_6337_; double v___x_6338_; uint8_t v___x_6339_; 
v___x_6336_ = lean_unbox_float(v_snd_6271_);
v___x_6337_ = lean_unbox_float(v_fst_6270_);
v___x_6338_ = lean_float_sub(v___x_6336_, v___x_6337_);
v___x_6339_ = lean_float_decLt(v___y_6335_, v___x_6338_);
v___y_6303_ = v___x_6339_;
goto v___jp_6302_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2___boxed(lean_object* v_cls_6352_, lean_object* v_collapsed_6353_, lean_object* v_tag_6354_, lean_object* v_opts_6355_, lean_object* v_clsEnabled_6356_, lean_object* v_oldTraces_6357_, lean_object* v_msg_6358_, lean_object* v_resStartStop_6359_, lean_object* v___y_6360_, lean_object* v___y_6361_, lean_object* v___y_6362_, lean_object* v___y_6363_, lean_object* v___y_6364_){
_start:
{
uint8_t v_collapsed_boxed_6365_; uint8_t v_clsEnabled_boxed_6366_; lean_object* v_res_6367_; 
v_collapsed_boxed_6365_ = lean_unbox(v_collapsed_6353_);
v_clsEnabled_boxed_6366_ = lean_unbox(v_clsEnabled_6356_);
v_res_6367_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2(v_cls_6352_, v_collapsed_boxed_6365_, v_tag_6354_, v_opts_6355_, v_clsEnabled_boxed_6366_, v_oldTraces_6357_, v_msg_6358_, v_resStartStop_6359_, v___y_6360_, v___y_6361_, v___y_6362_, v___y_6363_);
lean_dec(v___y_6363_);
lean_dec_ref(v___y_6362_);
lean_dec(v___y_6361_);
lean_dec_ref(v___y_6360_);
lean_dec_ref(v_opts_6355_);
return v_res_6367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal(lean_object* v_m_6369_, lean_object* v_a_6370_, lean_object* v_a_6371_, lean_object* v_a_6372_, lean_object* v_a_6373_){
_start:
{
lean_object* v_options_6375_; lean_object* v_inheritedTraceOptions_6376_; uint8_t v_hasTrace_6377_; lean_object* v_cls_6378_; 
v_options_6375_ = lean_ctor_get(v_a_6372_, 2);
v_inheritedTraceOptions_6376_ = lean_ctor_get(v_a_6372_, 13);
v_hasTrace_6377_ = lean_ctor_get_uint8(v_options_6375_, sizeof(void*)*1);
v_cls_6378_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0));
if (v_hasTrace_6377_ == 0)
{
lean_object* v___x_6379_; lean_object* v___x_6380_; lean_object* v___x_6381_; lean_object* v___x_6382_; lean_object* v___f_6383_; lean_object* v___x_6384_; 
v___x_6379_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_6380_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_6375_, v___x_6379_);
v___x_6381_ = lean_unsigned_to_nat(2u);
v___x_6382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6382_, 0, v___x_6380_);
lean_ctor_set(v___x_6382_, 1, v___x_6381_);
v___f_6383_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___boxed), 10, 3);
lean_closure_set(v___f_6383_, 0, v_m_6369_);
lean_closure_set(v___f_6383_, 1, v___x_6382_);
lean_closure_set(v___f_6383_, 2, v_cls_6378_);
v___x_6384_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_6383_, v_a_6370_, v_a_6371_, v_a_6372_, v_a_6373_);
return v___x_6384_;
}
else
{
lean_object* v___f_6385_; lean_object* v___x_6386_; lean_object* v___x_6387_; uint8_t v___x_6388_; lean_object* v___y_6390_; lean_object* v___y_6391_; lean_object* v_a_6392_; lean_object* v___y_6405_; lean_object* v___y_6406_; lean_object* v_a_6407_; 
v___f_6385_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___closed__0));
v___x_6386_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__1));
v___x_6387_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1);
v___x_6388_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6376_, v_options_6375_, v___x_6387_);
if (v___x_6388_ == 0)
{
lean_object* v___x_6469_; uint8_t v___x_6470_; 
v___x_6469_ = l_Lean_trace_profiler;
v___x_6470_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_6375_, v___x_6469_);
if (v___x_6470_ == 0)
{
lean_object* v___x_6471_; lean_object* v___x_6472_; lean_object* v___x_6473_; lean_object* v___x_6474_; lean_object* v___x_6475_; lean_object* v___f_6476_; lean_object* v___x_6477_; 
v___x_6471_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_6472_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_6375_, v___x_6471_);
v___x_6473_ = lean_unsigned_to_nat(2u);
v___x_6474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6474_, 0, v___x_6472_);
lean_ctor_set(v___x_6474_, 1, v___x_6473_);
v___x_6475_ = lean_box(v_hasTrace_6377_);
v___f_6476_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__4___boxed), 11, 4);
lean_closure_set(v___f_6476_, 0, v_m_6369_);
lean_closure_set(v___f_6476_, 1, v___x_6474_);
lean_closure_set(v___f_6476_, 2, v___x_6475_);
lean_closure_set(v___f_6476_, 3, v_cls_6378_);
v___x_6477_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_6476_, v_a_6370_, v_a_6371_, v_a_6372_, v_a_6373_);
return v___x_6477_;
}
else
{
goto v___jp_6416_;
}
}
else
{
goto v___jp_6416_;
}
v___jp_6389_:
{
lean_object* v___x_6393_; double v___x_6394_; double v___x_6395_; double v___x_6396_; double v___x_6397_; double v___x_6398_; lean_object* v___x_6399_; lean_object* v___x_6400_; lean_object* v___x_6401_; lean_object* v___x_6402_; lean_object* v___x_6403_; 
v___x_6393_ = lean_io_mono_nanos_now();
v___x_6394_ = lean_float_of_nat(v___y_6391_);
v___x_6395_ = lean_float_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9);
v___x_6396_ = lean_float_div(v___x_6394_, v___x_6395_);
v___x_6397_ = lean_float_of_nat(v___x_6393_);
v___x_6398_ = lean_float_div(v___x_6397_, v___x_6395_);
v___x_6399_ = lean_box_float(v___x_6396_);
v___x_6400_ = lean_box_float(v___x_6398_);
v___x_6401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6401_, 0, v___x_6399_);
lean_ctor_set(v___x_6401_, 1, v___x_6400_);
v___x_6402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6402_, 0, v_a_6392_);
lean_ctor_set(v___x_6402_, 1, v___x_6401_);
v___x_6403_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2(v_cls_6378_, v_hasTrace_6377_, v___x_6386_, v_options_6375_, v___x_6388_, v___y_6390_, v___f_6385_, v___x_6402_, v_a_6370_, v_a_6371_, v_a_6372_, v_a_6373_);
return v___x_6403_;
}
v___jp_6404_:
{
lean_object* v___x_6408_; double v___x_6409_; double v___x_6410_; lean_object* v___x_6411_; lean_object* v___x_6412_; lean_object* v___x_6413_; lean_object* v___x_6414_; lean_object* v___x_6415_; 
v___x_6408_ = lean_io_get_num_heartbeats();
v___x_6409_ = lean_float_of_nat(v___y_6406_);
v___x_6410_ = lean_float_of_nat(v___x_6408_);
v___x_6411_ = lean_box_float(v___x_6409_);
v___x_6412_ = lean_box_float(v___x_6410_);
v___x_6413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6413_, 0, v___x_6411_);
lean_ctor_set(v___x_6413_, 1, v___x_6412_);
v___x_6414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6414_, 0, v_a_6407_);
lean_ctor_set(v___x_6414_, 1, v___x_6413_);
v___x_6415_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2(v_cls_6378_, v_hasTrace_6377_, v___x_6386_, v_options_6375_, v___x_6388_, v___y_6405_, v___f_6385_, v___x_6414_, v_a_6370_, v_a_6371_, v_a_6372_, v_a_6373_);
return v___x_6415_;
}
v___jp_6416_:
{
lean_object* v___x_6417_; lean_object* v_a_6418_; lean_object* v___x_6419_; uint8_t v___x_6420_; 
v___x_6417_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg(v_a_6373_);
v_a_6418_ = lean_ctor_get(v___x_6417_, 0);
lean_inc(v_a_6418_);
lean_dec_ref(v___x_6417_);
v___x_6419_ = l_Lean_trace_profiler_useHeartbeats;
v___x_6420_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_6375_, v___x_6419_);
if (v___x_6420_ == 0)
{
lean_object* v___x_6421_; lean_object* v___x_6422_; lean_object* v___x_6423_; lean_object* v___x_6424_; lean_object* v___x_6425_; lean_object* v___x_6426_; lean_object* v___f_6427_; lean_object* v___x_6428_; 
v___x_6421_ = lean_io_mono_nanos_now();
v___x_6422_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_6423_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_6375_, v___x_6422_);
v___x_6424_ = lean_unsigned_to_nat(2u);
v___x_6425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6425_, 0, v___x_6423_);
lean_ctor_set(v___x_6425_, 1, v___x_6424_);
v___x_6426_ = lean_box(v_hasTrace_6377_);
v___f_6427_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__4___boxed), 11, 4);
lean_closure_set(v___f_6427_, 0, v_m_6369_);
lean_closure_set(v___f_6427_, 1, v___x_6425_);
lean_closure_set(v___f_6427_, 2, v___x_6426_);
lean_closure_set(v___f_6427_, 3, v_cls_6378_);
v___x_6428_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_6427_, v_a_6370_, v_a_6371_, v_a_6372_, v_a_6373_);
if (lean_obj_tag(v___x_6428_) == 0)
{
lean_object* v_a_6429_; lean_object* v___x_6431_; uint8_t v_isShared_6432_; uint8_t v_isSharedCheck_6436_; 
v_a_6429_ = lean_ctor_get(v___x_6428_, 0);
v_isSharedCheck_6436_ = !lean_is_exclusive(v___x_6428_);
if (v_isSharedCheck_6436_ == 0)
{
v___x_6431_ = v___x_6428_;
v_isShared_6432_ = v_isSharedCheck_6436_;
goto v_resetjp_6430_;
}
else
{
lean_inc(v_a_6429_);
lean_dec(v___x_6428_);
v___x_6431_ = lean_box(0);
v_isShared_6432_ = v_isSharedCheck_6436_;
goto v_resetjp_6430_;
}
v_resetjp_6430_:
{
lean_object* v___x_6434_; 
if (v_isShared_6432_ == 0)
{
lean_ctor_set_tag(v___x_6431_, 1);
v___x_6434_ = v___x_6431_;
goto v_reusejp_6433_;
}
else
{
lean_object* v_reuseFailAlloc_6435_; 
v_reuseFailAlloc_6435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6435_, 0, v_a_6429_);
v___x_6434_ = v_reuseFailAlloc_6435_;
goto v_reusejp_6433_;
}
v_reusejp_6433_:
{
v___y_6390_ = v_a_6418_;
v___y_6391_ = v___x_6421_;
v_a_6392_ = v___x_6434_;
goto v___jp_6389_;
}
}
}
else
{
lean_object* v_a_6437_; lean_object* v___x_6439_; uint8_t v_isShared_6440_; uint8_t v_isSharedCheck_6444_; 
v_a_6437_ = lean_ctor_get(v___x_6428_, 0);
v_isSharedCheck_6444_ = !lean_is_exclusive(v___x_6428_);
if (v_isSharedCheck_6444_ == 0)
{
v___x_6439_ = v___x_6428_;
v_isShared_6440_ = v_isSharedCheck_6444_;
goto v_resetjp_6438_;
}
else
{
lean_inc(v_a_6437_);
lean_dec(v___x_6428_);
v___x_6439_ = lean_box(0);
v_isShared_6440_ = v_isSharedCheck_6444_;
goto v_resetjp_6438_;
}
v_resetjp_6438_:
{
lean_object* v___x_6442_; 
if (v_isShared_6440_ == 0)
{
lean_ctor_set_tag(v___x_6439_, 0);
v___x_6442_ = v___x_6439_;
goto v_reusejp_6441_;
}
else
{
lean_object* v_reuseFailAlloc_6443_; 
v_reuseFailAlloc_6443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6443_, 0, v_a_6437_);
v___x_6442_ = v_reuseFailAlloc_6443_;
goto v_reusejp_6441_;
}
v_reusejp_6441_:
{
v___y_6390_ = v_a_6418_;
v___y_6391_ = v___x_6421_;
v_a_6392_ = v___x_6442_;
goto v___jp_6389_;
}
}
}
}
else
{
lean_object* v___x_6445_; lean_object* v___x_6446_; lean_object* v___x_6447_; lean_object* v___x_6448_; lean_object* v___x_6449_; lean_object* v___x_6450_; lean_object* v___f_6451_; lean_object* v___x_6452_; 
v___x_6445_ = lean_io_get_num_heartbeats();
v___x_6446_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_6447_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_6375_, v___x_6446_);
v___x_6448_ = lean_unsigned_to_nat(2u);
v___x_6449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6449_, 0, v___x_6447_);
lean_ctor_set(v___x_6449_, 1, v___x_6448_);
v___x_6450_ = lean_box(v___x_6420_);
v___f_6451_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__6___boxed), 11, 4);
lean_closure_set(v___f_6451_, 0, v_m_6369_);
lean_closure_set(v___f_6451_, 1, v___x_6449_);
lean_closure_set(v___f_6451_, 2, v___x_6450_);
lean_closure_set(v___f_6451_, 3, v_cls_6378_);
v___x_6452_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_6451_, v_a_6370_, v_a_6371_, v_a_6372_, v_a_6373_);
if (lean_obj_tag(v___x_6452_) == 0)
{
lean_object* v_a_6453_; lean_object* v___x_6455_; uint8_t v_isShared_6456_; uint8_t v_isSharedCheck_6460_; 
v_a_6453_ = lean_ctor_get(v___x_6452_, 0);
v_isSharedCheck_6460_ = !lean_is_exclusive(v___x_6452_);
if (v_isSharedCheck_6460_ == 0)
{
v___x_6455_ = v___x_6452_;
v_isShared_6456_ = v_isSharedCheck_6460_;
goto v_resetjp_6454_;
}
else
{
lean_inc(v_a_6453_);
lean_dec(v___x_6452_);
v___x_6455_ = lean_box(0);
v_isShared_6456_ = v_isSharedCheck_6460_;
goto v_resetjp_6454_;
}
v_resetjp_6454_:
{
lean_object* v___x_6458_; 
if (v_isShared_6456_ == 0)
{
lean_ctor_set_tag(v___x_6455_, 1);
v___x_6458_ = v___x_6455_;
goto v_reusejp_6457_;
}
else
{
lean_object* v_reuseFailAlloc_6459_; 
v_reuseFailAlloc_6459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6459_, 0, v_a_6453_);
v___x_6458_ = v_reuseFailAlloc_6459_;
goto v_reusejp_6457_;
}
v_reusejp_6457_:
{
v___y_6405_ = v_a_6418_;
v___y_6406_ = v___x_6445_;
v_a_6407_ = v___x_6458_;
goto v___jp_6404_;
}
}
}
else
{
lean_object* v_a_6461_; lean_object* v___x_6463_; uint8_t v_isShared_6464_; uint8_t v_isSharedCheck_6468_; 
v_a_6461_ = lean_ctor_get(v___x_6452_, 0);
v_isSharedCheck_6468_ = !lean_is_exclusive(v___x_6452_);
if (v_isSharedCheck_6468_ == 0)
{
v___x_6463_ = v___x_6452_;
v_isShared_6464_ = v_isSharedCheck_6468_;
goto v_resetjp_6462_;
}
else
{
lean_inc(v_a_6461_);
lean_dec(v___x_6452_);
v___x_6463_ = lean_box(0);
v_isShared_6464_ = v_isSharedCheck_6468_;
goto v_resetjp_6462_;
}
v_resetjp_6462_:
{
lean_object* v___x_6466_; 
if (v_isShared_6464_ == 0)
{
lean_ctor_set_tag(v___x_6463_, 0);
v___x_6466_ = v___x_6463_;
goto v_reusejp_6465_;
}
else
{
lean_object* v_reuseFailAlloc_6467_; 
v_reuseFailAlloc_6467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6467_, 0, v_a_6461_);
v___x_6466_ = v_reuseFailAlloc_6467_;
goto v_reusejp_6465_;
}
v_reusejp_6465_:
{
v___y_6405_ = v_a_6418_;
v___y_6406_ = v___x_6445_;
v_a_6407_ = v___x_6466_;
goto v___jp_6404_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___boxed(lean_object* v_m_6478_, lean_object* v_a_6479_, lean_object* v_a_6480_, lean_object* v_a_6481_, lean_object* v_a_6482_, lean_object* v_a_6483_){
_start:
{
lean_object* v_res_6484_; 
v_res_6484_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal(v_m_6478_, v_a_6479_, v_a_6480_, v_a_6481_, v_a_6482_);
lean_dec(v_a_6482_);
lean_dec_ref(v_a_6481_);
lean_dec(v_a_6480_);
lean_dec_ref(v_a_6479_);
return v_res_6484_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0(lean_object* v_00_u03b1_6485_, lean_object* v_msg_6486_, lean_object* v___y_6487_, lean_object* v___y_6488_, lean_object* v___y_6489_, lean_object* v___y_6490_, lean_object* v___y_6491_, lean_object* v___y_6492_){
_start:
{
lean_object* v___x_6494_; 
v___x_6494_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v_msg_6486_, v___y_6489_, v___y_6490_, v___y_6491_, v___y_6492_);
return v___x_6494_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___boxed(lean_object* v_00_u03b1_6495_, lean_object* v_msg_6496_, lean_object* v___y_6497_, lean_object* v___y_6498_, lean_object* v___y_6499_, lean_object* v___y_6500_, lean_object* v___y_6501_, lean_object* v___y_6502_, lean_object* v___y_6503_){
_start:
{
lean_object* v_res_6504_; 
v_res_6504_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0(v_00_u03b1_6495_, v_msg_6496_, v___y_6497_, v___y_6498_, v___y_6499_, v___y_6500_, v___y_6501_, v___y_6502_);
lean_dec(v___y_6502_);
lean_dec_ref(v___y_6501_);
lean_dec(v___y_6500_);
lean_dec_ref(v___y_6499_);
lean_dec(v___y_6498_);
lean_dec_ref(v___y_6497_);
return v_res_6504_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1(lean_object* v_cls_6505_, lean_object* v_msg_6506_, lean_object* v___y_6507_, lean_object* v___y_6508_, lean_object* v___y_6509_, lean_object* v___y_6510_, lean_object* v___y_6511_, lean_object* v___y_6512_){
_start:
{
lean_object* v___x_6514_; 
v___x_6514_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(v_cls_6505_, v_msg_6506_, v___y_6509_, v___y_6510_, v___y_6511_, v___y_6512_);
return v___x_6514_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___boxed(lean_object* v_cls_6515_, lean_object* v_msg_6516_, lean_object* v___y_6517_, lean_object* v___y_6518_, lean_object* v___y_6519_, lean_object* v___y_6520_, lean_object* v___y_6521_, lean_object* v___y_6522_, lean_object* v___y_6523_){
_start:
{
lean_object* v_res_6524_; 
v_res_6524_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1(v_cls_6515_, v_msg_6516_, v___y_6517_, v___y_6518_, v___y_6519_, v___y_6520_, v___y_6521_, v___y_6522_);
lean_dec(v___y_6522_);
lean_dec_ref(v___y_6521_);
lean_dec(v___y_6520_);
lean_dec_ref(v___y_6519_);
lean_dec(v___y_6518_);
lean_dec_ref(v___y_6517_);
return v_res_6524_;
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

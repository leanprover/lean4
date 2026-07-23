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
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
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
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__6(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__6___boxed(lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2_spec__2___boxed(lean_object*);
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
v___y_1091_ = v___y_1111_;
v___y_1092_ = v_a_1112_;
v___y_1093_ = v_contextDependent_1113_;
goto v___jp_1090_;
}
else
{
uint8_t v_contextDependent_1114_; 
v_contextDependent_1114_ = lean_ctor_get_uint8(v_a_1112_, sizeof(void*)*2 + 1);
v___y_1091_ = v___y_1111_;
v___y_1092_ = v_a_1112_;
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
lean_dec_ref(v___y_1091_);
v___x_1094_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_1092_);
v___x_1095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1094_);
return v___x_1095_;
}
else
{
lean_dec_ref(v___y_1092_);
return v___y_1091_;
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
v_debug_1638_ = lean_ctor_get_uint8(v___x_1637_, sizeof(void*)*11);
lean_dec(v___x_1637_);
if (v_debug_1638_ == 0)
{
v___y_1634_ = v___y_1627_;
goto v___jp_1633_;
}
else
{
lean_object* v___x_1639_; 
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
lean_object* v___x_1699_; lean_object* v___x_134448__overap_1700_; lean_object* v___x_1701_; 
v___x_1699_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___closed__0);
v___x_134448__overap_1700_ = lean_panic_fn_borrowed(v___x_1699_, v_msg_1688_);
lean_inc(v___y_1697_);
lean_inc_ref(v___y_1696_);
lean_inc(v___y_1695_);
lean_inc_ref(v___y_1694_);
lean_inc(v___y_1693_);
lean_inc_ref(v___y_1692_);
lean_inc(v___y_1691_);
lean_inc_ref(v___y_1690_);
lean_inc(v___y_1689_);
v___x_1701_ = lean_apply_10(v___x_134448__overap_1700_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, lean_box(0));
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
lean_object* v_keyedConfig_1803_; uint8_t v_trackZetaDelta_1804_; lean_object* v_zetaDeltaSet_1805_; lean_object* v_lctx_1806_; lean_object* v_localInstances_1807_; lean_object* v_defEqCtx_x3f_1808_; lean_object* v_synthPendingDepth_1809_; lean_object* v_customCanUnfoldPredicate_x3f_1810_; uint8_t v_univApprox_1811_; uint8_t v_inTypeClassResolution_1812_; uint8_t v_cacheInferType_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1822_; 
v_keyedConfig_1803_ = lean_ctor_get(v___y_1798_, 0);
v_trackZetaDelta_1804_ = lean_ctor_get_uint8(v___y_1798_, sizeof(void*)*7);
v_zetaDeltaSet_1805_ = lean_ctor_get(v___y_1798_, 1);
v_lctx_1806_ = lean_ctor_get(v___y_1798_, 2);
v_localInstances_1807_ = lean_ctor_get(v___y_1798_, 3);
v_defEqCtx_x3f_1808_ = lean_ctor_get(v___y_1798_, 4);
v_synthPendingDepth_1809_ = lean_ctor_get(v___y_1798_, 5);
v_customCanUnfoldPredicate_x3f_1810_ = lean_ctor_get(v___y_1798_, 6);
v_univApprox_1811_ = lean_ctor_get_uint8(v___y_1798_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1812_ = lean_ctor_get_uint8(v___y_1798_, sizeof(void*)*7 + 2);
v_cacheInferType_1813_ = lean_ctor_get_uint8(v___y_1798_, sizeof(void*)*7 + 3);
v_isSharedCheck_1822_ = !lean_is_exclusive(v___y_1798_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1815_ = v___y_1798_;
v_isShared_1816_ = v_isSharedCheck_1822_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_1810_);
lean_inc(v_synthPendingDepth_1809_);
lean_inc(v_defEqCtx_x3f_1808_);
lean_inc(v_localInstances_1807_);
lean_inc(v_lctx_1806_);
lean_inc(v_zetaDeltaSet_1805_);
lean_inc(v_keyedConfig_1803_);
lean_dec(v___y_1798_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1822_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1817_; lean_object* v___x_1819_; 
v___x_1817_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1796_, v_keyedConfig_1803_);
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 0, v___x_1817_);
v___x_1819_ = v___x_1815_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v___x_1817_);
lean_ctor_set(v_reuseFailAlloc_1821_, 1, v_zetaDeltaSet_1805_);
lean_ctor_set(v_reuseFailAlloc_1821_, 2, v_lctx_1806_);
lean_ctor_set(v_reuseFailAlloc_1821_, 3, v_localInstances_1807_);
lean_ctor_set(v_reuseFailAlloc_1821_, 4, v_defEqCtx_x3f_1808_);
lean_ctor_set(v_reuseFailAlloc_1821_, 5, v_synthPendingDepth_1809_);
lean_ctor_set(v_reuseFailAlloc_1821_, 6, v_customCanUnfoldPredicate_x3f_1810_);
lean_ctor_set_uint8(v_reuseFailAlloc_1821_, sizeof(void*)*7, v_trackZetaDelta_1804_);
lean_ctor_set_uint8(v_reuseFailAlloc_1821_, sizeof(void*)*7 + 1, v_univApprox_1811_);
lean_ctor_set_uint8(v_reuseFailAlloc_1821_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1812_);
lean_ctor_set_uint8(v_reuseFailAlloc_1821_, sizeof(void*)*7 + 3, v_cacheInferType_1813_);
v___x_1819_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
lean_object* v___x_1820_; 
v___x_1820_ = l_Lean_Meta_reduceProj_x3f(v_e_1797_, v___x_1819_, v___y_1799_, v___y_1800_, v___y_1801_);
lean_dec_ref(v___x_1819_);
return v___x_1820_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___boxed(lean_object* v___x_1823_, lean_object* v_e_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_){
_start:
{
uint8_t v___x_151092__boxed_1830_; lean_object* v_res_1831_; 
v___x_151092__boxed_1830_ = lean_unbox(v___x_1823_);
v_res_1831_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0(v___x_151092__boxed_1830_, v_e_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
lean_dec(v___y_1828_);
lean_dec_ref(v___y_1827_);
lean_dec(v___y_1826_);
return v_res_1831_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1833_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__0));
v___x_1834_ = l_Lean_stringToMessageData(v___x_1833_);
return v___x_1834_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; 
v___x_1836_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__2));
v___x_1837_ = l_Lean_stringToMessageData(v___x_1836_);
return v___x_1837_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__5(void){
_start:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1839_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__4));
v___x_1840_ = l_Lean_stringToMessageData(v___x_1839_);
return v___x_1840_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__7(void){
_start:
{
lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1842_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__6));
v___x_1843_ = l_Lean_stringToMessageData(v___x_1842_);
return v___x_1843_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__9(void){
_start:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1845_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__8));
v___x_1846_ = l_Lean_stringToMessageData(v___x_1845_);
return v___x_1846_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2(lean_object* v_typeName_1847_, lean_object* v_idx_1848_, lean_object* v_e_1849_, lean_object* v_x_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_){
_start:
{
if (lean_obj_tag(v_x_1850_) == 0)
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1881_; 
lean_dec_ref(v_e_1849_);
v_a_1861_ = lean_ctor_get(v_x_1850_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v_x_1850_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1863_ = v_x_1850_;
v_isShared_1864_ = v_isSharedCheck_1881_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v_x_1850_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1881_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1872_; 
v___x_1865_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__1, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__1);
v___x_1866_ = l_Lean_MessageData_ofName(v_typeName_1847_);
v___x_1867_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1867_, 0, v___x_1865_);
lean_ctor_set(v___x_1867_, 1, v___x_1866_);
v___x_1868_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_1869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1867_);
lean_ctor_set(v___x_1869_, 1, v___x_1868_);
v___x_1870_ = l_Nat_reprFast(v_idx_1848_);
if (v_isShared_1864_ == 0)
{
lean_ctor_set_tag(v___x_1863_, 3);
lean_ctor_set(v___x_1863_, 0, v___x_1870_);
v___x_1872_ = v___x_1863_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v___x_1870_);
v___x_1872_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1873_ = l_Lean_MessageData_ofFormat(v___x_1872_);
v___x_1874_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1869_);
lean_ctor_set(v___x_1874_, 1, v___x_1873_);
v___x_1875_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__3, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__3_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__3);
v___x_1876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1874_);
lean_ctor_set(v___x_1876_, 1, v___x_1875_);
v___x_1877_ = l_Lean_Exception_toMessageData(v_a_1861_);
v___x_1878_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1876_);
lean_ctor_set(v___x_1878_, 1, v___x_1877_);
v___x_1879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1879_, 0, v___x_1878_);
return v___x_1879_;
}
}
}
else
{
lean_object* v_a_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1938_; 
v_a_1882_ = lean_ctor_get(v_x_1850_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v_x_1850_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1884_ = v_x_1850_;
v_isShared_1885_ = v_isSharedCheck_1938_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_a_1882_);
lean_dec(v_x_1850_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1938_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
if (lean_obj_tag(v_a_1882_) == 0)
{
uint8_t v_done_1886_; 
v_done_1886_ = lean_ctor_get_uint8(v_a_1882_, 0);
lean_dec_ref_known(v_a_1882_, 0);
if (v_done_1886_ == 1)
{
lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1894_; 
v___x_1887_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__1, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__1);
v___x_1888_ = l_Lean_MessageData_ofName(v_typeName_1847_);
v___x_1889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1887_);
lean_ctor_set(v___x_1889_, 1, v___x_1888_);
v___x_1890_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_1891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1889_);
lean_ctor_set(v___x_1891_, 1, v___x_1890_);
v___x_1892_ = l_Nat_reprFast(v_idx_1848_);
if (v_isShared_1885_ == 0)
{
lean_ctor_set_tag(v___x_1884_, 3);
lean_ctor_set(v___x_1884_, 0, v___x_1892_);
v___x_1894_ = v___x_1884_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v___x_1892_);
v___x_1894_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1895_ = l_Lean_MessageData_ofFormat(v___x_1894_);
v___x_1896_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1891_);
lean_ctor_set(v___x_1896_, 1, v___x_1895_);
v___x_1897_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__5, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__5_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__5);
v___x_1898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1896_);
lean_ctor_set(v___x_1898_, 1, v___x_1897_);
v___x_1899_ = l_Lean_indentExpr(v_e_1849_);
v___x_1900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1898_);
lean_ctor_set(v___x_1900_, 1, v___x_1899_);
v___x_1901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1900_);
return v___x_1901_;
}
}
else
{
lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1910_; 
lean_dec_ref(v_e_1849_);
v___x_1903_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__1, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__1);
v___x_1904_ = l_Lean_MessageData_ofName(v_typeName_1847_);
v___x_1905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1903_);
lean_ctor_set(v___x_1905_, 1, v___x_1904_);
v___x_1906_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_1907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1905_);
lean_ctor_set(v___x_1907_, 1, v___x_1906_);
v___x_1908_ = l_Nat_reprFast(v_idx_1848_);
if (v_isShared_1885_ == 0)
{
lean_ctor_set_tag(v___x_1884_, 3);
lean_ctor_set(v___x_1884_, 0, v___x_1908_);
v___x_1910_ = v___x_1884_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v___x_1908_);
v___x_1910_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1911_ = l_Lean_MessageData_ofFormat(v___x_1910_);
v___x_1912_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1912_, 0, v___x_1907_);
lean_ctor_set(v___x_1912_, 1, v___x_1911_);
v___x_1913_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__7, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__7_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__7);
v___x_1914_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1912_);
lean_ctor_set(v___x_1914_, 1, v___x_1913_);
v___x_1915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1914_);
return v___x_1915_;
}
}
}
else
{
lean_object* v_e_x27_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1925_; 
v_e_x27_1917_ = lean_ctor_get(v_a_1882_, 0);
lean_inc_ref(v_e_x27_1917_);
lean_dec_ref_known(v_a_1882_, 2);
v___x_1918_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__1, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__1);
v___x_1919_ = l_Lean_MessageData_ofName(v_typeName_1847_);
v___x_1920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1918_);
lean_ctor_set(v___x_1920_, 1, v___x_1919_);
v___x_1921_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_1922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1920_);
lean_ctor_set(v___x_1922_, 1, v___x_1921_);
v___x_1923_ = l_Nat_reprFast(v_idx_1848_);
if (v_isShared_1885_ == 0)
{
lean_ctor_set_tag(v___x_1884_, 3);
lean_ctor_set(v___x_1884_, 0, v___x_1923_);
v___x_1925_ = v___x_1884_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v___x_1923_);
v___x_1925_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1926_ = l_Lean_MessageData_ofFormat(v___x_1925_);
v___x_1927_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1922_);
lean_ctor_set(v___x_1927_, 1, v___x_1926_);
v___x_1928_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__9, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__9_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__9);
v___x_1929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1927_);
lean_ctor_set(v___x_1929_, 1, v___x_1928_);
v___x_1930_ = l_Lean_indentExpr(v_e_1849_);
v___x_1931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1929_);
lean_ctor_set(v___x_1931_, 1, v___x_1930_);
v___x_1932_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_1933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1931_);
lean_ctor_set(v___x_1933_, 1, v___x_1932_);
v___x_1934_ = l_Lean_indentExpr(v_e_x27_1917_);
v___x_1935_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1933_);
lean_ctor_set(v___x_1935_, 1, v___x_1934_);
v___x_1936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1936_, 0, v___x_1935_);
return v___x_1936_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___boxed(lean_object* v_typeName_1939_, lean_object* v_idx_1940_, lean_object* v_e_1941_, lean_object* v_x_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_){
_start:
{
lean_object* v_res_1953_; 
v_res_1953_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2(v_typeName_1939_, v_idx_1940_, v_e_1941_, v_x_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_);
lean_dec(v___y_1951_);
lean_dec_ref(v___y_1950_);
lean_dec(v___y_1949_);
lean_dec_ref(v___y_1948_);
lean_dec(v___y_1947_);
lean_dec_ref(v___y_1946_);
lean_dec(v___y_1945_);
lean_dec_ref(v___y_1944_);
lean_dec(v___y_1943_);
return v_res_1953_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5___redArg(lean_object* v_x_1954_){
_start:
{
if (lean_obj_tag(v_x_1954_) == 0)
{
lean_object* v_a_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1963_; 
v_a_1956_ = lean_ctor_get(v_x_1954_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v_x_1954_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1958_ = v_x_1954_;
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_a_1956_);
lean_dec(v_x_1954_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1961_; 
if (v_isShared_1959_ == 0)
{
lean_ctor_set_tag(v___x_1958_, 1);
v___x_1961_ = v___x_1958_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_a_1956_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
return v___x_1961_;
}
}
}
else
{
lean_object* v_a_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1971_; 
v_a_1964_ = lean_ctor_get(v_x_1954_, 0);
v_isSharedCheck_1971_ = !lean_is_exclusive(v_x_1954_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1966_ = v_x_1954_;
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_a_1964_);
lean_dec(v_x_1954_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1969_; 
if (v_isShared_1967_ == 0)
{
lean_ctor_set_tag(v___x_1966_, 0);
v___x_1969_ = v___x_1966_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v_a_1964_);
v___x_1969_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
return v___x_1969_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5___redArg___boxed(lean_object* v_x_1972_, lean_object* v___y_1973_){
_start:
{
lean_object* v_res_1974_; 
v_res_1974_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5___redArg(v_x_1972_);
return v_res_1974_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4_spec__5(size_t v_sz_1975_, size_t v_i_1976_, lean_object* v_bs_1977_){
_start:
{
uint8_t v___x_1978_; 
v___x_1978_ = lean_usize_dec_lt(v_i_1976_, v_sz_1975_);
if (v___x_1978_ == 0)
{
return v_bs_1977_;
}
else
{
lean_object* v_v_1979_; lean_object* v_msg_1980_; lean_object* v___x_1981_; lean_object* v_bs_x27_1982_; size_t v___x_1983_; size_t v___x_1984_; lean_object* v___x_1985_; 
v_v_1979_ = lean_array_uget_borrowed(v_bs_1977_, v_i_1976_);
v_msg_1980_ = lean_ctor_get(v_v_1979_, 1);
lean_inc_ref(v_msg_1980_);
v___x_1981_ = lean_unsigned_to_nat(0u);
v_bs_x27_1982_ = lean_array_uset(v_bs_1977_, v_i_1976_, v___x_1981_);
v___x_1983_ = ((size_t)1ULL);
v___x_1984_ = lean_usize_add(v_i_1976_, v___x_1983_);
v___x_1985_ = lean_array_uset(v_bs_x27_1982_, v_i_1976_, v_msg_1980_);
v_i_1976_ = v___x_1984_;
v_bs_1977_ = v___x_1985_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4_spec__5___boxed(lean_object* v_sz_1987_, lean_object* v_i_1988_, lean_object* v_bs_1989_){
_start:
{
size_t v_sz_boxed_1990_; size_t v_i_boxed_1991_; lean_object* v_res_1992_; 
v_sz_boxed_1990_ = lean_unbox_usize(v_sz_1987_);
lean_dec(v_sz_1987_);
v_i_boxed_1991_ = lean_unbox_usize(v_i_1988_);
lean_dec(v_i_1988_);
v_res_1992_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4_spec__5(v_sz_boxed_1990_, v_i_boxed_1991_, v_bs_1989_);
return v_res_1992_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4___redArg(lean_object* v_oldTraces_1993_, lean_object* v_data_1994_, lean_object* v_ref_1995_, lean_object* v_msg_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_){
_start:
{
lean_object* v_fileName_2002_; lean_object* v_fileMap_2003_; lean_object* v_options_2004_; lean_object* v_currRecDepth_2005_; lean_object* v_maxRecDepth_2006_; lean_object* v_ref_2007_; lean_object* v_currNamespace_2008_; lean_object* v_openDecls_2009_; lean_object* v_initHeartbeats_2010_; lean_object* v_maxHeartbeats_2011_; lean_object* v_quotContext_2012_; lean_object* v_currMacroScope_2013_; uint8_t v_diag_2014_; lean_object* v_cancelTk_x3f_2015_; uint8_t v_suppressElabErrors_2016_; lean_object* v_inheritedTraceOptions_2017_; lean_object* v___x_2018_; lean_object* v_traceState_2019_; lean_object* v_traces_2020_; lean_object* v_ref_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; size_t v_sz_2024_; size_t v___x_2025_; lean_object* v___x_2026_; lean_object* v_msg_2027_; lean_object* v___x_2028_; lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2066_; 
v_fileName_2002_ = lean_ctor_get(v___y_1999_, 0);
v_fileMap_2003_ = lean_ctor_get(v___y_1999_, 1);
v_options_2004_ = lean_ctor_get(v___y_1999_, 2);
v_currRecDepth_2005_ = lean_ctor_get(v___y_1999_, 3);
v_maxRecDepth_2006_ = lean_ctor_get(v___y_1999_, 4);
v_ref_2007_ = lean_ctor_get(v___y_1999_, 5);
v_currNamespace_2008_ = lean_ctor_get(v___y_1999_, 6);
v_openDecls_2009_ = lean_ctor_get(v___y_1999_, 7);
v_initHeartbeats_2010_ = lean_ctor_get(v___y_1999_, 8);
v_maxHeartbeats_2011_ = lean_ctor_get(v___y_1999_, 9);
v_quotContext_2012_ = lean_ctor_get(v___y_1999_, 10);
v_currMacroScope_2013_ = lean_ctor_get(v___y_1999_, 11);
v_diag_2014_ = lean_ctor_get_uint8(v___y_1999_, sizeof(void*)*14);
v_cancelTk_x3f_2015_ = lean_ctor_get(v___y_1999_, 12);
v_suppressElabErrors_2016_ = lean_ctor_get_uint8(v___y_1999_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2017_ = lean_ctor_get(v___y_1999_, 13);
v___x_2018_ = lean_st_ref_get(v___y_2000_);
v_traceState_2019_ = lean_ctor_get(v___x_2018_, 4);
lean_inc_ref(v_traceState_2019_);
lean_dec(v___x_2018_);
v_traces_2020_ = lean_ctor_get(v_traceState_2019_, 0);
lean_inc_ref(v_traces_2020_);
lean_dec_ref(v_traceState_2019_);
v_ref_2021_ = l_Lean_replaceRef(v_ref_1995_, v_ref_2007_);
lean_inc_ref(v_inheritedTraceOptions_2017_);
lean_inc(v_cancelTk_x3f_2015_);
lean_inc(v_currMacroScope_2013_);
lean_inc(v_quotContext_2012_);
lean_inc(v_maxHeartbeats_2011_);
lean_inc(v_initHeartbeats_2010_);
lean_inc(v_openDecls_2009_);
lean_inc(v_currNamespace_2008_);
lean_inc(v_maxRecDepth_2006_);
lean_inc(v_currRecDepth_2005_);
lean_inc_ref(v_options_2004_);
lean_inc_ref(v_fileMap_2003_);
lean_inc_ref(v_fileName_2002_);
v___x_2022_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2022_, 0, v_fileName_2002_);
lean_ctor_set(v___x_2022_, 1, v_fileMap_2003_);
lean_ctor_set(v___x_2022_, 2, v_options_2004_);
lean_ctor_set(v___x_2022_, 3, v_currRecDepth_2005_);
lean_ctor_set(v___x_2022_, 4, v_maxRecDepth_2006_);
lean_ctor_set(v___x_2022_, 5, v_ref_2021_);
lean_ctor_set(v___x_2022_, 6, v_currNamespace_2008_);
lean_ctor_set(v___x_2022_, 7, v_openDecls_2009_);
lean_ctor_set(v___x_2022_, 8, v_initHeartbeats_2010_);
lean_ctor_set(v___x_2022_, 9, v_maxHeartbeats_2011_);
lean_ctor_set(v___x_2022_, 10, v_quotContext_2012_);
lean_ctor_set(v___x_2022_, 11, v_currMacroScope_2013_);
lean_ctor_set(v___x_2022_, 12, v_cancelTk_x3f_2015_);
lean_ctor_set(v___x_2022_, 13, v_inheritedTraceOptions_2017_);
lean_ctor_set_uint8(v___x_2022_, sizeof(void*)*14, v_diag_2014_);
lean_ctor_set_uint8(v___x_2022_, sizeof(void*)*14 + 1, v_suppressElabErrors_2016_);
v___x_2023_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2020_);
lean_dec_ref(v_traces_2020_);
v_sz_2024_ = lean_array_size(v___x_2023_);
v___x_2025_ = ((size_t)0ULL);
v___x_2026_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4_spec__5(v_sz_2024_, v___x_2025_, v___x_2023_);
v_msg_2027_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2027_, 0, v_data_1994_);
lean_ctor_set(v_msg_2027_, 1, v_msg_1996_);
lean_ctor_set(v_msg_2027_, 2, v___x_2026_);
v___x_2028_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0_spec__0(v_msg_2027_, v___y_1997_, v___y_1998_, v___x_2022_, v___y_2000_);
lean_dec_ref_known(v___x_2022_, 14);
v_a_2029_ = lean_ctor_get(v___x_2028_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2028_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2031_ = v___x_2028_;
v_isShared_2032_ = v_isSharedCheck_2066_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_dec(v___x_2028_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2066_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2033_; lean_object* v_traceState_2034_; lean_object* v_env_2035_; lean_object* v_nextMacroScope_2036_; lean_object* v_ngen_2037_; lean_object* v_auxDeclNGen_2038_; lean_object* v_cache_2039_; lean_object* v_messages_2040_; lean_object* v_infoState_2041_; lean_object* v_snapshotTasks_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2065_; 
v___x_2033_ = lean_st_ref_take(v___y_2000_);
v_traceState_2034_ = lean_ctor_get(v___x_2033_, 4);
v_env_2035_ = lean_ctor_get(v___x_2033_, 0);
v_nextMacroScope_2036_ = lean_ctor_get(v___x_2033_, 1);
v_ngen_2037_ = lean_ctor_get(v___x_2033_, 2);
v_auxDeclNGen_2038_ = lean_ctor_get(v___x_2033_, 3);
v_cache_2039_ = lean_ctor_get(v___x_2033_, 5);
v_messages_2040_ = lean_ctor_get(v___x_2033_, 6);
v_infoState_2041_ = lean_ctor_get(v___x_2033_, 7);
v_snapshotTasks_2042_ = lean_ctor_get(v___x_2033_, 8);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2044_ = v___x_2033_;
v_isShared_2045_ = v_isSharedCheck_2065_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_snapshotTasks_2042_);
lean_inc(v_infoState_2041_);
lean_inc(v_messages_2040_);
lean_inc(v_cache_2039_);
lean_inc(v_traceState_2034_);
lean_inc(v_auxDeclNGen_2038_);
lean_inc(v_ngen_2037_);
lean_inc(v_nextMacroScope_2036_);
lean_inc(v_env_2035_);
lean_dec(v___x_2033_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2065_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
uint64_t v_tid_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2063_; 
v_tid_2046_ = lean_ctor_get_uint64(v_traceState_2034_, sizeof(void*)*1);
v_isSharedCheck_2063_ = !lean_is_exclusive(v_traceState_2034_);
if (v_isSharedCheck_2063_ == 0)
{
lean_object* v_unused_2064_; 
v_unused_2064_ = lean_ctor_get(v_traceState_2034_, 0);
lean_dec(v_unused_2064_);
v___x_2048_ = v_traceState_2034_;
v_isShared_2049_ = v_isSharedCheck_2063_;
goto v_resetjp_2047_;
}
else
{
lean_dec(v_traceState_2034_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2063_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2053_; 
v___x_2050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2050_, 0, v_ref_1995_);
lean_ctor_set(v___x_2050_, 1, v_a_2029_);
v___x_2051_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1993_, v___x_2050_);
if (v_isShared_2049_ == 0)
{
lean_ctor_set(v___x_2048_, 0, v___x_2051_);
v___x_2053_ = v___x_2048_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v___x_2051_);
lean_ctor_set_uint64(v_reuseFailAlloc_2062_, sizeof(void*)*1, v_tid_2046_);
v___x_2053_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
lean_object* v___x_2055_; 
if (v_isShared_2045_ == 0)
{
lean_ctor_set(v___x_2044_, 4, v___x_2053_);
v___x_2055_ = v___x_2044_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v_env_2035_);
lean_ctor_set(v_reuseFailAlloc_2061_, 1, v_nextMacroScope_2036_);
lean_ctor_set(v_reuseFailAlloc_2061_, 2, v_ngen_2037_);
lean_ctor_set(v_reuseFailAlloc_2061_, 3, v_auxDeclNGen_2038_);
lean_ctor_set(v_reuseFailAlloc_2061_, 4, v___x_2053_);
lean_ctor_set(v_reuseFailAlloc_2061_, 5, v_cache_2039_);
lean_ctor_set(v_reuseFailAlloc_2061_, 6, v_messages_2040_);
lean_ctor_set(v_reuseFailAlloc_2061_, 7, v_infoState_2041_);
lean_ctor_set(v_reuseFailAlloc_2061_, 8, v_snapshotTasks_2042_);
v___x_2055_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2059_; 
v___x_2056_ = lean_st_ref_set(v___y_2000_, v___x_2055_);
v___x_2057_ = lean_box(0);
if (v_isShared_2032_ == 0)
{
lean_ctor_set(v___x_2031_, 0, v___x_2057_);
v___x_2059_ = v___x_2031_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v___x_2057_);
v___x_2059_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
return v___x_2059_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4___redArg___boxed(lean_object* v_oldTraces_2067_, lean_object* v_data_2068_, lean_object* v_ref_2069_, lean_object* v_msg_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_){
_start:
{
lean_object* v_res_2076_; 
v_res_2076_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4___redArg(v_oldTraces_2067_, v_data_2068_, v_ref_2069_, v_msg_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_);
lean_dec(v___y_2074_);
lean_dec_ref(v___y_2073_);
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2071_);
return v_res_2076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(lean_object* v_opts_2077_, lean_object* v_opt_2078_){
_start:
{
lean_object* v_name_2079_; lean_object* v_defValue_2080_; lean_object* v_map_2081_; lean_object* v___x_2082_; 
v_name_2079_ = lean_ctor_get(v_opt_2078_, 0);
v_defValue_2080_ = lean_ctor_get(v_opt_2078_, 1);
v_map_2081_ = lean_ctor_get(v_opts_2077_, 0);
v___x_2082_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2081_, v_name_2079_);
if (lean_obj_tag(v___x_2082_) == 0)
{
lean_inc(v_defValue_2080_);
return v_defValue_2080_;
}
else
{
lean_object* v_val_2083_; 
v_val_2083_ = lean_ctor_get(v___x_2082_, 0);
lean_inc(v_val_2083_);
lean_dec_ref_known(v___x_2082_, 1);
if (lean_obj_tag(v_val_2083_) == 3)
{
lean_object* v_v_2084_; 
v_v_2084_ = lean_ctor_get(v_val_2083_, 0);
lean_inc(v_v_2084_);
lean_dec_ref_known(v_val_2083_, 1);
return v_v_2084_;
}
else
{
lean_dec(v_val_2083_);
lean_inc(v_defValue_2080_);
return v_defValue_2080_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7___boxed(lean_object* v_opts_2085_, lean_object* v_opt_2086_){
_start:
{
lean_object* v_res_2087_; 
v_res_2087_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_2085_, v_opt_2086_);
lean_dec_ref(v_opt_2086_);
lean_dec_ref(v_opts_2085_);
return v_res_2087_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__6(lean_object* v_e_2088_){
_start:
{
if (lean_obj_tag(v_e_2088_) == 0)
{
uint8_t v___x_2089_; 
v___x_2089_ = 2;
return v___x_2089_;
}
else
{
uint8_t v___x_2090_; 
v___x_2090_ = 0;
return v___x_2090_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__6___boxed(lean_object* v_e_2091_){
_start:
{
uint8_t v_res_2092_; lean_object* v_r_2093_; 
v_res_2092_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__6(v_e_2091_);
lean_dec_ref(v_e_2091_);
v_r_2093_ = lean_box(v_res_2092_);
return v_r_2093_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1(void){
_start:
{
lean_object* v___x_2095_; lean_object* v___x_2096_; 
v___x_2095_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__0));
v___x_2096_ = l_Lean_stringToMessageData(v___x_2095_);
return v___x_2096_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2(void){
_start:
{
lean_object* v___x_2097_; double v___x_2098_; 
v___x_2097_ = lean_unsigned_to_nat(1000u);
v___x_2098_ = lean_float_of_nat(v___x_2097_);
return v___x_2098_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4(lean_object* v_cls_2099_, uint8_t v_collapsed_2100_, lean_object* v_tag_2101_, lean_object* v_opts_2102_, uint8_t v_clsEnabled_2103_, lean_object* v_oldTraces_2104_, lean_object* v_msg_2105_, lean_object* v_resStartStop_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_){
_start:
{
lean_object* v_fst_2117_; lean_object* v_snd_2118_; lean_object* v___y_2120_; lean_object* v___y_2121_; lean_object* v_data_2122_; lean_object* v_fst_2133_; lean_object* v_snd_2134_; lean_object* v___x_2135_; uint8_t v___x_2136_; lean_object* v___y_2138_; lean_object* v_a_2139_; uint8_t v___y_2154_; double v___y_2185_; 
v_fst_2117_ = lean_ctor_get(v_resStartStop_2106_, 0);
lean_inc(v_fst_2117_);
v_snd_2118_ = lean_ctor_get(v_resStartStop_2106_, 1);
lean_inc(v_snd_2118_);
lean_dec_ref(v_resStartStop_2106_);
v_fst_2133_ = lean_ctor_get(v_snd_2118_, 0);
lean_inc(v_fst_2133_);
v_snd_2134_ = lean_ctor_get(v_snd_2118_, 1);
lean_inc(v_snd_2134_);
lean_dec(v_snd_2118_);
v___x_2135_ = l_Lean_trace_profiler;
v___x_2136_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_2102_, v___x_2135_);
if (v___x_2136_ == 0)
{
v___y_2154_ = v___x_2136_;
goto v___jp_2153_;
}
else
{
lean_object* v___x_2190_; uint8_t v___x_2191_; 
v___x_2190_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2191_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_2102_, v___x_2190_);
if (v___x_2191_ == 0)
{
lean_object* v___x_2192_; lean_object* v___x_2193_; double v___x_2194_; double v___x_2195_; double v___x_2196_; 
v___x_2192_ = l_Lean_trace_profiler_threshold;
v___x_2193_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_2102_, v___x_2192_);
v___x_2194_ = lean_float_of_nat(v___x_2193_);
v___x_2195_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2);
v___x_2196_ = lean_float_div(v___x_2194_, v___x_2195_);
v___y_2185_ = v___x_2196_;
goto v___jp_2184_;
}
else
{
lean_object* v___x_2197_; lean_object* v___x_2198_; double v___x_2199_; 
v___x_2197_ = l_Lean_trace_profiler_threshold;
v___x_2198_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_2102_, v___x_2197_);
v___x_2199_ = lean_float_of_nat(v___x_2198_);
v___y_2185_ = v___x_2199_;
goto v___jp_2184_;
}
}
v___jp_2119_:
{
lean_object* v___x_2123_; 
lean_inc(v___y_2121_);
v___x_2123_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4___redArg(v_oldTraces_2104_, v_data_2122_, v___y_2121_, v___y_2120_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
if (lean_obj_tag(v___x_2123_) == 0)
{
lean_object* v___x_2124_; 
lean_dec_ref_known(v___x_2123_, 1);
v___x_2124_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5___redArg(v_fst_2117_);
return v___x_2124_;
}
else
{
lean_object* v_a_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2132_; 
lean_dec(v_fst_2117_);
v_a_2125_ = lean_ctor_get(v___x_2123_, 0);
v_isSharedCheck_2132_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2127_ = v___x_2123_;
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_a_2125_);
lean_dec(v___x_2123_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v___x_2130_; 
if (v_isShared_2128_ == 0)
{
v___x_2130_ = v___x_2127_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_a_2125_);
v___x_2130_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
return v___x_2130_;
}
}
}
}
v___jp_2137_:
{
uint8_t v_result_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; double v___x_2143_; lean_object* v_data_2144_; 
v_result_2140_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__6(v_fst_2117_);
v___x_2141_ = lean_box(v_result_2140_);
v___x_2142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2142_, 0, v___x_2141_);
v___x_2143_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_2101_);
lean_inc_ref(v___x_2142_);
lean_inc(v_cls_2099_);
v_data_2144_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2144_, 0, v_cls_2099_);
lean_ctor_set(v_data_2144_, 1, v___x_2142_);
lean_ctor_set(v_data_2144_, 2, v_tag_2101_);
lean_ctor_set_float(v_data_2144_, sizeof(void*)*3, v___x_2143_);
lean_ctor_set_float(v_data_2144_, sizeof(void*)*3 + 8, v___x_2143_);
lean_ctor_set_uint8(v_data_2144_, sizeof(void*)*3 + 16, v_collapsed_2100_);
if (v___x_2136_ == 0)
{
lean_dec_ref_known(v___x_2142_, 1);
lean_dec(v_snd_2134_);
lean_dec(v_fst_2133_);
lean_dec_ref(v_tag_2101_);
lean_dec(v_cls_2099_);
v___y_2120_ = v_a_2139_;
v___y_2121_ = v___y_2138_;
v_data_2122_ = v_data_2144_;
goto v___jp_2119_;
}
else
{
lean_object* v_data_2145_; double v___x_2146_; double v___x_2147_; 
lean_dec_ref_known(v_data_2144_, 3);
v_data_2145_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2145_, 0, v_cls_2099_);
lean_ctor_set(v_data_2145_, 1, v___x_2142_);
lean_ctor_set(v_data_2145_, 2, v_tag_2101_);
v___x_2146_ = lean_unbox_float(v_fst_2133_);
lean_dec(v_fst_2133_);
lean_ctor_set_float(v_data_2145_, sizeof(void*)*3, v___x_2146_);
v___x_2147_ = lean_unbox_float(v_snd_2134_);
lean_dec(v_snd_2134_);
lean_ctor_set_float(v_data_2145_, sizeof(void*)*3 + 8, v___x_2147_);
lean_ctor_set_uint8(v_data_2145_, sizeof(void*)*3 + 16, v_collapsed_2100_);
v___y_2120_ = v_a_2139_;
v___y_2121_ = v___y_2138_;
v_data_2122_ = v_data_2145_;
goto v___jp_2119_;
}
}
v___jp_2148_:
{
lean_object* v_ref_2149_; lean_object* v___x_2150_; 
v_ref_2149_ = lean_ctor_get(v___y_2114_, 5);
lean_inc(v___y_2115_);
lean_inc_ref(v___y_2114_);
lean_inc(v___y_2113_);
lean_inc_ref(v___y_2112_);
lean_inc(v___y_2111_);
lean_inc_ref(v___y_2110_);
lean_inc(v___y_2109_);
lean_inc_ref(v___y_2108_);
lean_inc(v___y_2107_);
lean_inc(v_fst_2117_);
v___x_2150_ = lean_apply_11(v_msg_2105_, v_fst_2117_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, lean_box(0));
if (lean_obj_tag(v___x_2150_) == 0)
{
lean_object* v_a_2151_; 
v_a_2151_ = lean_ctor_get(v___x_2150_, 0);
lean_inc(v_a_2151_);
lean_dec_ref_known(v___x_2150_, 1);
v___y_2138_ = v_ref_2149_;
v_a_2139_ = v_a_2151_;
goto v___jp_2137_;
}
else
{
lean_object* v___x_2152_; 
lean_dec_ref_known(v___x_2150_, 1);
v___x_2152_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1);
v___y_2138_ = v_ref_2149_;
v_a_2139_ = v___x_2152_;
goto v___jp_2137_;
}
}
v___jp_2153_:
{
if (v_clsEnabled_2103_ == 0)
{
if (v___y_2154_ == 0)
{
lean_object* v___x_2155_; lean_object* v_traceState_2156_; lean_object* v_env_2157_; lean_object* v_nextMacroScope_2158_; lean_object* v_ngen_2159_; lean_object* v_auxDeclNGen_2160_; lean_object* v_cache_2161_; lean_object* v_messages_2162_; lean_object* v_infoState_2163_; lean_object* v_snapshotTasks_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2183_; 
lean_dec(v_snd_2134_);
lean_dec(v_fst_2133_);
lean_dec_ref(v_msg_2105_);
lean_dec_ref(v_tag_2101_);
lean_dec(v_cls_2099_);
v___x_2155_ = lean_st_ref_take(v___y_2115_);
v_traceState_2156_ = lean_ctor_get(v___x_2155_, 4);
v_env_2157_ = lean_ctor_get(v___x_2155_, 0);
v_nextMacroScope_2158_ = lean_ctor_get(v___x_2155_, 1);
v_ngen_2159_ = lean_ctor_get(v___x_2155_, 2);
v_auxDeclNGen_2160_ = lean_ctor_get(v___x_2155_, 3);
v_cache_2161_ = lean_ctor_get(v___x_2155_, 5);
v_messages_2162_ = lean_ctor_get(v___x_2155_, 6);
v_infoState_2163_ = lean_ctor_get(v___x_2155_, 7);
v_snapshotTasks_2164_ = lean_ctor_get(v___x_2155_, 8);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2155_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2166_ = v___x_2155_;
v_isShared_2167_ = v_isSharedCheck_2183_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_snapshotTasks_2164_);
lean_inc(v_infoState_2163_);
lean_inc(v_messages_2162_);
lean_inc(v_cache_2161_);
lean_inc(v_traceState_2156_);
lean_inc(v_auxDeclNGen_2160_);
lean_inc(v_ngen_2159_);
lean_inc(v_nextMacroScope_2158_);
lean_inc(v_env_2157_);
lean_dec(v___x_2155_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2183_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
uint64_t v_tid_2168_; lean_object* v_traces_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2182_; 
v_tid_2168_ = lean_ctor_get_uint64(v_traceState_2156_, sizeof(void*)*1);
v_traces_2169_ = lean_ctor_get(v_traceState_2156_, 0);
v_isSharedCheck_2182_ = !lean_is_exclusive(v_traceState_2156_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2171_ = v_traceState_2156_;
v_isShared_2172_ = v_isSharedCheck_2182_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_traces_2169_);
lean_dec(v_traceState_2156_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2182_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v___x_2173_; lean_object* v___x_2175_; 
v___x_2173_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2104_, v_traces_2169_);
lean_dec_ref(v_traces_2169_);
if (v_isShared_2172_ == 0)
{
lean_ctor_set(v___x_2171_, 0, v___x_2173_);
v___x_2175_ = v___x_2171_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v___x_2173_);
lean_ctor_set_uint64(v_reuseFailAlloc_2181_, sizeof(void*)*1, v_tid_2168_);
v___x_2175_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
lean_object* v___x_2177_; 
if (v_isShared_2167_ == 0)
{
lean_ctor_set(v___x_2166_, 4, v___x_2175_);
v___x_2177_ = v___x_2166_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_env_2157_);
lean_ctor_set(v_reuseFailAlloc_2180_, 1, v_nextMacroScope_2158_);
lean_ctor_set(v_reuseFailAlloc_2180_, 2, v_ngen_2159_);
lean_ctor_set(v_reuseFailAlloc_2180_, 3, v_auxDeclNGen_2160_);
lean_ctor_set(v_reuseFailAlloc_2180_, 4, v___x_2175_);
lean_ctor_set(v_reuseFailAlloc_2180_, 5, v_cache_2161_);
lean_ctor_set(v_reuseFailAlloc_2180_, 6, v_messages_2162_);
lean_ctor_set(v_reuseFailAlloc_2180_, 7, v_infoState_2163_);
lean_ctor_set(v_reuseFailAlloc_2180_, 8, v_snapshotTasks_2164_);
v___x_2177_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2178_ = lean_st_ref_set(v___y_2115_, v___x_2177_);
v___x_2179_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5___redArg(v_fst_2117_);
return v___x_2179_;
}
}
}
}
}
else
{
goto v___jp_2148_;
}
}
else
{
goto v___jp_2148_;
}
}
v___jp_2184_:
{
double v___x_2186_; double v___x_2187_; double v___x_2188_; uint8_t v___x_2189_; 
v___x_2186_ = lean_unbox_float(v_snd_2134_);
v___x_2187_ = lean_unbox_float(v_fst_2133_);
v___x_2188_ = lean_float_sub(v___x_2186_, v___x_2187_);
v___x_2189_ = lean_float_decLt(v___y_2185_, v___x_2188_);
v___y_2154_ = v___x_2189_;
goto v___jp_2153_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___boxed(lean_object** _args){
lean_object* v_cls_2200_ = _args[0];
lean_object* v_collapsed_2201_ = _args[1];
lean_object* v_tag_2202_ = _args[2];
lean_object* v_opts_2203_ = _args[3];
lean_object* v_clsEnabled_2204_ = _args[4];
lean_object* v_oldTraces_2205_ = _args[5];
lean_object* v_msg_2206_ = _args[6];
lean_object* v_resStartStop_2207_ = _args[7];
lean_object* v___y_2208_ = _args[8];
lean_object* v___y_2209_ = _args[9];
lean_object* v___y_2210_ = _args[10];
lean_object* v___y_2211_ = _args[11];
lean_object* v___y_2212_ = _args[12];
lean_object* v___y_2213_ = _args[13];
lean_object* v___y_2214_ = _args[14];
lean_object* v___y_2215_ = _args[15];
lean_object* v___y_2216_ = _args[16];
lean_object* v___y_2217_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_2218_; uint8_t v_clsEnabled_boxed_2219_; lean_object* v_res_2220_; 
v_collapsed_boxed_2218_ = lean_unbox(v_collapsed_2201_);
v_clsEnabled_boxed_2219_ = lean_unbox(v_clsEnabled_2204_);
v_res_2220_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4(v_cls_2200_, v_collapsed_boxed_2218_, v_tag_2202_, v_opts_2203_, v_clsEnabled_boxed_2219_, v_oldTraces_2205_, v_msg_2206_, v_resStartStop_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_);
lean_dec(v___y_2216_);
lean_dec_ref(v___y_2215_);
lean_dec(v___y_2214_);
lean_dec_ref(v___y_2213_);
lean_dec(v___y_2212_);
lean_dec_ref(v___y_2211_);
lean_dec(v___y_2210_);
lean_dec_ref(v___y_2209_);
lean_dec(v___y_2208_);
lean_dec_ref(v_opts_2203_);
return v_res_2220_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2(void){
_start:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___x_2224_ = lean_unsigned_to_nat(0u);
v___x_2225_ = l_Lean_Expr_bvar___override(v___x_2224_);
return v___x_2225_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8(void){
_start:
{
lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; 
v___x_2232_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__7));
v___x_2233_ = lean_unsigned_to_nat(48u);
v___x_2234_ = lean_unsigned_to_nat(219u);
v___x_2235_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__6));
v___x_2236_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__5));
v___x_2237_ = l_mkPanicMessageWithDecl(v___x_2236_, v___x_2235_, v___x_2234_, v___x_2233_, v___x_2232_);
return v___x_2237_;
}
}
static double _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9(void){
_start:
{
lean_object* v___x_2238_; double v___x_2239_; 
v___x_2238_ = lean_unsigned_to_nat(1000000000u);
v___x_2239_ = lean_float_of_nat(v___x_2238_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj(lean_object* v_e_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_){
_start:
{
uint8_t v___y_2252_; uint8_t v___y_2253_; lean_object* v___y_2254_; lean_object* v_a_2255_; uint8_t v___y_2259_; lean_object* v___y_2260_; lean_object* v_a_2261_; 
if (lean_obj_tag(v_e_2240_) == 11)
{
lean_object* v_typeName_2265_; lean_object* v_idx_2266_; lean_object* v_struct_2267_; lean_object* v_res_2269_; lean_object* v___y_2270_; lean_object* v___y_2271_; lean_object* v___y_2272_; lean_object* v___y_2273_; lean_object* v___y_2274_; lean_object* v___y_2275_; lean_object* v___y_2276_; lean_object* v___y_2277_; lean_object* v___y_2278_; lean_object* v_options_2513_; uint8_t v_hasTrace_2514_; 
v_typeName_2265_ = lean_ctor_get(v_e_2240_, 0);
v_idx_2266_ = lean_ctor_get(v_e_2240_, 1);
v_struct_2267_ = lean_ctor_get(v_e_2240_, 2);
v_options_2513_ = lean_ctor_get(v_a_2248_, 2);
v_hasTrace_2514_ = lean_ctor_get_uint8(v_options_2513_, sizeof(void*)*1);
if (v_hasTrace_2514_ == 0)
{
lean_object* v___x_2515_; 
lean_inc(v_a_2249_);
lean_inc_ref(v_a_2248_);
lean_inc(v_a_2247_);
lean_inc_ref(v_a_2246_);
lean_inc(v_a_2245_);
lean_inc_ref(v_a_2244_);
lean_inc(v_a_2243_);
lean_inc_ref(v_a_2242_);
lean_inc(v_a_2241_);
lean_inc_ref(v_struct_2267_);
v___x_2515_ = lean_sym_simp(v_struct_2267_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_object* v_a_2516_; 
v_a_2516_ = lean_ctor_get(v___x_2515_, 0);
lean_inc(v_a_2516_);
lean_dec_ref_known(v___x_2515_, 1);
v_res_2269_ = v_a_2516_;
v___y_2270_ = v_a_2241_;
v___y_2271_ = v_a_2242_;
v___y_2272_ = v_a_2243_;
v___y_2273_ = v_a_2244_;
v___y_2274_ = v_a_2245_;
v___y_2275_ = v_a_2246_;
v___y_2276_ = v_a_2247_;
v___y_2277_ = v_a_2248_;
v___y_2278_ = v_a_2249_;
goto v___jp_2268_;
}
else
{
lean_dec_ref_known(v_e_2240_, 3);
return v___x_2515_;
}
}
else
{
lean_object* v_inheritedTraceOptions_2517_; lean_object* v___f_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; uint8_t v___x_2522_; lean_object* v___y_2524_; lean_object* v___y_2525_; lean_object* v_a_2526_; lean_object* v___y_2539_; lean_object* v___y_2540_; lean_object* v_a_2541_; lean_object* v___y_2544_; lean_object* v___y_2545_; lean_object* v_a_2546_; lean_object* v___y_2549_; uint8_t v___y_2550_; lean_object* v___y_2551_; lean_object* v___y_2552_; uint8_t v___y_2553_; lean_object* v_a_2554_; lean_object* v___y_2557_; lean_object* v___y_2558_; lean_object* v___y_2559_; lean_object* v___y_2563_; uint8_t v___y_2564_; lean_object* v___y_2565_; lean_object* v___y_2566_; uint8_t v___y_2567_; lean_object* v_a_2568_; lean_object* v___y_2571_; lean_object* v___y_2572_; lean_object* v_a_2573_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v_a_2585_; lean_object* v___y_2588_; lean_object* v___y_2589_; lean_object* v_a_2590_; lean_object* v___y_2593_; uint8_t v___y_2594_; uint8_t v___y_2595_; lean_object* v___y_2596_; lean_object* v___y_2597_; lean_object* v_a_2598_; lean_object* v___y_2601_; lean_object* v___y_2602_; lean_object* v___y_2603_; lean_object* v___y_2607_; uint8_t v___y_2608_; lean_object* v___y_2609_; lean_object* v___y_2610_; lean_object* v_a_2611_; 
v_inheritedTraceOptions_2517_ = lean_ctor_get(v_a_2248_, 13);
lean_inc_ref(v_e_2240_);
lean_inc(v_idx_2266_);
lean_inc(v_typeName_2265_);
v___f_2518_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___boxed), 14, 3);
lean_closure_set(v___f_2518_, 0, v_typeName_2265_);
lean_closure_set(v___f_2518_, 1, v_idx_2266_);
lean_closure_set(v___f_2518_, 2, v_e_2240_);
v___x_2519_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2));
v___x_2520_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__1));
v___x_2521_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3);
v___x_2522_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2517_, v_options_2513_, v___x_2521_);
if (v___x_2522_ == 0)
{
lean_object* v___x_2822_; uint8_t v___x_2823_; 
v___x_2822_ = l_Lean_trace_profiler;
v___x_2823_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_2513_, v___x_2822_);
if (v___x_2823_ == 0)
{
lean_object* v___x_2824_; 
lean_dec_ref(v___f_2518_);
lean_inc(v_a_2249_);
lean_inc_ref(v_a_2248_);
lean_inc(v_a_2247_);
lean_inc_ref(v_a_2246_);
lean_inc(v_a_2245_);
lean_inc_ref(v_a_2244_);
lean_inc(v_a_2243_);
lean_inc_ref(v_a_2242_);
lean_inc(v_a_2241_);
lean_inc_ref(v_struct_2267_);
v___x_2824_ = lean_sym_simp(v_struct_2267_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
if (lean_obj_tag(v___x_2824_) == 0)
{
lean_object* v_a_2825_; 
v_a_2825_ = lean_ctor_get(v___x_2824_, 0);
lean_inc(v_a_2825_);
lean_dec_ref_known(v___x_2824_, 1);
v_res_2269_ = v_a_2825_;
v___y_2270_ = v_a_2241_;
v___y_2271_ = v_a_2242_;
v___y_2272_ = v_a_2243_;
v___y_2273_ = v_a_2244_;
v___y_2274_ = v_a_2245_;
v___y_2275_ = v_a_2246_;
v___y_2276_ = v_a_2247_;
v___y_2277_ = v_a_2248_;
v___y_2278_ = v_a_2249_;
goto v___jp_2268_;
}
else
{
lean_dec_ref_known(v_e_2240_, 3);
return v___x_2824_;
}
}
else
{
goto v___jp_2614_;
}
}
else
{
goto v___jp_2614_;
}
v___jp_2523_:
{
lean_object* v___x_2527_; double v___x_2528_; double v___x_2529_; double v___x_2530_; double v___x_2531_; double v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2527_ = lean_io_mono_nanos_now();
v___x_2528_ = lean_float_of_nat(v___y_2524_);
v___x_2529_ = lean_float_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9);
v___x_2530_ = lean_float_div(v___x_2528_, v___x_2529_);
v___x_2531_ = lean_float_of_nat(v___x_2527_);
v___x_2532_ = lean_float_div(v___x_2531_, v___x_2529_);
v___x_2533_ = lean_box_float(v___x_2530_);
v___x_2534_ = lean_box_float(v___x_2532_);
v___x_2535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2535_, 0, v___x_2533_);
lean_ctor_set(v___x_2535_, 1, v___x_2534_);
v___x_2536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2536_, 0, v_a_2526_);
lean_ctor_set(v___x_2536_, 1, v___x_2535_);
v___x_2537_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4(v___x_2519_, v_hasTrace_2514_, v___x_2520_, v_options_2513_, v___x_2522_, v___y_2525_, v___f_2518_, v___x_2536_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
return v___x_2537_;
}
v___jp_2538_:
{
lean_object* v___x_2542_; 
v___x_2542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2542_, 0, v_a_2541_);
v___y_2524_ = v___y_2539_;
v___y_2525_ = v___y_2540_;
v_a_2526_ = v___x_2542_;
goto v___jp_2523_;
}
v___jp_2543_:
{
lean_object* v___x_2547_; 
v___x_2547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2547_, 0, v_a_2546_);
v___y_2524_ = v___y_2544_;
v___y_2525_ = v___y_2545_;
v_a_2526_ = v___x_2547_;
goto v___jp_2523_;
}
v___jp_2548_:
{
lean_object* v___x_2555_; 
v___x_2555_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2555_, 0, v_a_2554_);
lean_ctor_set(v___x_2555_, 1, v___y_2551_);
lean_ctor_set_uint8(v___x_2555_, sizeof(void*)*2, v___y_2550_);
lean_ctor_set_uint8(v___x_2555_, sizeof(void*)*2 + 1, v___y_2553_);
v___y_2544_ = v___y_2549_;
v___y_2545_ = v___y_2552_;
v_a_2546_ = v___x_2555_;
goto v___jp_2543_;
}
v___jp_2556_:
{
if (lean_obj_tag(v___y_2559_) == 0)
{
lean_object* v_a_2560_; 
v_a_2560_ = lean_ctor_get(v___y_2559_, 0);
lean_inc(v_a_2560_);
lean_dec_ref_known(v___y_2559_, 1);
v___y_2544_ = v___y_2557_;
v___y_2545_ = v___y_2558_;
v_a_2546_ = v_a_2560_;
goto v___jp_2543_;
}
else
{
lean_object* v_a_2561_; 
v_a_2561_ = lean_ctor_get(v___y_2559_, 0);
lean_inc(v_a_2561_);
lean_dec_ref_known(v___y_2559_, 1);
v___y_2539_ = v___y_2557_;
v___y_2540_ = v___y_2558_;
v_a_2541_ = v_a_2561_;
goto v___jp_2538_;
}
}
v___jp_2562_:
{
lean_object* v___x_2569_; 
v___x_2569_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2569_, 0, v_a_2568_);
lean_ctor_set(v___x_2569_, 1, v___y_2566_);
lean_ctor_set_uint8(v___x_2569_, sizeof(void*)*2, v___y_2564_);
lean_ctor_set_uint8(v___x_2569_, sizeof(void*)*2 + 1, v___y_2567_);
v___y_2544_ = v___y_2563_;
v___y_2545_ = v___y_2565_;
v_a_2546_ = v___x_2569_;
goto v___jp_2543_;
}
v___jp_2570_:
{
lean_object* v___x_2574_; double v___x_2575_; double v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; 
v___x_2574_ = lean_io_get_num_heartbeats();
v___x_2575_ = lean_float_of_nat(v___y_2571_);
v___x_2576_ = lean_float_of_nat(v___x_2574_);
v___x_2577_ = lean_box_float(v___x_2575_);
v___x_2578_ = lean_box_float(v___x_2576_);
v___x_2579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2579_, 0, v___x_2577_);
lean_ctor_set(v___x_2579_, 1, v___x_2578_);
v___x_2580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2580_, 0, v_a_2573_);
lean_ctor_set(v___x_2580_, 1, v___x_2579_);
v___x_2581_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4(v___x_2519_, v_hasTrace_2514_, v___x_2520_, v_options_2513_, v___x_2522_, v___y_2572_, v___f_2518_, v___x_2580_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
return v___x_2581_;
}
v___jp_2582_:
{
lean_object* v___x_2586_; 
v___x_2586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2586_, 0, v_a_2585_);
v___y_2571_ = v___y_2583_;
v___y_2572_ = v___y_2584_;
v_a_2573_ = v___x_2586_;
goto v___jp_2570_;
}
v___jp_2587_:
{
lean_object* v___x_2591_; 
v___x_2591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2591_, 0, v_a_2590_);
v___y_2571_ = v___y_2588_;
v___y_2572_ = v___y_2589_;
v_a_2573_ = v___x_2591_;
goto v___jp_2570_;
}
v___jp_2592_:
{
lean_object* v___x_2599_; 
v___x_2599_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2599_, 0, v_a_2598_);
lean_ctor_set(v___x_2599_, 1, v___y_2597_);
lean_ctor_set_uint8(v___x_2599_, sizeof(void*)*2, v___y_2595_);
lean_ctor_set_uint8(v___x_2599_, sizeof(void*)*2 + 1, v___y_2594_);
v___y_2588_ = v___y_2593_;
v___y_2589_ = v___y_2596_;
v_a_2590_ = v___x_2599_;
goto v___jp_2587_;
}
v___jp_2600_:
{
if (lean_obj_tag(v___y_2603_) == 0)
{
lean_object* v_a_2604_; 
v_a_2604_ = lean_ctor_get(v___y_2603_, 0);
lean_inc(v_a_2604_);
lean_dec_ref_known(v___y_2603_, 1);
v___y_2588_ = v___y_2601_;
v___y_2589_ = v___y_2602_;
v_a_2590_ = v_a_2604_;
goto v___jp_2587_;
}
else
{
lean_object* v_a_2605_; 
v_a_2605_ = lean_ctor_get(v___y_2603_, 0);
lean_inc(v_a_2605_);
lean_dec_ref_known(v___y_2603_, 1);
v___y_2583_ = v___y_2601_;
v___y_2584_ = v___y_2602_;
v_a_2585_ = v_a_2605_;
goto v___jp_2582_;
}
}
v___jp_2606_:
{
uint8_t v___x_2612_; lean_object* v___x_2613_; 
v___x_2612_ = 0;
v___x_2613_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2613_, 0, v_a_2611_);
lean_ctor_set(v___x_2613_, 1, v___y_2609_);
lean_ctor_set_uint8(v___x_2613_, sizeof(void*)*2, v___y_2608_);
lean_ctor_set_uint8(v___x_2613_, sizeof(void*)*2 + 1, v___x_2612_);
v___y_2588_ = v___y_2607_;
v___y_2589_ = v___y_2610_;
v_a_2590_ = v___x_2613_;
goto v___jp_2587_;
}
v___jp_2614_:
{
lean_object* v___x_2615_; lean_object* v_a_2616_; lean_object* v___x_2617_; uint8_t v___x_2618_; 
v___x_2615_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg(v_a_2249_);
v_a_2616_ = lean_ctor_get(v___x_2615_, 0);
lean_inc(v_a_2616_);
lean_dec_ref(v___x_2615_);
v___x_2617_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2618_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_2513_, v___x_2617_);
if (v___x_2618_ == 0)
{
lean_object* v___x_2619_; lean_object* v___x_2620_; 
v___x_2619_ = lean_io_mono_nanos_now();
lean_inc(v_a_2249_);
lean_inc_ref(v_a_2248_);
lean_inc(v_a_2247_);
lean_inc_ref(v_a_2246_);
lean_inc(v_a_2245_);
lean_inc_ref(v_a_2244_);
lean_inc(v_a_2243_);
lean_inc_ref(v_a_2242_);
lean_inc(v_a_2241_);
lean_inc_ref(v_struct_2267_);
v___x_2620_ = lean_sym_simp(v_struct_2267_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
if (lean_obj_tag(v___x_2620_) == 0)
{
lean_object* v_a_2621_; 
v_a_2621_ = lean_ctor_get(v___x_2620_, 0);
lean_inc(v_a_2621_);
lean_dec_ref_known(v___x_2620_, 1);
if (lean_obj_tag(v_a_2621_) == 0)
{
uint8_t v_contextDependent_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2643_; 
v_contextDependent_2622_ = lean_ctor_get_uint8(v_a_2621_, 1);
v_isSharedCheck_2643_ = !lean_is_exclusive(v_a_2621_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2624_ = v_a_2621_;
v_isShared_2625_ = v_isSharedCheck_2643_;
goto v_resetjp_2623_;
}
else
{
lean_dec(v_a_2621_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2643_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
uint8_t v___x_2626_; lean_object* v___x_2627_; lean_object* v___f_2628_; lean_object* v___x_2629_; 
v___x_2626_ = 1;
v___x_2627_ = lean_box(v___x_2626_);
v___f_2628_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2628_, 0, v___x_2627_);
lean_closure_set(v___f_2628_, 1, v_e_2240_);
v___x_2629_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___f_2628_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
if (lean_obj_tag(v___x_2629_) == 0)
{
lean_object* v_a_2630_; 
v_a_2630_ = lean_ctor_get(v___x_2629_, 0);
lean_inc(v_a_2630_);
lean_dec_ref_known(v___x_2629_, 1);
if (lean_obj_tag(v_a_2630_) == 1)
{
lean_object* v_val_2631_; lean_object* v___x_2632_; 
lean_del_object(v___x_2624_);
v_val_2631_ = lean_ctor_get(v_a_2630_, 0);
lean_inc(v_val_2631_);
lean_dec_ref_known(v_a_2630_, 1);
v___x_2632_ = l_Lean_Meta_Sym_shareCommonInc(v_val_2631_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
if (lean_obj_tag(v___x_2632_) == 0)
{
lean_object* v_a_2633_; lean_object* v___x_2634_; 
v_a_2633_ = lean_ctor_get(v___x_2632_, 0);
lean_inc_n(v_a_2633_, 2);
lean_dec_ref_known(v___x_2632_, 1);
v___x_2634_ = l_Lean_Meta_Sym_mkEqRefl(v_a_2633_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
if (lean_obj_tag(v___x_2634_) == 0)
{
lean_object* v_a_2635_; lean_object* v___x_2636_; 
v_a_2635_ = lean_ctor_get(v___x_2634_, 0);
lean_inc(v_a_2635_);
lean_dec_ref_known(v___x_2634_, 1);
v___x_2636_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2636_, 0, v_a_2633_);
lean_ctor_set(v___x_2636_, 1, v_a_2635_);
lean_ctor_set_uint8(v___x_2636_, sizeof(void*)*2, v_contextDependent_2622_);
lean_ctor_set_uint8(v___x_2636_, sizeof(void*)*2 + 1, v___x_2618_);
v___y_2544_ = v___x_2619_;
v___y_2545_ = v_a_2616_;
v_a_2546_ = v___x_2636_;
goto v___jp_2543_;
}
else
{
lean_object* v_a_2637_; 
lean_dec(v_a_2633_);
v_a_2637_ = lean_ctor_get(v___x_2634_, 0);
lean_inc(v_a_2637_);
lean_dec_ref_known(v___x_2634_, 1);
v___y_2539_ = v___x_2619_;
v___y_2540_ = v_a_2616_;
v_a_2541_ = v_a_2637_;
goto v___jp_2538_;
}
}
else
{
lean_object* v_a_2638_; 
v_a_2638_ = lean_ctor_get(v___x_2632_, 0);
lean_inc(v_a_2638_);
lean_dec_ref_known(v___x_2632_, 1);
v___y_2539_ = v___x_2619_;
v___y_2540_ = v_a_2616_;
v_a_2541_ = v_a_2638_;
goto v___jp_2538_;
}
}
else
{
lean_object* v___x_2640_; 
lean_dec(v_a_2630_);
if (v_isShared_2625_ == 0)
{
v___x_2640_ = v___x_2624_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v_reuseFailAlloc_2641_, 1, v_contextDependent_2622_);
v___x_2640_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
lean_ctor_set_uint8(v___x_2640_, 0, v_hasTrace_2514_);
v___y_2544_ = v___x_2619_;
v___y_2545_ = v_a_2616_;
v_a_2546_ = v___x_2640_;
goto v___jp_2543_;
}
}
}
else
{
lean_object* v_a_2642_; 
lean_del_object(v___x_2624_);
v_a_2642_ = lean_ctor_get(v___x_2629_, 0);
lean_inc(v_a_2642_);
lean_dec_ref_known(v___x_2629_, 1);
v___y_2539_ = v___x_2619_;
v___y_2540_ = v_a_2616_;
v_a_2541_ = v_a_2642_;
goto v___jp_2538_;
}
}
}
else
{
lean_object* v_e_x27_2644_; lean_object* v_proof_2645_; uint8_t v_contextDependent_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2719_; 
v_e_x27_2644_ = lean_ctor_get(v_a_2621_, 0);
v_proof_2645_ = lean_ctor_get(v_a_2621_, 1);
v_contextDependent_2646_ = lean_ctor_get_uint8(v_a_2621_, sizeof(void*)*2 + 1);
v_isSharedCheck_2719_ = !lean_is_exclusive(v_a_2621_);
if (v_isSharedCheck_2719_ == 0)
{
v___x_2648_ = v_a_2621_;
v_isShared_2649_ = v_isSharedCheck_2719_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_proof_2645_);
lean_inc(v_e_x27_2644_);
lean_dec(v_a_2621_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2719_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v___x_2650_; 
lean_inc_ref(v_e_x27_2644_);
v___x_2650_ = l_Lean_Meta_Sym_inferType(v_e_x27_2644_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
if (lean_obj_tag(v___x_2650_) == 0)
{
lean_object* v_a_2651_; lean_object* v___x_2652_; uint8_t v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; 
v_a_2651_ = lean_ctor_get(v___x_2650_, 0);
lean_inc(v_a_2651_);
lean_dec_ref_known(v___x_2650_, 1);
v___x_2652_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__1));
v___x_2653_ = 0;
v___x_2654_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2);
lean_inc(v_idx_2266_);
lean_inc(v_typeName_2265_);
v___x_2655_ = l_Lean_Expr_proj___override(v_typeName_2265_, v_idx_2266_, v___x_2654_);
v___x_2656_ = l_Lean_mkLambda(v___x_2652_, v___x_2653_, v_a_2651_, v___x_2655_);
lean_inc_ref(v___x_2656_);
v___x_2657_ = l_Lean_Meta_Sym_inferType(v___x_2656_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
if (lean_obj_tag(v___x_2657_) == 0)
{
lean_object* v_a_2658_; uint8_t v___x_2659_; 
v_a_2658_ = lean_ctor_get(v___x_2657_, 0);
lean_inc(v_a_2658_);
lean_dec_ref_known(v___x_2657_, 1);
v___x_2659_ = l_Lean_Expr_isArrow(v_a_2658_);
if (v___x_2659_ == 0)
{
uint8_t v___x_2660_; lean_object* v___x_2661_; lean_object* v___f_2662_; lean_object* v___x_2663_; 
lean_dec(v_a_2658_);
v___x_2660_ = 1;
v___x_2661_ = lean_box(v___x_2660_);
lean_inc_ref(v_e_2240_);
v___f_2662_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2662_, 0, v___x_2661_);
lean_closure_set(v___f_2662_, 1, v_e_2240_);
v___x_2663_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___f_2662_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
if (lean_obj_tag(v___x_2663_) == 0)
{
lean_object* v_a_2664_; 
v_a_2664_ = lean_ctor_get(v___x_2663_, 0);
lean_inc(v_a_2664_);
lean_dec_ref_known(v___x_2663_, 1);
if (lean_obj_tag(v_a_2664_) == 0)
{
lean_object* v___x_2665_; 
lean_del_object(v___x_2648_);
lean_inc_ref(v_e_x27_2644_);
lean_inc_ref(v_struct_2267_);
v___x_2665_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_struct_2267_, v_e_x27_2644_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
if (lean_obj_tag(v___x_2665_) == 0)
{
lean_object* v_a_2666_; uint8_t v___x_2667_; 
v_a_2666_ = lean_ctor_get(v___x_2665_, 0);
lean_inc(v_a_2666_);
lean_dec_ref_known(v___x_2665_, 1);
v___x_2667_ = lean_unbox(v_a_2666_);
lean_dec(v_a_2666_);
if (v___x_2667_ == 0)
{
lean_object* v___x_2668_; 
lean_dec_ref(v___x_2656_);
lean_dec_ref(v_proof_2645_);
lean_dec_ref(v_e_x27_2644_);
lean_dec_ref_known(v_e_2240_, 3);
v___x_2668_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2668_, 0, v_hasTrace_2514_);
lean_ctor_set_uint8(v___x_2668_, 1, v_contextDependent_2646_);
v___y_2544_ = v___x_2619_;
v___y_2545_ = v_a_2616_;
v_a_2546_ = v___x_2668_;
goto v___jp_2543_;
}
else
{
lean_object* v___x_2669_; 
v___x_2669_ = l_Lean_Meta_mkHCongr(v___x_2656_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
if (lean_obj_tag(v___x_2669_) == 0)
{
lean_object* v_a_2670_; lean_object* v_proof_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; 
v_a_2670_ = lean_ctor_get(v___x_2669_, 0);
lean_inc(v_a_2670_);
lean_dec_ref_known(v___x_2669_, 1);
v_proof_2671_ = lean_ctor_get(v_a_2670_, 1);
lean_inc_ref(v_proof_2671_);
lean_dec(v_a_2670_);
lean_inc_ref(v_e_x27_2644_);
lean_inc_ref(v_struct_2267_);
v___x_2672_ = l_Lean_mkApp3(v_proof_2671_, v_struct_2267_, v_e_x27_2644_, v_proof_2645_);
v___x_2673_ = l_Lean_Meta_mkEqOfHEq(v___x_2672_, v___x_2618_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
if (lean_obj_tag(v___x_2673_) == 0)
{
lean_object* v_a_2674_; size_t v___x_2675_; size_t v___x_2676_; uint8_t v___x_2677_; 
v_a_2674_ = lean_ctor_get(v___x_2673_, 0);
lean_inc(v_a_2674_);
lean_dec_ref_known(v___x_2673_, 1);
v___x_2675_ = lean_ptr_addr(v_struct_2267_);
v___x_2676_ = lean_ptr_addr(v_e_x27_2644_);
v___x_2677_ = lean_usize_dec_eq(v___x_2675_, v___x_2676_);
if (v___x_2677_ == 0)
{
lean_object* v___x_2678_; 
lean_inc(v_idx_2266_);
lean_inc(v_typeName_2265_);
lean_dec_ref_known(v_e_2240_, 3);
v___x_2678_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_typeName_2265_, v_idx_2266_, v_e_x27_2644_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
if (lean_obj_tag(v___x_2678_) == 0)
{
lean_object* v_a_2679_; 
v_a_2679_ = lean_ctor_get(v___x_2678_, 0);
lean_inc(v_a_2679_);
lean_dec_ref_known(v___x_2678_, 1);
v___y_2549_ = v___x_2619_;
v___y_2550_ = v_contextDependent_2646_;
v___y_2551_ = v_a_2674_;
v___y_2552_ = v_a_2616_;
v___y_2553_ = v___x_2618_;
v_a_2554_ = v_a_2679_;
goto v___jp_2548_;
}
else
{
lean_object* v_a_2680_; 
lean_dec(v_a_2674_);
v_a_2680_ = lean_ctor_get(v___x_2678_, 0);
lean_inc(v_a_2680_);
lean_dec_ref_known(v___x_2678_, 1);
v___y_2539_ = v___x_2619_;
v___y_2540_ = v_a_2616_;
v_a_2541_ = v_a_2680_;
goto v___jp_2538_;
}
}
else
{
lean_dec_ref(v_e_x27_2644_);
v___y_2549_ = v___x_2619_;
v___y_2550_ = v_contextDependent_2646_;
v___y_2551_ = v_a_2674_;
v___y_2552_ = v_a_2616_;
v___y_2553_ = v___x_2618_;
v_a_2554_ = v_e_2240_;
goto v___jp_2548_;
}
}
else
{
lean_object* v_a_2681_; 
lean_dec_ref(v_e_x27_2644_);
lean_dec_ref_known(v_e_2240_, 3);
v_a_2681_ = lean_ctor_get(v___x_2673_, 0);
lean_inc(v_a_2681_);
lean_dec_ref_known(v___x_2673_, 1);
v___y_2539_ = v___x_2619_;
v___y_2540_ = v_a_2616_;
v_a_2541_ = v_a_2681_;
goto v___jp_2538_;
}
}
else
{
lean_object* v_a_2682_; 
lean_dec_ref(v_proof_2645_);
lean_dec_ref(v_e_x27_2644_);
lean_dec_ref_known(v_e_2240_, 3);
v_a_2682_ = lean_ctor_get(v___x_2669_, 0);
lean_inc(v_a_2682_);
lean_dec_ref_known(v___x_2669_, 1);
v___y_2539_ = v___x_2619_;
v___y_2540_ = v_a_2616_;
v_a_2541_ = v_a_2682_;
goto v___jp_2538_;
}
}
}
else
{
lean_object* v_a_2683_; 
lean_dec_ref(v___x_2656_);
lean_dec_ref(v_proof_2645_);
lean_dec_ref(v_e_x27_2644_);
lean_dec_ref_known(v_e_2240_, 3);
v_a_2683_ = lean_ctor_get(v___x_2665_, 0);
lean_inc(v_a_2683_);
lean_dec_ref_known(v___x_2665_, 1);
v___y_2539_ = v___x_2619_;
v___y_2540_ = v_a_2616_;
v_a_2541_ = v_a_2683_;
goto v___jp_2538_;
}
}
else
{
lean_object* v_val_2684_; lean_object* v___x_2685_; 
lean_dec_ref(v___x_2656_);
lean_dec_ref(v_proof_2645_);
lean_dec_ref(v_e_x27_2644_);
lean_dec_ref_known(v_e_2240_, 3);
v_val_2684_ = lean_ctor_get(v_a_2664_, 0);
lean_inc(v_val_2684_);
lean_dec_ref_known(v_a_2664_, 1);
v___x_2685_ = l_Lean_Meta_Sym_shareCommonInc(v_val_2684_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
if (lean_obj_tag(v___x_2685_) == 0)
{
lean_object* v_a_2686_; lean_object* v___x_2687_; 
v_a_2686_ = lean_ctor_get(v___x_2685_, 0);
lean_inc_n(v_a_2686_, 2);
lean_dec_ref_known(v___x_2685_, 1);
v___x_2687_ = l_Lean_Meta_Sym_mkEqRefl(v_a_2686_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
if (lean_obj_tag(v___x_2687_) == 0)
{
lean_object* v_a_2688_; lean_object* v___x_2690_; 
v_a_2688_ = lean_ctor_get(v___x_2687_, 0);
lean_inc(v_a_2688_);
lean_dec_ref_known(v___x_2687_, 1);
if (v_isShared_2649_ == 0)
{
lean_ctor_set(v___x_2648_, 1, v_a_2688_);
lean_ctor_set(v___x_2648_, 0, v_a_2686_);
v___x_2690_ = v___x_2648_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v_a_2686_);
lean_ctor_set(v_reuseFailAlloc_2691_, 1, v_a_2688_);
v___x_2690_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
lean_ctor_set_uint8(v___x_2690_, sizeof(void*)*2, v_contextDependent_2646_);
lean_ctor_set_uint8(v___x_2690_, sizeof(void*)*2 + 1, v___x_2618_);
v___y_2544_ = v___x_2619_;
v___y_2545_ = v_a_2616_;
v_a_2546_ = v___x_2690_;
goto v___jp_2543_;
}
}
else
{
lean_object* v_a_2692_; 
lean_dec(v_a_2686_);
lean_del_object(v___x_2648_);
v_a_2692_ = lean_ctor_get(v___x_2687_, 0);
lean_inc(v_a_2692_);
lean_dec_ref_known(v___x_2687_, 1);
v___y_2539_ = v___x_2619_;
v___y_2540_ = v_a_2616_;
v_a_2541_ = v_a_2692_;
goto v___jp_2538_;
}
}
else
{
lean_object* v_a_2693_; 
lean_del_object(v___x_2648_);
v_a_2693_ = lean_ctor_get(v___x_2685_, 0);
lean_inc(v_a_2693_);
lean_dec_ref_known(v___x_2685_, 1);
v___y_2539_ = v___x_2619_;
v___y_2540_ = v_a_2616_;
v_a_2541_ = v_a_2693_;
goto v___jp_2538_;
}
}
}
else
{
lean_object* v_a_2694_; 
lean_dec_ref(v___x_2656_);
lean_del_object(v___x_2648_);
lean_dec_ref(v_proof_2645_);
lean_dec_ref(v_e_x27_2644_);
lean_dec_ref_known(v_e_2240_, 3);
v_a_2694_ = lean_ctor_get(v___x_2663_, 0);
lean_inc(v_a_2694_);
lean_dec_ref_known(v___x_2663_, 1);
v___y_2539_ = v___x_2619_;
v___y_2540_ = v_a_2616_;
v_a_2541_ = v_a_2694_;
goto v___jp_2538_;
}
}
else
{
lean_del_object(v___x_2648_);
if (lean_obj_tag(v_a_2658_) == 7)
{
lean_object* v_binderType_2695_; lean_object* v_body_2696_; lean_object* v___x_2697_; 
v_binderType_2695_ = lean_ctor_get(v_a_2658_, 1);
lean_inc_ref_n(v_binderType_2695_, 2);
v_body_2696_ = lean_ctor_get(v_a_2658_, 2);
lean_inc_ref(v_body_2696_);
lean_dec_ref_known(v_a_2658_, 3);
v___x_2697_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_2695_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
if (lean_obj_tag(v___x_2697_) == 0)
{
lean_object* v_a_2698_; lean_object* v___x_2699_; 
v_a_2698_ = lean_ctor_get(v___x_2697_, 0);
lean_inc(v_a_2698_);
lean_dec_ref_known(v___x_2697_, 1);
lean_inc_ref(v_body_2696_);
v___x_2699_ = l_Lean_Meta_Sym_getLevel___redArg(v_body_2696_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
if (lean_obj_tag(v___x_2699_) == 0)
{
lean_object* v_a_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; size_t v___x_2707_; size_t v___x_2708_; uint8_t v___x_2709_; 
v_a_2700_ = lean_ctor_get(v___x_2699_, 0);
lean_inc(v_a_2700_);
lean_dec_ref_known(v___x_2699_, 1);
v___x_2701_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4));
v___x_2702_ = lean_box(0);
v___x_2703_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2703_, 0, v_a_2700_);
lean_ctor_set(v___x_2703_, 1, v___x_2702_);
v___x_2704_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2704_, 0, v_a_2698_);
lean_ctor_set(v___x_2704_, 1, v___x_2703_);
v___x_2705_ = l_Lean_mkConst(v___x_2701_, v___x_2704_);
lean_inc_ref(v_e_x27_2644_);
lean_inc_ref(v_struct_2267_);
v___x_2706_ = l_Lean_mkApp6(v___x_2705_, v_binderType_2695_, v_body_2696_, v_struct_2267_, v_e_x27_2644_, v___x_2656_, v_proof_2645_);
v___x_2707_ = lean_ptr_addr(v_struct_2267_);
v___x_2708_ = lean_ptr_addr(v_e_x27_2644_);
v___x_2709_ = lean_usize_dec_eq(v___x_2707_, v___x_2708_);
if (v___x_2709_ == 0)
{
lean_object* v___x_2710_; 
lean_inc(v_idx_2266_);
lean_inc(v_typeName_2265_);
lean_dec_ref_known(v_e_2240_, 3);
v___x_2710_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_typeName_2265_, v_idx_2266_, v_e_x27_2644_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
if (lean_obj_tag(v___x_2710_) == 0)
{
lean_object* v_a_2711_; 
v_a_2711_ = lean_ctor_get(v___x_2710_, 0);
lean_inc(v_a_2711_);
lean_dec_ref_known(v___x_2710_, 1);
v___y_2563_ = v___x_2619_;
v___y_2564_ = v_contextDependent_2646_;
v___y_2565_ = v_a_2616_;
v___y_2566_ = v___x_2706_;
v___y_2567_ = v___x_2618_;
v_a_2568_ = v_a_2711_;
goto v___jp_2562_;
}
else
{
lean_object* v_a_2712_; 
lean_dec_ref(v___x_2706_);
v_a_2712_ = lean_ctor_get(v___x_2710_, 0);
lean_inc(v_a_2712_);
lean_dec_ref_known(v___x_2710_, 1);
v___y_2539_ = v___x_2619_;
v___y_2540_ = v_a_2616_;
v_a_2541_ = v_a_2712_;
goto v___jp_2538_;
}
}
else
{
lean_dec_ref(v_e_x27_2644_);
v___y_2563_ = v___x_2619_;
v___y_2564_ = v_contextDependent_2646_;
v___y_2565_ = v_a_2616_;
v___y_2566_ = v___x_2706_;
v___y_2567_ = v___x_2618_;
v_a_2568_ = v_e_2240_;
goto v___jp_2562_;
}
}
else
{
lean_object* v_a_2713_; 
lean_dec(v_a_2698_);
lean_dec_ref(v_body_2696_);
lean_dec_ref(v_binderType_2695_);
lean_dec_ref(v___x_2656_);
lean_dec_ref(v_proof_2645_);
lean_dec_ref(v_e_x27_2644_);
lean_dec_ref_known(v_e_2240_, 3);
v_a_2713_ = lean_ctor_get(v___x_2699_, 0);
lean_inc(v_a_2713_);
lean_dec_ref_known(v___x_2699_, 1);
v___y_2539_ = v___x_2619_;
v___y_2540_ = v_a_2616_;
v_a_2541_ = v_a_2713_;
goto v___jp_2538_;
}
}
else
{
lean_object* v_a_2714_; 
lean_dec_ref(v_body_2696_);
lean_dec_ref(v_binderType_2695_);
lean_dec_ref(v___x_2656_);
lean_dec_ref(v_proof_2645_);
lean_dec_ref(v_e_x27_2644_);
lean_dec_ref_known(v_e_2240_, 3);
v_a_2714_ = lean_ctor_get(v___x_2697_, 0);
lean_inc(v_a_2714_);
lean_dec_ref_known(v___x_2697_, 1);
v___y_2539_ = v___x_2619_;
v___y_2540_ = v_a_2616_;
v_a_2541_ = v_a_2714_;
goto v___jp_2538_;
}
}
else
{
lean_object* v___x_2715_; lean_object* v___x_2716_; 
lean_dec(v_a_2658_);
lean_dec_ref(v___x_2656_);
lean_dec_ref(v_proof_2645_);
lean_dec_ref(v_e_x27_2644_);
lean_dec_ref_known(v_e_2240_, 3);
v___x_2715_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8);
v___x_2716_ = l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1(v___x_2715_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
v___y_2557_ = v___x_2619_;
v___y_2558_ = v_a_2616_;
v___y_2559_ = v___x_2716_;
goto v___jp_2556_;
}
}
}
else
{
lean_object* v_a_2717_; 
lean_dec_ref(v___x_2656_);
lean_del_object(v___x_2648_);
lean_dec_ref(v_proof_2645_);
lean_dec_ref(v_e_x27_2644_);
lean_dec_ref_known(v_e_2240_, 3);
v_a_2717_ = lean_ctor_get(v___x_2657_, 0);
lean_inc(v_a_2717_);
lean_dec_ref_known(v___x_2657_, 1);
v___y_2539_ = v___x_2619_;
v___y_2540_ = v_a_2616_;
v_a_2541_ = v_a_2717_;
goto v___jp_2538_;
}
}
else
{
lean_object* v_a_2718_; 
lean_del_object(v___x_2648_);
lean_dec_ref(v_proof_2645_);
lean_dec_ref(v_e_x27_2644_);
lean_dec_ref_known(v_e_2240_, 3);
v_a_2718_ = lean_ctor_get(v___x_2650_, 0);
lean_inc(v_a_2718_);
lean_dec_ref_known(v___x_2650_, 1);
v___y_2539_ = v___x_2619_;
v___y_2540_ = v_a_2616_;
v_a_2541_ = v_a_2718_;
goto v___jp_2538_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_2240_, 3);
v___y_2557_ = v___x_2619_;
v___y_2558_ = v_a_2616_;
v___y_2559_ = v___x_2620_;
goto v___jp_2556_;
}
}
else
{
lean_object* v___x_2720_; lean_object* v___x_2721_; 
v___x_2720_ = lean_io_get_num_heartbeats();
lean_inc(v_a_2249_);
lean_inc_ref(v_a_2248_);
lean_inc(v_a_2247_);
lean_inc_ref(v_a_2246_);
lean_inc(v_a_2245_);
lean_inc_ref(v_a_2244_);
lean_inc(v_a_2243_);
lean_inc_ref(v_a_2242_);
lean_inc(v_a_2241_);
lean_inc_ref(v_struct_2267_);
v___x_2721_ = lean_sym_simp(v_struct_2267_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
if (lean_obj_tag(v___x_2721_) == 0)
{
lean_object* v_a_2722_; 
v_a_2722_ = lean_ctor_get(v___x_2721_, 0);
lean_inc(v_a_2722_);
lean_dec_ref_known(v___x_2721_, 1);
if (lean_obj_tag(v_a_2722_) == 0)
{
uint8_t v_contextDependent_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2745_; 
v_contextDependent_2723_ = lean_ctor_get_uint8(v_a_2722_, 1);
v_isSharedCheck_2745_ = !lean_is_exclusive(v_a_2722_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2725_ = v_a_2722_;
v_isShared_2726_ = v_isSharedCheck_2745_;
goto v_resetjp_2724_;
}
else
{
lean_dec(v_a_2722_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2745_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
uint8_t v___x_2727_; lean_object* v___x_2728_; lean_object* v___f_2729_; lean_object* v___x_2730_; 
v___x_2727_ = 1;
v___x_2728_ = lean_box(v___x_2727_);
v___f_2729_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2729_, 0, v___x_2728_);
lean_closure_set(v___f_2729_, 1, v_e_2240_);
v___x_2730_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___f_2729_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
if (lean_obj_tag(v___x_2730_) == 0)
{
lean_object* v_a_2731_; 
v_a_2731_ = lean_ctor_get(v___x_2730_, 0);
lean_inc(v_a_2731_);
lean_dec_ref_known(v___x_2730_, 1);
if (lean_obj_tag(v_a_2731_) == 1)
{
lean_object* v_val_2732_; lean_object* v___x_2733_; 
lean_del_object(v___x_2725_);
v_val_2732_ = lean_ctor_get(v_a_2731_, 0);
lean_inc(v_val_2732_);
lean_dec_ref_known(v_a_2731_, 1);
v___x_2733_ = l_Lean_Meta_Sym_shareCommonInc(v_val_2732_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
if (lean_obj_tag(v___x_2733_) == 0)
{
lean_object* v_a_2734_; lean_object* v___x_2735_; 
v_a_2734_ = lean_ctor_get(v___x_2733_, 0);
lean_inc_n(v_a_2734_, 2);
lean_dec_ref_known(v___x_2733_, 1);
v___x_2735_ = l_Lean_Meta_Sym_mkEqRefl(v_a_2734_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
if (lean_obj_tag(v___x_2735_) == 0)
{
lean_object* v_a_2736_; uint8_t v___x_2737_; lean_object* v___x_2738_; 
v_a_2736_ = lean_ctor_get(v___x_2735_, 0);
lean_inc(v_a_2736_);
lean_dec_ref_known(v___x_2735_, 1);
v___x_2737_ = 0;
v___x_2738_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2738_, 0, v_a_2734_);
lean_ctor_set(v___x_2738_, 1, v_a_2736_);
lean_ctor_set_uint8(v___x_2738_, sizeof(void*)*2, v_contextDependent_2723_);
lean_ctor_set_uint8(v___x_2738_, sizeof(void*)*2 + 1, v___x_2737_);
v___y_2588_ = v___x_2720_;
v___y_2589_ = v_a_2616_;
v_a_2590_ = v___x_2738_;
goto v___jp_2587_;
}
else
{
lean_object* v_a_2739_; 
lean_dec(v_a_2734_);
v_a_2739_ = lean_ctor_get(v___x_2735_, 0);
lean_inc(v_a_2739_);
lean_dec_ref_known(v___x_2735_, 1);
v___y_2583_ = v___x_2720_;
v___y_2584_ = v_a_2616_;
v_a_2585_ = v_a_2739_;
goto v___jp_2582_;
}
}
else
{
lean_object* v_a_2740_; 
v_a_2740_ = lean_ctor_get(v___x_2733_, 0);
lean_inc(v_a_2740_);
lean_dec_ref_known(v___x_2733_, 1);
v___y_2583_ = v___x_2720_;
v___y_2584_ = v_a_2616_;
v_a_2585_ = v_a_2740_;
goto v___jp_2582_;
}
}
else
{
lean_object* v___x_2742_; 
lean_dec(v_a_2731_);
if (v_isShared_2726_ == 0)
{
v___x_2742_ = v___x_2725_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v_reuseFailAlloc_2743_, 1, v_contextDependent_2723_);
v___x_2742_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
lean_ctor_set_uint8(v___x_2742_, 0, v___x_2618_);
v___y_2588_ = v___x_2720_;
v___y_2589_ = v_a_2616_;
v_a_2590_ = v___x_2742_;
goto v___jp_2587_;
}
}
}
else
{
lean_object* v_a_2744_; 
lean_del_object(v___x_2725_);
v_a_2744_ = lean_ctor_get(v___x_2730_, 0);
lean_inc(v_a_2744_);
lean_dec_ref_known(v___x_2730_, 1);
v___y_2583_ = v___x_2720_;
v___y_2584_ = v_a_2616_;
v_a_2585_ = v_a_2744_;
goto v___jp_2582_;
}
}
}
else
{
lean_object* v_e_x27_2746_; lean_object* v_proof_2747_; uint8_t v_contextDependent_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2821_; 
v_e_x27_2746_ = lean_ctor_get(v_a_2722_, 0);
v_proof_2747_ = lean_ctor_get(v_a_2722_, 1);
v_contextDependent_2748_ = lean_ctor_get_uint8(v_a_2722_, sizeof(void*)*2 + 1);
v_isSharedCheck_2821_ = !lean_is_exclusive(v_a_2722_);
if (v_isSharedCheck_2821_ == 0)
{
v___x_2750_ = v_a_2722_;
v_isShared_2751_ = v_isSharedCheck_2821_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_proof_2747_);
lean_inc(v_e_x27_2746_);
lean_dec(v_a_2722_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2821_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
lean_object* v___x_2752_; 
lean_inc_ref(v_e_x27_2746_);
v___x_2752_ = l_Lean_Meta_Sym_inferType(v_e_x27_2746_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
if (lean_obj_tag(v___x_2752_) == 0)
{
lean_object* v_a_2753_; lean_object* v___x_2754_; uint8_t v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; 
v_a_2753_ = lean_ctor_get(v___x_2752_, 0);
lean_inc(v_a_2753_);
lean_dec_ref_known(v___x_2752_, 1);
v___x_2754_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__1));
v___x_2755_ = 0;
v___x_2756_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2);
lean_inc(v_idx_2266_);
lean_inc(v_typeName_2265_);
v___x_2757_ = l_Lean_Expr_proj___override(v_typeName_2265_, v_idx_2266_, v___x_2756_);
v___x_2758_ = l_Lean_mkLambda(v___x_2754_, v___x_2755_, v_a_2753_, v___x_2757_);
lean_inc_ref(v___x_2758_);
v___x_2759_ = l_Lean_Meta_Sym_inferType(v___x_2758_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
if (lean_obj_tag(v___x_2759_) == 0)
{
lean_object* v_a_2760_; uint8_t v___x_2761_; 
v_a_2760_ = lean_ctor_get(v___x_2759_, 0);
lean_inc(v_a_2760_);
lean_dec_ref_known(v___x_2759_, 1);
v___x_2761_ = l_Lean_Expr_isArrow(v_a_2760_);
if (v___x_2761_ == 0)
{
uint8_t v___x_2762_; lean_object* v___x_2763_; lean_object* v___f_2764_; lean_object* v___x_2765_; 
lean_dec(v_a_2760_);
v___x_2762_ = 1;
v___x_2763_ = lean_box(v___x_2762_);
lean_inc_ref(v_e_2240_);
v___f_2764_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2764_, 0, v___x_2763_);
lean_closure_set(v___f_2764_, 1, v_e_2240_);
v___x_2765_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___f_2764_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
if (lean_obj_tag(v___x_2765_) == 0)
{
lean_object* v_a_2766_; 
v_a_2766_ = lean_ctor_get(v___x_2765_, 0);
lean_inc(v_a_2766_);
lean_dec_ref_known(v___x_2765_, 1);
if (lean_obj_tag(v_a_2766_) == 0)
{
lean_object* v___x_2767_; 
lean_del_object(v___x_2750_);
lean_inc_ref(v_e_x27_2746_);
lean_inc_ref(v_struct_2267_);
v___x_2767_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_struct_2267_, v_e_x27_2746_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
if (lean_obj_tag(v___x_2767_) == 0)
{
lean_object* v_a_2768_; uint8_t v___x_2769_; 
v_a_2768_ = lean_ctor_get(v___x_2767_, 0);
lean_inc(v_a_2768_);
lean_dec_ref_known(v___x_2767_, 1);
v___x_2769_ = lean_unbox(v_a_2768_);
lean_dec(v_a_2768_);
if (v___x_2769_ == 0)
{
lean_object* v___x_2770_; 
lean_dec_ref(v___x_2758_);
lean_dec_ref(v_proof_2747_);
lean_dec_ref(v_e_x27_2746_);
lean_dec_ref_known(v_e_2240_, 3);
v___x_2770_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2770_, 0, v___x_2618_);
lean_ctor_set_uint8(v___x_2770_, 1, v_contextDependent_2748_);
v___y_2588_ = v___x_2720_;
v___y_2589_ = v_a_2616_;
v_a_2590_ = v___x_2770_;
goto v___jp_2587_;
}
else
{
lean_object* v___x_2771_; 
v___x_2771_ = l_Lean_Meta_mkHCongr(v___x_2758_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
if (lean_obj_tag(v___x_2771_) == 0)
{
lean_object* v_a_2772_; lean_object* v_proof_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; 
v_a_2772_ = lean_ctor_get(v___x_2771_, 0);
lean_inc(v_a_2772_);
lean_dec_ref_known(v___x_2771_, 1);
v_proof_2773_ = lean_ctor_get(v_a_2772_, 1);
lean_inc_ref(v_proof_2773_);
lean_dec(v_a_2772_);
lean_inc_ref(v_e_x27_2746_);
lean_inc_ref(v_struct_2267_);
v___x_2774_ = l_Lean_mkApp3(v_proof_2773_, v_struct_2267_, v_e_x27_2746_, v_proof_2747_);
v___x_2775_ = l_Lean_Meta_mkEqOfHEq(v___x_2774_, v___x_2761_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
if (lean_obj_tag(v___x_2775_) == 0)
{
lean_object* v_a_2776_; size_t v___x_2777_; size_t v___x_2778_; uint8_t v___x_2779_; 
v_a_2776_ = lean_ctor_get(v___x_2775_, 0);
lean_inc(v_a_2776_);
lean_dec_ref_known(v___x_2775_, 1);
v___x_2777_ = lean_ptr_addr(v_struct_2267_);
v___x_2778_ = lean_ptr_addr(v_e_x27_2746_);
v___x_2779_ = lean_usize_dec_eq(v___x_2777_, v___x_2778_);
if (v___x_2779_ == 0)
{
lean_object* v___x_2780_; 
lean_inc(v_idx_2266_);
lean_inc(v_typeName_2265_);
lean_dec_ref_known(v_e_2240_, 3);
v___x_2780_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_typeName_2265_, v_idx_2266_, v_e_x27_2746_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
if (lean_obj_tag(v___x_2780_) == 0)
{
lean_object* v_a_2781_; 
v_a_2781_ = lean_ctor_get(v___x_2780_, 0);
lean_inc(v_a_2781_);
lean_dec_ref_known(v___x_2780_, 1);
v___y_2593_ = v___x_2720_;
v___y_2594_ = v___x_2761_;
v___y_2595_ = v_contextDependent_2748_;
v___y_2596_ = v_a_2616_;
v___y_2597_ = v_a_2776_;
v_a_2598_ = v_a_2781_;
goto v___jp_2592_;
}
else
{
lean_object* v_a_2782_; 
lean_dec(v_a_2776_);
v_a_2782_ = lean_ctor_get(v___x_2780_, 0);
lean_inc(v_a_2782_);
lean_dec_ref_known(v___x_2780_, 1);
v___y_2583_ = v___x_2720_;
v___y_2584_ = v_a_2616_;
v_a_2585_ = v_a_2782_;
goto v___jp_2582_;
}
}
else
{
lean_dec_ref(v_e_x27_2746_);
v___y_2593_ = v___x_2720_;
v___y_2594_ = v___x_2761_;
v___y_2595_ = v_contextDependent_2748_;
v___y_2596_ = v_a_2616_;
v___y_2597_ = v_a_2776_;
v_a_2598_ = v_e_2240_;
goto v___jp_2592_;
}
}
else
{
lean_object* v_a_2783_; 
lean_dec_ref(v_e_x27_2746_);
lean_dec_ref_known(v_e_2240_, 3);
v_a_2783_ = lean_ctor_get(v___x_2775_, 0);
lean_inc(v_a_2783_);
lean_dec_ref_known(v___x_2775_, 1);
v___y_2583_ = v___x_2720_;
v___y_2584_ = v_a_2616_;
v_a_2585_ = v_a_2783_;
goto v___jp_2582_;
}
}
else
{
lean_object* v_a_2784_; 
lean_dec_ref(v_proof_2747_);
lean_dec_ref(v_e_x27_2746_);
lean_dec_ref_known(v_e_2240_, 3);
v_a_2784_ = lean_ctor_get(v___x_2771_, 0);
lean_inc(v_a_2784_);
lean_dec_ref_known(v___x_2771_, 1);
v___y_2583_ = v___x_2720_;
v___y_2584_ = v_a_2616_;
v_a_2585_ = v_a_2784_;
goto v___jp_2582_;
}
}
}
else
{
lean_object* v_a_2785_; 
lean_dec_ref(v___x_2758_);
lean_dec_ref(v_proof_2747_);
lean_dec_ref(v_e_x27_2746_);
lean_dec_ref_known(v_e_2240_, 3);
v_a_2785_ = lean_ctor_get(v___x_2767_, 0);
lean_inc(v_a_2785_);
lean_dec_ref_known(v___x_2767_, 1);
v___y_2583_ = v___x_2720_;
v___y_2584_ = v_a_2616_;
v_a_2585_ = v_a_2785_;
goto v___jp_2582_;
}
}
else
{
lean_object* v_val_2786_; lean_object* v___x_2787_; 
lean_dec_ref(v___x_2758_);
lean_dec_ref(v_proof_2747_);
lean_dec_ref(v_e_x27_2746_);
lean_dec_ref_known(v_e_2240_, 3);
v_val_2786_ = lean_ctor_get(v_a_2766_, 0);
lean_inc(v_val_2786_);
lean_dec_ref_known(v_a_2766_, 1);
v___x_2787_ = l_Lean_Meta_Sym_shareCommonInc(v_val_2786_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
if (lean_obj_tag(v___x_2787_) == 0)
{
lean_object* v_a_2788_; lean_object* v___x_2789_; 
v_a_2788_ = lean_ctor_get(v___x_2787_, 0);
lean_inc_n(v_a_2788_, 2);
lean_dec_ref_known(v___x_2787_, 1);
v___x_2789_ = l_Lean_Meta_Sym_mkEqRefl(v_a_2788_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
if (lean_obj_tag(v___x_2789_) == 0)
{
lean_object* v_a_2790_; lean_object* v___x_2792_; 
v_a_2790_ = lean_ctor_get(v___x_2789_, 0);
lean_inc(v_a_2790_);
lean_dec_ref_known(v___x_2789_, 1);
if (v_isShared_2751_ == 0)
{
lean_ctor_set(v___x_2750_, 1, v_a_2790_);
lean_ctor_set(v___x_2750_, 0, v_a_2788_);
v___x_2792_ = v___x_2750_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v_a_2788_);
lean_ctor_set(v_reuseFailAlloc_2793_, 1, v_a_2790_);
v___x_2792_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
lean_ctor_set_uint8(v___x_2792_, sizeof(void*)*2, v_contextDependent_2748_);
lean_ctor_set_uint8(v___x_2792_, sizeof(void*)*2 + 1, v___x_2761_);
v___y_2588_ = v___x_2720_;
v___y_2589_ = v_a_2616_;
v_a_2590_ = v___x_2792_;
goto v___jp_2587_;
}
}
else
{
lean_object* v_a_2794_; 
lean_dec(v_a_2788_);
lean_del_object(v___x_2750_);
v_a_2794_ = lean_ctor_get(v___x_2789_, 0);
lean_inc(v_a_2794_);
lean_dec_ref_known(v___x_2789_, 1);
v___y_2583_ = v___x_2720_;
v___y_2584_ = v_a_2616_;
v_a_2585_ = v_a_2794_;
goto v___jp_2582_;
}
}
else
{
lean_object* v_a_2795_; 
lean_del_object(v___x_2750_);
v_a_2795_ = lean_ctor_get(v___x_2787_, 0);
lean_inc(v_a_2795_);
lean_dec_ref_known(v___x_2787_, 1);
v___y_2583_ = v___x_2720_;
v___y_2584_ = v_a_2616_;
v_a_2585_ = v_a_2795_;
goto v___jp_2582_;
}
}
}
else
{
lean_object* v_a_2796_; 
lean_dec_ref(v___x_2758_);
lean_del_object(v___x_2750_);
lean_dec_ref(v_proof_2747_);
lean_dec_ref(v_e_x27_2746_);
lean_dec_ref_known(v_e_2240_, 3);
v_a_2796_ = lean_ctor_get(v___x_2765_, 0);
lean_inc(v_a_2796_);
lean_dec_ref_known(v___x_2765_, 1);
v___y_2583_ = v___x_2720_;
v___y_2584_ = v_a_2616_;
v_a_2585_ = v_a_2796_;
goto v___jp_2582_;
}
}
else
{
lean_del_object(v___x_2750_);
if (lean_obj_tag(v_a_2760_) == 7)
{
lean_object* v_binderType_2797_; lean_object* v_body_2798_; lean_object* v___x_2799_; 
v_binderType_2797_ = lean_ctor_get(v_a_2760_, 1);
lean_inc_ref_n(v_binderType_2797_, 2);
v_body_2798_ = lean_ctor_get(v_a_2760_, 2);
lean_inc_ref(v_body_2798_);
lean_dec_ref_known(v_a_2760_, 3);
v___x_2799_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_2797_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
if (lean_obj_tag(v___x_2799_) == 0)
{
lean_object* v_a_2800_; lean_object* v___x_2801_; 
v_a_2800_ = lean_ctor_get(v___x_2799_, 0);
lean_inc(v_a_2800_);
lean_dec_ref_known(v___x_2799_, 1);
lean_inc_ref(v_body_2798_);
v___x_2801_ = l_Lean_Meta_Sym_getLevel___redArg(v_body_2798_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
if (lean_obj_tag(v___x_2801_) == 0)
{
lean_object* v_a_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; size_t v___x_2809_; size_t v___x_2810_; uint8_t v___x_2811_; 
v_a_2802_ = lean_ctor_get(v___x_2801_, 0);
lean_inc(v_a_2802_);
lean_dec_ref_known(v___x_2801_, 1);
v___x_2803_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4));
v___x_2804_ = lean_box(0);
v___x_2805_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2805_, 0, v_a_2802_);
lean_ctor_set(v___x_2805_, 1, v___x_2804_);
v___x_2806_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2806_, 0, v_a_2800_);
lean_ctor_set(v___x_2806_, 1, v___x_2805_);
v___x_2807_ = l_Lean_mkConst(v___x_2803_, v___x_2806_);
lean_inc_ref(v_e_x27_2746_);
lean_inc_ref(v_struct_2267_);
v___x_2808_ = l_Lean_mkApp6(v___x_2807_, v_binderType_2797_, v_body_2798_, v_struct_2267_, v_e_x27_2746_, v___x_2758_, v_proof_2747_);
v___x_2809_ = lean_ptr_addr(v_struct_2267_);
v___x_2810_ = lean_ptr_addr(v_e_x27_2746_);
v___x_2811_ = lean_usize_dec_eq(v___x_2809_, v___x_2810_);
if (v___x_2811_ == 0)
{
lean_object* v___x_2812_; 
lean_inc(v_idx_2266_);
lean_inc(v_typeName_2265_);
lean_dec_ref_known(v_e_2240_, 3);
v___x_2812_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_typeName_2265_, v_idx_2266_, v_e_x27_2746_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_object* v_a_2813_; 
v_a_2813_ = lean_ctor_get(v___x_2812_, 0);
lean_inc(v_a_2813_);
lean_dec_ref_known(v___x_2812_, 1);
v___y_2607_ = v___x_2720_;
v___y_2608_ = v_contextDependent_2748_;
v___y_2609_ = v___x_2808_;
v___y_2610_ = v_a_2616_;
v_a_2611_ = v_a_2813_;
goto v___jp_2606_;
}
else
{
lean_object* v_a_2814_; 
lean_dec_ref(v___x_2808_);
v_a_2814_ = lean_ctor_get(v___x_2812_, 0);
lean_inc(v_a_2814_);
lean_dec_ref_known(v___x_2812_, 1);
v___y_2583_ = v___x_2720_;
v___y_2584_ = v_a_2616_;
v_a_2585_ = v_a_2814_;
goto v___jp_2582_;
}
}
else
{
lean_dec_ref(v_e_x27_2746_);
v___y_2607_ = v___x_2720_;
v___y_2608_ = v_contextDependent_2748_;
v___y_2609_ = v___x_2808_;
v___y_2610_ = v_a_2616_;
v_a_2611_ = v_e_2240_;
goto v___jp_2606_;
}
}
else
{
lean_object* v_a_2815_; 
lean_dec(v_a_2800_);
lean_dec_ref(v_body_2798_);
lean_dec_ref(v_binderType_2797_);
lean_dec_ref(v___x_2758_);
lean_dec_ref(v_proof_2747_);
lean_dec_ref(v_e_x27_2746_);
lean_dec_ref_known(v_e_2240_, 3);
v_a_2815_ = lean_ctor_get(v___x_2801_, 0);
lean_inc(v_a_2815_);
lean_dec_ref_known(v___x_2801_, 1);
v___y_2583_ = v___x_2720_;
v___y_2584_ = v_a_2616_;
v_a_2585_ = v_a_2815_;
goto v___jp_2582_;
}
}
else
{
lean_object* v_a_2816_; 
lean_dec_ref(v_body_2798_);
lean_dec_ref(v_binderType_2797_);
lean_dec_ref(v___x_2758_);
lean_dec_ref(v_proof_2747_);
lean_dec_ref(v_e_x27_2746_);
lean_dec_ref_known(v_e_2240_, 3);
v_a_2816_ = lean_ctor_get(v___x_2799_, 0);
lean_inc(v_a_2816_);
lean_dec_ref_known(v___x_2799_, 1);
v___y_2583_ = v___x_2720_;
v___y_2584_ = v_a_2616_;
v_a_2585_ = v_a_2816_;
goto v___jp_2582_;
}
}
else
{
lean_object* v___x_2817_; lean_object* v___x_2818_; 
lean_dec(v_a_2760_);
lean_dec_ref(v___x_2758_);
lean_dec_ref(v_proof_2747_);
lean_dec_ref(v_e_x27_2746_);
lean_dec_ref_known(v_e_2240_, 3);
v___x_2817_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8);
v___x_2818_ = l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1(v___x_2817_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
v___y_2601_ = v___x_2720_;
v___y_2602_ = v_a_2616_;
v___y_2603_ = v___x_2818_;
goto v___jp_2600_;
}
}
}
else
{
lean_object* v_a_2819_; 
lean_dec_ref(v___x_2758_);
lean_del_object(v___x_2750_);
lean_dec_ref(v_proof_2747_);
lean_dec_ref(v_e_x27_2746_);
lean_dec_ref_known(v_e_2240_, 3);
v_a_2819_ = lean_ctor_get(v___x_2759_, 0);
lean_inc(v_a_2819_);
lean_dec_ref_known(v___x_2759_, 1);
v___y_2583_ = v___x_2720_;
v___y_2584_ = v_a_2616_;
v_a_2585_ = v_a_2819_;
goto v___jp_2582_;
}
}
else
{
lean_object* v_a_2820_; 
lean_del_object(v___x_2750_);
lean_dec_ref(v_proof_2747_);
lean_dec_ref(v_e_x27_2746_);
lean_dec_ref_known(v_e_2240_, 3);
v_a_2820_ = lean_ctor_get(v___x_2752_, 0);
lean_inc(v_a_2820_);
lean_dec_ref_known(v___x_2752_, 1);
v___y_2583_ = v___x_2720_;
v___y_2584_ = v_a_2616_;
v_a_2585_ = v_a_2820_;
goto v___jp_2582_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_2240_, 3);
v___y_2601_ = v___x_2720_;
v___y_2602_ = v_a_2616_;
v___y_2603_ = v___x_2721_;
goto v___jp_2600_;
}
}
}
}
v___jp_2268_:
{
if (lean_obj_tag(v_res_2269_) == 0)
{
uint8_t v_contextDependent_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2337_; 
v_contextDependent_2279_ = lean_ctor_get_uint8(v_res_2269_, 1);
v_isSharedCheck_2337_ = !lean_is_exclusive(v_res_2269_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2281_ = v_res_2269_;
v_isShared_2282_ = v_isSharedCheck_2337_;
goto v_resetjp_2280_;
}
else
{
lean_dec(v_res_2269_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2337_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
uint8_t v___x_2283_; lean_object* v___x_2284_; lean_object* v___f_2285_; lean_object* v___x_2286_; 
v___x_2283_ = 1;
v___x_2284_ = lean_box(v___x_2283_);
v___f_2285_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2285_, 0, v___x_2284_);
lean_closure_set(v___f_2285_, 1, v_e_2240_);
v___x_2286_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___f_2285_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
if (lean_obj_tag(v___x_2286_) == 0)
{
lean_object* v_a_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2328_; 
v_a_2287_ = lean_ctor_get(v___x_2286_, 0);
v_isSharedCheck_2328_ = !lean_is_exclusive(v___x_2286_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2289_ = v___x_2286_;
v_isShared_2290_ = v_isSharedCheck_2328_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_a_2287_);
lean_dec(v___x_2286_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2328_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
if (lean_obj_tag(v_a_2287_) == 1)
{
lean_object* v_val_2291_; lean_object* v___x_2292_; 
lean_del_object(v___x_2289_);
lean_del_object(v___x_2281_);
v_val_2291_ = lean_ctor_get(v_a_2287_, 0);
lean_inc(v_val_2291_);
lean_dec_ref_known(v_a_2287_, 1);
v___x_2292_ = l_Lean_Meta_Sym_shareCommonInc(v_val_2291_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
if (lean_obj_tag(v___x_2292_) == 0)
{
lean_object* v_a_2293_; lean_object* v___x_2294_; 
v_a_2293_ = lean_ctor_get(v___x_2292_, 0);
lean_inc_n(v_a_2293_, 2);
lean_dec_ref_known(v___x_2292_, 1);
v___x_2294_ = l_Lean_Meta_Sym_mkEqRefl(v_a_2293_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_object* v_a_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2304_; 
v_a_2295_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2304_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2304_ == 0)
{
v___x_2297_ = v___x_2294_;
v_isShared_2298_ = v_isSharedCheck_2304_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_a_2295_);
lean_dec(v___x_2294_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2304_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
uint8_t v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2302_; 
v___x_2299_ = 0;
v___x_2300_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2300_, 0, v_a_2293_);
lean_ctor_set(v___x_2300_, 1, v_a_2295_);
lean_ctor_set_uint8(v___x_2300_, sizeof(void*)*2, v_contextDependent_2279_);
lean_ctor_set_uint8(v___x_2300_, sizeof(void*)*2 + 1, v___x_2299_);
if (v_isShared_2298_ == 0)
{
lean_ctor_set(v___x_2297_, 0, v___x_2300_);
v___x_2302_ = v___x_2297_;
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
else
{
lean_object* v_a_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2312_; 
lean_dec(v_a_2293_);
v_a_2305_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2307_ = v___x_2294_;
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_a_2305_);
lean_dec(v___x_2294_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v___x_2310_; 
if (v_isShared_2308_ == 0)
{
v___x_2310_ = v___x_2307_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_a_2305_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
return v___x_2310_;
}
}
}
}
else
{
lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2320_; 
v_a_2313_ = lean_ctor_get(v___x_2292_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2292_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2315_ = v___x_2292_;
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v___x_2292_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2318_; 
if (v_isShared_2316_ == 0)
{
v___x_2318_ = v___x_2315_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_a_2313_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
}
}
else
{
uint8_t v___x_2321_; lean_object* v___x_2323_; 
lean_dec(v_a_2287_);
v___x_2321_ = 1;
if (v_isShared_2282_ == 0)
{
v___x_2323_ = v___x_2281_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v_reuseFailAlloc_2327_, 1, v_contextDependent_2279_);
v___x_2323_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
lean_object* v___x_2325_; 
lean_ctor_set_uint8(v___x_2323_, 0, v___x_2321_);
if (v_isShared_2290_ == 0)
{
lean_ctor_set(v___x_2289_, 0, v___x_2323_);
v___x_2325_ = v___x_2289_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v___x_2323_);
v___x_2325_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
return v___x_2325_;
}
}
}
}
}
else
{
lean_object* v_a_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2336_; 
lean_del_object(v___x_2281_);
v_a_2329_ = lean_ctor_get(v___x_2286_, 0);
v_isSharedCheck_2336_ = !lean_is_exclusive(v___x_2286_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2331_ = v___x_2286_;
v_isShared_2332_ = v_isSharedCheck_2336_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_a_2329_);
lean_dec(v___x_2286_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2336_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v___x_2334_; 
if (v_isShared_2332_ == 0)
{
v___x_2334_ = v___x_2331_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v_a_2329_);
v___x_2334_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
return v___x_2334_;
}
}
}
}
}
else
{
lean_object* v_e_x27_2338_; lean_object* v_proof_2339_; uint8_t v_contextDependent_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2512_; 
v_e_x27_2338_ = lean_ctor_get(v_res_2269_, 0);
v_proof_2339_ = lean_ctor_get(v_res_2269_, 1);
v_contextDependent_2340_ = lean_ctor_get_uint8(v_res_2269_, sizeof(void*)*2 + 1);
v_isSharedCheck_2512_ = !lean_is_exclusive(v_res_2269_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2342_ = v_res_2269_;
v_isShared_2343_ = v_isSharedCheck_2512_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_proof_2339_);
lean_inc(v_e_x27_2338_);
lean_dec(v_res_2269_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2512_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2344_; 
lean_inc_ref(v_e_x27_2338_);
v___x_2344_ = l_Lean_Meta_Sym_inferType(v_e_x27_2338_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
if (lean_obj_tag(v___x_2344_) == 0)
{
lean_object* v_a_2345_; lean_object* v___x_2346_; uint8_t v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; 
v_a_2345_ = lean_ctor_get(v___x_2344_, 0);
lean_inc(v_a_2345_);
lean_dec_ref_known(v___x_2344_, 1);
v___x_2346_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__1));
v___x_2347_ = 0;
v___x_2348_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2);
lean_inc(v_idx_2266_);
lean_inc(v_typeName_2265_);
v___x_2349_ = l_Lean_Expr_proj___override(v_typeName_2265_, v_idx_2266_, v___x_2348_);
v___x_2350_ = l_Lean_mkLambda(v___x_2346_, v___x_2347_, v_a_2345_, v___x_2349_);
lean_inc_ref(v___x_2350_);
v___x_2351_ = l_Lean_Meta_Sym_inferType(v___x_2350_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
if (lean_obj_tag(v___x_2351_) == 0)
{
lean_object* v_a_2352_; uint8_t v___x_2353_; 
v_a_2352_ = lean_ctor_get(v___x_2351_, 0);
lean_inc(v_a_2352_);
lean_dec_ref_known(v___x_2351_, 1);
v___x_2353_ = l_Lean_Expr_isArrow(v_a_2352_);
if (v___x_2353_ == 0)
{
uint8_t v___x_2354_; lean_object* v___x_2355_; lean_object* v___f_2356_; lean_object* v___x_2357_; 
lean_dec(v_a_2352_);
v___x_2354_ = 1;
v___x_2355_ = lean_box(v___x_2354_);
lean_inc_ref(v_e_2240_);
v___f_2356_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2356_, 0, v___x_2355_);
lean_closure_set(v___f_2356_, 1, v_e_2240_);
v___x_2357_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___f_2356_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
if (lean_obj_tag(v___x_2357_) == 0)
{
lean_object* v_a_2358_; 
v_a_2358_ = lean_ctor_get(v___x_2357_, 0);
lean_inc(v_a_2358_);
lean_dec_ref_known(v___x_2357_, 1);
if (lean_obj_tag(v_a_2358_) == 0)
{
lean_object* v___x_2359_; 
lean_del_object(v___x_2342_);
lean_inc_ref(v_e_x27_2338_);
lean_inc_ref(v_struct_2267_);
v___x_2359_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_struct_2267_, v_e_x27_2338_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
if (lean_obj_tag(v___x_2359_) == 0)
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2405_; 
v_a_2360_ = lean_ctor_get(v___x_2359_, 0);
v_isSharedCheck_2405_ = !lean_is_exclusive(v___x_2359_);
if (v_isSharedCheck_2405_ == 0)
{
v___x_2362_ = v___x_2359_;
v_isShared_2363_ = v_isSharedCheck_2405_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2359_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2405_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
uint8_t v___x_2364_; 
v___x_2364_ = lean_unbox(v_a_2360_);
lean_dec(v_a_2360_);
if (v___x_2364_ == 0)
{
uint8_t v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2368_; 
lean_dec_ref(v___x_2350_);
lean_dec_ref(v_proof_2339_);
lean_dec_ref(v_e_x27_2338_);
lean_dec_ref_known(v_e_2240_, 3);
v___x_2365_ = 1;
v___x_2366_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2366_, 0, v___x_2365_);
lean_ctor_set_uint8(v___x_2366_, 1, v_contextDependent_2340_);
if (v_isShared_2363_ == 0)
{
lean_ctor_set(v___x_2362_, 0, v___x_2366_);
v___x_2368_ = v___x_2362_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v___x_2366_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
return v___x_2368_;
}
}
else
{
lean_object* v___x_2370_; 
lean_del_object(v___x_2362_);
v___x_2370_ = l_Lean_Meta_mkHCongr(v___x_2350_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
if (lean_obj_tag(v___x_2370_) == 0)
{
lean_object* v_a_2371_; lean_object* v_proof_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; 
v_a_2371_ = lean_ctor_get(v___x_2370_, 0);
lean_inc(v_a_2371_);
lean_dec_ref_known(v___x_2370_, 1);
v_proof_2372_ = lean_ctor_get(v_a_2371_, 1);
lean_inc_ref(v_proof_2372_);
lean_dec(v_a_2371_);
lean_inc_ref(v_e_x27_2338_);
lean_inc_ref(v_struct_2267_);
v___x_2373_ = l_Lean_mkApp3(v_proof_2372_, v_struct_2267_, v_e_x27_2338_, v_proof_2339_);
v___x_2374_ = l_Lean_Meta_mkEqOfHEq(v___x_2373_, v___x_2353_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
if (lean_obj_tag(v___x_2374_) == 0)
{
lean_object* v_a_2375_; size_t v___x_2376_; size_t v___x_2377_; uint8_t v___x_2378_; 
v_a_2375_ = lean_ctor_get(v___x_2374_, 0);
lean_inc(v_a_2375_);
lean_dec_ref_known(v___x_2374_, 1);
v___x_2376_ = lean_ptr_addr(v_struct_2267_);
v___x_2377_ = lean_ptr_addr(v_e_x27_2338_);
v___x_2378_ = lean_usize_dec_eq(v___x_2376_, v___x_2377_);
if (v___x_2378_ == 0)
{
lean_object* v___x_2379_; 
lean_inc(v_idx_2266_);
lean_inc(v_typeName_2265_);
lean_dec_ref_known(v_e_2240_, 3);
v___x_2379_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_typeName_2265_, v_idx_2266_, v_e_x27_2338_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
if (lean_obj_tag(v___x_2379_) == 0)
{
lean_object* v_a_2380_; 
v_a_2380_ = lean_ctor_get(v___x_2379_, 0);
lean_inc(v_a_2380_);
lean_dec_ref_known(v___x_2379_, 1);
v___y_2252_ = v___x_2353_;
v___y_2253_ = v_contextDependent_2340_;
v___y_2254_ = v_a_2375_;
v_a_2255_ = v_a_2380_;
goto v___jp_2251_;
}
else
{
lean_object* v_a_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2388_; 
lean_dec(v_a_2375_);
v_a_2381_ = lean_ctor_get(v___x_2379_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2379_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2383_ = v___x_2379_;
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_a_2381_);
lean_dec(v___x_2379_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2386_; 
if (v_isShared_2384_ == 0)
{
v___x_2386_ = v___x_2383_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v_a_2381_);
v___x_2386_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
return v___x_2386_;
}
}
}
}
else
{
lean_dec_ref(v_e_x27_2338_);
v___y_2252_ = v___x_2353_;
v___y_2253_ = v_contextDependent_2340_;
v___y_2254_ = v_a_2375_;
v_a_2255_ = v_e_2240_;
goto v___jp_2251_;
}
}
else
{
lean_object* v_a_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2396_; 
lean_dec_ref(v_e_x27_2338_);
lean_dec_ref_known(v_e_2240_, 3);
v_a_2389_ = lean_ctor_get(v___x_2374_, 0);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2374_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2391_ = v___x_2374_;
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_a_2389_);
lean_dec(v___x_2374_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v___x_2394_; 
if (v_isShared_2392_ == 0)
{
v___x_2394_ = v___x_2391_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_a_2389_);
v___x_2394_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
return v___x_2394_;
}
}
}
}
else
{
lean_object* v_a_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2404_; 
lean_dec_ref(v_proof_2339_);
lean_dec_ref(v_e_x27_2338_);
lean_dec_ref_known(v_e_2240_, 3);
v_a_2397_ = lean_ctor_get(v___x_2370_, 0);
v_isSharedCheck_2404_ = !lean_is_exclusive(v___x_2370_);
if (v_isSharedCheck_2404_ == 0)
{
v___x_2399_ = v___x_2370_;
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_a_2397_);
lean_dec(v___x_2370_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v___x_2402_; 
if (v_isShared_2400_ == 0)
{
v___x_2402_ = v___x_2399_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v_a_2397_);
v___x_2402_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
return v___x_2402_;
}
}
}
}
}
}
else
{
lean_object* v_a_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2413_; 
lean_dec_ref(v___x_2350_);
lean_dec_ref(v_proof_2339_);
lean_dec_ref(v_e_x27_2338_);
lean_dec_ref_known(v_e_2240_, 3);
v_a_2406_ = lean_ctor_get(v___x_2359_, 0);
v_isSharedCheck_2413_ = !lean_is_exclusive(v___x_2359_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2408_ = v___x_2359_;
v_isShared_2409_ = v_isSharedCheck_2413_;
goto v_resetjp_2407_;
}
else
{
lean_inc(v_a_2406_);
lean_dec(v___x_2359_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2413_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
lean_object* v___x_2411_; 
if (v_isShared_2409_ == 0)
{
v___x_2411_ = v___x_2408_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v_a_2406_);
v___x_2411_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
return v___x_2411_;
}
}
}
}
else
{
lean_object* v_val_2414_; lean_object* v___x_2415_; 
lean_dec_ref(v___x_2350_);
lean_dec_ref(v_proof_2339_);
lean_dec_ref(v_e_x27_2338_);
lean_dec_ref_known(v_e_2240_, 3);
v_val_2414_ = lean_ctor_get(v_a_2358_, 0);
lean_inc(v_val_2414_);
lean_dec_ref_known(v_a_2358_, 1);
v___x_2415_ = l_Lean_Meta_Sym_shareCommonInc(v_val_2414_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
if (lean_obj_tag(v___x_2415_) == 0)
{
lean_object* v_a_2416_; lean_object* v___x_2417_; 
v_a_2416_ = lean_ctor_get(v___x_2415_, 0);
lean_inc_n(v_a_2416_, 2);
lean_dec_ref_known(v___x_2415_, 1);
v___x_2417_ = l_Lean_Meta_Sym_mkEqRefl(v_a_2416_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
if (lean_obj_tag(v___x_2417_) == 0)
{
lean_object* v_a_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2428_; 
v_a_2418_ = lean_ctor_get(v___x_2417_, 0);
v_isSharedCheck_2428_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2428_ == 0)
{
v___x_2420_ = v___x_2417_;
v_isShared_2421_ = v_isSharedCheck_2428_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_a_2418_);
lean_dec(v___x_2417_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2428_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v___x_2423_; 
if (v_isShared_2343_ == 0)
{
lean_ctor_set(v___x_2342_, 1, v_a_2418_);
lean_ctor_set(v___x_2342_, 0, v_a_2416_);
v___x_2423_ = v___x_2342_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v_a_2416_);
lean_ctor_set(v_reuseFailAlloc_2427_, 1, v_a_2418_);
v___x_2423_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
lean_object* v___x_2425_; 
lean_ctor_set_uint8(v___x_2423_, sizeof(void*)*2, v_contextDependent_2340_);
lean_ctor_set_uint8(v___x_2423_, sizeof(void*)*2 + 1, v___x_2353_);
if (v_isShared_2421_ == 0)
{
lean_ctor_set(v___x_2420_, 0, v___x_2423_);
v___x_2425_ = v___x_2420_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v___x_2423_);
v___x_2425_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
return v___x_2425_;
}
}
}
}
else
{
lean_object* v_a_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2436_; 
lean_dec(v_a_2416_);
lean_del_object(v___x_2342_);
v_a_2429_ = lean_ctor_get(v___x_2417_, 0);
v_isSharedCheck_2436_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2431_ = v___x_2417_;
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_a_2429_);
lean_dec(v___x_2417_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v___x_2434_; 
if (v_isShared_2432_ == 0)
{
v___x_2434_ = v___x_2431_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v_a_2429_);
v___x_2434_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
return v___x_2434_;
}
}
}
}
else
{
lean_object* v_a_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2444_; 
lean_del_object(v___x_2342_);
v_a_2437_ = lean_ctor_get(v___x_2415_, 0);
v_isSharedCheck_2444_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2439_ = v___x_2415_;
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_a_2437_);
lean_dec(v___x_2415_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2442_; 
if (v_isShared_2440_ == 0)
{
v___x_2442_ = v___x_2439_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v_a_2437_);
v___x_2442_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
return v___x_2442_;
}
}
}
}
}
else
{
lean_object* v_a_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2452_; 
lean_dec_ref(v___x_2350_);
lean_del_object(v___x_2342_);
lean_dec_ref(v_proof_2339_);
lean_dec_ref(v_e_x27_2338_);
lean_dec_ref_known(v_e_2240_, 3);
v_a_2445_ = lean_ctor_get(v___x_2357_, 0);
v_isSharedCheck_2452_ = !lean_is_exclusive(v___x_2357_);
if (v_isSharedCheck_2452_ == 0)
{
v___x_2447_ = v___x_2357_;
v_isShared_2448_ = v_isSharedCheck_2452_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_a_2445_);
lean_dec(v___x_2357_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2452_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
lean_object* v___x_2450_; 
if (v_isShared_2448_ == 0)
{
v___x_2450_ = v___x_2447_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v_a_2445_);
v___x_2450_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
return v___x_2450_;
}
}
}
}
else
{
lean_del_object(v___x_2342_);
if (lean_obj_tag(v_a_2352_) == 7)
{
lean_object* v_binderType_2453_; lean_object* v_body_2454_; lean_object* v___x_2455_; 
v_binderType_2453_ = lean_ctor_get(v_a_2352_, 1);
lean_inc_ref_n(v_binderType_2453_, 2);
v_body_2454_ = lean_ctor_get(v_a_2352_, 2);
lean_inc_ref(v_body_2454_);
lean_dec_ref_known(v_a_2352_, 3);
v___x_2455_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_2453_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
if (lean_obj_tag(v___x_2455_) == 0)
{
lean_object* v_a_2456_; lean_object* v___x_2457_; 
v_a_2456_ = lean_ctor_get(v___x_2455_, 0);
lean_inc(v_a_2456_);
lean_dec_ref_known(v___x_2455_, 1);
lean_inc_ref(v_body_2454_);
v___x_2457_ = l_Lean_Meta_Sym_getLevel___redArg(v_body_2454_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
if (lean_obj_tag(v___x_2457_) == 0)
{
lean_object* v_a_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; size_t v___x_2465_; size_t v___x_2466_; uint8_t v___x_2467_; 
v_a_2458_ = lean_ctor_get(v___x_2457_, 0);
lean_inc(v_a_2458_);
lean_dec_ref_known(v___x_2457_, 1);
v___x_2459_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4));
v___x_2460_ = lean_box(0);
v___x_2461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2461_, 0, v_a_2458_);
lean_ctor_set(v___x_2461_, 1, v___x_2460_);
v___x_2462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2462_, 0, v_a_2456_);
lean_ctor_set(v___x_2462_, 1, v___x_2461_);
v___x_2463_ = l_Lean_mkConst(v___x_2459_, v___x_2462_);
lean_inc_ref(v_e_x27_2338_);
lean_inc_ref(v_struct_2267_);
v___x_2464_ = l_Lean_mkApp6(v___x_2463_, v_binderType_2453_, v_body_2454_, v_struct_2267_, v_e_x27_2338_, v___x_2350_, v_proof_2339_);
v___x_2465_ = lean_ptr_addr(v_struct_2267_);
v___x_2466_ = lean_ptr_addr(v_e_x27_2338_);
v___x_2467_ = lean_usize_dec_eq(v___x_2465_, v___x_2466_);
if (v___x_2467_ == 0)
{
lean_object* v___x_2468_; 
lean_inc(v_idx_2266_);
lean_inc(v_typeName_2265_);
lean_dec_ref_known(v_e_2240_, 3);
v___x_2468_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_typeName_2265_, v_idx_2266_, v_e_x27_2338_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
if (lean_obj_tag(v___x_2468_) == 0)
{
lean_object* v_a_2469_; 
v_a_2469_ = lean_ctor_get(v___x_2468_, 0);
lean_inc(v_a_2469_);
lean_dec_ref_known(v___x_2468_, 1);
v___y_2259_ = v_contextDependent_2340_;
v___y_2260_ = v___x_2464_;
v_a_2261_ = v_a_2469_;
goto v___jp_2258_;
}
else
{
lean_object* v_a_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2477_; 
lean_dec_ref(v___x_2464_);
v_a_2470_ = lean_ctor_get(v___x_2468_, 0);
v_isSharedCheck_2477_ = !lean_is_exclusive(v___x_2468_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2472_ = v___x_2468_;
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_a_2470_);
lean_dec(v___x_2468_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v___x_2475_; 
if (v_isShared_2473_ == 0)
{
v___x_2475_ = v___x_2472_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v_a_2470_);
v___x_2475_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
return v___x_2475_;
}
}
}
}
else
{
lean_dec_ref(v_e_x27_2338_);
v___y_2259_ = v_contextDependent_2340_;
v___y_2260_ = v___x_2464_;
v_a_2261_ = v_e_2240_;
goto v___jp_2258_;
}
}
else
{
lean_object* v_a_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2485_; 
lean_dec(v_a_2456_);
lean_dec_ref(v_body_2454_);
lean_dec_ref(v_binderType_2453_);
lean_dec_ref(v___x_2350_);
lean_dec_ref(v_proof_2339_);
lean_dec_ref(v_e_x27_2338_);
lean_dec_ref_known(v_e_2240_, 3);
v_a_2478_ = lean_ctor_get(v___x_2457_, 0);
v_isSharedCheck_2485_ = !lean_is_exclusive(v___x_2457_);
if (v_isSharedCheck_2485_ == 0)
{
v___x_2480_ = v___x_2457_;
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_a_2478_);
lean_dec(v___x_2457_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2483_; 
if (v_isShared_2481_ == 0)
{
v___x_2483_ = v___x_2480_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v_a_2478_);
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
else
{
lean_object* v_a_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2493_; 
lean_dec_ref(v_body_2454_);
lean_dec_ref(v_binderType_2453_);
lean_dec_ref(v___x_2350_);
lean_dec_ref(v_proof_2339_);
lean_dec_ref(v_e_x27_2338_);
lean_dec_ref_known(v_e_2240_, 3);
v_a_2486_ = lean_ctor_get(v___x_2455_, 0);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2455_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2488_ = v___x_2455_;
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_a_2486_);
lean_dec(v___x_2455_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v___x_2491_; 
if (v_isShared_2489_ == 0)
{
v___x_2491_ = v___x_2488_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_a_2486_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
return v___x_2491_;
}
}
}
}
else
{
lean_object* v___x_2494_; lean_object* v___x_2495_; 
lean_dec(v_a_2352_);
lean_dec_ref(v___x_2350_);
lean_dec_ref(v_proof_2339_);
lean_dec_ref(v_e_x27_2338_);
lean_dec_ref_known(v_e_2240_, 3);
v___x_2494_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8);
v___x_2495_ = l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1(v___x_2494_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
return v___x_2495_;
}
}
}
else
{
lean_object* v_a_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2503_; 
lean_dec_ref(v___x_2350_);
lean_del_object(v___x_2342_);
lean_dec_ref(v_proof_2339_);
lean_dec_ref(v_e_x27_2338_);
lean_dec_ref_known(v_e_2240_, 3);
v_a_2496_ = lean_ctor_get(v___x_2351_, 0);
v_isSharedCheck_2503_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2498_ = v___x_2351_;
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_a_2496_);
lean_dec(v___x_2351_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v___x_2501_; 
if (v_isShared_2499_ == 0)
{
v___x_2501_ = v___x_2498_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v_a_2496_);
v___x_2501_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
return v___x_2501_;
}
}
}
}
else
{
lean_object* v_a_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2511_; 
lean_del_object(v___x_2342_);
lean_dec_ref(v_proof_2339_);
lean_dec_ref(v_e_x27_2338_);
lean_dec_ref_known(v_e_2240_, 3);
v_a_2504_ = lean_ctor_get(v___x_2344_, 0);
v_isSharedCheck_2511_ = !lean_is_exclusive(v___x_2344_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2506_ = v___x_2344_;
v_isShared_2507_ = v_isSharedCheck_2511_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_a_2504_);
lean_dec(v___x_2344_);
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
}
}
}
else
{
lean_object* v___x_2826_; lean_object* v___x_2827_; 
lean_dec_ref(v_e_2240_);
v___x_2826_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
v___x_2827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2827_, 0, v___x_2826_);
return v___x_2827_;
}
v___jp_2251_:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___x_2256_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2256_, 0, v_a_2255_);
lean_ctor_set(v___x_2256_, 1, v___y_2254_);
lean_ctor_set_uint8(v___x_2256_, sizeof(void*)*2, v___y_2253_);
lean_ctor_set_uint8(v___x_2256_, sizeof(void*)*2 + 1, v___y_2252_);
v___x_2257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2257_, 0, v___x_2256_);
return v___x_2257_;
}
v___jp_2258_:
{
uint8_t v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; 
v___x_2262_ = 0;
v___x_2263_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2263_, 0, v_a_2261_);
lean_ctor_set(v___x_2263_, 1, v___y_2260_);
lean_ctor_set_uint8(v___x_2263_, sizeof(void*)*2, v___y_2259_);
lean_ctor_set_uint8(v___x_2263_, sizeof(void*)*2 + 1, v___x_2262_);
v___x_2264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2264_, 0, v___x_2263_);
return v___x_2264_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___boxed(lean_object* v_e_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_){
_start:
{
lean_object* v_res_2839_; 
v_res_2839_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj(v_e_2828_, v_a_2829_, v_a_2830_, v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_);
lean_dec(v_a_2837_);
lean_dec_ref(v_a_2836_);
lean_dec(v_a_2835_);
lean_dec_ref(v_a_2834_);
lean_dec(v_a_2833_);
lean_dec_ref(v_a_2832_);
lean_dec(v_a_2831_);
lean_dec_ref(v_a_2830_);
lean_dec(v_a_2829_);
return v_res_2839_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5(lean_object* v_00_u03b1_2840_, lean_object* v_x_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_){
_start:
{
lean_object* v___x_2852_; 
v___x_2852_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5___redArg(v_x_2841_);
return v___x_2852_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5___boxed(lean_object* v_00_u03b1_2853_, lean_object* v_x_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_){
_start:
{
lean_object* v_res_2865_; 
v_res_2865_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5(v_00_u03b1_2853_, v_x_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
lean_dec(v___y_2863_);
lean_dec_ref(v___y_2862_);
lean_dec(v___y_2861_);
lean_dec_ref(v___y_2860_);
lean_dec(v___y_2859_);
lean_dec_ref(v___y_2858_);
lean_dec(v___y_2857_);
lean_dec_ref(v___y_2856_);
lean_dec(v___y_2855_);
return v_res_2865_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4(lean_object* v_oldTraces_2866_, lean_object* v_data_2867_, lean_object* v_ref_2868_, lean_object* v_msg_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_){
_start:
{
lean_object* v___x_2880_; 
v___x_2880_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4___redArg(v_oldTraces_2866_, v_data_2867_, v_ref_2868_, v_msg_2869_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_);
return v___x_2880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4___boxed(lean_object* v_oldTraces_2881_, lean_object* v_data_2882_, lean_object* v_ref_2883_, lean_object* v_msg_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_){
_start:
{
lean_object* v_res_2895_; 
v_res_2895_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4(v_oldTraces_2881_, v_data_2882_, v_ref_2883_, v_msg_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_);
lean_dec(v___y_2893_);
lean_dec_ref(v___y_2892_);
lean_dec(v___y_2891_);
lean_dec_ref(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec(v___y_2887_);
lean_dec_ref(v___y_2886_);
lean_dec(v___y_2885_);
return v_res_2895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0_spec__1___redArg(lean_object* v_f_2896_, lean_object* v_a_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_){
_start:
{
lean_object* v___y_2906_; lean_object* v___x_2909_; uint8_t v_debug_2910_; 
v___x_2909_ = lean_st_ref_get(v___y_2899_);
v_debug_2910_ = lean_ctor_get_uint8(v___x_2909_, sizeof(void*)*11);
lean_dec(v___x_2909_);
if (v_debug_2910_ == 0)
{
v___y_2906_ = v___y_2899_;
goto v___jp_2905_;
}
else
{
lean_object* v___x_2911_; 
v___x_2911_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_2896_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
if (lean_obj_tag(v___x_2911_) == 0)
{
lean_object* v___x_2912_; 
lean_dec_ref_known(v___x_2911_, 1);
v___x_2912_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
if (lean_obj_tag(v___x_2912_) == 0)
{
lean_dec_ref_known(v___x_2912_, 1);
v___y_2906_ = v___y_2899_;
goto v___jp_2905_;
}
else
{
lean_object* v_a_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2920_; 
lean_dec_ref(v_a_2897_);
lean_dec_ref(v_f_2896_);
v_a_2913_ = lean_ctor_get(v___x_2912_, 0);
v_isSharedCheck_2920_ = !lean_is_exclusive(v___x_2912_);
if (v_isSharedCheck_2920_ == 0)
{
v___x_2915_ = v___x_2912_;
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_a_2913_);
lean_dec(v___x_2912_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
lean_object* v___x_2918_; 
if (v_isShared_2916_ == 0)
{
v___x_2918_ = v___x_2915_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v_a_2913_);
v___x_2918_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
return v___x_2918_;
}
}
}
}
else
{
lean_object* v_a_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_2928_; 
lean_dec_ref(v_a_2897_);
lean_dec_ref(v_f_2896_);
v_a_2921_ = lean_ctor_get(v___x_2911_, 0);
v_isSharedCheck_2928_ = !lean_is_exclusive(v___x_2911_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2923_ = v___x_2911_;
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_a_2921_);
lean_dec(v___x_2911_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
lean_object* v___x_2926_; 
if (v_isShared_2924_ == 0)
{
v___x_2926_ = v___x_2923_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v_a_2921_);
v___x_2926_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
return v___x_2926_;
}
}
}
}
v___jp_2905_:
{
lean_object* v___x_2907_; lean_object* v___x_2908_; 
v___x_2907_ = l_Lean_Expr_app___override(v_f_2896_, v_a_2897_);
v___x_2908_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2907_, v___y_2906_);
return v___x_2908_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_2929_, lean_object* v_a_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_){
_start:
{
lean_object* v_res_2938_; 
v_res_2938_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0_spec__1___redArg(v_f_2929_, v_a_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_);
lean_dec(v___y_2936_);
lean_dec_ref(v___y_2935_);
lean_dec(v___y_2934_);
lean_dec_ref(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec_ref(v___y_2931_);
return v_res_2938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0(lean_object* v_args_2939_, lean_object* v_endIdx_2940_, lean_object* v_b_2941_, lean_object* v_i_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_){
_start:
{
uint8_t v___x_2953_; 
v___x_2953_ = lean_nat_dec_le(v_endIdx_2940_, v_i_2942_);
if (v___x_2953_ == 0)
{
lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; 
v___x_2954_ = l_Lean_instInhabitedExpr;
v___x_2955_ = lean_array_get_borrowed(v___x_2954_, v_args_2939_, v_i_2942_);
lean_inc(v___x_2955_);
v___x_2956_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0_spec__1___redArg(v_b_2941_, v___x_2955_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_);
if (lean_obj_tag(v___x_2956_) == 0)
{
lean_object* v_a_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; 
v_a_2957_ = lean_ctor_get(v___x_2956_, 0);
lean_inc(v_a_2957_);
lean_dec_ref_known(v___x_2956_, 1);
v___x_2958_ = lean_unsigned_to_nat(1u);
v___x_2959_ = lean_nat_add(v_i_2942_, v___x_2958_);
lean_dec(v_i_2942_);
v_b_2941_ = v_a_2957_;
v_i_2942_ = v___x_2959_;
goto _start;
}
else
{
lean_dec(v_i_2942_);
return v___x_2956_;
}
}
else
{
lean_object* v___x_2961_; 
lean_dec(v_i_2942_);
v___x_2961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2961_, 0, v_b_2941_);
return v___x_2961_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0___boxed(lean_object* v_args_2962_, lean_object* v_endIdx_2963_, lean_object* v_b_2964_, lean_object* v_i_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_){
_start:
{
lean_object* v_res_2976_; 
v_res_2976_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0(v_args_2962_, v_endIdx_2963_, v_b_2964_, v_i_2965_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_);
lean_dec(v___y_2974_);
lean_dec_ref(v___y_2973_);
lean_dec(v___y_2972_);
lean_dec_ref(v___y_2971_);
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
lean_dec(v___y_2966_);
lean_dec(v_endIdx_2963_);
lean_dec_ref(v_args_2962_);
return v_res_2976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0(lean_object* v_f_2977_, lean_object* v_args_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_){
_start:
{
lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; 
v___x_2989_ = lean_unsigned_to_nat(0u);
v___x_2990_ = lean_array_get_size(v_args_2978_);
v___x_2991_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0(v_args_2978_, v___x_2990_, v_f_2977_, v___x_2989_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_);
return v___x_2991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0___boxed(lean_object* v_f_2992_, lean_object* v_args_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_){
_start:
{
lean_object* v_res_3004_; 
v_res_3004_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0(v_f_2992_, v_args_2993_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_);
lean_dec(v___y_3002_);
lean_dec_ref(v___y_3001_);
lean_dec(v___y_3000_);
lean_dec_ref(v___y_2999_);
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2997_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2995_);
lean_dec(v___y_2994_);
lean_dec_ref(v_args_2993_);
return v_res_3004_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__0(void){
_start:
{
lean_object* v___x_3005_; lean_object* v_dummy_3006_; 
v___x_3005_ = lean_box(0);
v_dummy_3006_ = l_Lean_Expr_sort___override(v___x_3005_);
return v_dummy_3006_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__2(void){
_start:
{
lean_object* v___x_3008_; lean_object* v___x_3009_; 
v___x_3008_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__1));
v___x_3009_ = l_Lean_stringToMessageData(v___x_3008_);
return v___x_3009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn(lean_object* v_e_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_){
_start:
{
uint8_t v___x_3024_; 
v___x_3024_ = l_Lean_Expr_isApp(v_e_3010_);
if (v___x_3024_ == 0)
{
lean_object* v___x_3025_; lean_object* v___x_3026_; 
lean_dec_ref(v_e_3010_);
v___x_3025_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_3025_, 0, v___x_3024_);
lean_ctor_set_uint8(v___x_3025_, 1, v___x_3024_);
v___x_3026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3026_, 0, v___x_3025_);
return v___x_3026_;
}
else
{
lean_object* v_fn_3027_; uint8_t v___x_3028_; 
v_fn_3027_ = l_Lean_Expr_getAppFn(v_e_3010_);
v___x_3028_ = l_Lean_Expr_isLambda(v_fn_3027_);
if (v___x_3028_ == 0)
{
uint8_t v___x_3029_; 
v___x_3029_ = l_Lean_Expr_isConst(v_fn_3027_);
if (v___x_3029_ == 0)
{
lean_object* v___x_3030_; 
lean_inc(v_a_3019_);
lean_inc_ref(v_a_3018_);
lean_inc(v_a_3017_);
lean_inc_ref(v_a_3016_);
lean_inc(v_a_3015_);
lean_inc_ref(v_a_3014_);
lean_inc(v_a_3013_);
lean_inc_ref(v_a_3012_);
lean_inc(v_a_3011_);
lean_inc_ref(v_fn_3027_);
v___x_3030_ = lean_sym_simp(v_fn_3027_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_);
if (lean_obj_tag(v___x_3030_) == 0)
{
lean_object* v_a_3031_; 
v_a_3031_ = lean_ctor_get(v___x_3030_, 0);
lean_inc(v_a_3031_);
if (lean_obj_tag(v_a_3031_) == 0)
{
lean_dec_ref_known(v_a_3031_, 0);
lean_dec_ref(v_fn_3027_);
lean_dec_ref(v_e_3010_);
return v___x_3030_;
}
else
{
lean_object* v_e_x27_3032_; lean_object* v_proof_3033_; uint8_t v_contextDependent_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3138_; 
lean_dec_ref_known(v___x_3030_, 1);
v_e_x27_3032_ = lean_ctor_get(v_a_3031_, 0);
v_proof_3033_ = lean_ctor_get(v_a_3031_, 1);
v_contextDependent_3034_ = lean_ctor_get_uint8(v_a_3031_, sizeof(void*)*2 + 1);
v_isSharedCheck_3138_ = !lean_is_exclusive(v_a_3031_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3036_ = v_a_3031_;
v_isShared_3037_ = v_isSharedCheck_3138_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_proof_3033_);
lean_inc(v_e_x27_3032_);
lean_dec(v_a_3031_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3138_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v___x_3038_; 
lean_inc_ref(v_e_x27_3032_);
v___x_3038_ = l_Lean_Meta_Sym_inferType(v_e_x27_3032_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_);
if (lean_obj_tag(v___x_3038_) == 0)
{
lean_object* v_a_3039_; lean_object* v___x_3040_; lean_object* v_dummy_3041_; lean_object* v_nargs_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; 
v_a_3039_ = lean_ctor_get(v___x_3038_, 0);
lean_inc(v_a_3039_);
lean_dec_ref_known(v___x_3038_, 1);
v___x_3040_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2);
v_dummy_3041_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__0, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__0_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__0);
v_nargs_3042_ = l_Lean_Expr_getAppNumArgs(v_e_3010_);
lean_inc(v_nargs_3042_);
v___x_3043_ = lean_mk_array(v_nargs_3042_, v_dummy_3041_);
v___x_3044_ = lean_unsigned_to_nat(1u);
v___x_3045_ = lean_nat_sub(v_nargs_3042_, v___x_3044_);
lean_dec(v_nargs_3042_);
lean_inc_ref(v_e_3010_);
v___x_3046_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3010_, v___x_3043_, v___x_3045_);
v___x_3047_ = l_Lean_mkAppN(v___x_3040_, v___x_3046_);
lean_inc_ref(v_e_x27_3032_);
v___x_3048_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0(v_e_x27_3032_, v___x_3046_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_);
lean_dec_ref(v___x_3046_);
if (lean_obj_tag(v___x_3048_) == 0)
{
lean_object* v_a_3049_; lean_object* v___x_3050_; 
v_a_3049_ = lean_ctor_get(v___x_3048_, 0);
lean_inc(v_a_3049_);
lean_dec_ref_known(v___x_3048_, 1);
lean_inc_ref(v_e_3010_);
v___x_3050_ = l_Lean_Meta_Sym_inferType(v_e_3010_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_);
if (lean_obj_tag(v___x_3050_) == 0)
{
lean_object* v_a_3051_; lean_object* v___x_3052_; uint8_t v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; 
v_a_3051_ = lean_ctor_get(v___x_3050_, 0);
lean_inc(v_a_3051_);
lean_dec_ref_known(v___x_3050_, 1);
v___x_3052_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__1));
v___x_3053_ = 0;
lean_inc_n(v_a_3039_, 2);
v___x_3054_ = l_Lean_mkLambda(v___x_3052_, v___x_3053_, v_a_3039_, v___x_3047_);
v___x_3055_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_3039_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_);
if (lean_obj_tag(v___x_3055_) == 0)
{
lean_object* v_a_3056_; lean_object* v___x_3057_; 
v_a_3056_ = lean_ctor_get(v___x_3055_, 0);
lean_inc(v_a_3056_);
lean_dec_ref_known(v___x_3055_, 1);
lean_inc(v_a_3051_);
v___x_3057_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_3051_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_);
if (lean_obj_tag(v___x_3057_) == 0)
{
lean_object* v_options_3058_; lean_object* v_a_3059_; lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3097_; 
v_options_3058_ = lean_ctor_get(v_a_3018_, 2);
v_a_3059_ = lean_ctor_get(v___x_3057_, 0);
v_isSharedCheck_3097_ = !lean_is_exclusive(v___x_3057_);
if (v_isSharedCheck_3097_ == 0)
{
v___x_3061_ = v___x_3057_;
v_isShared_3062_ = v_isSharedCheck_3097_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_a_3059_);
lean_dec(v___x_3057_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3097_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
lean_object* v_inheritedTraceOptions_3063_; uint8_t v_hasTrace_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; 
v_inheritedTraceOptions_3063_ = lean_ctor_get(v_a_3018_, 13);
v_hasTrace_3064_ = lean_ctor_get_uint8(v_options_3058_, sizeof(void*)*1);
v___x_3065_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4));
v___x_3066_ = lean_box(0);
v___x_3067_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3067_, 0, v_a_3059_);
lean_ctor_set(v___x_3067_, 1, v___x_3066_);
v___x_3068_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3068_, 0, v_a_3056_);
lean_ctor_set(v___x_3068_, 1, v___x_3067_);
v___x_3069_ = l_Lean_mkConst(v___x_3065_, v___x_3068_);
v___x_3070_ = l_Lean_mkApp6(v___x_3069_, v_a_3039_, v_a_3051_, v_fn_3027_, v_e_x27_3032_, v___x_3054_, v_proof_3033_);
if (v_hasTrace_3064_ == 0)
{
lean_dec_ref(v_e_3010_);
goto v___jp_3071_;
}
else
{
lean_object* v___x_3078_; lean_object* v___x_3079_; uint8_t v___x_3080_; 
v___x_3078_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2));
v___x_3079_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3);
v___x_3080_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3063_, v_options_3058_, v___x_3079_);
if (v___x_3080_ == 0)
{
lean_dec_ref(v_e_3010_);
goto v___jp_3071_;
}
else
{
lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; 
v___x_3081_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__2, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__2);
v___x_3082_ = l_Lean_indentExpr(v_e_3010_);
v___x_3083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3083_, 0, v___x_3081_);
lean_ctor_set(v___x_3083_, 1, v___x_3082_);
v___x_3084_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_3085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3085_, 0, v___x_3083_);
lean_ctor_set(v___x_3085_, 1, v___x_3084_);
lean_inc(v_a_3049_);
v___x_3086_ = l_Lean_indentExpr(v_a_3049_);
v___x_3087_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3087_, 0, v___x_3085_);
lean_ctor_set(v___x_3087_, 1, v___x_3086_);
v___x_3088_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(v___x_3078_, v___x_3087_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_);
if (lean_obj_tag(v___x_3088_) == 0)
{
lean_dec_ref_known(v___x_3088_, 1);
goto v___jp_3071_;
}
else
{
lean_object* v_a_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3096_; 
lean_dec_ref(v___x_3070_);
lean_del_object(v___x_3061_);
lean_dec(v_a_3049_);
lean_del_object(v___x_3036_);
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
}
v___jp_3071_:
{
lean_object* v___x_3073_; 
if (v_isShared_3037_ == 0)
{
lean_ctor_set(v___x_3036_, 1, v___x_3070_);
lean_ctor_set(v___x_3036_, 0, v_a_3049_);
v___x_3073_ = v___x_3036_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v_a_3049_);
lean_ctor_set(v_reuseFailAlloc_3077_, 1, v___x_3070_);
v___x_3073_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
lean_object* v___x_3075_; 
lean_ctor_set_uint8(v___x_3073_, sizeof(void*)*2, v_contextDependent_3034_);
lean_ctor_set_uint8(v___x_3073_, sizeof(void*)*2 + 1, v___x_3029_);
if (v_isShared_3062_ == 0)
{
lean_ctor_set(v___x_3061_, 0, v___x_3073_);
v___x_3075_ = v___x_3061_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v___x_3073_);
v___x_3075_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
return v___x_3075_;
}
}
}
}
}
else
{
lean_object* v_a_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3105_; 
lean_dec(v_a_3056_);
lean_dec_ref(v___x_3054_);
lean_dec(v_a_3051_);
lean_dec(v_a_3049_);
lean_dec(v_a_3039_);
lean_del_object(v___x_3036_);
lean_dec_ref(v_proof_3033_);
lean_dec_ref(v_e_x27_3032_);
lean_dec_ref(v_fn_3027_);
lean_dec_ref(v_e_3010_);
v_a_3098_ = lean_ctor_get(v___x_3057_, 0);
v_isSharedCheck_3105_ = !lean_is_exclusive(v___x_3057_);
if (v_isSharedCheck_3105_ == 0)
{
v___x_3100_ = v___x_3057_;
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_a_3098_);
lean_dec(v___x_3057_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
lean_object* v___x_3103_; 
if (v_isShared_3101_ == 0)
{
v___x_3103_ = v___x_3100_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v_a_3098_);
v___x_3103_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
return v___x_3103_;
}
}
}
}
else
{
lean_object* v_a_3106_; lean_object* v___x_3108_; uint8_t v_isShared_3109_; uint8_t v_isSharedCheck_3113_; 
lean_dec_ref(v___x_3054_);
lean_dec(v_a_3051_);
lean_dec(v_a_3049_);
lean_dec(v_a_3039_);
lean_del_object(v___x_3036_);
lean_dec_ref(v_proof_3033_);
lean_dec_ref(v_e_x27_3032_);
lean_dec_ref(v_fn_3027_);
lean_dec_ref(v_e_3010_);
v_a_3106_ = lean_ctor_get(v___x_3055_, 0);
v_isSharedCheck_3113_ = !lean_is_exclusive(v___x_3055_);
if (v_isSharedCheck_3113_ == 0)
{
v___x_3108_ = v___x_3055_;
v_isShared_3109_ = v_isSharedCheck_3113_;
goto v_resetjp_3107_;
}
else
{
lean_inc(v_a_3106_);
lean_dec(v___x_3055_);
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
else
{
lean_object* v_a_3114_; lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3121_; 
lean_dec(v_a_3049_);
lean_dec_ref(v___x_3047_);
lean_dec(v_a_3039_);
lean_del_object(v___x_3036_);
lean_dec_ref(v_proof_3033_);
lean_dec_ref(v_e_x27_3032_);
lean_dec_ref(v_fn_3027_);
lean_dec_ref(v_e_3010_);
v_a_3114_ = lean_ctor_get(v___x_3050_, 0);
v_isSharedCheck_3121_ = !lean_is_exclusive(v___x_3050_);
if (v_isSharedCheck_3121_ == 0)
{
v___x_3116_ = v___x_3050_;
v_isShared_3117_ = v_isSharedCheck_3121_;
goto v_resetjp_3115_;
}
else
{
lean_inc(v_a_3114_);
lean_dec(v___x_3050_);
v___x_3116_ = lean_box(0);
v_isShared_3117_ = v_isSharedCheck_3121_;
goto v_resetjp_3115_;
}
v_resetjp_3115_:
{
lean_object* v___x_3119_; 
if (v_isShared_3117_ == 0)
{
v___x_3119_ = v___x_3116_;
goto v_reusejp_3118_;
}
else
{
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v_a_3114_);
v___x_3119_ = v_reuseFailAlloc_3120_;
goto v_reusejp_3118_;
}
v_reusejp_3118_:
{
return v___x_3119_;
}
}
}
}
else
{
lean_object* v_a_3122_; lean_object* v___x_3124_; uint8_t v_isShared_3125_; uint8_t v_isSharedCheck_3129_; 
lean_dec_ref(v___x_3047_);
lean_dec(v_a_3039_);
lean_del_object(v___x_3036_);
lean_dec_ref(v_proof_3033_);
lean_dec_ref(v_e_x27_3032_);
lean_dec_ref(v_fn_3027_);
lean_dec_ref(v_e_3010_);
v_a_3122_ = lean_ctor_get(v___x_3048_, 0);
v_isSharedCheck_3129_ = !lean_is_exclusive(v___x_3048_);
if (v_isSharedCheck_3129_ == 0)
{
v___x_3124_ = v___x_3048_;
v_isShared_3125_ = v_isSharedCheck_3129_;
goto v_resetjp_3123_;
}
else
{
lean_inc(v_a_3122_);
lean_dec(v___x_3048_);
v___x_3124_ = lean_box(0);
v_isShared_3125_ = v_isSharedCheck_3129_;
goto v_resetjp_3123_;
}
v_resetjp_3123_:
{
lean_object* v___x_3127_; 
if (v_isShared_3125_ == 0)
{
v___x_3127_ = v___x_3124_;
goto v_reusejp_3126_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v_a_3122_);
v___x_3127_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3126_;
}
v_reusejp_3126_:
{
return v___x_3127_;
}
}
}
}
else
{
lean_object* v_a_3130_; lean_object* v___x_3132_; uint8_t v_isShared_3133_; uint8_t v_isSharedCheck_3137_; 
lean_del_object(v___x_3036_);
lean_dec_ref(v_proof_3033_);
lean_dec_ref(v_e_x27_3032_);
lean_dec_ref(v_fn_3027_);
lean_dec_ref(v_e_3010_);
v_a_3130_ = lean_ctor_get(v___x_3038_, 0);
v_isSharedCheck_3137_ = !lean_is_exclusive(v___x_3038_);
if (v_isSharedCheck_3137_ == 0)
{
v___x_3132_ = v___x_3038_;
v_isShared_3133_ = v_isSharedCheck_3137_;
goto v_resetjp_3131_;
}
else
{
lean_inc(v_a_3130_);
lean_dec(v___x_3038_);
v___x_3132_ = lean_box(0);
v_isShared_3133_ = v_isSharedCheck_3137_;
goto v_resetjp_3131_;
}
v_resetjp_3131_:
{
lean_object* v___x_3135_; 
if (v_isShared_3133_ == 0)
{
v___x_3135_ = v___x_3132_;
goto v_reusejp_3134_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v_a_3130_);
v___x_3135_ = v_reuseFailAlloc_3136_;
goto v_reusejp_3134_;
}
v_reusejp_3134_:
{
return v___x_3135_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_fn_3027_);
lean_dec_ref(v_e_3010_);
return v___x_3030_;
}
}
else
{
lean_dec_ref(v_fn_3027_);
lean_dec_ref(v_e_3010_);
goto v___jp_3021_;
}
}
else
{
lean_dec_ref(v_fn_3027_);
lean_dec_ref(v_e_3010_);
goto v___jp_3021_;
}
}
v___jp_3021_:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; 
v___x_3022_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
v___x_3023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3023_, 0, v___x_3022_);
return v___x_3023_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___boxed(lean_object* v_e_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_, lean_object* v_a_3146_, lean_object* v_a_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_){
_start:
{
lean_object* v_res_3150_; 
v_res_3150_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn(v_e_3139_, v_a_3140_, v_a_3141_, v_a_3142_, v_a_3143_, v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_, v_a_3148_);
lean_dec(v_a_3148_);
lean_dec_ref(v_a_3147_);
lean_dec(v_a_3146_);
lean_dec_ref(v_a_3145_);
lean_dec(v_a_3144_);
lean_dec_ref(v_a_3143_);
lean_dec(v_a_3142_);
lean_dec_ref(v_a_3141_);
lean_dec(v_a_3140_);
return v_res_3150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0_spec__1(lean_object* v_f_3151_, lean_object* v_a_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_){
_start:
{
lean_object* v___x_3163_; 
v___x_3163_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0_spec__1___redArg(v_f_3151_, v_a_3152_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_);
return v___x_3163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0_spec__1___boxed(lean_object* v_f_3164_, lean_object* v_a_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_){
_start:
{
lean_object* v_res_3176_; 
v_res_3176_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0_spec__1(v_f_3164_, v_a_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_);
lean_dec(v___y_3174_);
lean_dec_ref(v___y_3173_);
lean_dec(v___y_3172_);
lean_dec_ref(v___y_3171_);
lean_dec(v___y_3170_);
lean_dec_ref(v___y_3169_);
lean_dec(v___y_3168_);
lean_dec_ref(v___y_3167_);
lean_dec(v___y_3166_);
return v_res_3176_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___closed__1(void){
_start:
{
lean_object* v___x_3178_; lean_object* v___x_3179_; 
v___x_3178_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___closed__0));
v___x_3179_ = l_Lean_stringToMessageData(v___x_3178_);
return v___x_3179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst(lean_object* v_e_3180_, lean_object* v_a_3181_, lean_object* v_a_3182_, lean_object* v_a_3183_, lean_object* v_a_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_){
_start:
{
if (lean_obj_tag(v_e_3180_) == 4)
{
lean_object* v_declName_3191_; lean_object* v_us_3192_; lean_object* v___x_3193_; 
v_declName_3191_ = lean_ctor_get(v_e_3180_, 0);
v_us_3192_ = lean_ctor_get(v_e_3180_, 1);
lean_inc(v_declName_3191_);
v___x_3193_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0(v_declName_3191_, v_a_3181_, v_a_3182_, v_a_3183_, v_a_3184_, v_a_3185_, v_a_3186_, v_a_3187_, v_a_3188_, v_a_3189_);
if (lean_obj_tag(v___x_3193_) == 0)
{
lean_object* v_a_3194_; lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3321_; 
v_a_3194_ = lean_ctor_get(v___x_3193_, 0);
v_isSharedCheck_3321_ = !lean_is_exclusive(v___x_3193_);
if (v_isSharedCheck_3321_ == 0)
{
v___x_3196_ = v___x_3193_;
v_isShared_3197_ = v_isSharedCheck_3321_;
goto v_resetjp_3195_;
}
else
{
lean_inc(v_a_3194_);
lean_dec(v___x_3193_);
v___x_3196_ = lean_box(0);
v_isShared_3197_ = v_isSharedCheck_3321_;
goto v_resetjp_3195_;
}
v_resetjp_3195_:
{
uint8_t v___x_3198_; 
v___x_3198_ = l_Lean_ConstantInfo_isDefinition(v_a_3194_);
if (v___x_3198_ == 0)
{
lean_object* v___x_3199_; lean_object* v___x_3201_; 
lean_dec(v_a_3194_);
lean_dec_ref_known(v_e_3180_, 2);
v___x_3199_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_3199_, 0, v___x_3198_);
lean_ctor_set_uint8(v___x_3199_, 1, v___x_3198_);
if (v_isShared_3197_ == 0)
{
lean_ctor_set(v___x_3196_, 0, v___x_3199_);
v___x_3201_ = v___x_3196_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v___x_3199_);
v___x_3201_ = v_reuseFailAlloc_3202_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
return v___x_3201_;
}
}
else
{
lean_object* v___x_3203_; 
v___x_3203_ = l_Lean_ConstantInfo_type(v_a_3194_);
if (lean_obj_tag(v___x_3203_) == 7)
{
lean_object* v___x_3204_; lean_object* v___x_3206_; 
lean_dec_ref_known(v___x_3203_, 3);
lean_dec(v_a_3194_);
lean_dec_ref_known(v_e_3180_, 2);
v___x_3204_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
if (v_isShared_3197_ == 0)
{
lean_ctor_set(v___x_3196_, 0, v___x_3204_);
v___x_3206_ = v___x_3196_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v___x_3204_);
v___x_3206_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
return v___x_3206_;
}
}
else
{
lean_object* v___x_3208_; 
v___x_3208_ = l_Lean_Meta_whnfD(v___x_3203_, v_a_3186_, v_a_3187_, v_a_3188_, v_a_3189_);
if (lean_obj_tag(v___x_3208_) == 0)
{
lean_object* v_a_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3312_; 
v_a_3209_ = lean_ctor_get(v___x_3208_, 0);
v_isSharedCheck_3312_ = !lean_is_exclusive(v___x_3208_);
if (v_isSharedCheck_3312_ == 0)
{
v___x_3211_ = v___x_3208_;
v_isShared_3212_ = v_isSharedCheck_3312_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_a_3209_);
lean_dec(v___x_3208_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3312_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
uint8_t v___x_3213_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; lean_object* v___y_3220_; lean_object* v___y_3221_; uint8_t v___y_3241_; 
v___x_3213_ = 0;
if (lean_obj_tag(v_a_3209_) == 7)
{
lean_object* v___x_3303_; lean_object* v___x_3305_; 
lean_dec_ref_known(v_a_3209_, 3);
lean_del_object(v___x_3211_);
lean_dec(v_a_3194_);
lean_dec_ref_known(v_e_3180_, 2);
v___x_3303_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
if (v_isShared_3197_ == 0)
{
lean_ctor_set(v___x_3196_, 0, v___x_3303_);
v___x_3305_ = v___x_3196_;
goto v_reusejp_3304_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v___x_3303_);
v___x_3305_ = v_reuseFailAlloc_3306_;
goto v_reusejp_3304_;
}
v_reusejp_3304_:
{
return v___x_3305_;
}
}
else
{
uint8_t v___x_3307_; 
lean_dec(v_a_3209_);
lean_del_object(v___x_3196_);
v___x_3307_ = l_Lean_ConstantInfo_hasValue(v_a_3194_, v___x_3213_);
if (v___x_3307_ == 0)
{
v___y_3241_ = v___x_3307_;
goto v___jp_3240_;
}
else
{
lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; uint8_t v___x_3311_; 
v___x_3308_ = l_Lean_ConstantInfo_levelParams(v_a_3194_);
v___x_3309_ = l_List_lengthTR___redArg(v___x_3308_);
lean_dec(v___x_3308_);
v___x_3310_ = l_List_lengthTR___redArg(v_us_3192_);
v___x_3311_ = lean_nat_dec_eq(v___x_3309_, v___x_3310_);
lean_dec(v___x_3310_);
lean_dec(v___x_3309_);
v___y_3241_ = v___x_3311_;
goto v___jp_3240_;
}
}
v___jp_3214_:
{
lean_object* v___x_3222_; 
lean_inc_ref(v___y_3215_);
v___x_3222_ = l_Lean_Meta_Sym_mkEqRefl(v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_);
if (lean_obj_tag(v___x_3222_) == 0)
{
lean_object* v_a_3223_; lean_object* v___x_3225_; uint8_t v_isShared_3226_; uint8_t v_isSharedCheck_3231_; 
v_a_3223_ = lean_ctor_get(v___x_3222_, 0);
v_isSharedCheck_3231_ = !lean_is_exclusive(v___x_3222_);
if (v_isSharedCheck_3231_ == 0)
{
v___x_3225_ = v___x_3222_;
v_isShared_3226_ = v_isSharedCheck_3231_;
goto v_resetjp_3224_;
}
else
{
lean_inc(v_a_3223_);
lean_dec(v___x_3222_);
v___x_3225_ = lean_box(0);
v_isShared_3226_ = v_isSharedCheck_3231_;
goto v_resetjp_3224_;
}
v_resetjp_3224_:
{
lean_object* v___x_3227_; lean_object* v___x_3229_; 
v___x_3227_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3227_, 0, v___y_3215_);
lean_ctor_set(v___x_3227_, 1, v_a_3223_);
lean_ctor_set_uint8(v___x_3227_, sizeof(void*)*2, v___x_3213_);
lean_ctor_set_uint8(v___x_3227_, sizeof(void*)*2 + 1, v___x_3213_);
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
}
else
{
lean_object* v_a_3232_; lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3239_; 
lean_dec_ref(v___y_3215_);
v_a_3232_ = lean_ctor_get(v___x_3222_, 0);
v_isSharedCheck_3239_ = !lean_is_exclusive(v___x_3222_);
if (v_isSharedCheck_3239_ == 0)
{
v___x_3234_ = v___x_3222_;
v_isShared_3235_ = v_isSharedCheck_3239_;
goto v_resetjp_3233_;
}
else
{
lean_inc(v_a_3232_);
lean_dec(v___x_3222_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3239_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
lean_object* v___x_3237_; 
if (v_isShared_3235_ == 0)
{
v___x_3237_ = v___x_3234_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v_a_3232_);
v___x_3237_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
return v___x_3237_;
}
}
}
}
v___jp_3240_:
{
if (v___y_3241_ == 0)
{
lean_object* v___x_3242_; lean_object* v___x_3244_; 
lean_dec(v_a_3194_);
lean_dec_ref_known(v_e_3180_, 2);
v___x_3242_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
if (v_isShared_3212_ == 0)
{
lean_ctor_set(v___x_3211_, 0, v___x_3242_);
v___x_3244_ = v___x_3211_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v___x_3242_);
v___x_3244_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
return v___x_3244_;
}
}
else
{
lean_object* v___x_3246_; 
lean_del_object(v___x_3211_);
lean_inc(v_us_3192_);
v___x_3246_ = l_Lean_Core_instantiateValueLevelParams(v_a_3194_, v_us_3192_, v___x_3213_, v_a_3188_, v_a_3189_);
lean_dec(v_a_3194_);
if (lean_obj_tag(v___x_3246_) == 0)
{
lean_object* v_a_3247_; lean_object* v___x_3248_; 
v_a_3247_ = lean_ctor_get(v___x_3246_, 0);
lean_inc(v_a_3247_);
lean_dec_ref_known(v___x_3246_, 1);
v___x_3248_ = l_Lean_Meta_Sym_unfoldReducible(v_a_3247_, v_a_3186_, v_a_3187_, v_a_3188_, v_a_3189_);
if (lean_obj_tag(v___x_3248_) == 0)
{
lean_object* v_a_3249_; lean_object* v___x_3250_; 
v_a_3249_ = lean_ctor_get(v___x_3248_, 0);
lean_inc(v_a_3249_);
lean_dec_ref_known(v___x_3248_, 1);
v___x_3250_ = l_Lean_Meta_Sym_shareCommonInc(v_a_3249_, v_a_3184_, v_a_3185_, v_a_3186_, v_a_3187_, v_a_3188_, v_a_3189_);
if (lean_obj_tag(v___x_3250_) == 0)
{
lean_object* v_options_3251_; uint8_t v_hasTrace_3252_; 
v_options_3251_ = lean_ctor_get(v_a_3188_, 2);
v_hasTrace_3252_ = lean_ctor_get_uint8(v_options_3251_, sizeof(void*)*1);
if (v_hasTrace_3252_ == 0)
{
lean_object* v_a_3253_; 
lean_dec_ref_known(v_e_3180_, 2);
v_a_3253_ = lean_ctor_get(v___x_3250_, 0);
lean_inc(v_a_3253_);
lean_dec_ref_known(v___x_3250_, 1);
v___y_3215_ = v_a_3253_;
v___y_3216_ = v_a_3184_;
v___y_3217_ = v_a_3185_;
v___y_3218_ = v_a_3186_;
v___y_3219_ = v_a_3187_;
v___y_3220_ = v_a_3188_;
v___y_3221_ = v_a_3189_;
goto v___jp_3214_;
}
else
{
lean_object* v_a_3254_; lean_object* v_inheritedTraceOptions_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; uint8_t v___x_3258_; 
v_a_3254_ = lean_ctor_get(v___x_3250_, 0);
lean_inc(v_a_3254_);
lean_dec_ref_known(v___x_3250_, 1);
v_inheritedTraceOptions_3255_ = lean_ctor_get(v_a_3188_, 13);
v___x_3256_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__1));
v___x_3257_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__2, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__2);
v___x_3258_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3255_, v_options_3251_, v___x_3257_);
if (v___x_3258_ == 0)
{
lean_dec_ref_known(v_e_3180_, 2);
v___y_3215_ = v_a_3254_;
v___y_3216_ = v_a_3184_;
v___y_3217_ = v_a_3185_;
v___y_3218_ = v_a_3186_;
v___y_3219_ = v_a_3187_;
v___y_3220_ = v_a_3188_;
v___y_3221_ = v_a_3189_;
goto v___jp_3214_;
}
else
{
lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; 
v___x_3259_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___closed__1, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___closed__1);
lean_inc(v_declName_3191_);
v___x_3260_ = l_Lean_MessageData_ofName(v_declName_3191_);
v___x_3261_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3261_, 0, v___x_3259_);
lean_ctor_set(v___x_3261_, 1, v___x_3260_);
v___x_3262_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8);
v___x_3263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3263_, 0, v___x_3261_);
lean_ctor_set(v___x_3263_, 1, v___x_3262_);
v___x_3264_ = l_Lean_indentExpr(v_e_3180_);
v___x_3265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3265_, 0, v___x_3263_);
lean_ctor_set(v___x_3265_, 1, v___x_3264_);
v___x_3266_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_3267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3267_, 0, v___x_3265_);
lean_ctor_set(v___x_3267_, 1, v___x_3266_);
lean_inc(v_a_3254_);
v___x_3268_ = l_Lean_indentExpr(v_a_3254_);
v___x_3269_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3269_, 0, v___x_3267_);
lean_ctor_set(v___x_3269_, 1, v___x_3268_);
v___x_3270_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(v___x_3256_, v___x_3269_, v_a_3186_, v_a_3187_, v_a_3188_, v_a_3189_);
if (lean_obj_tag(v___x_3270_) == 0)
{
lean_dec_ref_known(v___x_3270_, 1);
v___y_3215_ = v_a_3254_;
v___y_3216_ = v_a_3184_;
v___y_3217_ = v_a_3185_;
v___y_3218_ = v_a_3186_;
v___y_3219_ = v_a_3187_;
v___y_3220_ = v_a_3188_;
v___y_3221_ = v_a_3189_;
goto v___jp_3214_;
}
else
{
lean_object* v_a_3271_; lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3278_; 
lean_dec(v_a_3254_);
v_a_3271_ = lean_ctor_get(v___x_3270_, 0);
v_isSharedCheck_3278_ = !lean_is_exclusive(v___x_3270_);
if (v_isSharedCheck_3278_ == 0)
{
v___x_3273_ = v___x_3270_;
v_isShared_3274_ = v_isSharedCheck_3278_;
goto v_resetjp_3272_;
}
else
{
lean_inc(v_a_3271_);
lean_dec(v___x_3270_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3278_;
goto v_resetjp_3272_;
}
v_resetjp_3272_:
{
lean_object* v___x_3276_; 
if (v_isShared_3274_ == 0)
{
v___x_3276_ = v___x_3273_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v_a_3271_);
v___x_3276_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
return v___x_3276_;
}
}
}
}
}
}
else
{
lean_object* v_a_3279_; lean_object* v___x_3281_; uint8_t v_isShared_3282_; uint8_t v_isSharedCheck_3286_; 
lean_dec_ref_known(v_e_3180_, 2);
v_a_3279_ = lean_ctor_get(v___x_3250_, 0);
v_isSharedCheck_3286_ = !lean_is_exclusive(v___x_3250_);
if (v_isSharedCheck_3286_ == 0)
{
v___x_3281_ = v___x_3250_;
v_isShared_3282_ = v_isSharedCheck_3286_;
goto v_resetjp_3280_;
}
else
{
lean_inc(v_a_3279_);
lean_dec(v___x_3250_);
v___x_3281_ = lean_box(0);
v_isShared_3282_ = v_isSharedCheck_3286_;
goto v_resetjp_3280_;
}
v_resetjp_3280_:
{
lean_object* v___x_3284_; 
if (v_isShared_3282_ == 0)
{
v___x_3284_ = v___x_3281_;
goto v_reusejp_3283_;
}
else
{
lean_object* v_reuseFailAlloc_3285_; 
v_reuseFailAlloc_3285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3285_, 0, v_a_3279_);
v___x_3284_ = v_reuseFailAlloc_3285_;
goto v_reusejp_3283_;
}
v_reusejp_3283_:
{
return v___x_3284_;
}
}
}
}
else
{
lean_object* v_a_3287_; lean_object* v___x_3289_; uint8_t v_isShared_3290_; uint8_t v_isSharedCheck_3294_; 
lean_dec_ref_known(v_e_3180_, 2);
v_a_3287_ = lean_ctor_get(v___x_3248_, 0);
v_isSharedCheck_3294_ = !lean_is_exclusive(v___x_3248_);
if (v_isSharedCheck_3294_ == 0)
{
v___x_3289_ = v___x_3248_;
v_isShared_3290_ = v_isSharedCheck_3294_;
goto v_resetjp_3288_;
}
else
{
lean_inc(v_a_3287_);
lean_dec(v___x_3248_);
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
else
{
lean_object* v_a_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3302_; 
lean_dec_ref_known(v_e_3180_, 2);
v_a_3295_ = lean_ctor_get(v___x_3246_, 0);
v_isSharedCheck_3302_ = !lean_is_exclusive(v___x_3246_);
if (v_isSharedCheck_3302_ == 0)
{
v___x_3297_ = v___x_3246_;
v_isShared_3298_ = v_isSharedCheck_3302_;
goto v_resetjp_3296_;
}
else
{
lean_inc(v_a_3295_);
lean_dec(v___x_3246_);
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
}
}
}
else
{
lean_object* v_a_3313_; lean_object* v___x_3315_; uint8_t v_isShared_3316_; uint8_t v_isSharedCheck_3320_; 
lean_del_object(v___x_3196_);
lean_dec(v_a_3194_);
lean_dec_ref_known(v_e_3180_, 2);
v_a_3313_ = lean_ctor_get(v___x_3208_, 0);
v_isSharedCheck_3320_ = !lean_is_exclusive(v___x_3208_);
if (v_isSharedCheck_3320_ == 0)
{
v___x_3315_ = v___x_3208_;
v_isShared_3316_ = v_isSharedCheck_3320_;
goto v_resetjp_3314_;
}
else
{
lean_inc(v_a_3313_);
lean_dec(v___x_3208_);
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
}
}
}
else
{
lean_object* v_a_3322_; lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3329_; 
lean_dec_ref_known(v_e_3180_, 2);
v_a_3322_ = lean_ctor_get(v___x_3193_, 0);
v_isSharedCheck_3329_ = !lean_is_exclusive(v___x_3193_);
if (v_isSharedCheck_3329_ == 0)
{
v___x_3324_ = v___x_3193_;
v_isShared_3325_ = v_isSharedCheck_3329_;
goto v_resetjp_3323_;
}
else
{
lean_inc(v_a_3322_);
lean_dec(v___x_3193_);
v___x_3324_ = lean_box(0);
v_isShared_3325_ = v_isSharedCheck_3329_;
goto v_resetjp_3323_;
}
v_resetjp_3323_:
{
lean_object* v___x_3327_; 
if (v_isShared_3325_ == 0)
{
v___x_3327_ = v___x_3324_;
goto v_reusejp_3326_;
}
else
{
lean_object* v_reuseFailAlloc_3328_; 
v_reuseFailAlloc_3328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3328_, 0, v_a_3322_);
v___x_3327_ = v_reuseFailAlloc_3328_;
goto v_reusejp_3326_;
}
v_reusejp_3326_:
{
return v___x_3327_;
}
}
}
}
else
{
lean_object* v___x_3330_; lean_object* v___x_3331_; 
lean_dec_ref(v_e_3180_);
v___x_3330_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
v___x_3331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3331_, 0, v___x_3330_);
return v___x_3331_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___boxed(lean_object* v_e_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_, lean_object* v_a_3340_, lean_object* v_a_3341_, lean_object* v_a_3342_){
_start:
{
lean_object* v_res_3343_; 
v_res_3343_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst(v_e_3332_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_, v_a_3341_);
lean_dec(v_a_3341_);
lean_dec_ref(v_a_3340_);
lean_dec(v_a_3339_);
lean_dec_ref(v_a_3338_);
lean_dec(v_a_3337_);
lean_dec_ref(v_a_3336_);
lean_dec(v_a_3335_);
lean_dec_ref(v_a_3334_);
lean_dec(v_a_3333_);
return v_res_3343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___lam__0(lean_object* v_x_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_){
_start:
{
lean_object* v___x_3356_; 
lean_inc_ref(v___y_3345_);
v___x_3356_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems(v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_);
if (lean_obj_tag(v___x_3356_) == 0)
{
lean_object* v_a_3357_; 
v_a_3357_ = lean_ctor_get(v___x_3356_, 0);
lean_inc(v_a_3357_);
if (lean_obj_tag(v_a_3357_) == 0)
{
uint8_t v_done_3358_; 
v_done_3358_ = lean_ctor_get_uint8(v_a_3357_, 0);
if (v_done_3358_ == 0)
{
uint8_t v_contextDependent_3359_; lean_object* v___x_3360_; 
lean_dec_ref_known(v___x_3356_, 1);
v_contextDependent_3359_ = lean_ctor_get_uint8(v_a_3357_, 1);
lean_dec_ref_known(v_a_3357_, 0);
v___x_3360_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst(v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_);
if (lean_obj_tag(v___x_3360_) == 0)
{
lean_object* v_a_3361_; uint8_t v___y_3363_; 
v_a_3361_ = lean_ctor_get(v___x_3360_, 0);
lean_inc(v_a_3361_);
if (v_contextDependent_3359_ == 0)
{
lean_dec(v_a_3361_);
return v___x_3360_;
}
else
{
if (lean_obj_tag(v_a_3361_) == 0)
{
uint8_t v_contextDependent_3373_; 
v_contextDependent_3373_ = lean_ctor_get_uint8(v_a_3361_, 1);
v___y_3363_ = v_contextDependent_3373_;
goto v___jp_3362_;
}
else
{
uint8_t v___x_3374_; 
v___x_3374_ = 0;
v___y_3363_ = v___x_3374_;
goto v___jp_3362_;
}
}
v___jp_3362_:
{
if (v___y_3363_ == 0)
{
lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3371_; 
v_isSharedCheck_3371_ = !lean_is_exclusive(v___x_3360_);
if (v_isSharedCheck_3371_ == 0)
{
lean_object* v_unused_3372_; 
v_unused_3372_ = lean_ctor_get(v___x_3360_, 0);
lean_dec(v_unused_3372_);
v___x_3365_ = v___x_3360_;
v_isShared_3366_ = v_isSharedCheck_3371_;
goto v_resetjp_3364_;
}
else
{
lean_dec(v___x_3360_);
v___x_3365_ = lean_box(0);
v_isShared_3366_ = v_isSharedCheck_3371_;
goto v_resetjp_3364_;
}
v_resetjp_3364_:
{
lean_object* v___x_3367_; lean_object* v___x_3369_; 
v___x_3367_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3361_);
if (v_isShared_3366_ == 0)
{
lean_ctor_set(v___x_3365_, 0, v___x_3367_);
v___x_3369_ = v___x_3365_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3370_; 
v_reuseFailAlloc_3370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3370_, 0, v___x_3367_);
v___x_3369_ = v_reuseFailAlloc_3370_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
return v___x_3369_;
}
}
}
else
{
lean_dec(v_a_3361_);
return v___x_3360_;
}
}
}
else
{
return v___x_3360_;
}
}
else
{
lean_dec_ref_known(v_a_3357_, 0);
lean_dec_ref(v___y_3345_);
return v___x_3356_;
}
}
else
{
lean_dec_ref_known(v_a_3357_, 2);
lean_dec_ref(v___y_3345_);
return v___x_3356_;
}
}
else
{
lean_dec_ref(v___y_3345_);
return v___x_3356_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___lam__0___boxed(lean_object* v_x_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_){
_start:
{
lean_object* v_res_3387_; 
v_res_3387_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___lam__0(v_x_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_);
lean_dec(v___y_3385_);
lean_dec_ref(v___y_3384_);
lean_dec(v___y_3383_);
lean_dec_ref(v___y_3382_);
lean_dec(v___y_3381_);
lean_dec_ref(v___y_3380_);
lean_dec(v___y_3379_);
lean_dec_ref(v___y_3378_);
lean_dec(v___y_3377_);
return v_res_3387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep(lean_object* v_e_3391_, lean_object* v_a_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_, lean_object* v_a_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_){
_start:
{
switch(lean_obj_tag(v_e_3391_))
{
case 9:
{
lean_object* v___x_3405_; 
v___x_3405_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg(v_e_3391_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_);
return v___x_3405_;
}
case 11:
{
lean_object* v___x_3406_; 
v___x_3406_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj(v_e_3391_, v_a_3392_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_);
return v___x_3406_;
}
case 4:
{
lean_object* v___x_3407_; 
lean_inc_ref(v_e_3391_);
v___x_3407_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleOpaqueConst(v_e_3391_, v_a_3392_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_);
if (lean_obj_tag(v___x_3407_) == 0)
{
lean_object* v_a_3408_; lean_object* v___x_3409_; 
v_a_3408_ = lean_ctor_get(v___x_3407_, 0);
lean_inc(v_a_3408_);
v___x_3409_ = lean_box(0);
if (lean_obj_tag(v_a_3408_) == 0)
{
uint8_t v_done_3410_; 
v_done_3410_ = lean_ctor_get_uint8(v_a_3408_, 0);
if (v_done_3410_ == 0)
{
uint8_t v_contextDependent_3411_; lean_object* v___x_3412_; 
lean_dec_ref_known(v___x_3407_, 1);
v_contextDependent_3411_ = lean_ctor_get_uint8(v_a_3408_, 1);
lean_dec_ref_known(v_a_3408_, 0);
v___x_3412_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___lam__0(v___x_3409_, v_e_3391_, v_a_3392_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_);
if (lean_obj_tag(v___x_3412_) == 0)
{
lean_object* v_a_3413_; uint8_t v___y_3415_; 
v_a_3413_ = lean_ctor_get(v___x_3412_, 0);
lean_inc(v_a_3413_);
if (v_contextDependent_3411_ == 0)
{
lean_dec(v_a_3413_);
return v___x_3412_;
}
else
{
if (lean_obj_tag(v_a_3413_) == 0)
{
uint8_t v_contextDependent_3425_; 
v_contextDependent_3425_ = lean_ctor_get_uint8(v_a_3413_, 1);
v___y_3415_ = v_contextDependent_3425_;
goto v___jp_3414_;
}
else
{
uint8_t v_contextDependent_3426_; 
v_contextDependent_3426_ = lean_ctor_get_uint8(v_a_3413_, sizeof(void*)*2 + 1);
v___y_3415_ = v_contextDependent_3426_;
goto v___jp_3414_;
}
}
v___jp_3414_:
{
if (v___y_3415_ == 0)
{
lean_object* v___x_3417_; uint8_t v_isShared_3418_; uint8_t v_isSharedCheck_3423_; 
v_isSharedCheck_3423_ = !lean_is_exclusive(v___x_3412_);
if (v_isSharedCheck_3423_ == 0)
{
lean_object* v_unused_3424_; 
v_unused_3424_ = lean_ctor_get(v___x_3412_, 0);
lean_dec(v_unused_3424_);
v___x_3417_ = v___x_3412_;
v_isShared_3418_ = v_isSharedCheck_3423_;
goto v_resetjp_3416_;
}
else
{
lean_dec(v___x_3412_);
v___x_3417_ = lean_box(0);
v_isShared_3418_ = v_isSharedCheck_3423_;
goto v_resetjp_3416_;
}
v_resetjp_3416_:
{
lean_object* v___x_3419_; lean_object* v___x_3421_; 
v___x_3419_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3413_);
if (v_isShared_3418_ == 0)
{
lean_ctor_set(v___x_3417_, 0, v___x_3419_);
v___x_3421_ = v___x_3417_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v___x_3419_);
v___x_3421_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
return v___x_3421_;
}
}
}
else
{
lean_dec(v_a_3413_);
return v___x_3412_;
}
}
}
else
{
return v___x_3412_;
}
}
else
{
lean_dec_ref_known(v_a_3408_, 0);
lean_dec_ref_known(v_e_3391_, 2);
return v___x_3407_;
}
}
else
{
uint8_t v_done_3427_; 
v_done_3427_ = lean_ctor_get_uint8(v_a_3408_, sizeof(void*)*2);
if (v_done_3427_ == 0)
{
lean_object* v_e_x27_3428_; lean_object* v_proof_3429_; uint8_t v_contextDependent_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3480_; 
lean_dec_ref_known(v___x_3407_, 1);
v_e_x27_3428_ = lean_ctor_get(v_a_3408_, 0);
v_proof_3429_ = lean_ctor_get(v_a_3408_, 1);
v_contextDependent_3430_ = lean_ctor_get_uint8(v_a_3408_, sizeof(void*)*2 + 1);
v_isSharedCheck_3480_ = !lean_is_exclusive(v_a_3408_);
if (v_isSharedCheck_3480_ == 0)
{
v___x_3432_ = v_a_3408_;
v_isShared_3433_ = v_isSharedCheck_3480_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_proof_3429_);
lean_inc(v_e_x27_3428_);
lean_dec(v_a_3408_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3480_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v___x_3434_; 
lean_inc_ref(v_e_x27_3428_);
v___x_3434_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___lam__0(v___x_3409_, v_e_x27_3428_, v_a_3392_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_);
if (lean_obj_tag(v___x_3434_) == 0)
{
lean_object* v_a_3435_; lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3479_; 
v_a_3435_ = lean_ctor_get(v___x_3434_, 0);
v_isSharedCheck_3479_ = !lean_is_exclusive(v___x_3434_);
if (v_isSharedCheck_3479_ == 0)
{
v___x_3437_ = v___x_3434_;
v_isShared_3438_ = v_isSharedCheck_3479_;
goto v_resetjp_3436_;
}
else
{
lean_inc(v_a_3435_);
lean_dec(v___x_3434_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3479_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
if (lean_obj_tag(v_a_3435_) == 0)
{
uint8_t v_done_3439_; uint8_t v_contextDependent_3440_; uint8_t v___y_3442_; 
lean_dec_ref_known(v_e_3391_, 2);
v_done_3439_ = lean_ctor_get_uint8(v_a_3435_, 0);
v_contextDependent_3440_ = lean_ctor_get_uint8(v_a_3435_, 1);
lean_dec_ref_known(v_a_3435_, 0);
if (v_contextDependent_3430_ == 0)
{
v___y_3442_ = v_contextDependent_3440_;
goto v___jp_3441_;
}
else
{
v___y_3442_ = v_contextDependent_3430_;
goto v___jp_3441_;
}
v___jp_3441_:
{
lean_object* v___x_3444_; 
if (v_isShared_3433_ == 0)
{
v___x_3444_ = v___x_3432_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v_e_x27_3428_);
lean_ctor_set(v_reuseFailAlloc_3448_, 1, v_proof_3429_);
v___x_3444_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
lean_object* v___x_3446_; 
lean_ctor_set_uint8(v___x_3444_, sizeof(void*)*2, v_done_3439_);
lean_ctor_set_uint8(v___x_3444_, sizeof(void*)*2 + 1, v___y_3442_);
if (v_isShared_3438_ == 0)
{
lean_ctor_set(v___x_3437_, 0, v___x_3444_);
v___x_3446_ = v___x_3437_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v___x_3444_);
v___x_3446_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
return v___x_3446_;
}
}
}
}
else
{
lean_object* v_e_x27_3449_; lean_object* v_proof_3450_; uint8_t v_done_3451_; uint8_t v_contextDependent_3452_; lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3478_; 
lean_del_object(v___x_3437_);
lean_del_object(v___x_3432_);
v_e_x27_3449_ = lean_ctor_get(v_a_3435_, 0);
v_proof_3450_ = lean_ctor_get(v_a_3435_, 1);
v_done_3451_ = lean_ctor_get_uint8(v_a_3435_, sizeof(void*)*2);
v_contextDependent_3452_ = lean_ctor_get_uint8(v_a_3435_, sizeof(void*)*2 + 1);
v_isSharedCheck_3478_ = !lean_is_exclusive(v_a_3435_);
if (v_isSharedCheck_3478_ == 0)
{
v___x_3454_ = v_a_3435_;
v_isShared_3455_ = v_isSharedCheck_3478_;
goto v_resetjp_3453_;
}
else
{
lean_inc(v_proof_3450_);
lean_inc(v_e_x27_3449_);
lean_dec(v_a_3435_);
v___x_3454_ = lean_box(0);
v_isShared_3455_ = v_isSharedCheck_3478_;
goto v_resetjp_3453_;
}
v_resetjp_3453_:
{
lean_object* v___x_3456_; 
lean_inc_ref(v_e_x27_3449_);
v___x_3456_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v_e_3391_, v_e_x27_3428_, v_proof_3429_, v_e_x27_3449_, v_proof_3450_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_);
if (lean_obj_tag(v___x_3456_) == 0)
{
lean_object* v_a_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3469_; 
v_a_3457_ = lean_ctor_get(v___x_3456_, 0);
v_isSharedCheck_3469_ = !lean_is_exclusive(v___x_3456_);
if (v_isSharedCheck_3469_ == 0)
{
v___x_3459_ = v___x_3456_;
v_isShared_3460_ = v_isSharedCheck_3469_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_a_3457_);
lean_dec(v___x_3456_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3469_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
uint8_t v___y_3462_; 
if (v_contextDependent_3430_ == 0)
{
v___y_3462_ = v_contextDependent_3452_;
goto v___jp_3461_;
}
else
{
v___y_3462_ = v_contextDependent_3430_;
goto v___jp_3461_;
}
v___jp_3461_:
{
lean_object* v___x_3464_; 
if (v_isShared_3455_ == 0)
{
lean_ctor_set(v___x_3454_, 1, v_a_3457_);
v___x_3464_ = v___x_3454_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v_e_x27_3449_);
lean_ctor_set(v_reuseFailAlloc_3468_, 1, v_a_3457_);
lean_ctor_set_uint8(v_reuseFailAlloc_3468_, sizeof(void*)*2, v_done_3451_);
v___x_3464_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
lean_object* v___x_3466_; 
lean_ctor_set_uint8(v___x_3464_, sizeof(void*)*2 + 1, v___y_3462_);
if (v_isShared_3460_ == 0)
{
lean_ctor_set(v___x_3459_, 0, v___x_3464_);
v___x_3466_ = v___x_3459_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v___x_3464_);
v___x_3466_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
return v___x_3466_;
}
}
}
}
}
else
{
lean_object* v_a_3470_; lean_object* v___x_3472_; uint8_t v_isShared_3473_; uint8_t v_isSharedCheck_3477_; 
lean_del_object(v___x_3454_);
lean_dec_ref(v_e_x27_3449_);
v_a_3470_ = lean_ctor_get(v___x_3456_, 0);
v_isSharedCheck_3477_ = !lean_is_exclusive(v___x_3456_);
if (v_isSharedCheck_3477_ == 0)
{
v___x_3472_ = v___x_3456_;
v_isShared_3473_ = v_isSharedCheck_3477_;
goto v_resetjp_3471_;
}
else
{
lean_inc(v_a_3470_);
lean_dec(v___x_3456_);
v___x_3472_ = lean_box(0);
v_isShared_3473_ = v_isSharedCheck_3477_;
goto v_resetjp_3471_;
}
v_resetjp_3471_:
{
lean_object* v___x_3475_; 
if (v_isShared_3473_ == 0)
{
v___x_3475_ = v___x_3472_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v_a_3470_);
v___x_3475_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
return v___x_3475_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_3432_);
lean_dec_ref(v_proof_3429_);
lean_dec_ref(v_e_x27_3428_);
lean_dec_ref_known(v_e_3391_, 2);
return v___x_3434_;
}
}
}
else
{
lean_dec_ref_known(v_a_3408_, 2);
lean_dec_ref_known(v_e_3391_, 2);
return v___x_3407_;
}
}
}
else
{
lean_dec_ref_known(v_e_3391_, 2);
return v___x_3407_;
}
}
case 5:
{
lean_object* v___x_3481_; 
lean_inc_ref(v_e_3391_);
v___x_3481_ = l_Lean_Meta_Tactic_Cbv_tryMatcher(v_e_3391_, v_a_3392_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_);
if (lean_obj_tag(v___x_3481_) == 0)
{
lean_object* v_a_3482_; 
v_a_3482_ = lean_ctor_get(v___x_3481_, 0);
lean_inc(v_a_3482_);
if (lean_obj_tag(v_a_3482_) == 0)
{
uint8_t v_done_3483_; 
v_done_3483_ = lean_ctor_get_uint8(v_a_3482_, 0);
if (v_done_3483_ == 0)
{
uint8_t v_contextDependent_3484_; lean_object* v___x_3485_; 
lean_dec_ref_known(v___x_3481_, 1);
v_contextDependent_3484_ = lean_ctor_get_uint8(v_a_3482_, 1);
lean_dec_ref_known(v_a_3482_, 0);
v___x_3485_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn(v_e_3391_, v_a_3392_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_);
if (lean_obj_tag(v___x_3485_) == 0)
{
lean_object* v_a_3486_; uint8_t v___y_3488_; 
v_a_3486_ = lean_ctor_get(v___x_3485_, 0);
lean_inc(v_a_3486_);
if (v_contextDependent_3484_ == 0)
{
lean_dec(v_a_3486_);
return v___x_3485_;
}
else
{
if (lean_obj_tag(v_a_3486_) == 0)
{
uint8_t v_contextDependent_3498_; 
v_contextDependent_3498_ = lean_ctor_get_uint8(v_a_3486_, 1);
v___y_3488_ = v_contextDependent_3498_;
goto v___jp_3487_;
}
else
{
uint8_t v_contextDependent_3499_; 
v_contextDependent_3499_ = lean_ctor_get_uint8(v_a_3486_, sizeof(void*)*2 + 1);
v___y_3488_ = v_contextDependent_3499_;
goto v___jp_3487_;
}
}
v___jp_3487_:
{
if (v___y_3488_ == 0)
{
lean_object* v___x_3490_; uint8_t v_isShared_3491_; uint8_t v_isSharedCheck_3496_; 
v_isSharedCheck_3496_ = !lean_is_exclusive(v___x_3485_);
if (v_isSharedCheck_3496_ == 0)
{
lean_object* v_unused_3497_; 
v_unused_3497_ = lean_ctor_get(v___x_3485_, 0);
lean_dec(v_unused_3497_);
v___x_3490_ = v___x_3485_;
v_isShared_3491_ = v_isSharedCheck_3496_;
goto v_resetjp_3489_;
}
else
{
lean_dec(v___x_3485_);
v___x_3490_ = lean_box(0);
v_isShared_3491_ = v_isSharedCheck_3496_;
goto v_resetjp_3489_;
}
v_resetjp_3489_:
{
lean_object* v___x_3492_; lean_object* v___x_3494_; 
v___x_3492_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3486_);
if (v_isShared_3491_ == 0)
{
lean_ctor_set(v___x_3490_, 0, v___x_3492_);
v___x_3494_ = v___x_3490_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v___x_3492_);
v___x_3494_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
return v___x_3494_;
}
}
}
else
{
lean_dec(v_a_3486_);
return v___x_3485_;
}
}
}
else
{
return v___x_3485_;
}
}
else
{
lean_dec_ref_known(v_a_3482_, 0);
lean_dec_ref_known(v_e_3391_, 2);
return v___x_3481_;
}
}
else
{
lean_dec_ref_known(v_a_3482_, 2);
lean_dec_ref_known(v_e_3391_, 2);
return v___x_3481_;
}
}
else
{
lean_dec_ref_known(v_e_3391_, 2);
return v___x_3481_;
}
}
case 8:
{
uint8_t v___x_3500_; 
v___x_3500_ = l_Lean_Expr_letNondep_x21(v_e_3391_);
if (v___x_3500_ == 0)
{
lean_object* v___x_3501_; 
v___x_3501_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg(v_e_3391_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_);
return v___x_3501_;
}
else
{
lean_object* v___x_3502_; 
v___x_3502_ = l_Lean_Meta_Sym_Simp_toBetaApp(v_e_3391_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_);
if (lean_obj_tag(v___x_3502_) == 0)
{
lean_object* v_a_3503_; lean_object* v___x_3505_; uint8_t v_isShared_3506_; uint8_t v_isSharedCheck_3514_; 
v_a_3503_ = lean_ctor_get(v___x_3502_, 0);
v_isSharedCheck_3514_ = !lean_is_exclusive(v___x_3502_);
if (v_isSharedCheck_3514_ == 0)
{
v___x_3505_ = v___x_3502_;
v_isShared_3506_ = v_isSharedCheck_3514_;
goto v_resetjp_3504_;
}
else
{
lean_inc(v_a_3503_);
lean_dec(v___x_3502_);
v___x_3505_ = lean_box(0);
v_isShared_3506_ = v_isSharedCheck_3514_;
goto v_resetjp_3504_;
}
v_resetjp_3504_:
{
lean_object* v_e_3507_; lean_object* v_h_3508_; uint8_t v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3512_; 
v_e_3507_ = lean_ctor_get(v_a_3503_, 2);
lean_inc_ref(v_e_3507_);
v_h_3508_ = lean_ctor_get(v_a_3503_, 3);
lean_inc_ref(v_h_3508_);
lean_dec(v_a_3503_);
v___x_3509_ = 0;
v___x_3510_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3510_, 0, v_e_3507_);
lean_ctor_set(v___x_3510_, 1, v_h_3508_);
lean_ctor_set_uint8(v___x_3510_, sizeof(void*)*2, v___x_3509_);
lean_ctor_set_uint8(v___x_3510_, sizeof(void*)*2 + 1, v___x_3509_);
if (v_isShared_3506_ == 0)
{
lean_ctor_set(v___x_3505_, 0, v___x_3510_);
v___x_3512_ = v___x_3505_;
goto v_reusejp_3511_;
}
else
{
lean_object* v_reuseFailAlloc_3513_; 
v_reuseFailAlloc_3513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3513_, 0, v___x_3510_);
v___x_3512_ = v_reuseFailAlloc_3513_;
goto v_reusejp_3511_;
}
v_reusejp_3511_:
{
return v___x_3512_;
}
}
}
else
{
lean_object* v_a_3515_; lean_object* v___x_3517_; uint8_t v_isShared_3518_; uint8_t v_isSharedCheck_3522_; 
v_a_3515_ = lean_ctor_get(v___x_3502_, 0);
v_isSharedCheck_3522_ = !lean_is_exclusive(v___x_3502_);
if (v_isSharedCheck_3522_ == 0)
{
v___x_3517_ = v___x_3502_;
v_isShared_3518_ = v_isSharedCheck_3522_;
goto v_resetjp_3516_;
}
else
{
lean_inc(v_a_3515_);
lean_dec(v___x_3502_);
v___x_3517_ = lean_box(0);
v_isShared_3518_ = v_isSharedCheck_3522_;
goto v_resetjp_3516_;
}
v_resetjp_3516_:
{
lean_object* v___x_3520_; 
if (v_isShared_3518_ == 0)
{
v___x_3520_ = v___x_3517_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3521_; 
v_reuseFailAlloc_3521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3521_, 0, v_a_3515_);
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
case 7:
{
lean_dec_ref_known(v_e_3391_, 3);
goto v___jp_3402_;
}
case 6:
{
lean_dec_ref_known(v_e_3391_, 3);
goto v___jp_3402_;
}
case 1:
{
lean_object* v___x_3523_; lean_object* v___x_3524_; 
lean_dec_ref_known(v_e_3391_, 1);
v___x_3523_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___closed__0));
v___x_3524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3524_, 0, v___x_3523_);
return v___x_3524_;
}
case 2:
{
lean_object* v___x_3525_; lean_object* v___x_3526_; 
lean_dec_ref_known(v_e_3391_, 1);
v___x_3525_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___closed__0));
v___x_3526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3526_, 0, v___x_3525_);
return v___x_3526_;
}
case 0:
{
lean_object* v___x_3527_; lean_object* v___x_3528_; 
lean_dec_ref_known(v_e_3391_, 1);
v___x_3527_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___closed__0));
v___x_3528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3528_, 0, v___x_3527_);
return v___x_3528_;
}
case 3:
{
lean_object* v___x_3529_; lean_object* v___x_3530_; 
lean_dec_ref_known(v_e_3391_, 1);
v___x_3529_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___closed__0));
v___x_3530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3530_, 0, v___x_3529_);
return v___x_3530_;
}
default: 
{
lean_object* v___x_3531_; lean_object* v___x_3532_; 
lean_dec_ref(v_e_3391_);
v___x_3531_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
v___x_3532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3532_, 0, v___x_3531_);
return v___x_3532_;
}
}
v___jp_3402_:
{
lean_object* v___x_3403_; lean_object* v___x_3404_; 
v___x_3403_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___closed__0));
v___x_3404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3404_, 0, v___x_3403_);
return v___x_3404_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___boxed(lean_object* v_e_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_, lean_object* v_a_3543_){
_start:
{
lean_object* v_res_3544_; 
v_res_3544_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep(v_e_3533_, v_a_3534_, v_a_3535_, v_a_3536_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_);
lean_dec(v_a_3542_);
lean_dec_ref(v_a_3541_);
lean_dec(v_a_3540_);
lean_dec_ref(v_a_3539_);
lean_dec(v_a_3538_);
lean_dec_ref(v_a_3537_);
lean_dec(v_a_3536_);
lean_dec_ref(v_a_3535_);
lean_dec(v_a_3534_);
return v_res_3544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPre(lean_object* v_simprocs_3545_, lean_object* v_a_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_, lean_object* v_a_3554_, lean_object* v_a_3555_){
_start:
{
lean_object* v___y_3558_; lean_object* v___y_3559_; uint8_t v___y_3560_; lean_object* v___x_3563_; 
lean_inc_ref(v_a_3546_);
v___x_3563_ = l_Lean_Meta_Tactic_Cbv_isBuiltinValue___redArg(v_a_3546_);
if (lean_obj_tag(v___x_3563_) == 0)
{
lean_object* v_a_3564_; 
v_a_3564_ = lean_ctor_get(v___x_3563_, 0);
lean_inc(v_a_3564_);
if (lean_obj_tag(v_a_3564_) == 0)
{
uint8_t v_done_3565_; uint8_t v_contextDependent_3566_; lean_object* v___y_3568_; lean_object* v_a_3569_; lean_object* v___y_3573_; lean_object* v___y_3574_; uint8_t v___y_3575_; lean_object* v___y_3579_; 
v_done_3565_ = lean_ctor_get_uint8(v_a_3564_, 0);
v_contextDependent_3566_ = lean_ctor_get_uint8(v_a_3564_, 1);
lean_dec_ref_known(v_a_3564_, 0);
if (v_done_3565_ == 0)
{
lean_object* v___x_3581_; 
lean_dec_ref_known(v___x_3563_, 1);
lean_inc_ref(v_a_3546_);
v___x_3581_ = l_Lean_Meta_Tactic_Cbv_isProofTerm___redArg(v_a_3546_, v_a_3550_, v_a_3551_, v_a_3552_, v_a_3553_, v_a_3554_, v_a_3555_);
if (lean_obj_tag(v___x_3581_) == 0)
{
lean_object* v_a_3582_; 
v_a_3582_ = lean_ctor_get(v___x_3581_, 0);
lean_inc(v_a_3582_);
if (lean_obj_tag(v_a_3582_) == 0)
{
uint8_t v_done_3583_; uint8_t v_contextDependent_3584_; lean_object* v___y_3586_; lean_object* v_a_3587_; lean_object* v___y_3591_; 
v_done_3583_ = lean_ctor_get_uint8(v_a_3582_, 0);
v_contextDependent_3584_ = lean_ctor_get_uint8(v_a_3582_, 1);
lean_dec_ref_known(v_a_3582_, 0);
if (v_done_3583_ == 0)
{
lean_object* v_pre_3593_; lean_object* v_erased_3594_; lean_object* v___x_3595_; 
lean_dec_ref_known(v___x_3581_, 1);
v_pre_3593_ = lean_ctor_get(v_simprocs_3545_, 0);
v_erased_3594_ = lean_ctor_get(v_simprocs_3545_, 4);
lean_inc_ref(v_a_3546_);
v___x_3595_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch(v_pre_3593_, v_erased_3594_, v_a_3546_, v_a_3547_, v_a_3548_, v_a_3549_, v_a_3550_, v_a_3551_, v_a_3552_, v_a_3553_, v_a_3554_, v_a_3555_);
if (lean_obj_tag(v___x_3595_) == 0)
{
lean_object* v_a_3596_; 
v_a_3596_ = lean_ctor_get(v___x_3595_, 0);
lean_inc(v_a_3596_);
if (lean_obj_tag(v_a_3596_) == 0)
{
uint8_t v_done_3597_; 
v_done_3597_ = lean_ctor_get_uint8(v_a_3596_, 0);
if (v_done_3597_ == 0)
{
uint8_t v_contextDependent_3598_; lean_object* v___x_3599_; 
lean_dec_ref_known(v___x_3595_, 1);
v_contextDependent_3598_ = lean_ctor_get_uint8(v_a_3596_, 1);
lean_dec_ref_known(v_a_3596_, 0);
v___x_3599_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep(v_a_3546_, v_a_3547_, v_a_3548_, v_a_3549_, v_a_3550_, v_a_3551_, v_a_3552_, v_a_3553_, v_a_3554_, v_a_3555_);
if (lean_obj_tag(v___x_3599_) == 0)
{
lean_object* v_a_3600_; uint8_t v___y_3602_; 
v_a_3600_ = lean_ctor_get(v___x_3599_, 0);
lean_inc(v_a_3600_);
if (v_contextDependent_3598_ == 0)
{
lean_dec(v_a_3600_);
v___y_3591_ = v___x_3599_;
goto v___jp_3590_;
}
else
{
if (lean_obj_tag(v_a_3600_) == 0)
{
uint8_t v_contextDependent_3612_; 
v_contextDependent_3612_ = lean_ctor_get_uint8(v_a_3600_, 1);
v___y_3602_ = v_contextDependent_3612_;
goto v___jp_3601_;
}
else
{
uint8_t v_contextDependent_3613_; 
v_contextDependent_3613_ = lean_ctor_get_uint8(v_a_3600_, sizeof(void*)*2 + 1);
v___y_3602_ = v_contextDependent_3613_;
goto v___jp_3601_;
}
}
v___jp_3601_:
{
if (v___y_3602_ == 0)
{
lean_object* v___x_3604_; uint8_t v_isShared_3605_; uint8_t v_isSharedCheck_3610_; 
v_isSharedCheck_3610_ = !lean_is_exclusive(v___x_3599_);
if (v_isSharedCheck_3610_ == 0)
{
lean_object* v_unused_3611_; 
v_unused_3611_ = lean_ctor_get(v___x_3599_, 0);
lean_dec(v_unused_3611_);
v___x_3604_ = v___x_3599_;
v_isShared_3605_ = v_isSharedCheck_3610_;
goto v_resetjp_3603_;
}
else
{
lean_dec(v___x_3599_);
v___x_3604_ = lean_box(0);
v_isShared_3605_ = v_isSharedCheck_3610_;
goto v_resetjp_3603_;
}
v_resetjp_3603_:
{
lean_object* v___x_3606_; lean_object* v___x_3608_; 
v___x_3606_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3600_);
lean_inc_ref(v___x_3606_);
if (v_isShared_3605_ == 0)
{
lean_ctor_set(v___x_3604_, 0, v___x_3606_);
v___x_3608_ = v___x_3604_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v___x_3606_);
v___x_3608_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
v___y_3586_ = v___x_3608_;
v_a_3587_ = v___x_3606_;
goto v___jp_3585_;
}
}
}
else
{
lean_dec(v_a_3600_);
v___y_3591_ = v___x_3599_;
goto v___jp_3590_;
}
}
}
else
{
v___y_3591_ = v___x_3599_;
goto v___jp_3590_;
}
}
else
{
lean_dec_ref_known(v_a_3596_, 0);
lean_dec_ref(v_a_3546_);
v___y_3591_ = v___x_3595_;
goto v___jp_3590_;
}
}
else
{
lean_dec_ref_known(v_a_3596_, 2);
lean_dec_ref(v_a_3546_);
v___y_3591_ = v___x_3595_;
goto v___jp_3590_;
}
}
else
{
lean_dec_ref(v_a_3546_);
v___y_3591_ = v___x_3595_;
goto v___jp_3590_;
}
}
else
{
lean_dec_ref(v_a_3546_);
v___y_3579_ = v___x_3581_;
goto v___jp_3578_;
}
v___jp_3585_:
{
if (v_contextDependent_3584_ == 0)
{
v___y_3568_ = v___y_3586_;
v_a_3569_ = v_a_3587_;
goto v___jp_3567_;
}
else
{
if (lean_obj_tag(v_a_3587_) == 0)
{
uint8_t v_contextDependent_3588_; 
v_contextDependent_3588_ = lean_ctor_get_uint8(v_a_3587_, 1);
v___y_3573_ = v___y_3586_;
v___y_3574_ = v_a_3587_;
v___y_3575_ = v_contextDependent_3588_;
goto v___jp_3572_;
}
else
{
uint8_t v_contextDependent_3589_; 
v_contextDependent_3589_ = lean_ctor_get_uint8(v_a_3587_, sizeof(void*)*2 + 1);
v___y_3573_ = v___y_3586_;
v___y_3574_ = v_a_3587_;
v___y_3575_ = v_contextDependent_3589_;
goto v___jp_3572_;
}
}
}
v___jp_3590_:
{
if (lean_obj_tag(v___y_3591_) == 0)
{
lean_object* v_a_3592_; 
v_a_3592_ = lean_ctor_get(v___y_3591_, 0);
lean_inc(v_a_3592_);
v___y_3586_ = v___y_3591_;
v_a_3587_ = v_a_3592_;
goto v___jp_3585_;
}
else
{
return v___y_3591_;
}
}
}
else
{
lean_dec_ref_known(v_a_3582_, 2);
lean_dec_ref(v_a_3546_);
v___y_3579_ = v___x_3581_;
goto v___jp_3578_;
}
}
else
{
lean_dec_ref(v_a_3546_);
v___y_3579_ = v___x_3581_;
goto v___jp_3578_;
}
}
else
{
lean_dec_ref(v_a_3546_);
return v___x_3563_;
}
v___jp_3567_:
{
if (v_contextDependent_3566_ == 0)
{
lean_dec_ref(v_a_3569_);
return v___y_3568_;
}
else
{
if (lean_obj_tag(v_a_3569_) == 0)
{
uint8_t v_contextDependent_3570_; 
v_contextDependent_3570_ = lean_ctor_get_uint8(v_a_3569_, 1);
v___y_3558_ = v___y_3568_;
v___y_3559_ = v_a_3569_;
v___y_3560_ = v_contextDependent_3570_;
goto v___jp_3557_;
}
else
{
uint8_t v_contextDependent_3571_; 
v_contextDependent_3571_ = lean_ctor_get_uint8(v_a_3569_, sizeof(void*)*2 + 1);
v___y_3558_ = v___y_3568_;
v___y_3559_ = v_a_3569_;
v___y_3560_ = v_contextDependent_3571_;
goto v___jp_3557_;
}
}
}
v___jp_3572_:
{
if (v___y_3575_ == 0)
{
lean_object* v___x_3576_; lean_object* v___x_3577_; 
lean_dec_ref(v___y_3573_);
v___x_3576_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_3574_);
lean_inc_ref(v___x_3576_);
v___x_3577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3577_, 0, v___x_3576_);
v___y_3568_ = v___x_3577_;
v_a_3569_ = v___x_3576_;
goto v___jp_3567_;
}
else
{
v___y_3568_ = v___y_3573_;
v_a_3569_ = v___y_3574_;
goto v___jp_3567_;
}
}
v___jp_3578_:
{
if (lean_obj_tag(v___y_3579_) == 0)
{
lean_object* v_a_3580_; 
v_a_3580_ = lean_ctor_get(v___y_3579_, 0);
lean_inc(v_a_3580_);
v___y_3568_ = v___y_3579_;
v_a_3569_ = v_a_3580_;
goto v___jp_3567_;
}
else
{
return v___y_3579_;
}
}
}
else
{
lean_dec_ref_known(v_a_3564_, 2);
lean_dec_ref(v_a_3546_);
return v___x_3563_;
}
}
else
{
lean_dec_ref(v_a_3546_);
return v___x_3563_;
}
v___jp_3557_:
{
if (v___y_3560_ == 0)
{
lean_object* v___x_3561_; lean_object* v___x_3562_; 
lean_dec_ref(v___y_3558_);
v___x_3561_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_3559_);
v___x_3562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3562_, 0, v___x_3561_);
return v___x_3562_;
}
else
{
lean_dec_ref(v___y_3559_);
return v___y_3558_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPre___boxed(lean_object* v_simprocs_3614_, lean_object* v_a_3615_, lean_object* v_a_3616_, lean_object* v_a_3617_, lean_object* v_a_3618_, lean_object* v_a_3619_, lean_object* v_a_3620_, lean_object* v_a_3621_, lean_object* v_a_3622_, lean_object* v_a_3623_, lean_object* v_a_3624_, lean_object* v_a_3625_){
_start:
{
lean_object* v_res_3626_; 
v_res_3626_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPre(v_simprocs_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_);
lean_dec(v_a_3624_);
lean_dec_ref(v_a_3623_);
lean_dec(v_a_3622_);
lean_dec_ref(v_a_3621_);
lean_dec(v_a_3620_);
lean_dec_ref(v_a_3619_);
lean_dec(v_a_3618_);
lean_dec_ref(v_a_3617_);
lean_dec(v_a_3616_);
lean_dec_ref(v_simprocs_3614_);
return v_res_3626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPost(lean_object* v_simprocs_3627_, lean_object* v_a_3628_, lean_object* v_a_3629_, lean_object* v_a_3630_, lean_object* v_a_3631_, lean_object* v_a_3632_, lean_object* v_a_3633_, lean_object* v_a_3634_, lean_object* v_a_3635_, lean_object* v_a_3636_, lean_object* v_a_3637_){
_start:
{
lean_object* v___y_3640_; lean_object* v___y_3641_; uint8_t v___y_3642_; lean_object* v___x_3645_; lean_object* v___x_3646_; 
v___x_3645_ = lean_unsigned_to_nat(255u);
lean_inc_ref(v_a_3628_);
v___x_3646_ = l_Lean_Meta_Sym_Simp_evalGround___redArg(v___x_3645_, v_a_3628_, v_a_3632_, v_a_3633_, v_a_3634_, v_a_3635_, v_a_3636_, v_a_3637_);
if (lean_obj_tag(v___x_3646_) == 0)
{
lean_object* v_a_3647_; 
v_a_3647_ = lean_ctor_get(v___x_3646_, 0);
lean_inc(v_a_3647_);
if (lean_obj_tag(v_a_3647_) == 0)
{
uint8_t v_done_3648_; uint8_t v_contextDependent_3649_; lean_object* v___y_3651_; lean_object* v_a_3652_; lean_object* v___y_3656_; lean_object* v___y_3657_; uint8_t v___y_3658_; lean_object* v___y_3662_; 
v_done_3648_ = lean_ctor_get_uint8(v_a_3647_, 0);
v_contextDependent_3649_ = lean_ctor_get_uint8(v_a_3647_, 1);
lean_dec_ref_known(v_a_3647_, 0);
if (v_done_3648_ == 0)
{
lean_object* v_eval_3664_; lean_object* v_post_3665_; lean_object* v_erased_3666_; lean_object* v___x_3667_; 
lean_dec_ref_known(v___x_3646_, 1);
v_eval_3664_ = lean_ctor_get(v_simprocs_3627_, 1);
v_post_3665_ = lean_ctor_get(v_simprocs_3627_, 2);
v_erased_3666_ = lean_ctor_get(v_simprocs_3627_, 4);
lean_inc_ref(v_a_3628_);
v___x_3667_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch(v_eval_3664_, v_erased_3666_, v_a_3628_, v_a_3629_, v_a_3630_, v_a_3631_, v_a_3632_, v_a_3633_, v_a_3634_, v_a_3635_, v_a_3636_, v_a_3637_);
if (lean_obj_tag(v___x_3667_) == 0)
{
lean_object* v_a_3668_; 
v_a_3668_ = lean_ctor_get(v___x_3667_, 0);
lean_inc(v_a_3668_);
if (lean_obj_tag(v_a_3668_) == 0)
{
uint8_t v_done_3669_; uint8_t v_contextDependent_3670_; lean_object* v___y_3672_; lean_object* v_a_3673_; lean_object* v___y_3677_; 
v_done_3669_ = lean_ctor_get_uint8(v_a_3668_, 0);
v_contextDependent_3670_ = lean_ctor_get_uint8(v_a_3668_, 1);
lean_dec_ref_known(v_a_3668_, 0);
if (v_done_3669_ == 0)
{
lean_object* v___x_3679_; 
lean_dec_ref_known(v___x_3667_, 1);
lean_inc_ref(v_a_3628_);
v___x_3679_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp(v_a_3628_, v_a_3629_, v_a_3630_, v_a_3631_, v_a_3632_, v_a_3633_, v_a_3634_, v_a_3635_, v_a_3636_, v_a_3637_);
if (lean_obj_tag(v___x_3679_) == 0)
{
lean_object* v_a_3680_; 
v_a_3680_ = lean_ctor_get(v___x_3679_, 0);
lean_inc(v_a_3680_);
if (lean_obj_tag(v_a_3680_) == 0)
{
uint8_t v_done_3681_; 
v_done_3681_ = lean_ctor_get_uint8(v_a_3680_, 0);
if (v_done_3681_ == 0)
{
uint8_t v_contextDependent_3682_; lean_object* v___x_3683_; 
lean_dec_ref_known(v___x_3679_, 1);
v_contextDependent_3682_ = lean_ctor_get_uint8(v_a_3680_, 1);
lean_dec_ref_known(v_a_3680_, 0);
v___x_3683_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch(v_post_3665_, v_erased_3666_, v_a_3628_, v_a_3629_, v_a_3630_, v_a_3631_, v_a_3632_, v_a_3633_, v_a_3634_, v_a_3635_, v_a_3636_, v_a_3637_);
if (lean_obj_tag(v___x_3683_) == 0)
{
lean_object* v_a_3684_; uint8_t v___y_3686_; 
v_a_3684_ = lean_ctor_get(v___x_3683_, 0);
lean_inc(v_a_3684_);
if (v_contextDependent_3682_ == 0)
{
lean_dec(v_a_3684_);
v___y_3677_ = v___x_3683_;
goto v___jp_3676_;
}
else
{
if (lean_obj_tag(v_a_3684_) == 0)
{
uint8_t v_contextDependent_3696_; 
v_contextDependent_3696_ = lean_ctor_get_uint8(v_a_3684_, 1);
v___y_3686_ = v_contextDependent_3696_;
goto v___jp_3685_;
}
else
{
uint8_t v_contextDependent_3697_; 
v_contextDependent_3697_ = lean_ctor_get_uint8(v_a_3684_, sizeof(void*)*2 + 1);
v___y_3686_ = v_contextDependent_3697_;
goto v___jp_3685_;
}
}
v___jp_3685_:
{
if (v___y_3686_ == 0)
{
lean_object* v___x_3688_; uint8_t v_isShared_3689_; uint8_t v_isSharedCheck_3694_; 
v_isSharedCheck_3694_ = !lean_is_exclusive(v___x_3683_);
if (v_isSharedCheck_3694_ == 0)
{
lean_object* v_unused_3695_; 
v_unused_3695_ = lean_ctor_get(v___x_3683_, 0);
lean_dec(v_unused_3695_);
v___x_3688_ = v___x_3683_;
v_isShared_3689_ = v_isSharedCheck_3694_;
goto v_resetjp_3687_;
}
else
{
lean_dec(v___x_3683_);
v___x_3688_ = lean_box(0);
v_isShared_3689_ = v_isSharedCheck_3694_;
goto v_resetjp_3687_;
}
v_resetjp_3687_:
{
lean_object* v___x_3690_; lean_object* v___x_3692_; 
v___x_3690_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3684_);
lean_inc_ref(v___x_3690_);
if (v_isShared_3689_ == 0)
{
lean_ctor_set(v___x_3688_, 0, v___x_3690_);
v___x_3692_ = v___x_3688_;
goto v_reusejp_3691_;
}
else
{
lean_object* v_reuseFailAlloc_3693_; 
v_reuseFailAlloc_3693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3693_, 0, v___x_3690_);
v___x_3692_ = v_reuseFailAlloc_3693_;
goto v_reusejp_3691_;
}
v_reusejp_3691_:
{
v___y_3672_ = v___x_3692_;
v_a_3673_ = v___x_3690_;
goto v___jp_3671_;
}
}
}
else
{
lean_dec(v_a_3684_);
v___y_3677_ = v___x_3683_;
goto v___jp_3676_;
}
}
}
else
{
v___y_3677_ = v___x_3683_;
goto v___jp_3676_;
}
}
else
{
lean_dec_ref_known(v_a_3680_, 0);
lean_dec_ref(v_a_3628_);
v___y_3677_ = v___x_3679_;
goto v___jp_3676_;
}
}
else
{
lean_dec_ref_known(v_a_3680_, 2);
lean_dec_ref(v_a_3628_);
v___y_3677_ = v___x_3679_;
goto v___jp_3676_;
}
}
else
{
lean_dec_ref(v_a_3628_);
v___y_3677_ = v___x_3679_;
goto v___jp_3676_;
}
}
else
{
lean_dec_ref(v_a_3628_);
v___y_3662_ = v___x_3667_;
goto v___jp_3661_;
}
v___jp_3671_:
{
if (v_contextDependent_3670_ == 0)
{
v___y_3651_ = v___y_3672_;
v_a_3652_ = v_a_3673_;
goto v___jp_3650_;
}
else
{
if (lean_obj_tag(v_a_3673_) == 0)
{
uint8_t v_contextDependent_3674_; 
v_contextDependent_3674_ = lean_ctor_get_uint8(v_a_3673_, 1);
v___y_3656_ = v___y_3672_;
v___y_3657_ = v_a_3673_;
v___y_3658_ = v_contextDependent_3674_;
goto v___jp_3655_;
}
else
{
uint8_t v_contextDependent_3675_; 
v_contextDependent_3675_ = lean_ctor_get_uint8(v_a_3673_, sizeof(void*)*2 + 1);
v___y_3656_ = v___y_3672_;
v___y_3657_ = v_a_3673_;
v___y_3658_ = v_contextDependent_3675_;
goto v___jp_3655_;
}
}
}
v___jp_3676_:
{
if (lean_obj_tag(v___y_3677_) == 0)
{
lean_object* v_a_3678_; 
v_a_3678_ = lean_ctor_get(v___y_3677_, 0);
lean_inc(v_a_3678_);
v___y_3672_ = v___y_3677_;
v_a_3673_ = v_a_3678_;
goto v___jp_3671_;
}
else
{
return v___y_3677_;
}
}
}
else
{
lean_dec_ref_known(v_a_3668_, 2);
lean_dec_ref(v_a_3628_);
v___y_3662_ = v___x_3667_;
goto v___jp_3661_;
}
}
else
{
lean_dec_ref(v_a_3628_);
v___y_3662_ = v___x_3667_;
goto v___jp_3661_;
}
}
else
{
lean_dec_ref(v_a_3628_);
return v___x_3646_;
}
v___jp_3650_:
{
if (v_contextDependent_3649_ == 0)
{
lean_dec_ref(v_a_3652_);
return v___y_3651_;
}
else
{
if (lean_obj_tag(v_a_3652_) == 0)
{
uint8_t v_contextDependent_3653_; 
v_contextDependent_3653_ = lean_ctor_get_uint8(v_a_3652_, 1);
v___y_3640_ = v___y_3651_;
v___y_3641_ = v_a_3652_;
v___y_3642_ = v_contextDependent_3653_;
goto v___jp_3639_;
}
else
{
uint8_t v_contextDependent_3654_; 
v_contextDependent_3654_ = lean_ctor_get_uint8(v_a_3652_, sizeof(void*)*2 + 1);
v___y_3640_ = v___y_3651_;
v___y_3641_ = v_a_3652_;
v___y_3642_ = v_contextDependent_3654_;
goto v___jp_3639_;
}
}
}
v___jp_3655_:
{
if (v___y_3658_ == 0)
{
lean_object* v___x_3659_; lean_object* v___x_3660_; 
lean_dec_ref(v___y_3656_);
v___x_3659_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_3657_);
lean_inc_ref(v___x_3659_);
v___x_3660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3660_, 0, v___x_3659_);
v___y_3651_ = v___x_3660_;
v_a_3652_ = v___x_3659_;
goto v___jp_3650_;
}
else
{
v___y_3651_ = v___y_3656_;
v_a_3652_ = v___y_3657_;
goto v___jp_3650_;
}
}
v___jp_3661_:
{
if (lean_obj_tag(v___y_3662_) == 0)
{
lean_object* v_a_3663_; 
v_a_3663_ = lean_ctor_get(v___y_3662_, 0);
lean_inc(v_a_3663_);
v___y_3651_ = v___y_3662_;
v_a_3652_ = v_a_3663_;
goto v___jp_3650_;
}
else
{
return v___y_3662_;
}
}
}
else
{
lean_dec_ref_known(v_a_3647_, 2);
lean_dec_ref(v_a_3628_);
return v___x_3646_;
}
}
else
{
lean_dec_ref(v_a_3628_);
return v___x_3646_;
}
v___jp_3639_:
{
if (v___y_3642_ == 0)
{
lean_object* v___x_3643_; lean_object* v___x_3644_; 
lean_dec_ref(v___y_3640_);
v___x_3643_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_3641_);
v___x_3644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3644_, 0, v___x_3643_);
return v___x_3644_;
}
else
{
lean_dec_ref(v___y_3641_);
return v___y_3640_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPost___boxed(lean_object* v_simprocs_3698_, lean_object* v_a_3699_, lean_object* v_a_3700_, lean_object* v_a_3701_, lean_object* v_a_3702_, lean_object* v_a_3703_, lean_object* v_a_3704_, lean_object* v_a_3705_, lean_object* v_a_3706_, lean_object* v_a_3707_, lean_object* v_a_3708_, lean_object* v_a_3709_){
_start:
{
lean_object* v_res_3710_; 
v_res_3710_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPost(v_simprocs_3698_, v_a_3699_, v_a_3700_, v_a_3701_, v_a_3702_, v_a_3703_, v_a_3704_, v_a_3705_, v_a_3706_, v_a_3707_, v_a_3708_);
lean_dec(v_a_3708_);
lean_dec_ref(v_a_3707_);
lean_dec(v_a_3706_);
lean_dec_ref(v_a_3705_);
lean_dec(v_a_3704_);
lean_dec_ref(v_a_3703_);
lean_dec(v_a_3702_);
lean_dec_ref(v_a_3701_);
lean_dec(v_a_3700_);
lean_dec_ref(v_simprocs_3698_);
return v_res_3710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(lean_object* v_simprocs_3711_){
_start:
{
lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; 
lean_inc_ref(v_simprocs_3711_);
v___x_3712_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPre___boxed), 12, 1);
lean_closure_set(v___x_3712_, 0, v_simprocs_3711_);
v___x_3713_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPost___boxed), 12, 1);
lean_closure_set(v___x_3713_, 0, v_simprocs_3711_);
v___x_3714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3714_, 0, v___x_3712_);
lean_ctor_set(v___x_3714_, 1, v___x_3713_);
return v___x_3714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0___redArg(lean_object* v_x_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_){
_start:
{
lean_object* v_config_3723_; lean_object* v_sharedExprs_3724_; uint8_t v_verbose_3725_; uint8_t v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; 
v_config_3723_ = lean_ctor_get(v___y_3716_, 1);
v_sharedExprs_3724_ = lean_ctor_get(v___y_3716_, 0);
v_verbose_3725_ = lean_ctor_get_uint8(v_config_3723_, 0);
v___x_3726_ = 0;
v___x_3727_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v___x_3727_, 0, v_verbose_3725_);
lean_ctor_set_uint8(v___x_3727_, 1, v___x_3726_);
lean_ctor_set_uint8(v___x_3727_, 2, v___x_3726_);
lean_inc_ref(v_sharedExprs_3724_);
v___x_3728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3728_, 0, v_sharedExprs_3724_);
lean_ctor_set(v___x_3728_, 1, v___x_3727_);
lean_inc(v___y_3721_);
lean_inc_ref(v___y_3720_);
lean_inc(v___y_3719_);
lean_inc_ref(v___y_3718_);
lean_inc(v___y_3717_);
v___x_3729_ = lean_apply_7(v_x_3715_, v___x_3728_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_, v___y_3721_, lean_box(0));
return v___x_3729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0___redArg___boxed(lean_object* v_x_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_){
_start:
{
lean_object* v_res_3738_; 
v_res_3738_ = l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0___redArg(v_x_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_);
lean_dec(v___y_3736_);
lean_dec_ref(v___y_3735_);
lean_dec(v___y_3734_);
lean_dec_ref(v___y_3733_);
lean_dec(v___y_3732_);
lean_dec_ref(v___y_3731_);
return v_res_3738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0(lean_object* v_00_u03b1_3739_, lean_object* v_x_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_){
_start:
{
lean_object* v___x_3748_; 
v___x_3748_ = l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0___redArg(v_x_3740_, v___y_3741_, v___y_3742_, v___y_3743_, v___y_3744_, v___y_3745_, v___y_3746_);
return v___x_3748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0___boxed(lean_object* v_00_u03b1_3749_, lean_object* v_x_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_){
_start:
{
lean_object* v_res_3758_; 
v_res_3758_ = l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0(v_00_u03b1_3749_, v_x_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_);
lean_dec(v___y_3756_);
lean_dec_ref(v___y_3755_);
lean_dec(v___y_3754_);
lean_dec_ref(v___y_3753_);
lean_dec(v___y_3752_);
lean_dec_ref(v___y_3751_);
return v_res_3758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore___lam__0(lean_object* v_e_3759_, lean_object* v_config_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_){
_start:
{
lean_object* v___x_3768_; 
v___x_3768_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v___y_3766_);
if (lean_obj_tag(v___x_3768_) == 0)
{
lean_object* v_a_3769_; lean_object* v_methods_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; 
v_a_3769_ = lean_ctor_get(v___x_3768_, 0);
lean_inc(v_a_3769_);
lean_dec_ref_known(v___x_3768_, 1);
v_methods_3770_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(v_a_3769_);
v___x_3771_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_3771_, 0, v_e_3759_);
v___x_3772_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v___x_3771_, v_methods_3770_, v_config_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_);
return v___x_3772_;
}
else
{
lean_object* v_a_3773_; lean_object* v___x_3775_; uint8_t v_isShared_3776_; uint8_t v_isSharedCheck_3780_; 
lean_dec_ref(v_config_3760_);
lean_dec_ref(v_e_3759_);
v_a_3773_ = lean_ctor_get(v___x_3768_, 0);
v_isSharedCheck_3780_ = !lean_is_exclusive(v___x_3768_);
if (v_isSharedCheck_3780_ == 0)
{
v___x_3775_ = v___x_3768_;
v_isShared_3776_ = v_isSharedCheck_3780_;
goto v_resetjp_3774_;
}
else
{
lean_inc(v_a_3773_);
lean_dec(v___x_3768_);
v___x_3775_ = lean_box(0);
v_isShared_3776_ = v_isSharedCheck_3780_;
goto v_resetjp_3774_;
}
v_resetjp_3774_:
{
lean_object* v___x_3778_; 
if (v_isShared_3776_ == 0)
{
v___x_3778_ = v___x_3775_;
goto v_reusejp_3777_;
}
else
{
lean_object* v_reuseFailAlloc_3779_; 
v_reuseFailAlloc_3779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3779_, 0, v_a_3773_);
v___x_3778_ = v_reuseFailAlloc_3779_;
goto v_reusejp_3777_;
}
v_reusejp_3777_:
{
return v___x_3778_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore___lam__0___boxed(lean_object* v_e_3781_, lean_object* v_config_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_){
_start:
{
lean_object* v_res_3790_; 
v_res_3790_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore___lam__0(v_e_3781_, v_config_3782_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_);
lean_dec(v___y_3788_);
lean_dec_ref(v___y_3787_);
lean_dec(v___y_3786_);
lean_dec_ref(v___y_3785_);
lean_dec(v___y_3784_);
lean_dec_ref(v___y_3783_);
return v_res_3790_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(lean_object* v_e_3791_, lean_object* v_config_3792_, lean_object* v_a_3793_, lean_object* v_a_3794_, lean_object* v_a_3795_, lean_object* v_a_3796_, lean_object* v_a_3797_, lean_object* v_a_3798_){
_start:
{
lean_object* v___f_3800_; lean_object* v___x_3801_; 
v___f_3800_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore___lam__0___boxed), 9, 2);
lean_closure_set(v___f_3800_, 0, v_e_3791_);
lean_closure_set(v___f_3800_, 1, v_config_3792_);
v___x_3801_ = l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0___redArg(v___f_3800_, v_a_3793_, v_a_3794_, v_a_3795_, v_a_3796_, v_a_3797_, v_a_3798_);
return v___x_3801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore___boxed(lean_object* v_e_3802_, lean_object* v_config_3803_, lean_object* v_a_3804_, lean_object* v_a_3805_, lean_object* v_a_3806_, lean_object* v_a_3807_, lean_object* v_a_3808_, lean_object* v_a_3809_, lean_object* v_a_3810_){
_start:
{
lean_object* v_res_3811_; 
v_res_3811_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v_e_3802_, v_config_3803_, v_a_3804_, v_a_3805_, v_a_3806_, v_a_3807_, v_a_3808_, v_a_3809_);
lean_dec(v_a_3809_);
lean_dec_ref(v_a_3808_);
lean_dec(v_a_3807_);
lean_dec_ref(v_a_3806_);
lean_dec(v_a_3805_);
lean_dec_ref(v_a_3804_);
return v_res_3811_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg(lean_object* v___y_3812_){
_start:
{
lean_object* v___x_3814_; lean_object* v_traceState_3815_; lean_object* v_traces_3816_; lean_object* v___x_3817_; lean_object* v_traceState_3818_; lean_object* v_env_3819_; lean_object* v_nextMacroScope_3820_; lean_object* v_ngen_3821_; lean_object* v_auxDeclNGen_3822_; lean_object* v_cache_3823_; lean_object* v_messages_3824_; lean_object* v_infoState_3825_; lean_object* v_snapshotTasks_3826_; lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_3847_; 
v___x_3814_ = lean_st_ref_get(v___y_3812_);
v_traceState_3815_ = lean_ctor_get(v___x_3814_, 4);
lean_inc_ref(v_traceState_3815_);
lean_dec(v___x_3814_);
v_traces_3816_ = lean_ctor_get(v_traceState_3815_, 0);
lean_inc_ref(v_traces_3816_);
lean_dec_ref(v_traceState_3815_);
v___x_3817_ = lean_st_ref_take(v___y_3812_);
v_traceState_3818_ = lean_ctor_get(v___x_3817_, 4);
v_env_3819_ = lean_ctor_get(v___x_3817_, 0);
v_nextMacroScope_3820_ = lean_ctor_get(v___x_3817_, 1);
v_ngen_3821_ = lean_ctor_get(v___x_3817_, 2);
v_auxDeclNGen_3822_ = lean_ctor_get(v___x_3817_, 3);
v_cache_3823_ = lean_ctor_get(v___x_3817_, 5);
v_messages_3824_ = lean_ctor_get(v___x_3817_, 6);
v_infoState_3825_ = lean_ctor_get(v___x_3817_, 7);
v_snapshotTasks_3826_ = lean_ctor_get(v___x_3817_, 8);
v_isSharedCheck_3847_ = !lean_is_exclusive(v___x_3817_);
if (v_isSharedCheck_3847_ == 0)
{
v___x_3828_ = v___x_3817_;
v_isShared_3829_ = v_isSharedCheck_3847_;
goto v_resetjp_3827_;
}
else
{
lean_inc(v_snapshotTasks_3826_);
lean_inc(v_infoState_3825_);
lean_inc(v_messages_3824_);
lean_inc(v_cache_3823_);
lean_inc(v_traceState_3818_);
lean_inc(v_auxDeclNGen_3822_);
lean_inc(v_ngen_3821_);
lean_inc(v_nextMacroScope_3820_);
lean_inc(v_env_3819_);
lean_dec(v___x_3817_);
v___x_3828_ = lean_box(0);
v_isShared_3829_ = v_isSharedCheck_3847_;
goto v_resetjp_3827_;
}
v_resetjp_3827_:
{
uint64_t v_tid_3830_; lean_object* v___x_3832_; uint8_t v_isShared_3833_; uint8_t v_isSharedCheck_3845_; 
v_tid_3830_ = lean_ctor_get_uint64(v_traceState_3818_, sizeof(void*)*1);
v_isSharedCheck_3845_ = !lean_is_exclusive(v_traceState_3818_);
if (v_isSharedCheck_3845_ == 0)
{
lean_object* v_unused_3846_; 
v_unused_3846_ = lean_ctor_get(v_traceState_3818_, 0);
lean_dec(v_unused_3846_);
v___x_3832_ = v_traceState_3818_;
v_isShared_3833_ = v_isSharedCheck_3845_;
goto v_resetjp_3831_;
}
else
{
lean_dec(v_traceState_3818_);
v___x_3832_ = lean_box(0);
v_isShared_3833_ = v_isSharedCheck_3845_;
goto v_resetjp_3831_;
}
v_resetjp_3831_:
{
lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3838_; 
v___x_3834_ = lean_unsigned_to_nat(32u);
v___x_3835_ = lean_mk_empty_array_with_capacity(v___x_3834_);
lean_dec_ref(v___x_3835_);
v___x_3836_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1);
if (v_isShared_3833_ == 0)
{
lean_ctor_set(v___x_3832_, 0, v___x_3836_);
v___x_3838_ = v___x_3832_;
goto v_reusejp_3837_;
}
else
{
lean_object* v_reuseFailAlloc_3844_; 
v_reuseFailAlloc_3844_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3844_, 0, v___x_3836_);
lean_ctor_set_uint64(v_reuseFailAlloc_3844_, sizeof(void*)*1, v_tid_3830_);
v___x_3838_ = v_reuseFailAlloc_3844_;
goto v_reusejp_3837_;
}
v_reusejp_3837_:
{
lean_object* v___x_3840_; 
if (v_isShared_3829_ == 0)
{
lean_ctor_set(v___x_3828_, 4, v___x_3838_);
v___x_3840_ = v___x_3828_;
goto v_reusejp_3839_;
}
else
{
lean_object* v_reuseFailAlloc_3843_; 
v_reuseFailAlloc_3843_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3843_, 0, v_env_3819_);
lean_ctor_set(v_reuseFailAlloc_3843_, 1, v_nextMacroScope_3820_);
lean_ctor_set(v_reuseFailAlloc_3843_, 2, v_ngen_3821_);
lean_ctor_set(v_reuseFailAlloc_3843_, 3, v_auxDeclNGen_3822_);
lean_ctor_set(v_reuseFailAlloc_3843_, 4, v___x_3838_);
lean_ctor_set(v_reuseFailAlloc_3843_, 5, v_cache_3823_);
lean_ctor_set(v_reuseFailAlloc_3843_, 6, v_messages_3824_);
lean_ctor_set(v_reuseFailAlloc_3843_, 7, v_infoState_3825_);
lean_ctor_set(v_reuseFailAlloc_3843_, 8, v_snapshotTasks_3826_);
v___x_3840_ = v_reuseFailAlloc_3843_;
goto v_reusejp_3839_;
}
v_reusejp_3839_:
{
lean_object* v___x_3841_; lean_object* v___x_3842_; 
v___x_3841_ = lean_st_ref_set(v___y_3812_, v___x_3840_);
v___x_3842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3842_, 0, v_traces_3816_);
return v___x_3842_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg___boxed(lean_object* v___y_3848_, lean_object* v___y_3849_){
_start:
{
lean_object* v_res_3850_; 
v_res_3850_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg(v___y_3848_);
lean_dec(v___y_3848_);
return v_res_3850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0(lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_){
_start:
{
lean_object* v___x_3856_; 
v___x_3856_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg(v___y_3854_);
return v___x_3856_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___boxed(lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_){
_start:
{
lean_object* v_res_3862_; 
v_res_3862_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0(v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_);
lean_dec(v___y_3860_);
lean_dec_ref(v___y_3859_);
lean_dec(v___y_3858_);
lean_dec_ref(v___y_3857_);
return v_res_3862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0(lean_object* v_a_3863_, lean_object* v___x_3864_, lean_object* v___x_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_){
_start:
{
lean_object* v___x_3873_; 
v___x_3873_ = l_Lean_Meta_Sym_shareCommon(v_a_3863_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_);
if (lean_obj_tag(v___x_3873_) == 0)
{
lean_object* v_a_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; 
v_a_3874_ = lean_ctor_get(v___x_3873_, 0);
lean_inc(v_a_3874_);
lean_dec_ref_known(v___x_3873_, 1);
v___x_3875_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_3875_, 0, v_a_3874_);
v___x_3876_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v___x_3875_, v___x_3864_, v___x_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_);
return v___x_3876_;
}
else
{
lean_object* v_a_3877_; lean_object* v___x_3879_; uint8_t v_isShared_3880_; uint8_t v_isSharedCheck_3884_; 
lean_dec_ref(v___x_3865_);
lean_dec_ref(v___x_3864_);
v_a_3877_ = lean_ctor_get(v___x_3873_, 0);
v_isSharedCheck_3884_ = !lean_is_exclusive(v___x_3873_);
if (v_isSharedCheck_3884_ == 0)
{
v___x_3879_ = v___x_3873_;
v_isShared_3880_ = v_isSharedCheck_3884_;
goto v_resetjp_3878_;
}
else
{
lean_inc(v_a_3877_);
lean_dec(v___x_3873_);
v___x_3879_ = lean_box(0);
v_isShared_3880_ = v_isSharedCheck_3884_;
goto v_resetjp_3878_;
}
v_resetjp_3878_:
{
lean_object* v___x_3882_; 
if (v_isShared_3880_ == 0)
{
v___x_3882_ = v___x_3879_;
goto v_reusejp_3881_;
}
else
{
lean_object* v_reuseFailAlloc_3883_; 
v_reuseFailAlloc_3883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3883_, 0, v_a_3877_);
v___x_3882_ = v_reuseFailAlloc_3883_;
goto v_reusejp_3881_;
}
v_reusejp_3881_:
{
return v___x_3882_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___boxed(lean_object* v_a_3885_, lean_object* v___x_3886_, lean_object* v___x_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_){
_start:
{
lean_object* v_res_3895_; 
v_res_3895_ = l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0(v_a_3885_, v___x_3886_, v___x_3887_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
lean_dec(v___y_3893_);
lean_dec_ref(v___y_3892_);
lean_dec(v___y_3891_);
lean_dec_ref(v___y_3890_);
lean_dec(v___y_3889_);
lean_dec_ref(v___y_3888_);
return v_res_3895_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3897_; lean_object* v___x_3898_; 
v___x_3897_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__0));
v___x_3898_ = l_Lean_stringToMessageData(v___x_3897_);
return v___x_3898_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3900_; lean_object* v___x_3901_; 
v___x_3900_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__2));
v___x_3901_ = l_Lean_stringToMessageData(v___x_3900_);
return v___x_3901_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__5(void){
_start:
{
lean_object* v___x_3903_; lean_object* v___x_3904_; 
v___x_3903_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__4));
v___x_3904_ = l_Lean_stringToMessageData(v___x_3903_);
return v___x_3904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1(lean_object* v_e_3905_, lean_object* v_x_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_){
_start:
{
if (lean_obj_tag(v_x_3906_) == 0)
{
lean_object* v_a_3912_; lean_object* v___x_3914_; uint8_t v_isShared_3915_; uint8_t v_isSharedCheck_3922_; 
lean_dec_ref(v_e_3905_);
v_a_3912_ = lean_ctor_get(v_x_3906_, 0);
v_isSharedCheck_3922_ = !lean_is_exclusive(v_x_3906_);
if (v_isSharedCheck_3922_ == 0)
{
v___x_3914_ = v_x_3906_;
v_isShared_3915_ = v_isSharedCheck_3922_;
goto v_resetjp_3913_;
}
else
{
lean_inc(v_a_3912_);
lean_dec(v_x_3906_);
v___x_3914_ = lean_box(0);
v_isShared_3915_ = v_isSharedCheck_3922_;
goto v_resetjp_3913_;
}
v_resetjp_3913_:
{
lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3920_; 
v___x_3916_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__1);
v___x_3917_ = l_Lean_Exception_toMessageData(v_a_3912_);
v___x_3918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3918_, 0, v___x_3916_);
lean_ctor_set(v___x_3918_, 1, v___x_3917_);
if (v_isShared_3915_ == 0)
{
lean_ctor_set(v___x_3914_, 0, v___x_3918_);
v___x_3920_ = v___x_3914_;
goto v_reusejp_3919_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v___x_3918_);
v___x_3920_ = v_reuseFailAlloc_3921_;
goto v_reusejp_3919_;
}
v_reusejp_3919_:
{
return v___x_3920_;
}
}
}
else
{
lean_object* v_a_3923_; lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3944_; 
v_a_3923_ = lean_ctor_get(v_x_3906_, 0);
v_isSharedCheck_3944_ = !lean_is_exclusive(v_x_3906_);
if (v_isSharedCheck_3944_ == 0)
{
v___x_3925_ = v_x_3906_;
v_isShared_3926_ = v_isSharedCheck_3944_;
goto v_resetjp_3924_;
}
else
{
lean_inc(v_a_3923_);
lean_dec(v_x_3906_);
v___x_3925_ = lean_box(0);
v_isShared_3926_ = v_isSharedCheck_3944_;
goto v_resetjp_3924_;
}
v_resetjp_3924_:
{
if (lean_obj_tag(v_a_3923_) == 0)
{
lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3931_; 
lean_dec_ref_known(v_a_3923_, 0);
v___x_3927_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__3, &l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__3);
v___x_3928_ = l_Lean_indentExpr(v_e_3905_);
v___x_3929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3929_, 0, v___x_3927_);
lean_ctor_set(v___x_3929_, 1, v___x_3928_);
if (v_isShared_3926_ == 0)
{
lean_ctor_set_tag(v___x_3925_, 0);
lean_ctor_set(v___x_3925_, 0, v___x_3929_);
v___x_3931_ = v___x_3925_;
goto v_reusejp_3930_;
}
else
{
lean_object* v_reuseFailAlloc_3932_; 
v_reuseFailAlloc_3932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3932_, 0, v___x_3929_);
v___x_3931_ = v_reuseFailAlloc_3932_;
goto v_reusejp_3930_;
}
v_reusejp_3930_:
{
return v___x_3931_;
}
}
else
{
lean_object* v_e_x27_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3942_; 
v_e_x27_3933_ = lean_ctor_get(v_a_3923_, 0);
lean_inc_ref(v_e_x27_3933_);
lean_dec_ref_known(v_a_3923_, 2);
v___x_3934_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__5, &l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__5_once, _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__5);
v___x_3935_ = l_Lean_indentExpr(v_e_3905_);
v___x_3936_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3936_, 0, v___x_3934_);
lean_ctor_set(v___x_3936_, 1, v___x_3935_);
v___x_3937_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_3938_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3938_, 0, v___x_3936_);
lean_ctor_set(v___x_3938_, 1, v___x_3937_);
v___x_3939_ = l_Lean_indentExpr(v_e_x27_3933_);
v___x_3940_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3940_, 0, v___x_3938_);
lean_ctor_set(v___x_3940_, 1, v___x_3939_);
if (v_isShared_3926_ == 0)
{
lean_ctor_set_tag(v___x_3925_, 0);
lean_ctor_set(v___x_3925_, 0, v___x_3940_);
v___x_3942_ = v___x_3925_;
goto v_reusejp_3941_;
}
else
{
lean_object* v_reuseFailAlloc_3943_; 
v_reuseFailAlloc_3943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3943_, 0, v___x_3940_);
v___x_3942_ = v_reuseFailAlloc_3943_;
goto v_reusejp_3941_;
}
v_reusejp_3941_:
{
return v___x_3942_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___boxed(lean_object* v_e_3945_, lean_object* v_x_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_){
_start:
{
lean_object* v_res_3952_; 
v_res_3952_ = l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1(v_e_3945_, v_x_3946_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_);
lean_dec(v___y_3950_);
lean_dec_ref(v___y_3949_);
lean_dec(v___y_3948_);
lean_dec_ref(v___y_3947_);
return v_res_3952_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg(lean_object* v_x_3953_){
_start:
{
if (lean_obj_tag(v_x_3953_) == 0)
{
lean_object* v_a_3955_; lean_object* v___x_3957_; uint8_t v_isShared_3958_; uint8_t v_isSharedCheck_3962_; 
v_a_3955_ = lean_ctor_get(v_x_3953_, 0);
v_isSharedCheck_3962_ = !lean_is_exclusive(v_x_3953_);
if (v_isSharedCheck_3962_ == 0)
{
v___x_3957_ = v_x_3953_;
v_isShared_3958_ = v_isSharedCheck_3962_;
goto v_resetjp_3956_;
}
else
{
lean_inc(v_a_3955_);
lean_dec(v_x_3953_);
v___x_3957_ = lean_box(0);
v_isShared_3958_ = v_isSharedCheck_3962_;
goto v_resetjp_3956_;
}
v_resetjp_3956_:
{
lean_object* v___x_3960_; 
if (v_isShared_3958_ == 0)
{
lean_ctor_set_tag(v___x_3957_, 1);
v___x_3960_ = v___x_3957_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v_a_3955_);
v___x_3960_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3959_;
}
v_reusejp_3959_:
{
return v___x_3960_;
}
}
}
else
{
lean_object* v_a_3963_; lean_object* v___x_3965_; uint8_t v_isShared_3966_; uint8_t v_isSharedCheck_3970_; 
v_a_3963_ = lean_ctor_get(v_x_3953_, 0);
v_isSharedCheck_3970_ = !lean_is_exclusive(v_x_3953_);
if (v_isSharedCheck_3970_ == 0)
{
v___x_3965_ = v_x_3953_;
v_isShared_3966_ = v_isSharedCheck_3970_;
goto v_resetjp_3964_;
}
else
{
lean_inc(v_a_3963_);
lean_dec(v_x_3953_);
v___x_3965_ = lean_box(0);
v_isShared_3966_ = v_isSharedCheck_3970_;
goto v_resetjp_3964_;
}
v_resetjp_3964_:
{
lean_object* v___x_3968_; 
if (v_isShared_3966_ == 0)
{
lean_ctor_set_tag(v___x_3965_, 0);
v___x_3968_ = v___x_3965_;
goto v_reusejp_3967_;
}
else
{
lean_object* v_reuseFailAlloc_3969_; 
v_reuseFailAlloc_3969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3969_, 0, v_a_3963_);
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg___boxed(lean_object* v_x_3971_, lean_object* v___y_3972_){
_start:
{
lean_object* v_res_3973_; 
v_res_3973_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg(v_x_3971_);
return v_res_3973_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__1(lean_object* v_oldTraces_3974_, lean_object* v_data_3975_, lean_object* v_ref_3976_, lean_object* v_msg_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_){
_start:
{
lean_object* v_fileName_3983_; lean_object* v_fileMap_3984_; lean_object* v_options_3985_; lean_object* v_currRecDepth_3986_; lean_object* v_maxRecDepth_3987_; lean_object* v_ref_3988_; lean_object* v_currNamespace_3989_; lean_object* v_openDecls_3990_; lean_object* v_initHeartbeats_3991_; lean_object* v_maxHeartbeats_3992_; lean_object* v_quotContext_3993_; lean_object* v_currMacroScope_3994_; uint8_t v_diag_3995_; lean_object* v_cancelTk_x3f_3996_; uint8_t v_suppressElabErrors_3997_; lean_object* v_inheritedTraceOptions_3998_; lean_object* v___x_3999_; lean_object* v_traceState_4000_; lean_object* v_traces_4001_; lean_object* v_ref_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; size_t v_sz_4005_; size_t v___x_4006_; lean_object* v___x_4007_; lean_object* v_msg_4008_; lean_object* v___x_4009_; lean_object* v_a_4010_; lean_object* v___x_4012_; uint8_t v_isShared_4013_; uint8_t v_isSharedCheck_4047_; 
v_fileName_3983_ = lean_ctor_get(v___y_3980_, 0);
v_fileMap_3984_ = lean_ctor_get(v___y_3980_, 1);
v_options_3985_ = lean_ctor_get(v___y_3980_, 2);
v_currRecDepth_3986_ = lean_ctor_get(v___y_3980_, 3);
v_maxRecDepth_3987_ = lean_ctor_get(v___y_3980_, 4);
v_ref_3988_ = lean_ctor_get(v___y_3980_, 5);
v_currNamespace_3989_ = lean_ctor_get(v___y_3980_, 6);
v_openDecls_3990_ = lean_ctor_get(v___y_3980_, 7);
v_initHeartbeats_3991_ = lean_ctor_get(v___y_3980_, 8);
v_maxHeartbeats_3992_ = lean_ctor_get(v___y_3980_, 9);
v_quotContext_3993_ = lean_ctor_get(v___y_3980_, 10);
v_currMacroScope_3994_ = lean_ctor_get(v___y_3980_, 11);
v_diag_3995_ = lean_ctor_get_uint8(v___y_3980_, sizeof(void*)*14);
v_cancelTk_x3f_3996_ = lean_ctor_get(v___y_3980_, 12);
v_suppressElabErrors_3997_ = lean_ctor_get_uint8(v___y_3980_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3998_ = lean_ctor_get(v___y_3980_, 13);
v___x_3999_ = lean_st_ref_get(v___y_3981_);
v_traceState_4000_ = lean_ctor_get(v___x_3999_, 4);
lean_inc_ref(v_traceState_4000_);
lean_dec(v___x_3999_);
v_traces_4001_ = lean_ctor_get(v_traceState_4000_, 0);
lean_inc_ref(v_traces_4001_);
lean_dec_ref(v_traceState_4000_);
v_ref_4002_ = l_Lean_replaceRef(v_ref_3976_, v_ref_3988_);
lean_inc_ref(v_inheritedTraceOptions_3998_);
lean_inc(v_cancelTk_x3f_3996_);
lean_inc(v_currMacroScope_3994_);
lean_inc(v_quotContext_3993_);
lean_inc(v_maxHeartbeats_3992_);
lean_inc(v_initHeartbeats_3991_);
lean_inc(v_openDecls_3990_);
lean_inc(v_currNamespace_3989_);
lean_inc(v_maxRecDepth_3987_);
lean_inc(v_currRecDepth_3986_);
lean_inc_ref(v_options_3985_);
lean_inc_ref(v_fileMap_3984_);
lean_inc_ref(v_fileName_3983_);
v___x_4003_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_4003_, 0, v_fileName_3983_);
lean_ctor_set(v___x_4003_, 1, v_fileMap_3984_);
lean_ctor_set(v___x_4003_, 2, v_options_3985_);
lean_ctor_set(v___x_4003_, 3, v_currRecDepth_3986_);
lean_ctor_set(v___x_4003_, 4, v_maxRecDepth_3987_);
lean_ctor_set(v___x_4003_, 5, v_ref_4002_);
lean_ctor_set(v___x_4003_, 6, v_currNamespace_3989_);
lean_ctor_set(v___x_4003_, 7, v_openDecls_3990_);
lean_ctor_set(v___x_4003_, 8, v_initHeartbeats_3991_);
lean_ctor_set(v___x_4003_, 9, v_maxHeartbeats_3992_);
lean_ctor_set(v___x_4003_, 10, v_quotContext_3993_);
lean_ctor_set(v___x_4003_, 11, v_currMacroScope_3994_);
lean_ctor_set(v___x_4003_, 12, v_cancelTk_x3f_3996_);
lean_ctor_set(v___x_4003_, 13, v_inheritedTraceOptions_3998_);
lean_ctor_set_uint8(v___x_4003_, sizeof(void*)*14, v_diag_3995_);
lean_ctor_set_uint8(v___x_4003_, sizeof(void*)*14 + 1, v_suppressElabErrors_3997_);
v___x_4004_ = l_Lean_PersistentArray_toArray___redArg(v_traces_4001_);
lean_dec_ref(v_traces_4001_);
v_sz_4005_ = lean_array_size(v___x_4004_);
v___x_4006_ = ((size_t)0ULL);
v___x_4007_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4_spec__5(v_sz_4005_, v___x_4006_, v___x_4004_);
v_msg_4008_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_4008_, 0, v_data_3975_);
lean_ctor_set(v_msg_4008_, 1, v_msg_3977_);
lean_ctor_set(v_msg_4008_, 2, v___x_4007_);
v___x_4009_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0_spec__0(v_msg_4008_, v___y_3978_, v___y_3979_, v___x_4003_, v___y_3981_);
lean_dec_ref_known(v___x_4003_, 14);
v_a_4010_ = lean_ctor_get(v___x_4009_, 0);
v_isSharedCheck_4047_ = !lean_is_exclusive(v___x_4009_);
if (v_isSharedCheck_4047_ == 0)
{
v___x_4012_ = v___x_4009_;
v_isShared_4013_ = v_isSharedCheck_4047_;
goto v_resetjp_4011_;
}
else
{
lean_inc(v_a_4010_);
lean_dec(v___x_4009_);
v___x_4012_ = lean_box(0);
v_isShared_4013_ = v_isSharedCheck_4047_;
goto v_resetjp_4011_;
}
v_resetjp_4011_:
{
lean_object* v___x_4014_; lean_object* v_traceState_4015_; lean_object* v_env_4016_; lean_object* v_nextMacroScope_4017_; lean_object* v_ngen_4018_; lean_object* v_auxDeclNGen_4019_; lean_object* v_cache_4020_; lean_object* v_messages_4021_; lean_object* v_infoState_4022_; lean_object* v_snapshotTasks_4023_; lean_object* v___x_4025_; uint8_t v_isShared_4026_; uint8_t v_isSharedCheck_4046_; 
v___x_4014_ = lean_st_ref_take(v___y_3981_);
v_traceState_4015_ = lean_ctor_get(v___x_4014_, 4);
v_env_4016_ = lean_ctor_get(v___x_4014_, 0);
v_nextMacroScope_4017_ = lean_ctor_get(v___x_4014_, 1);
v_ngen_4018_ = lean_ctor_get(v___x_4014_, 2);
v_auxDeclNGen_4019_ = lean_ctor_get(v___x_4014_, 3);
v_cache_4020_ = lean_ctor_get(v___x_4014_, 5);
v_messages_4021_ = lean_ctor_get(v___x_4014_, 6);
v_infoState_4022_ = lean_ctor_get(v___x_4014_, 7);
v_snapshotTasks_4023_ = lean_ctor_get(v___x_4014_, 8);
v_isSharedCheck_4046_ = !lean_is_exclusive(v___x_4014_);
if (v_isSharedCheck_4046_ == 0)
{
v___x_4025_ = v___x_4014_;
v_isShared_4026_ = v_isSharedCheck_4046_;
goto v_resetjp_4024_;
}
else
{
lean_inc(v_snapshotTasks_4023_);
lean_inc(v_infoState_4022_);
lean_inc(v_messages_4021_);
lean_inc(v_cache_4020_);
lean_inc(v_traceState_4015_);
lean_inc(v_auxDeclNGen_4019_);
lean_inc(v_ngen_4018_);
lean_inc(v_nextMacroScope_4017_);
lean_inc(v_env_4016_);
lean_dec(v___x_4014_);
v___x_4025_ = lean_box(0);
v_isShared_4026_ = v_isSharedCheck_4046_;
goto v_resetjp_4024_;
}
v_resetjp_4024_:
{
uint64_t v_tid_4027_; lean_object* v___x_4029_; uint8_t v_isShared_4030_; uint8_t v_isSharedCheck_4044_; 
v_tid_4027_ = lean_ctor_get_uint64(v_traceState_4015_, sizeof(void*)*1);
v_isSharedCheck_4044_ = !lean_is_exclusive(v_traceState_4015_);
if (v_isSharedCheck_4044_ == 0)
{
lean_object* v_unused_4045_; 
v_unused_4045_ = lean_ctor_get(v_traceState_4015_, 0);
lean_dec(v_unused_4045_);
v___x_4029_ = v_traceState_4015_;
v_isShared_4030_ = v_isSharedCheck_4044_;
goto v_resetjp_4028_;
}
else
{
lean_dec(v_traceState_4015_);
v___x_4029_ = lean_box(0);
v_isShared_4030_ = v_isSharedCheck_4044_;
goto v_resetjp_4028_;
}
v_resetjp_4028_:
{
lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4034_; 
v___x_4031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4031_, 0, v_ref_3976_);
lean_ctor_set(v___x_4031_, 1, v_a_4010_);
v___x_4032_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_3974_, v___x_4031_);
if (v_isShared_4030_ == 0)
{
lean_ctor_set(v___x_4029_, 0, v___x_4032_);
v___x_4034_ = v___x_4029_;
goto v_reusejp_4033_;
}
else
{
lean_object* v_reuseFailAlloc_4043_; 
v_reuseFailAlloc_4043_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4043_, 0, v___x_4032_);
lean_ctor_set_uint64(v_reuseFailAlloc_4043_, sizeof(void*)*1, v_tid_4027_);
v___x_4034_ = v_reuseFailAlloc_4043_;
goto v_reusejp_4033_;
}
v_reusejp_4033_:
{
lean_object* v___x_4036_; 
if (v_isShared_4026_ == 0)
{
lean_ctor_set(v___x_4025_, 4, v___x_4034_);
v___x_4036_ = v___x_4025_;
goto v_reusejp_4035_;
}
else
{
lean_object* v_reuseFailAlloc_4042_; 
v_reuseFailAlloc_4042_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4042_, 0, v_env_4016_);
lean_ctor_set(v_reuseFailAlloc_4042_, 1, v_nextMacroScope_4017_);
lean_ctor_set(v_reuseFailAlloc_4042_, 2, v_ngen_4018_);
lean_ctor_set(v_reuseFailAlloc_4042_, 3, v_auxDeclNGen_4019_);
lean_ctor_set(v_reuseFailAlloc_4042_, 4, v___x_4034_);
lean_ctor_set(v_reuseFailAlloc_4042_, 5, v_cache_4020_);
lean_ctor_set(v_reuseFailAlloc_4042_, 6, v_messages_4021_);
lean_ctor_set(v_reuseFailAlloc_4042_, 7, v_infoState_4022_);
lean_ctor_set(v_reuseFailAlloc_4042_, 8, v_snapshotTasks_4023_);
v___x_4036_ = v_reuseFailAlloc_4042_;
goto v_reusejp_4035_;
}
v_reusejp_4035_:
{
lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4040_; 
v___x_4037_ = lean_st_ref_set(v___y_3981_, v___x_4036_);
v___x_4038_ = lean_box(0);
if (v_isShared_4013_ == 0)
{
lean_ctor_set(v___x_4012_, 0, v___x_4038_);
v___x_4040_ = v___x_4012_;
goto v_reusejp_4039_;
}
else
{
lean_object* v_reuseFailAlloc_4041_; 
v_reuseFailAlloc_4041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4041_, 0, v___x_4038_);
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__1___boxed(lean_object* v_oldTraces_4048_, lean_object* v_data_4049_, lean_object* v_ref_4050_, lean_object* v_msg_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_){
_start:
{
lean_object* v_res_4057_; 
v_res_4057_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__1(v_oldTraces_4048_, v_data_4049_, v_ref_4050_, v_msg_4051_, v___y_4052_, v___y_4053_, v___y_4054_, v___y_4055_);
lean_dec(v___y_4055_);
lean_dec_ref(v___y_4054_);
lean_dec(v___y_4053_);
lean_dec_ref(v___y_4052_);
return v_res_4057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1(lean_object* v_cls_4058_, uint8_t v_collapsed_4059_, lean_object* v_tag_4060_, lean_object* v_opts_4061_, uint8_t v_clsEnabled_4062_, lean_object* v_oldTraces_4063_, lean_object* v_msg_4064_, lean_object* v_resStartStop_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_){
_start:
{
lean_object* v_fst_4071_; lean_object* v_snd_4072_; lean_object* v___y_4074_; lean_object* v___y_4075_; lean_object* v_data_4076_; lean_object* v_fst_4087_; lean_object* v_snd_4088_; lean_object* v___x_4089_; uint8_t v___x_4090_; lean_object* v___y_4092_; lean_object* v_a_4093_; uint8_t v___y_4108_; double v___y_4139_; 
v_fst_4071_ = lean_ctor_get(v_resStartStop_4065_, 0);
lean_inc(v_fst_4071_);
v_snd_4072_ = lean_ctor_get(v_resStartStop_4065_, 1);
lean_inc(v_snd_4072_);
lean_dec_ref(v_resStartStop_4065_);
v_fst_4087_ = lean_ctor_get(v_snd_4072_, 0);
lean_inc(v_fst_4087_);
v_snd_4088_ = lean_ctor_get(v_snd_4072_, 1);
lean_inc(v_snd_4088_);
lean_dec(v_snd_4072_);
v___x_4089_ = l_Lean_trace_profiler;
v___x_4090_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_4061_, v___x_4089_);
if (v___x_4090_ == 0)
{
v___y_4108_ = v___x_4090_;
goto v___jp_4107_;
}
else
{
lean_object* v___x_4144_; uint8_t v___x_4145_; 
v___x_4144_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4145_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_4061_, v___x_4144_);
if (v___x_4145_ == 0)
{
lean_object* v___x_4146_; lean_object* v___x_4147_; double v___x_4148_; double v___x_4149_; double v___x_4150_; 
v___x_4146_ = l_Lean_trace_profiler_threshold;
v___x_4147_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_4061_, v___x_4146_);
v___x_4148_ = lean_float_of_nat(v___x_4147_);
v___x_4149_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2);
v___x_4150_ = lean_float_div(v___x_4148_, v___x_4149_);
v___y_4139_ = v___x_4150_;
goto v___jp_4138_;
}
else
{
lean_object* v___x_4151_; lean_object* v___x_4152_; double v___x_4153_; 
v___x_4151_ = l_Lean_trace_profiler_threshold;
v___x_4152_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_4061_, v___x_4151_);
v___x_4153_ = lean_float_of_nat(v___x_4152_);
v___y_4139_ = v___x_4153_;
goto v___jp_4138_;
}
}
v___jp_4073_:
{
lean_object* v___x_4077_; 
lean_inc(v___y_4074_);
v___x_4077_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__1(v_oldTraces_4063_, v_data_4076_, v___y_4074_, v___y_4075_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_);
if (lean_obj_tag(v___x_4077_) == 0)
{
lean_object* v___x_4078_; 
lean_dec_ref_known(v___x_4077_, 1);
v___x_4078_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg(v_fst_4071_);
return v___x_4078_;
}
else
{
lean_object* v_a_4079_; lean_object* v___x_4081_; uint8_t v_isShared_4082_; uint8_t v_isSharedCheck_4086_; 
lean_dec(v_fst_4071_);
v_a_4079_ = lean_ctor_get(v___x_4077_, 0);
v_isSharedCheck_4086_ = !lean_is_exclusive(v___x_4077_);
if (v_isSharedCheck_4086_ == 0)
{
v___x_4081_ = v___x_4077_;
v_isShared_4082_ = v_isSharedCheck_4086_;
goto v_resetjp_4080_;
}
else
{
lean_inc(v_a_4079_);
lean_dec(v___x_4077_);
v___x_4081_ = lean_box(0);
v_isShared_4082_ = v_isSharedCheck_4086_;
goto v_resetjp_4080_;
}
v_resetjp_4080_:
{
lean_object* v___x_4084_; 
if (v_isShared_4082_ == 0)
{
v___x_4084_ = v___x_4081_;
goto v_reusejp_4083_;
}
else
{
lean_object* v_reuseFailAlloc_4085_; 
v_reuseFailAlloc_4085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4085_, 0, v_a_4079_);
v___x_4084_ = v_reuseFailAlloc_4085_;
goto v_reusejp_4083_;
}
v_reusejp_4083_:
{
return v___x_4084_;
}
}
}
}
v___jp_4091_:
{
uint8_t v_result_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; double v___x_4097_; lean_object* v_data_4098_; 
v_result_4094_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__6(v_fst_4071_);
v___x_4095_ = lean_box(v_result_4094_);
v___x_4096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4096_, 0, v___x_4095_);
v___x_4097_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_4060_);
lean_inc_ref(v___x_4096_);
lean_inc(v_cls_4058_);
v_data_4098_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4098_, 0, v_cls_4058_);
lean_ctor_set(v_data_4098_, 1, v___x_4096_);
lean_ctor_set(v_data_4098_, 2, v_tag_4060_);
lean_ctor_set_float(v_data_4098_, sizeof(void*)*3, v___x_4097_);
lean_ctor_set_float(v_data_4098_, sizeof(void*)*3 + 8, v___x_4097_);
lean_ctor_set_uint8(v_data_4098_, sizeof(void*)*3 + 16, v_collapsed_4059_);
if (v___x_4090_ == 0)
{
lean_dec_ref_known(v___x_4096_, 1);
lean_dec(v_snd_4088_);
lean_dec(v_fst_4087_);
lean_dec_ref(v_tag_4060_);
lean_dec(v_cls_4058_);
v___y_4074_ = v___y_4092_;
v___y_4075_ = v_a_4093_;
v_data_4076_ = v_data_4098_;
goto v___jp_4073_;
}
else
{
lean_object* v_data_4099_; double v___x_4100_; double v___x_4101_; 
lean_dec_ref_known(v_data_4098_, 3);
v_data_4099_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4099_, 0, v_cls_4058_);
lean_ctor_set(v_data_4099_, 1, v___x_4096_);
lean_ctor_set(v_data_4099_, 2, v_tag_4060_);
v___x_4100_ = lean_unbox_float(v_fst_4087_);
lean_dec(v_fst_4087_);
lean_ctor_set_float(v_data_4099_, sizeof(void*)*3, v___x_4100_);
v___x_4101_ = lean_unbox_float(v_snd_4088_);
lean_dec(v_snd_4088_);
lean_ctor_set_float(v_data_4099_, sizeof(void*)*3 + 8, v___x_4101_);
lean_ctor_set_uint8(v_data_4099_, sizeof(void*)*3 + 16, v_collapsed_4059_);
v___y_4074_ = v___y_4092_;
v___y_4075_ = v_a_4093_;
v_data_4076_ = v_data_4099_;
goto v___jp_4073_;
}
}
v___jp_4102_:
{
lean_object* v_ref_4103_; lean_object* v___x_4104_; 
v_ref_4103_ = lean_ctor_get(v___y_4068_, 5);
lean_inc(v___y_4069_);
lean_inc_ref(v___y_4068_);
lean_inc(v___y_4067_);
lean_inc_ref(v___y_4066_);
lean_inc(v_fst_4071_);
v___x_4104_ = lean_apply_6(v_msg_4064_, v_fst_4071_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_, lean_box(0));
if (lean_obj_tag(v___x_4104_) == 0)
{
lean_object* v_a_4105_; 
v_a_4105_ = lean_ctor_get(v___x_4104_, 0);
lean_inc(v_a_4105_);
lean_dec_ref_known(v___x_4104_, 1);
v___y_4092_ = v_ref_4103_;
v_a_4093_ = v_a_4105_;
goto v___jp_4091_;
}
else
{
lean_object* v___x_4106_; 
lean_dec_ref_known(v___x_4104_, 1);
v___x_4106_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1);
v___y_4092_ = v_ref_4103_;
v_a_4093_ = v___x_4106_;
goto v___jp_4091_;
}
}
v___jp_4107_:
{
if (v_clsEnabled_4062_ == 0)
{
if (v___y_4108_ == 0)
{
lean_object* v___x_4109_; lean_object* v_traceState_4110_; lean_object* v_env_4111_; lean_object* v_nextMacroScope_4112_; lean_object* v_ngen_4113_; lean_object* v_auxDeclNGen_4114_; lean_object* v_cache_4115_; lean_object* v_messages_4116_; lean_object* v_infoState_4117_; lean_object* v_snapshotTasks_4118_; lean_object* v___x_4120_; uint8_t v_isShared_4121_; uint8_t v_isSharedCheck_4137_; 
lean_dec(v_snd_4088_);
lean_dec(v_fst_4087_);
lean_dec_ref(v_msg_4064_);
lean_dec_ref(v_tag_4060_);
lean_dec(v_cls_4058_);
v___x_4109_ = lean_st_ref_take(v___y_4069_);
v_traceState_4110_ = lean_ctor_get(v___x_4109_, 4);
v_env_4111_ = lean_ctor_get(v___x_4109_, 0);
v_nextMacroScope_4112_ = lean_ctor_get(v___x_4109_, 1);
v_ngen_4113_ = lean_ctor_get(v___x_4109_, 2);
v_auxDeclNGen_4114_ = lean_ctor_get(v___x_4109_, 3);
v_cache_4115_ = lean_ctor_get(v___x_4109_, 5);
v_messages_4116_ = lean_ctor_get(v___x_4109_, 6);
v_infoState_4117_ = lean_ctor_get(v___x_4109_, 7);
v_snapshotTasks_4118_ = lean_ctor_get(v___x_4109_, 8);
v_isSharedCheck_4137_ = !lean_is_exclusive(v___x_4109_);
if (v_isSharedCheck_4137_ == 0)
{
v___x_4120_ = v___x_4109_;
v_isShared_4121_ = v_isSharedCheck_4137_;
goto v_resetjp_4119_;
}
else
{
lean_inc(v_snapshotTasks_4118_);
lean_inc(v_infoState_4117_);
lean_inc(v_messages_4116_);
lean_inc(v_cache_4115_);
lean_inc(v_traceState_4110_);
lean_inc(v_auxDeclNGen_4114_);
lean_inc(v_ngen_4113_);
lean_inc(v_nextMacroScope_4112_);
lean_inc(v_env_4111_);
lean_dec(v___x_4109_);
v___x_4120_ = lean_box(0);
v_isShared_4121_ = v_isSharedCheck_4137_;
goto v_resetjp_4119_;
}
v_resetjp_4119_:
{
uint64_t v_tid_4122_; lean_object* v_traces_4123_; lean_object* v___x_4125_; uint8_t v_isShared_4126_; uint8_t v_isSharedCheck_4136_; 
v_tid_4122_ = lean_ctor_get_uint64(v_traceState_4110_, sizeof(void*)*1);
v_traces_4123_ = lean_ctor_get(v_traceState_4110_, 0);
v_isSharedCheck_4136_ = !lean_is_exclusive(v_traceState_4110_);
if (v_isSharedCheck_4136_ == 0)
{
v___x_4125_ = v_traceState_4110_;
v_isShared_4126_ = v_isSharedCheck_4136_;
goto v_resetjp_4124_;
}
else
{
lean_inc(v_traces_4123_);
lean_dec(v_traceState_4110_);
v___x_4125_ = lean_box(0);
v_isShared_4126_ = v_isSharedCheck_4136_;
goto v_resetjp_4124_;
}
v_resetjp_4124_:
{
lean_object* v___x_4127_; lean_object* v___x_4129_; 
v___x_4127_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_4063_, v_traces_4123_);
lean_dec_ref(v_traces_4123_);
if (v_isShared_4126_ == 0)
{
lean_ctor_set(v___x_4125_, 0, v___x_4127_);
v___x_4129_ = v___x_4125_;
goto v_reusejp_4128_;
}
else
{
lean_object* v_reuseFailAlloc_4135_; 
v_reuseFailAlloc_4135_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4135_, 0, v___x_4127_);
lean_ctor_set_uint64(v_reuseFailAlloc_4135_, sizeof(void*)*1, v_tid_4122_);
v___x_4129_ = v_reuseFailAlloc_4135_;
goto v_reusejp_4128_;
}
v_reusejp_4128_:
{
lean_object* v___x_4131_; 
if (v_isShared_4121_ == 0)
{
lean_ctor_set(v___x_4120_, 4, v___x_4129_);
v___x_4131_ = v___x_4120_;
goto v_reusejp_4130_;
}
else
{
lean_object* v_reuseFailAlloc_4134_; 
v_reuseFailAlloc_4134_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4134_, 0, v_env_4111_);
lean_ctor_set(v_reuseFailAlloc_4134_, 1, v_nextMacroScope_4112_);
lean_ctor_set(v_reuseFailAlloc_4134_, 2, v_ngen_4113_);
lean_ctor_set(v_reuseFailAlloc_4134_, 3, v_auxDeclNGen_4114_);
lean_ctor_set(v_reuseFailAlloc_4134_, 4, v___x_4129_);
lean_ctor_set(v_reuseFailAlloc_4134_, 5, v_cache_4115_);
lean_ctor_set(v_reuseFailAlloc_4134_, 6, v_messages_4116_);
lean_ctor_set(v_reuseFailAlloc_4134_, 7, v_infoState_4117_);
lean_ctor_set(v_reuseFailAlloc_4134_, 8, v_snapshotTasks_4118_);
v___x_4131_ = v_reuseFailAlloc_4134_;
goto v_reusejp_4130_;
}
v_reusejp_4130_:
{
lean_object* v___x_4132_; lean_object* v___x_4133_; 
v___x_4132_ = lean_st_ref_set(v___y_4069_, v___x_4131_);
v___x_4133_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg(v_fst_4071_);
return v___x_4133_;
}
}
}
}
}
else
{
goto v___jp_4102_;
}
}
else
{
goto v___jp_4102_;
}
}
v___jp_4138_:
{
double v___x_4140_; double v___x_4141_; double v___x_4142_; uint8_t v___x_4143_; 
v___x_4140_ = lean_unbox_float(v_snd_4088_);
v___x_4141_ = lean_unbox_float(v_fst_4087_);
v___x_4142_ = lean_float_sub(v___x_4140_, v___x_4141_);
v___x_4143_ = lean_float_decLt(v___y_4139_, v___x_4142_);
v___y_4108_ = v___x_4143_;
goto v___jp_4107_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1___boxed(lean_object* v_cls_4154_, lean_object* v_collapsed_4155_, lean_object* v_tag_4156_, lean_object* v_opts_4157_, lean_object* v_clsEnabled_4158_, lean_object* v_oldTraces_4159_, lean_object* v_msg_4160_, lean_object* v_resStartStop_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_){
_start:
{
uint8_t v_collapsed_boxed_4167_; uint8_t v_clsEnabled_boxed_4168_; lean_object* v_res_4169_; 
v_collapsed_boxed_4167_ = lean_unbox(v_collapsed_4155_);
v_clsEnabled_boxed_4168_ = lean_unbox(v_clsEnabled_4158_);
v_res_4169_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1(v_cls_4154_, v_collapsed_boxed_4167_, v_tag_4156_, v_opts_4157_, v_clsEnabled_boxed_4168_, v_oldTraces_4159_, v_msg_4160_, v_resStartStop_4161_, v___y_4162_, v___y_4163_, v___y_4164_, v___y_4165_);
lean_dec(v___y_4165_);
lean_dec_ref(v___y_4164_);
lean_dec(v___y_4163_);
lean_dec_ref(v___y_4162_);
lean_dec_ref(v_opts_4157_);
return v_res_4169_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1(void){
_start:
{
lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; 
v___x_4174_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0));
v___x_4175_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__3));
v___x_4176_ = l_Lean_Name_append(v___x_4175_, v___x_4174_);
return v___x_4176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry(lean_object* v_e_4177_, lean_object* v_a_4178_, lean_object* v_a_4179_, lean_object* v_a_4180_, lean_object* v_a_4181_){
_start:
{
lean_object* v_options_4183_; uint8_t v_hasTrace_4184_; 
v_options_4183_ = lean_ctor_get(v_a_4180_, 2);
v_hasTrace_4184_ = lean_ctor_get_uint8(v_options_4183_, sizeof(void*)*1);
if (v_hasTrace_4184_ == 0)
{
lean_object* v___x_4185_; 
v___x_4185_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_4181_);
if (lean_obj_tag(v___x_4185_) == 0)
{
lean_object* v_a_4186_; lean_object* v___x_4187_; 
v_a_4186_ = lean_ctor_get(v___x_4185_, 0);
lean_inc(v_a_4186_);
lean_dec_ref_known(v___x_4185_, 1);
v___x_4187_ = l_Lean_Meta_Sym_unfoldReducible(v_e_4177_, v_a_4178_, v_a_4179_, v_a_4180_, v_a_4181_);
if (lean_obj_tag(v___x_4187_) == 0)
{
lean_object* v_a_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___f_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; 
v_a_4188_ = lean_ctor_get(v___x_4187_, 0);
lean_inc(v_a_4188_);
lean_dec_ref_known(v___x_4187_, 1);
v___x_4189_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_4190_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_4183_, v___x_4189_);
v___x_4191_ = lean_unsigned_to_nat(2u);
v___x_4192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4192_, 0, v___x_4190_);
lean_ctor_set(v___x_4192_, 1, v___x_4191_);
v___x_4193_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(v_a_4186_);
v___f_4194_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4194_, 0, v_a_4188_);
lean_closure_set(v___f_4194_, 1, v___x_4193_);
lean_closure_set(v___f_4194_, 2, v___x_4192_);
v___x_4195_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0___boxed), 9, 2);
lean_closure_set(v___x_4195_, 0, lean_box(0));
lean_closure_set(v___x_4195_, 1, v___f_4194_);
v___x_4196_ = l_Lean_Meta_Sym_SymM_run___redArg(v___x_4195_, v_a_4178_, v_a_4179_, v_a_4180_, v_a_4181_);
return v___x_4196_;
}
else
{
lean_object* v_a_4197_; lean_object* v___x_4199_; uint8_t v_isShared_4200_; uint8_t v_isSharedCheck_4204_; 
lean_dec(v_a_4186_);
v_a_4197_ = lean_ctor_get(v___x_4187_, 0);
v_isSharedCheck_4204_ = !lean_is_exclusive(v___x_4187_);
if (v_isSharedCheck_4204_ == 0)
{
v___x_4199_ = v___x_4187_;
v_isShared_4200_ = v_isSharedCheck_4204_;
goto v_resetjp_4198_;
}
else
{
lean_inc(v_a_4197_);
lean_dec(v___x_4187_);
v___x_4199_ = lean_box(0);
v_isShared_4200_ = v_isSharedCheck_4204_;
goto v_resetjp_4198_;
}
v_resetjp_4198_:
{
lean_object* v___x_4202_; 
if (v_isShared_4200_ == 0)
{
v___x_4202_ = v___x_4199_;
goto v_reusejp_4201_;
}
else
{
lean_object* v_reuseFailAlloc_4203_; 
v_reuseFailAlloc_4203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4203_, 0, v_a_4197_);
v___x_4202_ = v_reuseFailAlloc_4203_;
goto v_reusejp_4201_;
}
v_reusejp_4201_:
{
return v___x_4202_;
}
}
}
}
else
{
lean_object* v_a_4205_; lean_object* v___x_4207_; uint8_t v_isShared_4208_; uint8_t v_isSharedCheck_4212_; 
lean_dec_ref(v_e_4177_);
v_a_4205_ = lean_ctor_get(v___x_4185_, 0);
v_isSharedCheck_4212_ = !lean_is_exclusive(v___x_4185_);
if (v_isSharedCheck_4212_ == 0)
{
v___x_4207_ = v___x_4185_;
v_isShared_4208_ = v_isSharedCheck_4212_;
goto v_resetjp_4206_;
}
else
{
lean_inc(v_a_4205_);
lean_dec(v___x_4185_);
v___x_4207_ = lean_box(0);
v_isShared_4208_ = v_isSharedCheck_4212_;
goto v_resetjp_4206_;
}
v_resetjp_4206_:
{
lean_object* v___x_4210_; 
if (v_isShared_4208_ == 0)
{
v___x_4210_ = v___x_4207_;
goto v_reusejp_4209_;
}
else
{
lean_object* v_reuseFailAlloc_4211_; 
v_reuseFailAlloc_4211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4211_, 0, v_a_4205_);
v___x_4210_ = v_reuseFailAlloc_4211_;
goto v_reusejp_4209_;
}
v_reusejp_4209_:
{
return v___x_4210_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_4213_; lean_object* v___f_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; uint8_t v___x_4218_; lean_object* v___y_4220_; lean_object* v___y_4221_; lean_object* v_a_4222_; lean_object* v___y_4235_; lean_object* v___y_4236_; lean_object* v_a_4237_; lean_object* v___y_4240_; lean_object* v___y_4241_; lean_object* v_a_4242_; lean_object* v___y_4252_; lean_object* v___y_4253_; lean_object* v_a_4254_; 
v_inheritedTraceOptions_4213_ = lean_ctor_get(v_a_4180_, 13);
lean_inc_ref(v_e_4177_);
v___f_4214_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___boxed), 7, 1);
lean_closure_set(v___f_4214_, 0, v_e_4177_);
v___x_4215_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0));
v___x_4216_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__1));
v___x_4217_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1);
v___x_4218_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4213_, v_options_4183_, v___x_4217_);
if (v___x_4218_ == 0)
{
lean_object* v___x_4309_; uint8_t v___x_4310_; 
v___x_4309_ = l_Lean_trace_profiler;
v___x_4310_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_4183_, v___x_4309_);
if (v___x_4310_ == 0)
{
lean_object* v___x_4311_; 
lean_dec_ref(v___f_4214_);
v___x_4311_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_4181_);
if (lean_obj_tag(v___x_4311_) == 0)
{
lean_object* v_a_4312_; lean_object* v___x_4313_; 
v_a_4312_ = lean_ctor_get(v___x_4311_, 0);
lean_inc(v_a_4312_);
lean_dec_ref_known(v___x_4311_, 1);
v___x_4313_ = l_Lean_Meta_Sym_unfoldReducible(v_e_4177_, v_a_4178_, v_a_4179_, v_a_4180_, v_a_4181_);
if (lean_obj_tag(v___x_4313_) == 0)
{
lean_object* v_a_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___f_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; 
v_a_4314_ = lean_ctor_get(v___x_4313_, 0);
lean_inc(v_a_4314_);
lean_dec_ref_known(v___x_4313_, 1);
v___x_4315_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_4316_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_4183_, v___x_4315_);
v___x_4317_ = lean_unsigned_to_nat(2u);
v___x_4318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4318_, 0, v___x_4316_);
lean_ctor_set(v___x_4318_, 1, v___x_4317_);
v___x_4319_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(v_a_4312_);
v___f_4320_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4320_, 0, v_a_4314_);
lean_closure_set(v___f_4320_, 1, v___x_4319_);
lean_closure_set(v___f_4320_, 2, v___x_4318_);
v___x_4321_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0___boxed), 9, 2);
lean_closure_set(v___x_4321_, 0, lean_box(0));
lean_closure_set(v___x_4321_, 1, v___f_4320_);
v___x_4322_ = l_Lean_Meta_Sym_SymM_run___redArg(v___x_4321_, v_a_4178_, v_a_4179_, v_a_4180_, v_a_4181_);
return v___x_4322_;
}
else
{
lean_object* v_a_4323_; lean_object* v___x_4325_; uint8_t v_isShared_4326_; uint8_t v_isSharedCheck_4330_; 
lean_dec(v_a_4312_);
v_a_4323_ = lean_ctor_get(v___x_4313_, 0);
v_isSharedCheck_4330_ = !lean_is_exclusive(v___x_4313_);
if (v_isSharedCheck_4330_ == 0)
{
v___x_4325_ = v___x_4313_;
v_isShared_4326_ = v_isSharedCheck_4330_;
goto v_resetjp_4324_;
}
else
{
lean_inc(v_a_4323_);
lean_dec(v___x_4313_);
v___x_4325_ = lean_box(0);
v_isShared_4326_ = v_isSharedCheck_4330_;
goto v_resetjp_4324_;
}
v_resetjp_4324_:
{
lean_object* v___x_4328_; 
if (v_isShared_4326_ == 0)
{
v___x_4328_ = v___x_4325_;
goto v_reusejp_4327_;
}
else
{
lean_object* v_reuseFailAlloc_4329_; 
v_reuseFailAlloc_4329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4329_, 0, v_a_4323_);
v___x_4328_ = v_reuseFailAlloc_4329_;
goto v_reusejp_4327_;
}
v_reusejp_4327_:
{
return v___x_4328_;
}
}
}
}
else
{
lean_object* v_a_4331_; lean_object* v___x_4333_; uint8_t v_isShared_4334_; uint8_t v_isSharedCheck_4338_; 
lean_dec_ref(v_e_4177_);
v_a_4331_ = lean_ctor_get(v___x_4311_, 0);
v_isSharedCheck_4338_ = !lean_is_exclusive(v___x_4311_);
if (v_isSharedCheck_4338_ == 0)
{
v___x_4333_ = v___x_4311_;
v_isShared_4334_ = v_isSharedCheck_4338_;
goto v_resetjp_4332_;
}
else
{
lean_inc(v_a_4331_);
lean_dec(v___x_4311_);
v___x_4333_ = lean_box(0);
v_isShared_4334_ = v_isSharedCheck_4338_;
goto v_resetjp_4332_;
}
v_resetjp_4332_:
{
lean_object* v___x_4336_; 
if (v_isShared_4334_ == 0)
{
v___x_4336_ = v___x_4333_;
goto v_reusejp_4335_;
}
else
{
lean_object* v_reuseFailAlloc_4337_; 
v_reuseFailAlloc_4337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4337_, 0, v_a_4331_);
v___x_4336_ = v_reuseFailAlloc_4337_;
goto v_reusejp_4335_;
}
v_reusejp_4335_:
{
return v___x_4336_;
}
}
}
}
else
{
goto v___jp_4256_;
}
}
else
{
goto v___jp_4256_;
}
v___jp_4219_:
{
lean_object* v___x_4223_; double v___x_4224_; double v___x_4225_; double v___x_4226_; double v___x_4227_; double v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; 
v___x_4223_ = lean_io_mono_nanos_now();
v___x_4224_ = lean_float_of_nat(v___y_4220_);
v___x_4225_ = lean_float_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9);
v___x_4226_ = lean_float_div(v___x_4224_, v___x_4225_);
v___x_4227_ = lean_float_of_nat(v___x_4223_);
v___x_4228_ = lean_float_div(v___x_4227_, v___x_4225_);
v___x_4229_ = lean_box_float(v___x_4226_);
v___x_4230_ = lean_box_float(v___x_4228_);
v___x_4231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4231_, 0, v___x_4229_);
lean_ctor_set(v___x_4231_, 1, v___x_4230_);
v___x_4232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4232_, 0, v_a_4222_);
lean_ctor_set(v___x_4232_, 1, v___x_4231_);
v___x_4233_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1(v___x_4215_, v_hasTrace_4184_, v___x_4216_, v_options_4183_, v___x_4218_, v___y_4221_, v___f_4214_, v___x_4232_, v_a_4178_, v_a_4179_, v_a_4180_, v_a_4181_);
return v___x_4233_;
}
v___jp_4234_:
{
lean_object* v___x_4238_; 
v___x_4238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4238_, 0, v_a_4237_);
v___y_4220_ = v___y_4235_;
v___y_4221_ = v___y_4236_;
v_a_4222_ = v___x_4238_;
goto v___jp_4219_;
}
v___jp_4239_:
{
lean_object* v___x_4243_; double v___x_4244_; double v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; 
v___x_4243_ = lean_io_get_num_heartbeats();
v___x_4244_ = lean_float_of_nat(v___y_4240_);
v___x_4245_ = lean_float_of_nat(v___x_4243_);
v___x_4246_ = lean_box_float(v___x_4244_);
v___x_4247_ = lean_box_float(v___x_4245_);
v___x_4248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4248_, 0, v___x_4246_);
lean_ctor_set(v___x_4248_, 1, v___x_4247_);
v___x_4249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4249_, 0, v_a_4242_);
lean_ctor_set(v___x_4249_, 1, v___x_4248_);
v___x_4250_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1(v___x_4215_, v_hasTrace_4184_, v___x_4216_, v_options_4183_, v___x_4218_, v___y_4241_, v___f_4214_, v___x_4249_, v_a_4178_, v_a_4179_, v_a_4180_, v_a_4181_);
return v___x_4250_;
}
v___jp_4251_:
{
lean_object* v___x_4255_; 
v___x_4255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4255_, 0, v_a_4254_);
v___y_4240_ = v___y_4252_;
v___y_4241_ = v___y_4253_;
v_a_4242_ = v___x_4255_;
goto v___jp_4239_;
}
v___jp_4256_:
{
lean_object* v___x_4257_; lean_object* v_a_4258_; lean_object* v___x_4259_; uint8_t v___x_4260_; 
v___x_4257_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg(v_a_4181_);
v_a_4258_ = lean_ctor_get(v___x_4257_, 0);
lean_inc(v_a_4258_);
lean_dec_ref(v___x_4257_);
v___x_4259_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4260_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_4183_, v___x_4259_);
if (v___x_4260_ == 0)
{
lean_object* v___x_4261_; lean_object* v___x_4262_; 
v___x_4261_ = lean_io_mono_nanos_now();
v___x_4262_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_4181_);
if (lean_obj_tag(v___x_4262_) == 0)
{
lean_object* v_a_4263_; lean_object* v___x_4264_; 
v_a_4263_ = lean_ctor_get(v___x_4262_, 0);
lean_inc(v_a_4263_);
lean_dec_ref_known(v___x_4262_, 1);
v___x_4264_ = l_Lean_Meta_Sym_unfoldReducible(v_e_4177_, v_a_4178_, v_a_4179_, v_a_4180_, v_a_4181_);
if (lean_obj_tag(v___x_4264_) == 0)
{
lean_object* v_a_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___f_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; 
v_a_4265_ = lean_ctor_get(v___x_4264_, 0);
lean_inc(v_a_4265_);
lean_dec_ref_known(v___x_4264_, 1);
v___x_4266_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_4267_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_4183_, v___x_4266_);
v___x_4268_ = lean_unsigned_to_nat(2u);
v___x_4269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4269_, 0, v___x_4267_);
lean_ctor_set(v___x_4269_, 1, v___x_4268_);
v___x_4270_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(v_a_4263_);
v___f_4271_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4271_, 0, v_a_4265_);
lean_closure_set(v___f_4271_, 1, v___x_4270_);
lean_closure_set(v___f_4271_, 2, v___x_4269_);
v___x_4272_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0___boxed), 9, 2);
lean_closure_set(v___x_4272_, 0, lean_box(0));
lean_closure_set(v___x_4272_, 1, v___f_4271_);
v___x_4273_ = l_Lean_Meta_Sym_SymM_run___redArg(v___x_4272_, v_a_4178_, v_a_4179_, v_a_4180_, v_a_4181_);
if (lean_obj_tag(v___x_4273_) == 0)
{
lean_object* v_a_4274_; lean_object* v___x_4276_; uint8_t v_isShared_4277_; uint8_t v_isSharedCheck_4281_; 
v_a_4274_ = lean_ctor_get(v___x_4273_, 0);
v_isSharedCheck_4281_ = !lean_is_exclusive(v___x_4273_);
if (v_isSharedCheck_4281_ == 0)
{
v___x_4276_ = v___x_4273_;
v_isShared_4277_ = v_isSharedCheck_4281_;
goto v_resetjp_4275_;
}
else
{
lean_inc(v_a_4274_);
lean_dec(v___x_4273_);
v___x_4276_ = lean_box(0);
v_isShared_4277_ = v_isSharedCheck_4281_;
goto v_resetjp_4275_;
}
v_resetjp_4275_:
{
lean_object* v___x_4279_; 
if (v_isShared_4277_ == 0)
{
lean_ctor_set_tag(v___x_4276_, 1);
v___x_4279_ = v___x_4276_;
goto v_reusejp_4278_;
}
else
{
lean_object* v_reuseFailAlloc_4280_; 
v_reuseFailAlloc_4280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4280_, 0, v_a_4274_);
v___x_4279_ = v_reuseFailAlloc_4280_;
goto v_reusejp_4278_;
}
v_reusejp_4278_:
{
v___y_4220_ = v___x_4261_;
v___y_4221_ = v_a_4258_;
v_a_4222_ = v___x_4279_;
goto v___jp_4219_;
}
}
}
else
{
lean_object* v_a_4282_; 
v_a_4282_ = lean_ctor_get(v___x_4273_, 0);
lean_inc(v_a_4282_);
lean_dec_ref_known(v___x_4273_, 1);
v___y_4235_ = v___x_4261_;
v___y_4236_ = v_a_4258_;
v_a_4237_ = v_a_4282_;
goto v___jp_4234_;
}
}
else
{
lean_object* v_a_4283_; 
lean_dec(v_a_4263_);
v_a_4283_ = lean_ctor_get(v___x_4264_, 0);
lean_inc(v_a_4283_);
lean_dec_ref_known(v___x_4264_, 1);
v___y_4235_ = v___x_4261_;
v___y_4236_ = v_a_4258_;
v_a_4237_ = v_a_4283_;
goto v___jp_4234_;
}
}
else
{
lean_object* v_a_4284_; 
lean_dec_ref(v_e_4177_);
v_a_4284_ = lean_ctor_get(v___x_4262_, 0);
lean_inc(v_a_4284_);
lean_dec_ref_known(v___x_4262_, 1);
v___y_4235_ = v___x_4261_;
v___y_4236_ = v_a_4258_;
v_a_4237_ = v_a_4284_;
goto v___jp_4234_;
}
}
else
{
lean_object* v___x_4285_; lean_object* v___x_4286_; 
v___x_4285_ = lean_io_get_num_heartbeats();
v___x_4286_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_4181_);
if (lean_obj_tag(v___x_4286_) == 0)
{
lean_object* v_a_4287_; lean_object* v___x_4288_; 
v_a_4287_ = lean_ctor_get(v___x_4286_, 0);
lean_inc(v_a_4287_);
lean_dec_ref_known(v___x_4286_, 1);
v___x_4288_ = l_Lean_Meta_Sym_unfoldReducible(v_e_4177_, v_a_4178_, v_a_4179_, v_a_4180_, v_a_4181_);
if (lean_obj_tag(v___x_4288_) == 0)
{
lean_object* v_a_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___f_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; 
v_a_4289_ = lean_ctor_get(v___x_4288_, 0);
lean_inc(v_a_4289_);
lean_dec_ref_known(v___x_4288_, 1);
v___x_4290_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_4291_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_4183_, v___x_4290_);
v___x_4292_ = lean_unsigned_to_nat(2u);
v___x_4293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4293_, 0, v___x_4291_);
lean_ctor_set(v___x_4293_, 1, v___x_4292_);
v___x_4294_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(v_a_4287_);
v___f_4295_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4295_, 0, v_a_4289_);
lean_closure_set(v___f_4295_, 1, v___x_4294_);
lean_closure_set(v___f_4295_, 2, v___x_4293_);
v___x_4296_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0___boxed), 9, 2);
lean_closure_set(v___x_4296_, 0, lean_box(0));
lean_closure_set(v___x_4296_, 1, v___f_4295_);
v___x_4297_ = l_Lean_Meta_Sym_SymM_run___redArg(v___x_4296_, v_a_4178_, v_a_4179_, v_a_4180_, v_a_4181_);
if (lean_obj_tag(v___x_4297_) == 0)
{
lean_object* v_a_4298_; lean_object* v___x_4300_; uint8_t v_isShared_4301_; uint8_t v_isSharedCheck_4305_; 
v_a_4298_ = lean_ctor_get(v___x_4297_, 0);
v_isSharedCheck_4305_ = !lean_is_exclusive(v___x_4297_);
if (v_isSharedCheck_4305_ == 0)
{
v___x_4300_ = v___x_4297_;
v_isShared_4301_ = v_isSharedCheck_4305_;
goto v_resetjp_4299_;
}
else
{
lean_inc(v_a_4298_);
lean_dec(v___x_4297_);
v___x_4300_ = lean_box(0);
v_isShared_4301_ = v_isSharedCheck_4305_;
goto v_resetjp_4299_;
}
v_resetjp_4299_:
{
lean_object* v___x_4303_; 
if (v_isShared_4301_ == 0)
{
lean_ctor_set_tag(v___x_4300_, 1);
v___x_4303_ = v___x_4300_;
goto v_reusejp_4302_;
}
else
{
lean_object* v_reuseFailAlloc_4304_; 
v_reuseFailAlloc_4304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4304_, 0, v_a_4298_);
v___x_4303_ = v_reuseFailAlloc_4304_;
goto v_reusejp_4302_;
}
v_reusejp_4302_:
{
v___y_4240_ = v___x_4285_;
v___y_4241_ = v_a_4258_;
v_a_4242_ = v___x_4303_;
goto v___jp_4239_;
}
}
}
else
{
lean_object* v_a_4306_; 
v_a_4306_ = lean_ctor_get(v___x_4297_, 0);
lean_inc(v_a_4306_);
lean_dec_ref_known(v___x_4297_, 1);
v___y_4252_ = v___x_4285_;
v___y_4253_ = v_a_4258_;
v_a_4254_ = v_a_4306_;
goto v___jp_4251_;
}
}
else
{
lean_object* v_a_4307_; 
lean_dec(v_a_4287_);
v_a_4307_ = lean_ctor_get(v___x_4288_, 0);
lean_inc(v_a_4307_);
lean_dec_ref_known(v___x_4288_, 1);
v___y_4252_ = v___x_4285_;
v___y_4253_ = v_a_4258_;
v_a_4254_ = v_a_4307_;
goto v___jp_4251_;
}
}
else
{
lean_object* v_a_4308_; 
lean_dec_ref(v_e_4177_);
v_a_4308_ = lean_ctor_get(v___x_4286_, 0);
lean_inc(v_a_4308_);
lean_dec_ref_known(v___x_4286_, 1);
v___y_4252_ = v___x_4285_;
v___y_4253_ = v_a_4258_;
v_a_4254_ = v_a_4308_;
goto v___jp_4251_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___boxed(lean_object* v_e_4339_, lean_object* v_a_4340_, lean_object* v_a_4341_, lean_object* v_a_4342_, lean_object* v_a_4343_, lean_object* v_a_4344_){
_start:
{
lean_object* v_res_4345_; 
v_res_4345_ = l_Lean_Meta_Tactic_Cbv_cbvEntry(v_e_4339_, v_a_4340_, v_a_4341_, v_a_4342_, v_a_4343_);
lean_dec(v_a_4343_);
lean_dec_ref(v_a_4342_);
lean_dec(v_a_4341_);
lean_dec_ref(v_a_4340_);
return v_res_4345_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2(lean_object* v_00_u03b1_4346_, lean_object* v_x_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_){
_start:
{
lean_object* v___x_4353_; 
v___x_4353_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg(v_x_4347_);
return v___x_4353_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___boxed(lean_object* v_00_u03b1_4354_, lean_object* v_x_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_){
_start:
{
lean_object* v_res_4361_; 
v_res_4361_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2(v_00_u03b1_4354_, v_x_4355_, v___y_4356_, v___y_4357_, v___y_4358_, v___y_4359_);
lean_dec(v___y_4359_);
lean_dec_ref(v___y_4358_);
lean_dec(v___y_4357_);
lean_dec_ref(v___y_4356_);
return v_res_4361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1___redArg(lean_object* v___y_4362_){
_start:
{
lean_object* v___x_4364_; lean_object* v_traceState_4365_; lean_object* v_traces_4366_; lean_object* v___x_4367_; lean_object* v_traceState_4368_; lean_object* v_env_4369_; lean_object* v_nextMacroScope_4370_; lean_object* v_ngen_4371_; lean_object* v_auxDeclNGen_4372_; lean_object* v_cache_4373_; lean_object* v_messages_4374_; lean_object* v_infoState_4375_; lean_object* v_snapshotTasks_4376_; lean_object* v___x_4378_; uint8_t v_isShared_4379_; uint8_t v_isSharedCheck_4397_; 
v___x_4364_ = lean_st_ref_get(v___y_4362_);
v_traceState_4365_ = lean_ctor_get(v___x_4364_, 4);
lean_inc_ref(v_traceState_4365_);
lean_dec(v___x_4364_);
v_traces_4366_ = lean_ctor_get(v_traceState_4365_, 0);
lean_inc_ref(v_traces_4366_);
lean_dec_ref(v_traceState_4365_);
v___x_4367_ = lean_st_ref_take(v___y_4362_);
v_traceState_4368_ = lean_ctor_get(v___x_4367_, 4);
v_env_4369_ = lean_ctor_get(v___x_4367_, 0);
v_nextMacroScope_4370_ = lean_ctor_get(v___x_4367_, 1);
v_ngen_4371_ = lean_ctor_get(v___x_4367_, 2);
v_auxDeclNGen_4372_ = lean_ctor_get(v___x_4367_, 3);
v_cache_4373_ = lean_ctor_get(v___x_4367_, 5);
v_messages_4374_ = lean_ctor_get(v___x_4367_, 6);
v_infoState_4375_ = lean_ctor_get(v___x_4367_, 7);
v_snapshotTasks_4376_ = lean_ctor_get(v___x_4367_, 8);
v_isSharedCheck_4397_ = !lean_is_exclusive(v___x_4367_);
if (v_isSharedCheck_4397_ == 0)
{
v___x_4378_ = v___x_4367_;
v_isShared_4379_ = v_isSharedCheck_4397_;
goto v_resetjp_4377_;
}
else
{
lean_inc(v_snapshotTasks_4376_);
lean_inc(v_infoState_4375_);
lean_inc(v_messages_4374_);
lean_inc(v_cache_4373_);
lean_inc(v_traceState_4368_);
lean_inc(v_auxDeclNGen_4372_);
lean_inc(v_ngen_4371_);
lean_inc(v_nextMacroScope_4370_);
lean_inc(v_env_4369_);
lean_dec(v___x_4367_);
v___x_4378_ = lean_box(0);
v_isShared_4379_ = v_isSharedCheck_4397_;
goto v_resetjp_4377_;
}
v_resetjp_4377_:
{
uint64_t v_tid_4380_; lean_object* v___x_4382_; uint8_t v_isShared_4383_; uint8_t v_isSharedCheck_4395_; 
v_tid_4380_ = lean_ctor_get_uint64(v_traceState_4368_, sizeof(void*)*1);
v_isSharedCheck_4395_ = !lean_is_exclusive(v_traceState_4368_);
if (v_isSharedCheck_4395_ == 0)
{
lean_object* v_unused_4396_; 
v_unused_4396_ = lean_ctor_get(v_traceState_4368_, 0);
lean_dec(v_unused_4396_);
v___x_4382_ = v_traceState_4368_;
v_isShared_4383_ = v_isSharedCheck_4395_;
goto v_resetjp_4381_;
}
else
{
lean_dec(v_traceState_4368_);
v___x_4382_ = lean_box(0);
v_isShared_4383_ = v_isSharedCheck_4395_;
goto v_resetjp_4381_;
}
v_resetjp_4381_:
{
lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4388_; 
v___x_4384_ = lean_unsigned_to_nat(32u);
v___x_4385_ = lean_mk_empty_array_with_capacity(v___x_4384_);
lean_dec_ref(v___x_4385_);
v___x_4386_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1);
if (v_isShared_4383_ == 0)
{
lean_ctor_set(v___x_4382_, 0, v___x_4386_);
v___x_4388_ = v___x_4382_;
goto v_reusejp_4387_;
}
else
{
lean_object* v_reuseFailAlloc_4394_; 
v_reuseFailAlloc_4394_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4394_, 0, v___x_4386_);
lean_ctor_set_uint64(v_reuseFailAlloc_4394_, sizeof(void*)*1, v_tid_4380_);
v___x_4388_ = v_reuseFailAlloc_4394_;
goto v_reusejp_4387_;
}
v_reusejp_4387_:
{
lean_object* v___x_4390_; 
if (v_isShared_4379_ == 0)
{
lean_ctor_set(v___x_4378_, 4, v___x_4388_);
v___x_4390_ = v___x_4378_;
goto v_reusejp_4389_;
}
else
{
lean_object* v_reuseFailAlloc_4393_; 
v_reuseFailAlloc_4393_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4393_, 0, v_env_4369_);
lean_ctor_set(v_reuseFailAlloc_4393_, 1, v_nextMacroScope_4370_);
lean_ctor_set(v_reuseFailAlloc_4393_, 2, v_ngen_4371_);
lean_ctor_set(v_reuseFailAlloc_4393_, 3, v_auxDeclNGen_4372_);
lean_ctor_set(v_reuseFailAlloc_4393_, 4, v___x_4388_);
lean_ctor_set(v_reuseFailAlloc_4393_, 5, v_cache_4373_);
lean_ctor_set(v_reuseFailAlloc_4393_, 6, v_messages_4374_);
lean_ctor_set(v_reuseFailAlloc_4393_, 7, v_infoState_4375_);
lean_ctor_set(v_reuseFailAlloc_4393_, 8, v_snapshotTasks_4376_);
v___x_4390_ = v_reuseFailAlloc_4393_;
goto v_reusejp_4389_;
}
v_reusejp_4389_:
{
lean_object* v___x_4391_; lean_object* v___x_4392_; 
v___x_4391_ = lean_st_ref_set(v___y_4362_, v___x_4390_);
v___x_4392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4392_, 0, v_traces_4366_);
return v___x_4392_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1___redArg___boxed(lean_object* v___y_4398_, lean_object* v___y_4399_){
_start:
{
lean_object* v_res_4400_; 
v_res_4400_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1___redArg(v___y_4398_);
lean_dec(v___y_4398_);
return v_res_4400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1(lean_object* v___y_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_){
_start:
{
lean_object* v___x_4408_; 
v___x_4408_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1___redArg(v___y_4406_);
return v___x_4408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1___boxed(lean_object* v___y_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_){
_start:
{
lean_object* v_res_4416_; 
v_res_4416_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1(v___y_4409_, v___y_4410_, v___y_4411_, v___y_4412_, v___y_4413_, v___y_4414_);
lean_dec(v___y_4414_);
lean_dec_ref(v___y_4413_);
lean_dec(v___y_4412_);
lean_dec_ref(v___y_4411_);
lean_dec(v___y_4410_);
lean_dec_ref(v___y_4409_);
return v_res_4416_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg___lam__0(lean_object* v_x_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_){
_start:
{
lean_object* v___x_4425_; 
lean_inc(v___y_4419_);
lean_inc_ref(v___y_4418_);
v___x_4425_ = lean_apply_7(v_x_4417_, v___y_4418_, v___y_4419_, v___y_4420_, v___y_4421_, v___y_4422_, v___y_4423_, lean_box(0));
return v___x_4425_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg___lam__0___boxed(lean_object* v_x_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_){
_start:
{
lean_object* v_res_4434_; 
v_res_4434_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg___lam__0(v_x_4426_, v___y_4427_, v___y_4428_, v___y_4429_, v___y_4430_, v___y_4431_, v___y_4432_);
lean_dec(v___y_4428_);
lean_dec_ref(v___y_4427_);
return v_res_4434_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg(lean_object* v_mvarId_4435_, lean_object* v_x_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_){
_start:
{
lean_object* v___f_4444_; lean_object* v___x_4445_; 
lean_inc(v___y_4438_);
lean_inc_ref(v___y_4437_);
v___f_4444_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4444_, 0, v_x_4436_);
lean_closure_set(v___f_4444_, 1, v___y_4437_);
lean_closure_set(v___f_4444_, 2, v___y_4438_);
v___x_4445_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_4435_, v___f_4444_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_);
if (lean_obj_tag(v___x_4445_) == 0)
{
return v___x_4445_;
}
else
{
lean_object* v_a_4446_; lean_object* v___x_4448_; uint8_t v_isShared_4449_; uint8_t v_isSharedCheck_4453_; 
v_a_4446_ = lean_ctor_get(v___x_4445_, 0);
v_isSharedCheck_4453_ = !lean_is_exclusive(v___x_4445_);
if (v_isSharedCheck_4453_ == 0)
{
v___x_4448_ = v___x_4445_;
v_isShared_4449_ = v_isSharedCheck_4453_;
goto v_resetjp_4447_;
}
else
{
lean_inc(v_a_4446_);
lean_dec(v___x_4445_);
v___x_4448_ = lean_box(0);
v_isShared_4449_ = v_isSharedCheck_4453_;
goto v_resetjp_4447_;
}
v_resetjp_4447_:
{
lean_object* v___x_4451_; 
if (v_isShared_4449_ == 0)
{
v___x_4451_ = v___x_4448_;
goto v_reusejp_4450_;
}
else
{
lean_object* v_reuseFailAlloc_4452_; 
v_reuseFailAlloc_4452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4452_, 0, v_a_4446_);
v___x_4451_ = v_reuseFailAlloc_4452_;
goto v_reusejp_4450_;
}
v_reusejp_4450_:
{
return v___x_4451_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg___boxed(lean_object* v_mvarId_4454_, lean_object* v_x_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_){
_start:
{
lean_object* v_res_4463_; 
v_res_4463_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg(v_mvarId_4454_, v_x_4455_, v___y_4456_, v___y_4457_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_);
lean_dec(v___y_4461_);
lean_dec_ref(v___y_4460_);
lean_dec(v___y_4459_);
lean_dec_ref(v___y_4458_);
lean_dec(v___y_4457_);
lean_dec_ref(v___y_4456_);
return v_res_4463_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4(lean_object* v_00_u03b1_4464_, lean_object* v_mvarId_4465_, lean_object* v_x_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_){
_start:
{
lean_object* v___x_4474_; 
v___x_4474_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg(v_mvarId_4465_, v_x_4466_, v___y_4467_, v___y_4468_, v___y_4469_, v___y_4470_, v___y_4471_, v___y_4472_);
return v___x_4474_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___boxed(lean_object* v_00_u03b1_4475_, lean_object* v_mvarId_4476_, lean_object* v_x_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_){
_start:
{
lean_object* v_res_4485_; 
v_res_4485_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4(v_00_u03b1_4475_, v_mvarId_4476_, v_x_4477_, v___y_4478_, v___y_4479_, v___y_4480_, v___y_4481_, v___y_4482_, v___y_4483_);
lean_dec(v___y_4483_);
lean_dec_ref(v___y_4482_);
lean_dec(v___y_4481_);
lean_dec_ref(v___y_4480_);
lean_dec(v___y_4479_);
lean_dec_ref(v___y_4478_);
return v_res_4485_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4487_; lean_object* v___x_4488_; 
v___x_4487_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__0));
v___x_4488_ = l_Lean_stringToMessageData(v___x_4487_);
return v___x_4488_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4490_; lean_object* v___x_4491_; 
v___x_4490_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__2));
v___x_4491_ = l_Lean_stringToMessageData(v___x_4490_);
return v___x_4491_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4493_; lean_object* v___x_4494_; 
v___x_4493_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__4));
v___x_4494_ = l_Lean_stringToMessageData(v___x_4493_);
return v___x_4494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0(lean_object* v_a_4495_, lean_object* v_x_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_){
_start:
{
if (lean_obj_tag(v_x_4496_) == 0)
{
lean_object* v_a_4504_; lean_object* v___x_4506_; uint8_t v_isShared_4507_; uint8_t v_isSharedCheck_4514_; 
lean_dec_ref(v_a_4495_);
v_a_4504_ = lean_ctor_get(v_x_4496_, 0);
v_isSharedCheck_4514_ = !lean_is_exclusive(v_x_4496_);
if (v_isSharedCheck_4514_ == 0)
{
v___x_4506_ = v_x_4496_;
v_isShared_4507_ = v_isSharedCheck_4514_;
goto v_resetjp_4505_;
}
else
{
lean_inc(v_a_4504_);
lean_dec(v_x_4496_);
v___x_4506_ = lean_box(0);
v_isShared_4507_ = v_isSharedCheck_4514_;
goto v_resetjp_4505_;
}
v_resetjp_4505_:
{
lean_object* v___x_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; lean_object* v___x_4512_; 
v___x_4508_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__1);
v___x_4509_ = l_Lean_Exception_toMessageData(v_a_4504_);
v___x_4510_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4510_, 0, v___x_4508_);
lean_ctor_set(v___x_4510_, 1, v___x_4509_);
if (v_isShared_4507_ == 0)
{
lean_ctor_set(v___x_4506_, 0, v___x_4510_);
v___x_4512_ = v___x_4506_;
goto v_reusejp_4511_;
}
else
{
lean_object* v_reuseFailAlloc_4513_; 
v_reuseFailAlloc_4513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4513_, 0, v___x_4510_);
v___x_4512_ = v_reuseFailAlloc_4513_;
goto v_reusejp_4511_;
}
v_reusejp_4511_:
{
return v___x_4512_;
}
}
}
else
{
lean_object* v_a_4515_; lean_object* v___x_4517_; uint8_t v_isShared_4518_; uint8_t v_isSharedCheck_4534_; 
v_a_4515_ = lean_ctor_get(v_x_4496_, 0);
v_isSharedCheck_4534_ = !lean_is_exclusive(v_x_4496_);
if (v_isSharedCheck_4534_ == 0)
{
v___x_4517_ = v_x_4496_;
v_isShared_4518_ = v_isSharedCheck_4534_;
goto v_resetjp_4516_;
}
else
{
lean_inc(v_a_4515_);
lean_dec(v_x_4496_);
v___x_4517_ = lean_box(0);
v_isShared_4518_ = v_isSharedCheck_4534_;
goto v_resetjp_4516_;
}
v_resetjp_4516_:
{
if (lean_obj_tag(v_a_4515_) == 0)
{
lean_object* v___x_4519_; lean_object* v___x_4521_; 
lean_dec_ref_known(v_a_4515_, 0);
lean_dec_ref(v_a_4495_);
v___x_4519_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__3, &l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__3);
if (v_isShared_4518_ == 0)
{
lean_ctor_set_tag(v___x_4517_, 0);
lean_ctor_set(v___x_4517_, 0, v___x_4519_);
v___x_4521_ = v___x_4517_;
goto v_reusejp_4520_;
}
else
{
lean_object* v_reuseFailAlloc_4522_; 
v_reuseFailAlloc_4522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4522_, 0, v___x_4519_);
v___x_4521_ = v_reuseFailAlloc_4522_;
goto v_reusejp_4520_;
}
v_reusejp_4520_:
{
return v___x_4521_;
}
}
else
{
lean_object* v_e_x27_4523_; lean_object* v___x_4524_; lean_object* v___x_4525_; lean_object* v___x_4526_; lean_object* v___x_4527_; lean_object* v___x_4528_; lean_object* v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4532_; 
v_e_x27_4523_ = lean_ctor_get(v_a_4515_, 0);
lean_inc_ref(v_e_x27_4523_);
lean_dec_ref_known(v_a_4515_, 2);
v___x_4524_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__5, &l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__5_once, _init_l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__5);
v___x_4525_ = l_Lean_indentExpr(v_a_4495_);
v___x_4526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4526_, 0, v___x_4524_);
lean_ctor_set(v___x_4526_, 1, v___x_4525_);
v___x_4527_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_4528_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4528_, 0, v___x_4526_);
lean_ctor_set(v___x_4528_, 1, v___x_4527_);
v___x_4529_ = l_Lean_indentExpr(v_e_x27_4523_);
v___x_4530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4530_, 0, v___x_4528_);
lean_ctor_set(v___x_4530_, 1, v___x_4529_);
if (v_isShared_4518_ == 0)
{
lean_ctor_set_tag(v___x_4517_, 0);
lean_ctor_set(v___x_4517_, 0, v___x_4530_);
v___x_4532_ = v___x_4517_;
goto v_reusejp_4531_;
}
else
{
lean_object* v_reuseFailAlloc_4533_; 
v_reuseFailAlloc_4533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4533_, 0, v___x_4530_);
v___x_4532_ = v_reuseFailAlloc_4533_;
goto v_reusejp_4531_;
}
v_reusejp_4531_:
{
return v___x_4532_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___boxed(lean_object* v_a_4535_, lean_object* v_x_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_){
_start:
{
lean_object* v_res_4544_; 
v_res_4544_ = l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0(v_a_4535_, v_x_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_);
lean_dec(v___y_4542_);
lean_dec_ref(v___y_4541_);
lean_dec(v___y_4540_);
lean_dec_ref(v___y_4539_);
lean_dec(v___y_4538_);
lean_dec_ref(v___y_4537_);
return v_res_4544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__3___redArg(lean_object* v_oldTraces_4545_, lean_object* v_data_4546_, lean_object* v_ref_4547_, lean_object* v_msg_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_){
_start:
{
lean_object* v_fileName_4554_; lean_object* v_fileMap_4555_; lean_object* v_options_4556_; lean_object* v_currRecDepth_4557_; lean_object* v_maxRecDepth_4558_; lean_object* v_ref_4559_; lean_object* v_currNamespace_4560_; lean_object* v_openDecls_4561_; lean_object* v_initHeartbeats_4562_; lean_object* v_maxHeartbeats_4563_; lean_object* v_quotContext_4564_; lean_object* v_currMacroScope_4565_; uint8_t v_diag_4566_; lean_object* v_cancelTk_x3f_4567_; uint8_t v_suppressElabErrors_4568_; lean_object* v_inheritedTraceOptions_4569_; lean_object* v___x_4570_; lean_object* v_traceState_4571_; lean_object* v_traces_4572_; lean_object* v_ref_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; size_t v_sz_4576_; size_t v___x_4577_; lean_object* v___x_4578_; lean_object* v_msg_4579_; lean_object* v___x_4580_; lean_object* v_a_4581_; lean_object* v___x_4583_; uint8_t v_isShared_4584_; uint8_t v_isSharedCheck_4618_; 
v_fileName_4554_ = lean_ctor_get(v___y_4551_, 0);
v_fileMap_4555_ = lean_ctor_get(v___y_4551_, 1);
v_options_4556_ = lean_ctor_get(v___y_4551_, 2);
v_currRecDepth_4557_ = lean_ctor_get(v___y_4551_, 3);
v_maxRecDepth_4558_ = lean_ctor_get(v___y_4551_, 4);
v_ref_4559_ = lean_ctor_get(v___y_4551_, 5);
v_currNamespace_4560_ = lean_ctor_get(v___y_4551_, 6);
v_openDecls_4561_ = lean_ctor_get(v___y_4551_, 7);
v_initHeartbeats_4562_ = lean_ctor_get(v___y_4551_, 8);
v_maxHeartbeats_4563_ = lean_ctor_get(v___y_4551_, 9);
v_quotContext_4564_ = lean_ctor_get(v___y_4551_, 10);
v_currMacroScope_4565_ = lean_ctor_get(v___y_4551_, 11);
v_diag_4566_ = lean_ctor_get_uint8(v___y_4551_, sizeof(void*)*14);
v_cancelTk_x3f_4567_ = lean_ctor_get(v___y_4551_, 12);
v_suppressElabErrors_4568_ = lean_ctor_get_uint8(v___y_4551_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_4569_ = lean_ctor_get(v___y_4551_, 13);
v___x_4570_ = lean_st_ref_get(v___y_4552_);
v_traceState_4571_ = lean_ctor_get(v___x_4570_, 4);
lean_inc_ref(v_traceState_4571_);
lean_dec(v___x_4570_);
v_traces_4572_ = lean_ctor_get(v_traceState_4571_, 0);
lean_inc_ref(v_traces_4572_);
lean_dec_ref(v_traceState_4571_);
v_ref_4573_ = l_Lean_replaceRef(v_ref_4547_, v_ref_4559_);
lean_inc_ref(v_inheritedTraceOptions_4569_);
lean_inc(v_cancelTk_x3f_4567_);
lean_inc(v_currMacroScope_4565_);
lean_inc(v_quotContext_4564_);
lean_inc(v_maxHeartbeats_4563_);
lean_inc(v_initHeartbeats_4562_);
lean_inc(v_openDecls_4561_);
lean_inc(v_currNamespace_4560_);
lean_inc(v_maxRecDepth_4558_);
lean_inc(v_currRecDepth_4557_);
lean_inc_ref(v_options_4556_);
lean_inc_ref(v_fileMap_4555_);
lean_inc_ref(v_fileName_4554_);
v___x_4574_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_4574_, 0, v_fileName_4554_);
lean_ctor_set(v___x_4574_, 1, v_fileMap_4555_);
lean_ctor_set(v___x_4574_, 2, v_options_4556_);
lean_ctor_set(v___x_4574_, 3, v_currRecDepth_4557_);
lean_ctor_set(v___x_4574_, 4, v_maxRecDepth_4558_);
lean_ctor_set(v___x_4574_, 5, v_ref_4573_);
lean_ctor_set(v___x_4574_, 6, v_currNamespace_4560_);
lean_ctor_set(v___x_4574_, 7, v_openDecls_4561_);
lean_ctor_set(v___x_4574_, 8, v_initHeartbeats_4562_);
lean_ctor_set(v___x_4574_, 9, v_maxHeartbeats_4563_);
lean_ctor_set(v___x_4574_, 10, v_quotContext_4564_);
lean_ctor_set(v___x_4574_, 11, v_currMacroScope_4565_);
lean_ctor_set(v___x_4574_, 12, v_cancelTk_x3f_4567_);
lean_ctor_set(v___x_4574_, 13, v_inheritedTraceOptions_4569_);
lean_ctor_set_uint8(v___x_4574_, sizeof(void*)*14, v_diag_4566_);
lean_ctor_set_uint8(v___x_4574_, sizeof(void*)*14 + 1, v_suppressElabErrors_4568_);
v___x_4575_ = l_Lean_PersistentArray_toArray___redArg(v_traces_4572_);
lean_dec_ref(v_traces_4572_);
v_sz_4576_ = lean_array_size(v___x_4575_);
v___x_4577_ = ((size_t)0ULL);
v___x_4578_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4_spec__5(v_sz_4576_, v___x_4577_, v___x_4575_);
v_msg_4579_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_4579_, 0, v_data_4546_);
lean_ctor_set(v_msg_4579_, 1, v_msg_4548_);
lean_ctor_set(v_msg_4579_, 2, v___x_4578_);
v___x_4580_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0_spec__0(v_msg_4579_, v___y_4549_, v___y_4550_, v___x_4574_, v___y_4552_);
lean_dec_ref_known(v___x_4574_, 14);
v_a_4581_ = lean_ctor_get(v___x_4580_, 0);
v_isSharedCheck_4618_ = !lean_is_exclusive(v___x_4580_);
if (v_isSharedCheck_4618_ == 0)
{
v___x_4583_ = v___x_4580_;
v_isShared_4584_ = v_isSharedCheck_4618_;
goto v_resetjp_4582_;
}
else
{
lean_inc(v_a_4581_);
lean_dec(v___x_4580_);
v___x_4583_ = lean_box(0);
v_isShared_4584_ = v_isSharedCheck_4618_;
goto v_resetjp_4582_;
}
v_resetjp_4582_:
{
lean_object* v___x_4585_; lean_object* v_traceState_4586_; lean_object* v_env_4587_; lean_object* v_nextMacroScope_4588_; lean_object* v_ngen_4589_; lean_object* v_auxDeclNGen_4590_; lean_object* v_cache_4591_; lean_object* v_messages_4592_; lean_object* v_infoState_4593_; lean_object* v_snapshotTasks_4594_; lean_object* v___x_4596_; uint8_t v_isShared_4597_; uint8_t v_isSharedCheck_4617_; 
v___x_4585_ = lean_st_ref_take(v___y_4552_);
v_traceState_4586_ = lean_ctor_get(v___x_4585_, 4);
v_env_4587_ = lean_ctor_get(v___x_4585_, 0);
v_nextMacroScope_4588_ = lean_ctor_get(v___x_4585_, 1);
v_ngen_4589_ = lean_ctor_get(v___x_4585_, 2);
v_auxDeclNGen_4590_ = lean_ctor_get(v___x_4585_, 3);
v_cache_4591_ = lean_ctor_get(v___x_4585_, 5);
v_messages_4592_ = lean_ctor_get(v___x_4585_, 6);
v_infoState_4593_ = lean_ctor_get(v___x_4585_, 7);
v_snapshotTasks_4594_ = lean_ctor_get(v___x_4585_, 8);
v_isSharedCheck_4617_ = !lean_is_exclusive(v___x_4585_);
if (v_isSharedCheck_4617_ == 0)
{
v___x_4596_ = v___x_4585_;
v_isShared_4597_ = v_isSharedCheck_4617_;
goto v_resetjp_4595_;
}
else
{
lean_inc(v_snapshotTasks_4594_);
lean_inc(v_infoState_4593_);
lean_inc(v_messages_4592_);
lean_inc(v_cache_4591_);
lean_inc(v_traceState_4586_);
lean_inc(v_auxDeclNGen_4590_);
lean_inc(v_ngen_4589_);
lean_inc(v_nextMacroScope_4588_);
lean_inc(v_env_4587_);
lean_dec(v___x_4585_);
v___x_4596_ = lean_box(0);
v_isShared_4597_ = v_isSharedCheck_4617_;
goto v_resetjp_4595_;
}
v_resetjp_4595_:
{
uint64_t v_tid_4598_; lean_object* v___x_4600_; uint8_t v_isShared_4601_; uint8_t v_isSharedCheck_4615_; 
v_tid_4598_ = lean_ctor_get_uint64(v_traceState_4586_, sizeof(void*)*1);
v_isSharedCheck_4615_ = !lean_is_exclusive(v_traceState_4586_);
if (v_isSharedCheck_4615_ == 0)
{
lean_object* v_unused_4616_; 
v_unused_4616_ = lean_ctor_get(v_traceState_4586_, 0);
lean_dec(v_unused_4616_);
v___x_4600_ = v_traceState_4586_;
v_isShared_4601_ = v_isSharedCheck_4615_;
goto v_resetjp_4599_;
}
else
{
lean_dec(v_traceState_4586_);
v___x_4600_ = lean_box(0);
v_isShared_4601_ = v_isSharedCheck_4615_;
goto v_resetjp_4599_;
}
v_resetjp_4599_:
{
lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4605_; 
v___x_4602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4602_, 0, v_ref_4547_);
lean_ctor_set(v___x_4602_, 1, v_a_4581_);
v___x_4603_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_4545_, v___x_4602_);
if (v_isShared_4601_ == 0)
{
lean_ctor_set(v___x_4600_, 0, v___x_4603_);
v___x_4605_ = v___x_4600_;
goto v_reusejp_4604_;
}
else
{
lean_object* v_reuseFailAlloc_4614_; 
v_reuseFailAlloc_4614_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4614_, 0, v___x_4603_);
lean_ctor_set_uint64(v_reuseFailAlloc_4614_, sizeof(void*)*1, v_tid_4598_);
v___x_4605_ = v_reuseFailAlloc_4614_;
goto v_reusejp_4604_;
}
v_reusejp_4604_:
{
lean_object* v___x_4607_; 
if (v_isShared_4597_ == 0)
{
lean_ctor_set(v___x_4596_, 4, v___x_4605_);
v___x_4607_ = v___x_4596_;
goto v_reusejp_4606_;
}
else
{
lean_object* v_reuseFailAlloc_4613_; 
v_reuseFailAlloc_4613_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4613_, 0, v_env_4587_);
lean_ctor_set(v_reuseFailAlloc_4613_, 1, v_nextMacroScope_4588_);
lean_ctor_set(v_reuseFailAlloc_4613_, 2, v_ngen_4589_);
lean_ctor_set(v_reuseFailAlloc_4613_, 3, v_auxDeclNGen_4590_);
lean_ctor_set(v_reuseFailAlloc_4613_, 4, v___x_4605_);
lean_ctor_set(v_reuseFailAlloc_4613_, 5, v_cache_4591_);
lean_ctor_set(v_reuseFailAlloc_4613_, 6, v_messages_4592_);
lean_ctor_set(v_reuseFailAlloc_4613_, 7, v_infoState_4593_);
lean_ctor_set(v_reuseFailAlloc_4613_, 8, v_snapshotTasks_4594_);
v___x_4607_ = v_reuseFailAlloc_4613_;
goto v_reusejp_4606_;
}
v_reusejp_4606_:
{
lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4611_; 
v___x_4608_ = lean_st_ref_set(v___y_4552_, v___x_4607_);
v___x_4609_ = lean_box(0);
if (v_isShared_4584_ == 0)
{
lean_ctor_set(v___x_4583_, 0, v___x_4609_);
v___x_4611_ = v___x_4583_;
goto v_reusejp_4610_;
}
else
{
lean_object* v_reuseFailAlloc_4612_; 
v_reuseFailAlloc_4612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4612_, 0, v___x_4609_);
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__3___redArg___boxed(lean_object* v_oldTraces_4619_, lean_object* v_data_4620_, lean_object* v_ref_4621_, lean_object* v_msg_4622_, lean_object* v___y_4623_, lean_object* v___y_4624_, lean_object* v___y_4625_, lean_object* v___y_4626_, lean_object* v___y_4627_){
_start:
{
lean_object* v_res_4628_; 
v_res_4628_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__3___redArg(v_oldTraces_4619_, v_data_4620_, v_ref_4621_, v_msg_4622_, v___y_4623_, v___y_4624_, v___y_4625_, v___y_4626_);
lean_dec(v___y_4626_);
lean_dec_ref(v___y_4625_);
lean_dec(v___y_4624_);
lean_dec_ref(v___y_4623_);
return v_res_4628_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4___redArg(lean_object* v_x_4629_){
_start:
{
if (lean_obj_tag(v_x_4629_) == 0)
{
lean_object* v_a_4631_; lean_object* v___x_4633_; uint8_t v_isShared_4634_; uint8_t v_isSharedCheck_4638_; 
v_a_4631_ = lean_ctor_get(v_x_4629_, 0);
v_isSharedCheck_4638_ = !lean_is_exclusive(v_x_4629_);
if (v_isSharedCheck_4638_ == 0)
{
v___x_4633_ = v_x_4629_;
v_isShared_4634_ = v_isSharedCheck_4638_;
goto v_resetjp_4632_;
}
else
{
lean_inc(v_a_4631_);
lean_dec(v_x_4629_);
v___x_4633_ = lean_box(0);
v_isShared_4634_ = v_isSharedCheck_4638_;
goto v_resetjp_4632_;
}
v_resetjp_4632_:
{
lean_object* v___x_4636_; 
if (v_isShared_4634_ == 0)
{
lean_ctor_set_tag(v___x_4633_, 1);
v___x_4636_ = v___x_4633_;
goto v_reusejp_4635_;
}
else
{
lean_object* v_reuseFailAlloc_4637_; 
v_reuseFailAlloc_4637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4637_, 0, v_a_4631_);
v___x_4636_ = v_reuseFailAlloc_4637_;
goto v_reusejp_4635_;
}
v_reusejp_4635_:
{
return v___x_4636_;
}
}
}
else
{
lean_object* v_a_4639_; lean_object* v___x_4641_; uint8_t v_isShared_4642_; uint8_t v_isSharedCheck_4646_; 
v_a_4639_ = lean_ctor_get(v_x_4629_, 0);
v_isSharedCheck_4646_ = !lean_is_exclusive(v_x_4629_);
if (v_isSharedCheck_4646_ == 0)
{
v___x_4641_ = v_x_4629_;
v_isShared_4642_ = v_isSharedCheck_4646_;
goto v_resetjp_4640_;
}
else
{
lean_inc(v_a_4639_);
lean_dec(v_x_4629_);
v___x_4641_ = lean_box(0);
v_isShared_4642_ = v_isSharedCheck_4646_;
goto v_resetjp_4640_;
}
v_resetjp_4640_:
{
lean_object* v___x_4644_; 
if (v_isShared_4642_ == 0)
{
lean_ctor_set_tag(v___x_4641_, 0);
v___x_4644_ = v___x_4641_;
goto v_reusejp_4643_;
}
else
{
lean_object* v_reuseFailAlloc_4645_; 
v_reuseFailAlloc_4645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4645_, 0, v_a_4639_);
v___x_4644_ = v_reuseFailAlloc_4645_;
goto v_reusejp_4643_;
}
v_reusejp_4643_:
{
return v___x_4644_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4___redArg___boxed(lean_object* v_x_4647_, lean_object* v___y_4648_){
_start:
{
lean_object* v_res_4649_; 
v_res_4649_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4___redArg(v_x_4647_);
return v_res_4649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2(lean_object* v_cls_4650_, uint8_t v_collapsed_4651_, lean_object* v_tag_4652_, lean_object* v_opts_4653_, uint8_t v_clsEnabled_4654_, lean_object* v_oldTraces_4655_, lean_object* v_msg_4656_, lean_object* v_resStartStop_4657_, lean_object* v___y_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_){
_start:
{
lean_object* v_fst_4665_; lean_object* v_snd_4666_; lean_object* v___y_4668_; lean_object* v___y_4669_; lean_object* v_data_4670_; lean_object* v_fst_4681_; lean_object* v_snd_4682_; lean_object* v___x_4683_; uint8_t v___x_4684_; lean_object* v___y_4686_; lean_object* v_a_4687_; uint8_t v___y_4702_; double v___y_4733_; 
v_fst_4665_ = lean_ctor_get(v_resStartStop_4657_, 0);
lean_inc(v_fst_4665_);
v_snd_4666_ = lean_ctor_get(v_resStartStop_4657_, 1);
lean_inc(v_snd_4666_);
lean_dec_ref(v_resStartStop_4657_);
v_fst_4681_ = lean_ctor_get(v_snd_4666_, 0);
lean_inc(v_fst_4681_);
v_snd_4682_ = lean_ctor_get(v_snd_4666_, 1);
lean_inc(v_snd_4682_);
lean_dec(v_snd_4666_);
v___x_4683_ = l_Lean_trace_profiler;
v___x_4684_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_4653_, v___x_4683_);
if (v___x_4684_ == 0)
{
v___y_4702_ = v___x_4684_;
goto v___jp_4701_;
}
else
{
lean_object* v___x_4738_; uint8_t v___x_4739_; 
v___x_4738_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4739_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_4653_, v___x_4738_);
if (v___x_4739_ == 0)
{
lean_object* v___x_4740_; lean_object* v___x_4741_; double v___x_4742_; double v___x_4743_; double v___x_4744_; 
v___x_4740_ = l_Lean_trace_profiler_threshold;
v___x_4741_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_4653_, v___x_4740_);
v___x_4742_ = lean_float_of_nat(v___x_4741_);
v___x_4743_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2);
v___x_4744_ = lean_float_div(v___x_4742_, v___x_4743_);
v___y_4733_ = v___x_4744_;
goto v___jp_4732_;
}
else
{
lean_object* v___x_4745_; lean_object* v___x_4746_; double v___x_4747_; 
v___x_4745_ = l_Lean_trace_profiler_threshold;
v___x_4746_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_4653_, v___x_4745_);
v___x_4747_ = lean_float_of_nat(v___x_4746_);
v___y_4733_ = v___x_4747_;
goto v___jp_4732_;
}
}
v___jp_4667_:
{
lean_object* v___x_4671_; 
lean_inc(v___y_4669_);
v___x_4671_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__3___redArg(v_oldTraces_4655_, v_data_4670_, v___y_4669_, v___y_4668_, v___y_4660_, v___y_4661_, v___y_4662_, v___y_4663_);
if (lean_obj_tag(v___x_4671_) == 0)
{
lean_object* v___x_4672_; 
lean_dec_ref_known(v___x_4671_, 1);
v___x_4672_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4___redArg(v_fst_4665_);
return v___x_4672_;
}
else
{
lean_object* v_a_4673_; lean_object* v___x_4675_; uint8_t v_isShared_4676_; uint8_t v_isSharedCheck_4680_; 
lean_dec(v_fst_4665_);
v_a_4673_ = lean_ctor_get(v___x_4671_, 0);
v_isSharedCheck_4680_ = !lean_is_exclusive(v___x_4671_);
if (v_isSharedCheck_4680_ == 0)
{
v___x_4675_ = v___x_4671_;
v_isShared_4676_ = v_isSharedCheck_4680_;
goto v_resetjp_4674_;
}
else
{
lean_inc(v_a_4673_);
lean_dec(v___x_4671_);
v___x_4675_ = lean_box(0);
v_isShared_4676_ = v_isSharedCheck_4680_;
goto v_resetjp_4674_;
}
v_resetjp_4674_:
{
lean_object* v___x_4678_; 
if (v_isShared_4676_ == 0)
{
v___x_4678_ = v___x_4675_;
goto v_reusejp_4677_;
}
else
{
lean_object* v_reuseFailAlloc_4679_; 
v_reuseFailAlloc_4679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4679_, 0, v_a_4673_);
v___x_4678_ = v_reuseFailAlloc_4679_;
goto v_reusejp_4677_;
}
v_reusejp_4677_:
{
return v___x_4678_;
}
}
}
}
v___jp_4685_:
{
uint8_t v_result_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; double v___x_4691_; lean_object* v_data_4692_; 
v_result_4688_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__6(v_fst_4665_);
v___x_4689_ = lean_box(v_result_4688_);
v___x_4690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4690_, 0, v___x_4689_);
v___x_4691_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_4652_);
lean_inc_ref(v___x_4690_);
lean_inc(v_cls_4650_);
v_data_4692_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4692_, 0, v_cls_4650_);
lean_ctor_set(v_data_4692_, 1, v___x_4690_);
lean_ctor_set(v_data_4692_, 2, v_tag_4652_);
lean_ctor_set_float(v_data_4692_, sizeof(void*)*3, v___x_4691_);
lean_ctor_set_float(v_data_4692_, sizeof(void*)*3 + 8, v___x_4691_);
lean_ctor_set_uint8(v_data_4692_, sizeof(void*)*3 + 16, v_collapsed_4651_);
if (v___x_4684_ == 0)
{
lean_dec_ref_known(v___x_4690_, 1);
lean_dec(v_snd_4682_);
lean_dec(v_fst_4681_);
lean_dec_ref(v_tag_4652_);
lean_dec(v_cls_4650_);
v___y_4668_ = v_a_4687_;
v___y_4669_ = v___y_4686_;
v_data_4670_ = v_data_4692_;
goto v___jp_4667_;
}
else
{
lean_object* v_data_4693_; double v___x_4694_; double v___x_4695_; 
lean_dec_ref_known(v_data_4692_, 3);
v_data_4693_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4693_, 0, v_cls_4650_);
lean_ctor_set(v_data_4693_, 1, v___x_4690_);
lean_ctor_set(v_data_4693_, 2, v_tag_4652_);
v___x_4694_ = lean_unbox_float(v_fst_4681_);
lean_dec(v_fst_4681_);
lean_ctor_set_float(v_data_4693_, sizeof(void*)*3, v___x_4694_);
v___x_4695_ = lean_unbox_float(v_snd_4682_);
lean_dec(v_snd_4682_);
lean_ctor_set_float(v_data_4693_, sizeof(void*)*3 + 8, v___x_4695_);
lean_ctor_set_uint8(v_data_4693_, sizeof(void*)*3 + 16, v_collapsed_4651_);
v___y_4668_ = v_a_4687_;
v___y_4669_ = v___y_4686_;
v_data_4670_ = v_data_4693_;
goto v___jp_4667_;
}
}
v___jp_4696_:
{
lean_object* v_ref_4697_; lean_object* v___x_4698_; 
v_ref_4697_ = lean_ctor_get(v___y_4662_, 5);
lean_inc(v___y_4663_);
lean_inc_ref(v___y_4662_);
lean_inc(v___y_4661_);
lean_inc_ref(v___y_4660_);
lean_inc(v___y_4659_);
lean_inc_ref(v___y_4658_);
lean_inc(v_fst_4665_);
v___x_4698_ = lean_apply_8(v_msg_4656_, v_fst_4665_, v___y_4658_, v___y_4659_, v___y_4660_, v___y_4661_, v___y_4662_, v___y_4663_, lean_box(0));
if (lean_obj_tag(v___x_4698_) == 0)
{
lean_object* v_a_4699_; 
v_a_4699_ = lean_ctor_get(v___x_4698_, 0);
lean_inc(v_a_4699_);
lean_dec_ref_known(v___x_4698_, 1);
v___y_4686_ = v_ref_4697_;
v_a_4687_ = v_a_4699_;
goto v___jp_4685_;
}
else
{
lean_object* v___x_4700_; 
lean_dec_ref_known(v___x_4698_, 1);
v___x_4700_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1);
v___y_4686_ = v_ref_4697_;
v_a_4687_ = v___x_4700_;
goto v___jp_4685_;
}
}
v___jp_4701_:
{
if (v_clsEnabled_4654_ == 0)
{
if (v___y_4702_ == 0)
{
lean_object* v___x_4703_; lean_object* v_traceState_4704_; lean_object* v_env_4705_; lean_object* v_nextMacroScope_4706_; lean_object* v_ngen_4707_; lean_object* v_auxDeclNGen_4708_; lean_object* v_cache_4709_; lean_object* v_messages_4710_; lean_object* v_infoState_4711_; lean_object* v_snapshotTasks_4712_; lean_object* v___x_4714_; uint8_t v_isShared_4715_; uint8_t v_isSharedCheck_4731_; 
lean_dec(v_snd_4682_);
lean_dec(v_fst_4681_);
lean_dec_ref(v_msg_4656_);
lean_dec_ref(v_tag_4652_);
lean_dec(v_cls_4650_);
v___x_4703_ = lean_st_ref_take(v___y_4663_);
v_traceState_4704_ = lean_ctor_get(v___x_4703_, 4);
v_env_4705_ = lean_ctor_get(v___x_4703_, 0);
v_nextMacroScope_4706_ = lean_ctor_get(v___x_4703_, 1);
v_ngen_4707_ = lean_ctor_get(v___x_4703_, 2);
v_auxDeclNGen_4708_ = lean_ctor_get(v___x_4703_, 3);
v_cache_4709_ = lean_ctor_get(v___x_4703_, 5);
v_messages_4710_ = lean_ctor_get(v___x_4703_, 6);
v_infoState_4711_ = lean_ctor_get(v___x_4703_, 7);
v_snapshotTasks_4712_ = lean_ctor_get(v___x_4703_, 8);
v_isSharedCheck_4731_ = !lean_is_exclusive(v___x_4703_);
if (v_isSharedCheck_4731_ == 0)
{
v___x_4714_ = v___x_4703_;
v_isShared_4715_ = v_isSharedCheck_4731_;
goto v_resetjp_4713_;
}
else
{
lean_inc(v_snapshotTasks_4712_);
lean_inc(v_infoState_4711_);
lean_inc(v_messages_4710_);
lean_inc(v_cache_4709_);
lean_inc(v_traceState_4704_);
lean_inc(v_auxDeclNGen_4708_);
lean_inc(v_ngen_4707_);
lean_inc(v_nextMacroScope_4706_);
lean_inc(v_env_4705_);
lean_dec(v___x_4703_);
v___x_4714_ = lean_box(0);
v_isShared_4715_ = v_isSharedCheck_4731_;
goto v_resetjp_4713_;
}
v_resetjp_4713_:
{
uint64_t v_tid_4716_; lean_object* v_traces_4717_; lean_object* v___x_4719_; uint8_t v_isShared_4720_; uint8_t v_isSharedCheck_4730_; 
v_tid_4716_ = lean_ctor_get_uint64(v_traceState_4704_, sizeof(void*)*1);
v_traces_4717_ = lean_ctor_get(v_traceState_4704_, 0);
v_isSharedCheck_4730_ = !lean_is_exclusive(v_traceState_4704_);
if (v_isSharedCheck_4730_ == 0)
{
v___x_4719_ = v_traceState_4704_;
v_isShared_4720_ = v_isSharedCheck_4730_;
goto v_resetjp_4718_;
}
else
{
lean_inc(v_traces_4717_);
lean_dec(v_traceState_4704_);
v___x_4719_ = lean_box(0);
v_isShared_4720_ = v_isSharedCheck_4730_;
goto v_resetjp_4718_;
}
v_resetjp_4718_:
{
lean_object* v___x_4721_; lean_object* v___x_4723_; 
v___x_4721_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_4655_, v_traces_4717_);
lean_dec_ref(v_traces_4717_);
if (v_isShared_4720_ == 0)
{
lean_ctor_set(v___x_4719_, 0, v___x_4721_);
v___x_4723_ = v___x_4719_;
goto v_reusejp_4722_;
}
else
{
lean_object* v_reuseFailAlloc_4729_; 
v_reuseFailAlloc_4729_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4729_, 0, v___x_4721_);
lean_ctor_set_uint64(v_reuseFailAlloc_4729_, sizeof(void*)*1, v_tid_4716_);
v___x_4723_ = v_reuseFailAlloc_4729_;
goto v_reusejp_4722_;
}
v_reusejp_4722_:
{
lean_object* v___x_4725_; 
if (v_isShared_4715_ == 0)
{
lean_ctor_set(v___x_4714_, 4, v___x_4723_);
v___x_4725_ = v___x_4714_;
goto v_reusejp_4724_;
}
else
{
lean_object* v_reuseFailAlloc_4728_; 
v_reuseFailAlloc_4728_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4728_, 0, v_env_4705_);
lean_ctor_set(v_reuseFailAlloc_4728_, 1, v_nextMacroScope_4706_);
lean_ctor_set(v_reuseFailAlloc_4728_, 2, v_ngen_4707_);
lean_ctor_set(v_reuseFailAlloc_4728_, 3, v_auxDeclNGen_4708_);
lean_ctor_set(v_reuseFailAlloc_4728_, 4, v___x_4723_);
lean_ctor_set(v_reuseFailAlloc_4728_, 5, v_cache_4709_);
lean_ctor_set(v_reuseFailAlloc_4728_, 6, v_messages_4710_);
lean_ctor_set(v_reuseFailAlloc_4728_, 7, v_infoState_4711_);
lean_ctor_set(v_reuseFailAlloc_4728_, 8, v_snapshotTasks_4712_);
v___x_4725_ = v_reuseFailAlloc_4728_;
goto v_reusejp_4724_;
}
v_reusejp_4724_:
{
lean_object* v___x_4726_; lean_object* v___x_4727_; 
v___x_4726_ = lean_st_ref_set(v___y_4663_, v___x_4725_);
v___x_4727_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4___redArg(v_fst_4665_);
return v___x_4727_;
}
}
}
}
}
else
{
goto v___jp_4696_;
}
}
else
{
goto v___jp_4696_;
}
}
v___jp_4732_:
{
double v___x_4734_; double v___x_4735_; double v___x_4736_; uint8_t v___x_4737_; 
v___x_4734_ = lean_unbox_float(v_snd_4682_);
v___x_4735_ = lean_unbox_float(v_fst_4681_);
v___x_4736_ = lean_float_sub(v___x_4734_, v___x_4735_);
v___x_4737_ = lean_float_decLt(v___y_4733_, v___x_4736_);
v___y_4702_ = v___x_4737_;
goto v___jp_4701_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2___boxed(lean_object* v_cls_4748_, lean_object* v_collapsed_4749_, lean_object* v_tag_4750_, lean_object* v_opts_4751_, lean_object* v_clsEnabled_4752_, lean_object* v_oldTraces_4753_, lean_object* v_msg_4754_, lean_object* v_resStartStop_4755_, lean_object* v___y_4756_, lean_object* v___y_4757_, lean_object* v___y_4758_, lean_object* v___y_4759_, lean_object* v___y_4760_, lean_object* v___y_4761_, lean_object* v___y_4762_){
_start:
{
uint8_t v_collapsed_boxed_4763_; uint8_t v_clsEnabled_boxed_4764_; lean_object* v_res_4765_; 
v_collapsed_boxed_4763_ = lean_unbox(v_collapsed_4749_);
v_clsEnabled_boxed_4764_ = lean_unbox(v_clsEnabled_4752_);
v_res_4765_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2(v_cls_4748_, v_collapsed_boxed_4763_, v_tag_4750_, v_opts_4751_, v_clsEnabled_boxed_4764_, v_oldTraces_4753_, v_msg_4754_, v_resStartStop_4755_, v___y_4756_, v___y_4757_, v___y_4758_, v___y_4759_, v___y_4760_, v___y_4761_);
lean_dec(v___y_4761_);
lean_dec_ref(v___y_4760_);
lean_dec(v___y_4759_);
lean_dec_ref(v___y_4758_);
lean_dec(v___y_4757_);
lean_dec_ref(v___y_4756_);
lean_dec_ref(v_opts_4751_);
return v_res_4765_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4767_; lean_object* v___x_4768_; 
v___x_4767_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__0));
v___x_4768_ = l_Lean_stringToMessageData(v___x_4767_);
return v___x_4768_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4770_; lean_object* v___x_4771_; 
v___x_4770_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__2));
v___x_4771_ = l_Lean_stringToMessageData(v___x_4770_);
return v___x_4771_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4773_; lean_object* v___x_4774_; 
v___x_4773_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__4));
v___x_4774_ = l_Lean_stringToMessageData(v___x_4773_);
return v___x_4774_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0(lean_object* v_a_4775_, lean_object* v___x_4776_, lean_object* v_x_4777_, lean_object* v___y_4778_, lean_object* v___y_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_, lean_object* v___y_4782_, lean_object* v___y_4783_){
_start:
{
if (lean_obj_tag(v_x_4777_) == 0)
{
lean_object* v_a_4785_; lean_object* v___x_4787_; uint8_t v_isShared_4788_; uint8_t v_isSharedCheck_4800_; 
lean_dec_ref(v___x_4776_);
v_a_4785_ = lean_ctor_get(v_x_4777_, 0);
v_isSharedCheck_4800_ = !lean_is_exclusive(v_x_4777_);
if (v_isSharedCheck_4800_ == 0)
{
v___x_4787_ = v_x_4777_;
v_isShared_4788_ = v_isSharedCheck_4800_;
goto v_resetjp_4786_;
}
else
{
lean_inc(v_a_4785_);
lean_dec(v_x_4777_);
v___x_4787_ = lean_box(0);
v_isShared_4788_ = v_isSharedCheck_4800_;
goto v_resetjp_4786_;
}
v_resetjp_4786_:
{
lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4798_; 
v___x_4789_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1);
v___x_4790_ = l_Lean_LocalDecl_userName(v_a_4775_);
v___x_4791_ = l_Lean_MessageData_ofName(v___x_4790_);
v___x_4792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4792_, 0, v___x_4789_);
lean_ctor_set(v___x_4792_, 1, v___x_4791_);
v___x_4793_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__3);
v___x_4794_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4794_, 0, v___x_4792_);
lean_ctor_set(v___x_4794_, 1, v___x_4793_);
v___x_4795_ = l_Lean_Exception_toMessageData(v_a_4785_);
v___x_4796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4796_, 0, v___x_4794_);
lean_ctor_set(v___x_4796_, 1, v___x_4795_);
if (v_isShared_4788_ == 0)
{
lean_ctor_set(v___x_4787_, 0, v___x_4796_);
v___x_4798_ = v___x_4787_;
goto v_reusejp_4797_;
}
else
{
lean_object* v_reuseFailAlloc_4799_; 
v_reuseFailAlloc_4799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4799_, 0, v___x_4796_);
v___x_4798_ = v_reuseFailAlloc_4799_;
goto v_reusejp_4797_;
}
v_reusejp_4797_:
{
return v___x_4798_;
}
}
}
else
{
lean_object* v_a_4801_; lean_object* v___x_4803_; uint8_t v_isShared_4804_; uint8_t v_isSharedCheck_4830_; 
v_a_4801_ = lean_ctor_get(v_x_4777_, 0);
v_isSharedCheck_4830_ = !lean_is_exclusive(v_x_4777_);
if (v_isSharedCheck_4830_ == 0)
{
v___x_4803_ = v_x_4777_;
v_isShared_4804_ = v_isSharedCheck_4830_;
goto v_resetjp_4802_;
}
else
{
lean_inc(v_a_4801_);
lean_dec(v_x_4777_);
v___x_4803_ = lean_box(0);
v_isShared_4804_ = v_isSharedCheck_4830_;
goto v_resetjp_4802_;
}
v_resetjp_4802_:
{
if (lean_obj_tag(v_a_4801_) == 0)
{
lean_object* v___x_4805_; lean_object* v___x_4806_; lean_object* v___x_4807_; lean_object* v___x_4808_; lean_object* v___x_4809_; lean_object* v___x_4810_; lean_object* v___x_4812_; 
lean_dec_ref_known(v_a_4801_, 0);
lean_dec_ref(v___x_4776_);
v___x_4805_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1);
v___x_4806_ = l_Lean_LocalDecl_userName(v_a_4775_);
v___x_4807_ = l_Lean_MessageData_ofName(v___x_4806_);
v___x_4808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4808_, 0, v___x_4805_);
lean_ctor_set(v___x_4808_, 1, v___x_4807_);
v___x_4809_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__5);
v___x_4810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4810_, 0, v___x_4808_);
lean_ctor_set(v___x_4810_, 1, v___x_4809_);
if (v_isShared_4804_ == 0)
{
lean_ctor_set_tag(v___x_4803_, 0);
lean_ctor_set(v___x_4803_, 0, v___x_4810_);
v___x_4812_ = v___x_4803_;
goto v_reusejp_4811_;
}
else
{
lean_object* v_reuseFailAlloc_4813_; 
v_reuseFailAlloc_4813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4813_, 0, v___x_4810_);
v___x_4812_ = v_reuseFailAlloc_4813_;
goto v_reusejp_4811_;
}
v_reusejp_4811_:
{
return v___x_4812_;
}
}
else
{
lean_object* v_e_x27_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; lean_object* v___x_4818_; lean_object* v___x_4819_; lean_object* v___x_4820_; lean_object* v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; lean_object* v___x_4825_; lean_object* v___x_4826_; lean_object* v___x_4828_; 
v_e_x27_4814_ = lean_ctor_get(v_a_4801_, 0);
lean_inc_ref(v_e_x27_4814_);
lean_dec_ref_known(v_a_4801_, 2);
v___x_4815_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1);
v___x_4816_ = l_Lean_LocalDecl_userName(v_a_4775_);
v___x_4817_ = l_Lean_MessageData_ofName(v___x_4816_);
v___x_4818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4818_, 0, v___x_4815_);
lean_ctor_set(v___x_4818_, 1, v___x_4817_);
v___x_4819_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8);
v___x_4820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4820_, 0, v___x_4818_);
lean_ctor_set(v___x_4820_, 1, v___x_4819_);
v___x_4821_ = l_Lean_indentExpr(v___x_4776_);
v___x_4822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4822_, 0, v___x_4820_);
lean_ctor_set(v___x_4822_, 1, v___x_4821_);
v___x_4823_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_4824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4824_, 0, v___x_4822_);
lean_ctor_set(v___x_4824_, 1, v___x_4823_);
v___x_4825_ = l_Lean_indentExpr(v_e_x27_4814_);
v___x_4826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4826_, 0, v___x_4824_);
lean_ctor_set(v___x_4826_, 1, v___x_4825_);
if (v_isShared_4804_ == 0)
{
lean_ctor_set_tag(v___x_4803_, 0);
lean_ctor_set(v___x_4803_, 0, v___x_4826_);
v___x_4828_ = v___x_4803_;
goto v_reusejp_4827_;
}
else
{
lean_object* v_reuseFailAlloc_4829_; 
v_reuseFailAlloc_4829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4829_, 0, v___x_4826_);
v___x_4828_ = v_reuseFailAlloc_4829_;
goto v_reusejp_4827_;
}
v_reusejp_4827_:
{
return v___x_4828_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___boxed(lean_object* v_a_4831_, lean_object* v___x_4832_, lean_object* v_x_4833_, lean_object* v___y_4834_, lean_object* v___y_4835_, lean_object* v___y_4836_, lean_object* v___y_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_, lean_object* v___y_4840_){
_start:
{
lean_object* v_res_4841_; 
v_res_4841_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0(v_a_4831_, v___x_4832_, v_x_4833_, v___y_4834_, v___y_4835_, v___y_4836_, v___y_4837_, v___y_4838_, v___y_4839_);
lean_dec(v___y_4839_);
lean_dec_ref(v___y_4838_);
lean_dec(v___y_4837_);
lean_dec_ref(v___y_4836_);
lean_dec(v___y_4835_);
lean_dec_ref(v___y_4834_);
lean_dec_ref(v_a_4831_);
return v_res_4841_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__7_spec__9___redArg(lean_object* v_x_4842_, lean_object* v_x_4843_, lean_object* v_x_4844_, lean_object* v_x_4845_){
_start:
{
lean_object* v_ks_4846_; lean_object* v_vs_4847_; lean_object* v___x_4849_; uint8_t v_isShared_4850_; uint8_t v_isSharedCheck_4871_; 
v_ks_4846_ = lean_ctor_get(v_x_4842_, 0);
v_vs_4847_ = lean_ctor_get(v_x_4842_, 1);
v_isSharedCheck_4871_ = !lean_is_exclusive(v_x_4842_);
if (v_isSharedCheck_4871_ == 0)
{
v___x_4849_ = v_x_4842_;
v_isShared_4850_ = v_isSharedCheck_4871_;
goto v_resetjp_4848_;
}
else
{
lean_inc(v_vs_4847_);
lean_inc(v_ks_4846_);
lean_dec(v_x_4842_);
v___x_4849_ = lean_box(0);
v_isShared_4850_ = v_isSharedCheck_4871_;
goto v_resetjp_4848_;
}
v_resetjp_4848_:
{
lean_object* v___x_4851_; uint8_t v___x_4852_; 
v___x_4851_ = lean_array_get_size(v_ks_4846_);
v___x_4852_ = lean_nat_dec_lt(v_x_4843_, v___x_4851_);
if (v___x_4852_ == 0)
{
lean_object* v___x_4853_; lean_object* v___x_4854_; lean_object* v___x_4856_; 
lean_dec(v_x_4843_);
v___x_4853_ = lean_array_push(v_ks_4846_, v_x_4844_);
v___x_4854_ = lean_array_push(v_vs_4847_, v_x_4845_);
if (v_isShared_4850_ == 0)
{
lean_ctor_set(v___x_4849_, 1, v___x_4854_);
lean_ctor_set(v___x_4849_, 0, v___x_4853_);
v___x_4856_ = v___x_4849_;
goto v_reusejp_4855_;
}
else
{
lean_object* v_reuseFailAlloc_4857_; 
v_reuseFailAlloc_4857_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4857_, 0, v___x_4853_);
lean_ctor_set(v_reuseFailAlloc_4857_, 1, v___x_4854_);
v___x_4856_ = v_reuseFailAlloc_4857_;
goto v_reusejp_4855_;
}
v_reusejp_4855_:
{
return v___x_4856_;
}
}
else
{
lean_object* v_k_x27_4858_; uint8_t v___x_4859_; 
v_k_x27_4858_ = lean_array_fget_borrowed(v_ks_4846_, v_x_4843_);
v___x_4859_ = l_Lean_instBEqMVarId_beq(v_x_4844_, v_k_x27_4858_);
if (v___x_4859_ == 0)
{
lean_object* v___x_4861_; 
if (v_isShared_4850_ == 0)
{
v___x_4861_ = v___x_4849_;
goto v_reusejp_4860_;
}
else
{
lean_object* v_reuseFailAlloc_4865_; 
v_reuseFailAlloc_4865_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4865_, 0, v_ks_4846_);
lean_ctor_set(v_reuseFailAlloc_4865_, 1, v_vs_4847_);
v___x_4861_ = v_reuseFailAlloc_4865_;
goto v_reusejp_4860_;
}
v_reusejp_4860_:
{
lean_object* v___x_4862_; lean_object* v___x_4863_; 
v___x_4862_ = lean_unsigned_to_nat(1u);
v___x_4863_ = lean_nat_add(v_x_4843_, v___x_4862_);
lean_dec(v_x_4843_);
v_x_4842_ = v___x_4861_;
v_x_4843_ = v___x_4863_;
goto _start;
}
}
else
{
lean_object* v___x_4866_; lean_object* v___x_4867_; lean_object* v___x_4869_; 
v___x_4866_ = lean_array_fset(v_ks_4846_, v_x_4843_, v_x_4844_);
v___x_4867_ = lean_array_fset(v_vs_4847_, v_x_4843_, v_x_4845_);
lean_dec(v_x_4843_);
if (v_isShared_4850_ == 0)
{
lean_ctor_set(v___x_4849_, 1, v___x_4867_);
lean_ctor_set(v___x_4849_, 0, v___x_4866_);
v___x_4869_ = v___x_4849_;
goto v_reusejp_4868_;
}
else
{
lean_object* v_reuseFailAlloc_4870_; 
v_reuseFailAlloc_4870_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4870_, 0, v___x_4866_);
lean_ctor_set(v_reuseFailAlloc_4870_, 1, v___x_4867_);
v___x_4869_ = v_reuseFailAlloc_4870_;
goto v_reusejp_4868_;
}
v_reusejp_4868_:
{
return v___x_4869_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__7___redArg(lean_object* v_n_4872_, lean_object* v_k_4873_, lean_object* v_v_4874_){
_start:
{
lean_object* v___x_4875_; lean_object* v___x_4876_; 
v___x_4875_ = lean_unsigned_to_nat(0u);
v___x_4876_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__7_spec__9___redArg(v_n_4872_, v___x_4875_, v_k_4873_, v_v_4874_);
return v___x_4876_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_4877_; 
v___x_4877_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_4877_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg(lean_object* v_x_4878_, size_t v_x_4879_, size_t v_x_4880_, lean_object* v_x_4881_, lean_object* v_x_4882_){
_start:
{
if (lean_obj_tag(v_x_4878_) == 0)
{
lean_object* v_es_4883_; size_t v___x_4884_; size_t v___x_4885_; lean_object* v_j_4886_; lean_object* v___x_4887_; uint8_t v___x_4888_; 
v_es_4883_ = lean_ctor_get(v_x_4878_, 0);
v___x_4884_ = ((size_t)31ULL);
v___x_4885_ = lean_usize_land(v_x_4879_, v___x_4884_);
v_j_4886_ = lean_usize_to_nat(v___x_4885_);
v___x_4887_ = lean_array_get_size(v_es_4883_);
v___x_4888_ = lean_nat_dec_lt(v_j_4886_, v___x_4887_);
if (v___x_4888_ == 0)
{
lean_dec(v_j_4886_);
lean_dec(v_x_4882_);
lean_dec(v_x_4881_);
return v_x_4878_;
}
else
{
lean_object* v___x_4890_; uint8_t v_isShared_4891_; uint8_t v_isSharedCheck_4927_; 
lean_inc_ref(v_es_4883_);
v_isSharedCheck_4927_ = !lean_is_exclusive(v_x_4878_);
if (v_isSharedCheck_4927_ == 0)
{
lean_object* v_unused_4928_; 
v_unused_4928_ = lean_ctor_get(v_x_4878_, 0);
lean_dec(v_unused_4928_);
v___x_4890_ = v_x_4878_;
v_isShared_4891_ = v_isSharedCheck_4927_;
goto v_resetjp_4889_;
}
else
{
lean_dec(v_x_4878_);
v___x_4890_ = lean_box(0);
v_isShared_4891_ = v_isSharedCheck_4927_;
goto v_resetjp_4889_;
}
v_resetjp_4889_:
{
lean_object* v_v_4892_; lean_object* v___x_4893_; lean_object* v_xs_x27_4894_; lean_object* v___y_4896_; 
v_v_4892_ = lean_array_fget(v_es_4883_, v_j_4886_);
v___x_4893_ = lean_box(0);
v_xs_x27_4894_ = lean_array_fset(v_es_4883_, v_j_4886_, v___x_4893_);
switch(lean_obj_tag(v_v_4892_))
{
case 0:
{
lean_object* v_key_4901_; lean_object* v_val_4902_; lean_object* v___x_4904_; uint8_t v_isShared_4905_; uint8_t v_isSharedCheck_4912_; 
v_key_4901_ = lean_ctor_get(v_v_4892_, 0);
v_val_4902_ = lean_ctor_get(v_v_4892_, 1);
v_isSharedCheck_4912_ = !lean_is_exclusive(v_v_4892_);
if (v_isSharedCheck_4912_ == 0)
{
v___x_4904_ = v_v_4892_;
v_isShared_4905_ = v_isSharedCheck_4912_;
goto v_resetjp_4903_;
}
else
{
lean_inc(v_val_4902_);
lean_inc(v_key_4901_);
lean_dec(v_v_4892_);
v___x_4904_ = lean_box(0);
v_isShared_4905_ = v_isSharedCheck_4912_;
goto v_resetjp_4903_;
}
v_resetjp_4903_:
{
uint8_t v___x_4906_; 
v___x_4906_ = l_Lean_instBEqMVarId_beq(v_x_4881_, v_key_4901_);
if (v___x_4906_ == 0)
{
lean_object* v___x_4907_; lean_object* v___x_4908_; 
lean_del_object(v___x_4904_);
v___x_4907_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_4901_, v_val_4902_, v_x_4881_, v_x_4882_);
v___x_4908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4908_, 0, v___x_4907_);
v___y_4896_ = v___x_4908_;
goto v___jp_4895_;
}
else
{
lean_object* v___x_4910_; 
lean_dec(v_val_4902_);
lean_dec(v_key_4901_);
if (v_isShared_4905_ == 0)
{
lean_ctor_set(v___x_4904_, 1, v_x_4882_);
lean_ctor_set(v___x_4904_, 0, v_x_4881_);
v___x_4910_ = v___x_4904_;
goto v_reusejp_4909_;
}
else
{
lean_object* v_reuseFailAlloc_4911_; 
v_reuseFailAlloc_4911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4911_, 0, v_x_4881_);
lean_ctor_set(v_reuseFailAlloc_4911_, 1, v_x_4882_);
v___x_4910_ = v_reuseFailAlloc_4911_;
goto v_reusejp_4909_;
}
v_reusejp_4909_:
{
v___y_4896_ = v___x_4910_;
goto v___jp_4895_;
}
}
}
}
case 1:
{
lean_object* v_node_4913_; lean_object* v___x_4915_; uint8_t v_isShared_4916_; uint8_t v_isSharedCheck_4925_; 
v_node_4913_ = lean_ctor_get(v_v_4892_, 0);
v_isSharedCheck_4925_ = !lean_is_exclusive(v_v_4892_);
if (v_isSharedCheck_4925_ == 0)
{
v___x_4915_ = v_v_4892_;
v_isShared_4916_ = v_isSharedCheck_4925_;
goto v_resetjp_4914_;
}
else
{
lean_inc(v_node_4913_);
lean_dec(v_v_4892_);
v___x_4915_ = lean_box(0);
v_isShared_4916_ = v_isSharedCheck_4925_;
goto v_resetjp_4914_;
}
v_resetjp_4914_:
{
size_t v___x_4917_; size_t v___x_4918_; size_t v___x_4919_; size_t v___x_4920_; lean_object* v___x_4921_; lean_object* v___x_4923_; 
v___x_4917_ = ((size_t)5ULL);
v___x_4918_ = lean_usize_shift_right(v_x_4879_, v___x_4917_);
v___x_4919_ = ((size_t)1ULL);
v___x_4920_ = lean_usize_add(v_x_4880_, v___x_4919_);
v___x_4921_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg(v_node_4913_, v___x_4918_, v___x_4920_, v_x_4881_, v_x_4882_);
if (v_isShared_4916_ == 0)
{
lean_ctor_set(v___x_4915_, 0, v___x_4921_);
v___x_4923_ = v___x_4915_;
goto v_reusejp_4922_;
}
else
{
lean_object* v_reuseFailAlloc_4924_; 
v_reuseFailAlloc_4924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4924_, 0, v___x_4921_);
v___x_4923_ = v_reuseFailAlloc_4924_;
goto v_reusejp_4922_;
}
v_reusejp_4922_:
{
v___y_4896_ = v___x_4923_;
goto v___jp_4895_;
}
}
}
default: 
{
lean_object* v___x_4926_; 
v___x_4926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4926_, 0, v_x_4881_);
lean_ctor_set(v___x_4926_, 1, v_x_4882_);
v___y_4896_ = v___x_4926_;
goto v___jp_4895_;
}
}
v___jp_4895_:
{
lean_object* v___x_4897_; lean_object* v___x_4899_; 
v___x_4897_ = lean_array_fset(v_xs_x27_4894_, v_j_4886_, v___y_4896_);
lean_dec(v_j_4886_);
if (v_isShared_4891_ == 0)
{
lean_ctor_set(v___x_4890_, 0, v___x_4897_);
v___x_4899_ = v___x_4890_;
goto v_reusejp_4898_;
}
else
{
lean_object* v_reuseFailAlloc_4900_; 
v_reuseFailAlloc_4900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4900_, 0, v___x_4897_);
v___x_4899_ = v_reuseFailAlloc_4900_;
goto v_reusejp_4898_;
}
v_reusejp_4898_:
{
return v___x_4899_;
}
}
}
}
}
else
{
lean_object* v_ks_4929_; lean_object* v_vs_4930_; lean_object* v___x_4932_; uint8_t v_isShared_4933_; uint8_t v_isSharedCheck_4950_; 
v_ks_4929_ = lean_ctor_get(v_x_4878_, 0);
v_vs_4930_ = lean_ctor_get(v_x_4878_, 1);
v_isSharedCheck_4950_ = !lean_is_exclusive(v_x_4878_);
if (v_isSharedCheck_4950_ == 0)
{
v___x_4932_ = v_x_4878_;
v_isShared_4933_ = v_isSharedCheck_4950_;
goto v_resetjp_4931_;
}
else
{
lean_inc(v_vs_4930_);
lean_inc(v_ks_4929_);
lean_dec(v_x_4878_);
v___x_4932_ = lean_box(0);
v_isShared_4933_ = v_isSharedCheck_4950_;
goto v_resetjp_4931_;
}
v_resetjp_4931_:
{
lean_object* v___x_4935_; 
if (v_isShared_4933_ == 0)
{
v___x_4935_ = v___x_4932_;
goto v_reusejp_4934_;
}
else
{
lean_object* v_reuseFailAlloc_4949_; 
v_reuseFailAlloc_4949_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4949_, 0, v_ks_4929_);
lean_ctor_set(v_reuseFailAlloc_4949_, 1, v_vs_4930_);
v___x_4935_ = v_reuseFailAlloc_4949_;
goto v_reusejp_4934_;
}
v_reusejp_4934_:
{
lean_object* v_newNode_4936_; uint8_t v___y_4938_; size_t v___x_4944_; uint8_t v___x_4945_; 
v_newNode_4936_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__7___redArg(v___x_4935_, v_x_4881_, v_x_4882_);
v___x_4944_ = ((size_t)7ULL);
v___x_4945_ = lean_usize_dec_le(v___x_4944_, v_x_4880_);
if (v___x_4945_ == 0)
{
lean_object* v___x_4946_; lean_object* v___x_4947_; uint8_t v___x_4948_; 
v___x_4946_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4936_);
v___x_4947_ = lean_unsigned_to_nat(4u);
v___x_4948_ = lean_nat_dec_lt(v___x_4946_, v___x_4947_);
lean_dec(v___x_4946_);
v___y_4938_ = v___x_4948_;
goto v___jp_4937_;
}
else
{
v___y_4938_ = v___x_4945_;
goto v___jp_4937_;
}
v___jp_4937_:
{
if (v___y_4938_ == 0)
{
lean_object* v_ks_4939_; lean_object* v_vs_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; 
v_ks_4939_ = lean_ctor_get(v_newNode_4936_, 0);
lean_inc_ref(v_ks_4939_);
v_vs_4940_ = lean_ctor_get(v_newNode_4936_, 1);
lean_inc_ref(v_vs_4940_);
lean_dec_ref(v_newNode_4936_);
v___x_4941_ = lean_unsigned_to_nat(0u);
v___x_4942_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg___closed__0);
v___x_4943_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__8___redArg(v_x_4880_, v_ks_4939_, v_vs_4940_, v___x_4941_, v___x_4942_);
lean_dec_ref(v_vs_4940_);
lean_dec_ref(v_ks_4939_);
return v___x_4943_;
}
else
{
return v_newNode_4936_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__8___redArg(size_t v_depth_4951_, lean_object* v_keys_4952_, lean_object* v_vals_4953_, lean_object* v_i_4954_, lean_object* v_entries_4955_){
_start:
{
lean_object* v___x_4956_; uint8_t v___x_4957_; 
v___x_4956_ = lean_array_get_size(v_keys_4952_);
v___x_4957_ = lean_nat_dec_lt(v_i_4954_, v___x_4956_);
if (v___x_4957_ == 0)
{
lean_dec(v_i_4954_);
return v_entries_4955_;
}
else
{
lean_object* v_k_4958_; lean_object* v_v_4959_; uint64_t v___x_4960_; size_t v_h_4961_; size_t v___x_4962_; lean_object* v___x_4963_; size_t v___x_4964_; size_t v___x_4965_; size_t v___x_4966_; size_t v_h_4967_; lean_object* v___x_4968_; lean_object* v___x_4969_; 
v_k_4958_ = lean_array_fget_borrowed(v_keys_4952_, v_i_4954_);
v_v_4959_ = lean_array_fget_borrowed(v_vals_4953_, v_i_4954_);
v___x_4960_ = l_Lean_instHashableMVarId_hash(v_k_4958_);
v_h_4961_ = lean_uint64_to_usize(v___x_4960_);
v___x_4962_ = ((size_t)5ULL);
v___x_4963_ = lean_unsigned_to_nat(1u);
v___x_4964_ = ((size_t)1ULL);
v___x_4965_ = lean_usize_sub(v_depth_4951_, v___x_4964_);
v___x_4966_ = lean_usize_mul(v___x_4962_, v___x_4965_);
v_h_4967_ = lean_usize_shift_right(v_h_4961_, v___x_4966_);
v___x_4968_ = lean_nat_add(v_i_4954_, v___x_4963_);
lean_dec(v_i_4954_);
lean_inc(v_v_4959_);
lean_inc(v_k_4958_);
v___x_4969_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg(v_entries_4955_, v_h_4967_, v_depth_4951_, v_k_4958_, v_v_4959_);
v_i_4954_ = v___x_4968_;
v_entries_4955_ = v___x_4969_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__8___redArg___boxed(lean_object* v_depth_4971_, lean_object* v_keys_4972_, lean_object* v_vals_4973_, lean_object* v_i_4974_, lean_object* v_entries_4975_){
_start:
{
size_t v_depth_boxed_4976_; lean_object* v_res_4977_; 
v_depth_boxed_4976_ = lean_unbox_usize(v_depth_4971_);
lean_dec(v_depth_4971_);
v_res_4977_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__8___redArg(v_depth_boxed_4976_, v_keys_4972_, v_vals_4973_, v_i_4974_, v_entries_4975_);
lean_dec_ref(v_vals_4973_);
lean_dec_ref(v_keys_4972_);
return v_res_4977_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_x_4978_, lean_object* v_x_4979_, lean_object* v_x_4980_, lean_object* v_x_4981_, lean_object* v_x_4982_){
_start:
{
size_t v_x_48522__boxed_4983_; size_t v_x_48523__boxed_4984_; lean_object* v_res_4985_; 
v_x_48522__boxed_4983_ = lean_unbox_usize(v_x_4979_);
lean_dec(v_x_4979_);
v_x_48523__boxed_4984_ = lean_unbox_usize(v_x_4980_);
lean_dec(v_x_4980_);
v_res_4985_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg(v_x_4978_, v_x_48522__boxed_4983_, v_x_48523__boxed_4984_, v_x_4981_, v_x_4982_);
return v_res_4985_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0___redArg(lean_object* v_x_4986_, lean_object* v_x_4987_, lean_object* v_x_4988_){
_start:
{
uint64_t v___x_4989_; size_t v___x_4990_; size_t v___x_4991_; lean_object* v___x_4992_; 
v___x_4989_ = l_Lean_instHashableMVarId_hash(v_x_4987_);
v___x_4990_ = lean_uint64_to_usize(v___x_4989_);
v___x_4991_ = ((size_t)1ULL);
v___x_4992_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg(v_x_4986_, v___x_4990_, v___x_4991_, v_x_4987_, v_x_4988_);
return v___x_4992_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___redArg(lean_object* v_mvarId_4993_, lean_object* v_val_4994_, lean_object* v___y_4995_){
_start:
{
lean_object* v___x_4997_; lean_object* v_mctx_4998_; lean_object* v_cache_4999_; lean_object* v_zetaDeltaFVarIds_5000_; lean_object* v_postponed_5001_; lean_object* v_diag_5002_; lean_object* v___x_5004_; uint8_t v_isShared_5005_; uint8_t v_isSharedCheck_5030_; 
v___x_4997_ = lean_st_ref_take(v___y_4995_);
v_mctx_4998_ = lean_ctor_get(v___x_4997_, 0);
v_cache_4999_ = lean_ctor_get(v___x_4997_, 1);
v_zetaDeltaFVarIds_5000_ = lean_ctor_get(v___x_4997_, 2);
v_postponed_5001_ = lean_ctor_get(v___x_4997_, 3);
v_diag_5002_ = lean_ctor_get(v___x_4997_, 4);
v_isSharedCheck_5030_ = !lean_is_exclusive(v___x_4997_);
if (v_isSharedCheck_5030_ == 0)
{
v___x_5004_ = v___x_4997_;
v_isShared_5005_ = v_isSharedCheck_5030_;
goto v_resetjp_5003_;
}
else
{
lean_inc(v_diag_5002_);
lean_inc(v_postponed_5001_);
lean_inc(v_zetaDeltaFVarIds_5000_);
lean_inc(v_cache_4999_);
lean_inc(v_mctx_4998_);
lean_dec(v___x_4997_);
v___x_5004_ = lean_box(0);
v_isShared_5005_ = v_isSharedCheck_5030_;
goto v_resetjp_5003_;
}
v_resetjp_5003_:
{
lean_object* v_depth_5006_; lean_object* v_levelAssignDepth_5007_; lean_object* v_lmvarCounter_5008_; lean_object* v_mvarCounter_5009_; lean_object* v_lDecls_5010_; lean_object* v_decls_5011_; lean_object* v_userNames_5012_; lean_object* v_lAssignment_5013_; lean_object* v_eAssignment_5014_; lean_object* v_dAssignment_5015_; lean_object* v___x_5017_; uint8_t v_isShared_5018_; uint8_t v_isSharedCheck_5029_; 
v_depth_5006_ = lean_ctor_get(v_mctx_4998_, 0);
v_levelAssignDepth_5007_ = lean_ctor_get(v_mctx_4998_, 1);
v_lmvarCounter_5008_ = lean_ctor_get(v_mctx_4998_, 2);
v_mvarCounter_5009_ = lean_ctor_get(v_mctx_4998_, 3);
v_lDecls_5010_ = lean_ctor_get(v_mctx_4998_, 4);
v_decls_5011_ = lean_ctor_get(v_mctx_4998_, 5);
v_userNames_5012_ = lean_ctor_get(v_mctx_4998_, 6);
v_lAssignment_5013_ = lean_ctor_get(v_mctx_4998_, 7);
v_eAssignment_5014_ = lean_ctor_get(v_mctx_4998_, 8);
v_dAssignment_5015_ = lean_ctor_get(v_mctx_4998_, 9);
v_isSharedCheck_5029_ = !lean_is_exclusive(v_mctx_4998_);
if (v_isSharedCheck_5029_ == 0)
{
v___x_5017_ = v_mctx_4998_;
v_isShared_5018_ = v_isSharedCheck_5029_;
goto v_resetjp_5016_;
}
else
{
lean_inc(v_dAssignment_5015_);
lean_inc(v_eAssignment_5014_);
lean_inc(v_lAssignment_5013_);
lean_inc(v_userNames_5012_);
lean_inc(v_decls_5011_);
lean_inc(v_lDecls_5010_);
lean_inc(v_mvarCounter_5009_);
lean_inc(v_lmvarCounter_5008_);
lean_inc(v_levelAssignDepth_5007_);
lean_inc(v_depth_5006_);
lean_dec(v_mctx_4998_);
v___x_5017_ = lean_box(0);
v_isShared_5018_ = v_isSharedCheck_5029_;
goto v_resetjp_5016_;
}
v_resetjp_5016_:
{
lean_object* v___x_5019_; lean_object* v___x_5021_; 
v___x_5019_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0___redArg(v_eAssignment_5014_, v_mvarId_4993_, v_val_4994_);
if (v_isShared_5018_ == 0)
{
lean_ctor_set(v___x_5017_, 8, v___x_5019_);
v___x_5021_ = v___x_5017_;
goto v_reusejp_5020_;
}
else
{
lean_object* v_reuseFailAlloc_5028_; 
v_reuseFailAlloc_5028_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5028_, 0, v_depth_5006_);
lean_ctor_set(v_reuseFailAlloc_5028_, 1, v_levelAssignDepth_5007_);
lean_ctor_set(v_reuseFailAlloc_5028_, 2, v_lmvarCounter_5008_);
lean_ctor_set(v_reuseFailAlloc_5028_, 3, v_mvarCounter_5009_);
lean_ctor_set(v_reuseFailAlloc_5028_, 4, v_lDecls_5010_);
lean_ctor_set(v_reuseFailAlloc_5028_, 5, v_decls_5011_);
lean_ctor_set(v_reuseFailAlloc_5028_, 6, v_userNames_5012_);
lean_ctor_set(v_reuseFailAlloc_5028_, 7, v_lAssignment_5013_);
lean_ctor_set(v_reuseFailAlloc_5028_, 8, v___x_5019_);
lean_ctor_set(v_reuseFailAlloc_5028_, 9, v_dAssignment_5015_);
v___x_5021_ = v_reuseFailAlloc_5028_;
goto v_reusejp_5020_;
}
v_reusejp_5020_:
{
lean_object* v___x_5023_; 
if (v_isShared_5005_ == 0)
{
lean_ctor_set(v___x_5004_, 0, v___x_5021_);
v___x_5023_ = v___x_5004_;
goto v_reusejp_5022_;
}
else
{
lean_object* v_reuseFailAlloc_5027_; 
v_reuseFailAlloc_5027_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5027_, 0, v___x_5021_);
lean_ctor_set(v_reuseFailAlloc_5027_, 1, v_cache_4999_);
lean_ctor_set(v_reuseFailAlloc_5027_, 2, v_zetaDeltaFVarIds_5000_);
lean_ctor_set(v_reuseFailAlloc_5027_, 3, v_postponed_5001_);
lean_ctor_set(v_reuseFailAlloc_5027_, 4, v_diag_5002_);
v___x_5023_ = v_reuseFailAlloc_5027_;
goto v_reusejp_5022_;
}
v_reusejp_5022_:
{
lean_object* v___x_5024_; lean_object* v___x_5025_; lean_object* v___x_5026_; 
v___x_5024_ = lean_st_ref_set(v___y_4995_, v___x_5023_);
v___x_5025_ = lean_box(0);
v___x_5026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5026_, 0, v___x_5025_);
return v___x_5026_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___redArg___boxed(lean_object* v_mvarId_5031_, lean_object* v_val_5032_, lean_object* v___y_5033_, lean_object* v___y_5034_){
_start:
{
lean_object* v_res_5035_; 
v_res_5035_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___redArg(v_mvarId_5031_, v_val_5032_, v___y_5033_);
lean_dec(v___y_5033_);
return v_res_5035_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3(lean_object* v_mvarId_5043_, lean_object* v_config_5044_, lean_object* v_as_5045_, size_t v_sz_5046_, size_t v_i_5047_, lean_object* v_b_5048_, lean_object* v___y_5049_, lean_object* v___y_5050_, lean_object* v___y_5051_, lean_object* v___y_5052_, lean_object* v___y_5053_, lean_object* v___y_5054_){
_start:
{
lean_object* v_a_5057_; uint8_t v___x_5061_; 
v___x_5061_ = lean_usize_dec_lt(v_i_5047_, v_sz_5046_);
if (v___x_5061_ == 0)
{
lean_object* v___x_5062_; 
lean_dec_ref(v_config_5044_);
lean_dec(v_mvarId_5043_);
v___x_5062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5062_, 0, v_b_5048_);
return v___x_5062_;
}
else
{
lean_object* v_a_5063_; lean_object* v___x_5064_; 
v_a_5063_ = lean_array_uget_borrowed(v_as_5045_, v_i_5047_);
lean_inc(v_a_5063_);
v___x_5064_ = l_Lean_FVarId_getDecl___redArg(v_a_5063_, v___y_5051_, v___y_5053_, v___y_5054_);
if (lean_obj_tag(v___x_5064_) == 0)
{
lean_object* v_options_5065_; lean_object* v_a_5066_; lean_object* v_snd_5067_; lean_object* v___x_5069_; uint8_t v_isShared_5070_; uint8_t v_isSharedCheck_5258_; 
v_options_5065_ = lean_ctor_get(v___y_5053_, 2);
v_a_5066_ = lean_ctor_get(v___x_5064_, 0);
lean_inc(v_a_5066_);
lean_dec_ref_known(v___x_5064_, 1);
v_snd_5067_ = lean_ctor_get(v_b_5048_, 1);
v_isSharedCheck_5258_ = !lean_is_exclusive(v_b_5048_);
if (v_isSharedCheck_5258_ == 0)
{
lean_object* v_unused_5259_; 
v_unused_5259_ = lean_ctor_get(v_b_5048_, 0);
lean_dec(v_unused_5259_);
v___x_5069_ = v_b_5048_;
v_isShared_5070_ = v_isSharedCheck_5258_;
goto v_resetjp_5068_;
}
else
{
lean_inc(v_snd_5067_);
lean_dec(v_b_5048_);
v___x_5069_ = lean_box(0);
v_isShared_5070_ = v_isSharedCheck_5258_;
goto v_resetjp_5068_;
}
v_resetjp_5068_:
{
lean_object* v_inheritedTraceOptions_5071_; uint8_t v_hasTrace_5072_; lean_object* v___x_5073_; lean_object* v___x_5074_; lean_object* v___y_5076_; 
v_inheritedTraceOptions_5071_ = lean_ctor_get(v___y_5053_, 13);
v_hasTrace_5072_ = lean_ctor_get_uint8(v_options_5065_, sizeof(void*)*1);
v___x_5073_ = lean_box(0);
v___x_5074_ = l_Lean_LocalDecl_type(v_a_5066_);
if (v_hasTrace_5072_ == 0)
{
lean_object* v___x_5173_; 
lean_inc_ref(v_config_5044_);
lean_inc_ref(v___x_5074_);
v___x_5173_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_5074_, v_config_5044_, v___y_5049_, v___y_5050_, v___y_5051_, v___y_5052_, v___y_5053_, v___y_5054_);
v___y_5076_ = v___x_5173_;
goto v___jp_5075_;
}
else
{
lean_object* v___f_5174_; lean_object* v___x_5175_; lean_object* v___x_5176_; lean_object* v___x_5177_; uint8_t v___x_5178_; lean_object* v___y_5180_; lean_object* v___y_5181_; lean_object* v_a_5182_; lean_object* v___y_5195_; lean_object* v___y_5196_; lean_object* v_a_5197_; 
lean_inc_ref(v___x_5074_);
lean_inc(v_a_5066_);
v___f_5174_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___boxed), 10, 2);
lean_closure_set(v___f_5174_, 0, v_a_5066_);
lean_closure_set(v___f_5174_, 1, v___x_5074_);
v___x_5175_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0));
v___x_5176_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__1));
v___x_5177_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1);
v___x_5178_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5071_, v_options_5065_, v___x_5177_);
if (v___x_5178_ == 0)
{
lean_object* v___x_5255_; uint8_t v___x_5256_; 
v___x_5255_ = l_Lean_trace_profiler;
v___x_5256_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_5065_, v___x_5255_);
if (v___x_5256_ == 0)
{
lean_object* v___x_5257_; 
lean_dec_ref(v___f_5174_);
lean_inc_ref(v_config_5044_);
lean_inc_ref(v___x_5074_);
v___x_5257_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_5074_, v_config_5044_, v___y_5049_, v___y_5050_, v___y_5051_, v___y_5052_, v___y_5053_, v___y_5054_);
v___y_5076_ = v___x_5257_;
goto v___jp_5075_;
}
else
{
goto v___jp_5206_;
}
}
else
{
goto v___jp_5206_;
}
v___jp_5179_:
{
lean_object* v___x_5183_; double v___x_5184_; double v___x_5185_; double v___x_5186_; double v___x_5187_; double v___x_5188_; lean_object* v___x_5189_; lean_object* v___x_5190_; lean_object* v___x_5191_; lean_object* v___x_5192_; lean_object* v___x_5193_; 
v___x_5183_ = lean_io_mono_nanos_now();
v___x_5184_ = lean_float_of_nat(v___y_5181_);
v___x_5185_ = lean_float_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9);
v___x_5186_ = lean_float_div(v___x_5184_, v___x_5185_);
v___x_5187_ = lean_float_of_nat(v___x_5183_);
v___x_5188_ = lean_float_div(v___x_5187_, v___x_5185_);
v___x_5189_ = lean_box_float(v___x_5186_);
v___x_5190_ = lean_box_float(v___x_5188_);
v___x_5191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5191_, 0, v___x_5189_);
lean_ctor_set(v___x_5191_, 1, v___x_5190_);
v___x_5192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5192_, 0, v_a_5182_);
lean_ctor_set(v___x_5192_, 1, v___x_5191_);
v___x_5193_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2(v___x_5175_, v_hasTrace_5072_, v___x_5176_, v_options_5065_, v___x_5178_, v___y_5180_, v___f_5174_, v___x_5192_, v___y_5049_, v___y_5050_, v___y_5051_, v___y_5052_, v___y_5053_, v___y_5054_);
v___y_5076_ = v___x_5193_;
goto v___jp_5075_;
}
v___jp_5194_:
{
lean_object* v___x_5198_; double v___x_5199_; double v___x_5200_; lean_object* v___x_5201_; lean_object* v___x_5202_; lean_object* v___x_5203_; lean_object* v___x_5204_; lean_object* v___x_5205_; 
v___x_5198_ = lean_io_get_num_heartbeats();
v___x_5199_ = lean_float_of_nat(v___y_5196_);
v___x_5200_ = lean_float_of_nat(v___x_5198_);
v___x_5201_ = lean_box_float(v___x_5199_);
v___x_5202_ = lean_box_float(v___x_5200_);
v___x_5203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5203_, 0, v___x_5201_);
lean_ctor_set(v___x_5203_, 1, v___x_5202_);
v___x_5204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5204_, 0, v_a_5197_);
lean_ctor_set(v___x_5204_, 1, v___x_5203_);
v___x_5205_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2(v___x_5175_, v_hasTrace_5072_, v___x_5176_, v_options_5065_, v___x_5178_, v___y_5195_, v___f_5174_, v___x_5204_, v___y_5049_, v___y_5050_, v___y_5051_, v___y_5052_, v___y_5053_, v___y_5054_);
v___y_5076_ = v___x_5205_;
goto v___jp_5075_;
}
v___jp_5206_:
{
lean_object* v___x_5207_; 
v___x_5207_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1___redArg(v___y_5054_);
if (lean_obj_tag(v___x_5207_) == 0)
{
lean_object* v_a_5208_; lean_object* v___x_5209_; uint8_t v___x_5210_; 
v_a_5208_ = lean_ctor_get(v___x_5207_, 0);
lean_inc(v_a_5208_);
lean_dec_ref_known(v___x_5207_, 1);
v___x_5209_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5210_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_5065_, v___x_5209_);
if (v___x_5210_ == 0)
{
lean_object* v___x_5211_; lean_object* v___x_5212_; 
v___x_5211_ = lean_io_mono_nanos_now();
lean_inc_ref(v_config_5044_);
lean_inc_ref(v___x_5074_);
v___x_5212_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_5074_, v_config_5044_, v___y_5049_, v___y_5050_, v___y_5051_, v___y_5052_, v___y_5053_, v___y_5054_);
if (lean_obj_tag(v___x_5212_) == 0)
{
lean_object* v_a_5213_; lean_object* v___x_5215_; uint8_t v_isShared_5216_; uint8_t v_isSharedCheck_5220_; 
v_a_5213_ = lean_ctor_get(v___x_5212_, 0);
v_isSharedCheck_5220_ = !lean_is_exclusive(v___x_5212_);
if (v_isSharedCheck_5220_ == 0)
{
v___x_5215_ = v___x_5212_;
v_isShared_5216_ = v_isSharedCheck_5220_;
goto v_resetjp_5214_;
}
else
{
lean_inc(v_a_5213_);
lean_dec(v___x_5212_);
v___x_5215_ = lean_box(0);
v_isShared_5216_ = v_isSharedCheck_5220_;
goto v_resetjp_5214_;
}
v_resetjp_5214_:
{
lean_object* v___x_5218_; 
if (v_isShared_5216_ == 0)
{
lean_ctor_set_tag(v___x_5215_, 1);
v___x_5218_ = v___x_5215_;
goto v_reusejp_5217_;
}
else
{
lean_object* v_reuseFailAlloc_5219_; 
v_reuseFailAlloc_5219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5219_, 0, v_a_5213_);
v___x_5218_ = v_reuseFailAlloc_5219_;
goto v_reusejp_5217_;
}
v_reusejp_5217_:
{
v___y_5180_ = v_a_5208_;
v___y_5181_ = v___x_5211_;
v_a_5182_ = v___x_5218_;
goto v___jp_5179_;
}
}
}
else
{
lean_object* v_a_5221_; lean_object* v___x_5223_; uint8_t v_isShared_5224_; uint8_t v_isSharedCheck_5228_; 
v_a_5221_ = lean_ctor_get(v___x_5212_, 0);
v_isSharedCheck_5228_ = !lean_is_exclusive(v___x_5212_);
if (v_isSharedCheck_5228_ == 0)
{
v___x_5223_ = v___x_5212_;
v_isShared_5224_ = v_isSharedCheck_5228_;
goto v_resetjp_5222_;
}
else
{
lean_inc(v_a_5221_);
lean_dec(v___x_5212_);
v___x_5223_ = lean_box(0);
v_isShared_5224_ = v_isSharedCheck_5228_;
goto v_resetjp_5222_;
}
v_resetjp_5222_:
{
lean_object* v___x_5226_; 
if (v_isShared_5224_ == 0)
{
lean_ctor_set_tag(v___x_5223_, 0);
v___x_5226_ = v___x_5223_;
goto v_reusejp_5225_;
}
else
{
lean_object* v_reuseFailAlloc_5227_; 
v_reuseFailAlloc_5227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5227_, 0, v_a_5221_);
v___x_5226_ = v_reuseFailAlloc_5227_;
goto v_reusejp_5225_;
}
v_reusejp_5225_:
{
v___y_5180_ = v_a_5208_;
v___y_5181_ = v___x_5211_;
v_a_5182_ = v___x_5226_;
goto v___jp_5179_;
}
}
}
}
else
{
lean_object* v___x_5229_; lean_object* v___x_5230_; 
v___x_5229_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_config_5044_);
lean_inc_ref(v___x_5074_);
v___x_5230_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_5074_, v_config_5044_, v___y_5049_, v___y_5050_, v___y_5051_, v___y_5052_, v___y_5053_, v___y_5054_);
if (lean_obj_tag(v___x_5230_) == 0)
{
lean_object* v_a_5231_; lean_object* v___x_5233_; uint8_t v_isShared_5234_; uint8_t v_isSharedCheck_5238_; 
v_a_5231_ = lean_ctor_get(v___x_5230_, 0);
v_isSharedCheck_5238_ = !lean_is_exclusive(v___x_5230_);
if (v_isSharedCheck_5238_ == 0)
{
v___x_5233_ = v___x_5230_;
v_isShared_5234_ = v_isSharedCheck_5238_;
goto v_resetjp_5232_;
}
else
{
lean_inc(v_a_5231_);
lean_dec(v___x_5230_);
v___x_5233_ = lean_box(0);
v_isShared_5234_ = v_isSharedCheck_5238_;
goto v_resetjp_5232_;
}
v_resetjp_5232_:
{
lean_object* v___x_5236_; 
if (v_isShared_5234_ == 0)
{
lean_ctor_set_tag(v___x_5233_, 1);
v___x_5236_ = v___x_5233_;
goto v_reusejp_5235_;
}
else
{
lean_object* v_reuseFailAlloc_5237_; 
v_reuseFailAlloc_5237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5237_, 0, v_a_5231_);
v___x_5236_ = v_reuseFailAlloc_5237_;
goto v_reusejp_5235_;
}
v_reusejp_5235_:
{
v___y_5195_ = v_a_5208_;
v___y_5196_ = v___x_5229_;
v_a_5197_ = v___x_5236_;
goto v___jp_5194_;
}
}
}
else
{
lean_object* v_a_5239_; lean_object* v___x_5241_; uint8_t v_isShared_5242_; uint8_t v_isSharedCheck_5246_; 
v_a_5239_ = lean_ctor_get(v___x_5230_, 0);
v_isSharedCheck_5246_ = !lean_is_exclusive(v___x_5230_);
if (v_isSharedCheck_5246_ == 0)
{
v___x_5241_ = v___x_5230_;
v_isShared_5242_ = v_isSharedCheck_5246_;
goto v_resetjp_5240_;
}
else
{
lean_inc(v_a_5239_);
lean_dec(v___x_5230_);
v___x_5241_ = lean_box(0);
v_isShared_5242_ = v_isSharedCheck_5246_;
goto v_resetjp_5240_;
}
v_resetjp_5240_:
{
lean_object* v___x_5244_; 
if (v_isShared_5242_ == 0)
{
lean_ctor_set_tag(v___x_5241_, 0);
v___x_5244_ = v___x_5241_;
goto v_reusejp_5243_;
}
else
{
lean_object* v_reuseFailAlloc_5245_; 
v_reuseFailAlloc_5245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5245_, 0, v_a_5239_);
v___x_5244_ = v_reuseFailAlloc_5245_;
goto v_reusejp_5243_;
}
v_reusejp_5243_:
{
v___y_5195_ = v_a_5208_;
v___y_5196_ = v___x_5229_;
v_a_5197_ = v___x_5244_;
goto v___jp_5194_;
}
}
}
}
}
else
{
lean_object* v_a_5247_; lean_object* v___x_5249_; uint8_t v_isShared_5250_; uint8_t v_isSharedCheck_5254_; 
lean_dec_ref(v___f_5174_);
lean_dec_ref(v___x_5074_);
lean_del_object(v___x_5069_);
lean_dec(v_snd_5067_);
lean_dec(v_a_5066_);
lean_dec_ref(v_config_5044_);
lean_dec(v_mvarId_5043_);
v_a_5247_ = lean_ctor_get(v___x_5207_, 0);
v_isSharedCheck_5254_ = !lean_is_exclusive(v___x_5207_);
if (v_isSharedCheck_5254_ == 0)
{
v___x_5249_ = v___x_5207_;
v_isShared_5250_ = v_isSharedCheck_5254_;
goto v_resetjp_5248_;
}
else
{
lean_inc(v_a_5247_);
lean_dec(v___x_5207_);
v___x_5249_ = lean_box(0);
v_isShared_5250_ = v_isSharedCheck_5254_;
goto v_resetjp_5248_;
}
v_resetjp_5248_:
{
lean_object* v___x_5252_; 
if (v_isShared_5250_ == 0)
{
v___x_5252_ = v___x_5249_;
goto v_reusejp_5251_;
}
else
{
lean_object* v_reuseFailAlloc_5253_; 
v_reuseFailAlloc_5253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5253_, 0, v_a_5247_);
v___x_5252_ = v_reuseFailAlloc_5253_;
goto v_reusejp_5251_;
}
v_reusejp_5251_:
{
return v___x_5252_;
}
}
}
}
}
v___jp_5075_:
{
if (lean_obj_tag(v___y_5076_) == 0)
{
lean_object* v_a_5077_; 
v_a_5077_ = lean_ctor_get(v___y_5076_, 0);
lean_inc(v_a_5077_);
lean_dec_ref_known(v___y_5076_, 1);
if (lean_obj_tag(v_a_5077_) == 0)
{
lean_object* v___x_5079_; 
lean_dec_ref_known(v_a_5077_, 0);
lean_dec_ref(v___x_5074_);
lean_dec(v_a_5066_);
if (v_isShared_5070_ == 0)
{
lean_ctor_set(v___x_5069_, 0, v___x_5073_);
v___x_5079_ = v___x_5069_;
goto v_reusejp_5078_;
}
else
{
lean_object* v_reuseFailAlloc_5080_; 
v_reuseFailAlloc_5080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5080_, 0, v___x_5073_);
lean_ctor_set(v_reuseFailAlloc_5080_, 1, v_snd_5067_);
v___x_5079_ = v_reuseFailAlloc_5080_;
goto v_reusejp_5078_;
}
v_reusejp_5078_:
{
v_a_5057_ = v___x_5079_;
goto v___jp_5056_;
}
}
else
{
lean_object* v_e_x27_5081_; lean_object* v_proof_5082_; uint8_t v___x_5083_; 
v_e_x27_5081_ = lean_ctor_get(v_a_5077_, 0);
lean_inc_ref_n(v_e_x27_5081_, 2);
v_proof_5082_ = lean_ctor_get(v_a_5077_, 1);
lean_inc_ref(v_proof_5082_);
lean_dec_ref_known(v_a_5077_, 2);
v___x_5083_ = l_Lean_Expr_isFalse(v_e_x27_5081_);
if (v___x_5083_ == 0)
{
lean_object* v___x_5084_; 
lean_inc_ref(v___x_5074_);
v___x_5084_ = l_Lean_Meta_Sym_getLevel___redArg(v___x_5074_, v___y_5050_, v___y_5051_, v___y_5052_, v___y_5053_, v___y_5054_);
if (lean_obj_tag(v___x_5084_) == 0)
{
lean_object* v_a_5085_; lean_object* v___x_5086_; lean_object* v___x_5087_; lean_object* v___x_5088_; lean_object* v___x_5089_; lean_object* v___x_5090_; lean_object* v___x_5091_; lean_object* v___x_5092_; uint8_t v___x_5093_; uint8_t v___x_5094_; lean_object* v___x_5095_; lean_object* v___x_5096_; lean_object* v___x_5098_; 
v_a_5085_ = lean_ctor_get(v___x_5084_, 0);
lean_inc(v_a_5085_);
lean_dec_ref_known(v___x_5084_, 1);
v___x_5086_ = l_Lean_LocalDecl_userName(v_a_5066_);
lean_dec(v_a_5066_);
v___x_5087_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___closed__2));
v___x_5088_ = lean_box(0);
v___x_5089_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5089_, 0, v_a_5085_);
lean_ctor_set(v___x_5089_, 1, v___x_5088_);
v___x_5090_ = l_Lean_mkConst(v___x_5087_, v___x_5089_);
lean_inc(v_a_5063_);
v___x_5091_ = l_Lean_mkFVar(v_a_5063_);
lean_inc_ref(v_e_x27_5081_);
v___x_5092_ = l_Lean_mkApp4(v___x_5090_, v___x_5074_, v_e_x27_5081_, v_proof_5082_, v___x_5091_);
v___x_5093_ = 0;
v___x_5094_ = 0;
v___x_5095_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5095_, 0, v___x_5086_);
lean_ctor_set(v___x_5095_, 1, v_e_x27_5081_);
lean_ctor_set(v___x_5095_, 2, v___x_5092_);
lean_ctor_set_uint8(v___x_5095_, sizeof(void*)*3, v___x_5093_);
lean_ctor_set_uint8(v___x_5095_, sizeof(void*)*3 + 1, v___x_5094_);
v___x_5096_ = lean_array_push(v_snd_5067_, v___x_5095_);
if (v_isShared_5070_ == 0)
{
lean_ctor_set(v___x_5069_, 1, v___x_5096_);
lean_ctor_set(v___x_5069_, 0, v___x_5073_);
v___x_5098_ = v___x_5069_;
goto v_reusejp_5097_;
}
else
{
lean_object* v_reuseFailAlloc_5099_; 
v_reuseFailAlloc_5099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5099_, 0, v___x_5073_);
lean_ctor_set(v_reuseFailAlloc_5099_, 1, v___x_5096_);
v___x_5098_ = v_reuseFailAlloc_5099_;
goto v_reusejp_5097_;
}
v_reusejp_5097_:
{
v_a_5057_ = v___x_5098_;
goto v___jp_5056_;
}
}
else
{
lean_object* v_a_5100_; lean_object* v___x_5102_; uint8_t v_isShared_5103_; uint8_t v_isSharedCheck_5107_; 
lean_dec_ref(v_proof_5082_);
lean_dec_ref(v_e_x27_5081_);
lean_dec_ref(v___x_5074_);
lean_del_object(v___x_5069_);
lean_dec(v_snd_5067_);
lean_dec(v_a_5066_);
lean_dec_ref(v_config_5044_);
lean_dec(v_mvarId_5043_);
v_a_5100_ = lean_ctor_get(v___x_5084_, 0);
v_isSharedCheck_5107_ = !lean_is_exclusive(v___x_5084_);
if (v_isSharedCheck_5107_ == 0)
{
v___x_5102_ = v___x_5084_;
v_isShared_5103_ = v_isSharedCheck_5107_;
goto v_resetjp_5101_;
}
else
{
lean_inc(v_a_5100_);
lean_dec(v___x_5084_);
v___x_5102_ = lean_box(0);
v_isShared_5103_ = v_isSharedCheck_5107_;
goto v_resetjp_5101_;
}
v_resetjp_5101_:
{
lean_object* v___x_5105_; 
if (v_isShared_5103_ == 0)
{
v___x_5105_ = v___x_5102_;
goto v_reusejp_5104_;
}
else
{
lean_object* v_reuseFailAlloc_5106_; 
v_reuseFailAlloc_5106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5106_, 0, v_a_5100_);
v___x_5105_ = v_reuseFailAlloc_5106_;
goto v_reusejp_5104_;
}
v_reusejp_5104_:
{
return v___x_5105_;
}
}
}
}
else
{
lean_object* v___x_5108_; 
lean_dec(v_a_5066_);
lean_dec_ref(v_config_5044_);
lean_inc_ref(v___x_5074_);
v___x_5108_ = l_Lean_Meta_Sym_getLevel___redArg(v___x_5074_, v___y_5050_, v___y_5051_, v___y_5052_, v___y_5053_, v___y_5054_);
if (lean_obj_tag(v___x_5108_) == 0)
{
lean_object* v_a_5109_; lean_object* v___x_5110_; 
v_a_5109_ = lean_ctor_get(v___x_5108_, 0);
lean_inc(v_a_5109_);
lean_dec_ref_known(v___x_5108_, 1);
lean_inc(v_mvarId_5043_);
v___x_5110_ = l_Lean_MVarId_getType(v_mvarId_5043_, v___y_5051_, v___y_5052_, v___y_5053_, v___y_5054_);
if (lean_obj_tag(v___x_5110_) == 0)
{
lean_object* v_a_5111_; lean_object* v___x_5112_; lean_object* v___x_5113_; lean_object* v___x_5114_; lean_object* v___x_5115_; lean_object* v___x_5116_; lean_object* v___x_5117_; lean_object* v___x_5118_; 
v_a_5111_ = lean_ctor_get(v___x_5110_, 0);
lean_inc(v_a_5111_);
lean_dec_ref_known(v___x_5110_, 1);
v___x_5112_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___closed__2));
v___x_5113_ = lean_box(0);
v___x_5114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5114_, 0, v_a_5109_);
lean_ctor_set(v___x_5114_, 1, v___x_5113_);
v___x_5115_ = l_Lean_mkConst(v___x_5112_, v___x_5114_);
lean_inc(v_a_5063_);
v___x_5116_ = l_Lean_mkFVar(v_a_5063_);
v___x_5117_ = l_Lean_mkApp4(v___x_5115_, v___x_5074_, v_e_x27_5081_, v_proof_5082_, v___x_5116_);
v___x_5118_ = l_Lean_Meta_mkFalseElim(v_a_5111_, v___x_5117_, v___y_5051_, v___y_5052_, v___y_5053_, v___y_5054_);
if (lean_obj_tag(v___x_5118_) == 0)
{
lean_object* v_a_5119_; lean_object* v___x_5120_; 
v_a_5119_ = lean_ctor_get(v___x_5118_, 0);
lean_inc(v_a_5119_);
lean_dec_ref_known(v___x_5118_, 1);
v___x_5120_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___redArg(v_mvarId_5043_, v_a_5119_, v___y_5052_);
if (lean_obj_tag(v___x_5120_) == 0)
{
lean_object* v___x_5122_; uint8_t v_isShared_5123_; uint8_t v_isSharedCheck_5131_; 
v_isSharedCheck_5131_ = !lean_is_exclusive(v___x_5120_);
if (v_isSharedCheck_5131_ == 0)
{
lean_object* v_unused_5132_; 
v_unused_5132_ = lean_ctor_get(v___x_5120_, 0);
lean_dec(v_unused_5132_);
v___x_5122_ = v___x_5120_;
v_isShared_5123_ = v_isSharedCheck_5131_;
goto v_resetjp_5121_;
}
else
{
lean_dec(v___x_5120_);
v___x_5122_ = lean_box(0);
v_isShared_5123_ = v_isSharedCheck_5131_;
goto v_resetjp_5121_;
}
v_resetjp_5121_:
{
lean_object* v___x_5124_; lean_object* v___x_5126_; 
v___x_5124_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___closed__3));
if (v_isShared_5070_ == 0)
{
lean_ctor_set(v___x_5069_, 0, v___x_5124_);
v___x_5126_ = v___x_5069_;
goto v_reusejp_5125_;
}
else
{
lean_object* v_reuseFailAlloc_5130_; 
v_reuseFailAlloc_5130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5130_, 0, v___x_5124_);
lean_ctor_set(v_reuseFailAlloc_5130_, 1, v_snd_5067_);
v___x_5126_ = v_reuseFailAlloc_5130_;
goto v_reusejp_5125_;
}
v_reusejp_5125_:
{
lean_object* v___x_5128_; 
if (v_isShared_5123_ == 0)
{
lean_ctor_set(v___x_5122_, 0, v___x_5126_);
v___x_5128_ = v___x_5122_;
goto v_reusejp_5127_;
}
else
{
lean_object* v_reuseFailAlloc_5129_; 
v_reuseFailAlloc_5129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5129_, 0, v___x_5126_);
v___x_5128_ = v_reuseFailAlloc_5129_;
goto v_reusejp_5127_;
}
v_reusejp_5127_:
{
return v___x_5128_;
}
}
}
}
else
{
lean_object* v_a_5133_; lean_object* v___x_5135_; uint8_t v_isShared_5136_; uint8_t v_isSharedCheck_5140_; 
lean_del_object(v___x_5069_);
lean_dec(v_snd_5067_);
v_a_5133_ = lean_ctor_get(v___x_5120_, 0);
v_isSharedCheck_5140_ = !lean_is_exclusive(v___x_5120_);
if (v_isSharedCheck_5140_ == 0)
{
v___x_5135_ = v___x_5120_;
v_isShared_5136_ = v_isSharedCheck_5140_;
goto v_resetjp_5134_;
}
else
{
lean_inc(v_a_5133_);
lean_dec(v___x_5120_);
v___x_5135_ = lean_box(0);
v_isShared_5136_ = v_isSharedCheck_5140_;
goto v_resetjp_5134_;
}
v_resetjp_5134_:
{
lean_object* v___x_5138_; 
if (v_isShared_5136_ == 0)
{
v___x_5138_ = v___x_5135_;
goto v_reusejp_5137_;
}
else
{
lean_object* v_reuseFailAlloc_5139_; 
v_reuseFailAlloc_5139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5139_, 0, v_a_5133_);
v___x_5138_ = v_reuseFailAlloc_5139_;
goto v_reusejp_5137_;
}
v_reusejp_5137_:
{
return v___x_5138_;
}
}
}
}
else
{
lean_object* v_a_5141_; lean_object* v___x_5143_; uint8_t v_isShared_5144_; uint8_t v_isSharedCheck_5148_; 
lean_del_object(v___x_5069_);
lean_dec(v_snd_5067_);
lean_dec(v_mvarId_5043_);
v_a_5141_ = lean_ctor_get(v___x_5118_, 0);
v_isSharedCheck_5148_ = !lean_is_exclusive(v___x_5118_);
if (v_isSharedCheck_5148_ == 0)
{
v___x_5143_ = v___x_5118_;
v_isShared_5144_ = v_isSharedCheck_5148_;
goto v_resetjp_5142_;
}
else
{
lean_inc(v_a_5141_);
lean_dec(v___x_5118_);
v___x_5143_ = lean_box(0);
v_isShared_5144_ = v_isSharedCheck_5148_;
goto v_resetjp_5142_;
}
v_resetjp_5142_:
{
lean_object* v___x_5146_; 
if (v_isShared_5144_ == 0)
{
v___x_5146_ = v___x_5143_;
goto v_reusejp_5145_;
}
else
{
lean_object* v_reuseFailAlloc_5147_; 
v_reuseFailAlloc_5147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5147_, 0, v_a_5141_);
v___x_5146_ = v_reuseFailAlloc_5147_;
goto v_reusejp_5145_;
}
v_reusejp_5145_:
{
return v___x_5146_;
}
}
}
}
else
{
lean_object* v_a_5149_; lean_object* v___x_5151_; uint8_t v_isShared_5152_; uint8_t v_isSharedCheck_5156_; 
lean_dec(v_a_5109_);
lean_dec_ref(v_proof_5082_);
lean_dec_ref(v_e_x27_5081_);
lean_dec_ref(v___x_5074_);
lean_del_object(v___x_5069_);
lean_dec(v_snd_5067_);
lean_dec(v_mvarId_5043_);
v_a_5149_ = lean_ctor_get(v___x_5110_, 0);
v_isSharedCheck_5156_ = !lean_is_exclusive(v___x_5110_);
if (v_isSharedCheck_5156_ == 0)
{
v___x_5151_ = v___x_5110_;
v_isShared_5152_ = v_isSharedCheck_5156_;
goto v_resetjp_5150_;
}
else
{
lean_inc(v_a_5149_);
lean_dec(v___x_5110_);
v___x_5151_ = lean_box(0);
v_isShared_5152_ = v_isSharedCheck_5156_;
goto v_resetjp_5150_;
}
v_resetjp_5150_:
{
lean_object* v___x_5154_; 
if (v_isShared_5152_ == 0)
{
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
return v___x_5154_;
}
}
}
}
else
{
lean_object* v_a_5157_; lean_object* v___x_5159_; uint8_t v_isShared_5160_; uint8_t v_isSharedCheck_5164_; 
lean_dec_ref(v_proof_5082_);
lean_dec_ref(v_e_x27_5081_);
lean_dec_ref(v___x_5074_);
lean_del_object(v___x_5069_);
lean_dec(v_snd_5067_);
lean_dec(v_mvarId_5043_);
v_a_5157_ = lean_ctor_get(v___x_5108_, 0);
v_isSharedCheck_5164_ = !lean_is_exclusive(v___x_5108_);
if (v_isSharedCheck_5164_ == 0)
{
v___x_5159_ = v___x_5108_;
v_isShared_5160_ = v_isSharedCheck_5164_;
goto v_resetjp_5158_;
}
else
{
lean_inc(v_a_5157_);
lean_dec(v___x_5108_);
v___x_5159_ = lean_box(0);
v_isShared_5160_ = v_isSharedCheck_5164_;
goto v_resetjp_5158_;
}
v_resetjp_5158_:
{
lean_object* v___x_5162_; 
if (v_isShared_5160_ == 0)
{
v___x_5162_ = v___x_5159_;
goto v_reusejp_5161_;
}
else
{
lean_object* v_reuseFailAlloc_5163_; 
v_reuseFailAlloc_5163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5163_, 0, v_a_5157_);
v___x_5162_ = v_reuseFailAlloc_5163_;
goto v_reusejp_5161_;
}
v_reusejp_5161_:
{
return v___x_5162_;
}
}
}
}
}
}
else
{
lean_object* v_a_5165_; lean_object* v___x_5167_; uint8_t v_isShared_5168_; uint8_t v_isSharedCheck_5172_; 
lean_dec_ref(v___x_5074_);
lean_del_object(v___x_5069_);
lean_dec(v_snd_5067_);
lean_dec(v_a_5066_);
lean_dec_ref(v_config_5044_);
lean_dec(v_mvarId_5043_);
v_a_5165_ = lean_ctor_get(v___y_5076_, 0);
v_isSharedCheck_5172_ = !lean_is_exclusive(v___y_5076_);
if (v_isSharedCheck_5172_ == 0)
{
v___x_5167_ = v___y_5076_;
v_isShared_5168_ = v_isSharedCheck_5172_;
goto v_resetjp_5166_;
}
else
{
lean_inc(v_a_5165_);
lean_dec(v___y_5076_);
v___x_5167_ = lean_box(0);
v_isShared_5168_ = v_isSharedCheck_5172_;
goto v_resetjp_5166_;
}
v_resetjp_5166_:
{
lean_object* v___x_5170_; 
if (v_isShared_5168_ == 0)
{
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
return v___x_5170_;
}
}
}
}
}
}
else
{
lean_object* v_a_5260_; lean_object* v___x_5262_; uint8_t v_isShared_5263_; uint8_t v_isSharedCheck_5267_; 
lean_dec_ref(v_b_5048_);
lean_dec_ref(v_config_5044_);
lean_dec(v_mvarId_5043_);
v_a_5260_ = lean_ctor_get(v___x_5064_, 0);
v_isSharedCheck_5267_ = !lean_is_exclusive(v___x_5064_);
if (v_isSharedCheck_5267_ == 0)
{
v___x_5262_ = v___x_5064_;
v_isShared_5263_ = v_isSharedCheck_5267_;
goto v_resetjp_5261_;
}
else
{
lean_inc(v_a_5260_);
lean_dec(v___x_5064_);
v___x_5262_ = lean_box(0);
v_isShared_5263_ = v_isSharedCheck_5267_;
goto v_resetjp_5261_;
}
v_resetjp_5261_:
{
lean_object* v___x_5265_; 
if (v_isShared_5263_ == 0)
{
v___x_5265_ = v___x_5262_;
goto v_reusejp_5264_;
}
else
{
lean_object* v_reuseFailAlloc_5266_; 
v_reuseFailAlloc_5266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5266_, 0, v_a_5260_);
v___x_5265_ = v_reuseFailAlloc_5266_;
goto v_reusejp_5264_;
}
v_reusejp_5264_:
{
return v___x_5265_;
}
}
}
}
v___jp_5056_:
{
size_t v___x_5058_; size_t v___x_5059_; 
v___x_5058_ = ((size_t)1ULL);
v___x_5059_ = lean_usize_add(v_i_5047_, v___x_5058_);
v_i_5047_ = v___x_5059_;
v_b_5048_ = v_a_5057_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___boxed(lean_object* v_mvarId_5268_, lean_object* v_config_5269_, lean_object* v_as_5270_, lean_object* v_sz_5271_, lean_object* v_i_5272_, lean_object* v_b_5273_, lean_object* v___y_5274_, lean_object* v___y_5275_, lean_object* v___y_5276_, lean_object* v___y_5277_, lean_object* v___y_5278_, lean_object* v___y_5279_, lean_object* v___y_5280_){
_start:
{
size_t v_sz_boxed_5281_; size_t v_i_boxed_5282_; lean_object* v_res_5283_; 
v_sz_boxed_5281_ = lean_unbox_usize(v_sz_5271_);
lean_dec(v_sz_5271_);
v_i_boxed_5282_ = lean_unbox_usize(v_i_5272_);
lean_dec(v_i_5272_);
v_res_5283_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3(v_mvarId_5268_, v_config_5269_, v_as_5270_, v_sz_boxed_5281_, v_i_boxed_5282_, v_b_5273_, v___y_5274_, v___y_5275_, v___y_5276_, v___y_5277_, v___y_5278_, v___y_5279_);
lean_dec(v___y_5279_);
lean_dec_ref(v___y_5278_);
lean_dec(v___y_5277_);
lean_dec_ref(v___y_5276_);
lean_dec(v___y_5275_);
lean_dec_ref(v___y_5274_);
lean_dec_ref(v_as_5270_);
return v_res_5283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__1(lean_object* v_mvarId_5284_, lean_object* v_config_5285_, lean_object* v_fvarIdsToSimp_5286_, size_t v_sz_5287_, size_t v___x_5288_, lean_object* v___x_5289_, uint8_t v_simplifyTarget_5290_, lean_object* v___y_5291_, lean_object* v___y_5292_, lean_object* v___y_5293_, lean_object* v___y_5294_, lean_object* v___y_5295_, lean_object* v___y_5296_){
_start:
{
lean_object* v___y_5299_; lean_object* v___y_5300_; lean_object* v___y_5301_; lean_object* v___y_5302_; lean_object* v___y_5303_; uint8_t v___y_5304_; lean_object* v___x_5324_; 
lean_inc_ref(v_config_5285_);
lean_inc(v_mvarId_5284_);
v___x_5324_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3(v_mvarId_5284_, v_config_5285_, v_fvarIdsToSimp_5286_, v_sz_5287_, v___x_5288_, v___x_5289_, v___y_5291_, v___y_5292_, v___y_5293_, v___y_5294_, v___y_5295_, v___y_5296_);
if (lean_obj_tag(v___x_5324_) == 0)
{
lean_object* v_a_5325_; lean_object* v___x_5327_; uint8_t v_isShared_5328_; uint8_t v_isSharedCheck_5527_; 
v_a_5325_ = lean_ctor_get(v___x_5324_, 0);
v_isSharedCheck_5527_ = !lean_is_exclusive(v___x_5324_);
if (v_isSharedCheck_5527_ == 0)
{
v___x_5327_ = v___x_5324_;
v_isShared_5328_ = v_isSharedCheck_5527_;
goto v_resetjp_5326_;
}
else
{
lean_inc(v_a_5325_);
lean_dec(v___x_5324_);
v___x_5327_ = lean_box(0);
v_isShared_5328_ = v_isSharedCheck_5527_;
goto v_resetjp_5326_;
}
v_resetjp_5326_:
{
lean_object* v_fst_5329_; lean_object* v_snd_5330_; lean_object* v___x_5332_; uint8_t v_isShared_5333_; uint8_t v_isSharedCheck_5526_; 
v_fst_5329_ = lean_ctor_get(v_a_5325_, 0);
v_snd_5330_ = lean_ctor_get(v_a_5325_, 1);
v_isSharedCheck_5526_ = !lean_is_exclusive(v_a_5325_);
if (v_isSharedCheck_5526_ == 0)
{
v___x_5332_ = v_a_5325_;
v_isShared_5333_ = v_isSharedCheck_5526_;
goto v_resetjp_5331_;
}
else
{
lean_inc(v_snd_5330_);
lean_inc(v_fst_5329_);
lean_dec(v_a_5325_);
v___x_5332_ = lean_box(0);
v_isShared_5333_ = v_isSharedCheck_5526_;
goto v_resetjp_5331_;
}
v_resetjp_5331_:
{
lean_object* v_mvarIdNew_5335_; lean_object* v___y_5336_; lean_object* v___y_5337_; lean_object* v___y_5338_; lean_object* v___y_5339_; lean_object* v___y_5386_; 
if (lean_obj_tag(v_fst_5329_) == 0)
{
lean_del_object(v___x_5327_);
if (v_simplifyTarget_5290_ == 0)
{
lean_del_object(v___x_5332_);
lean_dec_ref(v_config_5285_);
v_mvarIdNew_5335_ = v_mvarId_5284_;
v___y_5336_ = v___y_5293_;
v___y_5337_ = v___y_5294_;
v___y_5338_ = v___y_5295_;
v___y_5339_ = v___y_5296_;
goto v___jp_5334_;
}
else
{
lean_object* v___x_5429_; 
lean_inc(v_mvarId_5284_);
v___x_5429_ = l_Lean_MVarId_getType(v_mvarId_5284_, v___y_5293_, v___y_5294_, v___y_5295_, v___y_5296_);
if (lean_obj_tag(v___x_5429_) == 0)
{
lean_object* v_options_5430_; uint8_t v_hasTrace_5431_; 
v_options_5430_ = lean_ctor_get(v___y_5295_, 2);
v_hasTrace_5431_ = lean_ctor_get_uint8(v_options_5430_, sizeof(void*)*1);
if (v_hasTrace_5431_ == 0)
{
lean_object* v_a_5432_; lean_object* v___x_5433_; 
lean_del_object(v___x_5332_);
v_a_5432_ = lean_ctor_get(v___x_5429_, 0);
lean_inc(v_a_5432_);
lean_dec_ref_known(v___x_5429_, 1);
v___x_5433_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v_a_5432_, v_config_5285_, v___y_5291_, v___y_5292_, v___y_5293_, v___y_5294_, v___y_5295_, v___y_5296_);
v___y_5386_ = v___x_5433_;
goto v___jp_5385_;
}
else
{
lean_object* v_a_5434_; lean_object* v_inheritedTraceOptions_5435_; lean_object* v___f_5436_; lean_object* v___x_5437_; lean_object* v___x_5438_; lean_object* v___x_5439_; uint8_t v___x_5440_; lean_object* v___y_5442_; lean_object* v___y_5443_; lean_object* v_a_5444_; lean_object* v___y_5459_; lean_object* v___y_5460_; lean_object* v_a_5461_; 
v_a_5434_ = lean_ctor_get(v___x_5429_, 0);
lean_inc_n(v_a_5434_, 2);
lean_dec_ref_known(v___x_5429_, 1);
v_inheritedTraceOptions_5435_ = lean_ctor_get(v___y_5295_, 13);
v___f_5436_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___boxed), 9, 1);
lean_closure_set(v___f_5436_, 0, v_a_5434_);
v___x_5437_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0));
v___x_5438_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__1));
v___x_5439_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1);
v___x_5440_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5435_, v_options_5430_, v___x_5439_);
if (v___x_5440_ == 0)
{
lean_object* v___x_5511_; uint8_t v___x_5512_; 
v___x_5511_ = l_Lean_trace_profiler;
v___x_5512_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_5430_, v___x_5511_);
if (v___x_5512_ == 0)
{
lean_object* v___x_5513_; 
lean_dec_ref(v___f_5436_);
lean_del_object(v___x_5332_);
v___x_5513_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v_a_5434_, v_config_5285_, v___y_5291_, v___y_5292_, v___y_5293_, v___y_5294_, v___y_5295_, v___y_5296_);
v___y_5386_ = v___x_5513_;
goto v___jp_5385_;
}
else
{
goto v___jp_5470_;
}
}
else
{
goto v___jp_5470_;
}
v___jp_5441_:
{
lean_object* v___x_5445_; double v___x_5446_; double v___x_5447_; double v___x_5448_; double v___x_5449_; double v___x_5450_; lean_object* v___x_5451_; lean_object* v___x_5452_; lean_object* v___x_5454_; 
v___x_5445_ = lean_io_mono_nanos_now();
v___x_5446_ = lean_float_of_nat(v___y_5443_);
v___x_5447_ = lean_float_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9);
v___x_5448_ = lean_float_div(v___x_5446_, v___x_5447_);
v___x_5449_ = lean_float_of_nat(v___x_5445_);
v___x_5450_ = lean_float_div(v___x_5449_, v___x_5447_);
v___x_5451_ = lean_box_float(v___x_5448_);
v___x_5452_ = lean_box_float(v___x_5450_);
if (v_isShared_5333_ == 0)
{
lean_ctor_set(v___x_5332_, 1, v___x_5452_);
lean_ctor_set(v___x_5332_, 0, v___x_5451_);
v___x_5454_ = v___x_5332_;
goto v_reusejp_5453_;
}
else
{
lean_object* v_reuseFailAlloc_5457_; 
v_reuseFailAlloc_5457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5457_, 0, v___x_5451_);
lean_ctor_set(v_reuseFailAlloc_5457_, 1, v___x_5452_);
v___x_5454_ = v_reuseFailAlloc_5457_;
goto v_reusejp_5453_;
}
v_reusejp_5453_:
{
lean_object* v___x_5455_; lean_object* v___x_5456_; 
v___x_5455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5455_, 0, v_a_5444_);
lean_ctor_set(v___x_5455_, 1, v___x_5454_);
v___x_5456_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2(v___x_5437_, v_hasTrace_5431_, v___x_5438_, v_options_5430_, v___x_5440_, v___y_5442_, v___f_5436_, v___x_5455_, v___y_5291_, v___y_5292_, v___y_5293_, v___y_5294_, v___y_5295_, v___y_5296_);
v___y_5386_ = v___x_5456_;
goto v___jp_5385_;
}
}
v___jp_5458_:
{
lean_object* v___x_5462_; double v___x_5463_; double v___x_5464_; lean_object* v___x_5465_; lean_object* v___x_5466_; lean_object* v___x_5467_; lean_object* v___x_5468_; lean_object* v___x_5469_; 
v___x_5462_ = lean_io_get_num_heartbeats();
v___x_5463_ = lean_float_of_nat(v___y_5460_);
v___x_5464_ = lean_float_of_nat(v___x_5462_);
v___x_5465_ = lean_box_float(v___x_5463_);
v___x_5466_ = lean_box_float(v___x_5464_);
v___x_5467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5467_, 0, v___x_5465_);
lean_ctor_set(v___x_5467_, 1, v___x_5466_);
v___x_5468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5468_, 0, v_a_5461_);
lean_ctor_set(v___x_5468_, 1, v___x_5467_);
v___x_5469_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2(v___x_5437_, v_hasTrace_5431_, v___x_5438_, v_options_5430_, v___x_5440_, v___y_5459_, v___f_5436_, v___x_5468_, v___y_5291_, v___y_5292_, v___y_5293_, v___y_5294_, v___y_5295_, v___y_5296_);
v___y_5386_ = v___x_5469_;
goto v___jp_5385_;
}
v___jp_5470_:
{
lean_object* v___x_5471_; lean_object* v_a_5472_; lean_object* v___x_5473_; uint8_t v___x_5474_; 
v___x_5471_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1___redArg(v___y_5296_);
v_a_5472_ = lean_ctor_get(v___x_5471_, 0);
lean_inc(v_a_5472_);
lean_dec_ref(v___x_5471_);
v___x_5473_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5474_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_5430_, v___x_5473_);
if (v___x_5474_ == 0)
{
lean_object* v___x_5475_; lean_object* v___x_5476_; 
v___x_5475_ = lean_io_mono_nanos_now();
v___x_5476_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v_a_5434_, v_config_5285_, v___y_5291_, v___y_5292_, v___y_5293_, v___y_5294_, v___y_5295_, v___y_5296_);
if (lean_obj_tag(v___x_5476_) == 0)
{
lean_object* v_a_5477_; lean_object* v___x_5479_; uint8_t v_isShared_5480_; uint8_t v_isSharedCheck_5484_; 
v_a_5477_ = lean_ctor_get(v___x_5476_, 0);
v_isSharedCheck_5484_ = !lean_is_exclusive(v___x_5476_);
if (v_isSharedCheck_5484_ == 0)
{
v___x_5479_ = v___x_5476_;
v_isShared_5480_ = v_isSharedCheck_5484_;
goto v_resetjp_5478_;
}
else
{
lean_inc(v_a_5477_);
lean_dec(v___x_5476_);
v___x_5479_ = lean_box(0);
v_isShared_5480_ = v_isSharedCheck_5484_;
goto v_resetjp_5478_;
}
v_resetjp_5478_:
{
lean_object* v___x_5482_; 
if (v_isShared_5480_ == 0)
{
lean_ctor_set_tag(v___x_5479_, 1);
v___x_5482_ = v___x_5479_;
goto v_reusejp_5481_;
}
else
{
lean_object* v_reuseFailAlloc_5483_; 
v_reuseFailAlloc_5483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5483_, 0, v_a_5477_);
v___x_5482_ = v_reuseFailAlloc_5483_;
goto v_reusejp_5481_;
}
v_reusejp_5481_:
{
v___y_5442_ = v_a_5472_;
v___y_5443_ = v___x_5475_;
v_a_5444_ = v___x_5482_;
goto v___jp_5441_;
}
}
}
else
{
lean_object* v_a_5485_; lean_object* v___x_5487_; uint8_t v_isShared_5488_; uint8_t v_isSharedCheck_5492_; 
v_a_5485_ = lean_ctor_get(v___x_5476_, 0);
v_isSharedCheck_5492_ = !lean_is_exclusive(v___x_5476_);
if (v_isSharedCheck_5492_ == 0)
{
v___x_5487_ = v___x_5476_;
v_isShared_5488_ = v_isSharedCheck_5492_;
goto v_resetjp_5486_;
}
else
{
lean_inc(v_a_5485_);
lean_dec(v___x_5476_);
v___x_5487_ = lean_box(0);
v_isShared_5488_ = v_isSharedCheck_5492_;
goto v_resetjp_5486_;
}
v_resetjp_5486_:
{
lean_object* v___x_5490_; 
if (v_isShared_5488_ == 0)
{
lean_ctor_set_tag(v___x_5487_, 0);
v___x_5490_ = v___x_5487_;
goto v_reusejp_5489_;
}
else
{
lean_object* v_reuseFailAlloc_5491_; 
v_reuseFailAlloc_5491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5491_, 0, v_a_5485_);
v___x_5490_ = v_reuseFailAlloc_5491_;
goto v_reusejp_5489_;
}
v_reusejp_5489_:
{
v___y_5442_ = v_a_5472_;
v___y_5443_ = v___x_5475_;
v_a_5444_ = v___x_5490_;
goto v___jp_5441_;
}
}
}
}
else
{
lean_object* v___x_5493_; lean_object* v___x_5494_; 
lean_del_object(v___x_5332_);
v___x_5493_ = lean_io_get_num_heartbeats();
v___x_5494_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v_a_5434_, v_config_5285_, v___y_5291_, v___y_5292_, v___y_5293_, v___y_5294_, v___y_5295_, v___y_5296_);
if (lean_obj_tag(v___x_5494_) == 0)
{
lean_object* v_a_5495_; lean_object* v___x_5497_; uint8_t v_isShared_5498_; uint8_t v_isSharedCheck_5502_; 
v_a_5495_ = lean_ctor_get(v___x_5494_, 0);
v_isSharedCheck_5502_ = !lean_is_exclusive(v___x_5494_);
if (v_isSharedCheck_5502_ == 0)
{
v___x_5497_ = v___x_5494_;
v_isShared_5498_ = v_isSharedCheck_5502_;
goto v_resetjp_5496_;
}
else
{
lean_inc(v_a_5495_);
lean_dec(v___x_5494_);
v___x_5497_ = lean_box(0);
v_isShared_5498_ = v_isSharedCheck_5502_;
goto v_resetjp_5496_;
}
v_resetjp_5496_:
{
lean_object* v___x_5500_; 
if (v_isShared_5498_ == 0)
{
lean_ctor_set_tag(v___x_5497_, 1);
v___x_5500_ = v___x_5497_;
goto v_reusejp_5499_;
}
else
{
lean_object* v_reuseFailAlloc_5501_; 
v_reuseFailAlloc_5501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5501_, 0, v_a_5495_);
v___x_5500_ = v_reuseFailAlloc_5501_;
goto v_reusejp_5499_;
}
v_reusejp_5499_:
{
v___y_5459_ = v_a_5472_;
v___y_5460_ = v___x_5493_;
v_a_5461_ = v___x_5500_;
goto v___jp_5458_;
}
}
}
else
{
lean_object* v_a_5503_; lean_object* v___x_5505_; uint8_t v_isShared_5506_; uint8_t v_isSharedCheck_5510_; 
v_a_5503_ = lean_ctor_get(v___x_5494_, 0);
v_isSharedCheck_5510_ = !lean_is_exclusive(v___x_5494_);
if (v_isSharedCheck_5510_ == 0)
{
v___x_5505_ = v___x_5494_;
v_isShared_5506_ = v_isSharedCheck_5510_;
goto v_resetjp_5504_;
}
else
{
lean_inc(v_a_5503_);
lean_dec(v___x_5494_);
v___x_5505_ = lean_box(0);
v_isShared_5506_ = v_isSharedCheck_5510_;
goto v_resetjp_5504_;
}
v_resetjp_5504_:
{
lean_object* v___x_5508_; 
if (v_isShared_5506_ == 0)
{
lean_ctor_set_tag(v___x_5505_, 0);
v___x_5508_ = v___x_5505_;
goto v_reusejp_5507_;
}
else
{
lean_object* v_reuseFailAlloc_5509_; 
v_reuseFailAlloc_5509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5509_, 0, v_a_5503_);
v___x_5508_ = v_reuseFailAlloc_5509_;
goto v_reusejp_5507_;
}
v_reusejp_5507_:
{
v___y_5459_ = v_a_5472_;
v___y_5460_ = v___x_5493_;
v_a_5461_ = v___x_5508_;
goto v___jp_5458_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5514_; lean_object* v___x_5516_; uint8_t v_isShared_5517_; uint8_t v_isSharedCheck_5521_; 
lean_del_object(v___x_5332_);
lean_dec(v_snd_5330_);
lean_dec_ref(v_config_5285_);
lean_dec(v_mvarId_5284_);
v_a_5514_ = lean_ctor_get(v___x_5429_, 0);
v_isSharedCheck_5521_ = !lean_is_exclusive(v___x_5429_);
if (v_isSharedCheck_5521_ == 0)
{
v___x_5516_ = v___x_5429_;
v_isShared_5517_ = v_isSharedCheck_5521_;
goto v_resetjp_5515_;
}
else
{
lean_inc(v_a_5514_);
lean_dec(v___x_5429_);
v___x_5516_ = lean_box(0);
v_isShared_5517_ = v_isSharedCheck_5521_;
goto v_resetjp_5515_;
}
v_resetjp_5515_:
{
lean_object* v___x_5519_; 
if (v_isShared_5517_ == 0)
{
v___x_5519_ = v___x_5516_;
goto v_reusejp_5518_;
}
else
{
lean_object* v_reuseFailAlloc_5520_; 
v_reuseFailAlloc_5520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5520_, 0, v_a_5514_);
v___x_5519_ = v_reuseFailAlloc_5520_;
goto v_reusejp_5518_;
}
v_reusejp_5518_:
{
return v___x_5519_;
}
}
}
}
}
else
{
lean_object* v_val_5522_; lean_object* v___x_5524_; 
lean_del_object(v___x_5332_);
lean_dec(v_snd_5330_);
lean_dec_ref(v_config_5285_);
lean_dec(v_mvarId_5284_);
v_val_5522_ = lean_ctor_get(v_fst_5329_, 0);
lean_inc(v_val_5522_);
lean_dec_ref_known(v_fst_5329_, 1);
if (v_isShared_5328_ == 0)
{
lean_ctor_set(v___x_5327_, 0, v_val_5522_);
v___x_5524_ = v___x_5327_;
goto v_reusejp_5523_;
}
else
{
lean_object* v_reuseFailAlloc_5525_; 
v_reuseFailAlloc_5525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5525_, 0, v_val_5522_);
v___x_5524_ = v_reuseFailAlloc_5525_;
goto v_reusejp_5523_;
}
v_reusejp_5523_:
{
return v___x_5524_;
}
}
v___jp_5334_:
{
lean_object* v___x_5340_; 
v___x_5340_ = l_Lean_MVarId_assertHypotheses(v_mvarIdNew_5335_, v_snd_5330_, v___y_5336_, v___y_5337_, v___y_5338_, v___y_5339_);
if (lean_obj_tag(v___x_5340_) == 0)
{
lean_object* v_a_5341_; lean_object* v_snd_5342_; lean_object* v___x_5343_; 
v_a_5341_ = lean_ctor_get(v___x_5340_, 0);
lean_inc(v_a_5341_);
lean_dec_ref_known(v___x_5340_, 1);
v_snd_5342_ = lean_ctor_get(v_a_5341_, 1);
lean_inc(v_snd_5342_);
lean_dec(v_a_5341_);
v___x_5343_ = l_Lean_MVarId_tryClearMany(v_snd_5342_, v_fvarIdsToSimp_5286_, v___y_5336_, v___y_5337_, v___y_5338_, v___y_5339_);
if (lean_obj_tag(v___x_5343_) == 0)
{
lean_object* v_a_5344_; lean_object* v___x_5345_; 
v_a_5344_ = lean_ctor_get(v___x_5343_, 0);
lean_inc(v_a_5344_);
lean_dec_ref_known(v___x_5343_, 1);
v___x_5345_ = l_Lean_Meta_saveState___redArg(v___y_5337_, v___y_5339_);
if (lean_obj_tag(v___x_5345_) == 0)
{
lean_object* v_a_5346_; uint8_t v___x_5347_; lean_object* v___x_5348_; 
v_a_5346_ = lean_ctor_get(v___x_5345_, 0);
lean_inc(v_a_5346_);
lean_dec_ref_known(v___x_5345_, 1);
v___x_5347_ = 1;
lean_inc(v_a_5344_);
v___x_5348_ = l_Lean_MVarId_refl(v_a_5344_, v___x_5347_, v___y_5336_, v___y_5337_, v___y_5338_, v___y_5339_);
if (lean_obj_tag(v___x_5348_) == 0)
{
lean_object* v___x_5350_; uint8_t v_isShared_5351_; uint8_t v_isSharedCheck_5356_; 
lean_dec(v_a_5346_);
lean_dec(v_a_5344_);
v_isSharedCheck_5356_ = !lean_is_exclusive(v___x_5348_);
if (v_isSharedCheck_5356_ == 0)
{
lean_object* v_unused_5357_; 
v_unused_5357_ = lean_ctor_get(v___x_5348_, 0);
lean_dec(v_unused_5357_);
v___x_5350_ = v___x_5348_;
v_isShared_5351_ = v_isSharedCheck_5356_;
goto v_resetjp_5349_;
}
else
{
lean_dec(v___x_5348_);
v___x_5350_ = lean_box(0);
v_isShared_5351_ = v_isSharedCheck_5356_;
goto v_resetjp_5349_;
}
v_resetjp_5349_:
{
lean_object* v___x_5352_; lean_object* v___x_5354_; 
v___x_5352_ = lean_box(0);
if (v_isShared_5351_ == 0)
{
lean_ctor_set(v___x_5350_, 0, v___x_5352_);
v___x_5354_ = v___x_5350_;
goto v_reusejp_5353_;
}
else
{
lean_object* v_reuseFailAlloc_5355_; 
v_reuseFailAlloc_5355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5355_, 0, v___x_5352_);
v___x_5354_ = v_reuseFailAlloc_5355_;
goto v_reusejp_5353_;
}
v_reusejp_5353_:
{
return v___x_5354_;
}
}
}
else
{
lean_object* v_a_5358_; uint8_t v___x_5359_; 
v_a_5358_ = lean_ctor_get(v___x_5348_, 0);
lean_inc(v_a_5358_);
lean_dec_ref_known(v___x_5348_, 1);
v___x_5359_ = l_Lean_Exception_isInterrupt(v_a_5358_);
if (v___x_5359_ == 0)
{
uint8_t v___x_5360_; 
lean_inc(v_a_5358_);
v___x_5360_ = l_Lean_Exception_isRuntime(v_a_5358_);
v___y_5299_ = v___y_5339_;
v___y_5300_ = v_a_5344_;
v___y_5301_ = v___y_5337_;
v___y_5302_ = v_a_5346_;
v___y_5303_ = v_a_5358_;
v___y_5304_ = v___x_5360_;
goto v___jp_5298_;
}
else
{
v___y_5299_ = v___y_5339_;
v___y_5300_ = v_a_5344_;
v___y_5301_ = v___y_5337_;
v___y_5302_ = v_a_5346_;
v___y_5303_ = v_a_5358_;
v___y_5304_ = v___x_5359_;
goto v___jp_5298_;
}
}
}
else
{
lean_object* v_a_5361_; lean_object* v___x_5363_; uint8_t v_isShared_5364_; uint8_t v_isSharedCheck_5368_; 
lean_dec(v_a_5344_);
v_a_5361_ = lean_ctor_get(v___x_5345_, 0);
v_isSharedCheck_5368_ = !lean_is_exclusive(v___x_5345_);
if (v_isSharedCheck_5368_ == 0)
{
v___x_5363_ = v___x_5345_;
v_isShared_5364_ = v_isSharedCheck_5368_;
goto v_resetjp_5362_;
}
else
{
lean_inc(v_a_5361_);
lean_dec(v___x_5345_);
v___x_5363_ = lean_box(0);
v_isShared_5364_ = v_isSharedCheck_5368_;
goto v_resetjp_5362_;
}
v_resetjp_5362_:
{
lean_object* v___x_5366_; 
if (v_isShared_5364_ == 0)
{
v___x_5366_ = v___x_5363_;
goto v_reusejp_5365_;
}
else
{
lean_object* v_reuseFailAlloc_5367_; 
v_reuseFailAlloc_5367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5367_, 0, v_a_5361_);
v___x_5366_ = v_reuseFailAlloc_5367_;
goto v_reusejp_5365_;
}
v_reusejp_5365_:
{
return v___x_5366_;
}
}
}
}
else
{
lean_object* v_a_5369_; lean_object* v___x_5371_; uint8_t v_isShared_5372_; uint8_t v_isSharedCheck_5376_; 
v_a_5369_ = lean_ctor_get(v___x_5343_, 0);
v_isSharedCheck_5376_ = !lean_is_exclusive(v___x_5343_);
if (v_isSharedCheck_5376_ == 0)
{
v___x_5371_ = v___x_5343_;
v_isShared_5372_ = v_isSharedCheck_5376_;
goto v_resetjp_5370_;
}
else
{
lean_inc(v_a_5369_);
lean_dec(v___x_5343_);
v___x_5371_ = lean_box(0);
v_isShared_5372_ = v_isSharedCheck_5376_;
goto v_resetjp_5370_;
}
v_resetjp_5370_:
{
lean_object* v___x_5374_; 
if (v_isShared_5372_ == 0)
{
v___x_5374_ = v___x_5371_;
goto v_reusejp_5373_;
}
else
{
lean_object* v_reuseFailAlloc_5375_; 
v_reuseFailAlloc_5375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5375_, 0, v_a_5369_);
v___x_5374_ = v_reuseFailAlloc_5375_;
goto v_reusejp_5373_;
}
v_reusejp_5373_:
{
return v___x_5374_;
}
}
}
}
else
{
lean_object* v_a_5377_; lean_object* v___x_5379_; uint8_t v_isShared_5380_; uint8_t v_isSharedCheck_5384_; 
v_a_5377_ = lean_ctor_get(v___x_5340_, 0);
v_isSharedCheck_5384_ = !lean_is_exclusive(v___x_5340_);
if (v_isSharedCheck_5384_ == 0)
{
v___x_5379_ = v___x_5340_;
v_isShared_5380_ = v_isSharedCheck_5384_;
goto v_resetjp_5378_;
}
else
{
lean_inc(v_a_5377_);
lean_dec(v___x_5340_);
v___x_5379_ = lean_box(0);
v_isShared_5380_ = v_isSharedCheck_5384_;
goto v_resetjp_5378_;
}
v_resetjp_5378_:
{
lean_object* v___x_5382_; 
if (v_isShared_5380_ == 0)
{
v___x_5382_ = v___x_5379_;
goto v_reusejp_5381_;
}
else
{
lean_object* v_reuseFailAlloc_5383_; 
v_reuseFailAlloc_5383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5383_, 0, v_a_5377_);
v___x_5382_ = v_reuseFailAlloc_5383_;
goto v_reusejp_5381_;
}
v_reusejp_5381_:
{
return v___x_5382_;
}
}
}
}
v___jp_5385_:
{
if (lean_obj_tag(v___y_5386_) == 0)
{
lean_object* v_a_5387_; 
v_a_5387_ = lean_ctor_get(v___y_5386_, 0);
lean_inc(v_a_5387_);
lean_dec_ref_known(v___y_5386_, 1);
if (lean_obj_tag(v_a_5387_) == 0)
{
lean_dec_ref_known(v_a_5387_, 0);
v_mvarIdNew_5335_ = v_mvarId_5284_;
v___y_5336_ = v___y_5293_;
v___y_5337_ = v___y_5294_;
v___y_5338_ = v___y_5295_;
v___y_5339_ = v___y_5296_;
goto v___jp_5334_;
}
else
{
lean_object* v_e_x27_5388_; lean_object* v_proof_5389_; uint8_t v___x_5390_; 
v_e_x27_5388_ = lean_ctor_get(v_a_5387_, 0);
lean_inc_ref_n(v_e_x27_5388_, 2);
v_proof_5389_ = lean_ctor_get(v_a_5387_, 1);
lean_inc_ref(v_proof_5389_);
lean_dec_ref_known(v_a_5387_, 2);
v___x_5390_ = l_Lean_Expr_isTrue(v_e_x27_5388_);
if (v___x_5390_ == 0)
{
lean_object* v___x_5391_; 
v___x_5391_ = l_Lean_MVarId_replaceTargetEq(v_mvarId_5284_, v_e_x27_5388_, v_proof_5389_, v___y_5293_, v___y_5294_, v___y_5295_, v___y_5296_);
if (lean_obj_tag(v___x_5391_) == 0)
{
lean_object* v_a_5392_; 
v_a_5392_ = lean_ctor_get(v___x_5391_, 0);
lean_inc(v_a_5392_);
lean_dec_ref_known(v___x_5391_, 1);
v_mvarIdNew_5335_ = v_a_5392_;
v___y_5336_ = v___y_5293_;
v___y_5337_ = v___y_5294_;
v___y_5338_ = v___y_5295_;
v___y_5339_ = v___y_5296_;
goto v___jp_5334_;
}
else
{
lean_object* v_a_5393_; lean_object* v___x_5395_; uint8_t v_isShared_5396_; uint8_t v_isSharedCheck_5400_; 
lean_dec(v_snd_5330_);
v_a_5393_ = lean_ctor_get(v___x_5391_, 0);
v_isSharedCheck_5400_ = !lean_is_exclusive(v___x_5391_);
if (v_isSharedCheck_5400_ == 0)
{
v___x_5395_ = v___x_5391_;
v_isShared_5396_ = v_isSharedCheck_5400_;
goto v_resetjp_5394_;
}
else
{
lean_inc(v_a_5393_);
lean_dec(v___x_5391_);
v___x_5395_ = lean_box(0);
v_isShared_5396_ = v_isSharedCheck_5400_;
goto v_resetjp_5394_;
}
v_resetjp_5394_:
{
lean_object* v___x_5398_; 
if (v_isShared_5396_ == 0)
{
v___x_5398_ = v___x_5395_;
goto v_reusejp_5397_;
}
else
{
lean_object* v_reuseFailAlloc_5399_; 
v_reuseFailAlloc_5399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5399_, 0, v_a_5393_);
v___x_5398_ = v_reuseFailAlloc_5399_;
goto v_reusejp_5397_;
}
v_reusejp_5397_:
{
return v___x_5398_;
}
}
}
}
else
{
lean_object* v___x_5401_; 
lean_dec_ref(v_e_x27_5388_);
lean_dec(v_snd_5330_);
v___x_5401_ = l_Lean_Meta_mkOfEqTrue(v_proof_5389_, v___y_5293_, v___y_5294_, v___y_5295_, v___y_5296_);
if (lean_obj_tag(v___x_5401_) == 0)
{
lean_object* v_a_5402_; lean_object* v___x_5403_; lean_object* v___x_5405_; uint8_t v_isShared_5406_; uint8_t v_isSharedCheck_5411_; 
v_a_5402_ = lean_ctor_get(v___x_5401_, 0);
lean_inc(v_a_5402_);
lean_dec_ref_known(v___x_5401_, 1);
v___x_5403_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___redArg(v_mvarId_5284_, v_a_5402_, v___y_5294_);
v_isSharedCheck_5411_ = !lean_is_exclusive(v___x_5403_);
if (v_isSharedCheck_5411_ == 0)
{
lean_object* v_unused_5412_; 
v_unused_5412_ = lean_ctor_get(v___x_5403_, 0);
lean_dec(v_unused_5412_);
v___x_5405_ = v___x_5403_;
v_isShared_5406_ = v_isSharedCheck_5411_;
goto v_resetjp_5404_;
}
else
{
lean_dec(v___x_5403_);
v___x_5405_ = lean_box(0);
v_isShared_5406_ = v_isSharedCheck_5411_;
goto v_resetjp_5404_;
}
v_resetjp_5404_:
{
lean_object* v___x_5407_; lean_object* v___x_5409_; 
v___x_5407_ = lean_box(0);
if (v_isShared_5406_ == 0)
{
lean_ctor_set(v___x_5405_, 0, v___x_5407_);
v___x_5409_ = v___x_5405_;
goto v_reusejp_5408_;
}
else
{
lean_object* v_reuseFailAlloc_5410_; 
v_reuseFailAlloc_5410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5410_, 0, v___x_5407_);
v___x_5409_ = v_reuseFailAlloc_5410_;
goto v_reusejp_5408_;
}
v_reusejp_5408_:
{
return v___x_5409_;
}
}
}
else
{
lean_object* v_a_5413_; lean_object* v___x_5415_; uint8_t v_isShared_5416_; uint8_t v_isSharedCheck_5420_; 
lean_dec(v_mvarId_5284_);
v_a_5413_ = lean_ctor_get(v___x_5401_, 0);
v_isSharedCheck_5420_ = !lean_is_exclusive(v___x_5401_);
if (v_isSharedCheck_5420_ == 0)
{
v___x_5415_ = v___x_5401_;
v_isShared_5416_ = v_isSharedCheck_5420_;
goto v_resetjp_5414_;
}
else
{
lean_inc(v_a_5413_);
lean_dec(v___x_5401_);
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
}
}
else
{
lean_object* v_a_5421_; lean_object* v___x_5423_; uint8_t v_isShared_5424_; uint8_t v_isSharedCheck_5428_; 
lean_dec(v_snd_5330_);
lean_dec(v_mvarId_5284_);
v_a_5421_ = lean_ctor_get(v___y_5386_, 0);
v_isSharedCheck_5428_ = !lean_is_exclusive(v___y_5386_);
if (v_isSharedCheck_5428_ == 0)
{
v___x_5423_ = v___y_5386_;
v_isShared_5424_ = v_isSharedCheck_5428_;
goto v_resetjp_5422_;
}
else
{
lean_inc(v_a_5421_);
lean_dec(v___y_5386_);
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
}
}
}
else
{
lean_object* v_a_5528_; lean_object* v___x_5530_; uint8_t v_isShared_5531_; uint8_t v_isSharedCheck_5535_; 
lean_dec_ref(v_config_5285_);
lean_dec(v_mvarId_5284_);
v_a_5528_ = lean_ctor_get(v___x_5324_, 0);
v_isSharedCheck_5535_ = !lean_is_exclusive(v___x_5324_);
if (v_isSharedCheck_5535_ == 0)
{
v___x_5530_ = v___x_5324_;
v_isShared_5531_ = v_isSharedCheck_5535_;
goto v_resetjp_5529_;
}
else
{
lean_inc(v_a_5528_);
lean_dec(v___x_5324_);
v___x_5530_ = lean_box(0);
v_isShared_5531_ = v_isSharedCheck_5535_;
goto v_resetjp_5529_;
}
v_resetjp_5529_:
{
lean_object* v___x_5533_; 
if (v_isShared_5531_ == 0)
{
v___x_5533_ = v___x_5530_;
goto v_reusejp_5532_;
}
else
{
lean_object* v_reuseFailAlloc_5534_; 
v_reuseFailAlloc_5534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5534_, 0, v_a_5528_);
v___x_5533_ = v_reuseFailAlloc_5534_;
goto v_reusejp_5532_;
}
v_reusejp_5532_:
{
return v___x_5533_;
}
}
}
v___jp_5298_:
{
if (v___y_5304_ == 0)
{
lean_object* v___x_5305_; 
lean_dec_ref(v___y_5303_);
v___x_5305_ = l_Lean_Meta_SavedState_restore___redArg(v___y_5302_, v___y_5301_, v___y_5299_);
lean_dec_ref(v___y_5302_);
if (lean_obj_tag(v___x_5305_) == 0)
{
lean_object* v___x_5307_; uint8_t v_isShared_5308_; uint8_t v_isSharedCheck_5313_; 
v_isSharedCheck_5313_ = !lean_is_exclusive(v___x_5305_);
if (v_isSharedCheck_5313_ == 0)
{
lean_object* v_unused_5314_; 
v_unused_5314_ = lean_ctor_get(v___x_5305_, 0);
lean_dec(v_unused_5314_);
v___x_5307_ = v___x_5305_;
v_isShared_5308_ = v_isSharedCheck_5313_;
goto v_resetjp_5306_;
}
else
{
lean_dec(v___x_5305_);
v___x_5307_ = lean_box(0);
v_isShared_5308_ = v_isSharedCheck_5313_;
goto v_resetjp_5306_;
}
v_resetjp_5306_:
{
lean_object* v___x_5309_; lean_object* v___x_5311_; 
v___x_5309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5309_, 0, v___y_5300_);
if (v_isShared_5308_ == 0)
{
lean_ctor_set(v___x_5307_, 0, v___x_5309_);
v___x_5311_ = v___x_5307_;
goto v_reusejp_5310_;
}
else
{
lean_object* v_reuseFailAlloc_5312_; 
v_reuseFailAlloc_5312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5312_, 0, v___x_5309_);
v___x_5311_ = v_reuseFailAlloc_5312_;
goto v_reusejp_5310_;
}
v_reusejp_5310_:
{
return v___x_5311_;
}
}
}
else
{
lean_object* v_a_5315_; lean_object* v___x_5317_; uint8_t v_isShared_5318_; uint8_t v_isSharedCheck_5322_; 
lean_dec(v___y_5300_);
v_a_5315_ = lean_ctor_get(v___x_5305_, 0);
v_isSharedCheck_5322_ = !lean_is_exclusive(v___x_5305_);
if (v_isSharedCheck_5322_ == 0)
{
v___x_5317_ = v___x_5305_;
v_isShared_5318_ = v_isSharedCheck_5322_;
goto v_resetjp_5316_;
}
else
{
lean_inc(v_a_5315_);
lean_dec(v___x_5305_);
v___x_5317_ = lean_box(0);
v_isShared_5318_ = v_isSharedCheck_5322_;
goto v_resetjp_5316_;
}
v_resetjp_5316_:
{
lean_object* v___x_5320_; 
if (v_isShared_5318_ == 0)
{
v___x_5320_ = v___x_5317_;
goto v_reusejp_5319_;
}
else
{
lean_object* v_reuseFailAlloc_5321_; 
v_reuseFailAlloc_5321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5321_, 0, v_a_5315_);
v___x_5320_ = v_reuseFailAlloc_5321_;
goto v_reusejp_5319_;
}
v_reusejp_5319_:
{
return v___x_5320_;
}
}
}
}
else
{
lean_object* v___x_5323_; 
lean_dec_ref(v___y_5302_);
lean_dec(v___y_5300_);
v___x_5323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5323_, 0, v___y_5303_);
return v___x_5323_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__1___boxed(lean_object* v_mvarId_5536_, lean_object* v_config_5537_, lean_object* v_fvarIdsToSimp_5538_, lean_object* v_sz_5539_, lean_object* v___x_5540_, lean_object* v___x_5541_, lean_object* v_simplifyTarget_5542_, lean_object* v___y_5543_, lean_object* v___y_5544_, lean_object* v___y_5545_, lean_object* v___y_5546_, lean_object* v___y_5547_, lean_object* v___y_5548_, lean_object* v___y_5549_){
_start:
{
size_t v_sz_boxed_5550_; size_t v___x_49233__boxed_5551_; uint8_t v_simplifyTarget_boxed_5552_; lean_object* v_res_5553_; 
v_sz_boxed_5550_ = lean_unbox_usize(v_sz_5539_);
lean_dec(v_sz_5539_);
v___x_49233__boxed_5551_ = lean_unbox_usize(v___x_5540_);
lean_dec(v___x_5540_);
v_simplifyTarget_boxed_5552_ = lean_unbox(v_simplifyTarget_5542_);
v_res_5553_ = l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__1(v_mvarId_5536_, v_config_5537_, v_fvarIdsToSimp_5538_, v_sz_boxed_5550_, v___x_49233__boxed_5551_, v___x_5541_, v_simplifyTarget_boxed_5552_, v___y_5543_, v___y_5544_, v___y_5545_, v___y_5546_, v___y_5547_, v___y_5548_);
lean_dec(v___y_5548_);
lean_dec_ref(v___y_5547_);
lean_dec(v___y_5546_);
lean_dec_ref(v___y_5545_);
lean_dec(v___y_5544_);
lean_dec_ref(v___y_5543_);
lean_dec_ref(v_fvarIdsToSimp_5538_);
return v_res_5553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__2(lean_object* v_fvarIdsToSimp_5561_, lean_object* v_mvarId_5562_, uint8_t v_simplifyTarget_5563_, lean_object* v___y_5564_, lean_object* v___y_5565_, lean_object* v___y_5566_, lean_object* v___y_5567_, lean_object* v___y_5568_, lean_object* v___y_5569_){
_start:
{
lean_object* v_options_5571_; lean_object* v___x_5572_; lean_object* v___x_5573_; lean_object* v___x_5574_; lean_object* v_config_5575_; lean_object* v___x_5576_; size_t v_sz_5577_; lean_object* v___x_5578_; lean_object* v___x_5579_; lean_object* v___x_5580_; lean_object* v___f_5581_; lean_object* v___x_5582_; 
v_options_5571_ = lean_ctor_get(v___y_5568_, 2);
v___x_5572_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_5573_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_5571_, v___x_5572_);
v___x_5574_ = lean_unsigned_to_nat(2u);
v_config_5575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_config_5575_, 0, v___x_5573_);
lean_ctor_set(v_config_5575_, 1, v___x_5574_);
v___x_5576_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__2___closed__1));
v_sz_5577_ = lean_array_size(v_fvarIdsToSimp_5561_);
v___x_5578_ = lean_box_usize(v_sz_5577_);
v___x_5579_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__2___boxed__const__1));
v___x_5580_ = lean_box(v_simplifyTarget_5563_);
lean_inc(v_mvarId_5562_);
v___f_5581_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__1___boxed), 14, 7);
lean_closure_set(v___f_5581_, 0, v_mvarId_5562_);
lean_closure_set(v___f_5581_, 1, v_config_5575_);
lean_closure_set(v___f_5581_, 2, v_fvarIdsToSimp_5561_);
lean_closure_set(v___f_5581_, 3, v___x_5578_);
lean_closure_set(v___f_5581_, 4, v___x_5579_);
lean_closure_set(v___f_5581_, 5, v___x_5576_);
lean_closure_set(v___f_5581_, 6, v___x_5580_);
v___x_5582_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg(v_mvarId_5562_, v___f_5581_, v___y_5564_, v___y_5565_, v___y_5566_, v___y_5567_, v___y_5568_, v___y_5569_);
return v___x_5582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__2___boxed(lean_object* v_fvarIdsToSimp_5583_, lean_object* v_mvarId_5584_, lean_object* v_simplifyTarget_5585_, lean_object* v___y_5586_, lean_object* v___y_5587_, lean_object* v___y_5588_, lean_object* v___y_5589_, lean_object* v___y_5590_, lean_object* v___y_5591_, lean_object* v___y_5592_){
_start:
{
uint8_t v_simplifyTarget_boxed_5593_; lean_object* v_res_5594_; 
v_simplifyTarget_boxed_5593_ = lean_unbox(v_simplifyTarget_5585_);
v_res_5594_ = l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__2(v_fvarIdsToSimp_5583_, v_mvarId_5584_, v_simplifyTarget_boxed_5593_, v___y_5586_, v___y_5587_, v___y_5588_, v___y_5589_, v___y_5590_, v___y_5591_);
lean_dec(v___y_5591_);
lean_dec_ref(v___y_5590_);
lean_dec(v___y_5589_);
lean_dec_ref(v___y_5588_);
lean_dec(v___y_5587_);
lean_dec_ref(v___y_5586_);
return v_res_5594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore(lean_object* v_mvarId_5595_, uint8_t v_simplifyTarget_5596_, lean_object* v_fvarIdsToSimp_5597_, lean_object* v_a_5598_, lean_object* v_a_5599_, lean_object* v_a_5600_, lean_object* v_a_5601_, lean_object* v_a_5602_, lean_object* v_a_5603_){
_start:
{
lean_object* v___x_5605_; lean_object* v___f_5606_; lean_object* v___x_5607_; 
v___x_5605_ = lean_box(v_simplifyTarget_5596_);
v___f_5606_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__2___boxed), 10, 3);
lean_closure_set(v___f_5606_, 0, v_fvarIdsToSimp_5597_);
lean_closure_set(v___f_5606_, 1, v_mvarId_5595_);
lean_closure_set(v___f_5606_, 2, v___x_5605_);
v___x_5607_ = l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0___redArg(v___f_5606_, v_a_5598_, v_a_5599_, v_a_5600_, v_a_5601_, v_a_5602_, v_a_5603_);
return v___x_5607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___boxed(lean_object* v_mvarId_5608_, lean_object* v_simplifyTarget_5609_, lean_object* v_fvarIdsToSimp_5610_, lean_object* v_a_5611_, lean_object* v_a_5612_, lean_object* v_a_5613_, lean_object* v_a_5614_, lean_object* v_a_5615_, lean_object* v_a_5616_, lean_object* v_a_5617_){
_start:
{
uint8_t v_simplifyTarget_boxed_5618_; lean_object* v_res_5619_; 
v_simplifyTarget_boxed_5618_ = lean_unbox(v_simplifyTarget_5609_);
v_res_5619_ = l_Lean_Meta_Tactic_Cbv_cbvGoalCore(v_mvarId_5608_, v_simplifyTarget_boxed_5618_, v_fvarIdsToSimp_5610_, v_a_5611_, v_a_5612_, v_a_5613_, v_a_5614_, v_a_5615_, v_a_5616_);
lean_dec(v_a_5616_);
lean_dec_ref(v_a_5615_);
lean_dec(v_a_5614_);
lean_dec_ref(v_a_5613_);
lean_dec(v_a_5612_);
lean_dec_ref(v_a_5611_);
return v_res_5619_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0(lean_object* v_mvarId_5620_, lean_object* v_val_5621_, lean_object* v___y_5622_, lean_object* v___y_5623_, lean_object* v___y_5624_, lean_object* v___y_5625_, lean_object* v___y_5626_, lean_object* v___y_5627_){
_start:
{
lean_object* v___x_5629_; 
v___x_5629_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___redArg(v_mvarId_5620_, v_val_5621_, v___y_5625_);
return v___x_5629_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___boxed(lean_object* v_mvarId_5630_, lean_object* v_val_5631_, lean_object* v___y_5632_, lean_object* v___y_5633_, lean_object* v___y_5634_, lean_object* v___y_5635_, lean_object* v___y_5636_, lean_object* v___y_5637_, lean_object* v___y_5638_){
_start:
{
lean_object* v_res_5639_; 
v_res_5639_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0(v_mvarId_5630_, v_val_5631_, v___y_5632_, v___y_5633_, v___y_5634_, v___y_5635_, v___y_5636_, v___y_5637_);
lean_dec(v___y_5637_);
lean_dec_ref(v___y_5636_);
lean_dec(v___y_5635_);
lean_dec_ref(v___y_5634_);
lean_dec(v___y_5633_);
lean_dec_ref(v___y_5632_);
return v_res_5639_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4(lean_object* v_00_u03b1_5640_, lean_object* v_x_5641_, lean_object* v___y_5642_, lean_object* v___y_5643_, lean_object* v___y_5644_, lean_object* v___y_5645_, lean_object* v___y_5646_, lean_object* v___y_5647_){
_start:
{
lean_object* v___x_5649_; 
v___x_5649_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4___redArg(v_x_5641_);
return v___x_5649_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4___boxed(lean_object* v_00_u03b1_5650_, lean_object* v_x_5651_, lean_object* v___y_5652_, lean_object* v___y_5653_, lean_object* v___y_5654_, lean_object* v___y_5655_, lean_object* v___y_5656_, lean_object* v___y_5657_, lean_object* v___y_5658_){
_start:
{
lean_object* v_res_5659_; 
v_res_5659_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4(v_00_u03b1_5650_, v_x_5651_, v___y_5652_, v___y_5653_, v___y_5654_, v___y_5655_, v___y_5656_, v___y_5657_);
lean_dec(v___y_5657_);
lean_dec_ref(v___y_5656_);
lean_dec(v___y_5655_);
lean_dec_ref(v___y_5654_);
lean_dec(v___y_5653_);
lean_dec_ref(v___y_5652_);
return v_res_5659_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0(lean_object* v_00_u03b2_5660_, lean_object* v_x_5661_, lean_object* v_x_5662_, lean_object* v_x_5663_){
_start:
{
lean_object* v___x_5664_; 
v___x_5664_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0___redArg(v_x_5661_, v_x_5662_, v_x_5663_);
return v___x_5664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__3(lean_object* v_oldTraces_5665_, lean_object* v_data_5666_, lean_object* v_ref_5667_, lean_object* v_msg_5668_, lean_object* v___y_5669_, lean_object* v___y_5670_, lean_object* v___y_5671_, lean_object* v___y_5672_, lean_object* v___y_5673_, lean_object* v___y_5674_){
_start:
{
lean_object* v___x_5676_; 
v___x_5676_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__3___redArg(v_oldTraces_5665_, v_data_5666_, v_ref_5667_, v_msg_5668_, v___y_5671_, v___y_5672_, v___y_5673_, v___y_5674_);
return v___x_5676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__3___boxed(lean_object* v_oldTraces_5677_, lean_object* v_data_5678_, lean_object* v_ref_5679_, lean_object* v_msg_5680_, lean_object* v___y_5681_, lean_object* v___y_5682_, lean_object* v___y_5683_, lean_object* v___y_5684_, lean_object* v___y_5685_, lean_object* v___y_5686_, lean_object* v___y_5687_){
_start:
{
lean_object* v_res_5688_; 
v_res_5688_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__3(v_oldTraces_5677_, v_data_5678_, v_ref_5679_, v_msg_5680_, v___y_5681_, v___y_5682_, v___y_5683_, v___y_5684_, v___y_5685_, v___y_5686_);
lean_dec(v___y_5686_);
lean_dec_ref(v___y_5685_);
lean_dec(v___y_5684_);
lean_dec_ref(v___y_5683_);
lean_dec(v___y_5682_);
lean_dec_ref(v___y_5681_);
return v_res_5688_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_5689_, lean_object* v_x_5690_, size_t v_x_5691_, size_t v_x_5692_, lean_object* v_x_5693_, lean_object* v_x_5694_){
_start:
{
lean_object* v___x_5695_; 
v___x_5695_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg(v_x_5690_, v_x_5691_, v_x_5692_, v_x_5693_, v_x_5694_);
return v___x_5695_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_5696_, lean_object* v_x_5697_, lean_object* v_x_5698_, lean_object* v_x_5699_, lean_object* v_x_5700_, lean_object* v_x_5701_){
_start:
{
size_t v_x_49883__boxed_5702_; size_t v_x_49884__boxed_5703_; lean_object* v_res_5704_; 
v_x_49883__boxed_5702_ = lean_unbox_usize(v_x_5698_);
lean_dec(v_x_5698_);
v_x_49884__boxed_5703_ = lean_unbox_usize(v_x_5699_);
lean_dec(v_x_5699_);
v_res_5704_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3(v_00_u03b2_5696_, v_x_5697_, v_x_49883__boxed_5702_, v_x_49884__boxed_5703_, v_x_5700_, v_x_5701_);
return v_res_5704_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__7(lean_object* v_00_u03b2_5705_, lean_object* v_n_5706_, lean_object* v_k_5707_, lean_object* v_v_5708_){
_start:
{
lean_object* v___x_5709_; 
v___x_5709_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__7___redArg(v_n_5706_, v_k_5707_, v_v_5708_);
return v___x_5709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__8(lean_object* v_00_u03b2_5710_, size_t v_depth_5711_, lean_object* v_keys_5712_, lean_object* v_vals_5713_, lean_object* v_heq_5714_, lean_object* v_i_5715_, lean_object* v_entries_5716_){
_start:
{
lean_object* v___x_5717_; 
v___x_5717_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__8___redArg(v_depth_5711_, v_keys_5712_, v_vals_5713_, v_i_5715_, v_entries_5716_);
return v___x_5717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__8___boxed(lean_object* v_00_u03b2_5718_, lean_object* v_depth_5719_, lean_object* v_keys_5720_, lean_object* v_vals_5721_, lean_object* v_heq_5722_, lean_object* v_i_5723_, lean_object* v_entries_5724_){
_start:
{
size_t v_depth_boxed_5725_; lean_object* v_res_5726_; 
v_depth_boxed_5725_ = lean_unbox_usize(v_depth_5719_);
lean_dec(v_depth_5719_);
v_res_5726_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__8(v_00_u03b2_5718_, v_depth_boxed_5725_, v_keys_5720_, v_vals_5721_, v_heq_5722_, v_i_5723_, v_entries_5724_);
lean_dec_ref(v_vals_5721_);
lean_dec_ref(v_keys_5720_);
return v_res_5726_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__7_spec__9(lean_object* v_00_u03b2_5727_, lean_object* v_x_5728_, lean_object* v_x_5729_, lean_object* v_x_5730_, lean_object* v_x_5731_){
_start:
{
lean_object* v___x_5732_; 
v___x_5732_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__7_spec__9___redArg(v_x_5728_, v_x_5729_, v_x_5730_, v_x_5731_);
return v___x_5732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0(lean_object* v_mvarId_5733_, uint8_t v_simplifyTarget_5734_, lean_object* v_fvarIdsToSimp_5735_, lean_object* v___y_5736_, lean_object* v___y_5737_, lean_object* v___y_5738_, lean_object* v___y_5739_, lean_object* v___y_5740_, lean_object* v___y_5741_){
_start:
{
lean_object* v___x_5743_; 
v___x_5743_ = l_Lean_Meta_Sym_preprocessMVar(v_mvarId_5733_, v___y_5736_, v___y_5737_, v___y_5738_, v___y_5739_, v___y_5740_, v___y_5741_);
if (lean_obj_tag(v___x_5743_) == 0)
{
lean_object* v_a_5744_; lean_object* v___x_5745_; 
v_a_5744_ = lean_ctor_get(v___x_5743_, 0);
lean_inc(v_a_5744_);
lean_dec_ref_known(v___x_5743_, 1);
v___x_5745_ = l_Lean_Meta_Tactic_Cbv_cbvGoalCore(v_a_5744_, v_simplifyTarget_5734_, v_fvarIdsToSimp_5735_, v___y_5736_, v___y_5737_, v___y_5738_, v___y_5739_, v___y_5740_, v___y_5741_);
return v___x_5745_;
}
else
{
lean_object* v_a_5746_; lean_object* v___x_5748_; uint8_t v_isShared_5749_; uint8_t v_isSharedCheck_5753_; 
lean_dec_ref(v_fvarIdsToSimp_5735_);
v_a_5746_ = lean_ctor_get(v___x_5743_, 0);
v_isSharedCheck_5753_ = !lean_is_exclusive(v___x_5743_);
if (v_isSharedCheck_5753_ == 0)
{
v___x_5748_ = v___x_5743_;
v_isShared_5749_ = v_isSharedCheck_5753_;
goto v_resetjp_5747_;
}
else
{
lean_inc(v_a_5746_);
lean_dec(v___x_5743_);
v___x_5748_ = lean_box(0);
v_isShared_5749_ = v_isSharedCheck_5753_;
goto v_resetjp_5747_;
}
v_resetjp_5747_:
{
lean_object* v___x_5751_; 
if (v_isShared_5749_ == 0)
{
v___x_5751_ = v___x_5748_;
goto v_reusejp_5750_;
}
else
{
lean_object* v_reuseFailAlloc_5752_; 
v_reuseFailAlloc_5752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5752_, 0, v_a_5746_);
v___x_5751_ = v_reuseFailAlloc_5752_;
goto v_reusejp_5750_;
}
v_reusejp_5750_:
{
return v___x_5751_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___boxed(lean_object* v_mvarId_5754_, lean_object* v_simplifyTarget_5755_, lean_object* v_fvarIdsToSimp_5756_, lean_object* v___y_5757_, lean_object* v___y_5758_, lean_object* v___y_5759_, lean_object* v___y_5760_, lean_object* v___y_5761_, lean_object* v___y_5762_, lean_object* v___y_5763_){
_start:
{
uint8_t v_simplifyTarget_boxed_5764_; lean_object* v_res_5765_; 
v_simplifyTarget_boxed_5764_ = lean_unbox(v_simplifyTarget_5755_);
v_res_5765_ = l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0(v_mvarId_5754_, v_simplifyTarget_boxed_5764_, v_fvarIdsToSimp_5756_, v___y_5757_, v___y_5758_, v___y_5759_, v___y_5760_, v___y_5761_, v___y_5762_);
lean_dec(v___y_5762_);
lean_dec_ref(v___y_5761_);
lean_dec(v___y_5760_);
lean_dec_ref(v___y_5759_);
lean_dec(v___y_5758_);
lean_dec_ref(v___y_5757_);
return v_res_5765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal(lean_object* v_mvarId_5766_, uint8_t v_simplifyTarget_5767_, lean_object* v_fvarIdsToSimp_5768_, lean_object* v_a_5769_, lean_object* v_a_5770_, lean_object* v_a_5771_, lean_object* v_a_5772_){
_start:
{
lean_object* v___x_5774_; lean_object* v___f_5775_; lean_object* v___x_5776_; 
v___x_5774_ = lean_box(v_simplifyTarget_5767_);
v___f_5775_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___boxed), 10, 3);
lean_closure_set(v___f_5775_, 0, v_mvarId_5766_);
lean_closure_set(v___f_5775_, 1, v___x_5774_);
lean_closure_set(v___f_5775_, 2, v_fvarIdsToSimp_5768_);
v___x_5776_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_5775_, v_a_5769_, v_a_5770_, v_a_5771_, v_a_5772_);
return v___x_5776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___boxed(lean_object* v_mvarId_5777_, lean_object* v_simplifyTarget_5778_, lean_object* v_fvarIdsToSimp_5779_, lean_object* v_a_5780_, lean_object* v_a_5781_, lean_object* v_a_5782_, lean_object* v_a_5783_, lean_object* v_a_5784_){
_start:
{
uint8_t v_simplifyTarget_boxed_5785_; lean_object* v_res_5786_; 
v_simplifyTarget_boxed_5785_ = lean_unbox(v_simplifyTarget_5778_);
v_res_5786_ = l_Lean_Meta_Tactic_Cbv_cbvGoal(v_mvarId_5777_, v_simplifyTarget_boxed_5785_, v_fvarIdsToSimp_5779_, v_a_5780_, v_a_5781_, v_a_5782_, v_a_5783_);
lean_dec(v_a_5783_);
lean_dec_ref(v_a_5782_);
lean_dec(v_a_5781_);
lean_dec_ref(v_a_5780_);
return v_res_5786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0(lean_object* v_a_5787_, uint8_t v___x_5788_, lean_object* v___y_5789_, lean_object* v___y_5790_, lean_object* v___y_5791_, lean_object* v___y_5792_, lean_object* v___y_5793_, lean_object* v___y_5794_){
_start:
{
lean_object* v___x_5796_; 
v___x_5796_ = l_Lean_MVarId_refl(v_a_5787_, v___x_5788_, v___y_5791_, v___y_5792_, v___y_5793_, v___y_5794_);
return v___x_5796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0___boxed(lean_object* v_a_5797_, lean_object* v___x_5798_, lean_object* v___y_5799_, lean_object* v___y_5800_, lean_object* v___y_5801_, lean_object* v___y_5802_, lean_object* v___y_5803_, lean_object* v___y_5804_, lean_object* v___y_5805_){
_start:
{
uint8_t v___x_25154__boxed_5806_; lean_object* v_res_5807_; 
v___x_25154__boxed_5806_ = lean_unbox(v___x_5798_);
v_res_5807_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0(v_a_5797_, v___x_25154__boxed_5806_, v___y_5799_, v___y_5800_, v___y_5801_, v___y_5802_, v___y_5803_, v___y_5804_);
lean_dec(v___y_5804_);
lean_dec_ref(v___y_5803_);
lean_dec(v___y_5802_);
lean_dec_ref(v___y_5801_);
lean_dec(v___y_5800_);
lean_dec_ref(v___y_5799_);
return v_res_5807_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(lean_object* v_cls_5808_, lean_object* v_msg_5809_, lean_object* v___y_5810_, lean_object* v___y_5811_, lean_object* v___y_5812_, lean_object* v___y_5813_){
_start:
{
lean_object* v_ref_5815_; lean_object* v___x_5816_; lean_object* v_a_5817_; lean_object* v___x_5819_; uint8_t v_isShared_5820_; uint8_t v_isSharedCheck_5861_; 
v_ref_5815_ = lean_ctor_get(v___y_5812_, 5);
v___x_5816_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0_spec__0(v_msg_5809_, v___y_5810_, v___y_5811_, v___y_5812_, v___y_5813_);
v_a_5817_ = lean_ctor_get(v___x_5816_, 0);
v_isSharedCheck_5861_ = !lean_is_exclusive(v___x_5816_);
if (v_isSharedCheck_5861_ == 0)
{
v___x_5819_ = v___x_5816_;
v_isShared_5820_ = v_isSharedCheck_5861_;
goto v_resetjp_5818_;
}
else
{
lean_inc(v_a_5817_);
lean_dec(v___x_5816_);
v___x_5819_ = lean_box(0);
v_isShared_5820_ = v_isSharedCheck_5861_;
goto v_resetjp_5818_;
}
v_resetjp_5818_:
{
lean_object* v___x_5821_; lean_object* v_traceState_5822_; lean_object* v_env_5823_; lean_object* v_nextMacroScope_5824_; lean_object* v_ngen_5825_; lean_object* v_auxDeclNGen_5826_; lean_object* v_cache_5827_; lean_object* v_messages_5828_; lean_object* v_infoState_5829_; lean_object* v_snapshotTasks_5830_; lean_object* v___x_5832_; uint8_t v_isShared_5833_; uint8_t v_isSharedCheck_5860_; 
v___x_5821_ = lean_st_ref_take(v___y_5813_);
v_traceState_5822_ = lean_ctor_get(v___x_5821_, 4);
v_env_5823_ = lean_ctor_get(v___x_5821_, 0);
v_nextMacroScope_5824_ = lean_ctor_get(v___x_5821_, 1);
v_ngen_5825_ = lean_ctor_get(v___x_5821_, 2);
v_auxDeclNGen_5826_ = lean_ctor_get(v___x_5821_, 3);
v_cache_5827_ = lean_ctor_get(v___x_5821_, 5);
v_messages_5828_ = lean_ctor_get(v___x_5821_, 6);
v_infoState_5829_ = lean_ctor_get(v___x_5821_, 7);
v_snapshotTasks_5830_ = lean_ctor_get(v___x_5821_, 8);
v_isSharedCheck_5860_ = !lean_is_exclusive(v___x_5821_);
if (v_isSharedCheck_5860_ == 0)
{
v___x_5832_ = v___x_5821_;
v_isShared_5833_ = v_isSharedCheck_5860_;
goto v_resetjp_5831_;
}
else
{
lean_inc(v_snapshotTasks_5830_);
lean_inc(v_infoState_5829_);
lean_inc(v_messages_5828_);
lean_inc(v_cache_5827_);
lean_inc(v_traceState_5822_);
lean_inc(v_auxDeclNGen_5826_);
lean_inc(v_ngen_5825_);
lean_inc(v_nextMacroScope_5824_);
lean_inc(v_env_5823_);
lean_dec(v___x_5821_);
v___x_5832_ = lean_box(0);
v_isShared_5833_ = v_isSharedCheck_5860_;
goto v_resetjp_5831_;
}
v_resetjp_5831_:
{
uint64_t v_tid_5834_; lean_object* v_traces_5835_; lean_object* v___x_5837_; uint8_t v_isShared_5838_; uint8_t v_isSharedCheck_5859_; 
v_tid_5834_ = lean_ctor_get_uint64(v_traceState_5822_, sizeof(void*)*1);
v_traces_5835_ = lean_ctor_get(v_traceState_5822_, 0);
v_isSharedCheck_5859_ = !lean_is_exclusive(v_traceState_5822_);
if (v_isSharedCheck_5859_ == 0)
{
v___x_5837_ = v_traceState_5822_;
v_isShared_5838_ = v_isSharedCheck_5859_;
goto v_resetjp_5836_;
}
else
{
lean_inc(v_traces_5835_);
lean_dec(v_traceState_5822_);
v___x_5837_ = lean_box(0);
v_isShared_5838_ = v_isSharedCheck_5859_;
goto v_resetjp_5836_;
}
v_resetjp_5836_:
{
lean_object* v___x_5839_; double v___x_5840_; uint8_t v___x_5841_; lean_object* v___x_5842_; lean_object* v___x_5843_; lean_object* v___x_5844_; lean_object* v___x_5845_; lean_object* v___x_5846_; lean_object* v___x_5847_; lean_object* v___x_5849_; 
v___x_5839_ = lean_box(0);
v___x_5840_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0);
v___x_5841_ = 0;
v___x_5842_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__1));
v___x_5843_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_5843_, 0, v_cls_5808_);
lean_ctor_set(v___x_5843_, 1, v___x_5839_);
lean_ctor_set(v___x_5843_, 2, v___x_5842_);
lean_ctor_set_float(v___x_5843_, sizeof(void*)*3, v___x_5840_);
lean_ctor_set_float(v___x_5843_, sizeof(void*)*3 + 8, v___x_5840_);
lean_ctor_set_uint8(v___x_5843_, sizeof(void*)*3 + 16, v___x_5841_);
v___x_5844_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__2));
v___x_5845_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_5845_, 0, v___x_5843_);
lean_ctor_set(v___x_5845_, 1, v_a_5817_);
lean_ctor_set(v___x_5845_, 2, v___x_5844_);
lean_inc(v_ref_5815_);
v___x_5846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5846_, 0, v_ref_5815_);
lean_ctor_set(v___x_5846_, 1, v___x_5845_);
v___x_5847_ = l_Lean_PersistentArray_push___redArg(v_traces_5835_, v___x_5846_);
if (v_isShared_5838_ == 0)
{
lean_ctor_set(v___x_5837_, 0, v___x_5847_);
v___x_5849_ = v___x_5837_;
goto v_reusejp_5848_;
}
else
{
lean_object* v_reuseFailAlloc_5858_; 
v_reuseFailAlloc_5858_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5858_, 0, v___x_5847_);
lean_ctor_set_uint64(v_reuseFailAlloc_5858_, sizeof(void*)*1, v_tid_5834_);
v___x_5849_ = v_reuseFailAlloc_5858_;
goto v_reusejp_5848_;
}
v_reusejp_5848_:
{
lean_object* v___x_5851_; 
if (v_isShared_5833_ == 0)
{
lean_ctor_set(v___x_5832_, 4, v___x_5849_);
v___x_5851_ = v___x_5832_;
goto v_reusejp_5850_;
}
else
{
lean_object* v_reuseFailAlloc_5857_; 
v_reuseFailAlloc_5857_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5857_, 0, v_env_5823_);
lean_ctor_set(v_reuseFailAlloc_5857_, 1, v_nextMacroScope_5824_);
lean_ctor_set(v_reuseFailAlloc_5857_, 2, v_ngen_5825_);
lean_ctor_set(v_reuseFailAlloc_5857_, 3, v_auxDeclNGen_5826_);
lean_ctor_set(v_reuseFailAlloc_5857_, 4, v___x_5849_);
lean_ctor_set(v_reuseFailAlloc_5857_, 5, v_cache_5827_);
lean_ctor_set(v_reuseFailAlloc_5857_, 6, v_messages_5828_);
lean_ctor_set(v_reuseFailAlloc_5857_, 7, v_infoState_5829_);
lean_ctor_set(v_reuseFailAlloc_5857_, 8, v_snapshotTasks_5830_);
v___x_5851_ = v_reuseFailAlloc_5857_;
goto v_reusejp_5850_;
}
v_reusejp_5850_:
{
lean_object* v___x_5852_; lean_object* v___x_5853_; lean_object* v___x_5855_; 
v___x_5852_ = lean_st_ref_set(v___y_5813_, v___x_5851_);
v___x_5853_ = lean_box(0);
if (v_isShared_5820_ == 0)
{
lean_ctor_set(v___x_5819_, 0, v___x_5853_);
v___x_5855_ = v___x_5819_;
goto v_reusejp_5854_;
}
else
{
lean_object* v_reuseFailAlloc_5856_; 
v_reuseFailAlloc_5856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5856_, 0, v___x_5853_);
v___x_5855_ = v_reuseFailAlloc_5856_;
goto v_reusejp_5854_;
}
v_reusejp_5854_:
{
return v___x_5855_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg___boxed(lean_object* v_cls_5862_, lean_object* v_msg_5863_, lean_object* v___y_5864_, lean_object* v___y_5865_, lean_object* v___y_5866_, lean_object* v___y_5867_, lean_object* v___y_5868_){
_start:
{
lean_object* v_res_5869_; 
v_res_5869_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(v_cls_5862_, v_msg_5863_, v___y_5864_, v___y_5865_, v___y_5866_, v___y_5867_);
lean_dec(v___y_5867_);
lean_dec_ref(v___y_5866_);
lean_dec(v___y_5865_);
lean_dec_ref(v___y_5864_);
return v_res_5869_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(lean_object* v_msg_5870_, lean_object* v___y_5871_, lean_object* v___y_5872_, lean_object* v___y_5873_, lean_object* v___y_5874_){
_start:
{
lean_object* v_ref_5876_; lean_object* v___x_5877_; lean_object* v_a_5878_; lean_object* v___x_5880_; uint8_t v_isShared_5881_; uint8_t v_isSharedCheck_5886_; 
v_ref_5876_ = lean_ctor_get(v___y_5873_, 5);
v___x_5877_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0_spec__0(v_msg_5870_, v___y_5871_, v___y_5872_, v___y_5873_, v___y_5874_);
v_a_5878_ = lean_ctor_get(v___x_5877_, 0);
v_isSharedCheck_5886_ = !lean_is_exclusive(v___x_5877_);
if (v_isSharedCheck_5886_ == 0)
{
v___x_5880_ = v___x_5877_;
v_isShared_5881_ = v_isSharedCheck_5886_;
goto v_resetjp_5879_;
}
else
{
lean_inc(v_a_5878_);
lean_dec(v___x_5877_);
v___x_5880_ = lean_box(0);
v_isShared_5881_ = v_isSharedCheck_5886_;
goto v_resetjp_5879_;
}
v_resetjp_5879_:
{
lean_object* v___x_5882_; lean_object* v___x_5884_; 
lean_inc(v_ref_5876_);
v___x_5882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5882_, 0, v_ref_5876_);
lean_ctor_set(v___x_5882_, 1, v_a_5878_);
if (v_isShared_5881_ == 0)
{
lean_ctor_set_tag(v___x_5880_, 1);
lean_ctor_set(v___x_5880_, 0, v___x_5882_);
v___x_5884_ = v___x_5880_;
goto v_reusejp_5883_;
}
else
{
lean_object* v_reuseFailAlloc_5885_; 
v_reuseFailAlloc_5885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5885_, 0, v___x_5882_);
v___x_5884_ = v_reuseFailAlloc_5885_;
goto v_reusejp_5883_;
}
v_reusejp_5883_:
{
return v___x_5884_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg___boxed(lean_object* v_msg_5887_, lean_object* v___y_5888_, lean_object* v___y_5889_, lean_object* v___y_5890_, lean_object* v___y_5891_, lean_object* v___y_5892_){
_start:
{
lean_object* v_res_5893_; 
v_res_5893_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v_msg_5887_, v___y_5888_, v___y_5889_, v___y_5890_, v___y_5891_);
lean_dec(v___y_5891_);
lean_dec_ref(v___y_5890_);
lean_dec(v___y_5889_);
lean_dec_ref(v___y_5888_);
return v_res_5893_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1(void){
_start:
{
lean_object* v___x_5895_; lean_object* v___x_5896_; 
v___x_5895_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__0));
v___x_5896_ = l_Lean_stringToMessageData(v___x_5895_);
return v___x_5896_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3(void){
_start:
{
lean_object* v___x_5898_; lean_object* v___x_5899_; 
v___x_5898_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__2));
v___x_5899_ = l_Lean_stringToMessageData(v___x_5898_);
return v___x_5899_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6(void){
_start:
{
lean_object* v___x_5903_; lean_object* v___x_5904_; 
v___x_5903_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__5));
v___x_5904_ = l_Lean_stringToMessageData(v___x_5903_);
return v___x_5904_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8(void){
_start:
{
lean_object* v___x_5906_; lean_object* v___x_5907_; 
v___x_5906_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__7));
v___x_5907_ = l_Lean_stringToMessageData(v___x_5906_);
return v___x_5907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1(lean_object* v_m_5908_, lean_object* v___x_5909_, lean_object* v_cls_5910_, lean_object* v___y_5911_, lean_object* v___y_5912_, lean_object* v___y_5913_, lean_object* v___y_5914_, lean_object* v___y_5915_, lean_object* v___y_5916_){
_start:
{
lean_object* v_e_5919_; lean_object* v_onTrue_5920_; lean_object* v___y_5921_; lean_object* v___y_5922_; lean_object* v___y_5923_; lean_object* v___y_5924_; lean_object* v___y_5925_; lean_object* v___y_5926_; lean_object* v___x_5956_; 
v___x_5956_ = l_Lean_Meta_Sym_preprocessMVar(v_m_5908_, v___y_5911_, v___y_5912_, v___y_5913_, v___y_5914_, v___y_5915_, v___y_5916_);
if (lean_obj_tag(v___x_5956_) == 0)
{
lean_object* v_a_5957_; lean_object* v___x_5958_; 
v_a_5957_ = lean_ctor_get(v___x_5956_, 0);
lean_inc_n(v_a_5957_, 2);
lean_dec_ref_known(v___x_5956_, 1);
v___x_5958_ = l_Lean_MVarId_getType(v_a_5957_, v___y_5913_, v___y_5914_, v___y_5915_, v___y_5916_);
if (lean_obj_tag(v___x_5958_) == 0)
{
lean_object* v_a_5959_; lean_object* v___x_5960_; lean_object* v___x_5961_; uint8_t v___x_5962_; 
v_a_5959_ = lean_ctor_get(v___x_5958_, 0);
lean_inc(v_a_5959_);
lean_dec_ref_known(v___x_5958_, 1);
v___x_5960_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__4));
v___x_5961_ = lean_unsigned_to_nat(3u);
v___x_5962_ = l_Lean_Expr_isAppOfArity(v_a_5959_, v___x_5960_, v___x_5961_);
if (v___x_5962_ == 0)
{
lean_object* v___x_5963_; lean_object* v___x_5964_; lean_object* v___x_5965_; lean_object* v___x_5966_; 
lean_dec(v_a_5957_);
lean_dec(v_cls_5910_);
lean_dec_ref(v___x_5909_);
v___x_5963_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6);
v___x_5964_ = l_Lean_indentExpr(v_a_5959_);
v___x_5965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5965_, 0, v___x_5963_);
lean_ctor_set(v___x_5965_, 1, v___x_5964_);
v___x_5966_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_5965_, v___y_5913_, v___y_5914_, v___y_5915_, v___y_5916_);
return v___x_5966_;
}
else
{
lean_object* v___x_5967_; lean_object* v___x_5968_; lean_object* v___x_5969_; 
v___x_5967_ = l_Lean_Expr_appFn_x21(v_a_5959_);
lean_dec(v_a_5959_);
v___x_5968_ = l_Lean_Expr_appArg_x21(v___x_5967_);
lean_dec_ref(v___x_5967_);
lean_inc_ref(v___x_5968_);
v___x_5969_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_5968_, v___x_5909_, v___y_5911_, v___y_5912_, v___y_5913_, v___y_5914_, v___y_5915_, v___y_5916_);
if (lean_obj_tag(v___x_5969_) == 0)
{
lean_object* v_options_5970_; lean_object* v_a_5971_; lean_object* v_inheritedTraceOptions_5972_; uint8_t v_hasTrace_5973_; lean_object* v___x_5974_; lean_object* v___f_5975_; lean_object* v___y_5977_; lean_object* v___y_5978_; lean_object* v___y_5979_; lean_object* v___y_5980_; lean_object* v___y_5981_; lean_object* v___y_5982_; 
v_options_5970_ = lean_ctor_get(v___y_5915_, 2);
v_a_5971_ = lean_ctor_get(v___x_5969_, 0);
lean_inc(v_a_5971_);
lean_dec_ref_known(v___x_5969_, 1);
v_inheritedTraceOptions_5972_ = lean_ctor_get(v___y_5915_, 13);
v_hasTrace_5973_ = lean_ctor_get_uint8(v_options_5970_, sizeof(void*)*1);
v___x_5974_ = lean_box(v___x_5962_);
lean_inc(v_a_5957_);
v___f_5975_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5975_, 0, v_a_5957_);
lean_closure_set(v___f_5975_, 1, v___x_5974_);
if (v_hasTrace_5973_ == 0)
{
lean_dec(v_cls_5910_);
v___y_5977_ = v___y_5911_;
v___y_5978_ = v___y_5912_;
v___y_5979_ = v___y_5913_;
v___y_5980_ = v___y_5914_;
v___y_5981_ = v___y_5915_;
v___y_5982_ = v___y_5916_;
goto v___jp_5976_;
}
else
{
lean_object* v___x_5986_; lean_object* v___x_5987_; uint8_t v___x_5988_; 
v___x_5986_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__3));
lean_inc(v_cls_5910_);
v___x_5987_ = l_Lean_Name_append(v___x_5986_, v_cls_5910_);
v___x_5988_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5972_, v_options_5970_, v___x_5987_);
lean_dec(v___x_5987_);
if (v___x_5988_ == 0)
{
lean_dec(v_cls_5910_);
v___y_5977_ = v___y_5911_;
v___y_5978_ = v___y_5912_;
v___y_5979_ = v___y_5913_;
v___y_5980_ = v___y_5914_;
v___y_5981_ = v___y_5915_;
v___y_5982_ = v___y_5916_;
goto v___jp_5976_;
}
else
{
lean_object* v___x_5989_; lean_object* v___x_5990_; lean_object* v___x_5991_; lean_object* v___x_5992_; lean_object* v___x_5993_; lean_object* v___x_5994_; lean_object* v___x_5995_; lean_object* v___x_5996_; lean_object* v___x_5997_; 
v___x_5989_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8);
lean_inc_ref(v___x_5968_);
v___x_5990_ = l_Lean_indentExpr(v___x_5968_);
v___x_5991_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5991_, 0, v___x_5989_);
lean_ctor_set(v___x_5991_, 1, v___x_5990_);
v___x_5992_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_5993_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5993_, 0, v___x_5991_);
lean_ctor_set(v___x_5993_, 1, v___x_5992_);
v___x_5994_ = l_Lean_Meta_Sym_Simp_Result_getResultExpr(v___x_5968_, v_a_5971_);
v___x_5995_ = l_Lean_indentExpr(v___x_5994_);
v___x_5996_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5996_, 0, v___x_5993_);
lean_ctor_set(v___x_5996_, 1, v___x_5995_);
v___x_5997_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(v_cls_5910_, v___x_5996_, v___y_5913_, v___y_5914_, v___y_5915_, v___y_5916_);
if (lean_obj_tag(v___x_5997_) == 0)
{
lean_dec_ref_known(v___x_5997_, 1);
v___y_5977_ = v___y_5911_;
v___y_5978_ = v___y_5912_;
v___y_5979_ = v___y_5913_;
v___y_5980_ = v___y_5914_;
v___y_5981_ = v___y_5915_;
v___y_5982_ = v___y_5916_;
goto v___jp_5976_;
}
else
{
lean_dec_ref(v___f_5975_);
lean_dec(v_a_5971_);
lean_dec_ref(v___x_5968_);
lean_dec(v_a_5957_);
return v___x_5997_;
}
}
}
v___jp_5976_:
{
if (lean_obj_tag(v_a_5971_) == 0)
{
lean_dec_ref_known(v_a_5971_, 0);
lean_dec(v_a_5957_);
v_e_5919_ = v___x_5968_;
v_onTrue_5920_ = v___f_5975_;
v___y_5921_ = v___y_5977_;
v___y_5922_ = v___y_5978_;
v___y_5923_ = v___y_5979_;
v___y_5924_ = v___y_5980_;
v___y_5925_ = v___y_5981_;
v___y_5926_ = v___y_5982_;
goto v___jp_5918_;
}
else
{
lean_object* v_e_x27_5983_; lean_object* v_proof_5984_; lean_object* v___x_5985_; 
lean_dec_ref(v___f_5975_);
lean_dec_ref(v___x_5968_);
v_e_x27_5983_ = lean_ctor_get(v_a_5971_, 0);
lean_inc_ref(v_e_x27_5983_);
v_proof_5984_ = lean_ctor_get(v_a_5971_, 1);
lean_inc_ref(v_proof_5984_);
lean_dec_ref_known(v_a_5971_, 2);
v___x_5985_ = lean_alloc_closure((void*)(l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___boxed), 9, 2);
lean_closure_set(v___x_5985_, 0, v_a_5957_);
lean_closure_set(v___x_5985_, 1, v_proof_5984_);
v_e_5919_ = v_e_x27_5983_;
v_onTrue_5920_ = v___x_5985_;
v___y_5921_ = v___y_5977_;
v___y_5922_ = v___y_5978_;
v___y_5923_ = v___y_5979_;
v___y_5924_ = v___y_5980_;
v___y_5925_ = v___y_5981_;
v___y_5926_ = v___y_5982_;
goto v___jp_5918_;
}
}
}
else
{
lean_object* v_a_5998_; lean_object* v___x_6000_; uint8_t v_isShared_6001_; uint8_t v_isSharedCheck_6005_; 
lean_dec_ref(v___x_5968_);
lean_dec(v_a_5957_);
lean_dec(v_cls_5910_);
v_a_5998_ = lean_ctor_get(v___x_5969_, 0);
v_isSharedCheck_6005_ = !lean_is_exclusive(v___x_5969_);
if (v_isSharedCheck_6005_ == 0)
{
v___x_6000_ = v___x_5969_;
v_isShared_6001_ = v_isSharedCheck_6005_;
goto v_resetjp_5999_;
}
else
{
lean_inc(v_a_5998_);
lean_dec(v___x_5969_);
v___x_6000_ = lean_box(0);
v_isShared_6001_ = v_isSharedCheck_6005_;
goto v_resetjp_5999_;
}
v_resetjp_5999_:
{
lean_object* v___x_6003_; 
if (v_isShared_6001_ == 0)
{
v___x_6003_ = v___x_6000_;
goto v_reusejp_6002_;
}
else
{
lean_object* v_reuseFailAlloc_6004_; 
v_reuseFailAlloc_6004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6004_, 0, v_a_5998_);
v___x_6003_ = v_reuseFailAlloc_6004_;
goto v_reusejp_6002_;
}
v_reusejp_6002_:
{
return v___x_6003_;
}
}
}
}
}
else
{
lean_object* v_a_6006_; lean_object* v___x_6008_; uint8_t v_isShared_6009_; uint8_t v_isSharedCheck_6013_; 
lean_dec(v_a_5957_);
lean_dec(v_cls_5910_);
lean_dec_ref(v___x_5909_);
v_a_6006_ = lean_ctor_get(v___x_5958_, 0);
v_isSharedCheck_6013_ = !lean_is_exclusive(v___x_5958_);
if (v_isSharedCheck_6013_ == 0)
{
v___x_6008_ = v___x_5958_;
v_isShared_6009_ = v_isSharedCheck_6013_;
goto v_resetjp_6007_;
}
else
{
lean_inc(v_a_6006_);
lean_dec(v___x_5958_);
v___x_6008_ = lean_box(0);
v_isShared_6009_ = v_isSharedCheck_6013_;
goto v_resetjp_6007_;
}
v_resetjp_6007_:
{
lean_object* v___x_6011_; 
if (v_isShared_6009_ == 0)
{
v___x_6011_ = v___x_6008_;
goto v_reusejp_6010_;
}
else
{
lean_object* v_reuseFailAlloc_6012_; 
v_reuseFailAlloc_6012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6012_, 0, v_a_6006_);
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
else
{
lean_object* v_a_6014_; lean_object* v___x_6016_; uint8_t v_isShared_6017_; uint8_t v_isSharedCheck_6021_; 
lean_dec(v_cls_5910_);
lean_dec_ref(v___x_5909_);
v_a_6014_ = lean_ctor_get(v___x_5956_, 0);
v_isSharedCheck_6021_ = !lean_is_exclusive(v___x_5956_);
if (v_isSharedCheck_6021_ == 0)
{
v___x_6016_ = v___x_5956_;
v_isShared_6017_ = v_isSharedCheck_6021_;
goto v_resetjp_6015_;
}
else
{
lean_inc(v_a_6014_);
lean_dec(v___x_5956_);
v___x_6016_ = lean_box(0);
v_isShared_6017_ = v_isSharedCheck_6021_;
goto v_resetjp_6015_;
}
v_resetjp_6015_:
{
lean_object* v___x_6019_; 
if (v_isShared_6017_ == 0)
{
v___x_6019_ = v___x_6016_;
goto v_reusejp_6018_;
}
else
{
lean_object* v_reuseFailAlloc_6020_; 
v_reuseFailAlloc_6020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6020_, 0, v_a_6014_);
v___x_6019_ = v_reuseFailAlloc_6020_;
goto v_reusejp_6018_;
}
v_reusejp_6018_:
{
return v___x_6019_;
}
}
}
v___jp_5918_:
{
lean_object* v___x_5927_; 
v___x_5927_ = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(v_e_5919_, v___y_5921_);
if (lean_obj_tag(v___x_5927_) == 0)
{
lean_object* v_a_5928_; uint8_t v___x_5929_; 
v_a_5928_ = lean_ctor_get(v___x_5927_, 0);
lean_inc(v_a_5928_);
lean_dec_ref_known(v___x_5927_, 1);
v___x_5929_ = lean_unbox(v_a_5928_);
lean_dec(v_a_5928_);
if (v___x_5929_ == 0)
{
lean_object* v___x_5930_; 
lean_dec_ref(v_onTrue_5920_);
v___x_5930_ = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(v_e_5919_, v___y_5921_);
if (lean_obj_tag(v___x_5930_) == 0)
{
lean_object* v_a_5931_; uint8_t v___x_5932_; 
v_a_5931_ = lean_ctor_get(v___x_5930_, 0);
lean_inc(v_a_5931_);
lean_dec_ref_known(v___x_5930_, 1);
v___x_5932_ = lean_unbox(v_a_5931_);
lean_dec(v_a_5931_);
if (v___x_5932_ == 0)
{
lean_object* v___x_5933_; lean_object* v___x_5934_; lean_object* v___x_5935_; lean_object* v___x_5936_; 
v___x_5933_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1);
v___x_5934_ = l_Lean_indentExpr(v_e_5919_);
v___x_5935_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5935_, 0, v___x_5933_);
lean_ctor_set(v___x_5935_, 1, v___x_5934_);
v___x_5936_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_5935_, v___y_5923_, v___y_5924_, v___y_5925_, v___y_5926_);
return v___x_5936_;
}
else
{
lean_object* v___x_5937_; lean_object* v___x_5938_; 
lean_dec_ref(v_e_5919_);
v___x_5937_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3);
v___x_5938_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_5937_, v___y_5923_, v___y_5924_, v___y_5925_, v___y_5926_);
return v___x_5938_;
}
}
else
{
lean_object* v_a_5939_; lean_object* v___x_5941_; uint8_t v_isShared_5942_; uint8_t v_isSharedCheck_5946_; 
lean_dec_ref(v_e_5919_);
v_a_5939_ = lean_ctor_get(v___x_5930_, 0);
v_isSharedCheck_5946_ = !lean_is_exclusive(v___x_5930_);
if (v_isSharedCheck_5946_ == 0)
{
v___x_5941_ = v___x_5930_;
v_isShared_5942_ = v_isSharedCheck_5946_;
goto v_resetjp_5940_;
}
else
{
lean_inc(v_a_5939_);
lean_dec(v___x_5930_);
v___x_5941_ = lean_box(0);
v_isShared_5942_ = v_isSharedCheck_5946_;
goto v_resetjp_5940_;
}
v_resetjp_5940_:
{
lean_object* v___x_5944_; 
if (v_isShared_5942_ == 0)
{
v___x_5944_ = v___x_5941_;
goto v_reusejp_5943_;
}
else
{
lean_object* v_reuseFailAlloc_5945_; 
v_reuseFailAlloc_5945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5945_, 0, v_a_5939_);
v___x_5944_ = v_reuseFailAlloc_5945_;
goto v_reusejp_5943_;
}
v_reusejp_5943_:
{
return v___x_5944_;
}
}
}
}
else
{
lean_object* v___x_5947_; 
lean_dec_ref(v_e_5919_);
lean_inc(v___y_5926_);
lean_inc_ref(v___y_5925_);
lean_inc(v___y_5924_);
lean_inc_ref(v___y_5923_);
lean_inc(v___y_5922_);
lean_inc_ref(v___y_5921_);
v___x_5947_ = lean_apply_7(v_onTrue_5920_, v___y_5921_, v___y_5922_, v___y_5923_, v___y_5924_, v___y_5925_, v___y_5926_, lean_box(0));
return v___x_5947_;
}
}
else
{
lean_object* v_a_5948_; lean_object* v___x_5950_; uint8_t v_isShared_5951_; uint8_t v_isSharedCheck_5955_; 
lean_dec_ref(v_onTrue_5920_);
lean_dec_ref(v_e_5919_);
v_a_5948_ = lean_ctor_get(v___x_5927_, 0);
v_isSharedCheck_5955_ = !lean_is_exclusive(v___x_5927_);
if (v_isSharedCheck_5955_ == 0)
{
v___x_5950_ = v___x_5927_;
v_isShared_5951_ = v_isSharedCheck_5955_;
goto v_resetjp_5949_;
}
else
{
lean_inc(v_a_5948_);
lean_dec(v___x_5927_);
v___x_5950_ = lean_box(0);
v_isShared_5951_ = v_isSharedCheck_5955_;
goto v_resetjp_5949_;
}
v_resetjp_5949_:
{
lean_object* v___x_5953_; 
if (v_isShared_5951_ == 0)
{
v___x_5953_ = v___x_5950_;
goto v_reusejp_5952_;
}
else
{
lean_object* v_reuseFailAlloc_5954_; 
v_reuseFailAlloc_5954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5954_, 0, v_a_5948_);
v___x_5953_ = v_reuseFailAlloc_5954_;
goto v_reusejp_5952_;
}
v_reusejp_5952_:
{
return v___x_5953_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___boxed(lean_object* v_m_6022_, lean_object* v___x_6023_, lean_object* v_cls_6024_, lean_object* v___y_6025_, lean_object* v___y_6026_, lean_object* v___y_6027_, lean_object* v___y_6028_, lean_object* v___y_6029_, lean_object* v___y_6030_, lean_object* v___y_6031_){
_start:
{
lean_object* v_res_6032_; 
v_res_6032_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1(v_m_6022_, v___x_6023_, v_cls_6024_, v___y_6025_, v___y_6026_, v___y_6027_, v___y_6028_, v___y_6029_, v___y_6030_);
lean_dec(v___y_6030_);
lean_dec_ref(v___y_6029_);
lean_dec(v___y_6028_);
lean_dec_ref(v___y_6027_);
lean_dec(v___y_6026_);
lean_dec_ref(v___y_6025_);
return v_res_6032_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__1(void){
_start:
{
lean_object* v___x_6034_; lean_object* v___x_6035_; 
v___x_6034_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__0));
v___x_6035_ = l_Lean_stringToMessageData(v___x_6034_);
return v___x_6035_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__3(void){
_start:
{
lean_object* v___x_6037_; lean_object* v___x_6038_; 
v___x_6037_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__2));
v___x_6038_ = l_Lean_stringToMessageData(v___x_6037_);
return v___x_6038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2(lean_object* v_x_6039_, lean_object* v___y_6040_, lean_object* v___y_6041_, lean_object* v___y_6042_, lean_object* v___y_6043_){
_start:
{
if (lean_obj_tag(v_x_6039_) == 0)
{
lean_object* v_a_6045_; lean_object* v___x_6047_; uint8_t v_isShared_6048_; uint8_t v_isSharedCheck_6055_; 
v_a_6045_ = lean_ctor_get(v_x_6039_, 0);
v_isSharedCheck_6055_ = !lean_is_exclusive(v_x_6039_);
if (v_isSharedCheck_6055_ == 0)
{
v___x_6047_ = v_x_6039_;
v_isShared_6048_ = v_isSharedCheck_6055_;
goto v_resetjp_6046_;
}
else
{
lean_inc(v_a_6045_);
lean_dec(v_x_6039_);
v___x_6047_ = lean_box(0);
v_isShared_6048_ = v_isSharedCheck_6055_;
goto v_resetjp_6046_;
}
v_resetjp_6046_:
{
lean_object* v___x_6049_; lean_object* v___x_6050_; lean_object* v___x_6051_; lean_object* v___x_6053_; 
v___x_6049_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__1);
v___x_6050_ = l_Lean_Exception_toMessageData(v_a_6045_);
v___x_6051_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6051_, 0, v___x_6049_);
lean_ctor_set(v___x_6051_, 1, v___x_6050_);
if (v_isShared_6048_ == 0)
{
lean_ctor_set(v___x_6047_, 0, v___x_6051_);
v___x_6053_ = v___x_6047_;
goto v_reusejp_6052_;
}
else
{
lean_object* v_reuseFailAlloc_6054_; 
v_reuseFailAlloc_6054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6054_, 0, v___x_6051_);
v___x_6053_ = v_reuseFailAlloc_6054_;
goto v_reusejp_6052_;
}
v_reusejp_6052_:
{
return v___x_6053_;
}
}
}
else
{
lean_object* v___x_6057_; uint8_t v_isShared_6058_; uint8_t v_isSharedCheck_6063_; 
v_isSharedCheck_6063_ = !lean_is_exclusive(v_x_6039_);
if (v_isSharedCheck_6063_ == 0)
{
lean_object* v_unused_6064_; 
v_unused_6064_ = lean_ctor_get(v_x_6039_, 0);
lean_dec(v_unused_6064_);
v___x_6057_ = v_x_6039_;
v_isShared_6058_ = v_isSharedCheck_6063_;
goto v_resetjp_6056_;
}
else
{
lean_dec(v_x_6039_);
v___x_6057_ = lean_box(0);
v_isShared_6058_ = v_isSharedCheck_6063_;
goto v_resetjp_6056_;
}
v_resetjp_6056_:
{
lean_object* v___x_6059_; lean_object* v___x_6061_; 
v___x_6059_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__3, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__3);
if (v_isShared_6058_ == 0)
{
lean_ctor_set_tag(v___x_6057_, 0);
lean_ctor_set(v___x_6057_, 0, v___x_6059_);
v___x_6061_ = v___x_6057_;
goto v_reusejp_6060_;
}
else
{
lean_object* v_reuseFailAlloc_6062_; 
v_reuseFailAlloc_6062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6062_, 0, v___x_6059_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___boxed(lean_object* v_x_6065_, lean_object* v___y_6066_, lean_object* v___y_6067_, lean_object* v___y_6068_, lean_object* v___y_6069_, lean_object* v___y_6070_){
_start:
{
lean_object* v_res_6071_; 
v_res_6071_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2(v_x_6065_, v___y_6066_, v___y_6067_, v___y_6068_, v___y_6069_);
lean_dec(v___y_6069_);
lean_dec_ref(v___y_6068_);
lean_dec(v___y_6067_);
lean_dec_ref(v___y_6066_);
return v_res_6071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__3(lean_object* v_a_6072_, uint8_t v_hasTrace_6073_, lean_object* v___y_6074_, lean_object* v___y_6075_, lean_object* v___y_6076_, lean_object* v___y_6077_, lean_object* v___y_6078_, lean_object* v___y_6079_){
_start:
{
lean_object* v___x_6081_; 
v___x_6081_ = l_Lean_MVarId_refl(v_a_6072_, v_hasTrace_6073_, v___y_6076_, v___y_6077_, v___y_6078_, v___y_6079_);
return v___x_6081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__3___boxed(lean_object* v_a_6082_, lean_object* v_hasTrace_6083_, lean_object* v___y_6084_, lean_object* v___y_6085_, lean_object* v___y_6086_, lean_object* v___y_6087_, lean_object* v___y_6088_, lean_object* v___y_6089_, lean_object* v___y_6090_){
_start:
{
uint8_t v_hasTrace_boxed_6091_; lean_object* v_res_6092_; 
v_hasTrace_boxed_6091_ = lean_unbox(v_hasTrace_6083_);
v_res_6092_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__3(v_a_6082_, v_hasTrace_boxed_6091_, v___y_6084_, v___y_6085_, v___y_6086_, v___y_6087_, v___y_6088_, v___y_6089_);
lean_dec(v___y_6089_);
lean_dec_ref(v___y_6088_);
lean_dec(v___y_6087_);
lean_dec_ref(v___y_6086_);
lean_dec(v___y_6085_);
lean_dec_ref(v___y_6084_);
return v_res_6092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__4(lean_object* v_m_6093_, lean_object* v___x_6094_, uint8_t v_hasTrace_6095_, lean_object* v_cls_6096_, lean_object* v___y_6097_, lean_object* v___y_6098_, lean_object* v___y_6099_, lean_object* v___y_6100_, lean_object* v___y_6101_, lean_object* v___y_6102_){
_start:
{
lean_object* v_e_6105_; lean_object* v_onTrue_6106_; lean_object* v___y_6107_; lean_object* v___y_6108_; lean_object* v___y_6109_; lean_object* v___y_6110_; lean_object* v___y_6111_; lean_object* v___y_6112_; lean_object* v___x_6142_; 
v___x_6142_ = l_Lean_Meta_Sym_preprocessMVar(v_m_6093_, v___y_6097_, v___y_6098_, v___y_6099_, v___y_6100_, v___y_6101_, v___y_6102_);
if (lean_obj_tag(v___x_6142_) == 0)
{
lean_object* v_a_6143_; lean_object* v___x_6144_; 
v_a_6143_ = lean_ctor_get(v___x_6142_, 0);
lean_inc_n(v_a_6143_, 2);
lean_dec_ref_known(v___x_6142_, 1);
v___x_6144_ = l_Lean_MVarId_getType(v_a_6143_, v___y_6099_, v___y_6100_, v___y_6101_, v___y_6102_);
if (lean_obj_tag(v___x_6144_) == 0)
{
lean_object* v_a_6145_; lean_object* v___x_6146_; lean_object* v___x_6147_; uint8_t v___x_6148_; 
v_a_6145_ = lean_ctor_get(v___x_6144_, 0);
lean_inc(v_a_6145_);
lean_dec_ref_known(v___x_6144_, 1);
v___x_6146_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__4));
v___x_6147_ = lean_unsigned_to_nat(3u);
v___x_6148_ = l_Lean_Expr_isAppOfArity(v_a_6145_, v___x_6146_, v___x_6147_);
if (v___x_6148_ == 0)
{
lean_object* v___x_6149_; lean_object* v___x_6150_; lean_object* v___x_6151_; lean_object* v___x_6152_; 
lean_dec(v_a_6143_);
lean_dec(v_cls_6096_);
lean_dec_ref(v___x_6094_);
v___x_6149_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6);
v___x_6150_ = l_Lean_indentExpr(v_a_6145_);
v___x_6151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6151_, 0, v___x_6149_);
lean_ctor_set(v___x_6151_, 1, v___x_6150_);
v___x_6152_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_6151_, v___y_6099_, v___y_6100_, v___y_6101_, v___y_6102_);
return v___x_6152_;
}
else
{
lean_object* v___x_6153_; lean_object* v___x_6154_; lean_object* v___x_6155_; 
v___x_6153_ = l_Lean_Expr_appFn_x21(v_a_6145_);
lean_dec(v_a_6145_);
v___x_6154_ = l_Lean_Expr_appArg_x21(v___x_6153_);
lean_dec_ref(v___x_6153_);
lean_inc_ref(v___x_6154_);
v___x_6155_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_6154_, v___x_6094_, v___y_6097_, v___y_6098_, v___y_6099_, v___y_6100_, v___y_6101_, v___y_6102_);
if (lean_obj_tag(v___x_6155_) == 0)
{
lean_object* v_options_6156_; lean_object* v_a_6157_; lean_object* v_inheritedTraceOptions_6158_; uint8_t v_hasTrace_6159_; lean_object* v___x_6160_; lean_object* v___f_6161_; lean_object* v___y_6163_; lean_object* v___y_6164_; lean_object* v___y_6165_; lean_object* v___y_6166_; lean_object* v___y_6167_; lean_object* v___y_6168_; 
v_options_6156_ = lean_ctor_get(v___y_6101_, 2);
v_a_6157_ = lean_ctor_get(v___x_6155_, 0);
lean_inc(v_a_6157_);
lean_dec_ref_known(v___x_6155_, 1);
v_inheritedTraceOptions_6158_ = lean_ctor_get(v___y_6101_, 13);
v_hasTrace_6159_ = lean_ctor_get_uint8(v_options_6156_, sizeof(void*)*1);
v___x_6160_ = lean_box(v_hasTrace_6095_);
lean_inc(v_a_6143_);
v___f_6161_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__3___boxed), 9, 2);
lean_closure_set(v___f_6161_, 0, v_a_6143_);
lean_closure_set(v___f_6161_, 1, v___x_6160_);
if (v_hasTrace_6159_ == 0)
{
lean_dec(v_cls_6096_);
v___y_6163_ = v___y_6097_;
v___y_6164_ = v___y_6098_;
v___y_6165_ = v___y_6099_;
v___y_6166_ = v___y_6100_;
v___y_6167_ = v___y_6101_;
v___y_6168_ = v___y_6102_;
goto v___jp_6162_;
}
else
{
lean_object* v___x_6172_; lean_object* v___x_6173_; uint8_t v___x_6174_; 
v___x_6172_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__3));
lean_inc(v_cls_6096_);
v___x_6173_ = l_Lean_Name_append(v___x_6172_, v_cls_6096_);
v___x_6174_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6158_, v_options_6156_, v___x_6173_);
lean_dec(v___x_6173_);
if (v___x_6174_ == 0)
{
lean_dec(v_cls_6096_);
v___y_6163_ = v___y_6097_;
v___y_6164_ = v___y_6098_;
v___y_6165_ = v___y_6099_;
v___y_6166_ = v___y_6100_;
v___y_6167_ = v___y_6101_;
v___y_6168_ = v___y_6102_;
goto v___jp_6162_;
}
else
{
lean_object* v___x_6175_; lean_object* v___x_6176_; lean_object* v___x_6177_; lean_object* v___x_6178_; lean_object* v___x_6179_; lean_object* v___x_6180_; lean_object* v___x_6181_; lean_object* v___x_6182_; lean_object* v___x_6183_; 
v___x_6175_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8);
lean_inc_ref(v___x_6154_);
v___x_6176_ = l_Lean_indentExpr(v___x_6154_);
v___x_6177_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6177_, 0, v___x_6175_);
lean_ctor_set(v___x_6177_, 1, v___x_6176_);
v___x_6178_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_6179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6179_, 0, v___x_6177_);
lean_ctor_set(v___x_6179_, 1, v___x_6178_);
v___x_6180_ = l_Lean_Meta_Sym_Simp_Result_getResultExpr(v___x_6154_, v_a_6157_);
v___x_6181_ = l_Lean_indentExpr(v___x_6180_);
v___x_6182_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6182_, 0, v___x_6179_);
lean_ctor_set(v___x_6182_, 1, v___x_6181_);
v___x_6183_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(v_cls_6096_, v___x_6182_, v___y_6099_, v___y_6100_, v___y_6101_, v___y_6102_);
if (lean_obj_tag(v___x_6183_) == 0)
{
lean_dec_ref_known(v___x_6183_, 1);
v___y_6163_ = v___y_6097_;
v___y_6164_ = v___y_6098_;
v___y_6165_ = v___y_6099_;
v___y_6166_ = v___y_6100_;
v___y_6167_ = v___y_6101_;
v___y_6168_ = v___y_6102_;
goto v___jp_6162_;
}
else
{
lean_dec_ref(v___f_6161_);
lean_dec(v_a_6157_);
lean_dec_ref(v___x_6154_);
lean_dec(v_a_6143_);
return v___x_6183_;
}
}
}
v___jp_6162_:
{
if (lean_obj_tag(v_a_6157_) == 0)
{
lean_dec_ref_known(v_a_6157_, 0);
lean_dec(v_a_6143_);
v_e_6105_ = v___x_6154_;
v_onTrue_6106_ = v___f_6161_;
v___y_6107_ = v___y_6163_;
v___y_6108_ = v___y_6164_;
v___y_6109_ = v___y_6165_;
v___y_6110_ = v___y_6166_;
v___y_6111_ = v___y_6167_;
v___y_6112_ = v___y_6168_;
goto v___jp_6104_;
}
else
{
lean_object* v_e_x27_6169_; lean_object* v_proof_6170_; lean_object* v___x_6171_; 
lean_dec_ref(v___f_6161_);
lean_dec_ref(v___x_6154_);
v_e_x27_6169_ = lean_ctor_get(v_a_6157_, 0);
lean_inc_ref(v_e_x27_6169_);
v_proof_6170_ = lean_ctor_get(v_a_6157_, 1);
lean_inc_ref(v_proof_6170_);
lean_dec_ref_known(v_a_6157_, 2);
v___x_6171_ = lean_alloc_closure((void*)(l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___boxed), 9, 2);
lean_closure_set(v___x_6171_, 0, v_a_6143_);
lean_closure_set(v___x_6171_, 1, v_proof_6170_);
v_e_6105_ = v_e_x27_6169_;
v_onTrue_6106_ = v___x_6171_;
v___y_6107_ = v___y_6163_;
v___y_6108_ = v___y_6164_;
v___y_6109_ = v___y_6165_;
v___y_6110_ = v___y_6166_;
v___y_6111_ = v___y_6167_;
v___y_6112_ = v___y_6168_;
goto v___jp_6104_;
}
}
}
else
{
lean_object* v_a_6184_; lean_object* v___x_6186_; uint8_t v_isShared_6187_; uint8_t v_isSharedCheck_6191_; 
lean_dec_ref(v___x_6154_);
lean_dec(v_a_6143_);
lean_dec(v_cls_6096_);
v_a_6184_ = lean_ctor_get(v___x_6155_, 0);
v_isSharedCheck_6191_ = !lean_is_exclusive(v___x_6155_);
if (v_isSharedCheck_6191_ == 0)
{
v___x_6186_ = v___x_6155_;
v_isShared_6187_ = v_isSharedCheck_6191_;
goto v_resetjp_6185_;
}
else
{
lean_inc(v_a_6184_);
lean_dec(v___x_6155_);
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
else
{
lean_object* v_a_6192_; lean_object* v___x_6194_; uint8_t v_isShared_6195_; uint8_t v_isSharedCheck_6199_; 
lean_dec(v_a_6143_);
lean_dec(v_cls_6096_);
lean_dec_ref(v___x_6094_);
v_a_6192_ = lean_ctor_get(v___x_6144_, 0);
v_isSharedCheck_6199_ = !lean_is_exclusive(v___x_6144_);
if (v_isSharedCheck_6199_ == 0)
{
v___x_6194_ = v___x_6144_;
v_isShared_6195_ = v_isSharedCheck_6199_;
goto v_resetjp_6193_;
}
else
{
lean_inc(v_a_6192_);
lean_dec(v___x_6144_);
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
lean_object* v_a_6200_; lean_object* v___x_6202_; uint8_t v_isShared_6203_; uint8_t v_isSharedCheck_6207_; 
lean_dec(v_cls_6096_);
lean_dec_ref(v___x_6094_);
v_a_6200_ = lean_ctor_get(v___x_6142_, 0);
v_isSharedCheck_6207_ = !lean_is_exclusive(v___x_6142_);
if (v_isSharedCheck_6207_ == 0)
{
v___x_6202_ = v___x_6142_;
v_isShared_6203_ = v_isSharedCheck_6207_;
goto v_resetjp_6201_;
}
else
{
lean_inc(v_a_6200_);
lean_dec(v___x_6142_);
v___x_6202_ = lean_box(0);
v_isShared_6203_ = v_isSharedCheck_6207_;
goto v_resetjp_6201_;
}
v_resetjp_6201_:
{
lean_object* v___x_6205_; 
if (v_isShared_6203_ == 0)
{
v___x_6205_ = v___x_6202_;
goto v_reusejp_6204_;
}
else
{
lean_object* v_reuseFailAlloc_6206_; 
v_reuseFailAlloc_6206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6206_, 0, v_a_6200_);
v___x_6205_ = v_reuseFailAlloc_6206_;
goto v_reusejp_6204_;
}
v_reusejp_6204_:
{
return v___x_6205_;
}
}
}
v___jp_6104_:
{
lean_object* v___x_6113_; 
v___x_6113_ = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(v_e_6105_, v___y_6107_);
if (lean_obj_tag(v___x_6113_) == 0)
{
lean_object* v_a_6114_; uint8_t v___x_6115_; 
v_a_6114_ = lean_ctor_get(v___x_6113_, 0);
lean_inc(v_a_6114_);
lean_dec_ref_known(v___x_6113_, 1);
v___x_6115_ = lean_unbox(v_a_6114_);
lean_dec(v_a_6114_);
if (v___x_6115_ == 0)
{
lean_object* v___x_6116_; 
lean_dec_ref(v_onTrue_6106_);
v___x_6116_ = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(v_e_6105_, v___y_6107_);
if (lean_obj_tag(v___x_6116_) == 0)
{
lean_object* v_a_6117_; uint8_t v___x_6118_; 
v_a_6117_ = lean_ctor_get(v___x_6116_, 0);
lean_inc(v_a_6117_);
lean_dec_ref_known(v___x_6116_, 1);
v___x_6118_ = lean_unbox(v_a_6117_);
lean_dec(v_a_6117_);
if (v___x_6118_ == 0)
{
lean_object* v___x_6119_; lean_object* v___x_6120_; lean_object* v___x_6121_; lean_object* v___x_6122_; 
v___x_6119_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1);
v___x_6120_ = l_Lean_indentExpr(v_e_6105_);
v___x_6121_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6121_, 0, v___x_6119_);
lean_ctor_set(v___x_6121_, 1, v___x_6120_);
v___x_6122_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_6121_, v___y_6109_, v___y_6110_, v___y_6111_, v___y_6112_);
return v___x_6122_;
}
else
{
lean_object* v___x_6123_; lean_object* v___x_6124_; 
lean_dec_ref(v_e_6105_);
v___x_6123_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3);
v___x_6124_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_6123_, v___y_6109_, v___y_6110_, v___y_6111_, v___y_6112_);
return v___x_6124_;
}
}
else
{
lean_object* v_a_6125_; lean_object* v___x_6127_; uint8_t v_isShared_6128_; uint8_t v_isSharedCheck_6132_; 
lean_dec_ref(v_e_6105_);
v_a_6125_ = lean_ctor_get(v___x_6116_, 0);
v_isSharedCheck_6132_ = !lean_is_exclusive(v___x_6116_);
if (v_isSharedCheck_6132_ == 0)
{
v___x_6127_ = v___x_6116_;
v_isShared_6128_ = v_isSharedCheck_6132_;
goto v_resetjp_6126_;
}
else
{
lean_inc(v_a_6125_);
lean_dec(v___x_6116_);
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
else
{
lean_object* v___x_6133_; 
lean_dec_ref(v_e_6105_);
lean_inc(v___y_6112_);
lean_inc_ref(v___y_6111_);
lean_inc(v___y_6110_);
lean_inc_ref(v___y_6109_);
lean_inc(v___y_6108_);
lean_inc_ref(v___y_6107_);
v___x_6133_ = lean_apply_7(v_onTrue_6106_, v___y_6107_, v___y_6108_, v___y_6109_, v___y_6110_, v___y_6111_, v___y_6112_, lean_box(0));
return v___x_6133_;
}
}
else
{
lean_object* v_a_6134_; lean_object* v___x_6136_; uint8_t v_isShared_6137_; uint8_t v_isSharedCheck_6141_; 
lean_dec_ref(v_onTrue_6106_);
lean_dec_ref(v_e_6105_);
v_a_6134_ = lean_ctor_get(v___x_6113_, 0);
v_isSharedCheck_6141_ = !lean_is_exclusive(v___x_6113_);
if (v_isSharedCheck_6141_ == 0)
{
v___x_6136_ = v___x_6113_;
v_isShared_6137_ = v_isSharedCheck_6141_;
goto v_resetjp_6135_;
}
else
{
lean_inc(v_a_6134_);
lean_dec(v___x_6113_);
v___x_6136_ = lean_box(0);
v_isShared_6137_ = v_isSharedCheck_6141_;
goto v_resetjp_6135_;
}
v_resetjp_6135_:
{
lean_object* v___x_6139_; 
if (v_isShared_6137_ == 0)
{
v___x_6139_ = v___x_6136_;
goto v_reusejp_6138_;
}
else
{
lean_object* v_reuseFailAlloc_6140_; 
v_reuseFailAlloc_6140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6140_, 0, v_a_6134_);
v___x_6139_ = v_reuseFailAlloc_6140_;
goto v_reusejp_6138_;
}
v_reusejp_6138_:
{
return v___x_6139_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__4___boxed(lean_object* v_m_6208_, lean_object* v___x_6209_, lean_object* v_hasTrace_6210_, lean_object* v_cls_6211_, lean_object* v___y_6212_, lean_object* v___y_6213_, lean_object* v___y_6214_, lean_object* v___y_6215_, lean_object* v___y_6216_, lean_object* v___y_6217_, lean_object* v___y_6218_){
_start:
{
uint8_t v_hasTrace_boxed_6219_; lean_object* v_res_6220_; 
v_hasTrace_boxed_6219_ = lean_unbox(v_hasTrace_6210_);
v_res_6220_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__4(v_m_6208_, v___x_6209_, v_hasTrace_boxed_6219_, v_cls_6211_, v___y_6212_, v___y_6213_, v___y_6214_, v___y_6215_, v___y_6216_, v___y_6217_);
lean_dec(v___y_6217_);
lean_dec_ref(v___y_6216_);
lean_dec(v___y_6215_);
lean_dec_ref(v___y_6214_);
lean_dec(v___y_6213_);
lean_dec_ref(v___y_6212_);
return v_res_6220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__6(lean_object* v_m_6221_, lean_object* v___x_6222_, uint8_t v___x_6223_, lean_object* v_cls_6224_, lean_object* v___y_6225_, lean_object* v___y_6226_, lean_object* v___y_6227_, lean_object* v___y_6228_, lean_object* v___y_6229_, lean_object* v___y_6230_){
_start:
{
lean_object* v_e_6233_; lean_object* v_onTrue_6234_; lean_object* v___y_6235_; lean_object* v___y_6236_; lean_object* v___y_6237_; lean_object* v___y_6238_; lean_object* v___y_6239_; lean_object* v___y_6240_; lean_object* v___x_6270_; 
v___x_6270_ = l_Lean_Meta_Sym_preprocessMVar(v_m_6221_, v___y_6225_, v___y_6226_, v___y_6227_, v___y_6228_, v___y_6229_, v___y_6230_);
if (lean_obj_tag(v___x_6270_) == 0)
{
lean_object* v_a_6271_; lean_object* v___x_6272_; 
v_a_6271_ = lean_ctor_get(v___x_6270_, 0);
lean_inc_n(v_a_6271_, 2);
lean_dec_ref_known(v___x_6270_, 1);
v___x_6272_ = l_Lean_MVarId_getType(v_a_6271_, v___y_6227_, v___y_6228_, v___y_6229_, v___y_6230_);
if (lean_obj_tag(v___x_6272_) == 0)
{
lean_object* v_a_6273_; lean_object* v___x_6274_; lean_object* v___x_6275_; uint8_t v___x_6276_; 
v_a_6273_ = lean_ctor_get(v___x_6272_, 0);
lean_inc(v_a_6273_);
lean_dec_ref_known(v___x_6272_, 1);
v___x_6274_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__4));
v___x_6275_ = lean_unsigned_to_nat(3u);
v___x_6276_ = l_Lean_Expr_isAppOfArity(v_a_6273_, v___x_6274_, v___x_6275_);
if (v___x_6276_ == 0)
{
lean_object* v___x_6277_; lean_object* v___x_6278_; lean_object* v___x_6279_; lean_object* v___x_6280_; 
lean_dec(v_a_6271_);
lean_dec(v_cls_6224_);
lean_dec_ref(v___x_6222_);
v___x_6277_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6);
v___x_6278_ = l_Lean_indentExpr(v_a_6273_);
v___x_6279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6279_, 0, v___x_6277_);
lean_ctor_set(v___x_6279_, 1, v___x_6278_);
v___x_6280_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_6279_, v___y_6227_, v___y_6228_, v___y_6229_, v___y_6230_);
return v___x_6280_;
}
else
{
lean_object* v___x_6281_; lean_object* v___x_6282_; lean_object* v___x_6283_; 
v___x_6281_ = l_Lean_Expr_appFn_x21(v_a_6273_);
lean_dec(v_a_6273_);
v___x_6282_ = l_Lean_Expr_appArg_x21(v___x_6281_);
lean_dec_ref(v___x_6281_);
lean_inc_ref(v___x_6282_);
v___x_6283_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_6282_, v___x_6222_, v___y_6225_, v___y_6226_, v___y_6227_, v___y_6228_, v___y_6229_, v___y_6230_);
if (lean_obj_tag(v___x_6283_) == 0)
{
lean_object* v_options_6284_; lean_object* v_a_6285_; lean_object* v_inheritedTraceOptions_6286_; uint8_t v_hasTrace_6287_; lean_object* v___x_6288_; lean_object* v___f_6289_; lean_object* v___y_6291_; lean_object* v___y_6292_; lean_object* v___y_6293_; lean_object* v___y_6294_; lean_object* v___y_6295_; lean_object* v___y_6296_; 
v_options_6284_ = lean_ctor_get(v___y_6229_, 2);
v_a_6285_ = lean_ctor_get(v___x_6283_, 0);
lean_inc(v_a_6285_);
lean_dec_ref_known(v___x_6283_, 1);
v_inheritedTraceOptions_6286_ = lean_ctor_get(v___y_6229_, 13);
v_hasTrace_6287_ = lean_ctor_get_uint8(v_options_6284_, sizeof(void*)*1);
v___x_6288_ = lean_box(v___x_6223_);
lean_inc(v_a_6271_);
v___f_6289_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0___boxed), 9, 2);
lean_closure_set(v___f_6289_, 0, v_a_6271_);
lean_closure_set(v___f_6289_, 1, v___x_6288_);
if (v_hasTrace_6287_ == 0)
{
lean_dec(v_cls_6224_);
v___y_6291_ = v___y_6225_;
v___y_6292_ = v___y_6226_;
v___y_6293_ = v___y_6227_;
v___y_6294_ = v___y_6228_;
v___y_6295_ = v___y_6229_;
v___y_6296_ = v___y_6230_;
goto v___jp_6290_;
}
else
{
lean_object* v___x_6300_; lean_object* v___x_6301_; uint8_t v___x_6302_; 
v___x_6300_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__3));
lean_inc(v_cls_6224_);
v___x_6301_ = l_Lean_Name_append(v___x_6300_, v_cls_6224_);
v___x_6302_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6286_, v_options_6284_, v___x_6301_);
lean_dec(v___x_6301_);
if (v___x_6302_ == 0)
{
lean_dec(v_cls_6224_);
v___y_6291_ = v___y_6225_;
v___y_6292_ = v___y_6226_;
v___y_6293_ = v___y_6227_;
v___y_6294_ = v___y_6228_;
v___y_6295_ = v___y_6229_;
v___y_6296_ = v___y_6230_;
goto v___jp_6290_;
}
else
{
lean_object* v___x_6303_; lean_object* v___x_6304_; lean_object* v___x_6305_; lean_object* v___x_6306_; lean_object* v___x_6307_; lean_object* v___x_6308_; lean_object* v___x_6309_; lean_object* v___x_6310_; lean_object* v___x_6311_; 
v___x_6303_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8);
lean_inc_ref(v___x_6282_);
v___x_6304_ = l_Lean_indentExpr(v___x_6282_);
v___x_6305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6305_, 0, v___x_6303_);
lean_ctor_set(v___x_6305_, 1, v___x_6304_);
v___x_6306_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_6307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6307_, 0, v___x_6305_);
lean_ctor_set(v___x_6307_, 1, v___x_6306_);
v___x_6308_ = l_Lean_Meta_Sym_Simp_Result_getResultExpr(v___x_6282_, v_a_6285_);
v___x_6309_ = l_Lean_indentExpr(v___x_6308_);
v___x_6310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6310_, 0, v___x_6307_);
lean_ctor_set(v___x_6310_, 1, v___x_6309_);
v___x_6311_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(v_cls_6224_, v___x_6310_, v___y_6227_, v___y_6228_, v___y_6229_, v___y_6230_);
if (lean_obj_tag(v___x_6311_) == 0)
{
lean_dec_ref_known(v___x_6311_, 1);
v___y_6291_ = v___y_6225_;
v___y_6292_ = v___y_6226_;
v___y_6293_ = v___y_6227_;
v___y_6294_ = v___y_6228_;
v___y_6295_ = v___y_6229_;
v___y_6296_ = v___y_6230_;
goto v___jp_6290_;
}
else
{
lean_dec_ref(v___f_6289_);
lean_dec(v_a_6285_);
lean_dec_ref(v___x_6282_);
lean_dec(v_a_6271_);
return v___x_6311_;
}
}
}
v___jp_6290_:
{
if (lean_obj_tag(v_a_6285_) == 0)
{
lean_dec_ref_known(v_a_6285_, 0);
lean_dec(v_a_6271_);
v_e_6233_ = v___x_6282_;
v_onTrue_6234_ = v___f_6289_;
v___y_6235_ = v___y_6291_;
v___y_6236_ = v___y_6292_;
v___y_6237_ = v___y_6293_;
v___y_6238_ = v___y_6294_;
v___y_6239_ = v___y_6295_;
v___y_6240_ = v___y_6296_;
goto v___jp_6232_;
}
else
{
lean_object* v_e_x27_6297_; lean_object* v_proof_6298_; lean_object* v___x_6299_; 
lean_dec_ref(v___f_6289_);
lean_dec_ref(v___x_6282_);
v_e_x27_6297_ = lean_ctor_get(v_a_6285_, 0);
lean_inc_ref(v_e_x27_6297_);
v_proof_6298_ = lean_ctor_get(v_a_6285_, 1);
lean_inc_ref(v_proof_6298_);
lean_dec_ref_known(v_a_6285_, 2);
v___x_6299_ = lean_alloc_closure((void*)(l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___boxed), 9, 2);
lean_closure_set(v___x_6299_, 0, v_a_6271_);
lean_closure_set(v___x_6299_, 1, v_proof_6298_);
v_e_6233_ = v_e_x27_6297_;
v_onTrue_6234_ = v___x_6299_;
v___y_6235_ = v___y_6291_;
v___y_6236_ = v___y_6292_;
v___y_6237_ = v___y_6293_;
v___y_6238_ = v___y_6294_;
v___y_6239_ = v___y_6295_;
v___y_6240_ = v___y_6296_;
goto v___jp_6232_;
}
}
}
else
{
lean_object* v_a_6312_; lean_object* v___x_6314_; uint8_t v_isShared_6315_; uint8_t v_isSharedCheck_6319_; 
lean_dec_ref(v___x_6282_);
lean_dec(v_a_6271_);
lean_dec(v_cls_6224_);
v_a_6312_ = lean_ctor_get(v___x_6283_, 0);
v_isSharedCheck_6319_ = !lean_is_exclusive(v___x_6283_);
if (v_isSharedCheck_6319_ == 0)
{
v___x_6314_ = v___x_6283_;
v_isShared_6315_ = v_isSharedCheck_6319_;
goto v_resetjp_6313_;
}
else
{
lean_inc(v_a_6312_);
lean_dec(v___x_6283_);
v___x_6314_ = lean_box(0);
v_isShared_6315_ = v_isSharedCheck_6319_;
goto v_resetjp_6313_;
}
v_resetjp_6313_:
{
lean_object* v___x_6317_; 
if (v_isShared_6315_ == 0)
{
v___x_6317_ = v___x_6314_;
goto v_reusejp_6316_;
}
else
{
lean_object* v_reuseFailAlloc_6318_; 
v_reuseFailAlloc_6318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6318_, 0, v_a_6312_);
v___x_6317_ = v_reuseFailAlloc_6318_;
goto v_reusejp_6316_;
}
v_reusejp_6316_:
{
return v___x_6317_;
}
}
}
}
}
else
{
lean_object* v_a_6320_; lean_object* v___x_6322_; uint8_t v_isShared_6323_; uint8_t v_isSharedCheck_6327_; 
lean_dec(v_a_6271_);
lean_dec(v_cls_6224_);
lean_dec_ref(v___x_6222_);
v_a_6320_ = lean_ctor_get(v___x_6272_, 0);
v_isSharedCheck_6327_ = !lean_is_exclusive(v___x_6272_);
if (v_isSharedCheck_6327_ == 0)
{
v___x_6322_ = v___x_6272_;
v_isShared_6323_ = v_isSharedCheck_6327_;
goto v_resetjp_6321_;
}
else
{
lean_inc(v_a_6320_);
lean_dec(v___x_6272_);
v___x_6322_ = lean_box(0);
v_isShared_6323_ = v_isSharedCheck_6327_;
goto v_resetjp_6321_;
}
v_resetjp_6321_:
{
lean_object* v___x_6325_; 
if (v_isShared_6323_ == 0)
{
v___x_6325_ = v___x_6322_;
goto v_reusejp_6324_;
}
else
{
lean_object* v_reuseFailAlloc_6326_; 
v_reuseFailAlloc_6326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6326_, 0, v_a_6320_);
v___x_6325_ = v_reuseFailAlloc_6326_;
goto v_reusejp_6324_;
}
v_reusejp_6324_:
{
return v___x_6325_;
}
}
}
}
else
{
lean_object* v_a_6328_; lean_object* v___x_6330_; uint8_t v_isShared_6331_; uint8_t v_isSharedCheck_6335_; 
lean_dec(v_cls_6224_);
lean_dec_ref(v___x_6222_);
v_a_6328_ = lean_ctor_get(v___x_6270_, 0);
v_isSharedCheck_6335_ = !lean_is_exclusive(v___x_6270_);
if (v_isSharedCheck_6335_ == 0)
{
v___x_6330_ = v___x_6270_;
v_isShared_6331_ = v_isSharedCheck_6335_;
goto v_resetjp_6329_;
}
else
{
lean_inc(v_a_6328_);
lean_dec(v___x_6270_);
v___x_6330_ = lean_box(0);
v_isShared_6331_ = v_isSharedCheck_6335_;
goto v_resetjp_6329_;
}
v_resetjp_6329_:
{
lean_object* v___x_6333_; 
if (v_isShared_6331_ == 0)
{
v___x_6333_ = v___x_6330_;
goto v_reusejp_6332_;
}
else
{
lean_object* v_reuseFailAlloc_6334_; 
v_reuseFailAlloc_6334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6334_, 0, v_a_6328_);
v___x_6333_ = v_reuseFailAlloc_6334_;
goto v_reusejp_6332_;
}
v_reusejp_6332_:
{
return v___x_6333_;
}
}
}
v___jp_6232_:
{
lean_object* v___x_6241_; 
v___x_6241_ = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(v_e_6233_, v___y_6235_);
if (lean_obj_tag(v___x_6241_) == 0)
{
lean_object* v_a_6242_; uint8_t v___x_6243_; 
v_a_6242_ = lean_ctor_get(v___x_6241_, 0);
lean_inc(v_a_6242_);
lean_dec_ref_known(v___x_6241_, 1);
v___x_6243_ = lean_unbox(v_a_6242_);
lean_dec(v_a_6242_);
if (v___x_6243_ == 0)
{
lean_object* v___x_6244_; 
lean_dec_ref(v_onTrue_6234_);
v___x_6244_ = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(v_e_6233_, v___y_6235_);
if (lean_obj_tag(v___x_6244_) == 0)
{
lean_object* v_a_6245_; uint8_t v___x_6246_; 
v_a_6245_ = lean_ctor_get(v___x_6244_, 0);
lean_inc(v_a_6245_);
lean_dec_ref_known(v___x_6244_, 1);
v___x_6246_ = lean_unbox(v_a_6245_);
lean_dec(v_a_6245_);
if (v___x_6246_ == 0)
{
lean_object* v___x_6247_; lean_object* v___x_6248_; lean_object* v___x_6249_; lean_object* v___x_6250_; 
v___x_6247_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1);
v___x_6248_ = l_Lean_indentExpr(v_e_6233_);
v___x_6249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6249_, 0, v___x_6247_);
lean_ctor_set(v___x_6249_, 1, v___x_6248_);
v___x_6250_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_6249_, v___y_6237_, v___y_6238_, v___y_6239_, v___y_6240_);
return v___x_6250_;
}
else
{
lean_object* v___x_6251_; lean_object* v___x_6252_; 
lean_dec_ref(v_e_6233_);
v___x_6251_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3);
v___x_6252_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_6251_, v___y_6237_, v___y_6238_, v___y_6239_, v___y_6240_);
return v___x_6252_;
}
}
else
{
lean_object* v_a_6253_; lean_object* v___x_6255_; uint8_t v_isShared_6256_; uint8_t v_isSharedCheck_6260_; 
lean_dec_ref(v_e_6233_);
v_a_6253_ = lean_ctor_get(v___x_6244_, 0);
v_isSharedCheck_6260_ = !lean_is_exclusive(v___x_6244_);
if (v_isSharedCheck_6260_ == 0)
{
v___x_6255_ = v___x_6244_;
v_isShared_6256_ = v_isSharedCheck_6260_;
goto v_resetjp_6254_;
}
else
{
lean_inc(v_a_6253_);
lean_dec(v___x_6244_);
v___x_6255_ = lean_box(0);
v_isShared_6256_ = v_isSharedCheck_6260_;
goto v_resetjp_6254_;
}
v_resetjp_6254_:
{
lean_object* v___x_6258_; 
if (v_isShared_6256_ == 0)
{
v___x_6258_ = v___x_6255_;
goto v_reusejp_6257_;
}
else
{
lean_object* v_reuseFailAlloc_6259_; 
v_reuseFailAlloc_6259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6259_, 0, v_a_6253_);
v___x_6258_ = v_reuseFailAlloc_6259_;
goto v_reusejp_6257_;
}
v_reusejp_6257_:
{
return v___x_6258_;
}
}
}
}
else
{
lean_object* v___x_6261_; 
lean_dec_ref(v_e_6233_);
lean_inc(v___y_6240_);
lean_inc_ref(v___y_6239_);
lean_inc(v___y_6238_);
lean_inc_ref(v___y_6237_);
lean_inc(v___y_6236_);
lean_inc_ref(v___y_6235_);
v___x_6261_ = lean_apply_7(v_onTrue_6234_, v___y_6235_, v___y_6236_, v___y_6237_, v___y_6238_, v___y_6239_, v___y_6240_, lean_box(0));
return v___x_6261_;
}
}
else
{
lean_object* v_a_6262_; lean_object* v___x_6264_; uint8_t v_isShared_6265_; uint8_t v_isSharedCheck_6269_; 
lean_dec_ref(v_onTrue_6234_);
lean_dec_ref(v_e_6233_);
v_a_6262_ = lean_ctor_get(v___x_6241_, 0);
v_isSharedCheck_6269_ = !lean_is_exclusive(v___x_6241_);
if (v_isSharedCheck_6269_ == 0)
{
v___x_6264_ = v___x_6241_;
v_isShared_6265_ = v_isSharedCheck_6269_;
goto v_resetjp_6263_;
}
else
{
lean_inc(v_a_6262_);
lean_dec(v___x_6241_);
v___x_6264_ = lean_box(0);
v_isShared_6265_ = v_isSharedCheck_6269_;
goto v_resetjp_6263_;
}
v_resetjp_6263_:
{
lean_object* v___x_6267_; 
if (v_isShared_6265_ == 0)
{
v___x_6267_ = v___x_6264_;
goto v_reusejp_6266_;
}
else
{
lean_object* v_reuseFailAlloc_6268_; 
v_reuseFailAlloc_6268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6268_, 0, v_a_6262_);
v___x_6267_ = v_reuseFailAlloc_6268_;
goto v_reusejp_6266_;
}
v_reusejp_6266_:
{
return v___x_6267_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__6___boxed(lean_object* v_m_6336_, lean_object* v___x_6337_, lean_object* v___x_6338_, lean_object* v_cls_6339_, lean_object* v___y_6340_, lean_object* v___y_6341_, lean_object* v___y_6342_, lean_object* v___y_6343_, lean_object* v___y_6344_, lean_object* v___y_6345_, lean_object* v___y_6346_){
_start:
{
uint8_t v___x_25974__boxed_6347_; lean_object* v_res_6348_; 
v___x_25974__boxed_6347_ = lean_unbox(v___x_6338_);
v_res_6348_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__6(v_m_6336_, v___x_6337_, v___x_25974__boxed_6347_, v_cls_6339_, v___y_6340_, v___y_6341_, v___y_6342_, v___y_6343_, v___y_6344_, v___y_6345_);
lean_dec(v___y_6345_);
lean_dec_ref(v___y_6344_);
lean_dec(v___y_6343_);
lean_dec_ref(v___y_6342_);
lean_dec(v___y_6341_);
lean_dec_ref(v___y_6340_);
return v_res_6348_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2_spec__2(lean_object* v_e_6349_){
_start:
{
if (lean_obj_tag(v_e_6349_) == 0)
{
uint8_t v___x_6350_; 
v___x_6350_ = 2;
return v___x_6350_;
}
else
{
uint8_t v___x_6351_; 
v___x_6351_ = 0;
return v___x_6351_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2_spec__2___boxed(lean_object* v_e_6352_){
_start:
{
uint8_t v_res_6353_; lean_object* v_r_6354_; 
v_res_6353_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2_spec__2(v_e_6352_);
lean_dec_ref(v_e_6352_);
v_r_6354_ = lean_box(v_res_6353_);
return v_r_6354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2(lean_object* v_cls_6355_, uint8_t v_collapsed_6356_, lean_object* v_tag_6357_, lean_object* v_opts_6358_, uint8_t v_clsEnabled_6359_, lean_object* v_oldTraces_6360_, lean_object* v_msg_6361_, lean_object* v_resStartStop_6362_, lean_object* v___y_6363_, lean_object* v___y_6364_, lean_object* v___y_6365_, lean_object* v___y_6366_){
_start:
{
lean_object* v_fst_6368_; lean_object* v_snd_6369_; lean_object* v___y_6371_; lean_object* v___y_6372_; lean_object* v_data_6373_; lean_object* v_fst_6376_; lean_object* v_snd_6377_; lean_object* v___x_6378_; uint8_t v___x_6379_; lean_object* v___y_6381_; lean_object* v_a_6382_; uint8_t v___y_6397_; double v___y_6428_; 
v_fst_6368_ = lean_ctor_get(v_resStartStop_6362_, 0);
lean_inc(v_fst_6368_);
v_snd_6369_ = lean_ctor_get(v_resStartStop_6362_, 1);
lean_inc(v_snd_6369_);
lean_dec_ref(v_resStartStop_6362_);
v_fst_6376_ = lean_ctor_get(v_snd_6369_, 0);
lean_inc(v_fst_6376_);
v_snd_6377_ = lean_ctor_get(v_snd_6369_, 1);
lean_inc(v_snd_6377_);
lean_dec(v_snd_6369_);
v___x_6378_ = l_Lean_trace_profiler;
v___x_6379_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_6358_, v___x_6378_);
if (v___x_6379_ == 0)
{
v___y_6397_ = v___x_6379_;
goto v___jp_6396_;
}
else
{
lean_object* v___x_6433_; uint8_t v___x_6434_; 
v___x_6433_ = l_Lean_trace_profiler_useHeartbeats;
v___x_6434_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_6358_, v___x_6433_);
if (v___x_6434_ == 0)
{
lean_object* v___x_6435_; lean_object* v___x_6436_; double v___x_6437_; double v___x_6438_; double v___x_6439_; 
v___x_6435_ = l_Lean_trace_profiler_threshold;
v___x_6436_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_6358_, v___x_6435_);
v___x_6437_ = lean_float_of_nat(v___x_6436_);
v___x_6438_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2);
v___x_6439_ = lean_float_div(v___x_6437_, v___x_6438_);
v___y_6428_ = v___x_6439_;
goto v___jp_6427_;
}
else
{
lean_object* v___x_6440_; lean_object* v___x_6441_; double v___x_6442_; 
v___x_6440_ = l_Lean_trace_profiler_threshold;
v___x_6441_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_6358_, v___x_6440_);
v___x_6442_ = lean_float_of_nat(v___x_6441_);
v___y_6428_ = v___x_6442_;
goto v___jp_6427_;
}
}
v___jp_6370_:
{
lean_object* v___x_6374_; 
lean_inc(v___y_6372_);
v___x_6374_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__1(v_oldTraces_6360_, v_data_6373_, v___y_6372_, v___y_6371_, v___y_6363_, v___y_6364_, v___y_6365_, v___y_6366_);
if (lean_obj_tag(v___x_6374_) == 0)
{
lean_object* v___x_6375_; 
lean_dec_ref_known(v___x_6374_, 1);
v___x_6375_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg(v_fst_6368_);
return v___x_6375_;
}
else
{
lean_dec(v_fst_6368_);
return v___x_6374_;
}
}
v___jp_6380_:
{
uint8_t v_result_6383_; lean_object* v___x_6384_; lean_object* v___x_6385_; double v___x_6386_; lean_object* v_data_6387_; 
v_result_6383_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2_spec__2(v_fst_6368_);
v___x_6384_ = lean_box(v_result_6383_);
v___x_6385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6385_, 0, v___x_6384_);
v___x_6386_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_6357_);
lean_inc_ref(v___x_6385_);
lean_inc(v_cls_6355_);
v_data_6387_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_6387_, 0, v_cls_6355_);
lean_ctor_set(v_data_6387_, 1, v___x_6385_);
lean_ctor_set(v_data_6387_, 2, v_tag_6357_);
lean_ctor_set_float(v_data_6387_, sizeof(void*)*3, v___x_6386_);
lean_ctor_set_float(v_data_6387_, sizeof(void*)*3 + 8, v___x_6386_);
lean_ctor_set_uint8(v_data_6387_, sizeof(void*)*3 + 16, v_collapsed_6356_);
if (v___x_6379_ == 0)
{
lean_dec_ref_known(v___x_6385_, 1);
lean_dec(v_snd_6377_);
lean_dec(v_fst_6376_);
lean_dec_ref(v_tag_6357_);
lean_dec(v_cls_6355_);
v___y_6371_ = v_a_6382_;
v___y_6372_ = v___y_6381_;
v_data_6373_ = v_data_6387_;
goto v___jp_6370_;
}
else
{
lean_object* v_data_6388_; double v___x_6389_; double v___x_6390_; 
lean_dec_ref_known(v_data_6387_, 3);
v_data_6388_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_6388_, 0, v_cls_6355_);
lean_ctor_set(v_data_6388_, 1, v___x_6385_);
lean_ctor_set(v_data_6388_, 2, v_tag_6357_);
v___x_6389_ = lean_unbox_float(v_fst_6376_);
lean_dec(v_fst_6376_);
lean_ctor_set_float(v_data_6388_, sizeof(void*)*3, v___x_6389_);
v___x_6390_ = lean_unbox_float(v_snd_6377_);
lean_dec(v_snd_6377_);
lean_ctor_set_float(v_data_6388_, sizeof(void*)*3 + 8, v___x_6390_);
lean_ctor_set_uint8(v_data_6388_, sizeof(void*)*3 + 16, v_collapsed_6356_);
v___y_6371_ = v_a_6382_;
v___y_6372_ = v___y_6381_;
v_data_6373_ = v_data_6388_;
goto v___jp_6370_;
}
}
v___jp_6391_:
{
lean_object* v_ref_6392_; lean_object* v___x_6393_; 
v_ref_6392_ = lean_ctor_get(v___y_6365_, 5);
lean_inc(v___y_6366_);
lean_inc_ref(v___y_6365_);
lean_inc(v___y_6364_);
lean_inc_ref(v___y_6363_);
lean_inc(v_fst_6368_);
v___x_6393_ = lean_apply_6(v_msg_6361_, v_fst_6368_, v___y_6363_, v___y_6364_, v___y_6365_, v___y_6366_, lean_box(0));
if (lean_obj_tag(v___x_6393_) == 0)
{
lean_object* v_a_6394_; 
v_a_6394_ = lean_ctor_get(v___x_6393_, 0);
lean_inc(v_a_6394_);
lean_dec_ref_known(v___x_6393_, 1);
v___y_6381_ = v_ref_6392_;
v_a_6382_ = v_a_6394_;
goto v___jp_6380_;
}
else
{
lean_object* v___x_6395_; 
lean_dec_ref_known(v___x_6393_, 1);
v___x_6395_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1);
v___y_6381_ = v_ref_6392_;
v_a_6382_ = v___x_6395_;
goto v___jp_6380_;
}
}
v___jp_6396_:
{
if (v_clsEnabled_6359_ == 0)
{
if (v___y_6397_ == 0)
{
lean_object* v___x_6398_; lean_object* v_traceState_6399_; lean_object* v_env_6400_; lean_object* v_nextMacroScope_6401_; lean_object* v_ngen_6402_; lean_object* v_auxDeclNGen_6403_; lean_object* v_cache_6404_; lean_object* v_messages_6405_; lean_object* v_infoState_6406_; lean_object* v_snapshotTasks_6407_; lean_object* v___x_6409_; uint8_t v_isShared_6410_; uint8_t v_isSharedCheck_6426_; 
lean_dec(v_snd_6377_);
lean_dec(v_fst_6376_);
lean_dec_ref(v_msg_6361_);
lean_dec_ref(v_tag_6357_);
lean_dec(v_cls_6355_);
v___x_6398_ = lean_st_ref_take(v___y_6366_);
v_traceState_6399_ = lean_ctor_get(v___x_6398_, 4);
v_env_6400_ = lean_ctor_get(v___x_6398_, 0);
v_nextMacroScope_6401_ = lean_ctor_get(v___x_6398_, 1);
v_ngen_6402_ = lean_ctor_get(v___x_6398_, 2);
v_auxDeclNGen_6403_ = lean_ctor_get(v___x_6398_, 3);
v_cache_6404_ = lean_ctor_get(v___x_6398_, 5);
v_messages_6405_ = lean_ctor_get(v___x_6398_, 6);
v_infoState_6406_ = lean_ctor_get(v___x_6398_, 7);
v_snapshotTasks_6407_ = lean_ctor_get(v___x_6398_, 8);
v_isSharedCheck_6426_ = !lean_is_exclusive(v___x_6398_);
if (v_isSharedCheck_6426_ == 0)
{
v___x_6409_ = v___x_6398_;
v_isShared_6410_ = v_isSharedCheck_6426_;
goto v_resetjp_6408_;
}
else
{
lean_inc(v_snapshotTasks_6407_);
lean_inc(v_infoState_6406_);
lean_inc(v_messages_6405_);
lean_inc(v_cache_6404_);
lean_inc(v_traceState_6399_);
lean_inc(v_auxDeclNGen_6403_);
lean_inc(v_ngen_6402_);
lean_inc(v_nextMacroScope_6401_);
lean_inc(v_env_6400_);
lean_dec(v___x_6398_);
v___x_6409_ = lean_box(0);
v_isShared_6410_ = v_isSharedCheck_6426_;
goto v_resetjp_6408_;
}
v_resetjp_6408_:
{
uint64_t v_tid_6411_; lean_object* v_traces_6412_; lean_object* v___x_6414_; uint8_t v_isShared_6415_; uint8_t v_isSharedCheck_6425_; 
v_tid_6411_ = lean_ctor_get_uint64(v_traceState_6399_, sizeof(void*)*1);
v_traces_6412_ = lean_ctor_get(v_traceState_6399_, 0);
v_isSharedCheck_6425_ = !lean_is_exclusive(v_traceState_6399_);
if (v_isSharedCheck_6425_ == 0)
{
v___x_6414_ = v_traceState_6399_;
v_isShared_6415_ = v_isSharedCheck_6425_;
goto v_resetjp_6413_;
}
else
{
lean_inc(v_traces_6412_);
lean_dec(v_traceState_6399_);
v___x_6414_ = lean_box(0);
v_isShared_6415_ = v_isSharedCheck_6425_;
goto v_resetjp_6413_;
}
v_resetjp_6413_:
{
lean_object* v___x_6416_; lean_object* v___x_6418_; 
v___x_6416_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_6360_, v_traces_6412_);
lean_dec_ref(v_traces_6412_);
if (v_isShared_6415_ == 0)
{
lean_ctor_set(v___x_6414_, 0, v___x_6416_);
v___x_6418_ = v___x_6414_;
goto v_reusejp_6417_;
}
else
{
lean_object* v_reuseFailAlloc_6424_; 
v_reuseFailAlloc_6424_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6424_, 0, v___x_6416_);
lean_ctor_set_uint64(v_reuseFailAlloc_6424_, sizeof(void*)*1, v_tid_6411_);
v___x_6418_ = v_reuseFailAlloc_6424_;
goto v_reusejp_6417_;
}
v_reusejp_6417_:
{
lean_object* v___x_6420_; 
if (v_isShared_6410_ == 0)
{
lean_ctor_set(v___x_6409_, 4, v___x_6418_);
v___x_6420_ = v___x_6409_;
goto v_reusejp_6419_;
}
else
{
lean_object* v_reuseFailAlloc_6423_; 
v_reuseFailAlloc_6423_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6423_, 0, v_env_6400_);
lean_ctor_set(v_reuseFailAlloc_6423_, 1, v_nextMacroScope_6401_);
lean_ctor_set(v_reuseFailAlloc_6423_, 2, v_ngen_6402_);
lean_ctor_set(v_reuseFailAlloc_6423_, 3, v_auxDeclNGen_6403_);
lean_ctor_set(v_reuseFailAlloc_6423_, 4, v___x_6418_);
lean_ctor_set(v_reuseFailAlloc_6423_, 5, v_cache_6404_);
lean_ctor_set(v_reuseFailAlloc_6423_, 6, v_messages_6405_);
lean_ctor_set(v_reuseFailAlloc_6423_, 7, v_infoState_6406_);
lean_ctor_set(v_reuseFailAlloc_6423_, 8, v_snapshotTasks_6407_);
v___x_6420_ = v_reuseFailAlloc_6423_;
goto v_reusejp_6419_;
}
v_reusejp_6419_:
{
lean_object* v___x_6421_; lean_object* v___x_6422_; 
v___x_6421_ = lean_st_ref_set(v___y_6366_, v___x_6420_);
v___x_6422_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg(v_fst_6368_);
return v___x_6422_;
}
}
}
}
}
else
{
goto v___jp_6391_;
}
}
else
{
goto v___jp_6391_;
}
}
v___jp_6427_:
{
double v___x_6429_; double v___x_6430_; double v___x_6431_; uint8_t v___x_6432_; 
v___x_6429_ = lean_unbox_float(v_snd_6377_);
v___x_6430_ = lean_unbox_float(v_fst_6376_);
v___x_6431_ = lean_float_sub(v___x_6429_, v___x_6430_);
v___x_6432_ = lean_float_decLt(v___y_6428_, v___x_6431_);
v___y_6397_ = v___x_6432_;
goto v___jp_6396_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2___boxed(lean_object* v_cls_6443_, lean_object* v_collapsed_6444_, lean_object* v_tag_6445_, lean_object* v_opts_6446_, lean_object* v_clsEnabled_6447_, lean_object* v_oldTraces_6448_, lean_object* v_msg_6449_, lean_object* v_resStartStop_6450_, lean_object* v___y_6451_, lean_object* v___y_6452_, lean_object* v___y_6453_, lean_object* v___y_6454_, lean_object* v___y_6455_){
_start:
{
uint8_t v_collapsed_boxed_6456_; uint8_t v_clsEnabled_boxed_6457_; lean_object* v_res_6458_; 
v_collapsed_boxed_6456_ = lean_unbox(v_collapsed_6444_);
v_clsEnabled_boxed_6457_ = lean_unbox(v_clsEnabled_6447_);
v_res_6458_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2(v_cls_6443_, v_collapsed_boxed_6456_, v_tag_6445_, v_opts_6446_, v_clsEnabled_boxed_6457_, v_oldTraces_6448_, v_msg_6449_, v_resStartStop_6450_, v___y_6451_, v___y_6452_, v___y_6453_, v___y_6454_);
lean_dec(v___y_6454_);
lean_dec_ref(v___y_6453_);
lean_dec(v___y_6452_);
lean_dec_ref(v___y_6451_);
lean_dec_ref(v_opts_6446_);
return v_res_6458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal(lean_object* v_m_6460_, lean_object* v_a_6461_, lean_object* v_a_6462_, lean_object* v_a_6463_, lean_object* v_a_6464_){
_start:
{
lean_object* v_options_6466_; lean_object* v_inheritedTraceOptions_6467_; uint8_t v_hasTrace_6468_; lean_object* v_cls_6469_; 
v_options_6466_ = lean_ctor_get(v_a_6463_, 2);
v_inheritedTraceOptions_6467_ = lean_ctor_get(v_a_6463_, 13);
v_hasTrace_6468_ = lean_ctor_get_uint8(v_options_6466_, sizeof(void*)*1);
v_cls_6469_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0));
if (v_hasTrace_6468_ == 0)
{
lean_object* v___x_6470_; lean_object* v___x_6471_; lean_object* v___x_6472_; lean_object* v___x_6473_; lean_object* v___f_6474_; lean_object* v___x_6475_; 
v___x_6470_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_6471_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_6466_, v___x_6470_);
v___x_6472_ = lean_unsigned_to_nat(2u);
v___x_6473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6473_, 0, v___x_6471_);
lean_ctor_set(v___x_6473_, 1, v___x_6472_);
v___f_6474_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___boxed), 10, 3);
lean_closure_set(v___f_6474_, 0, v_m_6460_);
lean_closure_set(v___f_6474_, 1, v___x_6473_);
lean_closure_set(v___f_6474_, 2, v_cls_6469_);
v___x_6475_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_6474_, v_a_6461_, v_a_6462_, v_a_6463_, v_a_6464_);
return v___x_6475_;
}
else
{
lean_object* v___f_6476_; lean_object* v___x_6477_; lean_object* v___x_6478_; uint8_t v___x_6479_; lean_object* v___y_6481_; lean_object* v___y_6482_; lean_object* v_a_6483_; lean_object* v___y_6496_; lean_object* v___y_6497_; lean_object* v_a_6498_; 
v___f_6476_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___closed__0));
v___x_6477_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__1));
v___x_6478_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1);
v___x_6479_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6467_, v_options_6466_, v___x_6478_);
if (v___x_6479_ == 0)
{
lean_object* v___x_6560_; uint8_t v___x_6561_; 
v___x_6560_ = l_Lean_trace_profiler;
v___x_6561_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_6466_, v___x_6560_);
if (v___x_6561_ == 0)
{
lean_object* v___x_6562_; lean_object* v___x_6563_; lean_object* v___x_6564_; lean_object* v___x_6565_; lean_object* v___x_6566_; lean_object* v___f_6567_; lean_object* v___x_6568_; 
v___x_6562_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_6563_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_6466_, v___x_6562_);
v___x_6564_ = lean_unsigned_to_nat(2u);
v___x_6565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6565_, 0, v___x_6563_);
lean_ctor_set(v___x_6565_, 1, v___x_6564_);
v___x_6566_ = lean_box(v_hasTrace_6468_);
v___f_6567_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__4___boxed), 11, 4);
lean_closure_set(v___f_6567_, 0, v_m_6460_);
lean_closure_set(v___f_6567_, 1, v___x_6565_);
lean_closure_set(v___f_6567_, 2, v___x_6566_);
lean_closure_set(v___f_6567_, 3, v_cls_6469_);
v___x_6568_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_6567_, v_a_6461_, v_a_6462_, v_a_6463_, v_a_6464_);
return v___x_6568_;
}
else
{
goto v___jp_6507_;
}
}
else
{
goto v___jp_6507_;
}
v___jp_6480_:
{
lean_object* v___x_6484_; double v___x_6485_; double v___x_6486_; double v___x_6487_; double v___x_6488_; double v___x_6489_; lean_object* v___x_6490_; lean_object* v___x_6491_; lean_object* v___x_6492_; lean_object* v___x_6493_; lean_object* v___x_6494_; 
v___x_6484_ = lean_io_mono_nanos_now();
v___x_6485_ = lean_float_of_nat(v___y_6482_);
v___x_6486_ = lean_float_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9);
v___x_6487_ = lean_float_div(v___x_6485_, v___x_6486_);
v___x_6488_ = lean_float_of_nat(v___x_6484_);
v___x_6489_ = lean_float_div(v___x_6488_, v___x_6486_);
v___x_6490_ = lean_box_float(v___x_6487_);
v___x_6491_ = lean_box_float(v___x_6489_);
v___x_6492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6492_, 0, v___x_6490_);
lean_ctor_set(v___x_6492_, 1, v___x_6491_);
v___x_6493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6493_, 0, v_a_6483_);
lean_ctor_set(v___x_6493_, 1, v___x_6492_);
v___x_6494_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2(v_cls_6469_, v_hasTrace_6468_, v___x_6477_, v_options_6466_, v___x_6479_, v___y_6481_, v___f_6476_, v___x_6493_, v_a_6461_, v_a_6462_, v_a_6463_, v_a_6464_);
return v___x_6494_;
}
v___jp_6495_:
{
lean_object* v___x_6499_; double v___x_6500_; double v___x_6501_; lean_object* v___x_6502_; lean_object* v___x_6503_; lean_object* v___x_6504_; lean_object* v___x_6505_; lean_object* v___x_6506_; 
v___x_6499_ = lean_io_get_num_heartbeats();
v___x_6500_ = lean_float_of_nat(v___y_6497_);
v___x_6501_ = lean_float_of_nat(v___x_6499_);
v___x_6502_ = lean_box_float(v___x_6500_);
v___x_6503_ = lean_box_float(v___x_6501_);
v___x_6504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6504_, 0, v___x_6502_);
lean_ctor_set(v___x_6504_, 1, v___x_6503_);
v___x_6505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6505_, 0, v_a_6498_);
lean_ctor_set(v___x_6505_, 1, v___x_6504_);
v___x_6506_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2(v_cls_6469_, v_hasTrace_6468_, v___x_6477_, v_options_6466_, v___x_6479_, v___y_6496_, v___f_6476_, v___x_6505_, v_a_6461_, v_a_6462_, v_a_6463_, v_a_6464_);
return v___x_6506_;
}
v___jp_6507_:
{
lean_object* v___x_6508_; lean_object* v_a_6509_; lean_object* v___x_6510_; uint8_t v___x_6511_; 
v___x_6508_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg(v_a_6464_);
v_a_6509_ = lean_ctor_get(v___x_6508_, 0);
lean_inc(v_a_6509_);
lean_dec_ref(v___x_6508_);
v___x_6510_ = l_Lean_trace_profiler_useHeartbeats;
v___x_6511_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_6466_, v___x_6510_);
if (v___x_6511_ == 0)
{
lean_object* v___x_6512_; lean_object* v___x_6513_; lean_object* v___x_6514_; lean_object* v___x_6515_; lean_object* v___x_6516_; lean_object* v___x_6517_; lean_object* v___f_6518_; lean_object* v___x_6519_; 
v___x_6512_ = lean_io_mono_nanos_now();
v___x_6513_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_6514_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_6466_, v___x_6513_);
v___x_6515_ = lean_unsigned_to_nat(2u);
v___x_6516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6516_, 0, v___x_6514_);
lean_ctor_set(v___x_6516_, 1, v___x_6515_);
v___x_6517_ = lean_box(v_hasTrace_6468_);
v___f_6518_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__4___boxed), 11, 4);
lean_closure_set(v___f_6518_, 0, v_m_6460_);
lean_closure_set(v___f_6518_, 1, v___x_6516_);
lean_closure_set(v___f_6518_, 2, v___x_6517_);
lean_closure_set(v___f_6518_, 3, v_cls_6469_);
v___x_6519_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_6518_, v_a_6461_, v_a_6462_, v_a_6463_, v_a_6464_);
if (lean_obj_tag(v___x_6519_) == 0)
{
lean_object* v_a_6520_; lean_object* v___x_6522_; uint8_t v_isShared_6523_; uint8_t v_isSharedCheck_6527_; 
v_a_6520_ = lean_ctor_get(v___x_6519_, 0);
v_isSharedCheck_6527_ = !lean_is_exclusive(v___x_6519_);
if (v_isSharedCheck_6527_ == 0)
{
v___x_6522_ = v___x_6519_;
v_isShared_6523_ = v_isSharedCheck_6527_;
goto v_resetjp_6521_;
}
else
{
lean_inc(v_a_6520_);
lean_dec(v___x_6519_);
v___x_6522_ = lean_box(0);
v_isShared_6523_ = v_isSharedCheck_6527_;
goto v_resetjp_6521_;
}
v_resetjp_6521_:
{
lean_object* v___x_6525_; 
if (v_isShared_6523_ == 0)
{
lean_ctor_set_tag(v___x_6522_, 1);
v___x_6525_ = v___x_6522_;
goto v_reusejp_6524_;
}
else
{
lean_object* v_reuseFailAlloc_6526_; 
v_reuseFailAlloc_6526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6526_, 0, v_a_6520_);
v___x_6525_ = v_reuseFailAlloc_6526_;
goto v_reusejp_6524_;
}
v_reusejp_6524_:
{
v___y_6481_ = v_a_6509_;
v___y_6482_ = v___x_6512_;
v_a_6483_ = v___x_6525_;
goto v___jp_6480_;
}
}
}
else
{
lean_object* v_a_6528_; lean_object* v___x_6530_; uint8_t v_isShared_6531_; uint8_t v_isSharedCheck_6535_; 
v_a_6528_ = lean_ctor_get(v___x_6519_, 0);
v_isSharedCheck_6535_ = !lean_is_exclusive(v___x_6519_);
if (v_isSharedCheck_6535_ == 0)
{
v___x_6530_ = v___x_6519_;
v_isShared_6531_ = v_isSharedCheck_6535_;
goto v_resetjp_6529_;
}
else
{
lean_inc(v_a_6528_);
lean_dec(v___x_6519_);
v___x_6530_ = lean_box(0);
v_isShared_6531_ = v_isSharedCheck_6535_;
goto v_resetjp_6529_;
}
v_resetjp_6529_:
{
lean_object* v___x_6533_; 
if (v_isShared_6531_ == 0)
{
lean_ctor_set_tag(v___x_6530_, 0);
v___x_6533_ = v___x_6530_;
goto v_reusejp_6532_;
}
else
{
lean_object* v_reuseFailAlloc_6534_; 
v_reuseFailAlloc_6534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6534_, 0, v_a_6528_);
v___x_6533_ = v_reuseFailAlloc_6534_;
goto v_reusejp_6532_;
}
v_reusejp_6532_:
{
v___y_6481_ = v_a_6509_;
v___y_6482_ = v___x_6512_;
v_a_6483_ = v___x_6533_;
goto v___jp_6480_;
}
}
}
}
else
{
lean_object* v___x_6536_; lean_object* v___x_6537_; lean_object* v___x_6538_; lean_object* v___x_6539_; lean_object* v___x_6540_; lean_object* v___x_6541_; lean_object* v___f_6542_; lean_object* v___x_6543_; 
v___x_6536_ = lean_io_get_num_heartbeats();
v___x_6537_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_6538_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_6466_, v___x_6537_);
v___x_6539_ = lean_unsigned_to_nat(2u);
v___x_6540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6540_, 0, v___x_6538_);
lean_ctor_set(v___x_6540_, 1, v___x_6539_);
v___x_6541_ = lean_box(v___x_6511_);
v___f_6542_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__6___boxed), 11, 4);
lean_closure_set(v___f_6542_, 0, v_m_6460_);
lean_closure_set(v___f_6542_, 1, v___x_6540_);
lean_closure_set(v___f_6542_, 2, v___x_6541_);
lean_closure_set(v___f_6542_, 3, v_cls_6469_);
v___x_6543_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_6542_, v_a_6461_, v_a_6462_, v_a_6463_, v_a_6464_);
if (lean_obj_tag(v___x_6543_) == 0)
{
lean_object* v_a_6544_; lean_object* v___x_6546_; uint8_t v_isShared_6547_; uint8_t v_isSharedCheck_6551_; 
v_a_6544_ = lean_ctor_get(v___x_6543_, 0);
v_isSharedCheck_6551_ = !lean_is_exclusive(v___x_6543_);
if (v_isSharedCheck_6551_ == 0)
{
v___x_6546_ = v___x_6543_;
v_isShared_6547_ = v_isSharedCheck_6551_;
goto v_resetjp_6545_;
}
else
{
lean_inc(v_a_6544_);
lean_dec(v___x_6543_);
v___x_6546_ = lean_box(0);
v_isShared_6547_ = v_isSharedCheck_6551_;
goto v_resetjp_6545_;
}
v_resetjp_6545_:
{
lean_object* v___x_6549_; 
if (v_isShared_6547_ == 0)
{
lean_ctor_set_tag(v___x_6546_, 1);
v___x_6549_ = v___x_6546_;
goto v_reusejp_6548_;
}
else
{
lean_object* v_reuseFailAlloc_6550_; 
v_reuseFailAlloc_6550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6550_, 0, v_a_6544_);
v___x_6549_ = v_reuseFailAlloc_6550_;
goto v_reusejp_6548_;
}
v_reusejp_6548_:
{
v___y_6496_ = v_a_6509_;
v___y_6497_ = v___x_6536_;
v_a_6498_ = v___x_6549_;
goto v___jp_6495_;
}
}
}
else
{
lean_object* v_a_6552_; lean_object* v___x_6554_; uint8_t v_isShared_6555_; uint8_t v_isSharedCheck_6559_; 
v_a_6552_ = lean_ctor_get(v___x_6543_, 0);
v_isSharedCheck_6559_ = !lean_is_exclusive(v___x_6543_);
if (v_isSharedCheck_6559_ == 0)
{
v___x_6554_ = v___x_6543_;
v_isShared_6555_ = v_isSharedCheck_6559_;
goto v_resetjp_6553_;
}
else
{
lean_inc(v_a_6552_);
lean_dec(v___x_6543_);
v___x_6554_ = lean_box(0);
v_isShared_6555_ = v_isSharedCheck_6559_;
goto v_resetjp_6553_;
}
v_resetjp_6553_:
{
lean_object* v___x_6557_; 
if (v_isShared_6555_ == 0)
{
lean_ctor_set_tag(v___x_6554_, 0);
v___x_6557_ = v___x_6554_;
goto v_reusejp_6556_;
}
else
{
lean_object* v_reuseFailAlloc_6558_; 
v_reuseFailAlloc_6558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6558_, 0, v_a_6552_);
v___x_6557_ = v_reuseFailAlloc_6558_;
goto v_reusejp_6556_;
}
v_reusejp_6556_:
{
v___y_6496_ = v_a_6509_;
v___y_6497_ = v___x_6536_;
v_a_6498_ = v___x_6557_;
goto v___jp_6495_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___boxed(lean_object* v_m_6569_, lean_object* v_a_6570_, lean_object* v_a_6571_, lean_object* v_a_6572_, lean_object* v_a_6573_, lean_object* v_a_6574_){
_start:
{
lean_object* v_res_6575_; 
v_res_6575_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal(v_m_6569_, v_a_6570_, v_a_6571_, v_a_6572_, v_a_6573_);
lean_dec(v_a_6573_);
lean_dec_ref(v_a_6572_);
lean_dec(v_a_6571_);
lean_dec_ref(v_a_6570_);
return v_res_6575_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0(lean_object* v_00_u03b1_6576_, lean_object* v_msg_6577_, lean_object* v___y_6578_, lean_object* v___y_6579_, lean_object* v___y_6580_, lean_object* v___y_6581_, lean_object* v___y_6582_, lean_object* v___y_6583_){
_start:
{
lean_object* v___x_6585_; 
v___x_6585_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v_msg_6577_, v___y_6580_, v___y_6581_, v___y_6582_, v___y_6583_);
return v___x_6585_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___boxed(lean_object* v_00_u03b1_6586_, lean_object* v_msg_6587_, lean_object* v___y_6588_, lean_object* v___y_6589_, lean_object* v___y_6590_, lean_object* v___y_6591_, lean_object* v___y_6592_, lean_object* v___y_6593_, lean_object* v___y_6594_){
_start:
{
lean_object* v_res_6595_; 
v_res_6595_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0(v_00_u03b1_6586_, v_msg_6587_, v___y_6588_, v___y_6589_, v___y_6590_, v___y_6591_, v___y_6592_, v___y_6593_);
lean_dec(v___y_6593_);
lean_dec_ref(v___y_6592_);
lean_dec(v___y_6591_);
lean_dec_ref(v___y_6590_);
lean_dec(v___y_6589_);
lean_dec_ref(v___y_6588_);
return v_res_6595_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1(lean_object* v_cls_6596_, lean_object* v_msg_6597_, lean_object* v___y_6598_, lean_object* v___y_6599_, lean_object* v___y_6600_, lean_object* v___y_6601_, lean_object* v___y_6602_, lean_object* v___y_6603_){
_start:
{
lean_object* v___x_6605_; 
v___x_6605_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(v_cls_6596_, v_msg_6597_, v___y_6600_, v___y_6601_, v___y_6602_, v___y_6603_);
return v___x_6605_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___boxed(lean_object* v_cls_6606_, lean_object* v_msg_6607_, lean_object* v___y_6608_, lean_object* v___y_6609_, lean_object* v___y_6610_, lean_object* v___y_6611_, lean_object* v___y_6612_, lean_object* v___y_6613_, lean_object* v___y_6614_){
_start:
{
lean_object* v_res_6615_; 
v_res_6615_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1(v_cls_6606_, v_msg_6607_, v___y_6608_, v___y_6609_, v___y_6610_, v___y_6611_, v___y_6612_, v___y_6613_);
lean_dec(v___y_6613_);
lean_dec_ref(v___y_6612_);
lean_dec(v___y_6611_);
lean_dec_ref(v___y_6610_);
lean_dec(v___y_6609_);
lean_dec_ref(v___y_6608_);
return v_res_6615_;
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

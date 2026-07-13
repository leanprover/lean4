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
lean_object* v___x_1699_; lean_object* v___x_149214__overap_1700_; lean_object* v___x_1701_; 
v___x_1699_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___closed__0);
v___x_149214__overap_1700_ = lean_panic_fn_borrowed(v___x_1699_, v_msg_1688_);
lean_inc(v___y_1697_);
lean_inc_ref(v___y_1696_);
lean_inc(v___y_1695_);
lean_inc_ref(v___y_1694_);
lean_inc(v___y_1693_);
lean_inc_ref(v___y_1692_);
lean_inc(v___y_1691_);
lean_inc_ref(v___y_1690_);
lean_inc(v___y_1689_);
v___x_1701_ = lean_apply_10(v___x_149214__overap_1700_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, lean_box(0));
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
uint8_t v___x_165986__boxed_1868_; lean_object* v_res_1869_; 
v___x_165986__boxed_1868_ = lean_unbox(v___x_1861_);
v_res_1869_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0(v___x_165986__boxed_1868_, v_e_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_);
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
lean_inc(v___y_2159_);
v___x_2161_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4___redArg(v_oldTraces_2142_, v_data_2160_, v___y_2159_, v___y_2158_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_);
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
v___y_2158_ = v_a_2177_;
v___y_2159_ = v___y_2176_;
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
v___y_2158_ = v_a_2177_;
v___y_2159_ = v___y_2176_;
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
uint8_t v___y_2290_; uint8_t v___y_2291_; lean_object* v___y_2292_; lean_object* v_a_2293_; lean_object* v___y_2297_; uint8_t v___y_2298_; lean_object* v_a_2299_; 
if (lean_obj_tag(v_e_2278_) == 11)
{
lean_object* v_typeName_2303_; lean_object* v_idx_2304_; lean_object* v_struct_2305_; lean_object* v_res_2307_; lean_object* v___y_2308_; lean_object* v___y_2309_; lean_object* v___y_2310_; lean_object* v___y_2311_; lean_object* v___y_2312_; lean_object* v___y_2313_; lean_object* v___y_2314_; lean_object* v___y_2315_; lean_object* v___y_2316_; lean_object* v_options_2551_; uint8_t v_hasTrace_2552_; 
v_typeName_2303_ = lean_ctor_get(v_e_2278_, 0);
v_idx_2304_ = lean_ctor_get(v_e_2278_, 1);
v_struct_2305_ = lean_ctor_get(v_e_2278_, 2);
v_options_2551_ = lean_ctor_get(v_a_2286_, 2);
v_hasTrace_2552_ = lean_ctor_get_uint8(v_options_2551_, sizeof(void*)*1);
if (v_hasTrace_2552_ == 0)
{
lean_object* v___x_2553_; 
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
v___x_2553_ = lean_sym_simp(v_struct_2305_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2553_) == 0)
{
lean_object* v_a_2554_; 
v_a_2554_ = lean_ctor_get(v___x_2553_, 0);
lean_inc(v_a_2554_);
lean_dec_ref_known(v___x_2553_, 1);
v_res_2307_ = v_a_2554_;
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
return v___x_2553_;
}
}
else
{
lean_object* v_inheritedTraceOptions_2555_; lean_object* v___f_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; uint8_t v___x_2560_; lean_object* v___y_2562_; lean_object* v___y_2563_; lean_object* v_a_2564_; lean_object* v___y_2577_; lean_object* v___y_2578_; lean_object* v_a_2579_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v_a_2584_; uint8_t v___y_2587_; lean_object* v___y_2588_; uint8_t v___y_2589_; lean_object* v___y_2590_; lean_object* v___y_2591_; lean_object* v_a_2592_; lean_object* v___y_2595_; lean_object* v___y_2596_; lean_object* v___y_2597_; uint8_t v___y_2601_; lean_object* v___y_2602_; uint8_t v___y_2603_; lean_object* v___y_2604_; lean_object* v___y_2605_; lean_object* v_a_2606_; lean_object* v___y_2609_; lean_object* v___y_2610_; lean_object* v_a_2611_; lean_object* v___y_2621_; lean_object* v___y_2622_; lean_object* v_a_2623_; lean_object* v___y_2626_; lean_object* v___y_2627_; lean_object* v_a_2628_; lean_object* v___y_2631_; uint8_t v___y_2632_; lean_object* v___y_2633_; uint8_t v___y_2634_; lean_object* v___y_2635_; lean_object* v_a_2636_; lean_object* v___y_2639_; lean_object* v___y_2640_; lean_object* v___y_2641_; lean_object* v___y_2645_; lean_object* v___y_2646_; uint8_t v___y_2647_; lean_object* v___y_2648_; lean_object* v_a_2649_; 
v_inheritedTraceOptions_2555_ = lean_ctor_get(v_a_2286_, 13);
lean_inc_ref(v_e_2278_);
lean_inc(v_idx_2304_);
lean_inc(v_typeName_2303_);
v___f_2556_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___boxed), 14, 3);
lean_closure_set(v___f_2556_, 0, v_typeName_2303_);
lean_closure_set(v___f_2556_, 1, v_idx_2304_);
lean_closure_set(v___f_2556_, 2, v_e_2278_);
v___x_2557_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2));
v___x_2558_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__1));
v___x_2559_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3);
v___x_2560_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2555_, v_options_2551_, v___x_2559_);
if (v___x_2560_ == 0)
{
lean_object* v___x_2860_; uint8_t v___x_2861_; 
v___x_2860_ = l_Lean_trace_profiler;
v___x_2861_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_2551_, v___x_2860_);
if (v___x_2861_ == 0)
{
lean_object* v___x_2862_; 
lean_dec_ref(v___f_2556_);
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
v___x_2862_ = lean_sym_simp(v_struct_2305_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2862_) == 0)
{
lean_object* v_a_2863_; 
v_a_2863_ = lean_ctor_get(v___x_2862_, 0);
lean_inc(v_a_2863_);
lean_dec_ref_known(v___x_2862_, 1);
v_res_2307_ = v_a_2863_;
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
return v___x_2862_;
}
}
else
{
goto v___jp_2652_;
}
}
else
{
goto v___jp_2652_;
}
v___jp_2561_:
{
lean_object* v___x_2565_; double v___x_2566_; double v___x_2567_; double v___x_2568_; double v___x_2569_; double v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
v___x_2565_ = lean_io_mono_nanos_now();
v___x_2566_ = lean_float_of_nat(v___y_2562_);
v___x_2567_ = lean_float_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9);
v___x_2568_ = lean_float_div(v___x_2566_, v___x_2567_);
v___x_2569_ = lean_float_of_nat(v___x_2565_);
v___x_2570_ = lean_float_div(v___x_2569_, v___x_2567_);
v___x_2571_ = lean_box_float(v___x_2568_);
v___x_2572_ = lean_box_float(v___x_2570_);
v___x_2573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2573_, 0, v___x_2571_);
lean_ctor_set(v___x_2573_, 1, v___x_2572_);
v___x_2574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2574_, 0, v_a_2564_);
lean_ctor_set(v___x_2574_, 1, v___x_2573_);
v___x_2575_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4(v___x_2557_, v_hasTrace_2552_, v___x_2558_, v_options_2551_, v___x_2560_, v___y_2563_, v___f_2556_, v___x_2574_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
return v___x_2575_;
}
v___jp_2576_:
{
lean_object* v___x_2580_; 
v___x_2580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2580_, 0, v_a_2579_);
v___y_2562_ = v___y_2577_;
v___y_2563_ = v___y_2578_;
v_a_2564_ = v___x_2580_;
goto v___jp_2561_;
}
v___jp_2581_:
{
lean_object* v___x_2585_; 
v___x_2585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2585_, 0, v_a_2584_);
v___y_2562_ = v___y_2582_;
v___y_2563_ = v___y_2583_;
v_a_2564_ = v___x_2585_;
goto v___jp_2561_;
}
v___jp_2586_:
{
lean_object* v___x_2593_; 
v___x_2593_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2593_, 0, v_a_2592_);
lean_ctor_set(v___x_2593_, 1, v___y_2588_);
lean_ctor_set_uint8(v___x_2593_, sizeof(void*)*2, v___y_2587_);
lean_ctor_set_uint8(v___x_2593_, sizeof(void*)*2 + 1, v___y_2589_);
v___y_2582_ = v___y_2590_;
v___y_2583_ = v___y_2591_;
v_a_2584_ = v___x_2593_;
goto v___jp_2581_;
}
v___jp_2594_:
{
if (lean_obj_tag(v___y_2597_) == 0)
{
lean_object* v_a_2598_; 
v_a_2598_ = lean_ctor_get(v___y_2597_, 0);
lean_inc(v_a_2598_);
lean_dec_ref_known(v___y_2597_, 1);
v___y_2582_ = v___y_2595_;
v___y_2583_ = v___y_2596_;
v_a_2584_ = v_a_2598_;
goto v___jp_2581_;
}
else
{
lean_object* v_a_2599_; 
v_a_2599_ = lean_ctor_get(v___y_2597_, 0);
lean_inc(v_a_2599_);
lean_dec_ref_known(v___y_2597_, 1);
v___y_2577_ = v___y_2595_;
v___y_2578_ = v___y_2596_;
v_a_2579_ = v_a_2599_;
goto v___jp_2576_;
}
}
v___jp_2600_:
{
lean_object* v___x_2607_; 
v___x_2607_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2607_, 0, v_a_2606_);
lean_ctor_set(v___x_2607_, 1, v___y_2602_);
lean_ctor_set_uint8(v___x_2607_, sizeof(void*)*2, v___y_2601_);
lean_ctor_set_uint8(v___x_2607_, sizeof(void*)*2 + 1, v___y_2603_);
v___y_2582_ = v___y_2604_;
v___y_2583_ = v___y_2605_;
v_a_2584_ = v___x_2607_;
goto v___jp_2581_;
}
v___jp_2608_:
{
lean_object* v___x_2612_; double v___x_2613_; double v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2612_ = lean_io_get_num_heartbeats();
v___x_2613_ = lean_float_of_nat(v___y_2609_);
v___x_2614_ = lean_float_of_nat(v___x_2612_);
v___x_2615_ = lean_box_float(v___x_2613_);
v___x_2616_ = lean_box_float(v___x_2614_);
v___x_2617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2617_, 0, v___x_2615_);
lean_ctor_set(v___x_2617_, 1, v___x_2616_);
v___x_2618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2618_, 0, v_a_2611_);
lean_ctor_set(v___x_2618_, 1, v___x_2617_);
v___x_2619_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4(v___x_2557_, v_hasTrace_2552_, v___x_2558_, v_options_2551_, v___x_2560_, v___y_2610_, v___f_2556_, v___x_2618_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
return v___x_2619_;
}
v___jp_2620_:
{
lean_object* v___x_2624_; 
v___x_2624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2624_, 0, v_a_2623_);
v___y_2609_ = v___y_2621_;
v___y_2610_ = v___y_2622_;
v_a_2611_ = v___x_2624_;
goto v___jp_2608_;
}
v___jp_2625_:
{
lean_object* v___x_2629_; 
v___x_2629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2629_, 0, v_a_2628_);
v___y_2609_ = v___y_2626_;
v___y_2610_ = v___y_2627_;
v_a_2611_ = v___x_2629_;
goto v___jp_2608_;
}
v___jp_2630_:
{
lean_object* v___x_2637_; 
v___x_2637_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2637_, 0, v_a_2636_);
lean_ctor_set(v___x_2637_, 1, v___y_2631_);
lean_ctor_set_uint8(v___x_2637_, sizeof(void*)*2, v___y_2634_);
lean_ctor_set_uint8(v___x_2637_, sizeof(void*)*2 + 1, v___y_2632_);
v___y_2626_ = v___y_2633_;
v___y_2627_ = v___y_2635_;
v_a_2628_ = v___x_2637_;
goto v___jp_2625_;
}
v___jp_2638_:
{
if (lean_obj_tag(v___y_2641_) == 0)
{
lean_object* v_a_2642_; 
v_a_2642_ = lean_ctor_get(v___y_2641_, 0);
lean_inc(v_a_2642_);
lean_dec_ref_known(v___y_2641_, 1);
v___y_2626_ = v___y_2639_;
v___y_2627_ = v___y_2640_;
v_a_2628_ = v_a_2642_;
goto v___jp_2625_;
}
else
{
lean_object* v_a_2643_; 
v_a_2643_ = lean_ctor_get(v___y_2641_, 0);
lean_inc(v_a_2643_);
lean_dec_ref_known(v___y_2641_, 1);
v___y_2621_ = v___y_2639_;
v___y_2622_ = v___y_2640_;
v_a_2623_ = v_a_2643_;
goto v___jp_2620_;
}
}
v___jp_2644_:
{
uint8_t v___x_2650_; lean_object* v___x_2651_; 
v___x_2650_ = 0;
v___x_2651_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2651_, 0, v_a_2649_);
lean_ctor_set(v___x_2651_, 1, v___y_2645_);
lean_ctor_set_uint8(v___x_2651_, sizeof(void*)*2, v___y_2647_);
lean_ctor_set_uint8(v___x_2651_, sizeof(void*)*2 + 1, v___x_2650_);
v___y_2626_ = v___y_2646_;
v___y_2627_ = v___y_2648_;
v_a_2628_ = v___x_2651_;
goto v___jp_2625_;
}
v___jp_2652_:
{
lean_object* v___x_2653_; lean_object* v_a_2654_; lean_object* v___x_2655_; uint8_t v___x_2656_; 
v___x_2653_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg(v_a_2287_);
v_a_2654_ = lean_ctor_get(v___x_2653_, 0);
lean_inc(v_a_2654_);
lean_dec_ref(v___x_2653_);
v___x_2655_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2656_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_2551_, v___x_2655_);
if (v___x_2656_ == 0)
{
lean_object* v___x_2657_; lean_object* v___x_2658_; 
v___x_2657_ = lean_io_mono_nanos_now();
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
v___x_2658_ = lean_sym_simp(v_struct_2305_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2658_) == 0)
{
lean_object* v_a_2659_; 
v_a_2659_ = lean_ctor_get(v___x_2658_, 0);
lean_inc(v_a_2659_);
lean_dec_ref_known(v___x_2658_, 1);
if (lean_obj_tag(v_a_2659_) == 0)
{
uint8_t v_contextDependent_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2681_; 
v_contextDependent_2660_ = lean_ctor_get_uint8(v_a_2659_, 1);
v_isSharedCheck_2681_ = !lean_is_exclusive(v_a_2659_);
if (v_isSharedCheck_2681_ == 0)
{
v___x_2662_ = v_a_2659_;
v_isShared_2663_ = v_isSharedCheck_2681_;
goto v_resetjp_2661_;
}
else
{
lean_dec(v_a_2659_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2681_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
uint8_t v___x_2664_; lean_object* v___x_2665_; lean_object* v___f_2666_; lean_object* v___x_2667_; 
v___x_2664_ = 1;
v___x_2665_ = lean_box(v___x_2664_);
v___f_2666_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2666_, 0, v___x_2665_);
lean_closure_set(v___f_2666_, 1, v_e_2278_);
v___x_2667_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___f_2666_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2667_) == 0)
{
lean_object* v_a_2668_; 
v_a_2668_ = lean_ctor_get(v___x_2667_, 0);
lean_inc(v_a_2668_);
lean_dec_ref_known(v___x_2667_, 1);
if (lean_obj_tag(v_a_2668_) == 1)
{
lean_object* v_val_2669_; lean_object* v___x_2670_; 
lean_del_object(v___x_2662_);
v_val_2669_ = lean_ctor_get(v_a_2668_, 0);
lean_inc(v_val_2669_);
lean_dec_ref_known(v_a_2668_, 1);
v___x_2670_ = l_Lean_Meta_Sym_shareCommonInc(v_val_2669_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2670_) == 0)
{
lean_object* v_a_2671_; lean_object* v___x_2672_; 
v_a_2671_ = lean_ctor_get(v___x_2670_, 0);
lean_inc_n(v_a_2671_, 2);
lean_dec_ref_known(v___x_2670_, 1);
v___x_2672_ = l_Lean_Meta_Sym_mkEqRefl(v_a_2671_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2672_) == 0)
{
lean_object* v_a_2673_; lean_object* v___x_2674_; 
v_a_2673_ = lean_ctor_get(v___x_2672_, 0);
lean_inc(v_a_2673_);
lean_dec_ref_known(v___x_2672_, 1);
v___x_2674_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2674_, 0, v_a_2671_);
lean_ctor_set(v___x_2674_, 1, v_a_2673_);
lean_ctor_set_uint8(v___x_2674_, sizeof(void*)*2, v_contextDependent_2660_);
lean_ctor_set_uint8(v___x_2674_, sizeof(void*)*2 + 1, v___x_2656_);
v___y_2582_ = v___x_2657_;
v___y_2583_ = v_a_2654_;
v_a_2584_ = v___x_2674_;
goto v___jp_2581_;
}
else
{
lean_object* v_a_2675_; 
lean_dec(v_a_2671_);
v_a_2675_ = lean_ctor_get(v___x_2672_, 0);
lean_inc(v_a_2675_);
lean_dec_ref_known(v___x_2672_, 1);
v___y_2577_ = v___x_2657_;
v___y_2578_ = v_a_2654_;
v_a_2579_ = v_a_2675_;
goto v___jp_2576_;
}
}
else
{
lean_object* v_a_2676_; 
v_a_2676_ = lean_ctor_get(v___x_2670_, 0);
lean_inc(v_a_2676_);
lean_dec_ref_known(v___x_2670_, 1);
v___y_2577_ = v___x_2657_;
v___y_2578_ = v_a_2654_;
v_a_2579_ = v_a_2676_;
goto v___jp_2576_;
}
}
else
{
lean_object* v___x_2678_; 
lean_dec(v_a_2668_);
if (v_isShared_2663_ == 0)
{
v___x_2678_ = v___x_2662_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v_reuseFailAlloc_2679_, 1, v_contextDependent_2660_);
v___x_2678_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
lean_ctor_set_uint8(v___x_2678_, 0, v_hasTrace_2552_);
v___y_2582_ = v___x_2657_;
v___y_2583_ = v_a_2654_;
v_a_2584_ = v___x_2678_;
goto v___jp_2581_;
}
}
}
else
{
lean_object* v_a_2680_; 
lean_del_object(v___x_2662_);
v_a_2680_ = lean_ctor_get(v___x_2667_, 0);
lean_inc(v_a_2680_);
lean_dec_ref_known(v___x_2667_, 1);
v___y_2577_ = v___x_2657_;
v___y_2578_ = v_a_2654_;
v_a_2579_ = v_a_2680_;
goto v___jp_2576_;
}
}
}
else
{
lean_object* v_e_x27_2682_; lean_object* v_proof_2683_; uint8_t v_contextDependent_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2757_; 
v_e_x27_2682_ = lean_ctor_get(v_a_2659_, 0);
v_proof_2683_ = lean_ctor_get(v_a_2659_, 1);
v_contextDependent_2684_ = lean_ctor_get_uint8(v_a_2659_, sizeof(void*)*2 + 1);
v_isSharedCheck_2757_ = !lean_is_exclusive(v_a_2659_);
if (v_isSharedCheck_2757_ == 0)
{
v___x_2686_ = v_a_2659_;
v_isShared_2687_ = v_isSharedCheck_2757_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_proof_2683_);
lean_inc(v_e_x27_2682_);
lean_dec(v_a_2659_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2757_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v___x_2688_; 
lean_inc_ref(v_e_x27_2682_);
v___x_2688_ = l_Lean_Meta_Sym_inferType(v_e_x27_2682_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2688_) == 0)
{
lean_object* v_a_2689_; lean_object* v___x_2690_; uint8_t v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; 
v_a_2689_ = lean_ctor_get(v___x_2688_, 0);
lean_inc(v_a_2689_);
lean_dec_ref_known(v___x_2688_, 1);
v___x_2690_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__1));
v___x_2691_ = 0;
v___x_2692_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2);
lean_inc(v_idx_2304_);
lean_inc(v_typeName_2303_);
v___x_2693_ = l_Lean_Expr_proj___override(v_typeName_2303_, v_idx_2304_, v___x_2692_);
v___x_2694_ = l_Lean_mkLambda(v___x_2690_, v___x_2691_, v_a_2689_, v___x_2693_);
lean_inc_ref(v___x_2694_);
v___x_2695_ = l_Lean_Meta_Sym_inferType(v___x_2694_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2695_) == 0)
{
lean_object* v_a_2696_; uint8_t v___x_2697_; 
v_a_2696_ = lean_ctor_get(v___x_2695_, 0);
lean_inc(v_a_2696_);
lean_dec_ref_known(v___x_2695_, 1);
v___x_2697_ = l_Lean_Expr_isArrow(v_a_2696_);
if (v___x_2697_ == 0)
{
uint8_t v___x_2698_; lean_object* v___x_2699_; lean_object* v___f_2700_; lean_object* v___x_2701_; 
lean_dec(v_a_2696_);
v___x_2698_ = 1;
v___x_2699_ = lean_box(v___x_2698_);
lean_inc_ref(v_e_2278_);
v___f_2700_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2700_, 0, v___x_2699_);
lean_closure_set(v___f_2700_, 1, v_e_2278_);
v___x_2701_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___f_2700_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2701_) == 0)
{
lean_object* v_a_2702_; 
v_a_2702_ = lean_ctor_get(v___x_2701_, 0);
lean_inc(v_a_2702_);
lean_dec_ref_known(v___x_2701_, 1);
if (lean_obj_tag(v_a_2702_) == 0)
{
lean_object* v___x_2703_; 
lean_del_object(v___x_2686_);
lean_inc_ref(v_e_x27_2682_);
lean_inc_ref(v_struct_2305_);
v___x_2703_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_struct_2305_, v_e_x27_2682_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2703_) == 0)
{
lean_object* v_a_2704_; uint8_t v___x_2705_; 
v_a_2704_ = lean_ctor_get(v___x_2703_, 0);
lean_inc(v_a_2704_);
lean_dec_ref_known(v___x_2703_, 1);
v___x_2705_ = lean_unbox(v_a_2704_);
lean_dec(v_a_2704_);
if (v___x_2705_ == 0)
{
lean_object* v___x_2706_; 
lean_dec_ref(v___x_2694_);
lean_dec_ref(v_proof_2683_);
lean_dec_ref(v_e_x27_2682_);
lean_dec_ref_known(v_e_2278_, 3);
v___x_2706_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2706_, 0, v_hasTrace_2552_);
lean_ctor_set_uint8(v___x_2706_, 1, v_contextDependent_2684_);
v___y_2582_ = v___x_2657_;
v___y_2583_ = v_a_2654_;
v_a_2584_ = v___x_2706_;
goto v___jp_2581_;
}
else
{
lean_object* v___x_2707_; 
v___x_2707_ = l_Lean_Meta_mkHCongr(v___x_2694_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2707_) == 0)
{
lean_object* v_a_2708_; lean_object* v_proof_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; 
v_a_2708_ = lean_ctor_get(v___x_2707_, 0);
lean_inc(v_a_2708_);
lean_dec_ref_known(v___x_2707_, 1);
v_proof_2709_ = lean_ctor_get(v_a_2708_, 1);
lean_inc_ref(v_proof_2709_);
lean_dec(v_a_2708_);
lean_inc_ref(v_e_x27_2682_);
lean_inc_ref(v_struct_2305_);
v___x_2710_ = l_Lean_mkApp3(v_proof_2709_, v_struct_2305_, v_e_x27_2682_, v_proof_2683_);
v___x_2711_ = l_Lean_Meta_mkEqOfHEq(v___x_2710_, v___x_2656_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2711_) == 0)
{
lean_object* v_a_2712_; size_t v___x_2713_; size_t v___x_2714_; uint8_t v___x_2715_; 
v_a_2712_ = lean_ctor_get(v___x_2711_, 0);
lean_inc(v_a_2712_);
lean_dec_ref_known(v___x_2711_, 1);
v___x_2713_ = lean_ptr_addr(v_struct_2305_);
v___x_2714_ = lean_ptr_addr(v_e_x27_2682_);
v___x_2715_ = lean_usize_dec_eq(v___x_2713_, v___x_2714_);
if (v___x_2715_ == 0)
{
lean_object* v___x_2716_; 
lean_inc(v_idx_2304_);
lean_inc(v_typeName_2303_);
lean_dec_ref_known(v_e_2278_, 3);
v___x_2716_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_typeName_2303_, v_idx_2304_, v_e_x27_2682_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2716_) == 0)
{
lean_object* v_a_2717_; 
v_a_2717_ = lean_ctor_get(v___x_2716_, 0);
lean_inc(v_a_2717_);
lean_dec_ref_known(v___x_2716_, 1);
v___y_2587_ = v_contextDependent_2684_;
v___y_2588_ = v_a_2712_;
v___y_2589_ = v___x_2656_;
v___y_2590_ = v___x_2657_;
v___y_2591_ = v_a_2654_;
v_a_2592_ = v_a_2717_;
goto v___jp_2586_;
}
else
{
lean_object* v_a_2718_; 
lean_dec(v_a_2712_);
v_a_2718_ = lean_ctor_get(v___x_2716_, 0);
lean_inc(v_a_2718_);
lean_dec_ref_known(v___x_2716_, 1);
v___y_2577_ = v___x_2657_;
v___y_2578_ = v_a_2654_;
v_a_2579_ = v_a_2718_;
goto v___jp_2576_;
}
}
else
{
lean_dec_ref(v_e_x27_2682_);
v___y_2587_ = v_contextDependent_2684_;
v___y_2588_ = v_a_2712_;
v___y_2589_ = v___x_2656_;
v___y_2590_ = v___x_2657_;
v___y_2591_ = v_a_2654_;
v_a_2592_ = v_e_2278_;
goto v___jp_2586_;
}
}
else
{
lean_object* v_a_2719_; 
lean_dec_ref(v_e_x27_2682_);
lean_dec_ref_known(v_e_2278_, 3);
v_a_2719_ = lean_ctor_get(v___x_2711_, 0);
lean_inc(v_a_2719_);
lean_dec_ref_known(v___x_2711_, 1);
v___y_2577_ = v___x_2657_;
v___y_2578_ = v_a_2654_;
v_a_2579_ = v_a_2719_;
goto v___jp_2576_;
}
}
else
{
lean_object* v_a_2720_; 
lean_dec_ref(v_proof_2683_);
lean_dec_ref(v_e_x27_2682_);
lean_dec_ref_known(v_e_2278_, 3);
v_a_2720_ = lean_ctor_get(v___x_2707_, 0);
lean_inc(v_a_2720_);
lean_dec_ref_known(v___x_2707_, 1);
v___y_2577_ = v___x_2657_;
v___y_2578_ = v_a_2654_;
v_a_2579_ = v_a_2720_;
goto v___jp_2576_;
}
}
}
else
{
lean_object* v_a_2721_; 
lean_dec_ref(v___x_2694_);
lean_dec_ref(v_proof_2683_);
lean_dec_ref(v_e_x27_2682_);
lean_dec_ref_known(v_e_2278_, 3);
v_a_2721_ = lean_ctor_get(v___x_2703_, 0);
lean_inc(v_a_2721_);
lean_dec_ref_known(v___x_2703_, 1);
v___y_2577_ = v___x_2657_;
v___y_2578_ = v_a_2654_;
v_a_2579_ = v_a_2721_;
goto v___jp_2576_;
}
}
else
{
lean_object* v_val_2722_; lean_object* v___x_2723_; 
lean_dec_ref(v___x_2694_);
lean_dec_ref(v_proof_2683_);
lean_dec_ref(v_e_x27_2682_);
lean_dec_ref_known(v_e_2278_, 3);
v_val_2722_ = lean_ctor_get(v_a_2702_, 0);
lean_inc(v_val_2722_);
lean_dec_ref_known(v_a_2702_, 1);
v___x_2723_ = l_Lean_Meta_Sym_shareCommonInc(v_val_2722_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2723_) == 0)
{
lean_object* v_a_2724_; lean_object* v___x_2725_; 
v_a_2724_ = lean_ctor_get(v___x_2723_, 0);
lean_inc_n(v_a_2724_, 2);
lean_dec_ref_known(v___x_2723_, 1);
v___x_2725_ = l_Lean_Meta_Sym_mkEqRefl(v_a_2724_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2725_) == 0)
{
lean_object* v_a_2726_; lean_object* v___x_2728_; 
v_a_2726_ = lean_ctor_get(v___x_2725_, 0);
lean_inc(v_a_2726_);
lean_dec_ref_known(v___x_2725_, 1);
if (v_isShared_2687_ == 0)
{
lean_ctor_set(v___x_2686_, 1, v_a_2726_);
lean_ctor_set(v___x_2686_, 0, v_a_2724_);
v___x_2728_ = v___x_2686_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v_a_2724_);
lean_ctor_set(v_reuseFailAlloc_2729_, 1, v_a_2726_);
v___x_2728_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
lean_ctor_set_uint8(v___x_2728_, sizeof(void*)*2, v_contextDependent_2684_);
lean_ctor_set_uint8(v___x_2728_, sizeof(void*)*2 + 1, v___x_2656_);
v___y_2582_ = v___x_2657_;
v___y_2583_ = v_a_2654_;
v_a_2584_ = v___x_2728_;
goto v___jp_2581_;
}
}
else
{
lean_object* v_a_2730_; 
lean_dec(v_a_2724_);
lean_del_object(v___x_2686_);
v_a_2730_ = lean_ctor_get(v___x_2725_, 0);
lean_inc(v_a_2730_);
lean_dec_ref_known(v___x_2725_, 1);
v___y_2577_ = v___x_2657_;
v___y_2578_ = v_a_2654_;
v_a_2579_ = v_a_2730_;
goto v___jp_2576_;
}
}
else
{
lean_object* v_a_2731_; 
lean_del_object(v___x_2686_);
v_a_2731_ = lean_ctor_get(v___x_2723_, 0);
lean_inc(v_a_2731_);
lean_dec_ref_known(v___x_2723_, 1);
v___y_2577_ = v___x_2657_;
v___y_2578_ = v_a_2654_;
v_a_2579_ = v_a_2731_;
goto v___jp_2576_;
}
}
}
else
{
lean_object* v_a_2732_; 
lean_dec_ref(v___x_2694_);
lean_del_object(v___x_2686_);
lean_dec_ref(v_proof_2683_);
lean_dec_ref(v_e_x27_2682_);
lean_dec_ref_known(v_e_2278_, 3);
v_a_2732_ = lean_ctor_get(v___x_2701_, 0);
lean_inc(v_a_2732_);
lean_dec_ref_known(v___x_2701_, 1);
v___y_2577_ = v___x_2657_;
v___y_2578_ = v_a_2654_;
v_a_2579_ = v_a_2732_;
goto v___jp_2576_;
}
}
else
{
lean_del_object(v___x_2686_);
if (lean_obj_tag(v_a_2696_) == 7)
{
lean_object* v_binderType_2733_; lean_object* v_body_2734_; lean_object* v___x_2735_; 
v_binderType_2733_ = lean_ctor_get(v_a_2696_, 1);
lean_inc_ref_n(v_binderType_2733_, 2);
v_body_2734_ = lean_ctor_get(v_a_2696_, 2);
lean_inc_ref(v_body_2734_);
lean_dec_ref_known(v_a_2696_, 3);
v___x_2735_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_2733_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2735_) == 0)
{
lean_object* v_a_2736_; lean_object* v___x_2737_; 
v_a_2736_ = lean_ctor_get(v___x_2735_, 0);
lean_inc(v_a_2736_);
lean_dec_ref_known(v___x_2735_, 1);
lean_inc_ref(v_body_2734_);
v___x_2737_ = l_Lean_Meta_Sym_getLevel___redArg(v_body_2734_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2737_) == 0)
{
lean_object* v_a_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; size_t v___x_2745_; size_t v___x_2746_; uint8_t v___x_2747_; 
v_a_2738_ = lean_ctor_get(v___x_2737_, 0);
lean_inc(v_a_2738_);
lean_dec_ref_known(v___x_2737_, 1);
v___x_2739_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4));
v___x_2740_ = lean_box(0);
v___x_2741_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2741_, 0, v_a_2738_);
lean_ctor_set(v___x_2741_, 1, v___x_2740_);
v___x_2742_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2742_, 0, v_a_2736_);
lean_ctor_set(v___x_2742_, 1, v___x_2741_);
v___x_2743_ = l_Lean_mkConst(v___x_2739_, v___x_2742_);
lean_inc_ref(v_e_x27_2682_);
lean_inc_ref(v_struct_2305_);
v___x_2744_ = l_Lean_mkApp6(v___x_2743_, v_binderType_2733_, v_body_2734_, v_struct_2305_, v_e_x27_2682_, v___x_2694_, v_proof_2683_);
v___x_2745_ = lean_ptr_addr(v_struct_2305_);
v___x_2746_ = lean_ptr_addr(v_e_x27_2682_);
v___x_2747_ = lean_usize_dec_eq(v___x_2745_, v___x_2746_);
if (v___x_2747_ == 0)
{
lean_object* v___x_2748_; 
lean_inc(v_idx_2304_);
lean_inc(v_typeName_2303_);
lean_dec_ref_known(v_e_2278_, 3);
v___x_2748_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_typeName_2303_, v_idx_2304_, v_e_x27_2682_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2748_) == 0)
{
lean_object* v_a_2749_; 
v_a_2749_ = lean_ctor_get(v___x_2748_, 0);
lean_inc(v_a_2749_);
lean_dec_ref_known(v___x_2748_, 1);
v___y_2601_ = v_contextDependent_2684_;
v___y_2602_ = v___x_2744_;
v___y_2603_ = v___x_2656_;
v___y_2604_ = v___x_2657_;
v___y_2605_ = v_a_2654_;
v_a_2606_ = v_a_2749_;
goto v___jp_2600_;
}
else
{
lean_object* v_a_2750_; 
lean_dec_ref(v___x_2744_);
v_a_2750_ = lean_ctor_get(v___x_2748_, 0);
lean_inc(v_a_2750_);
lean_dec_ref_known(v___x_2748_, 1);
v___y_2577_ = v___x_2657_;
v___y_2578_ = v_a_2654_;
v_a_2579_ = v_a_2750_;
goto v___jp_2576_;
}
}
else
{
lean_dec_ref(v_e_x27_2682_);
v___y_2601_ = v_contextDependent_2684_;
v___y_2602_ = v___x_2744_;
v___y_2603_ = v___x_2656_;
v___y_2604_ = v___x_2657_;
v___y_2605_ = v_a_2654_;
v_a_2606_ = v_e_2278_;
goto v___jp_2600_;
}
}
else
{
lean_object* v_a_2751_; 
lean_dec(v_a_2736_);
lean_dec_ref(v_body_2734_);
lean_dec_ref(v_binderType_2733_);
lean_dec_ref(v___x_2694_);
lean_dec_ref(v_proof_2683_);
lean_dec_ref(v_e_x27_2682_);
lean_dec_ref_known(v_e_2278_, 3);
v_a_2751_ = lean_ctor_get(v___x_2737_, 0);
lean_inc(v_a_2751_);
lean_dec_ref_known(v___x_2737_, 1);
v___y_2577_ = v___x_2657_;
v___y_2578_ = v_a_2654_;
v_a_2579_ = v_a_2751_;
goto v___jp_2576_;
}
}
else
{
lean_object* v_a_2752_; 
lean_dec_ref(v_body_2734_);
lean_dec_ref(v_binderType_2733_);
lean_dec_ref(v___x_2694_);
lean_dec_ref(v_proof_2683_);
lean_dec_ref(v_e_x27_2682_);
lean_dec_ref_known(v_e_2278_, 3);
v_a_2752_ = lean_ctor_get(v___x_2735_, 0);
lean_inc(v_a_2752_);
lean_dec_ref_known(v___x_2735_, 1);
v___y_2577_ = v___x_2657_;
v___y_2578_ = v_a_2654_;
v_a_2579_ = v_a_2752_;
goto v___jp_2576_;
}
}
else
{
lean_object* v___x_2753_; lean_object* v___x_2754_; 
lean_dec(v_a_2696_);
lean_dec_ref(v___x_2694_);
lean_dec_ref(v_proof_2683_);
lean_dec_ref(v_e_x27_2682_);
lean_dec_ref_known(v_e_2278_, 3);
v___x_2753_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8);
v___x_2754_ = l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1(v___x_2753_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
v___y_2595_ = v___x_2657_;
v___y_2596_ = v_a_2654_;
v___y_2597_ = v___x_2754_;
goto v___jp_2594_;
}
}
}
else
{
lean_object* v_a_2755_; 
lean_dec_ref(v___x_2694_);
lean_del_object(v___x_2686_);
lean_dec_ref(v_proof_2683_);
lean_dec_ref(v_e_x27_2682_);
lean_dec_ref_known(v_e_2278_, 3);
v_a_2755_ = lean_ctor_get(v___x_2695_, 0);
lean_inc(v_a_2755_);
lean_dec_ref_known(v___x_2695_, 1);
v___y_2577_ = v___x_2657_;
v___y_2578_ = v_a_2654_;
v_a_2579_ = v_a_2755_;
goto v___jp_2576_;
}
}
else
{
lean_object* v_a_2756_; 
lean_del_object(v___x_2686_);
lean_dec_ref(v_proof_2683_);
lean_dec_ref(v_e_x27_2682_);
lean_dec_ref_known(v_e_2278_, 3);
v_a_2756_ = lean_ctor_get(v___x_2688_, 0);
lean_inc(v_a_2756_);
lean_dec_ref_known(v___x_2688_, 1);
v___y_2577_ = v___x_2657_;
v___y_2578_ = v_a_2654_;
v_a_2579_ = v_a_2756_;
goto v___jp_2576_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_2278_, 3);
v___y_2595_ = v___x_2657_;
v___y_2596_ = v_a_2654_;
v___y_2597_ = v___x_2658_;
goto v___jp_2594_;
}
}
else
{
lean_object* v___x_2758_; lean_object* v___x_2759_; 
v___x_2758_ = lean_io_get_num_heartbeats();
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
v___x_2759_ = lean_sym_simp(v_struct_2305_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2759_) == 0)
{
lean_object* v_a_2760_; 
v_a_2760_ = lean_ctor_get(v___x_2759_, 0);
lean_inc(v_a_2760_);
lean_dec_ref_known(v___x_2759_, 1);
if (lean_obj_tag(v_a_2760_) == 0)
{
uint8_t v_contextDependent_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2783_; 
v_contextDependent_2761_ = lean_ctor_get_uint8(v_a_2760_, 1);
v_isSharedCheck_2783_ = !lean_is_exclusive(v_a_2760_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2763_ = v_a_2760_;
v_isShared_2764_ = v_isSharedCheck_2783_;
goto v_resetjp_2762_;
}
else
{
lean_dec(v_a_2760_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2783_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
uint8_t v___x_2765_; lean_object* v___x_2766_; lean_object* v___f_2767_; lean_object* v___x_2768_; 
v___x_2765_ = 1;
v___x_2766_ = lean_box(v___x_2765_);
v___f_2767_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2767_, 0, v___x_2766_);
lean_closure_set(v___f_2767_, 1, v_e_2278_);
v___x_2768_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___f_2767_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2768_) == 0)
{
lean_object* v_a_2769_; 
v_a_2769_ = lean_ctor_get(v___x_2768_, 0);
lean_inc(v_a_2769_);
lean_dec_ref_known(v___x_2768_, 1);
if (lean_obj_tag(v_a_2769_) == 1)
{
lean_object* v_val_2770_; lean_object* v___x_2771_; 
lean_del_object(v___x_2763_);
v_val_2770_ = lean_ctor_get(v_a_2769_, 0);
lean_inc(v_val_2770_);
lean_dec_ref_known(v_a_2769_, 1);
v___x_2771_ = l_Lean_Meta_Sym_shareCommonInc(v_val_2770_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2771_) == 0)
{
lean_object* v_a_2772_; lean_object* v___x_2773_; 
v_a_2772_ = lean_ctor_get(v___x_2771_, 0);
lean_inc_n(v_a_2772_, 2);
lean_dec_ref_known(v___x_2771_, 1);
v___x_2773_ = l_Lean_Meta_Sym_mkEqRefl(v_a_2772_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2773_) == 0)
{
lean_object* v_a_2774_; uint8_t v___x_2775_; lean_object* v___x_2776_; 
v_a_2774_ = lean_ctor_get(v___x_2773_, 0);
lean_inc(v_a_2774_);
lean_dec_ref_known(v___x_2773_, 1);
v___x_2775_ = 0;
v___x_2776_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2776_, 0, v_a_2772_);
lean_ctor_set(v___x_2776_, 1, v_a_2774_);
lean_ctor_set_uint8(v___x_2776_, sizeof(void*)*2, v_contextDependent_2761_);
lean_ctor_set_uint8(v___x_2776_, sizeof(void*)*2 + 1, v___x_2775_);
v___y_2626_ = v___x_2758_;
v___y_2627_ = v_a_2654_;
v_a_2628_ = v___x_2776_;
goto v___jp_2625_;
}
else
{
lean_object* v_a_2777_; 
lean_dec(v_a_2772_);
v_a_2777_ = lean_ctor_get(v___x_2773_, 0);
lean_inc(v_a_2777_);
lean_dec_ref_known(v___x_2773_, 1);
v___y_2621_ = v___x_2758_;
v___y_2622_ = v_a_2654_;
v_a_2623_ = v_a_2777_;
goto v___jp_2620_;
}
}
else
{
lean_object* v_a_2778_; 
v_a_2778_ = lean_ctor_get(v___x_2771_, 0);
lean_inc(v_a_2778_);
lean_dec_ref_known(v___x_2771_, 1);
v___y_2621_ = v___x_2758_;
v___y_2622_ = v_a_2654_;
v_a_2623_ = v_a_2778_;
goto v___jp_2620_;
}
}
else
{
lean_object* v___x_2780_; 
lean_dec(v_a_2769_);
if (v_isShared_2764_ == 0)
{
v___x_2780_ = v___x_2763_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v_reuseFailAlloc_2781_, 1, v_contextDependent_2761_);
v___x_2780_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
lean_ctor_set_uint8(v___x_2780_, 0, v___x_2656_);
v___y_2626_ = v___x_2758_;
v___y_2627_ = v_a_2654_;
v_a_2628_ = v___x_2780_;
goto v___jp_2625_;
}
}
}
else
{
lean_object* v_a_2782_; 
lean_del_object(v___x_2763_);
v_a_2782_ = lean_ctor_get(v___x_2768_, 0);
lean_inc(v_a_2782_);
lean_dec_ref_known(v___x_2768_, 1);
v___y_2621_ = v___x_2758_;
v___y_2622_ = v_a_2654_;
v_a_2623_ = v_a_2782_;
goto v___jp_2620_;
}
}
}
else
{
lean_object* v_e_x27_2784_; lean_object* v_proof_2785_; uint8_t v_contextDependent_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2859_; 
v_e_x27_2784_ = lean_ctor_get(v_a_2760_, 0);
v_proof_2785_ = lean_ctor_get(v_a_2760_, 1);
v_contextDependent_2786_ = lean_ctor_get_uint8(v_a_2760_, sizeof(void*)*2 + 1);
v_isSharedCheck_2859_ = !lean_is_exclusive(v_a_2760_);
if (v_isSharedCheck_2859_ == 0)
{
v___x_2788_ = v_a_2760_;
v_isShared_2789_ = v_isSharedCheck_2859_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_proof_2785_);
lean_inc(v_e_x27_2784_);
lean_dec(v_a_2760_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2859_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v___x_2790_; 
lean_inc_ref(v_e_x27_2784_);
v___x_2790_ = l_Lean_Meta_Sym_inferType(v_e_x27_2784_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2790_) == 0)
{
lean_object* v_a_2791_; lean_object* v___x_2792_; uint8_t v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; 
v_a_2791_ = lean_ctor_get(v___x_2790_, 0);
lean_inc(v_a_2791_);
lean_dec_ref_known(v___x_2790_, 1);
v___x_2792_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__1));
v___x_2793_ = 0;
v___x_2794_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2);
lean_inc(v_idx_2304_);
lean_inc(v_typeName_2303_);
v___x_2795_ = l_Lean_Expr_proj___override(v_typeName_2303_, v_idx_2304_, v___x_2794_);
v___x_2796_ = l_Lean_mkLambda(v___x_2792_, v___x_2793_, v_a_2791_, v___x_2795_);
lean_inc_ref(v___x_2796_);
v___x_2797_ = l_Lean_Meta_Sym_inferType(v___x_2796_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2797_) == 0)
{
lean_object* v_a_2798_; uint8_t v___x_2799_; 
v_a_2798_ = lean_ctor_get(v___x_2797_, 0);
lean_inc(v_a_2798_);
lean_dec_ref_known(v___x_2797_, 1);
v___x_2799_ = l_Lean_Expr_isArrow(v_a_2798_);
if (v___x_2799_ == 0)
{
uint8_t v___x_2800_; lean_object* v___x_2801_; lean_object* v___f_2802_; lean_object* v___x_2803_; 
lean_dec(v_a_2798_);
v___x_2800_ = 1;
v___x_2801_ = lean_box(v___x_2800_);
lean_inc_ref(v_e_2278_);
v___f_2802_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2802_, 0, v___x_2801_);
lean_closure_set(v___f_2802_, 1, v_e_2278_);
v___x_2803_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___f_2802_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2803_) == 0)
{
lean_object* v_a_2804_; 
v_a_2804_ = lean_ctor_get(v___x_2803_, 0);
lean_inc(v_a_2804_);
lean_dec_ref_known(v___x_2803_, 1);
if (lean_obj_tag(v_a_2804_) == 0)
{
lean_object* v___x_2805_; 
lean_del_object(v___x_2788_);
lean_inc_ref(v_e_x27_2784_);
lean_inc_ref(v_struct_2305_);
v___x_2805_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_struct_2305_, v_e_x27_2784_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2805_) == 0)
{
lean_object* v_a_2806_; uint8_t v___x_2807_; 
v_a_2806_ = lean_ctor_get(v___x_2805_, 0);
lean_inc(v_a_2806_);
lean_dec_ref_known(v___x_2805_, 1);
v___x_2807_ = lean_unbox(v_a_2806_);
lean_dec(v_a_2806_);
if (v___x_2807_ == 0)
{
lean_object* v___x_2808_; 
lean_dec_ref(v___x_2796_);
lean_dec_ref(v_proof_2785_);
lean_dec_ref(v_e_x27_2784_);
lean_dec_ref_known(v_e_2278_, 3);
v___x_2808_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2808_, 0, v___x_2656_);
lean_ctor_set_uint8(v___x_2808_, 1, v_contextDependent_2786_);
v___y_2626_ = v___x_2758_;
v___y_2627_ = v_a_2654_;
v_a_2628_ = v___x_2808_;
goto v___jp_2625_;
}
else
{
lean_object* v___x_2809_; 
v___x_2809_ = l_Lean_Meta_mkHCongr(v___x_2796_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2809_) == 0)
{
lean_object* v_a_2810_; lean_object* v_proof_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; 
v_a_2810_ = lean_ctor_get(v___x_2809_, 0);
lean_inc(v_a_2810_);
lean_dec_ref_known(v___x_2809_, 1);
v_proof_2811_ = lean_ctor_get(v_a_2810_, 1);
lean_inc_ref(v_proof_2811_);
lean_dec(v_a_2810_);
lean_inc_ref(v_e_x27_2784_);
lean_inc_ref(v_struct_2305_);
v___x_2812_ = l_Lean_mkApp3(v_proof_2811_, v_struct_2305_, v_e_x27_2784_, v_proof_2785_);
v___x_2813_ = l_Lean_Meta_mkEqOfHEq(v___x_2812_, v___x_2799_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2813_) == 0)
{
lean_object* v_a_2814_; size_t v___x_2815_; size_t v___x_2816_; uint8_t v___x_2817_; 
v_a_2814_ = lean_ctor_get(v___x_2813_, 0);
lean_inc(v_a_2814_);
lean_dec_ref_known(v___x_2813_, 1);
v___x_2815_ = lean_ptr_addr(v_struct_2305_);
v___x_2816_ = lean_ptr_addr(v_e_x27_2784_);
v___x_2817_ = lean_usize_dec_eq(v___x_2815_, v___x_2816_);
if (v___x_2817_ == 0)
{
lean_object* v___x_2818_; 
lean_inc(v_idx_2304_);
lean_inc(v_typeName_2303_);
lean_dec_ref_known(v_e_2278_, 3);
v___x_2818_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_typeName_2303_, v_idx_2304_, v_e_x27_2784_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2818_) == 0)
{
lean_object* v_a_2819_; 
v_a_2819_ = lean_ctor_get(v___x_2818_, 0);
lean_inc(v_a_2819_);
lean_dec_ref_known(v___x_2818_, 1);
v___y_2631_ = v_a_2814_;
v___y_2632_ = v___x_2799_;
v___y_2633_ = v___x_2758_;
v___y_2634_ = v_contextDependent_2786_;
v___y_2635_ = v_a_2654_;
v_a_2636_ = v_a_2819_;
goto v___jp_2630_;
}
else
{
lean_object* v_a_2820_; 
lean_dec(v_a_2814_);
v_a_2820_ = lean_ctor_get(v___x_2818_, 0);
lean_inc(v_a_2820_);
lean_dec_ref_known(v___x_2818_, 1);
v___y_2621_ = v___x_2758_;
v___y_2622_ = v_a_2654_;
v_a_2623_ = v_a_2820_;
goto v___jp_2620_;
}
}
else
{
lean_dec_ref(v_e_x27_2784_);
v___y_2631_ = v_a_2814_;
v___y_2632_ = v___x_2799_;
v___y_2633_ = v___x_2758_;
v___y_2634_ = v_contextDependent_2786_;
v___y_2635_ = v_a_2654_;
v_a_2636_ = v_e_2278_;
goto v___jp_2630_;
}
}
else
{
lean_object* v_a_2821_; 
lean_dec_ref(v_e_x27_2784_);
lean_dec_ref_known(v_e_2278_, 3);
v_a_2821_ = lean_ctor_get(v___x_2813_, 0);
lean_inc(v_a_2821_);
lean_dec_ref_known(v___x_2813_, 1);
v___y_2621_ = v___x_2758_;
v___y_2622_ = v_a_2654_;
v_a_2623_ = v_a_2821_;
goto v___jp_2620_;
}
}
else
{
lean_object* v_a_2822_; 
lean_dec_ref(v_proof_2785_);
lean_dec_ref(v_e_x27_2784_);
lean_dec_ref_known(v_e_2278_, 3);
v_a_2822_ = lean_ctor_get(v___x_2809_, 0);
lean_inc(v_a_2822_);
lean_dec_ref_known(v___x_2809_, 1);
v___y_2621_ = v___x_2758_;
v___y_2622_ = v_a_2654_;
v_a_2623_ = v_a_2822_;
goto v___jp_2620_;
}
}
}
else
{
lean_object* v_a_2823_; 
lean_dec_ref(v___x_2796_);
lean_dec_ref(v_proof_2785_);
lean_dec_ref(v_e_x27_2784_);
lean_dec_ref_known(v_e_2278_, 3);
v_a_2823_ = lean_ctor_get(v___x_2805_, 0);
lean_inc(v_a_2823_);
lean_dec_ref_known(v___x_2805_, 1);
v___y_2621_ = v___x_2758_;
v___y_2622_ = v_a_2654_;
v_a_2623_ = v_a_2823_;
goto v___jp_2620_;
}
}
else
{
lean_object* v_val_2824_; lean_object* v___x_2825_; 
lean_dec_ref(v___x_2796_);
lean_dec_ref(v_proof_2785_);
lean_dec_ref(v_e_x27_2784_);
lean_dec_ref_known(v_e_2278_, 3);
v_val_2824_ = lean_ctor_get(v_a_2804_, 0);
lean_inc(v_val_2824_);
lean_dec_ref_known(v_a_2804_, 1);
v___x_2825_ = l_Lean_Meta_Sym_shareCommonInc(v_val_2824_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_object* v_a_2826_; lean_object* v___x_2827_; 
v_a_2826_ = lean_ctor_get(v___x_2825_, 0);
lean_inc_n(v_a_2826_, 2);
lean_dec_ref_known(v___x_2825_, 1);
v___x_2827_ = l_Lean_Meta_Sym_mkEqRefl(v_a_2826_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2827_) == 0)
{
lean_object* v_a_2828_; lean_object* v___x_2830_; 
v_a_2828_ = lean_ctor_get(v___x_2827_, 0);
lean_inc(v_a_2828_);
lean_dec_ref_known(v___x_2827_, 1);
if (v_isShared_2789_ == 0)
{
lean_ctor_set(v___x_2788_, 1, v_a_2828_);
lean_ctor_set(v___x_2788_, 0, v_a_2826_);
v___x_2830_ = v___x_2788_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_a_2826_);
lean_ctor_set(v_reuseFailAlloc_2831_, 1, v_a_2828_);
v___x_2830_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
lean_ctor_set_uint8(v___x_2830_, sizeof(void*)*2, v_contextDependent_2786_);
lean_ctor_set_uint8(v___x_2830_, sizeof(void*)*2 + 1, v___x_2799_);
v___y_2626_ = v___x_2758_;
v___y_2627_ = v_a_2654_;
v_a_2628_ = v___x_2830_;
goto v___jp_2625_;
}
}
else
{
lean_object* v_a_2832_; 
lean_dec(v_a_2826_);
lean_del_object(v___x_2788_);
v_a_2832_ = lean_ctor_get(v___x_2827_, 0);
lean_inc(v_a_2832_);
lean_dec_ref_known(v___x_2827_, 1);
v___y_2621_ = v___x_2758_;
v___y_2622_ = v_a_2654_;
v_a_2623_ = v_a_2832_;
goto v___jp_2620_;
}
}
else
{
lean_object* v_a_2833_; 
lean_del_object(v___x_2788_);
v_a_2833_ = lean_ctor_get(v___x_2825_, 0);
lean_inc(v_a_2833_);
lean_dec_ref_known(v___x_2825_, 1);
v___y_2621_ = v___x_2758_;
v___y_2622_ = v_a_2654_;
v_a_2623_ = v_a_2833_;
goto v___jp_2620_;
}
}
}
else
{
lean_object* v_a_2834_; 
lean_dec_ref(v___x_2796_);
lean_del_object(v___x_2788_);
lean_dec_ref(v_proof_2785_);
lean_dec_ref(v_e_x27_2784_);
lean_dec_ref_known(v_e_2278_, 3);
v_a_2834_ = lean_ctor_get(v___x_2803_, 0);
lean_inc(v_a_2834_);
lean_dec_ref_known(v___x_2803_, 1);
v___y_2621_ = v___x_2758_;
v___y_2622_ = v_a_2654_;
v_a_2623_ = v_a_2834_;
goto v___jp_2620_;
}
}
else
{
lean_del_object(v___x_2788_);
if (lean_obj_tag(v_a_2798_) == 7)
{
lean_object* v_binderType_2835_; lean_object* v_body_2836_; lean_object* v___x_2837_; 
v_binderType_2835_ = lean_ctor_get(v_a_2798_, 1);
lean_inc_ref_n(v_binderType_2835_, 2);
v_body_2836_ = lean_ctor_get(v_a_2798_, 2);
lean_inc_ref(v_body_2836_);
lean_dec_ref_known(v_a_2798_, 3);
v___x_2837_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_2835_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2837_) == 0)
{
lean_object* v_a_2838_; lean_object* v___x_2839_; 
v_a_2838_ = lean_ctor_get(v___x_2837_, 0);
lean_inc(v_a_2838_);
lean_dec_ref_known(v___x_2837_, 1);
lean_inc_ref(v_body_2836_);
v___x_2839_ = l_Lean_Meta_Sym_getLevel___redArg(v_body_2836_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2839_) == 0)
{
lean_object* v_a_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; size_t v___x_2847_; size_t v___x_2848_; uint8_t v___x_2849_; 
v_a_2840_ = lean_ctor_get(v___x_2839_, 0);
lean_inc(v_a_2840_);
lean_dec_ref_known(v___x_2839_, 1);
v___x_2841_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4));
v___x_2842_ = lean_box(0);
v___x_2843_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2843_, 0, v_a_2840_);
lean_ctor_set(v___x_2843_, 1, v___x_2842_);
v___x_2844_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2844_, 0, v_a_2838_);
lean_ctor_set(v___x_2844_, 1, v___x_2843_);
v___x_2845_ = l_Lean_mkConst(v___x_2841_, v___x_2844_);
lean_inc_ref(v_e_x27_2784_);
lean_inc_ref(v_struct_2305_);
v___x_2846_ = l_Lean_mkApp6(v___x_2845_, v_binderType_2835_, v_body_2836_, v_struct_2305_, v_e_x27_2784_, v___x_2796_, v_proof_2785_);
v___x_2847_ = lean_ptr_addr(v_struct_2305_);
v___x_2848_ = lean_ptr_addr(v_e_x27_2784_);
v___x_2849_ = lean_usize_dec_eq(v___x_2847_, v___x_2848_);
if (v___x_2849_ == 0)
{
lean_object* v___x_2850_; 
lean_inc(v_idx_2304_);
lean_inc(v_typeName_2303_);
lean_dec_ref_known(v_e_2278_, 3);
v___x_2850_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_typeName_2303_, v_idx_2304_, v_e_x27_2784_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2850_) == 0)
{
lean_object* v_a_2851_; 
v_a_2851_ = lean_ctor_get(v___x_2850_, 0);
lean_inc(v_a_2851_);
lean_dec_ref_known(v___x_2850_, 1);
v___y_2645_ = v___x_2846_;
v___y_2646_ = v___x_2758_;
v___y_2647_ = v_contextDependent_2786_;
v___y_2648_ = v_a_2654_;
v_a_2649_ = v_a_2851_;
goto v___jp_2644_;
}
else
{
lean_object* v_a_2852_; 
lean_dec_ref(v___x_2846_);
v_a_2852_ = lean_ctor_get(v___x_2850_, 0);
lean_inc(v_a_2852_);
lean_dec_ref_known(v___x_2850_, 1);
v___y_2621_ = v___x_2758_;
v___y_2622_ = v_a_2654_;
v_a_2623_ = v_a_2852_;
goto v___jp_2620_;
}
}
else
{
lean_dec_ref(v_e_x27_2784_);
v___y_2645_ = v___x_2846_;
v___y_2646_ = v___x_2758_;
v___y_2647_ = v_contextDependent_2786_;
v___y_2648_ = v_a_2654_;
v_a_2649_ = v_e_2278_;
goto v___jp_2644_;
}
}
else
{
lean_object* v_a_2853_; 
lean_dec(v_a_2838_);
lean_dec_ref(v_body_2836_);
lean_dec_ref(v_binderType_2835_);
lean_dec_ref(v___x_2796_);
lean_dec_ref(v_proof_2785_);
lean_dec_ref(v_e_x27_2784_);
lean_dec_ref_known(v_e_2278_, 3);
v_a_2853_ = lean_ctor_get(v___x_2839_, 0);
lean_inc(v_a_2853_);
lean_dec_ref_known(v___x_2839_, 1);
v___y_2621_ = v___x_2758_;
v___y_2622_ = v_a_2654_;
v_a_2623_ = v_a_2853_;
goto v___jp_2620_;
}
}
else
{
lean_object* v_a_2854_; 
lean_dec_ref(v_body_2836_);
lean_dec_ref(v_binderType_2835_);
lean_dec_ref(v___x_2796_);
lean_dec_ref(v_proof_2785_);
lean_dec_ref(v_e_x27_2784_);
lean_dec_ref_known(v_e_2278_, 3);
v_a_2854_ = lean_ctor_get(v___x_2837_, 0);
lean_inc(v_a_2854_);
lean_dec_ref_known(v___x_2837_, 1);
v___y_2621_ = v___x_2758_;
v___y_2622_ = v_a_2654_;
v_a_2623_ = v_a_2854_;
goto v___jp_2620_;
}
}
else
{
lean_object* v___x_2855_; lean_object* v___x_2856_; 
lean_dec(v_a_2798_);
lean_dec_ref(v___x_2796_);
lean_dec_ref(v_proof_2785_);
lean_dec_ref(v_e_x27_2784_);
lean_dec_ref_known(v_e_2278_, 3);
v___x_2855_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8);
v___x_2856_ = l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1(v___x_2855_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
v___y_2639_ = v___x_2758_;
v___y_2640_ = v_a_2654_;
v___y_2641_ = v___x_2856_;
goto v___jp_2638_;
}
}
}
else
{
lean_object* v_a_2857_; 
lean_dec_ref(v___x_2796_);
lean_del_object(v___x_2788_);
lean_dec_ref(v_proof_2785_);
lean_dec_ref(v_e_x27_2784_);
lean_dec_ref_known(v_e_2278_, 3);
v_a_2857_ = lean_ctor_get(v___x_2797_, 0);
lean_inc(v_a_2857_);
lean_dec_ref_known(v___x_2797_, 1);
v___y_2621_ = v___x_2758_;
v___y_2622_ = v_a_2654_;
v_a_2623_ = v_a_2857_;
goto v___jp_2620_;
}
}
else
{
lean_object* v_a_2858_; 
lean_del_object(v___x_2788_);
lean_dec_ref(v_proof_2785_);
lean_dec_ref(v_e_x27_2784_);
lean_dec_ref_known(v_e_2278_, 3);
v_a_2858_ = lean_ctor_get(v___x_2790_, 0);
lean_inc(v_a_2858_);
lean_dec_ref_known(v___x_2790_, 1);
v___y_2621_ = v___x_2758_;
v___y_2622_ = v_a_2654_;
v_a_2623_ = v_a_2858_;
goto v___jp_2620_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_2278_, 3);
v___y_2639_ = v___x_2758_;
v___y_2640_ = v_a_2654_;
v___y_2641_ = v___x_2759_;
goto v___jp_2638_;
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
lean_object* v_e_x27_2376_; lean_object* v_proof_2377_; uint8_t v_contextDependent_2378_; lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2550_; 
v_e_x27_2376_ = lean_ctor_get(v_res_2307_, 0);
v_proof_2377_ = lean_ctor_get(v_res_2307_, 1);
v_contextDependent_2378_ = lean_ctor_get_uint8(v_res_2307_, sizeof(void*)*2 + 1);
v_isSharedCheck_2550_ = !lean_is_exclusive(v_res_2307_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2380_ = v_res_2307_;
v_isShared_2381_ = v_isSharedCheck_2550_;
goto v_resetjp_2379_;
}
else
{
lean_inc(v_proof_2377_);
lean_inc(v_e_x27_2376_);
lean_dec(v_res_2307_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2550_;
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
lean_object* v_a_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2443_; 
v_a_2398_ = lean_ctor_get(v___x_2397_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v___x_2397_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2400_ = v___x_2397_;
v_isShared_2401_ = v_isSharedCheck_2443_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_a_2398_);
lean_dec(v___x_2397_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2443_;
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
lean_object* v_a_2413_; size_t v___x_2414_; size_t v___x_2415_; uint8_t v___x_2416_; 
v_a_2413_ = lean_ctor_get(v___x_2412_, 0);
lean_inc(v_a_2413_);
lean_dec_ref_known(v___x_2412_, 1);
v___x_2414_ = lean_ptr_addr(v_struct_2305_);
v___x_2415_ = lean_ptr_addr(v_e_x27_2376_);
v___x_2416_ = lean_usize_dec_eq(v___x_2414_, v___x_2415_);
if (v___x_2416_ == 0)
{
lean_object* v___x_2417_; 
lean_inc(v_idx_2304_);
lean_inc(v_typeName_2303_);
lean_dec_ref_known(v_e_2278_, 3);
v___x_2417_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_typeName_2303_, v_idx_2304_, v_e_x27_2376_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
if (lean_obj_tag(v___x_2417_) == 0)
{
lean_object* v_a_2418_; 
v_a_2418_ = lean_ctor_get(v___x_2417_, 0);
lean_inc(v_a_2418_);
lean_dec_ref_known(v___x_2417_, 1);
v___y_2290_ = v___x_2391_;
v___y_2291_ = v_contextDependent_2378_;
v___y_2292_ = v_a_2413_;
v_a_2293_ = v_a_2418_;
goto v___jp_2289_;
}
else
{
lean_object* v_a_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2426_; 
lean_dec(v_a_2413_);
v_a_2419_ = lean_ctor_get(v___x_2417_, 0);
v_isSharedCheck_2426_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2421_ = v___x_2417_;
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_a_2419_);
lean_dec(v___x_2417_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v___x_2424_; 
if (v_isShared_2422_ == 0)
{
v___x_2424_ = v___x_2421_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v_a_2419_);
v___x_2424_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
return v___x_2424_;
}
}
}
}
else
{
lean_dec_ref(v_e_x27_2376_);
v___y_2290_ = v___x_2391_;
v___y_2291_ = v_contextDependent_2378_;
v___y_2292_ = v_a_2413_;
v_a_2293_ = v_e_2278_;
goto v___jp_2289_;
}
}
else
{
lean_object* v_a_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2434_; 
lean_dec_ref(v_e_x27_2376_);
lean_dec_ref_known(v_e_2278_, 3);
v_a_2427_ = lean_ctor_get(v___x_2412_, 0);
v_isSharedCheck_2434_ = !lean_is_exclusive(v___x_2412_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2429_ = v___x_2412_;
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_a_2427_);
lean_dec(v___x_2412_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v___x_2432_; 
if (v_isShared_2430_ == 0)
{
v___x_2432_ = v___x_2429_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v_a_2427_);
v___x_2432_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
return v___x_2432_;
}
}
}
}
else
{
lean_object* v_a_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2442_; 
lean_dec_ref(v_proof_2377_);
lean_dec_ref(v_e_x27_2376_);
lean_dec_ref_known(v_e_2278_, 3);
v_a_2435_ = lean_ctor_get(v___x_2408_, 0);
v_isSharedCheck_2442_ = !lean_is_exclusive(v___x_2408_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2437_ = v___x_2408_;
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_a_2435_);
lean_dec(v___x_2408_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v___x_2440_; 
if (v_isShared_2438_ == 0)
{
v___x_2440_ = v___x_2437_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v_a_2435_);
v___x_2440_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
return v___x_2440_;
}
}
}
}
}
}
else
{
lean_object* v_a_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2451_; 
lean_dec_ref(v___x_2388_);
lean_dec_ref(v_proof_2377_);
lean_dec_ref(v_e_x27_2376_);
lean_dec_ref_known(v_e_2278_, 3);
v_a_2444_ = lean_ctor_get(v___x_2397_, 0);
v_isSharedCheck_2451_ = !lean_is_exclusive(v___x_2397_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2446_ = v___x_2397_;
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_a_2444_);
lean_dec(v___x_2397_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v___x_2449_; 
if (v_isShared_2447_ == 0)
{
v___x_2449_ = v___x_2446_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v_a_2444_);
v___x_2449_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
return v___x_2449_;
}
}
}
}
else
{
lean_object* v_val_2452_; lean_object* v___x_2453_; 
lean_dec_ref(v___x_2388_);
lean_dec_ref(v_proof_2377_);
lean_dec_ref(v_e_x27_2376_);
lean_dec_ref_known(v_e_2278_, 3);
v_val_2452_ = lean_ctor_get(v_a_2396_, 0);
lean_inc(v_val_2452_);
lean_dec_ref_known(v_a_2396_, 1);
v___x_2453_ = l_Lean_Meta_Sym_shareCommonInc(v_val_2452_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
if (lean_obj_tag(v___x_2453_) == 0)
{
lean_object* v_a_2454_; lean_object* v___x_2455_; 
v_a_2454_ = lean_ctor_get(v___x_2453_, 0);
lean_inc_n(v_a_2454_, 2);
lean_dec_ref_known(v___x_2453_, 1);
v___x_2455_ = l_Lean_Meta_Sym_mkEqRefl(v_a_2454_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
if (lean_obj_tag(v___x_2455_) == 0)
{
lean_object* v_a_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2466_; 
v_a_2456_ = lean_ctor_get(v___x_2455_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2455_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2458_ = v___x_2455_;
v_isShared_2459_ = v_isSharedCheck_2466_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_a_2456_);
lean_dec(v___x_2455_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2466_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v___x_2461_; 
if (v_isShared_2381_ == 0)
{
lean_ctor_set(v___x_2380_, 1, v_a_2456_);
lean_ctor_set(v___x_2380_, 0, v_a_2454_);
v___x_2461_ = v___x_2380_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v_a_2454_);
lean_ctor_set(v_reuseFailAlloc_2465_, 1, v_a_2456_);
v___x_2461_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
lean_object* v___x_2463_; 
lean_ctor_set_uint8(v___x_2461_, sizeof(void*)*2, v_contextDependent_2378_);
lean_ctor_set_uint8(v___x_2461_, sizeof(void*)*2 + 1, v___x_2391_);
if (v_isShared_2459_ == 0)
{
lean_ctor_set(v___x_2458_, 0, v___x_2461_);
v___x_2463_ = v___x_2458_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v___x_2461_);
v___x_2463_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
return v___x_2463_;
}
}
}
}
else
{
lean_object* v_a_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2474_; 
lean_dec(v_a_2454_);
lean_del_object(v___x_2380_);
v_a_2467_ = lean_ctor_get(v___x_2455_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2455_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2469_ = v___x_2455_;
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_a_2467_);
lean_dec(v___x_2455_);
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
lean_del_object(v___x_2380_);
v_a_2475_ = lean_ctor_get(v___x_2453_, 0);
v_isSharedCheck_2482_ = !lean_is_exclusive(v___x_2453_);
if (v_isSharedCheck_2482_ == 0)
{
v___x_2477_ = v___x_2453_;
v_isShared_2478_ = v_isSharedCheck_2482_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_a_2475_);
lean_dec(v___x_2453_);
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
else
{
lean_object* v_a_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2490_; 
lean_dec_ref(v___x_2388_);
lean_del_object(v___x_2380_);
lean_dec_ref(v_proof_2377_);
lean_dec_ref(v_e_x27_2376_);
lean_dec_ref_known(v_e_2278_, 3);
v_a_2483_ = lean_ctor_get(v___x_2395_, 0);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2395_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2485_ = v___x_2395_;
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_a_2483_);
lean_dec(v___x_2395_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2488_; 
if (v_isShared_2486_ == 0)
{
v___x_2488_ = v___x_2485_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_a_2483_);
v___x_2488_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
return v___x_2488_;
}
}
}
}
else
{
lean_del_object(v___x_2380_);
if (lean_obj_tag(v_a_2390_) == 7)
{
lean_object* v_binderType_2491_; lean_object* v_body_2492_; lean_object* v___x_2493_; 
v_binderType_2491_ = lean_ctor_get(v_a_2390_, 1);
lean_inc_ref_n(v_binderType_2491_, 2);
v_body_2492_ = lean_ctor_get(v_a_2390_, 2);
lean_inc_ref(v_body_2492_);
lean_dec_ref_known(v_a_2390_, 3);
v___x_2493_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_2491_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
if (lean_obj_tag(v___x_2493_) == 0)
{
lean_object* v_a_2494_; lean_object* v___x_2495_; 
v_a_2494_ = lean_ctor_get(v___x_2493_, 0);
lean_inc(v_a_2494_);
lean_dec_ref_known(v___x_2493_, 1);
lean_inc_ref(v_body_2492_);
v___x_2495_ = l_Lean_Meta_Sym_getLevel___redArg(v_body_2492_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
if (lean_obj_tag(v___x_2495_) == 0)
{
lean_object* v_a_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; size_t v___x_2503_; size_t v___x_2504_; uint8_t v___x_2505_; 
v_a_2496_ = lean_ctor_get(v___x_2495_, 0);
lean_inc(v_a_2496_);
lean_dec_ref_known(v___x_2495_, 1);
v___x_2497_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4));
v___x_2498_ = lean_box(0);
v___x_2499_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2499_, 0, v_a_2496_);
lean_ctor_set(v___x_2499_, 1, v___x_2498_);
v___x_2500_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2500_, 0, v_a_2494_);
lean_ctor_set(v___x_2500_, 1, v___x_2499_);
v___x_2501_ = l_Lean_mkConst(v___x_2497_, v___x_2500_);
lean_inc_ref(v_e_x27_2376_);
lean_inc_ref(v_struct_2305_);
v___x_2502_ = l_Lean_mkApp6(v___x_2501_, v_binderType_2491_, v_body_2492_, v_struct_2305_, v_e_x27_2376_, v___x_2388_, v_proof_2377_);
v___x_2503_ = lean_ptr_addr(v_struct_2305_);
v___x_2504_ = lean_ptr_addr(v_e_x27_2376_);
v___x_2505_ = lean_usize_dec_eq(v___x_2503_, v___x_2504_);
if (v___x_2505_ == 0)
{
lean_object* v___x_2506_; 
lean_inc(v_idx_2304_);
lean_inc(v_typeName_2303_);
lean_dec_ref_known(v_e_2278_, 3);
v___x_2506_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_typeName_2303_, v_idx_2304_, v_e_x27_2376_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
if (lean_obj_tag(v___x_2506_) == 0)
{
lean_object* v_a_2507_; 
v_a_2507_ = lean_ctor_get(v___x_2506_, 0);
lean_inc(v_a_2507_);
lean_dec_ref_known(v___x_2506_, 1);
v___y_2297_ = v___x_2502_;
v___y_2298_ = v_contextDependent_2378_;
v_a_2299_ = v_a_2507_;
goto v___jp_2296_;
}
else
{
lean_object* v_a_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2515_; 
lean_dec_ref(v___x_2502_);
v_a_2508_ = lean_ctor_get(v___x_2506_, 0);
v_isSharedCheck_2515_ = !lean_is_exclusive(v___x_2506_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2510_ = v___x_2506_;
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_a_2508_);
lean_dec(v___x_2506_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v___x_2513_; 
if (v_isShared_2511_ == 0)
{
v___x_2513_ = v___x_2510_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_a_2508_);
v___x_2513_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
return v___x_2513_;
}
}
}
}
else
{
lean_dec_ref(v_e_x27_2376_);
v___y_2297_ = v___x_2502_;
v___y_2298_ = v_contextDependent_2378_;
v_a_2299_ = v_e_2278_;
goto v___jp_2296_;
}
}
else
{
lean_object* v_a_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2523_; 
lean_dec(v_a_2494_);
lean_dec_ref(v_body_2492_);
lean_dec_ref(v_binderType_2491_);
lean_dec_ref(v___x_2388_);
lean_dec_ref(v_proof_2377_);
lean_dec_ref(v_e_x27_2376_);
lean_dec_ref_known(v_e_2278_, 3);
v_a_2516_ = lean_ctor_get(v___x_2495_, 0);
v_isSharedCheck_2523_ = !lean_is_exclusive(v___x_2495_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2518_ = v___x_2495_;
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_a_2516_);
lean_dec(v___x_2495_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2521_; 
if (v_isShared_2519_ == 0)
{
v___x_2521_ = v___x_2518_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_a_2516_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
return v___x_2521_;
}
}
}
}
else
{
lean_object* v_a_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2531_; 
lean_dec_ref(v_body_2492_);
lean_dec_ref(v_binderType_2491_);
lean_dec_ref(v___x_2388_);
lean_dec_ref(v_proof_2377_);
lean_dec_ref(v_e_x27_2376_);
lean_dec_ref_known(v_e_2278_, 3);
v_a_2524_ = lean_ctor_get(v___x_2493_, 0);
v_isSharedCheck_2531_ = !lean_is_exclusive(v___x_2493_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2526_ = v___x_2493_;
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_a_2524_);
lean_dec(v___x_2493_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2529_; 
if (v_isShared_2527_ == 0)
{
v___x_2529_ = v___x_2526_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_a_2524_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
}
else
{
lean_object* v___x_2532_; lean_object* v___x_2533_; 
lean_dec(v_a_2390_);
lean_dec_ref(v___x_2388_);
lean_dec_ref(v_proof_2377_);
lean_dec_ref(v_e_x27_2376_);
lean_dec_ref_known(v_e_2278_, 3);
v___x_2532_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8);
v___x_2533_ = l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1(v___x_2532_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
return v___x_2533_;
}
}
}
else
{
lean_object* v_a_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2541_; 
lean_dec_ref(v___x_2388_);
lean_del_object(v___x_2380_);
lean_dec_ref(v_proof_2377_);
lean_dec_ref(v_e_x27_2376_);
lean_dec_ref_known(v_e_2278_, 3);
v_a_2534_ = lean_ctor_get(v___x_2389_, 0);
v_isSharedCheck_2541_ = !lean_is_exclusive(v___x_2389_);
if (v_isSharedCheck_2541_ == 0)
{
v___x_2536_ = v___x_2389_;
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_a_2534_);
lean_dec(v___x_2389_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2541_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
lean_object* v___x_2539_; 
if (v_isShared_2537_ == 0)
{
v___x_2539_ = v___x_2536_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v_a_2534_);
v___x_2539_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
return v___x_2539_;
}
}
}
}
else
{
lean_object* v_a_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2549_; 
lean_del_object(v___x_2380_);
lean_dec_ref(v_proof_2377_);
lean_dec_ref(v_e_x27_2376_);
lean_dec_ref_known(v_e_2278_, 3);
v_a_2542_ = lean_ctor_get(v___x_2382_, 0);
v_isSharedCheck_2549_ = !lean_is_exclusive(v___x_2382_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2544_ = v___x_2382_;
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_a_2542_);
lean_dec(v___x_2382_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v___x_2547_; 
if (v_isShared_2545_ == 0)
{
v___x_2547_ = v___x_2544_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_a_2542_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
return v___x_2547_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2864_; lean_object* v___x_2865_; 
lean_dec_ref(v_e_2278_);
v___x_2864_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
v___x_2865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2865_, 0, v___x_2864_);
return v___x_2865_;
}
v___jp_2289_:
{
lean_object* v___x_2294_; lean_object* v___x_2295_; 
v___x_2294_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2294_, 0, v_a_2293_);
lean_ctor_set(v___x_2294_, 1, v___y_2292_);
lean_ctor_set_uint8(v___x_2294_, sizeof(void*)*2, v___y_2291_);
lean_ctor_set_uint8(v___x_2294_, sizeof(void*)*2 + 1, v___y_2290_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___boxed(lean_object* v_e_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_){
_start:
{
lean_object* v_res_2877_; 
v_res_2877_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj(v_e_2866_, v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_, v_a_2875_);
lean_dec(v_a_2875_);
lean_dec_ref(v_a_2874_);
lean_dec(v_a_2873_);
lean_dec_ref(v_a_2872_);
lean_dec(v_a_2871_);
lean_dec_ref(v_a_2870_);
lean_dec(v_a_2869_);
lean_dec_ref(v_a_2868_);
lean_dec(v_a_2867_);
return v_res_2877_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5(lean_object* v_00_u03b1_2878_, lean_object* v_x_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_){
_start:
{
lean_object* v___x_2890_; 
v___x_2890_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5___redArg(v_x_2879_);
return v___x_2890_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5___boxed(lean_object* v_00_u03b1_2891_, lean_object* v_x_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_){
_start:
{
lean_object* v_res_2903_; 
v_res_2903_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5(v_00_u03b1_2891_, v_x_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
lean_dec(v___y_2901_);
lean_dec_ref(v___y_2900_);
lean_dec(v___y_2899_);
lean_dec_ref(v___y_2898_);
lean_dec(v___y_2897_);
lean_dec_ref(v___y_2896_);
lean_dec(v___y_2895_);
lean_dec_ref(v___y_2894_);
lean_dec(v___y_2893_);
return v_res_2903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4(lean_object* v_oldTraces_2904_, lean_object* v_data_2905_, lean_object* v_ref_2906_, lean_object* v_msg_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_){
_start:
{
lean_object* v___x_2918_; 
v___x_2918_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4___redArg(v_oldTraces_2904_, v_data_2905_, v_ref_2906_, v_msg_2907_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_);
return v___x_2918_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4___boxed(lean_object* v_oldTraces_2919_, lean_object* v_data_2920_, lean_object* v_ref_2921_, lean_object* v_msg_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_){
_start:
{
lean_object* v_res_2933_; 
v_res_2933_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4(v_oldTraces_2919_, v_data_2920_, v_ref_2921_, v_msg_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_);
lean_dec(v___y_2931_);
lean_dec_ref(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v___y_2927_);
lean_dec_ref(v___y_2926_);
lean_dec(v___y_2925_);
lean_dec_ref(v___y_2924_);
lean_dec(v___y_2923_);
return v_res_2933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0_spec__1___redArg(lean_object* v_f_2934_, lean_object* v_a_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_){
_start:
{
lean_object* v___y_2944_; lean_object* v___x_2947_; uint8_t v_debug_2948_; 
v___x_2947_ = lean_st_ref_get(v___y_2937_);
v_debug_2948_ = lean_ctor_get_uint8(v___x_2947_, sizeof(void*)*11);
lean_dec(v___x_2947_);
if (v_debug_2948_ == 0)
{
v___y_2944_ = v___y_2937_;
goto v___jp_2943_;
}
else
{
lean_object* v___x_2949_; 
lean_inc_ref(v_f_2934_);
v___x_2949_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_2934_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_);
if (lean_obj_tag(v___x_2949_) == 0)
{
lean_object* v___x_2950_; 
lean_dec_ref_known(v___x_2949_, 1);
lean_inc_ref(v_a_2935_);
v___x_2950_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_);
if (lean_obj_tag(v___x_2950_) == 0)
{
lean_dec_ref_known(v___x_2950_, 1);
v___y_2944_ = v___y_2937_;
goto v___jp_2943_;
}
else
{
lean_object* v_a_2951_; lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_2958_; 
lean_dec_ref(v_a_2935_);
lean_dec_ref(v_f_2934_);
v_a_2951_ = lean_ctor_get(v___x_2950_, 0);
v_isSharedCheck_2958_ = !lean_is_exclusive(v___x_2950_);
if (v_isSharedCheck_2958_ == 0)
{
v___x_2953_ = v___x_2950_;
v_isShared_2954_ = v_isSharedCheck_2958_;
goto v_resetjp_2952_;
}
else
{
lean_inc(v_a_2951_);
lean_dec(v___x_2950_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_2958_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
lean_object* v___x_2956_; 
if (v_isShared_2954_ == 0)
{
v___x_2956_ = v___x_2953_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v_a_2951_);
v___x_2956_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
return v___x_2956_;
}
}
}
}
else
{
lean_object* v_a_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2966_; 
lean_dec_ref(v_a_2935_);
lean_dec_ref(v_f_2934_);
v_a_2959_ = lean_ctor_get(v___x_2949_, 0);
v_isSharedCheck_2966_ = !lean_is_exclusive(v___x_2949_);
if (v_isSharedCheck_2966_ == 0)
{
v___x_2961_ = v___x_2949_;
v_isShared_2962_ = v_isSharedCheck_2966_;
goto v_resetjp_2960_;
}
else
{
lean_inc(v_a_2959_);
lean_dec(v___x_2949_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_2966_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
lean_object* v___x_2964_; 
if (v_isShared_2962_ == 0)
{
v___x_2964_ = v___x_2961_;
goto v_reusejp_2963_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v_a_2959_);
v___x_2964_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2963_;
}
v_reusejp_2963_:
{
return v___x_2964_;
}
}
}
}
v___jp_2943_:
{
lean_object* v___x_2945_; lean_object* v___x_2946_; 
v___x_2945_ = l_Lean_Expr_app___override(v_f_2934_, v_a_2935_);
v___x_2946_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2945_, v___y_2944_);
return v___x_2946_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_2967_, lean_object* v_a_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_){
_start:
{
lean_object* v_res_2976_; 
v_res_2976_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0_spec__1___redArg(v_f_2967_, v_a_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_);
lean_dec(v___y_2974_);
lean_dec_ref(v___y_2973_);
lean_dec(v___y_2972_);
lean_dec_ref(v___y_2971_);
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
return v_res_2976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0(lean_object* v_args_2977_, lean_object* v_endIdx_2978_, lean_object* v_b_2979_, lean_object* v_i_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_){
_start:
{
uint8_t v___x_2991_; 
v___x_2991_ = lean_nat_dec_le(v_endIdx_2978_, v_i_2980_);
if (v___x_2991_ == 0)
{
lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; 
v___x_2992_ = l_Lean_instInhabitedExpr;
v___x_2993_ = lean_array_get_borrowed(v___x_2992_, v_args_2977_, v_i_2980_);
lean_inc(v___x_2993_);
v___x_2994_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0_spec__1___redArg(v_b_2979_, v___x_2993_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_);
if (lean_obj_tag(v___x_2994_) == 0)
{
lean_object* v_a_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; 
v_a_2995_ = lean_ctor_get(v___x_2994_, 0);
lean_inc(v_a_2995_);
lean_dec_ref_known(v___x_2994_, 1);
v___x_2996_ = lean_unsigned_to_nat(1u);
v___x_2997_ = lean_nat_add(v_i_2980_, v___x_2996_);
lean_dec(v_i_2980_);
v_b_2979_ = v_a_2995_;
v_i_2980_ = v___x_2997_;
goto _start;
}
else
{
lean_dec(v_i_2980_);
return v___x_2994_;
}
}
else
{
lean_object* v___x_2999_; 
lean_dec(v_i_2980_);
v___x_2999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2999_, 0, v_b_2979_);
return v___x_2999_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0___boxed(lean_object* v_args_3000_, lean_object* v_endIdx_3001_, lean_object* v_b_3002_, lean_object* v_i_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_){
_start:
{
lean_object* v_res_3014_; 
v_res_3014_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0(v_args_3000_, v_endIdx_3001_, v_b_3002_, v_i_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_);
lean_dec(v___y_3012_);
lean_dec_ref(v___y_3011_);
lean_dec(v___y_3010_);
lean_dec_ref(v___y_3009_);
lean_dec(v___y_3008_);
lean_dec_ref(v___y_3007_);
lean_dec(v___y_3006_);
lean_dec_ref(v___y_3005_);
lean_dec(v___y_3004_);
lean_dec(v_endIdx_3001_);
lean_dec_ref(v_args_3000_);
return v_res_3014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0(lean_object* v_f_3015_, lean_object* v_args_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_){
_start:
{
lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; 
v___x_3027_ = lean_unsigned_to_nat(0u);
v___x_3028_ = lean_array_get_size(v_args_3016_);
v___x_3029_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0(v_args_3016_, v___x_3028_, v_f_3015_, v___x_3027_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_);
return v___x_3029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0___boxed(lean_object* v_f_3030_, lean_object* v_args_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_){
_start:
{
lean_object* v_res_3042_; 
v_res_3042_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0(v_f_3030_, v_args_3031_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_);
lean_dec(v___y_3040_);
lean_dec_ref(v___y_3039_);
lean_dec(v___y_3038_);
lean_dec_ref(v___y_3037_);
lean_dec(v___y_3036_);
lean_dec_ref(v___y_3035_);
lean_dec(v___y_3034_);
lean_dec_ref(v___y_3033_);
lean_dec(v___y_3032_);
lean_dec_ref(v_args_3031_);
return v_res_3042_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__0(void){
_start:
{
lean_object* v___x_3043_; lean_object* v_dummy_3044_; 
v___x_3043_ = lean_box(0);
v_dummy_3044_ = l_Lean_Expr_sort___override(v___x_3043_);
return v_dummy_3044_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__2(void){
_start:
{
lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3046_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__1));
v___x_3047_ = l_Lean_stringToMessageData(v___x_3046_);
return v___x_3047_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn(lean_object* v_e_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_, lean_object* v_a_3057_){
_start:
{
uint8_t v___x_3062_; 
v___x_3062_ = l_Lean_Expr_isApp(v_e_3048_);
if (v___x_3062_ == 0)
{
lean_object* v___x_3063_; lean_object* v___x_3064_; 
lean_dec_ref(v_e_3048_);
v___x_3063_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_3063_, 0, v___x_3062_);
lean_ctor_set_uint8(v___x_3063_, 1, v___x_3062_);
v___x_3064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3064_, 0, v___x_3063_);
return v___x_3064_;
}
else
{
lean_object* v_fn_3065_; uint8_t v___x_3066_; 
v_fn_3065_ = l_Lean_Expr_getAppFn(v_e_3048_);
v___x_3066_ = l_Lean_Expr_isLambda(v_fn_3065_);
if (v___x_3066_ == 0)
{
uint8_t v___x_3067_; 
v___x_3067_ = l_Lean_Expr_isConst(v_fn_3065_);
if (v___x_3067_ == 0)
{
lean_object* v___x_3068_; 
lean_inc(v_a_3057_);
lean_inc_ref(v_a_3056_);
lean_inc(v_a_3055_);
lean_inc_ref(v_a_3054_);
lean_inc(v_a_3053_);
lean_inc_ref(v_a_3052_);
lean_inc(v_a_3051_);
lean_inc_ref(v_a_3050_);
lean_inc(v_a_3049_);
lean_inc_ref(v_fn_3065_);
v___x_3068_ = lean_sym_simp(v_fn_3065_, v_a_3049_, v_a_3050_, v_a_3051_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3055_, v_a_3056_, v_a_3057_);
if (lean_obj_tag(v___x_3068_) == 0)
{
lean_object* v_a_3069_; 
v_a_3069_ = lean_ctor_get(v___x_3068_, 0);
lean_inc(v_a_3069_);
if (lean_obj_tag(v_a_3069_) == 0)
{
lean_dec_ref_known(v_a_3069_, 0);
lean_dec_ref(v_fn_3065_);
lean_dec_ref(v_e_3048_);
return v___x_3068_;
}
else
{
lean_object* v_e_x27_3070_; lean_object* v_proof_3071_; uint8_t v_contextDependent_3072_; lean_object* v___x_3074_; uint8_t v_isShared_3075_; uint8_t v_isSharedCheck_3176_; 
lean_dec_ref_known(v___x_3068_, 1);
v_e_x27_3070_ = lean_ctor_get(v_a_3069_, 0);
v_proof_3071_ = lean_ctor_get(v_a_3069_, 1);
v_contextDependent_3072_ = lean_ctor_get_uint8(v_a_3069_, sizeof(void*)*2 + 1);
v_isSharedCheck_3176_ = !lean_is_exclusive(v_a_3069_);
if (v_isSharedCheck_3176_ == 0)
{
v___x_3074_ = v_a_3069_;
v_isShared_3075_ = v_isSharedCheck_3176_;
goto v_resetjp_3073_;
}
else
{
lean_inc(v_proof_3071_);
lean_inc(v_e_x27_3070_);
lean_dec(v_a_3069_);
v___x_3074_ = lean_box(0);
v_isShared_3075_ = v_isSharedCheck_3176_;
goto v_resetjp_3073_;
}
v_resetjp_3073_:
{
lean_object* v___x_3076_; 
lean_inc_ref(v_e_x27_3070_);
v___x_3076_ = l_Lean_Meta_Sym_inferType(v_e_x27_3070_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3055_, v_a_3056_, v_a_3057_);
if (lean_obj_tag(v___x_3076_) == 0)
{
lean_object* v_a_3077_; lean_object* v___x_3078_; lean_object* v_dummy_3079_; lean_object* v_nargs_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; 
v_a_3077_ = lean_ctor_get(v___x_3076_, 0);
lean_inc(v_a_3077_);
lean_dec_ref_known(v___x_3076_, 1);
v___x_3078_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2);
v_dummy_3079_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__0, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__0_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__0);
v_nargs_3080_ = l_Lean_Expr_getAppNumArgs(v_e_3048_);
lean_inc(v_nargs_3080_);
v___x_3081_ = lean_mk_array(v_nargs_3080_, v_dummy_3079_);
v___x_3082_ = lean_unsigned_to_nat(1u);
v___x_3083_ = lean_nat_sub(v_nargs_3080_, v___x_3082_);
lean_dec(v_nargs_3080_);
lean_inc_ref(v_e_3048_);
v___x_3084_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3048_, v___x_3081_, v___x_3083_);
v___x_3085_ = l_Lean_mkAppN(v___x_3078_, v___x_3084_);
lean_inc_ref(v_e_x27_3070_);
v___x_3086_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0(v_e_x27_3070_, v___x_3084_, v_a_3049_, v_a_3050_, v_a_3051_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3055_, v_a_3056_, v_a_3057_);
lean_dec_ref(v___x_3084_);
if (lean_obj_tag(v___x_3086_) == 0)
{
lean_object* v_a_3087_; lean_object* v___x_3088_; 
v_a_3087_ = lean_ctor_get(v___x_3086_, 0);
lean_inc(v_a_3087_);
lean_dec_ref_known(v___x_3086_, 1);
lean_inc_ref(v_e_3048_);
v___x_3088_ = l_Lean_Meta_Sym_inferType(v_e_3048_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3055_, v_a_3056_, v_a_3057_);
if (lean_obj_tag(v___x_3088_) == 0)
{
lean_object* v_a_3089_; lean_object* v___x_3090_; uint8_t v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; 
v_a_3089_ = lean_ctor_get(v___x_3088_, 0);
lean_inc(v_a_3089_);
lean_dec_ref_known(v___x_3088_, 1);
v___x_3090_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__1));
v___x_3091_ = 0;
lean_inc_n(v_a_3077_, 2);
v___x_3092_ = l_Lean_mkLambda(v___x_3090_, v___x_3091_, v_a_3077_, v___x_3085_);
v___x_3093_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_3077_, v_a_3053_, v_a_3054_, v_a_3055_, v_a_3056_, v_a_3057_);
if (lean_obj_tag(v___x_3093_) == 0)
{
lean_object* v_a_3094_; lean_object* v___x_3095_; 
v_a_3094_ = lean_ctor_get(v___x_3093_, 0);
lean_inc(v_a_3094_);
lean_dec_ref_known(v___x_3093_, 1);
lean_inc(v_a_3089_);
v___x_3095_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_3089_, v_a_3053_, v_a_3054_, v_a_3055_, v_a_3056_, v_a_3057_);
if (lean_obj_tag(v___x_3095_) == 0)
{
lean_object* v_options_3096_; lean_object* v_a_3097_; lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3135_; 
v_options_3096_ = lean_ctor_get(v_a_3056_, 2);
v_a_3097_ = lean_ctor_get(v___x_3095_, 0);
v_isSharedCheck_3135_ = !lean_is_exclusive(v___x_3095_);
if (v_isSharedCheck_3135_ == 0)
{
v___x_3099_ = v___x_3095_;
v_isShared_3100_ = v_isSharedCheck_3135_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_a_3097_);
lean_dec(v___x_3095_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3135_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v_inheritedTraceOptions_3101_; uint8_t v_hasTrace_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; 
v_inheritedTraceOptions_3101_ = lean_ctor_get(v_a_3056_, 13);
v_hasTrace_3102_ = lean_ctor_get_uint8(v_options_3096_, sizeof(void*)*1);
v___x_3103_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4));
v___x_3104_ = lean_box(0);
v___x_3105_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3105_, 0, v_a_3097_);
lean_ctor_set(v___x_3105_, 1, v___x_3104_);
v___x_3106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3106_, 0, v_a_3094_);
lean_ctor_set(v___x_3106_, 1, v___x_3105_);
v___x_3107_ = l_Lean_mkConst(v___x_3103_, v___x_3106_);
v___x_3108_ = l_Lean_mkApp6(v___x_3107_, v_a_3077_, v_a_3089_, v_fn_3065_, v_e_x27_3070_, v___x_3092_, v_proof_3071_);
if (v_hasTrace_3102_ == 0)
{
lean_dec_ref(v_e_3048_);
goto v___jp_3109_;
}
else
{
lean_object* v___x_3116_; lean_object* v___x_3117_; uint8_t v___x_3118_; 
v___x_3116_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2));
v___x_3117_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3);
v___x_3118_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3101_, v_options_3096_, v___x_3117_);
if (v___x_3118_ == 0)
{
lean_dec_ref(v_e_3048_);
goto v___jp_3109_;
}
else
{
lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; 
v___x_3119_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__2, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__2);
v___x_3120_ = l_Lean_indentExpr(v_e_3048_);
v___x_3121_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3121_, 0, v___x_3119_);
lean_ctor_set(v___x_3121_, 1, v___x_3120_);
v___x_3122_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_3123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3123_, 0, v___x_3121_);
lean_ctor_set(v___x_3123_, 1, v___x_3122_);
lean_inc(v_a_3087_);
v___x_3124_ = l_Lean_indentExpr(v_a_3087_);
v___x_3125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3125_, 0, v___x_3123_);
lean_ctor_set(v___x_3125_, 1, v___x_3124_);
v___x_3126_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(v___x_3116_, v___x_3125_, v_a_3054_, v_a_3055_, v_a_3056_, v_a_3057_);
if (lean_obj_tag(v___x_3126_) == 0)
{
lean_dec_ref_known(v___x_3126_, 1);
goto v___jp_3109_;
}
else
{
lean_object* v_a_3127_; lean_object* v___x_3129_; uint8_t v_isShared_3130_; uint8_t v_isSharedCheck_3134_; 
lean_dec_ref(v___x_3108_);
lean_del_object(v___x_3099_);
lean_dec(v_a_3087_);
lean_del_object(v___x_3074_);
v_a_3127_ = lean_ctor_get(v___x_3126_, 0);
v_isSharedCheck_3134_ = !lean_is_exclusive(v___x_3126_);
if (v_isSharedCheck_3134_ == 0)
{
v___x_3129_ = v___x_3126_;
v_isShared_3130_ = v_isSharedCheck_3134_;
goto v_resetjp_3128_;
}
else
{
lean_inc(v_a_3127_);
lean_dec(v___x_3126_);
v___x_3129_ = lean_box(0);
v_isShared_3130_ = v_isSharedCheck_3134_;
goto v_resetjp_3128_;
}
v_resetjp_3128_:
{
lean_object* v___x_3132_; 
if (v_isShared_3130_ == 0)
{
v___x_3132_ = v___x_3129_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v_a_3127_);
v___x_3132_ = v_reuseFailAlloc_3133_;
goto v_reusejp_3131_;
}
v_reusejp_3131_:
{
return v___x_3132_;
}
}
}
}
}
v___jp_3109_:
{
lean_object* v___x_3111_; 
if (v_isShared_3075_ == 0)
{
lean_ctor_set(v___x_3074_, 1, v___x_3108_);
lean_ctor_set(v___x_3074_, 0, v_a_3087_);
v___x_3111_ = v___x_3074_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v_a_3087_);
lean_ctor_set(v_reuseFailAlloc_3115_, 1, v___x_3108_);
v___x_3111_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3110_;
}
v_reusejp_3110_:
{
lean_object* v___x_3113_; 
lean_ctor_set_uint8(v___x_3111_, sizeof(void*)*2, v_contextDependent_3072_);
lean_ctor_set_uint8(v___x_3111_, sizeof(void*)*2 + 1, v___x_3067_);
if (v_isShared_3100_ == 0)
{
lean_ctor_set(v___x_3099_, 0, v___x_3111_);
v___x_3113_ = v___x_3099_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v___x_3111_);
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
else
{
lean_object* v_a_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3143_; 
lean_dec(v_a_3094_);
lean_dec_ref(v___x_3092_);
lean_dec(v_a_3089_);
lean_dec(v_a_3087_);
lean_dec(v_a_3077_);
lean_del_object(v___x_3074_);
lean_dec_ref(v_proof_3071_);
lean_dec_ref(v_e_x27_3070_);
lean_dec_ref(v_fn_3065_);
lean_dec_ref(v_e_3048_);
v_a_3136_ = lean_ctor_get(v___x_3095_, 0);
v_isSharedCheck_3143_ = !lean_is_exclusive(v___x_3095_);
if (v_isSharedCheck_3143_ == 0)
{
v___x_3138_ = v___x_3095_;
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_a_3136_);
lean_dec(v___x_3095_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v___x_3141_; 
if (v_isShared_3139_ == 0)
{
v___x_3141_ = v___x_3138_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v_a_3136_);
v___x_3141_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
return v___x_3141_;
}
}
}
}
else
{
lean_object* v_a_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3151_; 
lean_dec_ref(v___x_3092_);
lean_dec(v_a_3089_);
lean_dec(v_a_3087_);
lean_dec(v_a_3077_);
lean_del_object(v___x_3074_);
lean_dec_ref(v_proof_3071_);
lean_dec_ref(v_e_x27_3070_);
lean_dec_ref(v_fn_3065_);
lean_dec_ref(v_e_3048_);
v_a_3144_ = lean_ctor_get(v___x_3093_, 0);
v_isSharedCheck_3151_ = !lean_is_exclusive(v___x_3093_);
if (v_isSharedCheck_3151_ == 0)
{
v___x_3146_ = v___x_3093_;
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_a_3144_);
lean_dec(v___x_3093_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v___x_3149_; 
if (v_isShared_3147_ == 0)
{
v___x_3149_ = v___x_3146_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v_a_3144_);
v___x_3149_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
return v___x_3149_;
}
}
}
}
else
{
lean_object* v_a_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3159_; 
lean_dec(v_a_3087_);
lean_dec_ref(v___x_3085_);
lean_dec(v_a_3077_);
lean_del_object(v___x_3074_);
lean_dec_ref(v_proof_3071_);
lean_dec_ref(v_e_x27_3070_);
lean_dec_ref(v_fn_3065_);
lean_dec_ref(v_e_3048_);
v_a_3152_ = lean_ctor_get(v___x_3088_, 0);
v_isSharedCheck_3159_ = !lean_is_exclusive(v___x_3088_);
if (v_isSharedCheck_3159_ == 0)
{
v___x_3154_ = v___x_3088_;
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
else
{
lean_inc(v_a_3152_);
lean_dec(v___x_3088_);
v___x_3154_ = lean_box(0);
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
v_resetjp_3153_:
{
lean_object* v___x_3157_; 
if (v_isShared_3155_ == 0)
{
v___x_3157_ = v___x_3154_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v_a_3152_);
v___x_3157_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
return v___x_3157_;
}
}
}
}
else
{
lean_object* v_a_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3167_; 
lean_dec_ref(v___x_3085_);
lean_dec(v_a_3077_);
lean_del_object(v___x_3074_);
lean_dec_ref(v_proof_3071_);
lean_dec_ref(v_e_x27_3070_);
lean_dec_ref(v_fn_3065_);
lean_dec_ref(v_e_3048_);
v_a_3160_ = lean_ctor_get(v___x_3086_, 0);
v_isSharedCheck_3167_ = !lean_is_exclusive(v___x_3086_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3162_ = v___x_3086_;
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_a_3160_);
lean_dec(v___x_3086_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___x_3165_; 
if (v_isShared_3163_ == 0)
{
v___x_3165_ = v___x_3162_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v_a_3160_);
v___x_3165_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
return v___x_3165_;
}
}
}
}
else
{
lean_object* v_a_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3175_; 
lean_del_object(v___x_3074_);
lean_dec_ref(v_proof_3071_);
lean_dec_ref(v_e_x27_3070_);
lean_dec_ref(v_fn_3065_);
lean_dec_ref(v_e_3048_);
v_a_3168_ = lean_ctor_get(v___x_3076_, 0);
v_isSharedCheck_3175_ = !lean_is_exclusive(v___x_3076_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_3170_ = v___x_3076_;
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_a_3168_);
lean_dec(v___x_3076_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v___x_3173_; 
if (v_isShared_3171_ == 0)
{
v___x_3173_ = v___x_3170_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v_a_3168_);
v___x_3173_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
return v___x_3173_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_fn_3065_);
lean_dec_ref(v_e_3048_);
return v___x_3068_;
}
}
else
{
lean_dec_ref(v_fn_3065_);
lean_dec_ref(v_e_3048_);
goto v___jp_3059_;
}
}
else
{
lean_dec_ref(v_fn_3065_);
lean_dec_ref(v_e_3048_);
goto v___jp_3059_;
}
}
v___jp_3059_:
{
lean_object* v___x_3060_; lean_object* v___x_3061_; 
v___x_3060_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
v___x_3061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3061_, 0, v___x_3060_);
return v___x_3061_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___boxed(lean_object* v_e_3177_, lean_object* v_a_3178_, lean_object* v_a_3179_, lean_object* v_a_3180_, lean_object* v_a_3181_, lean_object* v_a_3182_, lean_object* v_a_3183_, lean_object* v_a_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_){
_start:
{
lean_object* v_res_3188_; 
v_res_3188_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn(v_e_3177_, v_a_3178_, v_a_3179_, v_a_3180_, v_a_3181_, v_a_3182_, v_a_3183_, v_a_3184_, v_a_3185_, v_a_3186_);
lean_dec(v_a_3186_);
lean_dec_ref(v_a_3185_);
lean_dec(v_a_3184_);
lean_dec_ref(v_a_3183_);
lean_dec(v_a_3182_);
lean_dec_ref(v_a_3181_);
lean_dec(v_a_3180_);
lean_dec_ref(v_a_3179_);
lean_dec(v_a_3178_);
return v_res_3188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0_spec__1(lean_object* v_f_3189_, lean_object* v_a_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_){
_start:
{
lean_object* v___x_3201_; 
v___x_3201_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0_spec__1___redArg(v_f_3189_, v_a_3190_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_);
return v___x_3201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0_spec__1___boxed(lean_object* v_f_3202_, lean_object* v_a_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_){
_start:
{
lean_object* v_res_3214_; 
v_res_3214_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0_spec__1(v_f_3202_, v_a_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_);
lean_dec(v___y_3212_);
lean_dec_ref(v___y_3211_);
lean_dec(v___y_3210_);
lean_dec_ref(v___y_3209_);
lean_dec(v___y_3208_);
lean_dec_ref(v___y_3207_);
lean_dec(v___y_3206_);
lean_dec_ref(v___y_3205_);
lean_dec(v___y_3204_);
return v_res_3214_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___closed__1(void){
_start:
{
lean_object* v___x_3216_; lean_object* v___x_3217_; 
v___x_3216_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___closed__0));
v___x_3217_ = l_Lean_stringToMessageData(v___x_3216_);
return v___x_3217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst(lean_object* v_e_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_, lean_object* v_a_3227_){
_start:
{
if (lean_obj_tag(v_e_3218_) == 4)
{
lean_object* v_declName_3229_; lean_object* v_us_3230_; lean_object* v___x_3231_; 
v_declName_3229_ = lean_ctor_get(v_e_3218_, 0);
v_us_3230_ = lean_ctor_get(v_e_3218_, 1);
lean_inc(v_declName_3229_);
v___x_3231_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0(v_declName_3229_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_);
if (lean_obj_tag(v___x_3231_) == 0)
{
lean_object* v_a_3232_; lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3359_; 
v_a_3232_ = lean_ctor_get(v___x_3231_, 0);
v_isSharedCheck_3359_ = !lean_is_exclusive(v___x_3231_);
if (v_isSharedCheck_3359_ == 0)
{
v___x_3234_ = v___x_3231_;
v_isShared_3235_ = v_isSharedCheck_3359_;
goto v_resetjp_3233_;
}
else
{
lean_inc(v_a_3232_);
lean_dec(v___x_3231_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3359_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
uint8_t v___x_3236_; 
v___x_3236_ = l_Lean_ConstantInfo_isDefinition(v_a_3232_);
if (v___x_3236_ == 0)
{
lean_object* v___x_3237_; lean_object* v___x_3239_; 
lean_dec(v_a_3232_);
lean_dec_ref_known(v_e_3218_, 2);
v___x_3237_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_3237_, 0, v___x_3236_);
lean_ctor_set_uint8(v___x_3237_, 1, v___x_3236_);
if (v_isShared_3235_ == 0)
{
lean_ctor_set(v___x_3234_, 0, v___x_3237_);
v___x_3239_ = v___x_3234_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v___x_3237_);
v___x_3239_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
return v___x_3239_;
}
}
else
{
lean_object* v___x_3241_; 
v___x_3241_ = l_Lean_ConstantInfo_type(v_a_3232_);
if (lean_obj_tag(v___x_3241_) == 7)
{
lean_object* v___x_3242_; lean_object* v___x_3244_; 
lean_dec_ref_known(v___x_3241_, 3);
lean_dec(v_a_3232_);
lean_dec_ref_known(v_e_3218_, 2);
v___x_3242_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
if (v_isShared_3235_ == 0)
{
lean_ctor_set(v___x_3234_, 0, v___x_3242_);
v___x_3244_ = v___x_3234_;
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
v___x_3246_ = l_Lean_Meta_whnfD(v___x_3241_, v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_);
if (lean_obj_tag(v___x_3246_) == 0)
{
lean_object* v_a_3247_; lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3350_; 
v_a_3247_ = lean_ctor_get(v___x_3246_, 0);
v_isSharedCheck_3350_ = !lean_is_exclusive(v___x_3246_);
if (v_isSharedCheck_3350_ == 0)
{
v___x_3249_ = v___x_3246_;
v_isShared_3250_ = v_isSharedCheck_3350_;
goto v_resetjp_3248_;
}
else
{
lean_inc(v_a_3247_);
lean_dec(v___x_3246_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3350_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
uint8_t v___x_3251_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; lean_object* v___y_3257_; lean_object* v___y_3258_; lean_object* v___y_3259_; uint8_t v___y_3279_; 
v___x_3251_ = 0;
if (lean_obj_tag(v_a_3247_) == 7)
{
lean_object* v___x_3341_; lean_object* v___x_3343_; 
lean_dec_ref_known(v_a_3247_, 3);
lean_del_object(v___x_3249_);
lean_dec(v_a_3232_);
lean_dec_ref_known(v_e_3218_, 2);
v___x_3341_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
if (v_isShared_3235_ == 0)
{
lean_ctor_set(v___x_3234_, 0, v___x_3341_);
v___x_3343_ = v___x_3234_;
goto v_reusejp_3342_;
}
else
{
lean_object* v_reuseFailAlloc_3344_; 
v_reuseFailAlloc_3344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3344_, 0, v___x_3341_);
v___x_3343_ = v_reuseFailAlloc_3344_;
goto v_reusejp_3342_;
}
v_reusejp_3342_:
{
return v___x_3343_;
}
}
else
{
uint8_t v___x_3345_; 
lean_dec(v_a_3247_);
lean_del_object(v___x_3234_);
v___x_3345_ = l_Lean_ConstantInfo_hasValue(v_a_3232_, v___x_3251_);
if (v___x_3345_ == 0)
{
v___y_3279_ = v___x_3345_;
goto v___jp_3278_;
}
else
{
lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; uint8_t v___x_3349_; 
v___x_3346_ = l_Lean_ConstantInfo_levelParams(v_a_3232_);
v___x_3347_ = l_List_lengthTR___redArg(v___x_3346_);
lean_dec(v___x_3346_);
v___x_3348_ = l_List_lengthTR___redArg(v_us_3230_);
v___x_3349_ = lean_nat_dec_eq(v___x_3347_, v___x_3348_);
lean_dec(v___x_3348_);
lean_dec(v___x_3347_);
v___y_3279_ = v___x_3349_;
goto v___jp_3278_;
}
}
v___jp_3252_:
{
lean_object* v___x_3260_; 
lean_inc_ref(v___y_3253_);
v___x_3260_ = l_Lean_Meta_Sym_mkEqRefl(v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_);
if (lean_obj_tag(v___x_3260_) == 0)
{
lean_object* v_a_3261_; lean_object* v___x_3263_; uint8_t v_isShared_3264_; uint8_t v_isSharedCheck_3269_; 
v_a_3261_ = lean_ctor_get(v___x_3260_, 0);
v_isSharedCheck_3269_ = !lean_is_exclusive(v___x_3260_);
if (v_isSharedCheck_3269_ == 0)
{
v___x_3263_ = v___x_3260_;
v_isShared_3264_ = v_isSharedCheck_3269_;
goto v_resetjp_3262_;
}
else
{
lean_inc(v_a_3261_);
lean_dec(v___x_3260_);
v___x_3263_ = lean_box(0);
v_isShared_3264_ = v_isSharedCheck_3269_;
goto v_resetjp_3262_;
}
v_resetjp_3262_:
{
lean_object* v___x_3265_; lean_object* v___x_3267_; 
v___x_3265_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3265_, 0, v___y_3253_);
lean_ctor_set(v___x_3265_, 1, v_a_3261_);
lean_ctor_set_uint8(v___x_3265_, sizeof(void*)*2, v___x_3251_);
lean_ctor_set_uint8(v___x_3265_, sizeof(void*)*2 + 1, v___x_3251_);
if (v_isShared_3264_ == 0)
{
lean_ctor_set(v___x_3263_, 0, v___x_3265_);
v___x_3267_ = v___x_3263_;
goto v_reusejp_3266_;
}
else
{
lean_object* v_reuseFailAlloc_3268_; 
v_reuseFailAlloc_3268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3268_, 0, v___x_3265_);
v___x_3267_ = v_reuseFailAlloc_3268_;
goto v_reusejp_3266_;
}
v_reusejp_3266_:
{
return v___x_3267_;
}
}
}
else
{
lean_object* v_a_3270_; lean_object* v___x_3272_; uint8_t v_isShared_3273_; uint8_t v_isSharedCheck_3277_; 
lean_dec_ref(v___y_3253_);
v_a_3270_ = lean_ctor_get(v___x_3260_, 0);
v_isSharedCheck_3277_ = !lean_is_exclusive(v___x_3260_);
if (v_isSharedCheck_3277_ == 0)
{
v___x_3272_ = v___x_3260_;
v_isShared_3273_ = v_isSharedCheck_3277_;
goto v_resetjp_3271_;
}
else
{
lean_inc(v_a_3270_);
lean_dec(v___x_3260_);
v___x_3272_ = lean_box(0);
v_isShared_3273_ = v_isSharedCheck_3277_;
goto v_resetjp_3271_;
}
v_resetjp_3271_:
{
lean_object* v___x_3275_; 
if (v_isShared_3273_ == 0)
{
v___x_3275_ = v___x_3272_;
goto v_reusejp_3274_;
}
else
{
lean_object* v_reuseFailAlloc_3276_; 
v_reuseFailAlloc_3276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3276_, 0, v_a_3270_);
v___x_3275_ = v_reuseFailAlloc_3276_;
goto v_reusejp_3274_;
}
v_reusejp_3274_:
{
return v___x_3275_;
}
}
}
}
v___jp_3278_:
{
if (v___y_3279_ == 0)
{
lean_object* v___x_3280_; lean_object* v___x_3282_; 
lean_dec(v_a_3232_);
lean_dec_ref_known(v_e_3218_, 2);
v___x_3280_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
if (v_isShared_3250_ == 0)
{
lean_ctor_set(v___x_3249_, 0, v___x_3280_);
v___x_3282_ = v___x_3249_;
goto v_reusejp_3281_;
}
else
{
lean_object* v_reuseFailAlloc_3283_; 
v_reuseFailAlloc_3283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3283_, 0, v___x_3280_);
v___x_3282_ = v_reuseFailAlloc_3283_;
goto v_reusejp_3281_;
}
v_reusejp_3281_:
{
return v___x_3282_;
}
}
else
{
lean_object* v___x_3284_; 
lean_del_object(v___x_3249_);
lean_inc(v_us_3230_);
v___x_3284_ = l_Lean_Core_instantiateValueLevelParams(v_a_3232_, v_us_3230_, v___x_3251_, v_a_3226_, v_a_3227_);
lean_dec(v_a_3232_);
if (lean_obj_tag(v___x_3284_) == 0)
{
lean_object* v_a_3285_; lean_object* v___x_3286_; 
v_a_3285_ = lean_ctor_get(v___x_3284_, 0);
lean_inc(v_a_3285_);
lean_dec_ref_known(v___x_3284_, 1);
v___x_3286_ = l_Lean_Meta_Sym_unfoldReducible(v_a_3285_, v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_);
if (lean_obj_tag(v___x_3286_) == 0)
{
lean_object* v_a_3287_; lean_object* v___x_3288_; 
v_a_3287_ = lean_ctor_get(v___x_3286_, 0);
lean_inc(v_a_3287_);
lean_dec_ref_known(v___x_3286_, 1);
v___x_3288_ = l_Lean_Meta_Sym_shareCommonInc(v_a_3287_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_);
if (lean_obj_tag(v___x_3288_) == 0)
{
lean_object* v_options_3289_; uint8_t v_hasTrace_3290_; 
v_options_3289_ = lean_ctor_get(v_a_3226_, 2);
v_hasTrace_3290_ = lean_ctor_get_uint8(v_options_3289_, sizeof(void*)*1);
if (v_hasTrace_3290_ == 0)
{
lean_object* v_a_3291_; 
lean_dec_ref_known(v_e_3218_, 2);
v_a_3291_ = lean_ctor_get(v___x_3288_, 0);
lean_inc(v_a_3291_);
lean_dec_ref_known(v___x_3288_, 1);
v___y_3253_ = v_a_3291_;
v___y_3254_ = v_a_3222_;
v___y_3255_ = v_a_3223_;
v___y_3256_ = v_a_3224_;
v___y_3257_ = v_a_3225_;
v___y_3258_ = v_a_3226_;
v___y_3259_ = v_a_3227_;
goto v___jp_3252_;
}
else
{
lean_object* v_a_3292_; lean_object* v_inheritedTraceOptions_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; uint8_t v___x_3296_; 
v_a_3292_ = lean_ctor_get(v___x_3288_, 0);
lean_inc(v_a_3292_);
lean_dec_ref_known(v___x_3288_, 1);
v_inheritedTraceOptions_3293_ = lean_ctor_get(v_a_3226_, 13);
v___x_3294_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__1));
v___x_3295_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__2, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__2);
v___x_3296_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3293_, v_options_3289_, v___x_3295_);
if (v___x_3296_ == 0)
{
lean_dec_ref_known(v_e_3218_, 2);
v___y_3253_ = v_a_3292_;
v___y_3254_ = v_a_3222_;
v___y_3255_ = v_a_3223_;
v___y_3256_ = v_a_3224_;
v___y_3257_ = v_a_3225_;
v___y_3258_ = v_a_3226_;
v___y_3259_ = v_a_3227_;
goto v___jp_3252_;
}
else
{
lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; 
v___x_3297_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___closed__1, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___closed__1);
lean_inc(v_declName_3229_);
v___x_3298_ = l_Lean_MessageData_ofName(v_declName_3229_);
v___x_3299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3299_, 0, v___x_3297_);
lean_ctor_set(v___x_3299_, 1, v___x_3298_);
v___x_3300_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8);
v___x_3301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3301_, 0, v___x_3299_);
lean_ctor_set(v___x_3301_, 1, v___x_3300_);
v___x_3302_ = l_Lean_indentExpr(v_e_3218_);
v___x_3303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3303_, 0, v___x_3301_);
lean_ctor_set(v___x_3303_, 1, v___x_3302_);
v___x_3304_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_3305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3305_, 0, v___x_3303_);
lean_ctor_set(v___x_3305_, 1, v___x_3304_);
lean_inc(v_a_3292_);
v___x_3306_ = l_Lean_indentExpr(v_a_3292_);
v___x_3307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3307_, 0, v___x_3305_);
lean_ctor_set(v___x_3307_, 1, v___x_3306_);
v___x_3308_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(v___x_3294_, v___x_3307_, v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_);
if (lean_obj_tag(v___x_3308_) == 0)
{
lean_dec_ref_known(v___x_3308_, 1);
v___y_3253_ = v_a_3292_;
v___y_3254_ = v_a_3222_;
v___y_3255_ = v_a_3223_;
v___y_3256_ = v_a_3224_;
v___y_3257_ = v_a_3225_;
v___y_3258_ = v_a_3226_;
v___y_3259_ = v_a_3227_;
goto v___jp_3252_;
}
else
{
lean_object* v_a_3309_; lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3316_; 
lean_dec(v_a_3292_);
v_a_3309_ = lean_ctor_get(v___x_3308_, 0);
v_isSharedCheck_3316_ = !lean_is_exclusive(v___x_3308_);
if (v_isSharedCheck_3316_ == 0)
{
v___x_3311_ = v___x_3308_;
v_isShared_3312_ = v_isSharedCheck_3316_;
goto v_resetjp_3310_;
}
else
{
lean_inc(v_a_3309_);
lean_dec(v___x_3308_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3316_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
lean_object* v___x_3314_; 
if (v_isShared_3312_ == 0)
{
v___x_3314_ = v___x_3311_;
goto v_reusejp_3313_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v_a_3309_);
v___x_3314_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3313_;
}
v_reusejp_3313_:
{
return v___x_3314_;
}
}
}
}
}
}
else
{
lean_object* v_a_3317_; lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3324_; 
lean_dec_ref_known(v_e_3218_, 2);
v_a_3317_ = lean_ctor_get(v___x_3288_, 0);
v_isSharedCheck_3324_ = !lean_is_exclusive(v___x_3288_);
if (v_isSharedCheck_3324_ == 0)
{
v___x_3319_ = v___x_3288_;
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
else
{
lean_inc(v_a_3317_);
lean_dec(v___x_3288_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
v_resetjp_3318_:
{
lean_object* v___x_3322_; 
if (v_isShared_3320_ == 0)
{
v___x_3322_ = v___x_3319_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v_a_3317_);
v___x_3322_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
return v___x_3322_;
}
}
}
}
else
{
lean_object* v_a_3325_; lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3332_; 
lean_dec_ref_known(v_e_3218_, 2);
v_a_3325_ = lean_ctor_get(v___x_3286_, 0);
v_isSharedCheck_3332_ = !lean_is_exclusive(v___x_3286_);
if (v_isSharedCheck_3332_ == 0)
{
v___x_3327_ = v___x_3286_;
v_isShared_3328_ = v_isSharedCheck_3332_;
goto v_resetjp_3326_;
}
else
{
lean_inc(v_a_3325_);
lean_dec(v___x_3286_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3332_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
lean_object* v___x_3330_; 
if (v_isShared_3328_ == 0)
{
v___x_3330_ = v___x_3327_;
goto v_reusejp_3329_;
}
else
{
lean_object* v_reuseFailAlloc_3331_; 
v_reuseFailAlloc_3331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3331_, 0, v_a_3325_);
v___x_3330_ = v_reuseFailAlloc_3331_;
goto v_reusejp_3329_;
}
v_reusejp_3329_:
{
return v___x_3330_;
}
}
}
}
else
{
lean_object* v_a_3333_; lean_object* v___x_3335_; uint8_t v_isShared_3336_; uint8_t v_isSharedCheck_3340_; 
lean_dec_ref_known(v_e_3218_, 2);
v_a_3333_ = lean_ctor_get(v___x_3284_, 0);
v_isSharedCheck_3340_ = !lean_is_exclusive(v___x_3284_);
if (v_isSharedCheck_3340_ == 0)
{
v___x_3335_ = v___x_3284_;
v_isShared_3336_ = v_isSharedCheck_3340_;
goto v_resetjp_3334_;
}
else
{
lean_inc(v_a_3333_);
lean_dec(v___x_3284_);
v___x_3335_ = lean_box(0);
v_isShared_3336_ = v_isSharedCheck_3340_;
goto v_resetjp_3334_;
}
v_resetjp_3334_:
{
lean_object* v___x_3338_; 
if (v_isShared_3336_ == 0)
{
v___x_3338_ = v___x_3335_;
goto v_reusejp_3337_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v_a_3333_);
v___x_3338_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3337_;
}
v_reusejp_3337_:
{
return v___x_3338_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3351_; lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3358_; 
lean_del_object(v___x_3234_);
lean_dec(v_a_3232_);
lean_dec_ref_known(v_e_3218_, 2);
v_a_3351_ = lean_ctor_get(v___x_3246_, 0);
v_isSharedCheck_3358_ = !lean_is_exclusive(v___x_3246_);
if (v_isSharedCheck_3358_ == 0)
{
v___x_3353_ = v___x_3246_;
v_isShared_3354_ = v_isSharedCheck_3358_;
goto v_resetjp_3352_;
}
else
{
lean_inc(v_a_3351_);
lean_dec(v___x_3246_);
v___x_3353_ = lean_box(0);
v_isShared_3354_ = v_isSharedCheck_3358_;
goto v_resetjp_3352_;
}
v_resetjp_3352_:
{
lean_object* v___x_3356_; 
if (v_isShared_3354_ == 0)
{
v___x_3356_ = v___x_3353_;
goto v_reusejp_3355_;
}
else
{
lean_object* v_reuseFailAlloc_3357_; 
v_reuseFailAlloc_3357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3357_, 0, v_a_3351_);
v___x_3356_ = v_reuseFailAlloc_3357_;
goto v_reusejp_3355_;
}
v_reusejp_3355_:
{
return v___x_3356_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3360_; lean_object* v___x_3362_; uint8_t v_isShared_3363_; uint8_t v_isSharedCheck_3367_; 
lean_dec_ref_known(v_e_3218_, 2);
v_a_3360_ = lean_ctor_get(v___x_3231_, 0);
v_isSharedCheck_3367_ = !lean_is_exclusive(v___x_3231_);
if (v_isSharedCheck_3367_ == 0)
{
v___x_3362_ = v___x_3231_;
v_isShared_3363_ = v_isSharedCheck_3367_;
goto v_resetjp_3361_;
}
else
{
lean_inc(v_a_3360_);
lean_dec(v___x_3231_);
v___x_3362_ = lean_box(0);
v_isShared_3363_ = v_isSharedCheck_3367_;
goto v_resetjp_3361_;
}
v_resetjp_3361_:
{
lean_object* v___x_3365_; 
if (v_isShared_3363_ == 0)
{
v___x_3365_ = v___x_3362_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3366_; 
v_reuseFailAlloc_3366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3366_, 0, v_a_3360_);
v___x_3365_ = v_reuseFailAlloc_3366_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
return v___x_3365_;
}
}
}
}
else
{
lean_object* v___x_3368_; lean_object* v___x_3369_; 
lean_dec_ref(v_e_3218_);
v___x_3368_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
v___x_3369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3369_, 0, v___x_3368_);
return v___x_3369_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___boxed(lean_object* v_e_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_, lean_object* v_a_3373_, lean_object* v_a_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_){
_start:
{
lean_object* v_res_3381_; 
v_res_3381_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst(v_e_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_, v_a_3377_, v_a_3378_, v_a_3379_);
lean_dec(v_a_3379_);
lean_dec_ref(v_a_3378_);
lean_dec(v_a_3377_);
lean_dec_ref(v_a_3376_);
lean_dec(v_a_3375_);
lean_dec_ref(v_a_3374_);
lean_dec(v_a_3373_);
lean_dec_ref(v_a_3372_);
lean_dec(v_a_3371_);
return v_res_3381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___lam__0(lean_object* v_x_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_){
_start:
{
lean_object* v___x_3394_; 
lean_inc_ref(v___y_3383_);
v___x_3394_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems(v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_);
if (lean_obj_tag(v___x_3394_) == 0)
{
lean_object* v_a_3395_; 
v_a_3395_ = lean_ctor_get(v___x_3394_, 0);
lean_inc(v_a_3395_);
if (lean_obj_tag(v_a_3395_) == 0)
{
uint8_t v_done_3396_; 
v_done_3396_ = lean_ctor_get_uint8(v_a_3395_, 0);
if (v_done_3396_ == 0)
{
uint8_t v_contextDependent_3397_; lean_object* v___x_3398_; 
lean_dec_ref_known(v___x_3394_, 1);
v_contextDependent_3397_ = lean_ctor_get_uint8(v_a_3395_, 1);
lean_dec_ref_known(v_a_3395_, 0);
v___x_3398_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst(v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_);
if (lean_obj_tag(v___x_3398_) == 0)
{
lean_object* v_a_3399_; uint8_t v___y_3401_; 
v_a_3399_ = lean_ctor_get(v___x_3398_, 0);
lean_inc(v_a_3399_);
if (v_contextDependent_3397_ == 0)
{
lean_dec(v_a_3399_);
return v___x_3398_;
}
else
{
if (lean_obj_tag(v_a_3399_) == 0)
{
uint8_t v_contextDependent_3411_; 
v_contextDependent_3411_ = lean_ctor_get_uint8(v_a_3399_, 1);
v___y_3401_ = v_contextDependent_3411_;
goto v___jp_3400_;
}
else
{
uint8_t v___x_3412_; 
v___x_3412_ = 0;
v___y_3401_ = v___x_3412_;
goto v___jp_3400_;
}
}
v___jp_3400_:
{
if (v___y_3401_ == 0)
{
lean_object* v___x_3403_; uint8_t v_isShared_3404_; uint8_t v_isSharedCheck_3409_; 
v_isSharedCheck_3409_ = !lean_is_exclusive(v___x_3398_);
if (v_isSharedCheck_3409_ == 0)
{
lean_object* v_unused_3410_; 
v_unused_3410_ = lean_ctor_get(v___x_3398_, 0);
lean_dec(v_unused_3410_);
v___x_3403_ = v___x_3398_;
v_isShared_3404_ = v_isSharedCheck_3409_;
goto v_resetjp_3402_;
}
else
{
lean_dec(v___x_3398_);
v___x_3403_ = lean_box(0);
v_isShared_3404_ = v_isSharedCheck_3409_;
goto v_resetjp_3402_;
}
v_resetjp_3402_:
{
lean_object* v___x_3405_; lean_object* v___x_3407_; 
v___x_3405_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3399_);
if (v_isShared_3404_ == 0)
{
lean_ctor_set(v___x_3403_, 0, v___x_3405_);
v___x_3407_ = v___x_3403_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v___x_3405_);
v___x_3407_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
return v___x_3407_;
}
}
}
else
{
lean_dec(v_a_3399_);
return v___x_3398_;
}
}
}
else
{
return v___x_3398_;
}
}
else
{
lean_dec_ref_known(v_a_3395_, 0);
lean_dec_ref(v___y_3383_);
return v___x_3394_;
}
}
else
{
lean_dec_ref_known(v_a_3395_, 2);
lean_dec_ref(v___y_3383_);
return v___x_3394_;
}
}
else
{
lean_dec_ref(v___y_3383_);
return v___x_3394_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___lam__0___boxed(lean_object* v_x_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_){
_start:
{
lean_object* v_res_3425_; 
v_res_3425_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___lam__0(v_x_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_);
lean_dec(v___y_3423_);
lean_dec_ref(v___y_3422_);
lean_dec(v___y_3421_);
lean_dec_ref(v___y_3420_);
lean_dec(v___y_3419_);
lean_dec_ref(v___y_3418_);
lean_dec(v___y_3417_);
lean_dec_ref(v___y_3416_);
lean_dec(v___y_3415_);
return v_res_3425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep(lean_object* v_e_3429_, lean_object* v_a_3430_, lean_object* v_a_3431_, lean_object* v_a_3432_, lean_object* v_a_3433_, lean_object* v_a_3434_, lean_object* v_a_3435_, lean_object* v_a_3436_, lean_object* v_a_3437_, lean_object* v_a_3438_){
_start:
{
switch(lean_obj_tag(v_e_3429_))
{
case 9:
{
lean_object* v___x_3443_; 
v___x_3443_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg(v_e_3429_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_);
return v___x_3443_;
}
case 11:
{
lean_object* v___x_3444_; 
v___x_3444_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj(v_e_3429_, v_a_3430_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_);
return v___x_3444_;
}
case 4:
{
lean_object* v___x_3445_; 
lean_inc_ref(v_e_3429_);
v___x_3445_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleOpaqueConst(v_e_3429_, v_a_3430_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_);
if (lean_obj_tag(v___x_3445_) == 0)
{
lean_object* v_a_3446_; lean_object* v___x_3447_; 
v_a_3446_ = lean_ctor_get(v___x_3445_, 0);
lean_inc(v_a_3446_);
v___x_3447_ = lean_box(0);
if (lean_obj_tag(v_a_3446_) == 0)
{
uint8_t v_done_3448_; 
v_done_3448_ = lean_ctor_get_uint8(v_a_3446_, 0);
if (v_done_3448_ == 0)
{
uint8_t v_contextDependent_3449_; lean_object* v___x_3450_; 
lean_dec_ref_known(v___x_3445_, 1);
v_contextDependent_3449_ = lean_ctor_get_uint8(v_a_3446_, 1);
lean_dec_ref_known(v_a_3446_, 0);
v___x_3450_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___lam__0(v___x_3447_, v_e_3429_, v_a_3430_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_);
if (lean_obj_tag(v___x_3450_) == 0)
{
lean_object* v_a_3451_; uint8_t v___y_3453_; 
v_a_3451_ = lean_ctor_get(v___x_3450_, 0);
lean_inc(v_a_3451_);
if (v_contextDependent_3449_ == 0)
{
lean_dec(v_a_3451_);
return v___x_3450_;
}
else
{
if (lean_obj_tag(v_a_3451_) == 0)
{
uint8_t v_contextDependent_3463_; 
v_contextDependent_3463_ = lean_ctor_get_uint8(v_a_3451_, 1);
v___y_3453_ = v_contextDependent_3463_;
goto v___jp_3452_;
}
else
{
uint8_t v_contextDependent_3464_; 
v_contextDependent_3464_ = lean_ctor_get_uint8(v_a_3451_, sizeof(void*)*2 + 1);
v___y_3453_ = v_contextDependent_3464_;
goto v___jp_3452_;
}
}
v___jp_3452_:
{
if (v___y_3453_ == 0)
{
lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3461_; 
v_isSharedCheck_3461_ = !lean_is_exclusive(v___x_3450_);
if (v_isSharedCheck_3461_ == 0)
{
lean_object* v_unused_3462_; 
v_unused_3462_ = lean_ctor_get(v___x_3450_, 0);
lean_dec(v_unused_3462_);
v___x_3455_ = v___x_3450_;
v_isShared_3456_ = v_isSharedCheck_3461_;
goto v_resetjp_3454_;
}
else
{
lean_dec(v___x_3450_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3461_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
lean_object* v___x_3457_; lean_object* v___x_3459_; 
v___x_3457_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3451_);
if (v_isShared_3456_ == 0)
{
lean_ctor_set(v___x_3455_, 0, v___x_3457_);
v___x_3459_ = v___x_3455_;
goto v_reusejp_3458_;
}
else
{
lean_object* v_reuseFailAlloc_3460_; 
v_reuseFailAlloc_3460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3460_, 0, v___x_3457_);
v___x_3459_ = v_reuseFailAlloc_3460_;
goto v_reusejp_3458_;
}
v_reusejp_3458_:
{
return v___x_3459_;
}
}
}
else
{
lean_dec(v_a_3451_);
return v___x_3450_;
}
}
}
else
{
return v___x_3450_;
}
}
else
{
lean_dec_ref_known(v_a_3446_, 0);
lean_dec_ref_known(v_e_3429_, 2);
return v___x_3445_;
}
}
else
{
uint8_t v_done_3465_; 
v_done_3465_ = lean_ctor_get_uint8(v_a_3446_, sizeof(void*)*2);
if (v_done_3465_ == 0)
{
lean_object* v_e_x27_3466_; lean_object* v_proof_3467_; uint8_t v_contextDependent_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3518_; 
lean_dec_ref_known(v___x_3445_, 1);
v_e_x27_3466_ = lean_ctor_get(v_a_3446_, 0);
v_proof_3467_ = lean_ctor_get(v_a_3446_, 1);
v_contextDependent_3468_ = lean_ctor_get_uint8(v_a_3446_, sizeof(void*)*2 + 1);
v_isSharedCheck_3518_ = !lean_is_exclusive(v_a_3446_);
if (v_isSharedCheck_3518_ == 0)
{
v___x_3470_ = v_a_3446_;
v_isShared_3471_ = v_isSharedCheck_3518_;
goto v_resetjp_3469_;
}
else
{
lean_inc(v_proof_3467_);
lean_inc(v_e_x27_3466_);
lean_dec(v_a_3446_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3518_;
goto v_resetjp_3469_;
}
v_resetjp_3469_:
{
lean_object* v___x_3472_; 
lean_inc_ref(v_e_x27_3466_);
v___x_3472_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___lam__0(v___x_3447_, v_e_x27_3466_, v_a_3430_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_);
if (lean_obj_tag(v___x_3472_) == 0)
{
lean_object* v_a_3473_; lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3517_; 
v_a_3473_ = lean_ctor_get(v___x_3472_, 0);
v_isSharedCheck_3517_ = !lean_is_exclusive(v___x_3472_);
if (v_isSharedCheck_3517_ == 0)
{
v___x_3475_ = v___x_3472_;
v_isShared_3476_ = v_isSharedCheck_3517_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_a_3473_);
lean_dec(v___x_3472_);
v___x_3475_ = lean_box(0);
v_isShared_3476_ = v_isSharedCheck_3517_;
goto v_resetjp_3474_;
}
v_resetjp_3474_:
{
if (lean_obj_tag(v_a_3473_) == 0)
{
uint8_t v_done_3477_; uint8_t v_contextDependent_3478_; uint8_t v___y_3480_; 
lean_dec_ref_known(v_e_3429_, 2);
v_done_3477_ = lean_ctor_get_uint8(v_a_3473_, 0);
v_contextDependent_3478_ = lean_ctor_get_uint8(v_a_3473_, 1);
lean_dec_ref_known(v_a_3473_, 0);
if (v_contextDependent_3468_ == 0)
{
v___y_3480_ = v_contextDependent_3478_;
goto v___jp_3479_;
}
else
{
v___y_3480_ = v_contextDependent_3468_;
goto v___jp_3479_;
}
v___jp_3479_:
{
lean_object* v___x_3482_; 
if (v_isShared_3471_ == 0)
{
v___x_3482_ = v___x_3470_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v_e_x27_3466_);
lean_ctor_set(v_reuseFailAlloc_3486_, 1, v_proof_3467_);
v___x_3482_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
lean_object* v___x_3484_; 
lean_ctor_set_uint8(v___x_3482_, sizeof(void*)*2, v_done_3477_);
lean_ctor_set_uint8(v___x_3482_, sizeof(void*)*2 + 1, v___y_3480_);
if (v_isShared_3476_ == 0)
{
lean_ctor_set(v___x_3475_, 0, v___x_3482_);
v___x_3484_ = v___x_3475_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v___x_3482_);
v___x_3484_ = v_reuseFailAlloc_3485_;
goto v_reusejp_3483_;
}
v_reusejp_3483_:
{
return v___x_3484_;
}
}
}
}
else
{
lean_object* v_e_x27_3487_; lean_object* v_proof_3488_; uint8_t v_done_3489_; uint8_t v_contextDependent_3490_; lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3516_; 
lean_del_object(v___x_3475_);
lean_del_object(v___x_3470_);
v_e_x27_3487_ = lean_ctor_get(v_a_3473_, 0);
v_proof_3488_ = lean_ctor_get(v_a_3473_, 1);
v_done_3489_ = lean_ctor_get_uint8(v_a_3473_, sizeof(void*)*2);
v_contextDependent_3490_ = lean_ctor_get_uint8(v_a_3473_, sizeof(void*)*2 + 1);
v_isSharedCheck_3516_ = !lean_is_exclusive(v_a_3473_);
if (v_isSharedCheck_3516_ == 0)
{
v___x_3492_ = v_a_3473_;
v_isShared_3493_ = v_isSharedCheck_3516_;
goto v_resetjp_3491_;
}
else
{
lean_inc(v_proof_3488_);
lean_inc(v_e_x27_3487_);
lean_dec(v_a_3473_);
v___x_3492_ = lean_box(0);
v_isShared_3493_ = v_isSharedCheck_3516_;
goto v_resetjp_3491_;
}
v_resetjp_3491_:
{
lean_object* v___x_3494_; 
lean_inc_ref(v_e_x27_3487_);
v___x_3494_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v_e_3429_, v_e_x27_3466_, v_proof_3467_, v_e_x27_3487_, v_proof_3488_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_);
if (lean_obj_tag(v___x_3494_) == 0)
{
lean_object* v_a_3495_; lean_object* v___x_3497_; uint8_t v_isShared_3498_; uint8_t v_isSharedCheck_3507_; 
v_a_3495_ = lean_ctor_get(v___x_3494_, 0);
v_isSharedCheck_3507_ = !lean_is_exclusive(v___x_3494_);
if (v_isSharedCheck_3507_ == 0)
{
v___x_3497_ = v___x_3494_;
v_isShared_3498_ = v_isSharedCheck_3507_;
goto v_resetjp_3496_;
}
else
{
lean_inc(v_a_3495_);
lean_dec(v___x_3494_);
v___x_3497_ = lean_box(0);
v_isShared_3498_ = v_isSharedCheck_3507_;
goto v_resetjp_3496_;
}
v_resetjp_3496_:
{
uint8_t v___y_3500_; 
if (v_contextDependent_3468_ == 0)
{
v___y_3500_ = v_contextDependent_3490_;
goto v___jp_3499_;
}
else
{
v___y_3500_ = v_contextDependent_3468_;
goto v___jp_3499_;
}
v___jp_3499_:
{
lean_object* v___x_3502_; 
if (v_isShared_3493_ == 0)
{
lean_ctor_set(v___x_3492_, 1, v_a_3495_);
v___x_3502_ = v___x_3492_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3506_; 
v_reuseFailAlloc_3506_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3506_, 0, v_e_x27_3487_);
lean_ctor_set(v_reuseFailAlloc_3506_, 1, v_a_3495_);
lean_ctor_set_uint8(v_reuseFailAlloc_3506_, sizeof(void*)*2, v_done_3489_);
v___x_3502_ = v_reuseFailAlloc_3506_;
goto v_reusejp_3501_;
}
v_reusejp_3501_:
{
lean_object* v___x_3504_; 
lean_ctor_set_uint8(v___x_3502_, sizeof(void*)*2 + 1, v___y_3500_);
if (v_isShared_3498_ == 0)
{
lean_ctor_set(v___x_3497_, 0, v___x_3502_);
v___x_3504_ = v___x_3497_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v___x_3502_);
v___x_3504_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
return v___x_3504_;
}
}
}
}
}
else
{
lean_object* v_a_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3515_; 
lean_del_object(v___x_3492_);
lean_dec_ref(v_e_x27_3487_);
v_a_3508_ = lean_ctor_get(v___x_3494_, 0);
v_isSharedCheck_3515_ = !lean_is_exclusive(v___x_3494_);
if (v_isSharedCheck_3515_ == 0)
{
v___x_3510_ = v___x_3494_;
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_a_3508_);
lean_dec(v___x_3494_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
lean_object* v___x_3513_; 
if (v_isShared_3511_ == 0)
{
v___x_3513_ = v___x_3510_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v_a_3508_);
v___x_3513_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
return v___x_3513_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_3470_);
lean_dec_ref(v_proof_3467_);
lean_dec_ref(v_e_x27_3466_);
lean_dec_ref_known(v_e_3429_, 2);
return v___x_3472_;
}
}
}
else
{
lean_dec_ref_known(v_a_3446_, 2);
lean_dec_ref_known(v_e_3429_, 2);
return v___x_3445_;
}
}
}
else
{
lean_dec_ref_known(v_e_3429_, 2);
return v___x_3445_;
}
}
case 5:
{
lean_object* v___x_3519_; 
lean_inc_ref(v_e_3429_);
v___x_3519_ = l_Lean_Meta_Tactic_Cbv_tryMatcher(v_e_3429_, v_a_3430_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_);
if (lean_obj_tag(v___x_3519_) == 0)
{
lean_object* v_a_3520_; 
v_a_3520_ = lean_ctor_get(v___x_3519_, 0);
lean_inc(v_a_3520_);
if (lean_obj_tag(v_a_3520_) == 0)
{
uint8_t v_done_3521_; 
v_done_3521_ = lean_ctor_get_uint8(v_a_3520_, 0);
if (v_done_3521_ == 0)
{
uint8_t v_contextDependent_3522_; lean_object* v___x_3523_; 
lean_dec_ref_known(v___x_3519_, 1);
v_contextDependent_3522_ = lean_ctor_get_uint8(v_a_3520_, 1);
lean_dec_ref_known(v_a_3520_, 0);
v___x_3523_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn(v_e_3429_, v_a_3430_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_);
if (lean_obj_tag(v___x_3523_) == 0)
{
lean_object* v_a_3524_; uint8_t v___y_3526_; 
v_a_3524_ = lean_ctor_get(v___x_3523_, 0);
lean_inc(v_a_3524_);
if (v_contextDependent_3522_ == 0)
{
lean_dec(v_a_3524_);
return v___x_3523_;
}
else
{
if (lean_obj_tag(v_a_3524_) == 0)
{
uint8_t v_contextDependent_3536_; 
v_contextDependent_3536_ = lean_ctor_get_uint8(v_a_3524_, 1);
v___y_3526_ = v_contextDependent_3536_;
goto v___jp_3525_;
}
else
{
uint8_t v_contextDependent_3537_; 
v_contextDependent_3537_ = lean_ctor_get_uint8(v_a_3524_, sizeof(void*)*2 + 1);
v___y_3526_ = v_contextDependent_3537_;
goto v___jp_3525_;
}
}
v___jp_3525_:
{
if (v___y_3526_ == 0)
{
lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3534_; 
v_isSharedCheck_3534_ = !lean_is_exclusive(v___x_3523_);
if (v_isSharedCheck_3534_ == 0)
{
lean_object* v_unused_3535_; 
v_unused_3535_ = lean_ctor_get(v___x_3523_, 0);
lean_dec(v_unused_3535_);
v___x_3528_ = v___x_3523_;
v_isShared_3529_ = v_isSharedCheck_3534_;
goto v_resetjp_3527_;
}
else
{
lean_dec(v___x_3523_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3534_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v___x_3530_; lean_object* v___x_3532_; 
v___x_3530_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3524_);
if (v_isShared_3529_ == 0)
{
lean_ctor_set(v___x_3528_, 0, v___x_3530_);
v___x_3532_ = v___x_3528_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v___x_3530_);
v___x_3532_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
return v___x_3532_;
}
}
}
else
{
lean_dec(v_a_3524_);
return v___x_3523_;
}
}
}
else
{
return v___x_3523_;
}
}
else
{
lean_dec_ref_known(v_a_3520_, 0);
lean_dec_ref_known(v_e_3429_, 2);
return v___x_3519_;
}
}
else
{
lean_dec_ref_known(v_a_3520_, 2);
lean_dec_ref_known(v_e_3429_, 2);
return v___x_3519_;
}
}
else
{
lean_dec_ref_known(v_e_3429_, 2);
return v___x_3519_;
}
}
case 8:
{
uint8_t v___x_3538_; 
v___x_3538_ = l_Lean_Expr_letNondep_x21(v_e_3429_);
if (v___x_3538_ == 0)
{
lean_object* v___x_3539_; 
v___x_3539_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg(v_e_3429_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_);
return v___x_3539_;
}
else
{
lean_object* v___x_3540_; 
v___x_3540_ = l_Lean_Meta_Sym_Simp_toBetaApp(v_e_3429_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_);
if (lean_obj_tag(v___x_3540_) == 0)
{
lean_object* v_a_3541_; lean_object* v___x_3543_; uint8_t v_isShared_3544_; uint8_t v_isSharedCheck_3552_; 
v_a_3541_ = lean_ctor_get(v___x_3540_, 0);
v_isSharedCheck_3552_ = !lean_is_exclusive(v___x_3540_);
if (v_isSharedCheck_3552_ == 0)
{
v___x_3543_ = v___x_3540_;
v_isShared_3544_ = v_isSharedCheck_3552_;
goto v_resetjp_3542_;
}
else
{
lean_inc(v_a_3541_);
lean_dec(v___x_3540_);
v___x_3543_ = lean_box(0);
v_isShared_3544_ = v_isSharedCheck_3552_;
goto v_resetjp_3542_;
}
v_resetjp_3542_:
{
lean_object* v_e_3545_; lean_object* v_h_3546_; uint8_t v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3550_; 
v_e_3545_ = lean_ctor_get(v_a_3541_, 2);
lean_inc_ref(v_e_3545_);
v_h_3546_ = lean_ctor_get(v_a_3541_, 3);
lean_inc_ref(v_h_3546_);
lean_dec(v_a_3541_);
v___x_3547_ = 0;
v___x_3548_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3548_, 0, v_e_3545_);
lean_ctor_set(v___x_3548_, 1, v_h_3546_);
lean_ctor_set_uint8(v___x_3548_, sizeof(void*)*2, v___x_3547_);
lean_ctor_set_uint8(v___x_3548_, sizeof(void*)*2 + 1, v___x_3547_);
if (v_isShared_3544_ == 0)
{
lean_ctor_set(v___x_3543_, 0, v___x_3548_);
v___x_3550_ = v___x_3543_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v___x_3548_);
v___x_3550_ = v_reuseFailAlloc_3551_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
return v___x_3550_;
}
}
}
else
{
lean_object* v_a_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3560_; 
v_a_3553_ = lean_ctor_get(v___x_3540_, 0);
v_isSharedCheck_3560_ = !lean_is_exclusive(v___x_3540_);
if (v_isSharedCheck_3560_ == 0)
{
v___x_3555_ = v___x_3540_;
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_a_3553_);
lean_dec(v___x_3540_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
lean_object* v___x_3558_; 
if (v_isShared_3556_ == 0)
{
v___x_3558_ = v___x_3555_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v_a_3553_);
v___x_3558_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
return v___x_3558_;
}
}
}
}
}
case 7:
{
lean_dec_ref_known(v_e_3429_, 3);
goto v___jp_3440_;
}
case 6:
{
lean_dec_ref_known(v_e_3429_, 3);
goto v___jp_3440_;
}
case 1:
{
lean_object* v___x_3561_; lean_object* v___x_3562_; 
lean_dec_ref_known(v_e_3429_, 1);
v___x_3561_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___closed__0));
v___x_3562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3562_, 0, v___x_3561_);
return v___x_3562_;
}
case 2:
{
lean_object* v___x_3563_; lean_object* v___x_3564_; 
lean_dec_ref_known(v_e_3429_, 1);
v___x_3563_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___closed__0));
v___x_3564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3564_, 0, v___x_3563_);
return v___x_3564_;
}
case 0:
{
lean_object* v___x_3565_; lean_object* v___x_3566_; 
lean_dec_ref_known(v_e_3429_, 1);
v___x_3565_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___closed__0));
v___x_3566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3566_, 0, v___x_3565_);
return v___x_3566_;
}
case 3:
{
lean_object* v___x_3567_; lean_object* v___x_3568_; 
lean_dec_ref_known(v_e_3429_, 1);
v___x_3567_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___closed__0));
v___x_3568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3568_, 0, v___x_3567_);
return v___x_3568_;
}
default: 
{
lean_object* v___x_3569_; lean_object* v___x_3570_; 
lean_dec_ref(v_e_3429_);
v___x_3569_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
v___x_3570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3570_, 0, v___x_3569_);
return v___x_3570_;
}
}
v___jp_3440_:
{
lean_object* v___x_3441_; lean_object* v___x_3442_; 
v___x_3441_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___closed__0));
v___x_3442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3442_, 0, v___x_3441_);
return v___x_3442_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___boxed(lean_object* v_e_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_){
_start:
{
lean_object* v_res_3582_; 
v_res_3582_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep(v_e_3571_, v_a_3572_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_);
lean_dec(v_a_3580_);
lean_dec_ref(v_a_3579_);
lean_dec(v_a_3578_);
lean_dec_ref(v_a_3577_);
lean_dec(v_a_3576_);
lean_dec_ref(v_a_3575_);
lean_dec(v_a_3574_);
lean_dec_ref(v_a_3573_);
lean_dec(v_a_3572_);
return v_res_3582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPre(lean_object* v_simprocs_3583_, lean_object* v_a_3584_, lean_object* v_a_3585_, lean_object* v_a_3586_, lean_object* v_a_3587_, lean_object* v_a_3588_, lean_object* v_a_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_){
_start:
{
lean_object* v___y_3596_; lean_object* v___y_3597_; uint8_t v___y_3598_; lean_object* v___x_3601_; 
lean_inc_ref(v_a_3584_);
v___x_3601_ = l_Lean_Meta_Tactic_Cbv_isBuiltinValue___redArg(v_a_3584_);
if (lean_obj_tag(v___x_3601_) == 0)
{
lean_object* v_a_3602_; 
v_a_3602_ = lean_ctor_get(v___x_3601_, 0);
lean_inc(v_a_3602_);
if (lean_obj_tag(v_a_3602_) == 0)
{
uint8_t v_done_3603_; uint8_t v_contextDependent_3604_; lean_object* v___y_3606_; lean_object* v_a_3607_; lean_object* v___y_3611_; lean_object* v___y_3612_; uint8_t v___y_3613_; lean_object* v___y_3617_; 
v_done_3603_ = lean_ctor_get_uint8(v_a_3602_, 0);
v_contextDependent_3604_ = lean_ctor_get_uint8(v_a_3602_, 1);
lean_dec_ref_known(v_a_3602_, 0);
if (v_done_3603_ == 0)
{
lean_object* v___x_3619_; 
lean_dec_ref_known(v___x_3601_, 1);
lean_inc_ref(v_a_3584_);
v___x_3619_ = l_Lean_Meta_Tactic_Cbv_isProofTerm___redArg(v_a_3584_, v_a_3588_, v_a_3589_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_);
if (lean_obj_tag(v___x_3619_) == 0)
{
lean_object* v_a_3620_; 
v_a_3620_ = lean_ctor_get(v___x_3619_, 0);
lean_inc(v_a_3620_);
if (lean_obj_tag(v_a_3620_) == 0)
{
uint8_t v_done_3621_; uint8_t v_contextDependent_3622_; lean_object* v___y_3624_; lean_object* v_a_3625_; lean_object* v___y_3629_; 
v_done_3621_ = lean_ctor_get_uint8(v_a_3620_, 0);
v_contextDependent_3622_ = lean_ctor_get_uint8(v_a_3620_, 1);
lean_dec_ref_known(v_a_3620_, 0);
if (v_done_3621_ == 0)
{
lean_object* v_pre_3631_; lean_object* v_erased_3632_; lean_object* v___x_3633_; 
lean_dec_ref_known(v___x_3619_, 1);
v_pre_3631_ = lean_ctor_get(v_simprocs_3583_, 0);
v_erased_3632_ = lean_ctor_get(v_simprocs_3583_, 4);
lean_inc_ref(v_a_3584_);
v___x_3633_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch(v_pre_3631_, v_erased_3632_, v_a_3584_, v_a_3585_, v_a_3586_, v_a_3587_, v_a_3588_, v_a_3589_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_);
if (lean_obj_tag(v___x_3633_) == 0)
{
lean_object* v_a_3634_; 
v_a_3634_ = lean_ctor_get(v___x_3633_, 0);
lean_inc(v_a_3634_);
if (lean_obj_tag(v_a_3634_) == 0)
{
uint8_t v_done_3635_; 
v_done_3635_ = lean_ctor_get_uint8(v_a_3634_, 0);
if (v_done_3635_ == 0)
{
uint8_t v_contextDependent_3636_; lean_object* v___x_3637_; 
lean_dec_ref_known(v___x_3633_, 1);
v_contextDependent_3636_ = lean_ctor_get_uint8(v_a_3634_, 1);
lean_dec_ref_known(v_a_3634_, 0);
v___x_3637_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep(v_a_3584_, v_a_3585_, v_a_3586_, v_a_3587_, v_a_3588_, v_a_3589_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_);
if (lean_obj_tag(v___x_3637_) == 0)
{
lean_object* v_a_3638_; uint8_t v___y_3640_; 
v_a_3638_ = lean_ctor_get(v___x_3637_, 0);
lean_inc(v_a_3638_);
if (v_contextDependent_3636_ == 0)
{
lean_dec(v_a_3638_);
v___y_3629_ = v___x_3637_;
goto v___jp_3628_;
}
else
{
if (lean_obj_tag(v_a_3638_) == 0)
{
uint8_t v_contextDependent_3650_; 
v_contextDependent_3650_ = lean_ctor_get_uint8(v_a_3638_, 1);
v___y_3640_ = v_contextDependent_3650_;
goto v___jp_3639_;
}
else
{
uint8_t v_contextDependent_3651_; 
v_contextDependent_3651_ = lean_ctor_get_uint8(v_a_3638_, sizeof(void*)*2 + 1);
v___y_3640_ = v_contextDependent_3651_;
goto v___jp_3639_;
}
}
v___jp_3639_:
{
if (v___y_3640_ == 0)
{
lean_object* v___x_3642_; uint8_t v_isShared_3643_; uint8_t v_isSharedCheck_3648_; 
v_isSharedCheck_3648_ = !lean_is_exclusive(v___x_3637_);
if (v_isSharedCheck_3648_ == 0)
{
lean_object* v_unused_3649_; 
v_unused_3649_ = lean_ctor_get(v___x_3637_, 0);
lean_dec(v_unused_3649_);
v___x_3642_ = v___x_3637_;
v_isShared_3643_ = v_isSharedCheck_3648_;
goto v_resetjp_3641_;
}
else
{
lean_dec(v___x_3637_);
v___x_3642_ = lean_box(0);
v_isShared_3643_ = v_isSharedCheck_3648_;
goto v_resetjp_3641_;
}
v_resetjp_3641_:
{
lean_object* v___x_3644_; lean_object* v___x_3646_; 
v___x_3644_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3638_);
lean_inc_ref(v___x_3644_);
if (v_isShared_3643_ == 0)
{
lean_ctor_set(v___x_3642_, 0, v___x_3644_);
v___x_3646_ = v___x_3642_;
goto v_reusejp_3645_;
}
else
{
lean_object* v_reuseFailAlloc_3647_; 
v_reuseFailAlloc_3647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3647_, 0, v___x_3644_);
v___x_3646_ = v_reuseFailAlloc_3647_;
goto v_reusejp_3645_;
}
v_reusejp_3645_:
{
v___y_3624_ = v___x_3646_;
v_a_3625_ = v___x_3644_;
goto v___jp_3623_;
}
}
}
else
{
lean_dec(v_a_3638_);
v___y_3629_ = v___x_3637_;
goto v___jp_3628_;
}
}
}
else
{
v___y_3629_ = v___x_3637_;
goto v___jp_3628_;
}
}
else
{
lean_dec_ref_known(v_a_3634_, 0);
lean_dec_ref(v_a_3584_);
v___y_3629_ = v___x_3633_;
goto v___jp_3628_;
}
}
else
{
lean_dec_ref_known(v_a_3634_, 2);
lean_dec_ref(v_a_3584_);
v___y_3629_ = v___x_3633_;
goto v___jp_3628_;
}
}
else
{
lean_dec_ref(v_a_3584_);
v___y_3629_ = v___x_3633_;
goto v___jp_3628_;
}
}
else
{
lean_dec_ref(v_a_3584_);
v___y_3617_ = v___x_3619_;
goto v___jp_3616_;
}
v___jp_3623_:
{
if (v_contextDependent_3622_ == 0)
{
v___y_3606_ = v___y_3624_;
v_a_3607_ = v_a_3625_;
goto v___jp_3605_;
}
else
{
if (lean_obj_tag(v_a_3625_) == 0)
{
uint8_t v_contextDependent_3626_; 
v_contextDependent_3626_ = lean_ctor_get_uint8(v_a_3625_, 1);
v___y_3611_ = v___y_3624_;
v___y_3612_ = v_a_3625_;
v___y_3613_ = v_contextDependent_3626_;
goto v___jp_3610_;
}
else
{
uint8_t v_contextDependent_3627_; 
v_contextDependent_3627_ = lean_ctor_get_uint8(v_a_3625_, sizeof(void*)*2 + 1);
v___y_3611_ = v___y_3624_;
v___y_3612_ = v_a_3625_;
v___y_3613_ = v_contextDependent_3627_;
goto v___jp_3610_;
}
}
}
v___jp_3628_:
{
if (lean_obj_tag(v___y_3629_) == 0)
{
lean_object* v_a_3630_; 
v_a_3630_ = lean_ctor_get(v___y_3629_, 0);
lean_inc(v_a_3630_);
v___y_3624_ = v___y_3629_;
v_a_3625_ = v_a_3630_;
goto v___jp_3623_;
}
else
{
return v___y_3629_;
}
}
}
else
{
lean_dec_ref_known(v_a_3620_, 2);
lean_dec_ref(v_a_3584_);
v___y_3617_ = v___x_3619_;
goto v___jp_3616_;
}
}
else
{
lean_dec_ref(v_a_3584_);
v___y_3617_ = v___x_3619_;
goto v___jp_3616_;
}
}
else
{
lean_dec_ref(v_a_3584_);
return v___x_3601_;
}
v___jp_3605_:
{
if (v_contextDependent_3604_ == 0)
{
lean_dec_ref(v_a_3607_);
return v___y_3606_;
}
else
{
if (lean_obj_tag(v_a_3607_) == 0)
{
uint8_t v_contextDependent_3608_; 
v_contextDependent_3608_ = lean_ctor_get_uint8(v_a_3607_, 1);
v___y_3596_ = v___y_3606_;
v___y_3597_ = v_a_3607_;
v___y_3598_ = v_contextDependent_3608_;
goto v___jp_3595_;
}
else
{
uint8_t v_contextDependent_3609_; 
v_contextDependent_3609_ = lean_ctor_get_uint8(v_a_3607_, sizeof(void*)*2 + 1);
v___y_3596_ = v___y_3606_;
v___y_3597_ = v_a_3607_;
v___y_3598_ = v_contextDependent_3609_;
goto v___jp_3595_;
}
}
}
v___jp_3610_:
{
if (v___y_3613_ == 0)
{
lean_object* v___x_3614_; lean_object* v___x_3615_; 
lean_dec_ref(v___y_3611_);
v___x_3614_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_3612_);
lean_inc_ref(v___x_3614_);
v___x_3615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3615_, 0, v___x_3614_);
v___y_3606_ = v___x_3615_;
v_a_3607_ = v___x_3614_;
goto v___jp_3605_;
}
else
{
v___y_3606_ = v___y_3611_;
v_a_3607_ = v___y_3612_;
goto v___jp_3605_;
}
}
v___jp_3616_:
{
if (lean_obj_tag(v___y_3617_) == 0)
{
lean_object* v_a_3618_; 
v_a_3618_ = lean_ctor_get(v___y_3617_, 0);
lean_inc(v_a_3618_);
v___y_3606_ = v___y_3617_;
v_a_3607_ = v_a_3618_;
goto v___jp_3605_;
}
else
{
return v___y_3617_;
}
}
}
else
{
lean_dec_ref_known(v_a_3602_, 2);
lean_dec_ref(v_a_3584_);
return v___x_3601_;
}
}
else
{
lean_dec_ref(v_a_3584_);
return v___x_3601_;
}
v___jp_3595_:
{
if (v___y_3598_ == 0)
{
lean_object* v___x_3599_; lean_object* v___x_3600_; 
lean_dec_ref(v___y_3596_);
v___x_3599_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_3597_);
v___x_3600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3600_, 0, v___x_3599_);
return v___x_3600_;
}
else
{
lean_dec_ref(v___y_3597_);
return v___y_3596_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPre___boxed(lean_object* v_simprocs_3652_, lean_object* v_a_3653_, lean_object* v_a_3654_, lean_object* v_a_3655_, lean_object* v_a_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_, lean_object* v_a_3659_, lean_object* v_a_3660_, lean_object* v_a_3661_, lean_object* v_a_3662_, lean_object* v_a_3663_){
_start:
{
lean_object* v_res_3664_; 
v_res_3664_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPre(v_simprocs_3652_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_);
lean_dec(v_a_3662_);
lean_dec_ref(v_a_3661_);
lean_dec(v_a_3660_);
lean_dec_ref(v_a_3659_);
lean_dec(v_a_3658_);
lean_dec_ref(v_a_3657_);
lean_dec(v_a_3656_);
lean_dec_ref(v_a_3655_);
lean_dec(v_a_3654_);
lean_dec_ref(v_simprocs_3652_);
return v_res_3664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPost(lean_object* v_simprocs_3665_, lean_object* v_a_3666_, lean_object* v_a_3667_, lean_object* v_a_3668_, lean_object* v_a_3669_, lean_object* v_a_3670_, lean_object* v_a_3671_, lean_object* v_a_3672_, lean_object* v_a_3673_, lean_object* v_a_3674_, lean_object* v_a_3675_){
_start:
{
lean_object* v___y_3678_; lean_object* v___y_3679_; uint8_t v___y_3680_; lean_object* v___x_3683_; lean_object* v___x_3684_; 
v___x_3683_ = lean_unsigned_to_nat(255u);
lean_inc_ref(v_a_3666_);
v___x_3684_ = l_Lean_Meta_Sym_Simp_evalGround___redArg(v___x_3683_, v_a_3666_, v_a_3670_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_, v_a_3675_);
if (lean_obj_tag(v___x_3684_) == 0)
{
lean_object* v_a_3685_; 
v_a_3685_ = lean_ctor_get(v___x_3684_, 0);
lean_inc(v_a_3685_);
if (lean_obj_tag(v_a_3685_) == 0)
{
uint8_t v_done_3686_; uint8_t v_contextDependent_3687_; lean_object* v___y_3689_; lean_object* v_a_3690_; lean_object* v___y_3694_; lean_object* v___y_3695_; uint8_t v___y_3696_; lean_object* v___y_3700_; 
v_done_3686_ = lean_ctor_get_uint8(v_a_3685_, 0);
v_contextDependent_3687_ = lean_ctor_get_uint8(v_a_3685_, 1);
lean_dec_ref_known(v_a_3685_, 0);
if (v_done_3686_ == 0)
{
lean_object* v_eval_3702_; lean_object* v_post_3703_; lean_object* v_erased_3704_; lean_object* v___x_3705_; 
lean_dec_ref_known(v___x_3684_, 1);
v_eval_3702_ = lean_ctor_get(v_simprocs_3665_, 1);
v_post_3703_ = lean_ctor_get(v_simprocs_3665_, 2);
v_erased_3704_ = lean_ctor_get(v_simprocs_3665_, 4);
lean_inc_ref(v_a_3666_);
v___x_3705_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch(v_eval_3702_, v_erased_3704_, v_a_3666_, v_a_3667_, v_a_3668_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_, v_a_3675_);
if (lean_obj_tag(v___x_3705_) == 0)
{
lean_object* v_a_3706_; 
v_a_3706_ = lean_ctor_get(v___x_3705_, 0);
lean_inc(v_a_3706_);
if (lean_obj_tag(v_a_3706_) == 0)
{
uint8_t v_done_3707_; uint8_t v_contextDependent_3708_; lean_object* v___y_3710_; lean_object* v_a_3711_; lean_object* v___y_3715_; 
v_done_3707_ = lean_ctor_get_uint8(v_a_3706_, 0);
v_contextDependent_3708_ = lean_ctor_get_uint8(v_a_3706_, 1);
lean_dec_ref_known(v_a_3706_, 0);
if (v_done_3707_ == 0)
{
lean_object* v___x_3717_; 
lean_dec_ref_known(v___x_3705_, 1);
lean_inc_ref(v_a_3666_);
v___x_3717_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp(v_a_3666_, v_a_3667_, v_a_3668_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_, v_a_3675_);
if (lean_obj_tag(v___x_3717_) == 0)
{
lean_object* v_a_3718_; 
v_a_3718_ = lean_ctor_get(v___x_3717_, 0);
lean_inc(v_a_3718_);
if (lean_obj_tag(v_a_3718_) == 0)
{
uint8_t v_done_3719_; 
v_done_3719_ = lean_ctor_get_uint8(v_a_3718_, 0);
if (v_done_3719_ == 0)
{
uint8_t v_contextDependent_3720_; lean_object* v___x_3721_; 
lean_dec_ref_known(v___x_3717_, 1);
v_contextDependent_3720_ = lean_ctor_get_uint8(v_a_3718_, 1);
lean_dec_ref_known(v_a_3718_, 0);
v___x_3721_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch(v_post_3703_, v_erased_3704_, v_a_3666_, v_a_3667_, v_a_3668_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_, v_a_3675_);
if (lean_obj_tag(v___x_3721_) == 0)
{
lean_object* v_a_3722_; uint8_t v___y_3724_; 
v_a_3722_ = lean_ctor_get(v___x_3721_, 0);
lean_inc(v_a_3722_);
if (v_contextDependent_3720_ == 0)
{
lean_dec(v_a_3722_);
v___y_3715_ = v___x_3721_;
goto v___jp_3714_;
}
else
{
if (lean_obj_tag(v_a_3722_) == 0)
{
uint8_t v_contextDependent_3734_; 
v_contextDependent_3734_ = lean_ctor_get_uint8(v_a_3722_, 1);
v___y_3724_ = v_contextDependent_3734_;
goto v___jp_3723_;
}
else
{
uint8_t v_contextDependent_3735_; 
v_contextDependent_3735_ = lean_ctor_get_uint8(v_a_3722_, sizeof(void*)*2 + 1);
v___y_3724_ = v_contextDependent_3735_;
goto v___jp_3723_;
}
}
v___jp_3723_:
{
if (v___y_3724_ == 0)
{
lean_object* v___x_3726_; uint8_t v_isShared_3727_; uint8_t v_isSharedCheck_3732_; 
v_isSharedCheck_3732_ = !lean_is_exclusive(v___x_3721_);
if (v_isSharedCheck_3732_ == 0)
{
lean_object* v_unused_3733_; 
v_unused_3733_ = lean_ctor_get(v___x_3721_, 0);
lean_dec(v_unused_3733_);
v___x_3726_ = v___x_3721_;
v_isShared_3727_ = v_isSharedCheck_3732_;
goto v_resetjp_3725_;
}
else
{
lean_dec(v___x_3721_);
v___x_3726_ = lean_box(0);
v_isShared_3727_ = v_isSharedCheck_3732_;
goto v_resetjp_3725_;
}
v_resetjp_3725_:
{
lean_object* v___x_3728_; lean_object* v___x_3730_; 
v___x_3728_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3722_);
lean_inc_ref(v___x_3728_);
if (v_isShared_3727_ == 0)
{
lean_ctor_set(v___x_3726_, 0, v___x_3728_);
v___x_3730_ = v___x_3726_;
goto v_reusejp_3729_;
}
else
{
lean_object* v_reuseFailAlloc_3731_; 
v_reuseFailAlloc_3731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3731_, 0, v___x_3728_);
v___x_3730_ = v_reuseFailAlloc_3731_;
goto v_reusejp_3729_;
}
v_reusejp_3729_:
{
v___y_3710_ = v___x_3730_;
v_a_3711_ = v___x_3728_;
goto v___jp_3709_;
}
}
}
else
{
lean_dec(v_a_3722_);
v___y_3715_ = v___x_3721_;
goto v___jp_3714_;
}
}
}
else
{
v___y_3715_ = v___x_3721_;
goto v___jp_3714_;
}
}
else
{
lean_dec_ref_known(v_a_3718_, 0);
lean_dec_ref(v_a_3666_);
v___y_3715_ = v___x_3717_;
goto v___jp_3714_;
}
}
else
{
lean_dec_ref_known(v_a_3718_, 2);
lean_dec_ref(v_a_3666_);
v___y_3715_ = v___x_3717_;
goto v___jp_3714_;
}
}
else
{
lean_dec_ref(v_a_3666_);
v___y_3715_ = v___x_3717_;
goto v___jp_3714_;
}
}
else
{
lean_dec_ref(v_a_3666_);
v___y_3700_ = v___x_3705_;
goto v___jp_3699_;
}
v___jp_3709_:
{
if (v_contextDependent_3708_ == 0)
{
v___y_3689_ = v___y_3710_;
v_a_3690_ = v_a_3711_;
goto v___jp_3688_;
}
else
{
if (lean_obj_tag(v_a_3711_) == 0)
{
uint8_t v_contextDependent_3712_; 
v_contextDependent_3712_ = lean_ctor_get_uint8(v_a_3711_, 1);
v___y_3694_ = v___y_3710_;
v___y_3695_ = v_a_3711_;
v___y_3696_ = v_contextDependent_3712_;
goto v___jp_3693_;
}
else
{
uint8_t v_contextDependent_3713_; 
v_contextDependent_3713_ = lean_ctor_get_uint8(v_a_3711_, sizeof(void*)*2 + 1);
v___y_3694_ = v___y_3710_;
v___y_3695_ = v_a_3711_;
v___y_3696_ = v_contextDependent_3713_;
goto v___jp_3693_;
}
}
}
v___jp_3714_:
{
if (lean_obj_tag(v___y_3715_) == 0)
{
lean_object* v_a_3716_; 
v_a_3716_ = lean_ctor_get(v___y_3715_, 0);
lean_inc(v_a_3716_);
v___y_3710_ = v___y_3715_;
v_a_3711_ = v_a_3716_;
goto v___jp_3709_;
}
else
{
return v___y_3715_;
}
}
}
else
{
lean_dec_ref_known(v_a_3706_, 2);
lean_dec_ref(v_a_3666_);
v___y_3700_ = v___x_3705_;
goto v___jp_3699_;
}
}
else
{
lean_dec_ref(v_a_3666_);
v___y_3700_ = v___x_3705_;
goto v___jp_3699_;
}
}
else
{
lean_dec_ref(v_a_3666_);
return v___x_3684_;
}
v___jp_3688_:
{
if (v_contextDependent_3687_ == 0)
{
lean_dec_ref(v_a_3690_);
return v___y_3689_;
}
else
{
if (lean_obj_tag(v_a_3690_) == 0)
{
uint8_t v_contextDependent_3691_; 
v_contextDependent_3691_ = lean_ctor_get_uint8(v_a_3690_, 1);
v___y_3678_ = v___y_3689_;
v___y_3679_ = v_a_3690_;
v___y_3680_ = v_contextDependent_3691_;
goto v___jp_3677_;
}
else
{
uint8_t v_contextDependent_3692_; 
v_contextDependent_3692_ = lean_ctor_get_uint8(v_a_3690_, sizeof(void*)*2 + 1);
v___y_3678_ = v___y_3689_;
v___y_3679_ = v_a_3690_;
v___y_3680_ = v_contextDependent_3692_;
goto v___jp_3677_;
}
}
}
v___jp_3693_:
{
if (v___y_3696_ == 0)
{
lean_object* v___x_3697_; lean_object* v___x_3698_; 
lean_dec_ref(v___y_3694_);
v___x_3697_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_3695_);
lean_inc_ref(v___x_3697_);
v___x_3698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3698_, 0, v___x_3697_);
v___y_3689_ = v___x_3698_;
v_a_3690_ = v___x_3697_;
goto v___jp_3688_;
}
else
{
v___y_3689_ = v___y_3694_;
v_a_3690_ = v___y_3695_;
goto v___jp_3688_;
}
}
v___jp_3699_:
{
if (lean_obj_tag(v___y_3700_) == 0)
{
lean_object* v_a_3701_; 
v_a_3701_ = lean_ctor_get(v___y_3700_, 0);
lean_inc(v_a_3701_);
v___y_3689_ = v___y_3700_;
v_a_3690_ = v_a_3701_;
goto v___jp_3688_;
}
else
{
return v___y_3700_;
}
}
}
else
{
lean_dec_ref_known(v_a_3685_, 2);
lean_dec_ref(v_a_3666_);
return v___x_3684_;
}
}
else
{
lean_dec_ref(v_a_3666_);
return v___x_3684_;
}
v___jp_3677_:
{
if (v___y_3680_ == 0)
{
lean_object* v___x_3681_; lean_object* v___x_3682_; 
lean_dec_ref(v___y_3678_);
v___x_3681_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_3679_);
v___x_3682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3682_, 0, v___x_3681_);
return v___x_3682_;
}
else
{
lean_dec_ref(v___y_3679_);
return v___y_3678_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPost___boxed(lean_object* v_simprocs_3736_, lean_object* v_a_3737_, lean_object* v_a_3738_, lean_object* v_a_3739_, lean_object* v_a_3740_, lean_object* v_a_3741_, lean_object* v_a_3742_, lean_object* v_a_3743_, lean_object* v_a_3744_, lean_object* v_a_3745_, lean_object* v_a_3746_, lean_object* v_a_3747_){
_start:
{
lean_object* v_res_3748_; 
v_res_3748_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPost(v_simprocs_3736_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_, v_a_3741_, v_a_3742_, v_a_3743_, v_a_3744_, v_a_3745_, v_a_3746_);
lean_dec(v_a_3746_);
lean_dec_ref(v_a_3745_);
lean_dec(v_a_3744_);
lean_dec_ref(v_a_3743_);
lean_dec(v_a_3742_);
lean_dec_ref(v_a_3741_);
lean_dec(v_a_3740_);
lean_dec_ref(v_a_3739_);
lean_dec(v_a_3738_);
lean_dec_ref(v_simprocs_3736_);
return v_res_3748_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(lean_object* v_simprocs_3749_){
_start:
{
lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; 
lean_inc_ref(v_simprocs_3749_);
v___x_3750_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPre___boxed), 12, 1);
lean_closure_set(v___x_3750_, 0, v_simprocs_3749_);
v___x_3751_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPost___boxed), 12, 1);
lean_closure_set(v___x_3751_, 0, v_simprocs_3749_);
v___x_3752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3752_, 0, v___x_3750_);
lean_ctor_set(v___x_3752_, 1, v___x_3751_);
return v___x_3752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0___redArg(lean_object* v_x_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_){
_start:
{
lean_object* v_config_3761_; lean_object* v_sharedExprs_3762_; uint8_t v_verbose_3763_; uint8_t v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; 
v_config_3761_ = lean_ctor_get(v___y_3754_, 1);
v_sharedExprs_3762_ = lean_ctor_get(v___y_3754_, 0);
v_verbose_3763_ = lean_ctor_get_uint8(v_config_3761_, 0);
v___x_3764_ = 0;
v___x_3765_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v___x_3765_, 0, v_verbose_3763_);
lean_ctor_set_uint8(v___x_3765_, 1, v___x_3764_);
lean_ctor_set_uint8(v___x_3765_, 2, v___x_3764_);
lean_inc_ref(v_sharedExprs_3762_);
v___x_3766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3766_, 0, v_sharedExprs_3762_);
lean_ctor_set(v___x_3766_, 1, v___x_3765_);
lean_inc(v___y_3759_);
lean_inc_ref(v___y_3758_);
lean_inc(v___y_3757_);
lean_inc_ref(v___y_3756_);
lean_inc(v___y_3755_);
v___x_3767_ = lean_apply_7(v_x_3753_, v___x_3766_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_, lean_box(0));
return v___x_3767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0___redArg___boxed(lean_object* v_x_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_){
_start:
{
lean_object* v_res_3776_; 
v_res_3776_ = l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0___redArg(v_x_3768_, v___y_3769_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_, v___y_3774_);
lean_dec(v___y_3774_);
lean_dec_ref(v___y_3773_);
lean_dec(v___y_3772_);
lean_dec_ref(v___y_3771_);
lean_dec(v___y_3770_);
lean_dec_ref(v___y_3769_);
return v_res_3776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0(lean_object* v_00_u03b1_3777_, lean_object* v_x_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_){
_start:
{
lean_object* v___x_3786_; 
v___x_3786_ = l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0___redArg(v_x_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_);
return v___x_3786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0___boxed(lean_object* v_00_u03b1_3787_, lean_object* v_x_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_){
_start:
{
lean_object* v_res_3796_; 
v_res_3796_ = l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0(v_00_u03b1_3787_, v_x_3788_, v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_);
lean_dec(v___y_3794_);
lean_dec_ref(v___y_3793_);
lean_dec(v___y_3792_);
lean_dec_ref(v___y_3791_);
lean_dec(v___y_3790_);
lean_dec_ref(v___y_3789_);
return v_res_3796_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore___lam__0(lean_object* v_e_3797_, lean_object* v_config_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_){
_start:
{
lean_object* v___x_3806_; 
v___x_3806_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v___y_3804_);
if (lean_obj_tag(v___x_3806_) == 0)
{
lean_object* v_a_3807_; lean_object* v_methods_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; 
v_a_3807_ = lean_ctor_get(v___x_3806_, 0);
lean_inc(v_a_3807_);
lean_dec_ref_known(v___x_3806_, 1);
v_methods_3808_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(v_a_3807_);
v___x_3809_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_3809_, 0, v_e_3797_);
v___x_3810_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v___x_3809_, v_methods_3808_, v_config_3798_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_);
return v___x_3810_;
}
else
{
lean_object* v_a_3811_; lean_object* v___x_3813_; uint8_t v_isShared_3814_; uint8_t v_isSharedCheck_3818_; 
lean_dec_ref(v_config_3798_);
lean_dec_ref(v_e_3797_);
v_a_3811_ = lean_ctor_get(v___x_3806_, 0);
v_isSharedCheck_3818_ = !lean_is_exclusive(v___x_3806_);
if (v_isSharedCheck_3818_ == 0)
{
v___x_3813_ = v___x_3806_;
v_isShared_3814_ = v_isSharedCheck_3818_;
goto v_resetjp_3812_;
}
else
{
lean_inc(v_a_3811_);
lean_dec(v___x_3806_);
v___x_3813_ = lean_box(0);
v_isShared_3814_ = v_isSharedCheck_3818_;
goto v_resetjp_3812_;
}
v_resetjp_3812_:
{
lean_object* v___x_3816_; 
if (v_isShared_3814_ == 0)
{
v___x_3816_ = v___x_3813_;
goto v_reusejp_3815_;
}
else
{
lean_object* v_reuseFailAlloc_3817_; 
v_reuseFailAlloc_3817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3817_, 0, v_a_3811_);
v___x_3816_ = v_reuseFailAlloc_3817_;
goto v_reusejp_3815_;
}
v_reusejp_3815_:
{
return v___x_3816_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore___lam__0___boxed(lean_object* v_e_3819_, lean_object* v_config_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_){
_start:
{
lean_object* v_res_3828_; 
v_res_3828_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore___lam__0(v_e_3819_, v_config_3820_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
lean_dec(v___y_3826_);
lean_dec_ref(v___y_3825_);
lean_dec(v___y_3824_);
lean_dec_ref(v___y_3823_);
lean_dec(v___y_3822_);
lean_dec_ref(v___y_3821_);
return v_res_3828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(lean_object* v_e_3829_, lean_object* v_config_3830_, lean_object* v_a_3831_, lean_object* v_a_3832_, lean_object* v_a_3833_, lean_object* v_a_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_){
_start:
{
lean_object* v___f_3838_; lean_object* v___x_3839_; 
v___f_3838_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore___lam__0___boxed), 9, 2);
lean_closure_set(v___f_3838_, 0, v_e_3829_);
lean_closure_set(v___f_3838_, 1, v_config_3830_);
v___x_3839_ = l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0___redArg(v___f_3838_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_, v_a_3835_, v_a_3836_);
return v___x_3839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore___boxed(lean_object* v_e_3840_, lean_object* v_config_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_, lean_object* v_a_3844_, lean_object* v_a_3845_, lean_object* v_a_3846_, lean_object* v_a_3847_, lean_object* v_a_3848_){
_start:
{
lean_object* v_res_3849_; 
v_res_3849_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v_e_3840_, v_config_3841_, v_a_3842_, v_a_3843_, v_a_3844_, v_a_3845_, v_a_3846_, v_a_3847_);
lean_dec(v_a_3847_);
lean_dec_ref(v_a_3846_);
lean_dec(v_a_3845_);
lean_dec_ref(v_a_3844_);
lean_dec(v_a_3843_);
lean_dec_ref(v_a_3842_);
return v_res_3849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg(lean_object* v___y_3850_){
_start:
{
lean_object* v___x_3852_; lean_object* v_traceState_3853_; lean_object* v_traces_3854_; lean_object* v___x_3855_; lean_object* v_traceState_3856_; lean_object* v_env_3857_; lean_object* v_nextMacroScope_3858_; lean_object* v_ngen_3859_; lean_object* v_auxDeclNGen_3860_; lean_object* v_cache_3861_; lean_object* v_messages_3862_; lean_object* v_infoState_3863_; lean_object* v_snapshotTasks_3864_; lean_object* v___x_3866_; uint8_t v_isShared_3867_; uint8_t v_isSharedCheck_3885_; 
v___x_3852_ = lean_st_ref_get(v___y_3850_);
v_traceState_3853_ = lean_ctor_get(v___x_3852_, 4);
lean_inc_ref(v_traceState_3853_);
lean_dec(v___x_3852_);
v_traces_3854_ = lean_ctor_get(v_traceState_3853_, 0);
lean_inc_ref(v_traces_3854_);
lean_dec_ref(v_traceState_3853_);
v___x_3855_ = lean_st_ref_take(v___y_3850_);
v_traceState_3856_ = lean_ctor_get(v___x_3855_, 4);
v_env_3857_ = lean_ctor_get(v___x_3855_, 0);
v_nextMacroScope_3858_ = lean_ctor_get(v___x_3855_, 1);
v_ngen_3859_ = lean_ctor_get(v___x_3855_, 2);
v_auxDeclNGen_3860_ = lean_ctor_get(v___x_3855_, 3);
v_cache_3861_ = lean_ctor_get(v___x_3855_, 5);
v_messages_3862_ = lean_ctor_get(v___x_3855_, 6);
v_infoState_3863_ = lean_ctor_get(v___x_3855_, 7);
v_snapshotTasks_3864_ = lean_ctor_get(v___x_3855_, 8);
v_isSharedCheck_3885_ = !lean_is_exclusive(v___x_3855_);
if (v_isSharedCheck_3885_ == 0)
{
v___x_3866_ = v___x_3855_;
v_isShared_3867_ = v_isSharedCheck_3885_;
goto v_resetjp_3865_;
}
else
{
lean_inc(v_snapshotTasks_3864_);
lean_inc(v_infoState_3863_);
lean_inc(v_messages_3862_);
lean_inc(v_cache_3861_);
lean_inc(v_traceState_3856_);
lean_inc(v_auxDeclNGen_3860_);
lean_inc(v_ngen_3859_);
lean_inc(v_nextMacroScope_3858_);
lean_inc(v_env_3857_);
lean_dec(v___x_3855_);
v___x_3866_ = lean_box(0);
v_isShared_3867_ = v_isSharedCheck_3885_;
goto v_resetjp_3865_;
}
v_resetjp_3865_:
{
uint64_t v_tid_3868_; lean_object* v___x_3870_; uint8_t v_isShared_3871_; uint8_t v_isSharedCheck_3883_; 
v_tid_3868_ = lean_ctor_get_uint64(v_traceState_3856_, sizeof(void*)*1);
v_isSharedCheck_3883_ = !lean_is_exclusive(v_traceState_3856_);
if (v_isSharedCheck_3883_ == 0)
{
lean_object* v_unused_3884_; 
v_unused_3884_ = lean_ctor_get(v_traceState_3856_, 0);
lean_dec(v_unused_3884_);
v___x_3870_ = v_traceState_3856_;
v_isShared_3871_ = v_isSharedCheck_3883_;
goto v_resetjp_3869_;
}
else
{
lean_dec(v_traceState_3856_);
v___x_3870_ = lean_box(0);
v_isShared_3871_ = v_isSharedCheck_3883_;
goto v_resetjp_3869_;
}
v_resetjp_3869_:
{
lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3876_; 
v___x_3872_ = lean_unsigned_to_nat(32u);
v___x_3873_ = lean_mk_empty_array_with_capacity(v___x_3872_);
lean_dec_ref(v___x_3873_);
v___x_3874_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1);
if (v_isShared_3871_ == 0)
{
lean_ctor_set(v___x_3870_, 0, v___x_3874_);
v___x_3876_ = v___x_3870_;
goto v_reusejp_3875_;
}
else
{
lean_object* v_reuseFailAlloc_3882_; 
v_reuseFailAlloc_3882_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3882_, 0, v___x_3874_);
lean_ctor_set_uint64(v_reuseFailAlloc_3882_, sizeof(void*)*1, v_tid_3868_);
v___x_3876_ = v_reuseFailAlloc_3882_;
goto v_reusejp_3875_;
}
v_reusejp_3875_:
{
lean_object* v___x_3878_; 
if (v_isShared_3867_ == 0)
{
lean_ctor_set(v___x_3866_, 4, v___x_3876_);
v___x_3878_ = v___x_3866_;
goto v_reusejp_3877_;
}
else
{
lean_object* v_reuseFailAlloc_3881_; 
v_reuseFailAlloc_3881_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3881_, 0, v_env_3857_);
lean_ctor_set(v_reuseFailAlloc_3881_, 1, v_nextMacroScope_3858_);
lean_ctor_set(v_reuseFailAlloc_3881_, 2, v_ngen_3859_);
lean_ctor_set(v_reuseFailAlloc_3881_, 3, v_auxDeclNGen_3860_);
lean_ctor_set(v_reuseFailAlloc_3881_, 4, v___x_3876_);
lean_ctor_set(v_reuseFailAlloc_3881_, 5, v_cache_3861_);
lean_ctor_set(v_reuseFailAlloc_3881_, 6, v_messages_3862_);
lean_ctor_set(v_reuseFailAlloc_3881_, 7, v_infoState_3863_);
lean_ctor_set(v_reuseFailAlloc_3881_, 8, v_snapshotTasks_3864_);
v___x_3878_ = v_reuseFailAlloc_3881_;
goto v_reusejp_3877_;
}
v_reusejp_3877_:
{
lean_object* v___x_3879_; lean_object* v___x_3880_; 
v___x_3879_ = lean_st_ref_set(v___y_3850_, v___x_3878_);
v___x_3880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3880_, 0, v_traces_3854_);
return v___x_3880_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg___boxed(lean_object* v___y_3886_, lean_object* v___y_3887_){
_start:
{
lean_object* v_res_3888_; 
v_res_3888_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg(v___y_3886_);
lean_dec(v___y_3886_);
return v_res_3888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0(lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_){
_start:
{
lean_object* v___x_3894_; 
v___x_3894_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg(v___y_3892_);
return v___x_3894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___boxed(lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_){
_start:
{
lean_object* v_res_3900_; 
v_res_3900_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0(v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_);
lean_dec(v___y_3898_);
lean_dec_ref(v___y_3897_);
lean_dec(v___y_3896_);
lean_dec_ref(v___y_3895_);
return v_res_3900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0(lean_object* v_a_3901_, lean_object* v___x_3902_, lean_object* v___x_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_){
_start:
{
lean_object* v___x_3911_; 
v___x_3911_ = l_Lean_Meta_Sym_shareCommon(v_a_3901_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_);
if (lean_obj_tag(v___x_3911_) == 0)
{
lean_object* v_a_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; 
v_a_3912_ = lean_ctor_get(v___x_3911_, 0);
lean_inc(v_a_3912_);
lean_dec_ref_known(v___x_3911_, 1);
v___x_3913_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_3913_, 0, v_a_3912_);
v___x_3914_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v___x_3913_, v___x_3902_, v___x_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_);
return v___x_3914_;
}
else
{
lean_object* v_a_3915_; lean_object* v___x_3917_; uint8_t v_isShared_3918_; uint8_t v_isSharedCheck_3922_; 
lean_dec_ref(v___x_3903_);
lean_dec_ref(v___x_3902_);
v_a_3915_ = lean_ctor_get(v___x_3911_, 0);
v_isSharedCheck_3922_ = !lean_is_exclusive(v___x_3911_);
if (v_isSharedCheck_3922_ == 0)
{
v___x_3917_ = v___x_3911_;
v_isShared_3918_ = v_isSharedCheck_3922_;
goto v_resetjp_3916_;
}
else
{
lean_inc(v_a_3915_);
lean_dec(v___x_3911_);
v___x_3917_ = lean_box(0);
v_isShared_3918_ = v_isSharedCheck_3922_;
goto v_resetjp_3916_;
}
v_resetjp_3916_:
{
lean_object* v___x_3920_; 
if (v_isShared_3918_ == 0)
{
v___x_3920_ = v___x_3917_;
goto v_reusejp_3919_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v_a_3915_);
v___x_3920_ = v_reuseFailAlloc_3921_;
goto v_reusejp_3919_;
}
v_reusejp_3919_:
{
return v___x_3920_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___boxed(lean_object* v_a_3923_, lean_object* v___x_3924_, lean_object* v___x_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_){
_start:
{
lean_object* v_res_3933_; 
v_res_3933_ = l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0(v_a_3923_, v___x_3924_, v___x_3925_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_);
lean_dec(v___y_3931_);
lean_dec_ref(v___y_3930_);
lean_dec(v___y_3929_);
lean_dec_ref(v___y_3928_);
lean_dec(v___y_3927_);
lean_dec_ref(v___y_3926_);
return v_res_3933_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3935_; lean_object* v___x_3936_; 
v___x_3935_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__0));
v___x_3936_ = l_Lean_stringToMessageData(v___x_3935_);
return v___x_3936_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3938_; lean_object* v___x_3939_; 
v___x_3938_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__2));
v___x_3939_ = l_Lean_stringToMessageData(v___x_3938_);
return v___x_3939_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__5(void){
_start:
{
lean_object* v___x_3941_; lean_object* v___x_3942_; 
v___x_3941_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__4));
v___x_3942_ = l_Lean_stringToMessageData(v___x_3941_);
return v___x_3942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1(lean_object* v_e_3943_, lean_object* v_x_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_){
_start:
{
if (lean_obj_tag(v_x_3944_) == 0)
{
lean_object* v_a_3950_; lean_object* v___x_3952_; uint8_t v_isShared_3953_; uint8_t v_isSharedCheck_3960_; 
lean_dec_ref(v_e_3943_);
v_a_3950_ = lean_ctor_get(v_x_3944_, 0);
v_isSharedCheck_3960_ = !lean_is_exclusive(v_x_3944_);
if (v_isSharedCheck_3960_ == 0)
{
v___x_3952_ = v_x_3944_;
v_isShared_3953_ = v_isSharedCheck_3960_;
goto v_resetjp_3951_;
}
else
{
lean_inc(v_a_3950_);
lean_dec(v_x_3944_);
v___x_3952_ = lean_box(0);
v_isShared_3953_ = v_isSharedCheck_3960_;
goto v_resetjp_3951_;
}
v_resetjp_3951_:
{
lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3958_; 
v___x_3954_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__1);
v___x_3955_ = l_Lean_Exception_toMessageData(v_a_3950_);
v___x_3956_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3956_, 0, v___x_3954_);
lean_ctor_set(v___x_3956_, 1, v___x_3955_);
if (v_isShared_3953_ == 0)
{
lean_ctor_set(v___x_3952_, 0, v___x_3956_);
v___x_3958_ = v___x_3952_;
goto v_reusejp_3957_;
}
else
{
lean_object* v_reuseFailAlloc_3959_; 
v_reuseFailAlloc_3959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3959_, 0, v___x_3956_);
v___x_3958_ = v_reuseFailAlloc_3959_;
goto v_reusejp_3957_;
}
v_reusejp_3957_:
{
return v___x_3958_;
}
}
}
else
{
lean_object* v_a_3961_; lean_object* v___x_3963_; uint8_t v_isShared_3964_; uint8_t v_isSharedCheck_3982_; 
v_a_3961_ = lean_ctor_get(v_x_3944_, 0);
v_isSharedCheck_3982_ = !lean_is_exclusive(v_x_3944_);
if (v_isSharedCheck_3982_ == 0)
{
v___x_3963_ = v_x_3944_;
v_isShared_3964_ = v_isSharedCheck_3982_;
goto v_resetjp_3962_;
}
else
{
lean_inc(v_a_3961_);
lean_dec(v_x_3944_);
v___x_3963_ = lean_box(0);
v_isShared_3964_ = v_isSharedCheck_3982_;
goto v_resetjp_3962_;
}
v_resetjp_3962_:
{
if (lean_obj_tag(v_a_3961_) == 0)
{
lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3969_; 
lean_dec_ref_known(v_a_3961_, 0);
v___x_3965_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__3, &l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__3);
v___x_3966_ = l_Lean_indentExpr(v_e_3943_);
v___x_3967_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3967_, 0, v___x_3965_);
lean_ctor_set(v___x_3967_, 1, v___x_3966_);
if (v_isShared_3964_ == 0)
{
lean_ctor_set_tag(v___x_3963_, 0);
lean_ctor_set(v___x_3963_, 0, v___x_3967_);
v___x_3969_ = v___x_3963_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_3970_; 
v_reuseFailAlloc_3970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3970_, 0, v___x_3967_);
v___x_3969_ = v_reuseFailAlloc_3970_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
return v___x_3969_;
}
}
else
{
lean_object* v_e_x27_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3980_; 
v_e_x27_3971_ = lean_ctor_get(v_a_3961_, 0);
lean_inc_ref(v_e_x27_3971_);
lean_dec_ref_known(v_a_3961_, 2);
v___x_3972_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__5, &l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__5_once, _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__5);
v___x_3973_ = l_Lean_indentExpr(v_e_3943_);
v___x_3974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3974_, 0, v___x_3972_);
lean_ctor_set(v___x_3974_, 1, v___x_3973_);
v___x_3975_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_3976_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3976_, 0, v___x_3974_);
lean_ctor_set(v___x_3976_, 1, v___x_3975_);
v___x_3977_ = l_Lean_indentExpr(v_e_x27_3971_);
v___x_3978_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3978_, 0, v___x_3976_);
lean_ctor_set(v___x_3978_, 1, v___x_3977_);
if (v_isShared_3964_ == 0)
{
lean_ctor_set_tag(v___x_3963_, 0);
lean_ctor_set(v___x_3963_, 0, v___x_3978_);
v___x_3980_ = v___x_3963_;
goto v_reusejp_3979_;
}
else
{
lean_object* v_reuseFailAlloc_3981_; 
v_reuseFailAlloc_3981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3981_, 0, v___x_3978_);
v___x_3980_ = v_reuseFailAlloc_3981_;
goto v_reusejp_3979_;
}
v_reusejp_3979_:
{
return v___x_3980_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___boxed(lean_object* v_e_3983_, lean_object* v_x_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_){
_start:
{
lean_object* v_res_3990_; 
v_res_3990_ = l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1(v_e_3983_, v_x_3984_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_);
lean_dec(v___y_3988_);
lean_dec_ref(v___y_3987_);
lean_dec(v___y_3986_);
lean_dec_ref(v___y_3985_);
return v_res_3990_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg(lean_object* v_x_3991_){
_start:
{
if (lean_obj_tag(v_x_3991_) == 0)
{
lean_object* v_a_3993_; lean_object* v___x_3995_; uint8_t v_isShared_3996_; uint8_t v_isSharedCheck_4000_; 
v_a_3993_ = lean_ctor_get(v_x_3991_, 0);
v_isSharedCheck_4000_ = !lean_is_exclusive(v_x_3991_);
if (v_isSharedCheck_4000_ == 0)
{
v___x_3995_ = v_x_3991_;
v_isShared_3996_ = v_isSharedCheck_4000_;
goto v_resetjp_3994_;
}
else
{
lean_inc(v_a_3993_);
lean_dec(v_x_3991_);
v___x_3995_ = lean_box(0);
v_isShared_3996_ = v_isSharedCheck_4000_;
goto v_resetjp_3994_;
}
v_resetjp_3994_:
{
lean_object* v___x_3998_; 
if (v_isShared_3996_ == 0)
{
lean_ctor_set_tag(v___x_3995_, 1);
v___x_3998_ = v___x_3995_;
goto v_reusejp_3997_;
}
else
{
lean_object* v_reuseFailAlloc_3999_; 
v_reuseFailAlloc_3999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3999_, 0, v_a_3993_);
v___x_3998_ = v_reuseFailAlloc_3999_;
goto v_reusejp_3997_;
}
v_reusejp_3997_:
{
return v___x_3998_;
}
}
}
else
{
lean_object* v_a_4001_; lean_object* v___x_4003_; uint8_t v_isShared_4004_; uint8_t v_isSharedCheck_4008_; 
v_a_4001_ = lean_ctor_get(v_x_3991_, 0);
v_isSharedCheck_4008_ = !lean_is_exclusive(v_x_3991_);
if (v_isSharedCheck_4008_ == 0)
{
v___x_4003_ = v_x_3991_;
v_isShared_4004_ = v_isSharedCheck_4008_;
goto v_resetjp_4002_;
}
else
{
lean_inc(v_a_4001_);
lean_dec(v_x_3991_);
v___x_4003_ = lean_box(0);
v_isShared_4004_ = v_isSharedCheck_4008_;
goto v_resetjp_4002_;
}
v_resetjp_4002_:
{
lean_object* v___x_4006_; 
if (v_isShared_4004_ == 0)
{
lean_ctor_set_tag(v___x_4003_, 0);
v___x_4006_ = v___x_4003_;
goto v_reusejp_4005_;
}
else
{
lean_object* v_reuseFailAlloc_4007_; 
v_reuseFailAlloc_4007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4007_, 0, v_a_4001_);
v___x_4006_ = v_reuseFailAlloc_4007_;
goto v_reusejp_4005_;
}
v_reusejp_4005_:
{
return v___x_4006_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg___boxed(lean_object* v_x_4009_, lean_object* v___y_4010_){
_start:
{
lean_object* v_res_4011_; 
v_res_4011_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg(v_x_4009_);
return v_res_4011_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__1(lean_object* v_oldTraces_4012_, lean_object* v_data_4013_, lean_object* v_ref_4014_, lean_object* v_msg_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_){
_start:
{
lean_object* v_fileName_4021_; lean_object* v_fileMap_4022_; lean_object* v_options_4023_; lean_object* v_currRecDepth_4024_; lean_object* v_maxRecDepth_4025_; lean_object* v_ref_4026_; lean_object* v_currNamespace_4027_; lean_object* v_openDecls_4028_; lean_object* v_initHeartbeats_4029_; lean_object* v_maxHeartbeats_4030_; lean_object* v_quotContext_4031_; lean_object* v_currMacroScope_4032_; uint8_t v_diag_4033_; lean_object* v_cancelTk_x3f_4034_; uint8_t v_suppressElabErrors_4035_; lean_object* v_inheritedTraceOptions_4036_; lean_object* v___x_4037_; lean_object* v_traceState_4038_; lean_object* v_traces_4039_; lean_object* v_ref_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; size_t v_sz_4043_; size_t v___x_4044_; lean_object* v___x_4045_; lean_object* v_msg_4046_; lean_object* v___x_4047_; lean_object* v_a_4048_; lean_object* v___x_4050_; uint8_t v_isShared_4051_; uint8_t v_isSharedCheck_4085_; 
v_fileName_4021_ = lean_ctor_get(v___y_4018_, 0);
v_fileMap_4022_ = lean_ctor_get(v___y_4018_, 1);
v_options_4023_ = lean_ctor_get(v___y_4018_, 2);
v_currRecDepth_4024_ = lean_ctor_get(v___y_4018_, 3);
v_maxRecDepth_4025_ = lean_ctor_get(v___y_4018_, 4);
v_ref_4026_ = lean_ctor_get(v___y_4018_, 5);
v_currNamespace_4027_ = lean_ctor_get(v___y_4018_, 6);
v_openDecls_4028_ = lean_ctor_get(v___y_4018_, 7);
v_initHeartbeats_4029_ = lean_ctor_get(v___y_4018_, 8);
v_maxHeartbeats_4030_ = lean_ctor_get(v___y_4018_, 9);
v_quotContext_4031_ = lean_ctor_get(v___y_4018_, 10);
v_currMacroScope_4032_ = lean_ctor_get(v___y_4018_, 11);
v_diag_4033_ = lean_ctor_get_uint8(v___y_4018_, sizeof(void*)*14);
v_cancelTk_x3f_4034_ = lean_ctor_get(v___y_4018_, 12);
v_suppressElabErrors_4035_ = lean_ctor_get_uint8(v___y_4018_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_4036_ = lean_ctor_get(v___y_4018_, 13);
v___x_4037_ = lean_st_ref_get(v___y_4019_);
v_traceState_4038_ = lean_ctor_get(v___x_4037_, 4);
lean_inc_ref(v_traceState_4038_);
lean_dec(v___x_4037_);
v_traces_4039_ = lean_ctor_get(v_traceState_4038_, 0);
lean_inc_ref(v_traces_4039_);
lean_dec_ref(v_traceState_4038_);
v_ref_4040_ = l_Lean_replaceRef(v_ref_4014_, v_ref_4026_);
lean_inc_ref(v_inheritedTraceOptions_4036_);
lean_inc(v_cancelTk_x3f_4034_);
lean_inc(v_currMacroScope_4032_);
lean_inc(v_quotContext_4031_);
lean_inc(v_maxHeartbeats_4030_);
lean_inc(v_initHeartbeats_4029_);
lean_inc(v_openDecls_4028_);
lean_inc(v_currNamespace_4027_);
lean_inc(v_maxRecDepth_4025_);
lean_inc(v_currRecDepth_4024_);
lean_inc_ref(v_options_4023_);
lean_inc_ref(v_fileMap_4022_);
lean_inc_ref(v_fileName_4021_);
v___x_4041_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_4041_, 0, v_fileName_4021_);
lean_ctor_set(v___x_4041_, 1, v_fileMap_4022_);
lean_ctor_set(v___x_4041_, 2, v_options_4023_);
lean_ctor_set(v___x_4041_, 3, v_currRecDepth_4024_);
lean_ctor_set(v___x_4041_, 4, v_maxRecDepth_4025_);
lean_ctor_set(v___x_4041_, 5, v_ref_4040_);
lean_ctor_set(v___x_4041_, 6, v_currNamespace_4027_);
lean_ctor_set(v___x_4041_, 7, v_openDecls_4028_);
lean_ctor_set(v___x_4041_, 8, v_initHeartbeats_4029_);
lean_ctor_set(v___x_4041_, 9, v_maxHeartbeats_4030_);
lean_ctor_set(v___x_4041_, 10, v_quotContext_4031_);
lean_ctor_set(v___x_4041_, 11, v_currMacroScope_4032_);
lean_ctor_set(v___x_4041_, 12, v_cancelTk_x3f_4034_);
lean_ctor_set(v___x_4041_, 13, v_inheritedTraceOptions_4036_);
lean_ctor_set_uint8(v___x_4041_, sizeof(void*)*14, v_diag_4033_);
lean_ctor_set_uint8(v___x_4041_, sizeof(void*)*14 + 1, v_suppressElabErrors_4035_);
v___x_4042_ = l_Lean_PersistentArray_toArray___redArg(v_traces_4039_);
lean_dec_ref(v_traces_4039_);
v_sz_4043_ = lean_array_size(v___x_4042_);
v___x_4044_ = ((size_t)0ULL);
v___x_4045_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4_spec__5(v_sz_4043_, v___x_4044_, v___x_4042_);
v_msg_4046_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_4046_, 0, v_data_4013_);
lean_ctor_set(v_msg_4046_, 1, v_msg_4015_);
lean_ctor_set(v_msg_4046_, 2, v___x_4045_);
v___x_4047_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0_spec__0(v_msg_4046_, v___y_4016_, v___y_4017_, v___x_4041_, v___y_4019_);
lean_dec_ref_known(v___x_4041_, 14);
v_a_4048_ = lean_ctor_get(v___x_4047_, 0);
v_isSharedCheck_4085_ = !lean_is_exclusive(v___x_4047_);
if (v_isSharedCheck_4085_ == 0)
{
v___x_4050_ = v___x_4047_;
v_isShared_4051_ = v_isSharedCheck_4085_;
goto v_resetjp_4049_;
}
else
{
lean_inc(v_a_4048_);
lean_dec(v___x_4047_);
v___x_4050_ = lean_box(0);
v_isShared_4051_ = v_isSharedCheck_4085_;
goto v_resetjp_4049_;
}
v_resetjp_4049_:
{
lean_object* v___x_4052_; lean_object* v_traceState_4053_; lean_object* v_env_4054_; lean_object* v_nextMacroScope_4055_; lean_object* v_ngen_4056_; lean_object* v_auxDeclNGen_4057_; lean_object* v_cache_4058_; lean_object* v_messages_4059_; lean_object* v_infoState_4060_; lean_object* v_snapshotTasks_4061_; lean_object* v___x_4063_; uint8_t v_isShared_4064_; uint8_t v_isSharedCheck_4084_; 
v___x_4052_ = lean_st_ref_take(v___y_4019_);
v_traceState_4053_ = lean_ctor_get(v___x_4052_, 4);
v_env_4054_ = lean_ctor_get(v___x_4052_, 0);
v_nextMacroScope_4055_ = lean_ctor_get(v___x_4052_, 1);
v_ngen_4056_ = lean_ctor_get(v___x_4052_, 2);
v_auxDeclNGen_4057_ = lean_ctor_get(v___x_4052_, 3);
v_cache_4058_ = lean_ctor_get(v___x_4052_, 5);
v_messages_4059_ = lean_ctor_get(v___x_4052_, 6);
v_infoState_4060_ = lean_ctor_get(v___x_4052_, 7);
v_snapshotTasks_4061_ = lean_ctor_get(v___x_4052_, 8);
v_isSharedCheck_4084_ = !lean_is_exclusive(v___x_4052_);
if (v_isSharedCheck_4084_ == 0)
{
v___x_4063_ = v___x_4052_;
v_isShared_4064_ = v_isSharedCheck_4084_;
goto v_resetjp_4062_;
}
else
{
lean_inc(v_snapshotTasks_4061_);
lean_inc(v_infoState_4060_);
lean_inc(v_messages_4059_);
lean_inc(v_cache_4058_);
lean_inc(v_traceState_4053_);
lean_inc(v_auxDeclNGen_4057_);
lean_inc(v_ngen_4056_);
lean_inc(v_nextMacroScope_4055_);
lean_inc(v_env_4054_);
lean_dec(v___x_4052_);
v___x_4063_ = lean_box(0);
v_isShared_4064_ = v_isSharedCheck_4084_;
goto v_resetjp_4062_;
}
v_resetjp_4062_:
{
uint64_t v_tid_4065_; lean_object* v___x_4067_; uint8_t v_isShared_4068_; uint8_t v_isSharedCheck_4082_; 
v_tid_4065_ = lean_ctor_get_uint64(v_traceState_4053_, sizeof(void*)*1);
v_isSharedCheck_4082_ = !lean_is_exclusive(v_traceState_4053_);
if (v_isSharedCheck_4082_ == 0)
{
lean_object* v_unused_4083_; 
v_unused_4083_ = lean_ctor_get(v_traceState_4053_, 0);
lean_dec(v_unused_4083_);
v___x_4067_ = v_traceState_4053_;
v_isShared_4068_ = v_isSharedCheck_4082_;
goto v_resetjp_4066_;
}
else
{
lean_dec(v_traceState_4053_);
v___x_4067_ = lean_box(0);
v_isShared_4068_ = v_isSharedCheck_4082_;
goto v_resetjp_4066_;
}
v_resetjp_4066_:
{
lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4072_; 
v___x_4069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4069_, 0, v_ref_4014_);
lean_ctor_set(v___x_4069_, 1, v_a_4048_);
v___x_4070_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_4012_, v___x_4069_);
if (v_isShared_4068_ == 0)
{
lean_ctor_set(v___x_4067_, 0, v___x_4070_);
v___x_4072_ = v___x_4067_;
goto v_reusejp_4071_;
}
else
{
lean_object* v_reuseFailAlloc_4081_; 
v_reuseFailAlloc_4081_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4081_, 0, v___x_4070_);
lean_ctor_set_uint64(v_reuseFailAlloc_4081_, sizeof(void*)*1, v_tid_4065_);
v___x_4072_ = v_reuseFailAlloc_4081_;
goto v_reusejp_4071_;
}
v_reusejp_4071_:
{
lean_object* v___x_4074_; 
if (v_isShared_4064_ == 0)
{
lean_ctor_set(v___x_4063_, 4, v___x_4072_);
v___x_4074_ = v___x_4063_;
goto v_reusejp_4073_;
}
else
{
lean_object* v_reuseFailAlloc_4080_; 
v_reuseFailAlloc_4080_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4080_, 0, v_env_4054_);
lean_ctor_set(v_reuseFailAlloc_4080_, 1, v_nextMacroScope_4055_);
lean_ctor_set(v_reuseFailAlloc_4080_, 2, v_ngen_4056_);
lean_ctor_set(v_reuseFailAlloc_4080_, 3, v_auxDeclNGen_4057_);
lean_ctor_set(v_reuseFailAlloc_4080_, 4, v___x_4072_);
lean_ctor_set(v_reuseFailAlloc_4080_, 5, v_cache_4058_);
lean_ctor_set(v_reuseFailAlloc_4080_, 6, v_messages_4059_);
lean_ctor_set(v_reuseFailAlloc_4080_, 7, v_infoState_4060_);
lean_ctor_set(v_reuseFailAlloc_4080_, 8, v_snapshotTasks_4061_);
v___x_4074_ = v_reuseFailAlloc_4080_;
goto v_reusejp_4073_;
}
v_reusejp_4073_:
{
lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4078_; 
v___x_4075_ = lean_st_ref_set(v___y_4019_, v___x_4074_);
v___x_4076_ = lean_box(0);
if (v_isShared_4051_ == 0)
{
lean_ctor_set(v___x_4050_, 0, v___x_4076_);
v___x_4078_ = v___x_4050_;
goto v_reusejp_4077_;
}
else
{
lean_object* v_reuseFailAlloc_4079_; 
v_reuseFailAlloc_4079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4079_, 0, v___x_4076_);
v___x_4078_ = v_reuseFailAlloc_4079_;
goto v_reusejp_4077_;
}
v_reusejp_4077_:
{
return v___x_4078_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__1___boxed(lean_object* v_oldTraces_4086_, lean_object* v_data_4087_, lean_object* v_ref_4088_, lean_object* v_msg_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_){
_start:
{
lean_object* v_res_4095_; 
v_res_4095_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__1(v_oldTraces_4086_, v_data_4087_, v_ref_4088_, v_msg_4089_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_);
lean_dec(v___y_4093_);
lean_dec_ref(v___y_4092_);
lean_dec(v___y_4091_);
lean_dec_ref(v___y_4090_);
return v_res_4095_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1(lean_object* v_cls_4096_, uint8_t v_collapsed_4097_, lean_object* v_tag_4098_, lean_object* v_opts_4099_, uint8_t v_clsEnabled_4100_, lean_object* v_oldTraces_4101_, lean_object* v_msg_4102_, lean_object* v_resStartStop_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_){
_start:
{
lean_object* v_fst_4109_; lean_object* v_snd_4110_; lean_object* v___y_4112_; lean_object* v___y_4113_; lean_object* v_data_4114_; lean_object* v_fst_4125_; lean_object* v_snd_4126_; lean_object* v___x_4127_; uint8_t v___x_4128_; lean_object* v___y_4130_; lean_object* v_a_4131_; uint8_t v___y_4146_; double v___y_4177_; 
v_fst_4109_ = lean_ctor_get(v_resStartStop_4103_, 0);
lean_inc(v_fst_4109_);
v_snd_4110_ = lean_ctor_get(v_resStartStop_4103_, 1);
lean_inc(v_snd_4110_);
lean_dec_ref(v_resStartStop_4103_);
v_fst_4125_ = lean_ctor_get(v_snd_4110_, 0);
lean_inc(v_fst_4125_);
v_snd_4126_ = lean_ctor_get(v_snd_4110_, 1);
lean_inc(v_snd_4126_);
lean_dec(v_snd_4110_);
v___x_4127_ = l_Lean_trace_profiler;
v___x_4128_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_4099_, v___x_4127_);
if (v___x_4128_ == 0)
{
v___y_4146_ = v___x_4128_;
goto v___jp_4145_;
}
else
{
lean_object* v___x_4182_; uint8_t v___x_4183_; 
v___x_4182_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4183_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_4099_, v___x_4182_);
if (v___x_4183_ == 0)
{
lean_object* v___x_4184_; lean_object* v___x_4185_; double v___x_4186_; double v___x_4187_; double v___x_4188_; 
v___x_4184_ = l_Lean_trace_profiler_threshold;
v___x_4185_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_4099_, v___x_4184_);
v___x_4186_ = lean_float_of_nat(v___x_4185_);
v___x_4187_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2);
v___x_4188_ = lean_float_div(v___x_4186_, v___x_4187_);
v___y_4177_ = v___x_4188_;
goto v___jp_4176_;
}
else
{
lean_object* v___x_4189_; lean_object* v___x_4190_; double v___x_4191_; 
v___x_4189_ = l_Lean_trace_profiler_threshold;
v___x_4190_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_4099_, v___x_4189_);
v___x_4191_ = lean_float_of_nat(v___x_4190_);
v___y_4177_ = v___x_4191_;
goto v___jp_4176_;
}
}
v___jp_4111_:
{
lean_object* v___x_4115_; 
lean_inc(v___y_4112_);
v___x_4115_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__1(v_oldTraces_4101_, v_data_4114_, v___y_4112_, v___y_4113_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_);
if (lean_obj_tag(v___x_4115_) == 0)
{
lean_object* v___x_4116_; 
lean_dec_ref_known(v___x_4115_, 1);
v___x_4116_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg(v_fst_4109_);
return v___x_4116_;
}
else
{
lean_object* v_a_4117_; lean_object* v___x_4119_; uint8_t v_isShared_4120_; uint8_t v_isSharedCheck_4124_; 
lean_dec(v_fst_4109_);
v_a_4117_ = lean_ctor_get(v___x_4115_, 0);
v_isSharedCheck_4124_ = !lean_is_exclusive(v___x_4115_);
if (v_isSharedCheck_4124_ == 0)
{
v___x_4119_ = v___x_4115_;
v_isShared_4120_ = v_isSharedCheck_4124_;
goto v_resetjp_4118_;
}
else
{
lean_inc(v_a_4117_);
lean_dec(v___x_4115_);
v___x_4119_ = lean_box(0);
v_isShared_4120_ = v_isSharedCheck_4124_;
goto v_resetjp_4118_;
}
v_resetjp_4118_:
{
lean_object* v___x_4122_; 
if (v_isShared_4120_ == 0)
{
v___x_4122_ = v___x_4119_;
goto v_reusejp_4121_;
}
else
{
lean_object* v_reuseFailAlloc_4123_; 
v_reuseFailAlloc_4123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4123_, 0, v_a_4117_);
v___x_4122_ = v_reuseFailAlloc_4123_;
goto v_reusejp_4121_;
}
v_reusejp_4121_:
{
return v___x_4122_;
}
}
}
}
v___jp_4129_:
{
uint8_t v_result_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; double v___x_4135_; lean_object* v_data_4136_; 
v_result_4132_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__6(v_fst_4109_);
v___x_4133_ = lean_box(v_result_4132_);
v___x_4134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4134_, 0, v___x_4133_);
v___x_4135_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_4098_);
lean_inc_ref(v___x_4134_);
lean_inc(v_cls_4096_);
v_data_4136_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4136_, 0, v_cls_4096_);
lean_ctor_set(v_data_4136_, 1, v___x_4134_);
lean_ctor_set(v_data_4136_, 2, v_tag_4098_);
lean_ctor_set_float(v_data_4136_, sizeof(void*)*3, v___x_4135_);
lean_ctor_set_float(v_data_4136_, sizeof(void*)*3 + 8, v___x_4135_);
lean_ctor_set_uint8(v_data_4136_, sizeof(void*)*3 + 16, v_collapsed_4097_);
if (v___x_4128_ == 0)
{
lean_dec_ref_known(v___x_4134_, 1);
lean_dec(v_snd_4126_);
lean_dec(v_fst_4125_);
lean_dec_ref(v_tag_4098_);
lean_dec(v_cls_4096_);
v___y_4112_ = v___y_4130_;
v___y_4113_ = v_a_4131_;
v_data_4114_ = v_data_4136_;
goto v___jp_4111_;
}
else
{
lean_object* v_data_4137_; double v___x_4138_; double v___x_4139_; 
lean_dec_ref_known(v_data_4136_, 3);
v_data_4137_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4137_, 0, v_cls_4096_);
lean_ctor_set(v_data_4137_, 1, v___x_4134_);
lean_ctor_set(v_data_4137_, 2, v_tag_4098_);
v___x_4138_ = lean_unbox_float(v_fst_4125_);
lean_dec(v_fst_4125_);
lean_ctor_set_float(v_data_4137_, sizeof(void*)*3, v___x_4138_);
v___x_4139_ = lean_unbox_float(v_snd_4126_);
lean_dec(v_snd_4126_);
lean_ctor_set_float(v_data_4137_, sizeof(void*)*3 + 8, v___x_4139_);
lean_ctor_set_uint8(v_data_4137_, sizeof(void*)*3 + 16, v_collapsed_4097_);
v___y_4112_ = v___y_4130_;
v___y_4113_ = v_a_4131_;
v_data_4114_ = v_data_4137_;
goto v___jp_4111_;
}
}
v___jp_4140_:
{
lean_object* v_ref_4141_; lean_object* v___x_4142_; 
v_ref_4141_ = lean_ctor_get(v___y_4106_, 5);
lean_inc(v___y_4107_);
lean_inc_ref(v___y_4106_);
lean_inc(v___y_4105_);
lean_inc_ref(v___y_4104_);
lean_inc(v_fst_4109_);
v___x_4142_ = lean_apply_6(v_msg_4102_, v_fst_4109_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, lean_box(0));
if (lean_obj_tag(v___x_4142_) == 0)
{
lean_object* v_a_4143_; 
v_a_4143_ = lean_ctor_get(v___x_4142_, 0);
lean_inc(v_a_4143_);
lean_dec_ref_known(v___x_4142_, 1);
v___y_4130_ = v_ref_4141_;
v_a_4131_ = v_a_4143_;
goto v___jp_4129_;
}
else
{
lean_object* v___x_4144_; 
lean_dec_ref_known(v___x_4142_, 1);
v___x_4144_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1);
v___y_4130_ = v_ref_4141_;
v_a_4131_ = v___x_4144_;
goto v___jp_4129_;
}
}
v___jp_4145_:
{
if (v_clsEnabled_4100_ == 0)
{
if (v___y_4146_ == 0)
{
lean_object* v___x_4147_; lean_object* v_traceState_4148_; lean_object* v_env_4149_; lean_object* v_nextMacroScope_4150_; lean_object* v_ngen_4151_; lean_object* v_auxDeclNGen_4152_; lean_object* v_cache_4153_; lean_object* v_messages_4154_; lean_object* v_infoState_4155_; lean_object* v_snapshotTasks_4156_; lean_object* v___x_4158_; uint8_t v_isShared_4159_; uint8_t v_isSharedCheck_4175_; 
lean_dec(v_snd_4126_);
lean_dec(v_fst_4125_);
lean_dec_ref(v_msg_4102_);
lean_dec_ref(v_tag_4098_);
lean_dec(v_cls_4096_);
v___x_4147_ = lean_st_ref_take(v___y_4107_);
v_traceState_4148_ = lean_ctor_get(v___x_4147_, 4);
v_env_4149_ = lean_ctor_get(v___x_4147_, 0);
v_nextMacroScope_4150_ = lean_ctor_get(v___x_4147_, 1);
v_ngen_4151_ = lean_ctor_get(v___x_4147_, 2);
v_auxDeclNGen_4152_ = lean_ctor_get(v___x_4147_, 3);
v_cache_4153_ = lean_ctor_get(v___x_4147_, 5);
v_messages_4154_ = lean_ctor_get(v___x_4147_, 6);
v_infoState_4155_ = lean_ctor_get(v___x_4147_, 7);
v_snapshotTasks_4156_ = lean_ctor_get(v___x_4147_, 8);
v_isSharedCheck_4175_ = !lean_is_exclusive(v___x_4147_);
if (v_isSharedCheck_4175_ == 0)
{
v___x_4158_ = v___x_4147_;
v_isShared_4159_ = v_isSharedCheck_4175_;
goto v_resetjp_4157_;
}
else
{
lean_inc(v_snapshotTasks_4156_);
lean_inc(v_infoState_4155_);
lean_inc(v_messages_4154_);
lean_inc(v_cache_4153_);
lean_inc(v_traceState_4148_);
lean_inc(v_auxDeclNGen_4152_);
lean_inc(v_ngen_4151_);
lean_inc(v_nextMacroScope_4150_);
lean_inc(v_env_4149_);
lean_dec(v___x_4147_);
v___x_4158_ = lean_box(0);
v_isShared_4159_ = v_isSharedCheck_4175_;
goto v_resetjp_4157_;
}
v_resetjp_4157_:
{
uint64_t v_tid_4160_; lean_object* v_traces_4161_; lean_object* v___x_4163_; uint8_t v_isShared_4164_; uint8_t v_isSharedCheck_4174_; 
v_tid_4160_ = lean_ctor_get_uint64(v_traceState_4148_, sizeof(void*)*1);
v_traces_4161_ = lean_ctor_get(v_traceState_4148_, 0);
v_isSharedCheck_4174_ = !lean_is_exclusive(v_traceState_4148_);
if (v_isSharedCheck_4174_ == 0)
{
v___x_4163_ = v_traceState_4148_;
v_isShared_4164_ = v_isSharedCheck_4174_;
goto v_resetjp_4162_;
}
else
{
lean_inc(v_traces_4161_);
lean_dec(v_traceState_4148_);
v___x_4163_ = lean_box(0);
v_isShared_4164_ = v_isSharedCheck_4174_;
goto v_resetjp_4162_;
}
v_resetjp_4162_:
{
lean_object* v___x_4165_; lean_object* v___x_4167_; 
v___x_4165_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_4101_, v_traces_4161_);
lean_dec_ref(v_traces_4161_);
if (v_isShared_4164_ == 0)
{
lean_ctor_set(v___x_4163_, 0, v___x_4165_);
v___x_4167_ = v___x_4163_;
goto v_reusejp_4166_;
}
else
{
lean_object* v_reuseFailAlloc_4173_; 
v_reuseFailAlloc_4173_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4173_, 0, v___x_4165_);
lean_ctor_set_uint64(v_reuseFailAlloc_4173_, sizeof(void*)*1, v_tid_4160_);
v___x_4167_ = v_reuseFailAlloc_4173_;
goto v_reusejp_4166_;
}
v_reusejp_4166_:
{
lean_object* v___x_4169_; 
if (v_isShared_4159_ == 0)
{
lean_ctor_set(v___x_4158_, 4, v___x_4167_);
v___x_4169_ = v___x_4158_;
goto v_reusejp_4168_;
}
else
{
lean_object* v_reuseFailAlloc_4172_; 
v_reuseFailAlloc_4172_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4172_, 0, v_env_4149_);
lean_ctor_set(v_reuseFailAlloc_4172_, 1, v_nextMacroScope_4150_);
lean_ctor_set(v_reuseFailAlloc_4172_, 2, v_ngen_4151_);
lean_ctor_set(v_reuseFailAlloc_4172_, 3, v_auxDeclNGen_4152_);
lean_ctor_set(v_reuseFailAlloc_4172_, 4, v___x_4167_);
lean_ctor_set(v_reuseFailAlloc_4172_, 5, v_cache_4153_);
lean_ctor_set(v_reuseFailAlloc_4172_, 6, v_messages_4154_);
lean_ctor_set(v_reuseFailAlloc_4172_, 7, v_infoState_4155_);
lean_ctor_set(v_reuseFailAlloc_4172_, 8, v_snapshotTasks_4156_);
v___x_4169_ = v_reuseFailAlloc_4172_;
goto v_reusejp_4168_;
}
v_reusejp_4168_:
{
lean_object* v___x_4170_; lean_object* v___x_4171_; 
v___x_4170_ = lean_st_ref_set(v___y_4107_, v___x_4169_);
v___x_4171_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg(v_fst_4109_);
return v___x_4171_;
}
}
}
}
}
else
{
goto v___jp_4140_;
}
}
else
{
goto v___jp_4140_;
}
}
v___jp_4176_:
{
double v___x_4178_; double v___x_4179_; double v___x_4180_; uint8_t v___x_4181_; 
v___x_4178_ = lean_unbox_float(v_snd_4126_);
v___x_4179_ = lean_unbox_float(v_fst_4125_);
v___x_4180_ = lean_float_sub(v___x_4178_, v___x_4179_);
v___x_4181_ = lean_float_decLt(v___y_4177_, v___x_4180_);
v___y_4146_ = v___x_4181_;
goto v___jp_4145_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1___boxed(lean_object* v_cls_4192_, lean_object* v_collapsed_4193_, lean_object* v_tag_4194_, lean_object* v_opts_4195_, lean_object* v_clsEnabled_4196_, lean_object* v_oldTraces_4197_, lean_object* v_msg_4198_, lean_object* v_resStartStop_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_){
_start:
{
uint8_t v_collapsed_boxed_4205_; uint8_t v_clsEnabled_boxed_4206_; lean_object* v_res_4207_; 
v_collapsed_boxed_4205_ = lean_unbox(v_collapsed_4193_);
v_clsEnabled_boxed_4206_ = lean_unbox(v_clsEnabled_4196_);
v_res_4207_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1(v_cls_4192_, v_collapsed_boxed_4205_, v_tag_4194_, v_opts_4195_, v_clsEnabled_boxed_4206_, v_oldTraces_4197_, v_msg_4198_, v_resStartStop_4199_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_);
lean_dec(v___y_4203_);
lean_dec_ref(v___y_4202_);
lean_dec(v___y_4201_);
lean_dec_ref(v___y_4200_);
lean_dec_ref(v_opts_4195_);
return v_res_4207_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1(void){
_start:
{
lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; 
v___x_4212_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0));
v___x_4213_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__3));
v___x_4214_ = l_Lean_Name_append(v___x_4213_, v___x_4212_);
return v___x_4214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry(lean_object* v_e_4215_, lean_object* v_a_4216_, lean_object* v_a_4217_, lean_object* v_a_4218_, lean_object* v_a_4219_){
_start:
{
lean_object* v_options_4221_; uint8_t v_hasTrace_4222_; 
v_options_4221_ = lean_ctor_get(v_a_4218_, 2);
v_hasTrace_4222_ = lean_ctor_get_uint8(v_options_4221_, sizeof(void*)*1);
if (v_hasTrace_4222_ == 0)
{
lean_object* v___x_4223_; 
v___x_4223_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_4219_);
if (lean_obj_tag(v___x_4223_) == 0)
{
lean_object* v_a_4224_; lean_object* v___x_4225_; 
v_a_4224_ = lean_ctor_get(v___x_4223_, 0);
lean_inc(v_a_4224_);
lean_dec_ref_known(v___x_4223_, 1);
v___x_4225_ = l_Lean_Meta_Sym_unfoldReducible(v_e_4215_, v_a_4216_, v_a_4217_, v_a_4218_, v_a_4219_);
if (lean_obj_tag(v___x_4225_) == 0)
{
lean_object* v_a_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___f_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; 
v_a_4226_ = lean_ctor_get(v___x_4225_, 0);
lean_inc(v_a_4226_);
lean_dec_ref_known(v___x_4225_, 1);
v___x_4227_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_4228_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_4221_, v___x_4227_);
v___x_4229_ = lean_unsigned_to_nat(2u);
v___x_4230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4230_, 0, v___x_4228_);
lean_ctor_set(v___x_4230_, 1, v___x_4229_);
v___x_4231_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(v_a_4224_);
v___f_4232_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4232_, 0, v_a_4226_);
lean_closure_set(v___f_4232_, 1, v___x_4231_);
lean_closure_set(v___f_4232_, 2, v___x_4230_);
v___x_4233_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0___boxed), 9, 2);
lean_closure_set(v___x_4233_, 0, lean_box(0));
lean_closure_set(v___x_4233_, 1, v___f_4232_);
v___x_4234_ = l_Lean_Meta_Sym_SymM_run___redArg(v___x_4233_, v_a_4216_, v_a_4217_, v_a_4218_, v_a_4219_);
return v___x_4234_;
}
else
{
lean_object* v_a_4235_; lean_object* v___x_4237_; uint8_t v_isShared_4238_; uint8_t v_isSharedCheck_4242_; 
lean_dec(v_a_4224_);
v_a_4235_ = lean_ctor_get(v___x_4225_, 0);
v_isSharedCheck_4242_ = !lean_is_exclusive(v___x_4225_);
if (v_isSharedCheck_4242_ == 0)
{
v___x_4237_ = v___x_4225_;
v_isShared_4238_ = v_isSharedCheck_4242_;
goto v_resetjp_4236_;
}
else
{
lean_inc(v_a_4235_);
lean_dec(v___x_4225_);
v___x_4237_ = lean_box(0);
v_isShared_4238_ = v_isSharedCheck_4242_;
goto v_resetjp_4236_;
}
v_resetjp_4236_:
{
lean_object* v___x_4240_; 
if (v_isShared_4238_ == 0)
{
v___x_4240_ = v___x_4237_;
goto v_reusejp_4239_;
}
else
{
lean_object* v_reuseFailAlloc_4241_; 
v_reuseFailAlloc_4241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4241_, 0, v_a_4235_);
v___x_4240_ = v_reuseFailAlloc_4241_;
goto v_reusejp_4239_;
}
v_reusejp_4239_:
{
return v___x_4240_;
}
}
}
}
else
{
lean_object* v_a_4243_; lean_object* v___x_4245_; uint8_t v_isShared_4246_; uint8_t v_isSharedCheck_4250_; 
lean_dec_ref(v_e_4215_);
v_a_4243_ = lean_ctor_get(v___x_4223_, 0);
v_isSharedCheck_4250_ = !lean_is_exclusive(v___x_4223_);
if (v_isSharedCheck_4250_ == 0)
{
v___x_4245_ = v___x_4223_;
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
else
{
lean_inc(v_a_4243_);
lean_dec(v___x_4223_);
v___x_4245_ = lean_box(0);
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
v_resetjp_4244_:
{
lean_object* v___x_4248_; 
if (v_isShared_4246_ == 0)
{
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
return v___x_4248_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_4251_; lean_object* v___f_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; uint8_t v___x_4256_; lean_object* v___y_4258_; lean_object* v___y_4259_; lean_object* v_a_4260_; lean_object* v___y_4273_; lean_object* v___y_4274_; lean_object* v_a_4275_; lean_object* v___y_4278_; lean_object* v___y_4279_; lean_object* v_a_4280_; lean_object* v___y_4290_; lean_object* v___y_4291_; lean_object* v_a_4292_; 
v_inheritedTraceOptions_4251_ = lean_ctor_get(v_a_4218_, 13);
lean_inc_ref(v_e_4215_);
v___f_4252_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___boxed), 7, 1);
lean_closure_set(v___f_4252_, 0, v_e_4215_);
v___x_4253_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0));
v___x_4254_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__1));
v___x_4255_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1);
v___x_4256_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4251_, v_options_4221_, v___x_4255_);
if (v___x_4256_ == 0)
{
lean_object* v___x_4347_; uint8_t v___x_4348_; 
v___x_4347_ = l_Lean_trace_profiler;
v___x_4348_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_4221_, v___x_4347_);
if (v___x_4348_ == 0)
{
lean_object* v___x_4349_; 
lean_dec_ref(v___f_4252_);
v___x_4349_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_4219_);
if (lean_obj_tag(v___x_4349_) == 0)
{
lean_object* v_a_4350_; lean_object* v___x_4351_; 
v_a_4350_ = lean_ctor_get(v___x_4349_, 0);
lean_inc(v_a_4350_);
lean_dec_ref_known(v___x_4349_, 1);
v___x_4351_ = l_Lean_Meta_Sym_unfoldReducible(v_e_4215_, v_a_4216_, v_a_4217_, v_a_4218_, v_a_4219_);
if (lean_obj_tag(v___x_4351_) == 0)
{
lean_object* v_a_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___f_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; 
v_a_4352_ = lean_ctor_get(v___x_4351_, 0);
lean_inc(v_a_4352_);
lean_dec_ref_known(v___x_4351_, 1);
v___x_4353_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_4354_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_4221_, v___x_4353_);
v___x_4355_ = lean_unsigned_to_nat(2u);
v___x_4356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4356_, 0, v___x_4354_);
lean_ctor_set(v___x_4356_, 1, v___x_4355_);
v___x_4357_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(v_a_4350_);
v___f_4358_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4358_, 0, v_a_4352_);
lean_closure_set(v___f_4358_, 1, v___x_4357_);
lean_closure_set(v___f_4358_, 2, v___x_4356_);
v___x_4359_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0___boxed), 9, 2);
lean_closure_set(v___x_4359_, 0, lean_box(0));
lean_closure_set(v___x_4359_, 1, v___f_4358_);
v___x_4360_ = l_Lean_Meta_Sym_SymM_run___redArg(v___x_4359_, v_a_4216_, v_a_4217_, v_a_4218_, v_a_4219_);
return v___x_4360_;
}
else
{
lean_object* v_a_4361_; lean_object* v___x_4363_; uint8_t v_isShared_4364_; uint8_t v_isSharedCheck_4368_; 
lean_dec(v_a_4350_);
v_a_4361_ = lean_ctor_get(v___x_4351_, 0);
v_isSharedCheck_4368_ = !lean_is_exclusive(v___x_4351_);
if (v_isSharedCheck_4368_ == 0)
{
v___x_4363_ = v___x_4351_;
v_isShared_4364_ = v_isSharedCheck_4368_;
goto v_resetjp_4362_;
}
else
{
lean_inc(v_a_4361_);
lean_dec(v___x_4351_);
v___x_4363_ = lean_box(0);
v_isShared_4364_ = v_isSharedCheck_4368_;
goto v_resetjp_4362_;
}
v_resetjp_4362_:
{
lean_object* v___x_4366_; 
if (v_isShared_4364_ == 0)
{
v___x_4366_ = v___x_4363_;
goto v_reusejp_4365_;
}
else
{
lean_object* v_reuseFailAlloc_4367_; 
v_reuseFailAlloc_4367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4367_, 0, v_a_4361_);
v___x_4366_ = v_reuseFailAlloc_4367_;
goto v_reusejp_4365_;
}
v_reusejp_4365_:
{
return v___x_4366_;
}
}
}
}
else
{
lean_object* v_a_4369_; lean_object* v___x_4371_; uint8_t v_isShared_4372_; uint8_t v_isSharedCheck_4376_; 
lean_dec_ref(v_e_4215_);
v_a_4369_ = lean_ctor_get(v___x_4349_, 0);
v_isSharedCheck_4376_ = !lean_is_exclusive(v___x_4349_);
if (v_isSharedCheck_4376_ == 0)
{
v___x_4371_ = v___x_4349_;
v_isShared_4372_ = v_isSharedCheck_4376_;
goto v_resetjp_4370_;
}
else
{
lean_inc(v_a_4369_);
lean_dec(v___x_4349_);
v___x_4371_ = lean_box(0);
v_isShared_4372_ = v_isSharedCheck_4376_;
goto v_resetjp_4370_;
}
v_resetjp_4370_:
{
lean_object* v___x_4374_; 
if (v_isShared_4372_ == 0)
{
v___x_4374_ = v___x_4371_;
goto v_reusejp_4373_;
}
else
{
lean_object* v_reuseFailAlloc_4375_; 
v_reuseFailAlloc_4375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4375_, 0, v_a_4369_);
v___x_4374_ = v_reuseFailAlloc_4375_;
goto v_reusejp_4373_;
}
v_reusejp_4373_:
{
return v___x_4374_;
}
}
}
}
else
{
goto v___jp_4294_;
}
}
else
{
goto v___jp_4294_;
}
v___jp_4257_:
{
lean_object* v___x_4261_; double v___x_4262_; double v___x_4263_; double v___x_4264_; double v___x_4265_; double v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; 
v___x_4261_ = lean_io_mono_nanos_now();
v___x_4262_ = lean_float_of_nat(v___y_4258_);
v___x_4263_ = lean_float_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9);
v___x_4264_ = lean_float_div(v___x_4262_, v___x_4263_);
v___x_4265_ = lean_float_of_nat(v___x_4261_);
v___x_4266_ = lean_float_div(v___x_4265_, v___x_4263_);
v___x_4267_ = lean_box_float(v___x_4264_);
v___x_4268_ = lean_box_float(v___x_4266_);
v___x_4269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4269_, 0, v___x_4267_);
lean_ctor_set(v___x_4269_, 1, v___x_4268_);
v___x_4270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4270_, 0, v_a_4260_);
lean_ctor_set(v___x_4270_, 1, v___x_4269_);
v___x_4271_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1(v___x_4253_, v_hasTrace_4222_, v___x_4254_, v_options_4221_, v___x_4256_, v___y_4259_, v___f_4252_, v___x_4270_, v_a_4216_, v_a_4217_, v_a_4218_, v_a_4219_);
return v___x_4271_;
}
v___jp_4272_:
{
lean_object* v___x_4276_; 
v___x_4276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4276_, 0, v_a_4275_);
v___y_4258_ = v___y_4273_;
v___y_4259_ = v___y_4274_;
v_a_4260_ = v___x_4276_;
goto v___jp_4257_;
}
v___jp_4277_:
{
lean_object* v___x_4281_; double v___x_4282_; double v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; 
v___x_4281_ = lean_io_get_num_heartbeats();
v___x_4282_ = lean_float_of_nat(v___y_4278_);
v___x_4283_ = lean_float_of_nat(v___x_4281_);
v___x_4284_ = lean_box_float(v___x_4282_);
v___x_4285_ = lean_box_float(v___x_4283_);
v___x_4286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4286_, 0, v___x_4284_);
lean_ctor_set(v___x_4286_, 1, v___x_4285_);
v___x_4287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4287_, 0, v_a_4280_);
lean_ctor_set(v___x_4287_, 1, v___x_4286_);
v___x_4288_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1(v___x_4253_, v_hasTrace_4222_, v___x_4254_, v_options_4221_, v___x_4256_, v___y_4279_, v___f_4252_, v___x_4287_, v_a_4216_, v_a_4217_, v_a_4218_, v_a_4219_);
return v___x_4288_;
}
v___jp_4289_:
{
lean_object* v___x_4293_; 
v___x_4293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4293_, 0, v_a_4292_);
v___y_4278_ = v___y_4290_;
v___y_4279_ = v___y_4291_;
v_a_4280_ = v___x_4293_;
goto v___jp_4277_;
}
v___jp_4294_:
{
lean_object* v___x_4295_; lean_object* v_a_4296_; lean_object* v___x_4297_; uint8_t v___x_4298_; 
v___x_4295_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg(v_a_4219_);
v_a_4296_ = lean_ctor_get(v___x_4295_, 0);
lean_inc(v_a_4296_);
lean_dec_ref(v___x_4295_);
v___x_4297_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4298_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_4221_, v___x_4297_);
if (v___x_4298_ == 0)
{
lean_object* v___x_4299_; lean_object* v___x_4300_; 
v___x_4299_ = lean_io_mono_nanos_now();
v___x_4300_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_4219_);
if (lean_obj_tag(v___x_4300_) == 0)
{
lean_object* v_a_4301_; lean_object* v___x_4302_; 
v_a_4301_ = lean_ctor_get(v___x_4300_, 0);
lean_inc(v_a_4301_);
lean_dec_ref_known(v___x_4300_, 1);
v___x_4302_ = l_Lean_Meta_Sym_unfoldReducible(v_e_4215_, v_a_4216_, v_a_4217_, v_a_4218_, v_a_4219_);
if (lean_obj_tag(v___x_4302_) == 0)
{
lean_object* v_a_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___f_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; 
v_a_4303_ = lean_ctor_get(v___x_4302_, 0);
lean_inc(v_a_4303_);
lean_dec_ref_known(v___x_4302_, 1);
v___x_4304_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_4305_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_4221_, v___x_4304_);
v___x_4306_ = lean_unsigned_to_nat(2u);
v___x_4307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4307_, 0, v___x_4305_);
lean_ctor_set(v___x_4307_, 1, v___x_4306_);
v___x_4308_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(v_a_4301_);
v___f_4309_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4309_, 0, v_a_4303_);
lean_closure_set(v___f_4309_, 1, v___x_4308_);
lean_closure_set(v___f_4309_, 2, v___x_4307_);
v___x_4310_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0___boxed), 9, 2);
lean_closure_set(v___x_4310_, 0, lean_box(0));
lean_closure_set(v___x_4310_, 1, v___f_4309_);
v___x_4311_ = l_Lean_Meta_Sym_SymM_run___redArg(v___x_4310_, v_a_4216_, v_a_4217_, v_a_4218_, v_a_4219_);
if (lean_obj_tag(v___x_4311_) == 0)
{
lean_object* v_a_4312_; lean_object* v___x_4314_; uint8_t v_isShared_4315_; uint8_t v_isSharedCheck_4319_; 
v_a_4312_ = lean_ctor_get(v___x_4311_, 0);
v_isSharedCheck_4319_ = !lean_is_exclusive(v___x_4311_);
if (v_isSharedCheck_4319_ == 0)
{
v___x_4314_ = v___x_4311_;
v_isShared_4315_ = v_isSharedCheck_4319_;
goto v_resetjp_4313_;
}
else
{
lean_inc(v_a_4312_);
lean_dec(v___x_4311_);
v___x_4314_ = lean_box(0);
v_isShared_4315_ = v_isSharedCheck_4319_;
goto v_resetjp_4313_;
}
v_resetjp_4313_:
{
lean_object* v___x_4317_; 
if (v_isShared_4315_ == 0)
{
lean_ctor_set_tag(v___x_4314_, 1);
v___x_4317_ = v___x_4314_;
goto v_reusejp_4316_;
}
else
{
lean_object* v_reuseFailAlloc_4318_; 
v_reuseFailAlloc_4318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4318_, 0, v_a_4312_);
v___x_4317_ = v_reuseFailAlloc_4318_;
goto v_reusejp_4316_;
}
v_reusejp_4316_:
{
v___y_4258_ = v___x_4299_;
v___y_4259_ = v_a_4296_;
v_a_4260_ = v___x_4317_;
goto v___jp_4257_;
}
}
}
else
{
lean_object* v_a_4320_; 
v_a_4320_ = lean_ctor_get(v___x_4311_, 0);
lean_inc(v_a_4320_);
lean_dec_ref_known(v___x_4311_, 1);
v___y_4273_ = v___x_4299_;
v___y_4274_ = v_a_4296_;
v_a_4275_ = v_a_4320_;
goto v___jp_4272_;
}
}
else
{
lean_object* v_a_4321_; 
lean_dec(v_a_4301_);
v_a_4321_ = lean_ctor_get(v___x_4302_, 0);
lean_inc(v_a_4321_);
lean_dec_ref_known(v___x_4302_, 1);
v___y_4273_ = v___x_4299_;
v___y_4274_ = v_a_4296_;
v_a_4275_ = v_a_4321_;
goto v___jp_4272_;
}
}
else
{
lean_object* v_a_4322_; 
lean_dec_ref(v_e_4215_);
v_a_4322_ = lean_ctor_get(v___x_4300_, 0);
lean_inc(v_a_4322_);
lean_dec_ref_known(v___x_4300_, 1);
v___y_4273_ = v___x_4299_;
v___y_4274_ = v_a_4296_;
v_a_4275_ = v_a_4322_;
goto v___jp_4272_;
}
}
else
{
lean_object* v___x_4323_; lean_object* v___x_4324_; 
v___x_4323_ = lean_io_get_num_heartbeats();
v___x_4324_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_4219_);
if (lean_obj_tag(v___x_4324_) == 0)
{
lean_object* v_a_4325_; lean_object* v___x_4326_; 
v_a_4325_ = lean_ctor_get(v___x_4324_, 0);
lean_inc(v_a_4325_);
lean_dec_ref_known(v___x_4324_, 1);
v___x_4326_ = l_Lean_Meta_Sym_unfoldReducible(v_e_4215_, v_a_4216_, v_a_4217_, v_a_4218_, v_a_4219_);
if (lean_obj_tag(v___x_4326_) == 0)
{
lean_object* v_a_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___f_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; 
v_a_4327_ = lean_ctor_get(v___x_4326_, 0);
lean_inc(v_a_4327_);
lean_dec_ref_known(v___x_4326_, 1);
v___x_4328_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_4329_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_4221_, v___x_4328_);
v___x_4330_ = lean_unsigned_to_nat(2u);
v___x_4331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4331_, 0, v___x_4329_);
lean_ctor_set(v___x_4331_, 1, v___x_4330_);
v___x_4332_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(v_a_4325_);
v___f_4333_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4333_, 0, v_a_4327_);
lean_closure_set(v___f_4333_, 1, v___x_4332_);
lean_closure_set(v___f_4333_, 2, v___x_4331_);
v___x_4334_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0___boxed), 9, 2);
lean_closure_set(v___x_4334_, 0, lean_box(0));
lean_closure_set(v___x_4334_, 1, v___f_4333_);
v___x_4335_ = l_Lean_Meta_Sym_SymM_run___redArg(v___x_4334_, v_a_4216_, v_a_4217_, v_a_4218_, v_a_4219_);
if (lean_obj_tag(v___x_4335_) == 0)
{
lean_object* v_a_4336_; lean_object* v___x_4338_; uint8_t v_isShared_4339_; uint8_t v_isSharedCheck_4343_; 
v_a_4336_ = lean_ctor_get(v___x_4335_, 0);
v_isSharedCheck_4343_ = !lean_is_exclusive(v___x_4335_);
if (v_isSharedCheck_4343_ == 0)
{
v___x_4338_ = v___x_4335_;
v_isShared_4339_ = v_isSharedCheck_4343_;
goto v_resetjp_4337_;
}
else
{
lean_inc(v_a_4336_);
lean_dec(v___x_4335_);
v___x_4338_ = lean_box(0);
v_isShared_4339_ = v_isSharedCheck_4343_;
goto v_resetjp_4337_;
}
v_resetjp_4337_:
{
lean_object* v___x_4341_; 
if (v_isShared_4339_ == 0)
{
lean_ctor_set_tag(v___x_4338_, 1);
v___x_4341_ = v___x_4338_;
goto v_reusejp_4340_;
}
else
{
lean_object* v_reuseFailAlloc_4342_; 
v_reuseFailAlloc_4342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4342_, 0, v_a_4336_);
v___x_4341_ = v_reuseFailAlloc_4342_;
goto v_reusejp_4340_;
}
v_reusejp_4340_:
{
v___y_4278_ = v___x_4323_;
v___y_4279_ = v_a_4296_;
v_a_4280_ = v___x_4341_;
goto v___jp_4277_;
}
}
}
else
{
lean_object* v_a_4344_; 
v_a_4344_ = lean_ctor_get(v___x_4335_, 0);
lean_inc(v_a_4344_);
lean_dec_ref_known(v___x_4335_, 1);
v___y_4290_ = v___x_4323_;
v___y_4291_ = v_a_4296_;
v_a_4292_ = v_a_4344_;
goto v___jp_4289_;
}
}
else
{
lean_object* v_a_4345_; 
lean_dec(v_a_4325_);
v_a_4345_ = lean_ctor_get(v___x_4326_, 0);
lean_inc(v_a_4345_);
lean_dec_ref_known(v___x_4326_, 1);
v___y_4290_ = v___x_4323_;
v___y_4291_ = v_a_4296_;
v_a_4292_ = v_a_4345_;
goto v___jp_4289_;
}
}
else
{
lean_object* v_a_4346_; 
lean_dec_ref(v_e_4215_);
v_a_4346_ = lean_ctor_get(v___x_4324_, 0);
lean_inc(v_a_4346_);
lean_dec_ref_known(v___x_4324_, 1);
v___y_4290_ = v___x_4323_;
v___y_4291_ = v_a_4296_;
v_a_4292_ = v_a_4346_;
goto v___jp_4289_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___boxed(lean_object* v_e_4377_, lean_object* v_a_4378_, lean_object* v_a_4379_, lean_object* v_a_4380_, lean_object* v_a_4381_, lean_object* v_a_4382_){
_start:
{
lean_object* v_res_4383_; 
v_res_4383_ = l_Lean_Meta_Tactic_Cbv_cbvEntry(v_e_4377_, v_a_4378_, v_a_4379_, v_a_4380_, v_a_4381_);
lean_dec(v_a_4381_);
lean_dec_ref(v_a_4380_);
lean_dec(v_a_4379_);
lean_dec_ref(v_a_4378_);
return v_res_4383_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2(lean_object* v_00_u03b1_4384_, lean_object* v_x_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_){
_start:
{
lean_object* v___x_4391_; 
v___x_4391_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg(v_x_4385_);
return v___x_4391_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___boxed(lean_object* v_00_u03b1_4392_, lean_object* v_x_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_){
_start:
{
lean_object* v_res_4399_; 
v_res_4399_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2(v_00_u03b1_4392_, v_x_4393_, v___y_4394_, v___y_4395_, v___y_4396_, v___y_4397_);
lean_dec(v___y_4397_);
lean_dec_ref(v___y_4396_);
lean_dec(v___y_4395_);
lean_dec_ref(v___y_4394_);
return v_res_4399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1___redArg(lean_object* v___y_4400_){
_start:
{
lean_object* v___x_4402_; lean_object* v_traceState_4403_; lean_object* v_traces_4404_; lean_object* v___x_4405_; lean_object* v_traceState_4406_; lean_object* v_env_4407_; lean_object* v_nextMacroScope_4408_; lean_object* v_ngen_4409_; lean_object* v_auxDeclNGen_4410_; lean_object* v_cache_4411_; lean_object* v_messages_4412_; lean_object* v_infoState_4413_; lean_object* v_snapshotTasks_4414_; lean_object* v___x_4416_; uint8_t v_isShared_4417_; uint8_t v_isSharedCheck_4435_; 
v___x_4402_ = lean_st_ref_get(v___y_4400_);
v_traceState_4403_ = lean_ctor_get(v___x_4402_, 4);
lean_inc_ref(v_traceState_4403_);
lean_dec(v___x_4402_);
v_traces_4404_ = lean_ctor_get(v_traceState_4403_, 0);
lean_inc_ref(v_traces_4404_);
lean_dec_ref(v_traceState_4403_);
v___x_4405_ = lean_st_ref_take(v___y_4400_);
v_traceState_4406_ = lean_ctor_get(v___x_4405_, 4);
v_env_4407_ = lean_ctor_get(v___x_4405_, 0);
v_nextMacroScope_4408_ = lean_ctor_get(v___x_4405_, 1);
v_ngen_4409_ = lean_ctor_get(v___x_4405_, 2);
v_auxDeclNGen_4410_ = lean_ctor_get(v___x_4405_, 3);
v_cache_4411_ = lean_ctor_get(v___x_4405_, 5);
v_messages_4412_ = lean_ctor_get(v___x_4405_, 6);
v_infoState_4413_ = lean_ctor_get(v___x_4405_, 7);
v_snapshotTasks_4414_ = lean_ctor_get(v___x_4405_, 8);
v_isSharedCheck_4435_ = !lean_is_exclusive(v___x_4405_);
if (v_isSharedCheck_4435_ == 0)
{
v___x_4416_ = v___x_4405_;
v_isShared_4417_ = v_isSharedCheck_4435_;
goto v_resetjp_4415_;
}
else
{
lean_inc(v_snapshotTasks_4414_);
lean_inc(v_infoState_4413_);
lean_inc(v_messages_4412_);
lean_inc(v_cache_4411_);
lean_inc(v_traceState_4406_);
lean_inc(v_auxDeclNGen_4410_);
lean_inc(v_ngen_4409_);
lean_inc(v_nextMacroScope_4408_);
lean_inc(v_env_4407_);
lean_dec(v___x_4405_);
v___x_4416_ = lean_box(0);
v_isShared_4417_ = v_isSharedCheck_4435_;
goto v_resetjp_4415_;
}
v_resetjp_4415_:
{
uint64_t v_tid_4418_; lean_object* v___x_4420_; uint8_t v_isShared_4421_; uint8_t v_isSharedCheck_4433_; 
v_tid_4418_ = lean_ctor_get_uint64(v_traceState_4406_, sizeof(void*)*1);
v_isSharedCheck_4433_ = !lean_is_exclusive(v_traceState_4406_);
if (v_isSharedCheck_4433_ == 0)
{
lean_object* v_unused_4434_; 
v_unused_4434_ = lean_ctor_get(v_traceState_4406_, 0);
lean_dec(v_unused_4434_);
v___x_4420_ = v_traceState_4406_;
v_isShared_4421_ = v_isSharedCheck_4433_;
goto v_resetjp_4419_;
}
else
{
lean_dec(v_traceState_4406_);
v___x_4420_ = lean_box(0);
v_isShared_4421_ = v_isSharedCheck_4433_;
goto v_resetjp_4419_;
}
v_resetjp_4419_:
{
lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4426_; 
v___x_4422_ = lean_unsigned_to_nat(32u);
v___x_4423_ = lean_mk_empty_array_with_capacity(v___x_4422_);
lean_dec_ref(v___x_4423_);
v___x_4424_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1);
if (v_isShared_4421_ == 0)
{
lean_ctor_set(v___x_4420_, 0, v___x_4424_);
v___x_4426_ = v___x_4420_;
goto v_reusejp_4425_;
}
else
{
lean_object* v_reuseFailAlloc_4432_; 
v_reuseFailAlloc_4432_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4432_, 0, v___x_4424_);
lean_ctor_set_uint64(v_reuseFailAlloc_4432_, sizeof(void*)*1, v_tid_4418_);
v___x_4426_ = v_reuseFailAlloc_4432_;
goto v_reusejp_4425_;
}
v_reusejp_4425_:
{
lean_object* v___x_4428_; 
if (v_isShared_4417_ == 0)
{
lean_ctor_set(v___x_4416_, 4, v___x_4426_);
v___x_4428_ = v___x_4416_;
goto v_reusejp_4427_;
}
else
{
lean_object* v_reuseFailAlloc_4431_; 
v_reuseFailAlloc_4431_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4431_, 0, v_env_4407_);
lean_ctor_set(v_reuseFailAlloc_4431_, 1, v_nextMacroScope_4408_);
lean_ctor_set(v_reuseFailAlloc_4431_, 2, v_ngen_4409_);
lean_ctor_set(v_reuseFailAlloc_4431_, 3, v_auxDeclNGen_4410_);
lean_ctor_set(v_reuseFailAlloc_4431_, 4, v___x_4426_);
lean_ctor_set(v_reuseFailAlloc_4431_, 5, v_cache_4411_);
lean_ctor_set(v_reuseFailAlloc_4431_, 6, v_messages_4412_);
lean_ctor_set(v_reuseFailAlloc_4431_, 7, v_infoState_4413_);
lean_ctor_set(v_reuseFailAlloc_4431_, 8, v_snapshotTasks_4414_);
v___x_4428_ = v_reuseFailAlloc_4431_;
goto v_reusejp_4427_;
}
v_reusejp_4427_:
{
lean_object* v___x_4429_; lean_object* v___x_4430_; 
v___x_4429_ = lean_st_ref_set(v___y_4400_, v___x_4428_);
v___x_4430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4430_, 0, v_traces_4404_);
return v___x_4430_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1___redArg___boxed(lean_object* v___y_4436_, lean_object* v___y_4437_){
_start:
{
lean_object* v_res_4438_; 
v_res_4438_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1___redArg(v___y_4436_);
lean_dec(v___y_4436_);
return v_res_4438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1(lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_){
_start:
{
lean_object* v___x_4446_; 
v___x_4446_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1___redArg(v___y_4444_);
return v___x_4446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1___boxed(lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_){
_start:
{
lean_object* v_res_4454_; 
v_res_4454_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1(v___y_4447_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_, v___y_4452_);
lean_dec(v___y_4452_);
lean_dec_ref(v___y_4451_);
lean_dec(v___y_4450_);
lean_dec_ref(v___y_4449_);
lean_dec(v___y_4448_);
lean_dec_ref(v___y_4447_);
return v_res_4454_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg___lam__0(lean_object* v_x_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_){
_start:
{
lean_object* v___x_4463_; 
lean_inc(v___y_4457_);
lean_inc_ref(v___y_4456_);
v___x_4463_ = lean_apply_7(v_x_4455_, v___y_4456_, v___y_4457_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_, lean_box(0));
return v___x_4463_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg___lam__0___boxed(lean_object* v_x_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_){
_start:
{
lean_object* v_res_4472_; 
v_res_4472_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg___lam__0(v_x_4464_, v___y_4465_, v___y_4466_, v___y_4467_, v___y_4468_, v___y_4469_, v___y_4470_);
lean_dec(v___y_4466_);
lean_dec_ref(v___y_4465_);
return v_res_4472_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg(lean_object* v_mvarId_4473_, lean_object* v_x_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_){
_start:
{
lean_object* v___f_4482_; lean_object* v___x_4483_; 
lean_inc(v___y_4476_);
lean_inc_ref(v___y_4475_);
v___f_4482_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4482_, 0, v_x_4474_);
lean_closure_set(v___f_4482_, 1, v___y_4475_);
lean_closure_set(v___f_4482_, 2, v___y_4476_);
v___x_4483_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_4473_, v___f_4482_, v___y_4477_, v___y_4478_, v___y_4479_, v___y_4480_);
if (lean_obj_tag(v___x_4483_) == 0)
{
return v___x_4483_;
}
else
{
lean_object* v_a_4484_; lean_object* v___x_4486_; uint8_t v_isShared_4487_; uint8_t v_isSharedCheck_4491_; 
v_a_4484_ = lean_ctor_get(v___x_4483_, 0);
v_isSharedCheck_4491_ = !lean_is_exclusive(v___x_4483_);
if (v_isSharedCheck_4491_ == 0)
{
v___x_4486_ = v___x_4483_;
v_isShared_4487_ = v_isSharedCheck_4491_;
goto v_resetjp_4485_;
}
else
{
lean_inc(v_a_4484_);
lean_dec(v___x_4483_);
v___x_4486_ = lean_box(0);
v_isShared_4487_ = v_isSharedCheck_4491_;
goto v_resetjp_4485_;
}
v_resetjp_4485_:
{
lean_object* v___x_4489_; 
if (v_isShared_4487_ == 0)
{
v___x_4489_ = v___x_4486_;
goto v_reusejp_4488_;
}
else
{
lean_object* v_reuseFailAlloc_4490_; 
v_reuseFailAlloc_4490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4490_, 0, v_a_4484_);
v___x_4489_ = v_reuseFailAlloc_4490_;
goto v_reusejp_4488_;
}
v_reusejp_4488_:
{
return v___x_4489_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg___boxed(lean_object* v_mvarId_4492_, lean_object* v_x_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_){
_start:
{
lean_object* v_res_4501_; 
v_res_4501_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg(v_mvarId_4492_, v_x_4493_, v___y_4494_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_);
lean_dec(v___y_4499_);
lean_dec_ref(v___y_4498_);
lean_dec(v___y_4497_);
lean_dec_ref(v___y_4496_);
lean_dec(v___y_4495_);
lean_dec_ref(v___y_4494_);
return v_res_4501_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4(lean_object* v_00_u03b1_4502_, lean_object* v_mvarId_4503_, lean_object* v_x_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_){
_start:
{
lean_object* v___x_4512_; 
v___x_4512_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg(v_mvarId_4503_, v_x_4504_, v___y_4505_, v___y_4506_, v___y_4507_, v___y_4508_, v___y_4509_, v___y_4510_);
return v___x_4512_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___boxed(lean_object* v_00_u03b1_4513_, lean_object* v_mvarId_4514_, lean_object* v_x_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_){
_start:
{
lean_object* v_res_4523_; 
v_res_4523_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4(v_00_u03b1_4513_, v_mvarId_4514_, v_x_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_, v___y_4520_, v___y_4521_);
lean_dec(v___y_4521_);
lean_dec_ref(v___y_4520_);
lean_dec(v___y_4519_);
lean_dec_ref(v___y_4518_);
lean_dec(v___y_4517_);
lean_dec_ref(v___y_4516_);
return v_res_4523_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4525_; lean_object* v___x_4526_; 
v___x_4525_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__0));
v___x_4526_ = l_Lean_stringToMessageData(v___x_4525_);
return v___x_4526_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4528_; lean_object* v___x_4529_; 
v___x_4528_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__2));
v___x_4529_ = l_Lean_stringToMessageData(v___x_4528_);
return v___x_4529_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4531_; lean_object* v___x_4532_; 
v___x_4531_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__4));
v___x_4532_ = l_Lean_stringToMessageData(v___x_4531_);
return v___x_4532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0(lean_object* v_a_4533_, lean_object* v_x_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_){
_start:
{
if (lean_obj_tag(v_x_4534_) == 0)
{
lean_object* v_a_4542_; lean_object* v___x_4544_; uint8_t v_isShared_4545_; uint8_t v_isSharedCheck_4552_; 
lean_dec_ref(v_a_4533_);
v_a_4542_ = lean_ctor_get(v_x_4534_, 0);
v_isSharedCheck_4552_ = !lean_is_exclusive(v_x_4534_);
if (v_isSharedCheck_4552_ == 0)
{
v___x_4544_ = v_x_4534_;
v_isShared_4545_ = v_isSharedCheck_4552_;
goto v_resetjp_4543_;
}
else
{
lean_inc(v_a_4542_);
lean_dec(v_x_4534_);
v___x_4544_ = lean_box(0);
v_isShared_4545_ = v_isSharedCheck_4552_;
goto v_resetjp_4543_;
}
v_resetjp_4543_:
{
lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4550_; 
v___x_4546_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__1);
v___x_4547_ = l_Lean_Exception_toMessageData(v_a_4542_);
v___x_4548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4548_, 0, v___x_4546_);
lean_ctor_set(v___x_4548_, 1, v___x_4547_);
if (v_isShared_4545_ == 0)
{
lean_ctor_set(v___x_4544_, 0, v___x_4548_);
v___x_4550_ = v___x_4544_;
goto v_reusejp_4549_;
}
else
{
lean_object* v_reuseFailAlloc_4551_; 
v_reuseFailAlloc_4551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4551_, 0, v___x_4548_);
v___x_4550_ = v_reuseFailAlloc_4551_;
goto v_reusejp_4549_;
}
v_reusejp_4549_:
{
return v___x_4550_;
}
}
}
else
{
lean_object* v_a_4553_; lean_object* v___x_4555_; uint8_t v_isShared_4556_; uint8_t v_isSharedCheck_4572_; 
v_a_4553_ = lean_ctor_get(v_x_4534_, 0);
v_isSharedCheck_4572_ = !lean_is_exclusive(v_x_4534_);
if (v_isSharedCheck_4572_ == 0)
{
v___x_4555_ = v_x_4534_;
v_isShared_4556_ = v_isSharedCheck_4572_;
goto v_resetjp_4554_;
}
else
{
lean_inc(v_a_4553_);
lean_dec(v_x_4534_);
v___x_4555_ = lean_box(0);
v_isShared_4556_ = v_isSharedCheck_4572_;
goto v_resetjp_4554_;
}
v_resetjp_4554_:
{
if (lean_obj_tag(v_a_4553_) == 0)
{
lean_object* v___x_4557_; lean_object* v___x_4559_; 
lean_dec_ref_known(v_a_4553_, 0);
lean_dec_ref(v_a_4533_);
v___x_4557_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__3, &l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__3);
if (v_isShared_4556_ == 0)
{
lean_ctor_set_tag(v___x_4555_, 0);
lean_ctor_set(v___x_4555_, 0, v___x_4557_);
v___x_4559_ = v___x_4555_;
goto v_reusejp_4558_;
}
else
{
lean_object* v_reuseFailAlloc_4560_; 
v_reuseFailAlloc_4560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4560_, 0, v___x_4557_);
v___x_4559_ = v_reuseFailAlloc_4560_;
goto v_reusejp_4558_;
}
v_reusejp_4558_:
{
return v___x_4559_;
}
}
else
{
lean_object* v_e_x27_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; lean_object* v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; lean_object* v___x_4568_; lean_object* v___x_4570_; 
v_e_x27_4561_ = lean_ctor_get(v_a_4553_, 0);
lean_inc_ref(v_e_x27_4561_);
lean_dec_ref_known(v_a_4553_, 2);
v___x_4562_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__5, &l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__5_once, _init_l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__5);
v___x_4563_ = l_Lean_indentExpr(v_a_4533_);
v___x_4564_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4564_, 0, v___x_4562_);
lean_ctor_set(v___x_4564_, 1, v___x_4563_);
v___x_4565_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_4566_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4566_, 0, v___x_4564_);
lean_ctor_set(v___x_4566_, 1, v___x_4565_);
v___x_4567_ = l_Lean_indentExpr(v_e_x27_4561_);
v___x_4568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4568_, 0, v___x_4566_);
lean_ctor_set(v___x_4568_, 1, v___x_4567_);
if (v_isShared_4556_ == 0)
{
lean_ctor_set_tag(v___x_4555_, 0);
lean_ctor_set(v___x_4555_, 0, v___x_4568_);
v___x_4570_ = v___x_4555_;
goto v_reusejp_4569_;
}
else
{
lean_object* v_reuseFailAlloc_4571_; 
v_reuseFailAlloc_4571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4571_, 0, v___x_4568_);
v___x_4570_ = v_reuseFailAlloc_4571_;
goto v_reusejp_4569_;
}
v_reusejp_4569_:
{
return v___x_4570_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___boxed(lean_object* v_a_4573_, lean_object* v_x_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_){
_start:
{
lean_object* v_res_4582_; 
v_res_4582_ = l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0(v_a_4573_, v_x_4574_, v___y_4575_, v___y_4576_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_);
lean_dec(v___y_4580_);
lean_dec_ref(v___y_4579_);
lean_dec(v___y_4578_);
lean_dec_ref(v___y_4577_);
lean_dec(v___y_4576_);
lean_dec_ref(v___y_4575_);
return v_res_4582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__3___redArg(lean_object* v_oldTraces_4583_, lean_object* v_data_4584_, lean_object* v_ref_4585_, lean_object* v_msg_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_){
_start:
{
lean_object* v_fileName_4592_; lean_object* v_fileMap_4593_; lean_object* v_options_4594_; lean_object* v_currRecDepth_4595_; lean_object* v_maxRecDepth_4596_; lean_object* v_ref_4597_; lean_object* v_currNamespace_4598_; lean_object* v_openDecls_4599_; lean_object* v_initHeartbeats_4600_; lean_object* v_maxHeartbeats_4601_; lean_object* v_quotContext_4602_; lean_object* v_currMacroScope_4603_; uint8_t v_diag_4604_; lean_object* v_cancelTk_x3f_4605_; uint8_t v_suppressElabErrors_4606_; lean_object* v_inheritedTraceOptions_4607_; lean_object* v___x_4608_; lean_object* v_traceState_4609_; lean_object* v_traces_4610_; lean_object* v_ref_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; size_t v_sz_4614_; size_t v___x_4615_; lean_object* v___x_4616_; lean_object* v_msg_4617_; lean_object* v___x_4618_; lean_object* v_a_4619_; lean_object* v___x_4621_; uint8_t v_isShared_4622_; uint8_t v_isSharedCheck_4656_; 
v_fileName_4592_ = lean_ctor_get(v___y_4589_, 0);
v_fileMap_4593_ = lean_ctor_get(v___y_4589_, 1);
v_options_4594_ = lean_ctor_get(v___y_4589_, 2);
v_currRecDepth_4595_ = lean_ctor_get(v___y_4589_, 3);
v_maxRecDepth_4596_ = lean_ctor_get(v___y_4589_, 4);
v_ref_4597_ = lean_ctor_get(v___y_4589_, 5);
v_currNamespace_4598_ = lean_ctor_get(v___y_4589_, 6);
v_openDecls_4599_ = lean_ctor_get(v___y_4589_, 7);
v_initHeartbeats_4600_ = lean_ctor_get(v___y_4589_, 8);
v_maxHeartbeats_4601_ = lean_ctor_get(v___y_4589_, 9);
v_quotContext_4602_ = lean_ctor_get(v___y_4589_, 10);
v_currMacroScope_4603_ = lean_ctor_get(v___y_4589_, 11);
v_diag_4604_ = lean_ctor_get_uint8(v___y_4589_, sizeof(void*)*14);
v_cancelTk_x3f_4605_ = lean_ctor_get(v___y_4589_, 12);
v_suppressElabErrors_4606_ = lean_ctor_get_uint8(v___y_4589_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_4607_ = lean_ctor_get(v___y_4589_, 13);
v___x_4608_ = lean_st_ref_get(v___y_4590_);
v_traceState_4609_ = lean_ctor_get(v___x_4608_, 4);
lean_inc_ref(v_traceState_4609_);
lean_dec(v___x_4608_);
v_traces_4610_ = lean_ctor_get(v_traceState_4609_, 0);
lean_inc_ref(v_traces_4610_);
lean_dec_ref(v_traceState_4609_);
v_ref_4611_ = l_Lean_replaceRef(v_ref_4585_, v_ref_4597_);
lean_inc_ref(v_inheritedTraceOptions_4607_);
lean_inc(v_cancelTk_x3f_4605_);
lean_inc(v_currMacroScope_4603_);
lean_inc(v_quotContext_4602_);
lean_inc(v_maxHeartbeats_4601_);
lean_inc(v_initHeartbeats_4600_);
lean_inc(v_openDecls_4599_);
lean_inc(v_currNamespace_4598_);
lean_inc(v_maxRecDepth_4596_);
lean_inc(v_currRecDepth_4595_);
lean_inc_ref(v_options_4594_);
lean_inc_ref(v_fileMap_4593_);
lean_inc_ref(v_fileName_4592_);
v___x_4612_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_4612_, 0, v_fileName_4592_);
lean_ctor_set(v___x_4612_, 1, v_fileMap_4593_);
lean_ctor_set(v___x_4612_, 2, v_options_4594_);
lean_ctor_set(v___x_4612_, 3, v_currRecDepth_4595_);
lean_ctor_set(v___x_4612_, 4, v_maxRecDepth_4596_);
lean_ctor_set(v___x_4612_, 5, v_ref_4611_);
lean_ctor_set(v___x_4612_, 6, v_currNamespace_4598_);
lean_ctor_set(v___x_4612_, 7, v_openDecls_4599_);
lean_ctor_set(v___x_4612_, 8, v_initHeartbeats_4600_);
lean_ctor_set(v___x_4612_, 9, v_maxHeartbeats_4601_);
lean_ctor_set(v___x_4612_, 10, v_quotContext_4602_);
lean_ctor_set(v___x_4612_, 11, v_currMacroScope_4603_);
lean_ctor_set(v___x_4612_, 12, v_cancelTk_x3f_4605_);
lean_ctor_set(v___x_4612_, 13, v_inheritedTraceOptions_4607_);
lean_ctor_set_uint8(v___x_4612_, sizeof(void*)*14, v_diag_4604_);
lean_ctor_set_uint8(v___x_4612_, sizeof(void*)*14 + 1, v_suppressElabErrors_4606_);
v___x_4613_ = l_Lean_PersistentArray_toArray___redArg(v_traces_4610_);
lean_dec_ref(v_traces_4610_);
v_sz_4614_ = lean_array_size(v___x_4613_);
v___x_4615_ = ((size_t)0ULL);
v___x_4616_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4_spec__5(v_sz_4614_, v___x_4615_, v___x_4613_);
v_msg_4617_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_4617_, 0, v_data_4584_);
lean_ctor_set(v_msg_4617_, 1, v_msg_4586_);
lean_ctor_set(v_msg_4617_, 2, v___x_4616_);
v___x_4618_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0_spec__0(v_msg_4617_, v___y_4587_, v___y_4588_, v___x_4612_, v___y_4590_);
lean_dec_ref_known(v___x_4612_, 14);
v_a_4619_ = lean_ctor_get(v___x_4618_, 0);
v_isSharedCheck_4656_ = !lean_is_exclusive(v___x_4618_);
if (v_isSharedCheck_4656_ == 0)
{
v___x_4621_ = v___x_4618_;
v_isShared_4622_ = v_isSharedCheck_4656_;
goto v_resetjp_4620_;
}
else
{
lean_inc(v_a_4619_);
lean_dec(v___x_4618_);
v___x_4621_ = lean_box(0);
v_isShared_4622_ = v_isSharedCheck_4656_;
goto v_resetjp_4620_;
}
v_resetjp_4620_:
{
lean_object* v___x_4623_; lean_object* v_traceState_4624_; lean_object* v_env_4625_; lean_object* v_nextMacroScope_4626_; lean_object* v_ngen_4627_; lean_object* v_auxDeclNGen_4628_; lean_object* v_cache_4629_; lean_object* v_messages_4630_; lean_object* v_infoState_4631_; lean_object* v_snapshotTasks_4632_; lean_object* v___x_4634_; uint8_t v_isShared_4635_; uint8_t v_isSharedCheck_4655_; 
v___x_4623_ = lean_st_ref_take(v___y_4590_);
v_traceState_4624_ = lean_ctor_get(v___x_4623_, 4);
v_env_4625_ = lean_ctor_get(v___x_4623_, 0);
v_nextMacroScope_4626_ = lean_ctor_get(v___x_4623_, 1);
v_ngen_4627_ = lean_ctor_get(v___x_4623_, 2);
v_auxDeclNGen_4628_ = lean_ctor_get(v___x_4623_, 3);
v_cache_4629_ = lean_ctor_get(v___x_4623_, 5);
v_messages_4630_ = lean_ctor_get(v___x_4623_, 6);
v_infoState_4631_ = lean_ctor_get(v___x_4623_, 7);
v_snapshotTasks_4632_ = lean_ctor_get(v___x_4623_, 8);
v_isSharedCheck_4655_ = !lean_is_exclusive(v___x_4623_);
if (v_isSharedCheck_4655_ == 0)
{
v___x_4634_ = v___x_4623_;
v_isShared_4635_ = v_isSharedCheck_4655_;
goto v_resetjp_4633_;
}
else
{
lean_inc(v_snapshotTasks_4632_);
lean_inc(v_infoState_4631_);
lean_inc(v_messages_4630_);
lean_inc(v_cache_4629_);
lean_inc(v_traceState_4624_);
lean_inc(v_auxDeclNGen_4628_);
lean_inc(v_ngen_4627_);
lean_inc(v_nextMacroScope_4626_);
lean_inc(v_env_4625_);
lean_dec(v___x_4623_);
v___x_4634_ = lean_box(0);
v_isShared_4635_ = v_isSharedCheck_4655_;
goto v_resetjp_4633_;
}
v_resetjp_4633_:
{
uint64_t v_tid_4636_; lean_object* v___x_4638_; uint8_t v_isShared_4639_; uint8_t v_isSharedCheck_4653_; 
v_tid_4636_ = lean_ctor_get_uint64(v_traceState_4624_, sizeof(void*)*1);
v_isSharedCheck_4653_ = !lean_is_exclusive(v_traceState_4624_);
if (v_isSharedCheck_4653_ == 0)
{
lean_object* v_unused_4654_; 
v_unused_4654_ = lean_ctor_get(v_traceState_4624_, 0);
lean_dec(v_unused_4654_);
v___x_4638_ = v_traceState_4624_;
v_isShared_4639_ = v_isSharedCheck_4653_;
goto v_resetjp_4637_;
}
else
{
lean_dec(v_traceState_4624_);
v___x_4638_ = lean_box(0);
v_isShared_4639_ = v_isSharedCheck_4653_;
goto v_resetjp_4637_;
}
v_resetjp_4637_:
{
lean_object* v___x_4640_; lean_object* v___x_4641_; lean_object* v___x_4643_; 
v___x_4640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4640_, 0, v_ref_4585_);
lean_ctor_set(v___x_4640_, 1, v_a_4619_);
v___x_4641_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_4583_, v___x_4640_);
if (v_isShared_4639_ == 0)
{
lean_ctor_set(v___x_4638_, 0, v___x_4641_);
v___x_4643_ = v___x_4638_;
goto v_reusejp_4642_;
}
else
{
lean_object* v_reuseFailAlloc_4652_; 
v_reuseFailAlloc_4652_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4652_, 0, v___x_4641_);
lean_ctor_set_uint64(v_reuseFailAlloc_4652_, sizeof(void*)*1, v_tid_4636_);
v___x_4643_ = v_reuseFailAlloc_4652_;
goto v_reusejp_4642_;
}
v_reusejp_4642_:
{
lean_object* v___x_4645_; 
if (v_isShared_4635_ == 0)
{
lean_ctor_set(v___x_4634_, 4, v___x_4643_);
v___x_4645_ = v___x_4634_;
goto v_reusejp_4644_;
}
else
{
lean_object* v_reuseFailAlloc_4651_; 
v_reuseFailAlloc_4651_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4651_, 0, v_env_4625_);
lean_ctor_set(v_reuseFailAlloc_4651_, 1, v_nextMacroScope_4626_);
lean_ctor_set(v_reuseFailAlloc_4651_, 2, v_ngen_4627_);
lean_ctor_set(v_reuseFailAlloc_4651_, 3, v_auxDeclNGen_4628_);
lean_ctor_set(v_reuseFailAlloc_4651_, 4, v___x_4643_);
lean_ctor_set(v_reuseFailAlloc_4651_, 5, v_cache_4629_);
lean_ctor_set(v_reuseFailAlloc_4651_, 6, v_messages_4630_);
lean_ctor_set(v_reuseFailAlloc_4651_, 7, v_infoState_4631_);
lean_ctor_set(v_reuseFailAlloc_4651_, 8, v_snapshotTasks_4632_);
v___x_4645_ = v_reuseFailAlloc_4651_;
goto v_reusejp_4644_;
}
v_reusejp_4644_:
{
lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4649_; 
v___x_4646_ = lean_st_ref_set(v___y_4590_, v___x_4645_);
v___x_4647_ = lean_box(0);
if (v_isShared_4622_ == 0)
{
lean_ctor_set(v___x_4621_, 0, v___x_4647_);
v___x_4649_ = v___x_4621_;
goto v_reusejp_4648_;
}
else
{
lean_object* v_reuseFailAlloc_4650_; 
v_reuseFailAlloc_4650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4650_, 0, v___x_4647_);
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__3___redArg___boxed(lean_object* v_oldTraces_4657_, lean_object* v_data_4658_, lean_object* v_ref_4659_, lean_object* v_msg_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_){
_start:
{
lean_object* v_res_4666_; 
v_res_4666_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__3___redArg(v_oldTraces_4657_, v_data_4658_, v_ref_4659_, v_msg_4660_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_);
lean_dec(v___y_4664_);
lean_dec_ref(v___y_4663_);
lean_dec(v___y_4662_);
lean_dec_ref(v___y_4661_);
return v_res_4666_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4___redArg(lean_object* v_x_4667_){
_start:
{
if (lean_obj_tag(v_x_4667_) == 0)
{
lean_object* v_a_4669_; lean_object* v___x_4671_; uint8_t v_isShared_4672_; uint8_t v_isSharedCheck_4676_; 
v_a_4669_ = lean_ctor_get(v_x_4667_, 0);
v_isSharedCheck_4676_ = !lean_is_exclusive(v_x_4667_);
if (v_isSharedCheck_4676_ == 0)
{
v___x_4671_ = v_x_4667_;
v_isShared_4672_ = v_isSharedCheck_4676_;
goto v_resetjp_4670_;
}
else
{
lean_inc(v_a_4669_);
lean_dec(v_x_4667_);
v___x_4671_ = lean_box(0);
v_isShared_4672_ = v_isSharedCheck_4676_;
goto v_resetjp_4670_;
}
v_resetjp_4670_:
{
lean_object* v___x_4674_; 
if (v_isShared_4672_ == 0)
{
lean_ctor_set_tag(v___x_4671_, 1);
v___x_4674_ = v___x_4671_;
goto v_reusejp_4673_;
}
else
{
lean_object* v_reuseFailAlloc_4675_; 
v_reuseFailAlloc_4675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4675_, 0, v_a_4669_);
v___x_4674_ = v_reuseFailAlloc_4675_;
goto v_reusejp_4673_;
}
v_reusejp_4673_:
{
return v___x_4674_;
}
}
}
else
{
lean_object* v_a_4677_; lean_object* v___x_4679_; uint8_t v_isShared_4680_; uint8_t v_isSharedCheck_4684_; 
v_a_4677_ = lean_ctor_get(v_x_4667_, 0);
v_isSharedCheck_4684_ = !lean_is_exclusive(v_x_4667_);
if (v_isSharedCheck_4684_ == 0)
{
v___x_4679_ = v_x_4667_;
v_isShared_4680_ = v_isSharedCheck_4684_;
goto v_resetjp_4678_;
}
else
{
lean_inc(v_a_4677_);
lean_dec(v_x_4667_);
v___x_4679_ = lean_box(0);
v_isShared_4680_ = v_isSharedCheck_4684_;
goto v_resetjp_4678_;
}
v_resetjp_4678_:
{
lean_object* v___x_4682_; 
if (v_isShared_4680_ == 0)
{
lean_ctor_set_tag(v___x_4679_, 0);
v___x_4682_ = v___x_4679_;
goto v_reusejp_4681_;
}
else
{
lean_object* v_reuseFailAlloc_4683_; 
v_reuseFailAlloc_4683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4683_, 0, v_a_4677_);
v___x_4682_ = v_reuseFailAlloc_4683_;
goto v_reusejp_4681_;
}
v_reusejp_4681_:
{
return v___x_4682_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4___redArg___boxed(lean_object* v_x_4685_, lean_object* v___y_4686_){
_start:
{
lean_object* v_res_4687_; 
v_res_4687_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4___redArg(v_x_4685_);
return v_res_4687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2(lean_object* v_cls_4688_, uint8_t v_collapsed_4689_, lean_object* v_tag_4690_, lean_object* v_opts_4691_, uint8_t v_clsEnabled_4692_, lean_object* v_oldTraces_4693_, lean_object* v_msg_4694_, lean_object* v_resStartStop_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_, lean_object* v___y_4700_, lean_object* v___y_4701_){
_start:
{
lean_object* v_fst_4703_; lean_object* v_snd_4704_; lean_object* v___y_4706_; lean_object* v___y_4707_; lean_object* v_data_4708_; lean_object* v_fst_4719_; lean_object* v_snd_4720_; lean_object* v___x_4721_; uint8_t v___x_4722_; lean_object* v___y_4724_; lean_object* v_a_4725_; uint8_t v___y_4740_; double v___y_4771_; 
v_fst_4703_ = lean_ctor_get(v_resStartStop_4695_, 0);
lean_inc(v_fst_4703_);
v_snd_4704_ = lean_ctor_get(v_resStartStop_4695_, 1);
lean_inc(v_snd_4704_);
lean_dec_ref(v_resStartStop_4695_);
v_fst_4719_ = lean_ctor_get(v_snd_4704_, 0);
lean_inc(v_fst_4719_);
v_snd_4720_ = lean_ctor_get(v_snd_4704_, 1);
lean_inc(v_snd_4720_);
lean_dec(v_snd_4704_);
v___x_4721_ = l_Lean_trace_profiler;
v___x_4722_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_4691_, v___x_4721_);
if (v___x_4722_ == 0)
{
v___y_4740_ = v___x_4722_;
goto v___jp_4739_;
}
else
{
lean_object* v___x_4776_; uint8_t v___x_4777_; 
v___x_4776_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4777_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_4691_, v___x_4776_);
if (v___x_4777_ == 0)
{
lean_object* v___x_4778_; lean_object* v___x_4779_; double v___x_4780_; double v___x_4781_; double v___x_4782_; 
v___x_4778_ = l_Lean_trace_profiler_threshold;
v___x_4779_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_4691_, v___x_4778_);
v___x_4780_ = lean_float_of_nat(v___x_4779_);
v___x_4781_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2);
v___x_4782_ = lean_float_div(v___x_4780_, v___x_4781_);
v___y_4771_ = v___x_4782_;
goto v___jp_4770_;
}
else
{
lean_object* v___x_4783_; lean_object* v___x_4784_; double v___x_4785_; 
v___x_4783_ = l_Lean_trace_profiler_threshold;
v___x_4784_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_4691_, v___x_4783_);
v___x_4785_ = lean_float_of_nat(v___x_4784_);
v___y_4771_ = v___x_4785_;
goto v___jp_4770_;
}
}
v___jp_4705_:
{
lean_object* v___x_4709_; 
lean_inc(v___y_4707_);
v___x_4709_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__3___redArg(v_oldTraces_4693_, v_data_4708_, v___y_4707_, v___y_4706_, v___y_4698_, v___y_4699_, v___y_4700_, v___y_4701_);
if (lean_obj_tag(v___x_4709_) == 0)
{
lean_object* v___x_4710_; 
lean_dec_ref_known(v___x_4709_, 1);
v___x_4710_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4___redArg(v_fst_4703_);
return v___x_4710_;
}
else
{
lean_object* v_a_4711_; lean_object* v___x_4713_; uint8_t v_isShared_4714_; uint8_t v_isSharedCheck_4718_; 
lean_dec(v_fst_4703_);
v_a_4711_ = lean_ctor_get(v___x_4709_, 0);
v_isSharedCheck_4718_ = !lean_is_exclusive(v___x_4709_);
if (v_isSharedCheck_4718_ == 0)
{
v___x_4713_ = v___x_4709_;
v_isShared_4714_ = v_isSharedCheck_4718_;
goto v_resetjp_4712_;
}
else
{
lean_inc(v_a_4711_);
lean_dec(v___x_4709_);
v___x_4713_ = lean_box(0);
v_isShared_4714_ = v_isSharedCheck_4718_;
goto v_resetjp_4712_;
}
v_resetjp_4712_:
{
lean_object* v___x_4716_; 
if (v_isShared_4714_ == 0)
{
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
return v___x_4716_;
}
}
}
}
v___jp_4723_:
{
uint8_t v_result_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; double v___x_4729_; lean_object* v_data_4730_; 
v_result_4726_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__6(v_fst_4703_);
v___x_4727_ = lean_box(v_result_4726_);
v___x_4728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4728_, 0, v___x_4727_);
v___x_4729_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_4690_);
lean_inc_ref(v___x_4728_);
lean_inc(v_cls_4688_);
v_data_4730_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4730_, 0, v_cls_4688_);
lean_ctor_set(v_data_4730_, 1, v___x_4728_);
lean_ctor_set(v_data_4730_, 2, v_tag_4690_);
lean_ctor_set_float(v_data_4730_, sizeof(void*)*3, v___x_4729_);
lean_ctor_set_float(v_data_4730_, sizeof(void*)*3 + 8, v___x_4729_);
lean_ctor_set_uint8(v_data_4730_, sizeof(void*)*3 + 16, v_collapsed_4689_);
if (v___x_4722_ == 0)
{
lean_dec_ref_known(v___x_4728_, 1);
lean_dec(v_snd_4720_);
lean_dec(v_fst_4719_);
lean_dec_ref(v_tag_4690_);
lean_dec(v_cls_4688_);
v___y_4706_ = v_a_4725_;
v___y_4707_ = v___y_4724_;
v_data_4708_ = v_data_4730_;
goto v___jp_4705_;
}
else
{
lean_object* v_data_4731_; double v___x_4732_; double v___x_4733_; 
lean_dec_ref_known(v_data_4730_, 3);
v_data_4731_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4731_, 0, v_cls_4688_);
lean_ctor_set(v_data_4731_, 1, v___x_4728_);
lean_ctor_set(v_data_4731_, 2, v_tag_4690_);
v___x_4732_ = lean_unbox_float(v_fst_4719_);
lean_dec(v_fst_4719_);
lean_ctor_set_float(v_data_4731_, sizeof(void*)*3, v___x_4732_);
v___x_4733_ = lean_unbox_float(v_snd_4720_);
lean_dec(v_snd_4720_);
lean_ctor_set_float(v_data_4731_, sizeof(void*)*3 + 8, v___x_4733_);
lean_ctor_set_uint8(v_data_4731_, sizeof(void*)*3 + 16, v_collapsed_4689_);
v___y_4706_ = v_a_4725_;
v___y_4707_ = v___y_4724_;
v_data_4708_ = v_data_4731_;
goto v___jp_4705_;
}
}
v___jp_4734_:
{
lean_object* v_ref_4735_; lean_object* v___x_4736_; 
v_ref_4735_ = lean_ctor_get(v___y_4700_, 5);
lean_inc(v___y_4701_);
lean_inc_ref(v___y_4700_);
lean_inc(v___y_4699_);
lean_inc_ref(v___y_4698_);
lean_inc(v___y_4697_);
lean_inc_ref(v___y_4696_);
lean_inc(v_fst_4703_);
v___x_4736_ = lean_apply_8(v_msg_4694_, v_fst_4703_, v___y_4696_, v___y_4697_, v___y_4698_, v___y_4699_, v___y_4700_, v___y_4701_, lean_box(0));
if (lean_obj_tag(v___x_4736_) == 0)
{
lean_object* v_a_4737_; 
v_a_4737_ = lean_ctor_get(v___x_4736_, 0);
lean_inc(v_a_4737_);
lean_dec_ref_known(v___x_4736_, 1);
v___y_4724_ = v_ref_4735_;
v_a_4725_ = v_a_4737_;
goto v___jp_4723_;
}
else
{
lean_object* v___x_4738_; 
lean_dec_ref_known(v___x_4736_, 1);
v___x_4738_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1);
v___y_4724_ = v_ref_4735_;
v_a_4725_ = v___x_4738_;
goto v___jp_4723_;
}
}
v___jp_4739_:
{
if (v_clsEnabled_4692_ == 0)
{
if (v___y_4740_ == 0)
{
lean_object* v___x_4741_; lean_object* v_traceState_4742_; lean_object* v_env_4743_; lean_object* v_nextMacroScope_4744_; lean_object* v_ngen_4745_; lean_object* v_auxDeclNGen_4746_; lean_object* v_cache_4747_; lean_object* v_messages_4748_; lean_object* v_infoState_4749_; lean_object* v_snapshotTasks_4750_; lean_object* v___x_4752_; uint8_t v_isShared_4753_; uint8_t v_isSharedCheck_4769_; 
lean_dec(v_snd_4720_);
lean_dec(v_fst_4719_);
lean_dec_ref(v_msg_4694_);
lean_dec_ref(v_tag_4690_);
lean_dec(v_cls_4688_);
v___x_4741_ = lean_st_ref_take(v___y_4701_);
v_traceState_4742_ = lean_ctor_get(v___x_4741_, 4);
v_env_4743_ = lean_ctor_get(v___x_4741_, 0);
v_nextMacroScope_4744_ = lean_ctor_get(v___x_4741_, 1);
v_ngen_4745_ = lean_ctor_get(v___x_4741_, 2);
v_auxDeclNGen_4746_ = lean_ctor_get(v___x_4741_, 3);
v_cache_4747_ = lean_ctor_get(v___x_4741_, 5);
v_messages_4748_ = lean_ctor_get(v___x_4741_, 6);
v_infoState_4749_ = lean_ctor_get(v___x_4741_, 7);
v_snapshotTasks_4750_ = lean_ctor_get(v___x_4741_, 8);
v_isSharedCheck_4769_ = !lean_is_exclusive(v___x_4741_);
if (v_isSharedCheck_4769_ == 0)
{
v___x_4752_ = v___x_4741_;
v_isShared_4753_ = v_isSharedCheck_4769_;
goto v_resetjp_4751_;
}
else
{
lean_inc(v_snapshotTasks_4750_);
lean_inc(v_infoState_4749_);
lean_inc(v_messages_4748_);
lean_inc(v_cache_4747_);
lean_inc(v_traceState_4742_);
lean_inc(v_auxDeclNGen_4746_);
lean_inc(v_ngen_4745_);
lean_inc(v_nextMacroScope_4744_);
lean_inc(v_env_4743_);
lean_dec(v___x_4741_);
v___x_4752_ = lean_box(0);
v_isShared_4753_ = v_isSharedCheck_4769_;
goto v_resetjp_4751_;
}
v_resetjp_4751_:
{
uint64_t v_tid_4754_; lean_object* v_traces_4755_; lean_object* v___x_4757_; uint8_t v_isShared_4758_; uint8_t v_isSharedCheck_4768_; 
v_tid_4754_ = lean_ctor_get_uint64(v_traceState_4742_, sizeof(void*)*1);
v_traces_4755_ = lean_ctor_get(v_traceState_4742_, 0);
v_isSharedCheck_4768_ = !lean_is_exclusive(v_traceState_4742_);
if (v_isSharedCheck_4768_ == 0)
{
v___x_4757_ = v_traceState_4742_;
v_isShared_4758_ = v_isSharedCheck_4768_;
goto v_resetjp_4756_;
}
else
{
lean_inc(v_traces_4755_);
lean_dec(v_traceState_4742_);
v___x_4757_ = lean_box(0);
v_isShared_4758_ = v_isSharedCheck_4768_;
goto v_resetjp_4756_;
}
v_resetjp_4756_:
{
lean_object* v___x_4759_; lean_object* v___x_4761_; 
v___x_4759_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_4693_, v_traces_4755_);
lean_dec_ref(v_traces_4755_);
if (v_isShared_4758_ == 0)
{
lean_ctor_set(v___x_4757_, 0, v___x_4759_);
v___x_4761_ = v___x_4757_;
goto v_reusejp_4760_;
}
else
{
lean_object* v_reuseFailAlloc_4767_; 
v_reuseFailAlloc_4767_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4767_, 0, v___x_4759_);
lean_ctor_set_uint64(v_reuseFailAlloc_4767_, sizeof(void*)*1, v_tid_4754_);
v___x_4761_ = v_reuseFailAlloc_4767_;
goto v_reusejp_4760_;
}
v_reusejp_4760_:
{
lean_object* v___x_4763_; 
if (v_isShared_4753_ == 0)
{
lean_ctor_set(v___x_4752_, 4, v___x_4761_);
v___x_4763_ = v___x_4752_;
goto v_reusejp_4762_;
}
else
{
lean_object* v_reuseFailAlloc_4766_; 
v_reuseFailAlloc_4766_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4766_, 0, v_env_4743_);
lean_ctor_set(v_reuseFailAlloc_4766_, 1, v_nextMacroScope_4744_);
lean_ctor_set(v_reuseFailAlloc_4766_, 2, v_ngen_4745_);
lean_ctor_set(v_reuseFailAlloc_4766_, 3, v_auxDeclNGen_4746_);
lean_ctor_set(v_reuseFailAlloc_4766_, 4, v___x_4761_);
lean_ctor_set(v_reuseFailAlloc_4766_, 5, v_cache_4747_);
lean_ctor_set(v_reuseFailAlloc_4766_, 6, v_messages_4748_);
lean_ctor_set(v_reuseFailAlloc_4766_, 7, v_infoState_4749_);
lean_ctor_set(v_reuseFailAlloc_4766_, 8, v_snapshotTasks_4750_);
v___x_4763_ = v_reuseFailAlloc_4766_;
goto v_reusejp_4762_;
}
v_reusejp_4762_:
{
lean_object* v___x_4764_; lean_object* v___x_4765_; 
v___x_4764_ = lean_st_ref_set(v___y_4701_, v___x_4763_);
v___x_4765_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4___redArg(v_fst_4703_);
return v___x_4765_;
}
}
}
}
}
else
{
goto v___jp_4734_;
}
}
else
{
goto v___jp_4734_;
}
}
v___jp_4770_:
{
double v___x_4772_; double v___x_4773_; double v___x_4774_; uint8_t v___x_4775_; 
v___x_4772_ = lean_unbox_float(v_snd_4720_);
v___x_4773_ = lean_unbox_float(v_fst_4719_);
v___x_4774_ = lean_float_sub(v___x_4772_, v___x_4773_);
v___x_4775_ = lean_float_decLt(v___y_4771_, v___x_4774_);
v___y_4740_ = v___x_4775_;
goto v___jp_4739_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2___boxed(lean_object* v_cls_4786_, lean_object* v_collapsed_4787_, lean_object* v_tag_4788_, lean_object* v_opts_4789_, lean_object* v_clsEnabled_4790_, lean_object* v_oldTraces_4791_, lean_object* v_msg_4792_, lean_object* v_resStartStop_4793_, lean_object* v___y_4794_, lean_object* v___y_4795_, lean_object* v___y_4796_, lean_object* v___y_4797_, lean_object* v___y_4798_, lean_object* v___y_4799_, lean_object* v___y_4800_){
_start:
{
uint8_t v_collapsed_boxed_4801_; uint8_t v_clsEnabled_boxed_4802_; lean_object* v_res_4803_; 
v_collapsed_boxed_4801_ = lean_unbox(v_collapsed_4787_);
v_clsEnabled_boxed_4802_ = lean_unbox(v_clsEnabled_4790_);
v_res_4803_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2(v_cls_4786_, v_collapsed_boxed_4801_, v_tag_4788_, v_opts_4789_, v_clsEnabled_boxed_4802_, v_oldTraces_4791_, v_msg_4792_, v_resStartStop_4793_, v___y_4794_, v___y_4795_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_);
lean_dec(v___y_4799_);
lean_dec_ref(v___y_4798_);
lean_dec(v___y_4797_);
lean_dec_ref(v___y_4796_);
lean_dec(v___y_4795_);
lean_dec_ref(v___y_4794_);
lean_dec_ref(v_opts_4789_);
return v_res_4803_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4805_; lean_object* v___x_4806_; 
v___x_4805_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__0));
v___x_4806_ = l_Lean_stringToMessageData(v___x_4805_);
return v___x_4806_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4808_; lean_object* v___x_4809_; 
v___x_4808_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__2));
v___x_4809_ = l_Lean_stringToMessageData(v___x_4808_);
return v___x_4809_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4811_; lean_object* v___x_4812_; 
v___x_4811_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__4));
v___x_4812_ = l_Lean_stringToMessageData(v___x_4811_);
return v___x_4812_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0(lean_object* v_a_4813_, lean_object* v___x_4814_, lean_object* v_x_4815_, lean_object* v___y_4816_, lean_object* v___y_4817_, lean_object* v___y_4818_, lean_object* v___y_4819_, lean_object* v___y_4820_, lean_object* v___y_4821_){
_start:
{
if (lean_obj_tag(v_x_4815_) == 0)
{
lean_object* v_a_4823_; lean_object* v___x_4825_; uint8_t v_isShared_4826_; uint8_t v_isSharedCheck_4838_; 
lean_dec_ref(v___x_4814_);
v_a_4823_ = lean_ctor_get(v_x_4815_, 0);
v_isSharedCheck_4838_ = !lean_is_exclusive(v_x_4815_);
if (v_isSharedCheck_4838_ == 0)
{
v___x_4825_ = v_x_4815_;
v_isShared_4826_ = v_isSharedCheck_4838_;
goto v_resetjp_4824_;
}
else
{
lean_inc(v_a_4823_);
lean_dec(v_x_4815_);
v___x_4825_ = lean_box(0);
v_isShared_4826_ = v_isSharedCheck_4838_;
goto v_resetjp_4824_;
}
v_resetjp_4824_:
{
lean_object* v___x_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; lean_object* v___x_4836_; 
v___x_4827_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1);
v___x_4828_ = l_Lean_LocalDecl_userName(v_a_4813_);
v___x_4829_ = l_Lean_MessageData_ofName(v___x_4828_);
v___x_4830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4830_, 0, v___x_4827_);
lean_ctor_set(v___x_4830_, 1, v___x_4829_);
v___x_4831_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__3);
v___x_4832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4832_, 0, v___x_4830_);
lean_ctor_set(v___x_4832_, 1, v___x_4831_);
v___x_4833_ = l_Lean_Exception_toMessageData(v_a_4823_);
v___x_4834_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4834_, 0, v___x_4832_);
lean_ctor_set(v___x_4834_, 1, v___x_4833_);
if (v_isShared_4826_ == 0)
{
lean_ctor_set(v___x_4825_, 0, v___x_4834_);
v___x_4836_ = v___x_4825_;
goto v_reusejp_4835_;
}
else
{
lean_object* v_reuseFailAlloc_4837_; 
v_reuseFailAlloc_4837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4837_, 0, v___x_4834_);
v___x_4836_ = v_reuseFailAlloc_4837_;
goto v_reusejp_4835_;
}
v_reusejp_4835_:
{
return v___x_4836_;
}
}
}
else
{
lean_object* v_a_4839_; lean_object* v___x_4841_; uint8_t v_isShared_4842_; uint8_t v_isSharedCheck_4868_; 
v_a_4839_ = lean_ctor_get(v_x_4815_, 0);
v_isSharedCheck_4868_ = !lean_is_exclusive(v_x_4815_);
if (v_isSharedCheck_4868_ == 0)
{
v___x_4841_ = v_x_4815_;
v_isShared_4842_ = v_isSharedCheck_4868_;
goto v_resetjp_4840_;
}
else
{
lean_inc(v_a_4839_);
lean_dec(v_x_4815_);
v___x_4841_ = lean_box(0);
v_isShared_4842_ = v_isSharedCheck_4868_;
goto v_resetjp_4840_;
}
v_resetjp_4840_:
{
if (lean_obj_tag(v_a_4839_) == 0)
{
lean_object* v___x_4843_; lean_object* v___x_4844_; lean_object* v___x_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; lean_object* v___x_4850_; 
lean_dec_ref_known(v_a_4839_, 0);
lean_dec_ref(v___x_4814_);
v___x_4843_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1);
v___x_4844_ = l_Lean_LocalDecl_userName(v_a_4813_);
v___x_4845_ = l_Lean_MessageData_ofName(v___x_4844_);
v___x_4846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4846_, 0, v___x_4843_);
lean_ctor_set(v___x_4846_, 1, v___x_4845_);
v___x_4847_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__5);
v___x_4848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4848_, 0, v___x_4846_);
lean_ctor_set(v___x_4848_, 1, v___x_4847_);
if (v_isShared_4842_ == 0)
{
lean_ctor_set_tag(v___x_4841_, 0);
lean_ctor_set(v___x_4841_, 0, v___x_4848_);
v___x_4850_ = v___x_4841_;
goto v_reusejp_4849_;
}
else
{
lean_object* v_reuseFailAlloc_4851_; 
v_reuseFailAlloc_4851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4851_, 0, v___x_4848_);
v___x_4850_ = v_reuseFailAlloc_4851_;
goto v_reusejp_4849_;
}
v_reusejp_4849_:
{
return v___x_4850_;
}
}
else
{
lean_object* v_e_x27_4852_; lean_object* v___x_4853_; lean_object* v___x_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; lean_object* v___x_4859_; lean_object* v___x_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; lean_object* v___x_4866_; 
v_e_x27_4852_ = lean_ctor_get(v_a_4839_, 0);
lean_inc_ref(v_e_x27_4852_);
lean_dec_ref_known(v_a_4839_, 2);
v___x_4853_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1);
v___x_4854_ = l_Lean_LocalDecl_userName(v_a_4813_);
v___x_4855_ = l_Lean_MessageData_ofName(v___x_4854_);
v___x_4856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4856_, 0, v___x_4853_);
lean_ctor_set(v___x_4856_, 1, v___x_4855_);
v___x_4857_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8);
v___x_4858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4858_, 0, v___x_4856_);
lean_ctor_set(v___x_4858_, 1, v___x_4857_);
v___x_4859_ = l_Lean_indentExpr(v___x_4814_);
v___x_4860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4860_, 0, v___x_4858_);
lean_ctor_set(v___x_4860_, 1, v___x_4859_);
v___x_4861_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_4862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4862_, 0, v___x_4860_);
lean_ctor_set(v___x_4862_, 1, v___x_4861_);
v___x_4863_ = l_Lean_indentExpr(v_e_x27_4852_);
v___x_4864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4864_, 0, v___x_4862_);
lean_ctor_set(v___x_4864_, 1, v___x_4863_);
if (v_isShared_4842_ == 0)
{
lean_ctor_set_tag(v___x_4841_, 0);
lean_ctor_set(v___x_4841_, 0, v___x_4864_);
v___x_4866_ = v___x_4841_;
goto v_reusejp_4865_;
}
else
{
lean_object* v_reuseFailAlloc_4867_; 
v_reuseFailAlloc_4867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4867_, 0, v___x_4864_);
v___x_4866_ = v_reuseFailAlloc_4867_;
goto v_reusejp_4865_;
}
v_reusejp_4865_:
{
return v___x_4866_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___boxed(lean_object* v_a_4869_, lean_object* v___x_4870_, lean_object* v_x_4871_, lean_object* v___y_4872_, lean_object* v___y_4873_, lean_object* v___y_4874_, lean_object* v___y_4875_, lean_object* v___y_4876_, lean_object* v___y_4877_, lean_object* v___y_4878_){
_start:
{
lean_object* v_res_4879_; 
v_res_4879_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0(v_a_4869_, v___x_4870_, v_x_4871_, v___y_4872_, v___y_4873_, v___y_4874_, v___y_4875_, v___y_4876_, v___y_4877_);
lean_dec(v___y_4877_);
lean_dec_ref(v___y_4876_);
lean_dec(v___y_4875_);
lean_dec_ref(v___y_4874_);
lean_dec(v___y_4873_);
lean_dec_ref(v___y_4872_);
lean_dec_ref(v_a_4869_);
return v_res_4879_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__7_spec__9___redArg(lean_object* v_x_4880_, lean_object* v_x_4881_, lean_object* v_x_4882_, lean_object* v_x_4883_){
_start:
{
lean_object* v_ks_4884_; lean_object* v_vs_4885_; lean_object* v___x_4887_; uint8_t v_isShared_4888_; uint8_t v_isSharedCheck_4909_; 
v_ks_4884_ = lean_ctor_get(v_x_4880_, 0);
v_vs_4885_ = lean_ctor_get(v_x_4880_, 1);
v_isSharedCheck_4909_ = !lean_is_exclusive(v_x_4880_);
if (v_isSharedCheck_4909_ == 0)
{
v___x_4887_ = v_x_4880_;
v_isShared_4888_ = v_isSharedCheck_4909_;
goto v_resetjp_4886_;
}
else
{
lean_inc(v_vs_4885_);
lean_inc(v_ks_4884_);
lean_dec(v_x_4880_);
v___x_4887_ = lean_box(0);
v_isShared_4888_ = v_isSharedCheck_4909_;
goto v_resetjp_4886_;
}
v_resetjp_4886_:
{
lean_object* v___x_4889_; uint8_t v___x_4890_; 
v___x_4889_ = lean_array_get_size(v_ks_4884_);
v___x_4890_ = lean_nat_dec_lt(v_x_4881_, v___x_4889_);
if (v___x_4890_ == 0)
{
lean_object* v___x_4891_; lean_object* v___x_4892_; lean_object* v___x_4894_; 
lean_dec(v_x_4881_);
v___x_4891_ = lean_array_push(v_ks_4884_, v_x_4882_);
v___x_4892_ = lean_array_push(v_vs_4885_, v_x_4883_);
if (v_isShared_4888_ == 0)
{
lean_ctor_set(v___x_4887_, 1, v___x_4892_);
lean_ctor_set(v___x_4887_, 0, v___x_4891_);
v___x_4894_ = v___x_4887_;
goto v_reusejp_4893_;
}
else
{
lean_object* v_reuseFailAlloc_4895_; 
v_reuseFailAlloc_4895_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4895_, 0, v___x_4891_);
lean_ctor_set(v_reuseFailAlloc_4895_, 1, v___x_4892_);
v___x_4894_ = v_reuseFailAlloc_4895_;
goto v_reusejp_4893_;
}
v_reusejp_4893_:
{
return v___x_4894_;
}
}
else
{
lean_object* v_k_x27_4896_; uint8_t v___x_4897_; 
v_k_x27_4896_ = lean_array_fget_borrowed(v_ks_4884_, v_x_4881_);
v___x_4897_ = l_Lean_instBEqMVarId_beq(v_x_4882_, v_k_x27_4896_);
if (v___x_4897_ == 0)
{
lean_object* v___x_4899_; 
if (v_isShared_4888_ == 0)
{
v___x_4899_ = v___x_4887_;
goto v_reusejp_4898_;
}
else
{
lean_object* v_reuseFailAlloc_4903_; 
v_reuseFailAlloc_4903_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4903_, 0, v_ks_4884_);
lean_ctor_set(v_reuseFailAlloc_4903_, 1, v_vs_4885_);
v___x_4899_ = v_reuseFailAlloc_4903_;
goto v_reusejp_4898_;
}
v_reusejp_4898_:
{
lean_object* v___x_4900_; lean_object* v___x_4901_; 
v___x_4900_ = lean_unsigned_to_nat(1u);
v___x_4901_ = lean_nat_add(v_x_4881_, v___x_4900_);
lean_dec(v_x_4881_);
v_x_4880_ = v___x_4899_;
v_x_4881_ = v___x_4901_;
goto _start;
}
}
else
{
lean_object* v___x_4904_; lean_object* v___x_4905_; lean_object* v___x_4907_; 
v___x_4904_ = lean_array_fset(v_ks_4884_, v_x_4881_, v_x_4882_);
v___x_4905_ = lean_array_fset(v_vs_4885_, v_x_4881_, v_x_4883_);
lean_dec(v_x_4881_);
if (v_isShared_4888_ == 0)
{
lean_ctor_set(v___x_4887_, 1, v___x_4905_);
lean_ctor_set(v___x_4887_, 0, v___x_4904_);
v___x_4907_ = v___x_4887_;
goto v_reusejp_4906_;
}
else
{
lean_object* v_reuseFailAlloc_4908_; 
v_reuseFailAlloc_4908_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4908_, 0, v___x_4904_);
lean_ctor_set(v_reuseFailAlloc_4908_, 1, v___x_4905_);
v___x_4907_ = v_reuseFailAlloc_4908_;
goto v_reusejp_4906_;
}
v_reusejp_4906_:
{
return v___x_4907_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__7___redArg(lean_object* v_n_4910_, lean_object* v_k_4911_, lean_object* v_v_4912_){
_start:
{
lean_object* v___x_4913_; lean_object* v___x_4914_; 
v___x_4913_ = lean_unsigned_to_nat(0u);
v___x_4914_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__7_spec__9___redArg(v_n_4910_, v___x_4913_, v_k_4911_, v_v_4912_);
return v___x_4914_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_4915_; 
v___x_4915_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_4915_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg(lean_object* v_x_4916_, size_t v_x_4917_, size_t v_x_4918_, lean_object* v_x_4919_, lean_object* v_x_4920_){
_start:
{
if (lean_obj_tag(v_x_4916_) == 0)
{
lean_object* v_es_4921_; size_t v___x_4922_; size_t v___x_4923_; lean_object* v_j_4924_; lean_object* v___x_4925_; uint8_t v___x_4926_; 
v_es_4921_ = lean_ctor_get(v_x_4916_, 0);
v___x_4922_ = ((size_t)31ULL);
v___x_4923_ = lean_usize_land(v_x_4917_, v___x_4922_);
v_j_4924_ = lean_usize_to_nat(v___x_4923_);
v___x_4925_ = lean_array_get_size(v_es_4921_);
v___x_4926_ = lean_nat_dec_lt(v_j_4924_, v___x_4925_);
if (v___x_4926_ == 0)
{
lean_dec(v_j_4924_);
lean_dec(v_x_4920_);
lean_dec(v_x_4919_);
return v_x_4916_;
}
else
{
lean_object* v___x_4928_; uint8_t v_isShared_4929_; uint8_t v_isSharedCheck_4965_; 
lean_inc_ref(v_es_4921_);
v_isSharedCheck_4965_ = !lean_is_exclusive(v_x_4916_);
if (v_isSharedCheck_4965_ == 0)
{
lean_object* v_unused_4966_; 
v_unused_4966_ = lean_ctor_get(v_x_4916_, 0);
lean_dec(v_unused_4966_);
v___x_4928_ = v_x_4916_;
v_isShared_4929_ = v_isSharedCheck_4965_;
goto v_resetjp_4927_;
}
else
{
lean_dec(v_x_4916_);
v___x_4928_ = lean_box(0);
v_isShared_4929_ = v_isSharedCheck_4965_;
goto v_resetjp_4927_;
}
v_resetjp_4927_:
{
lean_object* v_v_4930_; lean_object* v___x_4931_; lean_object* v_xs_x27_4932_; lean_object* v___y_4934_; 
v_v_4930_ = lean_array_fget(v_es_4921_, v_j_4924_);
v___x_4931_ = lean_box(0);
v_xs_x27_4932_ = lean_array_fset(v_es_4921_, v_j_4924_, v___x_4931_);
switch(lean_obj_tag(v_v_4930_))
{
case 0:
{
lean_object* v_key_4939_; lean_object* v_val_4940_; lean_object* v___x_4942_; uint8_t v_isShared_4943_; uint8_t v_isSharedCheck_4950_; 
v_key_4939_ = lean_ctor_get(v_v_4930_, 0);
v_val_4940_ = lean_ctor_get(v_v_4930_, 1);
v_isSharedCheck_4950_ = !lean_is_exclusive(v_v_4930_);
if (v_isSharedCheck_4950_ == 0)
{
v___x_4942_ = v_v_4930_;
v_isShared_4943_ = v_isSharedCheck_4950_;
goto v_resetjp_4941_;
}
else
{
lean_inc(v_val_4940_);
lean_inc(v_key_4939_);
lean_dec(v_v_4930_);
v___x_4942_ = lean_box(0);
v_isShared_4943_ = v_isSharedCheck_4950_;
goto v_resetjp_4941_;
}
v_resetjp_4941_:
{
uint8_t v___x_4944_; 
v___x_4944_ = l_Lean_instBEqMVarId_beq(v_x_4919_, v_key_4939_);
if (v___x_4944_ == 0)
{
lean_object* v___x_4945_; lean_object* v___x_4946_; 
lean_del_object(v___x_4942_);
v___x_4945_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_4939_, v_val_4940_, v_x_4919_, v_x_4920_);
v___x_4946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4946_, 0, v___x_4945_);
v___y_4934_ = v___x_4946_;
goto v___jp_4933_;
}
else
{
lean_object* v___x_4948_; 
lean_dec(v_val_4940_);
lean_dec(v_key_4939_);
if (v_isShared_4943_ == 0)
{
lean_ctor_set(v___x_4942_, 1, v_x_4920_);
lean_ctor_set(v___x_4942_, 0, v_x_4919_);
v___x_4948_ = v___x_4942_;
goto v_reusejp_4947_;
}
else
{
lean_object* v_reuseFailAlloc_4949_; 
v_reuseFailAlloc_4949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4949_, 0, v_x_4919_);
lean_ctor_set(v_reuseFailAlloc_4949_, 1, v_x_4920_);
v___x_4948_ = v_reuseFailAlloc_4949_;
goto v_reusejp_4947_;
}
v_reusejp_4947_:
{
v___y_4934_ = v___x_4948_;
goto v___jp_4933_;
}
}
}
}
case 1:
{
lean_object* v_node_4951_; lean_object* v___x_4953_; uint8_t v_isShared_4954_; uint8_t v_isSharedCheck_4963_; 
v_node_4951_ = lean_ctor_get(v_v_4930_, 0);
v_isSharedCheck_4963_ = !lean_is_exclusive(v_v_4930_);
if (v_isSharedCheck_4963_ == 0)
{
v___x_4953_ = v_v_4930_;
v_isShared_4954_ = v_isSharedCheck_4963_;
goto v_resetjp_4952_;
}
else
{
lean_inc(v_node_4951_);
lean_dec(v_v_4930_);
v___x_4953_ = lean_box(0);
v_isShared_4954_ = v_isSharedCheck_4963_;
goto v_resetjp_4952_;
}
v_resetjp_4952_:
{
size_t v___x_4955_; size_t v___x_4956_; size_t v___x_4957_; size_t v___x_4958_; lean_object* v___x_4959_; lean_object* v___x_4961_; 
v___x_4955_ = ((size_t)5ULL);
v___x_4956_ = lean_usize_shift_right(v_x_4917_, v___x_4955_);
v___x_4957_ = ((size_t)1ULL);
v___x_4958_ = lean_usize_add(v_x_4918_, v___x_4957_);
v___x_4959_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg(v_node_4951_, v___x_4956_, v___x_4958_, v_x_4919_, v_x_4920_);
if (v_isShared_4954_ == 0)
{
lean_ctor_set(v___x_4953_, 0, v___x_4959_);
v___x_4961_ = v___x_4953_;
goto v_reusejp_4960_;
}
else
{
lean_object* v_reuseFailAlloc_4962_; 
v_reuseFailAlloc_4962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4962_, 0, v___x_4959_);
v___x_4961_ = v_reuseFailAlloc_4962_;
goto v_reusejp_4960_;
}
v_reusejp_4960_:
{
v___y_4934_ = v___x_4961_;
goto v___jp_4933_;
}
}
}
default: 
{
lean_object* v___x_4964_; 
v___x_4964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4964_, 0, v_x_4919_);
lean_ctor_set(v___x_4964_, 1, v_x_4920_);
v___y_4934_ = v___x_4964_;
goto v___jp_4933_;
}
}
v___jp_4933_:
{
lean_object* v___x_4935_; lean_object* v___x_4937_; 
v___x_4935_ = lean_array_fset(v_xs_x27_4932_, v_j_4924_, v___y_4934_);
lean_dec(v_j_4924_);
if (v_isShared_4929_ == 0)
{
lean_ctor_set(v___x_4928_, 0, v___x_4935_);
v___x_4937_ = v___x_4928_;
goto v_reusejp_4936_;
}
else
{
lean_object* v_reuseFailAlloc_4938_; 
v_reuseFailAlloc_4938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4938_, 0, v___x_4935_);
v___x_4937_ = v_reuseFailAlloc_4938_;
goto v_reusejp_4936_;
}
v_reusejp_4936_:
{
return v___x_4937_;
}
}
}
}
}
else
{
lean_object* v_ks_4967_; lean_object* v_vs_4968_; lean_object* v___x_4970_; uint8_t v_isShared_4971_; uint8_t v_isSharedCheck_4988_; 
v_ks_4967_ = lean_ctor_get(v_x_4916_, 0);
v_vs_4968_ = lean_ctor_get(v_x_4916_, 1);
v_isSharedCheck_4988_ = !lean_is_exclusive(v_x_4916_);
if (v_isSharedCheck_4988_ == 0)
{
v___x_4970_ = v_x_4916_;
v_isShared_4971_ = v_isSharedCheck_4988_;
goto v_resetjp_4969_;
}
else
{
lean_inc(v_vs_4968_);
lean_inc(v_ks_4967_);
lean_dec(v_x_4916_);
v___x_4970_ = lean_box(0);
v_isShared_4971_ = v_isSharedCheck_4988_;
goto v_resetjp_4969_;
}
v_resetjp_4969_:
{
lean_object* v___x_4973_; 
if (v_isShared_4971_ == 0)
{
v___x_4973_ = v___x_4970_;
goto v_reusejp_4972_;
}
else
{
lean_object* v_reuseFailAlloc_4987_; 
v_reuseFailAlloc_4987_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4987_, 0, v_ks_4967_);
lean_ctor_set(v_reuseFailAlloc_4987_, 1, v_vs_4968_);
v___x_4973_ = v_reuseFailAlloc_4987_;
goto v_reusejp_4972_;
}
v_reusejp_4972_:
{
lean_object* v_newNode_4974_; uint8_t v___y_4976_; size_t v___x_4982_; uint8_t v___x_4983_; 
v_newNode_4974_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__7___redArg(v___x_4973_, v_x_4919_, v_x_4920_);
v___x_4982_ = ((size_t)7ULL);
v___x_4983_ = lean_usize_dec_le(v___x_4982_, v_x_4918_);
if (v___x_4983_ == 0)
{
lean_object* v___x_4984_; lean_object* v___x_4985_; uint8_t v___x_4986_; 
v___x_4984_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4974_);
v___x_4985_ = lean_unsigned_to_nat(4u);
v___x_4986_ = lean_nat_dec_lt(v___x_4984_, v___x_4985_);
lean_dec(v___x_4984_);
v___y_4976_ = v___x_4986_;
goto v___jp_4975_;
}
else
{
v___y_4976_ = v___x_4983_;
goto v___jp_4975_;
}
v___jp_4975_:
{
if (v___y_4976_ == 0)
{
lean_object* v_ks_4977_; lean_object* v_vs_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; 
v_ks_4977_ = lean_ctor_get(v_newNode_4974_, 0);
lean_inc_ref(v_ks_4977_);
v_vs_4978_ = lean_ctor_get(v_newNode_4974_, 1);
lean_inc_ref(v_vs_4978_);
lean_dec_ref(v_newNode_4974_);
v___x_4979_ = lean_unsigned_to_nat(0u);
v___x_4980_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg___closed__0);
v___x_4981_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__8___redArg(v_x_4918_, v_ks_4977_, v_vs_4978_, v___x_4979_, v___x_4980_);
lean_dec_ref(v_vs_4978_);
lean_dec_ref(v_ks_4977_);
return v___x_4981_;
}
else
{
return v_newNode_4974_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__8___redArg(size_t v_depth_4989_, lean_object* v_keys_4990_, lean_object* v_vals_4991_, lean_object* v_i_4992_, lean_object* v_entries_4993_){
_start:
{
lean_object* v___x_4994_; uint8_t v___x_4995_; 
v___x_4994_ = lean_array_get_size(v_keys_4990_);
v___x_4995_ = lean_nat_dec_lt(v_i_4992_, v___x_4994_);
if (v___x_4995_ == 0)
{
lean_dec(v_i_4992_);
return v_entries_4993_;
}
else
{
lean_object* v_k_4996_; lean_object* v_v_4997_; uint64_t v___x_4998_; size_t v_h_4999_; size_t v___x_5000_; lean_object* v___x_5001_; size_t v___x_5002_; size_t v___x_5003_; size_t v___x_5004_; size_t v_h_5005_; lean_object* v___x_5006_; lean_object* v___x_5007_; 
v_k_4996_ = lean_array_fget_borrowed(v_keys_4990_, v_i_4992_);
v_v_4997_ = lean_array_fget_borrowed(v_vals_4991_, v_i_4992_);
v___x_4998_ = l_Lean_instHashableMVarId_hash(v_k_4996_);
v_h_4999_ = lean_uint64_to_usize(v___x_4998_);
v___x_5000_ = ((size_t)5ULL);
v___x_5001_ = lean_unsigned_to_nat(1u);
v___x_5002_ = ((size_t)1ULL);
v___x_5003_ = lean_usize_sub(v_depth_4989_, v___x_5002_);
v___x_5004_ = lean_usize_mul(v___x_5000_, v___x_5003_);
v_h_5005_ = lean_usize_shift_right(v_h_4999_, v___x_5004_);
v___x_5006_ = lean_nat_add(v_i_4992_, v___x_5001_);
lean_dec(v_i_4992_);
lean_inc(v_v_4997_);
lean_inc(v_k_4996_);
v___x_5007_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg(v_entries_4993_, v_h_5005_, v_depth_4989_, v_k_4996_, v_v_4997_);
v_i_4992_ = v___x_5006_;
v_entries_4993_ = v___x_5007_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__8___redArg___boxed(lean_object* v_depth_5009_, lean_object* v_keys_5010_, lean_object* v_vals_5011_, lean_object* v_i_5012_, lean_object* v_entries_5013_){
_start:
{
size_t v_depth_boxed_5014_; lean_object* v_res_5015_; 
v_depth_boxed_5014_ = lean_unbox_usize(v_depth_5009_);
lean_dec(v_depth_5009_);
v_res_5015_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__8___redArg(v_depth_boxed_5014_, v_keys_5010_, v_vals_5011_, v_i_5012_, v_entries_5013_);
lean_dec_ref(v_vals_5011_);
lean_dec_ref(v_keys_5010_);
return v_res_5015_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_x_5016_, lean_object* v_x_5017_, lean_object* v_x_5018_, lean_object* v_x_5019_, lean_object* v_x_5020_){
_start:
{
size_t v_x_48522__boxed_5021_; size_t v_x_48523__boxed_5022_; lean_object* v_res_5023_; 
v_x_48522__boxed_5021_ = lean_unbox_usize(v_x_5017_);
lean_dec(v_x_5017_);
v_x_48523__boxed_5022_ = lean_unbox_usize(v_x_5018_);
lean_dec(v_x_5018_);
v_res_5023_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg(v_x_5016_, v_x_48522__boxed_5021_, v_x_48523__boxed_5022_, v_x_5019_, v_x_5020_);
return v_res_5023_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0___redArg(lean_object* v_x_5024_, lean_object* v_x_5025_, lean_object* v_x_5026_){
_start:
{
uint64_t v___x_5027_; size_t v___x_5028_; size_t v___x_5029_; lean_object* v___x_5030_; 
v___x_5027_ = l_Lean_instHashableMVarId_hash(v_x_5025_);
v___x_5028_ = lean_uint64_to_usize(v___x_5027_);
v___x_5029_ = ((size_t)1ULL);
v___x_5030_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg(v_x_5024_, v___x_5028_, v___x_5029_, v_x_5025_, v_x_5026_);
return v___x_5030_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___redArg(lean_object* v_mvarId_5031_, lean_object* v_val_5032_, lean_object* v___y_5033_){
_start:
{
lean_object* v___x_5035_; lean_object* v_mctx_5036_; lean_object* v_cache_5037_; lean_object* v_zetaDeltaFVarIds_5038_; lean_object* v_postponed_5039_; lean_object* v_diag_5040_; lean_object* v___x_5042_; uint8_t v_isShared_5043_; uint8_t v_isSharedCheck_5068_; 
v___x_5035_ = lean_st_ref_take(v___y_5033_);
v_mctx_5036_ = lean_ctor_get(v___x_5035_, 0);
v_cache_5037_ = lean_ctor_get(v___x_5035_, 1);
v_zetaDeltaFVarIds_5038_ = lean_ctor_get(v___x_5035_, 2);
v_postponed_5039_ = lean_ctor_get(v___x_5035_, 3);
v_diag_5040_ = lean_ctor_get(v___x_5035_, 4);
v_isSharedCheck_5068_ = !lean_is_exclusive(v___x_5035_);
if (v_isSharedCheck_5068_ == 0)
{
v___x_5042_ = v___x_5035_;
v_isShared_5043_ = v_isSharedCheck_5068_;
goto v_resetjp_5041_;
}
else
{
lean_inc(v_diag_5040_);
lean_inc(v_postponed_5039_);
lean_inc(v_zetaDeltaFVarIds_5038_);
lean_inc(v_cache_5037_);
lean_inc(v_mctx_5036_);
lean_dec(v___x_5035_);
v___x_5042_ = lean_box(0);
v_isShared_5043_ = v_isSharedCheck_5068_;
goto v_resetjp_5041_;
}
v_resetjp_5041_:
{
lean_object* v_depth_5044_; lean_object* v_levelAssignDepth_5045_; lean_object* v_lmvarCounter_5046_; lean_object* v_mvarCounter_5047_; lean_object* v_lDecls_5048_; lean_object* v_decls_5049_; lean_object* v_userNames_5050_; lean_object* v_lAssignment_5051_; lean_object* v_eAssignment_5052_; lean_object* v_dAssignment_5053_; lean_object* v___x_5055_; uint8_t v_isShared_5056_; uint8_t v_isSharedCheck_5067_; 
v_depth_5044_ = lean_ctor_get(v_mctx_5036_, 0);
v_levelAssignDepth_5045_ = lean_ctor_get(v_mctx_5036_, 1);
v_lmvarCounter_5046_ = lean_ctor_get(v_mctx_5036_, 2);
v_mvarCounter_5047_ = lean_ctor_get(v_mctx_5036_, 3);
v_lDecls_5048_ = lean_ctor_get(v_mctx_5036_, 4);
v_decls_5049_ = lean_ctor_get(v_mctx_5036_, 5);
v_userNames_5050_ = lean_ctor_get(v_mctx_5036_, 6);
v_lAssignment_5051_ = lean_ctor_get(v_mctx_5036_, 7);
v_eAssignment_5052_ = lean_ctor_get(v_mctx_5036_, 8);
v_dAssignment_5053_ = lean_ctor_get(v_mctx_5036_, 9);
v_isSharedCheck_5067_ = !lean_is_exclusive(v_mctx_5036_);
if (v_isSharedCheck_5067_ == 0)
{
v___x_5055_ = v_mctx_5036_;
v_isShared_5056_ = v_isSharedCheck_5067_;
goto v_resetjp_5054_;
}
else
{
lean_inc(v_dAssignment_5053_);
lean_inc(v_eAssignment_5052_);
lean_inc(v_lAssignment_5051_);
lean_inc(v_userNames_5050_);
lean_inc(v_decls_5049_);
lean_inc(v_lDecls_5048_);
lean_inc(v_mvarCounter_5047_);
lean_inc(v_lmvarCounter_5046_);
lean_inc(v_levelAssignDepth_5045_);
lean_inc(v_depth_5044_);
lean_dec(v_mctx_5036_);
v___x_5055_ = lean_box(0);
v_isShared_5056_ = v_isSharedCheck_5067_;
goto v_resetjp_5054_;
}
v_resetjp_5054_:
{
lean_object* v___x_5057_; lean_object* v___x_5059_; 
v___x_5057_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0___redArg(v_eAssignment_5052_, v_mvarId_5031_, v_val_5032_);
if (v_isShared_5056_ == 0)
{
lean_ctor_set(v___x_5055_, 8, v___x_5057_);
v___x_5059_ = v___x_5055_;
goto v_reusejp_5058_;
}
else
{
lean_object* v_reuseFailAlloc_5066_; 
v_reuseFailAlloc_5066_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5066_, 0, v_depth_5044_);
lean_ctor_set(v_reuseFailAlloc_5066_, 1, v_levelAssignDepth_5045_);
lean_ctor_set(v_reuseFailAlloc_5066_, 2, v_lmvarCounter_5046_);
lean_ctor_set(v_reuseFailAlloc_5066_, 3, v_mvarCounter_5047_);
lean_ctor_set(v_reuseFailAlloc_5066_, 4, v_lDecls_5048_);
lean_ctor_set(v_reuseFailAlloc_5066_, 5, v_decls_5049_);
lean_ctor_set(v_reuseFailAlloc_5066_, 6, v_userNames_5050_);
lean_ctor_set(v_reuseFailAlloc_5066_, 7, v_lAssignment_5051_);
lean_ctor_set(v_reuseFailAlloc_5066_, 8, v___x_5057_);
lean_ctor_set(v_reuseFailAlloc_5066_, 9, v_dAssignment_5053_);
v___x_5059_ = v_reuseFailAlloc_5066_;
goto v_reusejp_5058_;
}
v_reusejp_5058_:
{
lean_object* v___x_5061_; 
if (v_isShared_5043_ == 0)
{
lean_ctor_set(v___x_5042_, 0, v___x_5059_);
v___x_5061_ = v___x_5042_;
goto v_reusejp_5060_;
}
else
{
lean_object* v_reuseFailAlloc_5065_; 
v_reuseFailAlloc_5065_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5065_, 0, v___x_5059_);
lean_ctor_set(v_reuseFailAlloc_5065_, 1, v_cache_5037_);
lean_ctor_set(v_reuseFailAlloc_5065_, 2, v_zetaDeltaFVarIds_5038_);
lean_ctor_set(v_reuseFailAlloc_5065_, 3, v_postponed_5039_);
lean_ctor_set(v_reuseFailAlloc_5065_, 4, v_diag_5040_);
v___x_5061_ = v_reuseFailAlloc_5065_;
goto v_reusejp_5060_;
}
v_reusejp_5060_:
{
lean_object* v___x_5062_; lean_object* v___x_5063_; lean_object* v___x_5064_; 
v___x_5062_ = lean_st_ref_set(v___y_5033_, v___x_5061_);
v___x_5063_ = lean_box(0);
v___x_5064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5064_, 0, v___x_5063_);
return v___x_5064_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___redArg___boxed(lean_object* v_mvarId_5069_, lean_object* v_val_5070_, lean_object* v___y_5071_, lean_object* v___y_5072_){
_start:
{
lean_object* v_res_5073_; 
v_res_5073_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___redArg(v_mvarId_5069_, v_val_5070_, v___y_5071_);
lean_dec(v___y_5071_);
return v_res_5073_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3(lean_object* v_mvarId_5081_, lean_object* v_config_5082_, lean_object* v_as_5083_, size_t v_sz_5084_, size_t v_i_5085_, lean_object* v_b_5086_, lean_object* v___y_5087_, lean_object* v___y_5088_, lean_object* v___y_5089_, lean_object* v___y_5090_, lean_object* v___y_5091_, lean_object* v___y_5092_){
_start:
{
lean_object* v_a_5095_; uint8_t v___x_5099_; 
v___x_5099_ = lean_usize_dec_lt(v_i_5085_, v_sz_5084_);
if (v___x_5099_ == 0)
{
lean_object* v___x_5100_; 
lean_dec_ref(v_config_5082_);
lean_dec(v_mvarId_5081_);
v___x_5100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5100_, 0, v_b_5086_);
return v___x_5100_;
}
else
{
lean_object* v_a_5101_; lean_object* v___x_5102_; 
v_a_5101_ = lean_array_uget_borrowed(v_as_5083_, v_i_5085_);
lean_inc(v_a_5101_);
v___x_5102_ = l_Lean_FVarId_getDecl___redArg(v_a_5101_, v___y_5089_, v___y_5091_, v___y_5092_);
if (lean_obj_tag(v___x_5102_) == 0)
{
lean_object* v_options_5103_; lean_object* v_a_5104_; lean_object* v_snd_5105_; lean_object* v___x_5107_; uint8_t v_isShared_5108_; uint8_t v_isSharedCheck_5296_; 
v_options_5103_ = lean_ctor_get(v___y_5091_, 2);
v_a_5104_ = lean_ctor_get(v___x_5102_, 0);
lean_inc(v_a_5104_);
lean_dec_ref_known(v___x_5102_, 1);
v_snd_5105_ = lean_ctor_get(v_b_5086_, 1);
v_isSharedCheck_5296_ = !lean_is_exclusive(v_b_5086_);
if (v_isSharedCheck_5296_ == 0)
{
lean_object* v_unused_5297_; 
v_unused_5297_ = lean_ctor_get(v_b_5086_, 0);
lean_dec(v_unused_5297_);
v___x_5107_ = v_b_5086_;
v_isShared_5108_ = v_isSharedCheck_5296_;
goto v_resetjp_5106_;
}
else
{
lean_inc(v_snd_5105_);
lean_dec(v_b_5086_);
v___x_5107_ = lean_box(0);
v_isShared_5108_ = v_isSharedCheck_5296_;
goto v_resetjp_5106_;
}
v_resetjp_5106_:
{
lean_object* v_inheritedTraceOptions_5109_; uint8_t v_hasTrace_5110_; lean_object* v___x_5111_; lean_object* v___x_5112_; lean_object* v___y_5114_; 
v_inheritedTraceOptions_5109_ = lean_ctor_get(v___y_5091_, 13);
v_hasTrace_5110_ = lean_ctor_get_uint8(v_options_5103_, sizeof(void*)*1);
v___x_5111_ = lean_box(0);
v___x_5112_ = l_Lean_LocalDecl_type(v_a_5104_);
if (v_hasTrace_5110_ == 0)
{
lean_object* v___x_5211_; 
lean_inc_ref(v_config_5082_);
lean_inc_ref(v___x_5112_);
v___x_5211_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_5112_, v_config_5082_, v___y_5087_, v___y_5088_, v___y_5089_, v___y_5090_, v___y_5091_, v___y_5092_);
v___y_5114_ = v___x_5211_;
goto v___jp_5113_;
}
else
{
lean_object* v___f_5212_; lean_object* v___x_5213_; lean_object* v___x_5214_; lean_object* v___x_5215_; uint8_t v___x_5216_; lean_object* v___y_5218_; lean_object* v___y_5219_; lean_object* v_a_5220_; lean_object* v___y_5233_; lean_object* v___y_5234_; lean_object* v_a_5235_; 
lean_inc_ref(v___x_5112_);
lean_inc(v_a_5104_);
v___f_5212_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___boxed), 10, 2);
lean_closure_set(v___f_5212_, 0, v_a_5104_);
lean_closure_set(v___f_5212_, 1, v___x_5112_);
v___x_5213_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0));
v___x_5214_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__1));
v___x_5215_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1);
v___x_5216_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5109_, v_options_5103_, v___x_5215_);
if (v___x_5216_ == 0)
{
lean_object* v___x_5293_; uint8_t v___x_5294_; 
v___x_5293_ = l_Lean_trace_profiler;
v___x_5294_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_5103_, v___x_5293_);
if (v___x_5294_ == 0)
{
lean_object* v___x_5295_; 
lean_dec_ref(v___f_5212_);
lean_inc_ref(v_config_5082_);
lean_inc_ref(v___x_5112_);
v___x_5295_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_5112_, v_config_5082_, v___y_5087_, v___y_5088_, v___y_5089_, v___y_5090_, v___y_5091_, v___y_5092_);
v___y_5114_ = v___x_5295_;
goto v___jp_5113_;
}
else
{
goto v___jp_5244_;
}
}
else
{
goto v___jp_5244_;
}
v___jp_5217_:
{
lean_object* v___x_5221_; double v___x_5222_; double v___x_5223_; double v___x_5224_; double v___x_5225_; double v___x_5226_; lean_object* v___x_5227_; lean_object* v___x_5228_; lean_object* v___x_5229_; lean_object* v___x_5230_; lean_object* v___x_5231_; 
v___x_5221_ = lean_io_mono_nanos_now();
v___x_5222_ = lean_float_of_nat(v___y_5219_);
v___x_5223_ = lean_float_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9);
v___x_5224_ = lean_float_div(v___x_5222_, v___x_5223_);
v___x_5225_ = lean_float_of_nat(v___x_5221_);
v___x_5226_ = lean_float_div(v___x_5225_, v___x_5223_);
v___x_5227_ = lean_box_float(v___x_5224_);
v___x_5228_ = lean_box_float(v___x_5226_);
v___x_5229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5229_, 0, v___x_5227_);
lean_ctor_set(v___x_5229_, 1, v___x_5228_);
v___x_5230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5230_, 0, v_a_5220_);
lean_ctor_set(v___x_5230_, 1, v___x_5229_);
v___x_5231_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2(v___x_5213_, v_hasTrace_5110_, v___x_5214_, v_options_5103_, v___x_5216_, v___y_5218_, v___f_5212_, v___x_5230_, v___y_5087_, v___y_5088_, v___y_5089_, v___y_5090_, v___y_5091_, v___y_5092_);
v___y_5114_ = v___x_5231_;
goto v___jp_5113_;
}
v___jp_5232_:
{
lean_object* v___x_5236_; double v___x_5237_; double v___x_5238_; lean_object* v___x_5239_; lean_object* v___x_5240_; lean_object* v___x_5241_; lean_object* v___x_5242_; lean_object* v___x_5243_; 
v___x_5236_ = lean_io_get_num_heartbeats();
v___x_5237_ = lean_float_of_nat(v___y_5234_);
v___x_5238_ = lean_float_of_nat(v___x_5236_);
v___x_5239_ = lean_box_float(v___x_5237_);
v___x_5240_ = lean_box_float(v___x_5238_);
v___x_5241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5241_, 0, v___x_5239_);
lean_ctor_set(v___x_5241_, 1, v___x_5240_);
v___x_5242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5242_, 0, v_a_5235_);
lean_ctor_set(v___x_5242_, 1, v___x_5241_);
v___x_5243_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2(v___x_5213_, v_hasTrace_5110_, v___x_5214_, v_options_5103_, v___x_5216_, v___y_5233_, v___f_5212_, v___x_5242_, v___y_5087_, v___y_5088_, v___y_5089_, v___y_5090_, v___y_5091_, v___y_5092_);
v___y_5114_ = v___x_5243_;
goto v___jp_5113_;
}
v___jp_5244_:
{
lean_object* v___x_5245_; 
v___x_5245_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1___redArg(v___y_5092_);
if (lean_obj_tag(v___x_5245_) == 0)
{
lean_object* v_a_5246_; lean_object* v___x_5247_; uint8_t v___x_5248_; 
v_a_5246_ = lean_ctor_get(v___x_5245_, 0);
lean_inc(v_a_5246_);
lean_dec_ref_known(v___x_5245_, 1);
v___x_5247_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5248_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_5103_, v___x_5247_);
if (v___x_5248_ == 0)
{
lean_object* v___x_5249_; lean_object* v___x_5250_; 
v___x_5249_ = lean_io_mono_nanos_now();
lean_inc_ref(v_config_5082_);
lean_inc_ref(v___x_5112_);
v___x_5250_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_5112_, v_config_5082_, v___y_5087_, v___y_5088_, v___y_5089_, v___y_5090_, v___y_5091_, v___y_5092_);
if (lean_obj_tag(v___x_5250_) == 0)
{
lean_object* v_a_5251_; lean_object* v___x_5253_; uint8_t v_isShared_5254_; uint8_t v_isSharedCheck_5258_; 
v_a_5251_ = lean_ctor_get(v___x_5250_, 0);
v_isSharedCheck_5258_ = !lean_is_exclusive(v___x_5250_);
if (v_isSharedCheck_5258_ == 0)
{
v___x_5253_ = v___x_5250_;
v_isShared_5254_ = v_isSharedCheck_5258_;
goto v_resetjp_5252_;
}
else
{
lean_inc(v_a_5251_);
lean_dec(v___x_5250_);
v___x_5253_ = lean_box(0);
v_isShared_5254_ = v_isSharedCheck_5258_;
goto v_resetjp_5252_;
}
v_resetjp_5252_:
{
lean_object* v___x_5256_; 
if (v_isShared_5254_ == 0)
{
lean_ctor_set_tag(v___x_5253_, 1);
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
v___y_5218_ = v_a_5246_;
v___y_5219_ = v___x_5249_;
v_a_5220_ = v___x_5256_;
goto v___jp_5217_;
}
}
}
else
{
lean_object* v_a_5259_; lean_object* v___x_5261_; uint8_t v_isShared_5262_; uint8_t v_isSharedCheck_5266_; 
v_a_5259_ = lean_ctor_get(v___x_5250_, 0);
v_isSharedCheck_5266_ = !lean_is_exclusive(v___x_5250_);
if (v_isSharedCheck_5266_ == 0)
{
v___x_5261_ = v___x_5250_;
v_isShared_5262_ = v_isSharedCheck_5266_;
goto v_resetjp_5260_;
}
else
{
lean_inc(v_a_5259_);
lean_dec(v___x_5250_);
v___x_5261_ = lean_box(0);
v_isShared_5262_ = v_isSharedCheck_5266_;
goto v_resetjp_5260_;
}
v_resetjp_5260_:
{
lean_object* v___x_5264_; 
if (v_isShared_5262_ == 0)
{
lean_ctor_set_tag(v___x_5261_, 0);
v___x_5264_ = v___x_5261_;
goto v_reusejp_5263_;
}
else
{
lean_object* v_reuseFailAlloc_5265_; 
v_reuseFailAlloc_5265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5265_, 0, v_a_5259_);
v___x_5264_ = v_reuseFailAlloc_5265_;
goto v_reusejp_5263_;
}
v_reusejp_5263_:
{
v___y_5218_ = v_a_5246_;
v___y_5219_ = v___x_5249_;
v_a_5220_ = v___x_5264_;
goto v___jp_5217_;
}
}
}
}
else
{
lean_object* v___x_5267_; lean_object* v___x_5268_; 
v___x_5267_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_config_5082_);
lean_inc_ref(v___x_5112_);
v___x_5268_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_5112_, v_config_5082_, v___y_5087_, v___y_5088_, v___y_5089_, v___y_5090_, v___y_5091_, v___y_5092_);
if (lean_obj_tag(v___x_5268_) == 0)
{
lean_object* v_a_5269_; lean_object* v___x_5271_; uint8_t v_isShared_5272_; uint8_t v_isSharedCheck_5276_; 
v_a_5269_ = lean_ctor_get(v___x_5268_, 0);
v_isSharedCheck_5276_ = !lean_is_exclusive(v___x_5268_);
if (v_isSharedCheck_5276_ == 0)
{
v___x_5271_ = v___x_5268_;
v_isShared_5272_ = v_isSharedCheck_5276_;
goto v_resetjp_5270_;
}
else
{
lean_inc(v_a_5269_);
lean_dec(v___x_5268_);
v___x_5271_ = lean_box(0);
v_isShared_5272_ = v_isSharedCheck_5276_;
goto v_resetjp_5270_;
}
v_resetjp_5270_:
{
lean_object* v___x_5274_; 
if (v_isShared_5272_ == 0)
{
lean_ctor_set_tag(v___x_5271_, 1);
v___x_5274_ = v___x_5271_;
goto v_reusejp_5273_;
}
else
{
lean_object* v_reuseFailAlloc_5275_; 
v_reuseFailAlloc_5275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5275_, 0, v_a_5269_);
v___x_5274_ = v_reuseFailAlloc_5275_;
goto v_reusejp_5273_;
}
v_reusejp_5273_:
{
v___y_5233_ = v_a_5246_;
v___y_5234_ = v___x_5267_;
v_a_5235_ = v___x_5274_;
goto v___jp_5232_;
}
}
}
else
{
lean_object* v_a_5277_; lean_object* v___x_5279_; uint8_t v_isShared_5280_; uint8_t v_isSharedCheck_5284_; 
v_a_5277_ = lean_ctor_get(v___x_5268_, 0);
v_isSharedCheck_5284_ = !lean_is_exclusive(v___x_5268_);
if (v_isSharedCheck_5284_ == 0)
{
v___x_5279_ = v___x_5268_;
v_isShared_5280_ = v_isSharedCheck_5284_;
goto v_resetjp_5278_;
}
else
{
lean_inc(v_a_5277_);
lean_dec(v___x_5268_);
v___x_5279_ = lean_box(0);
v_isShared_5280_ = v_isSharedCheck_5284_;
goto v_resetjp_5278_;
}
v_resetjp_5278_:
{
lean_object* v___x_5282_; 
if (v_isShared_5280_ == 0)
{
lean_ctor_set_tag(v___x_5279_, 0);
v___x_5282_ = v___x_5279_;
goto v_reusejp_5281_;
}
else
{
lean_object* v_reuseFailAlloc_5283_; 
v_reuseFailAlloc_5283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5283_, 0, v_a_5277_);
v___x_5282_ = v_reuseFailAlloc_5283_;
goto v_reusejp_5281_;
}
v_reusejp_5281_:
{
v___y_5233_ = v_a_5246_;
v___y_5234_ = v___x_5267_;
v_a_5235_ = v___x_5282_;
goto v___jp_5232_;
}
}
}
}
}
else
{
lean_object* v_a_5285_; lean_object* v___x_5287_; uint8_t v_isShared_5288_; uint8_t v_isSharedCheck_5292_; 
lean_dec_ref(v___f_5212_);
lean_dec_ref(v___x_5112_);
lean_del_object(v___x_5107_);
lean_dec(v_snd_5105_);
lean_dec(v_a_5104_);
lean_dec_ref(v_config_5082_);
lean_dec(v_mvarId_5081_);
v_a_5285_ = lean_ctor_get(v___x_5245_, 0);
v_isSharedCheck_5292_ = !lean_is_exclusive(v___x_5245_);
if (v_isSharedCheck_5292_ == 0)
{
v___x_5287_ = v___x_5245_;
v_isShared_5288_ = v_isSharedCheck_5292_;
goto v_resetjp_5286_;
}
else
{
lean_inc(v_a_5285_);
lean_dec(v___x_5245_);
v___x_5287_ = lean_box(0);
v_isShared_5288_ = v_isSharedCheck_5292_;
goto v_resetjp_5286_;
}
v_resetjp_5286_:
{
lean_object* v___x_5290_; 
if (v_isShared_5288_ == 0)
{
v___x_5290_ = v___x_5287_;
goto v_reusejp_5289_;
}
else
{
lean_object* v_reuseFailAlloc_5291_; 
v_reuseFailAlloc_5291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5291_, 0, v_a_5285_);
v___x_5290_ = v_reuseFailAlloc_5291_;
goto v_reusejp_5289_;
}
v_reusejp_5289_:
{
return v___x_5290_;
}
}
}
}
}
v___jp_5113_:
{
if (lean_obj_tag(v___y_5114_) == 0)
{
lean_object* v_a_5115_; 
v_a_5115_ = lean_ctor_get(v___y_5114_, 0);
lean_inc(v_a_5115_);
lean_dec_ref_known(v___y_5114_, 1);
if (lean_obj_tag(v_a_5115_) == 0)
{
lean_object* v___x_5117_; 
lean_dec_ref_known(v_a_5115_, 0);
lean_dec_ref(v___x_5112_);
lean_dec(v_a_5104_);
if (v_isShared_5108_ == 0)
{
lean_ctor_set(v___x_5107_, 0, v___x_5111_);
v___x_5117_ = v___x_5107_;
goto v_reusejp_5116_;
}
else
{
lean_object* v_reuseFailAlloc_5118_; 
v_reuseFailAlloc_5118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5118_, 0, v___x_5111_);
lean_ctor_set(v_reuseFailAlloc_5118_, 1, v_snd_5105_);
v___x_5117_ = v_reuseFailAlloc_5118_;
goto v_reusejp_5116_;
}
v_reusejp_5116_:
{
v_a_5095_ = v___x_5117_;
goto v___jp_5094_;
}
}
else
{
lean_object* v_e_x27_5119_; lean_object* v_proof_5120_; uint8_t v___x_5121_; 
v_e_x27_5119_ = lean_ctor_get(v_a_5115_, 0);
lean_inc_ref_n(v_e_x27_5119_, 2);
v_proof_5120_ = lean_ctor_get(v_a_5115_, 1);
lean_inc_ref(v_proof_5120_);
lean_dec_ref_known(v_a_5115_, 2);
v___x_5121_ = l_Lean_Expr_isFalse(v_e_x27_5119_);
if (v___x_5121_ == 0)
{
lean_object* v___x_5122_; 
lean_inc_ref(v___x_5112_);
v___x_5122_ = l_Lean_Meta_Sym_getLevel___redArg(v___x_5112_, v___y_5088_, v___y_5089_, v___y_5090_, v___y_5091_, v___y_5092_);
if (lean_obj_tag(v___x_5122_) == 0)
{
lean_object* v_a_5123_; lean_object* v___x_5124_; lean_object* v___x_5125_; lean_object* v___x_5126_; lean_object* v___x_5127_; lean_object* v___x_5128_; lean_object* v___x_5129_; lean_object* v___x_5130_; uint8_t v___x_5131_; uint8_t v___x_5132_; lean_object* v___x_5133_; lean_object* v___x_5134_; lean_object* v___x_5136_; 
v_a_5123_ = lean_ctor_get(v___x_5122_, 0);
lean_inc(v_a_5123_);
lean_dec_ref_known(v___x_5122_, 1);
v___x_5124_ = l_Lean_LocalDecl_userName(v_a_5104_);
lean_dec(v_a_5104_);
v___x_5125_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___closed__2));
v___x_5126_ = lean_box(0);
v___x_5127_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5127_, 0, v_a_5123_);
lean_ctor_set(v___x_5127_, 1, v___x_5126_);
v___x_5128_ = l_Lean_mkConst(v___x_5125_, v___x_5127_);
lean_inc(v_a_5101_);
v___x_5129_ = l_Lean_mkFVar(v_a_5101_);
lean_inc_ref(v_e_x27_5119_);
v___x_5130_ = l_Lean_mkApp4(v___x_5128_, v___x_5112_, v_e_x27_5119_, v_proof_5120_, v___x_5129_);
v___x_5131_ = 0;
v___x_5132_ = 0;
v___x_5133_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5133_, 0, v___x_5124_);
lean_ctor_set(v___x_5133_, 1, v_e_x27_5119_);
lean_ctor_set(v___x_5133_, 2, v___x_5130_);
lean_ctor_set_uint8(v___x_5133_, sizeof(void*)*3, v___x_5131_);
lean_ctor_set_uint8(v___x_5133_, sizeof(void*)*3 + 1, v___x_5132_);
v___x_5134_ = lean_array_push(v_snd_5105_, v___x_5133_);
if (v_isShared_5108_ == 0)
{
lean_ctor_set(v___x_5107_, 1, v___x_5134_);
lean_ctor_set(v___x_5107_, 0, v___x_5111_);
v___x_5136_ = v___x_5107_;
goto v_reusejp_5135_;
}
else
{
lean_object* v_reuseFailAlloc_5137_; 
v_reuseFailAlloc_5137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5137_, 0, v___x_5111_);
lean_ctor_set(v_reuseFailAlloc_5137_, 1, v___x_5134_);
v___x_5136_ = v_reuseFailAlloc_5137_;
goto v_reusejp_5135_;
}
v_reusejp_5135_:
{
v_a_5095_ = v___x_5136_;
goto v___jp_5094_;
}
}
else
{
lean_object* v_a_5138_; lean_object* v___x_5140_; uint8_t v_isShared_5141_; uint8_t v_isSharedCheck_5145_; 
lean_dec_ref(v_proof_5120_);
lean_dec_ref(v_e_x27_5119_);
lean_dec_ref(v___x_5112_);
lean_del_object(v___x_5107_);
lean_dec(v_snd_5105_);
lean_dec(v_a_5104_);
lean_dec_ref(v_config_5082_);
lean_dec(v_mvarId_5081_);
v_a_5138_ = lean_ctor_get(v___x_5122_, 0);
v_isSharedCheck_5145_ = !lean_is_exclusive(v___x_5122_);
if (v_isSharedCheck_5145_ == 0)
{
v___x_5140_ = v___x_5122_;
v_isShared_5141_ = v_isSharedCheck_5145_;
goto v_resetjp_5139_;
}
else
{
lean_inc(v_a_5138_);
lean_dec(v___x_5122_);
v___x_5140_ = lean_box(0);
v_isShared_5141_ = v_isSharedCheck_5145_;
goto v_resetjp_5139_;
}
v_resetjp_5139_:
{
lean_object* v___x_5143_; 
if (v_isShared_5141_ == 0)
{
v___x_5143_ = v___x_5140_;
goto v_reusejp_5142_;
}
else
{
lean_object* v_reuseFailAlloc_5144_; 
v_reuseFailAlloc_5144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5144_, 0, v_a_5138_);
v___x_5143_ = v_reuseFailAlloc_5144_;
goto v_reusejp_5142_;
}
v_reusejp_5142_:
{
return v___x_5143_;
}
}
}
}
else
{
lean_object* v___x_5146_; 
lean_dec(v_a_5104_);
lean_dec_ref(v_config_5082_);
lean_inc_ref(v___x_5112_);
v___x_5146_ = l_Lean_Meta_Sym_getLevel___redArg(v___x_5112_, v___y_5088_, v___y_5089_, v___y_5090_, v___y_5091_, v___y_5092_);
if (lean_obj_tag(v___x_5146_) == 0)
{
lean_object* v_a_5147_; lean_object* v___x_5148_; 
v_a_5147_ = lean_ctor_get(v___x_5146_, 0);
lean_inc(v_a_5147_);
lean_dec_ref_known(v___x_5146_, 1);
lean_inc(v_mvarId_5081_);
v___x_5148_ = l_Lean_MVarId_getType(v_mvarId_5081_, v___y_5089_, v___y_5090_, v___y_5091_, v___y_5092_);
if (lean_obj_tag(v___x_5148_) == 0)
{
lean_object* v_a_5149_; lean_object* v___x_5150_; lean_object* v___x_5151_; lean_object* v___x_5152_; lean_object* v___x_5153_; lean_object* v___x_5154_; lean_object* v___x_5155_; lean_object* v___x_5156_; 
v_a_5149_ = lean_ctor_get(v___x_5148_, 0);
lean_inc(v_a_5149_);
lean_dec_ref_known(v___x_5148_, 1);
v___x_5150_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___closed__2));
v___x_5151_ = lean_box(0);
v___x_5152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5152_, 0, v_a_5147_);
lean_ctor_set(v___x_5152_, 1, v___x_5151_);
v___x_5153_ = l_Lean_mkConst(v___x_5150_, v___x_5152_);
lean_inc(v_a_5101_);
v___x_5154_ = l_Lean_mkFVar(v_a_5101_);
v___x_5155_ = l_Lean_mkApp4(v___x_5153_, v___x_5112_, v_e_x27_5119_, v_proof_5120_, v___x_5154_);
v___x_5156_ = l_Lean_Meta_mkFalseElim(v_a_5149_, v___x_5155_, v___y_5089_, v___y_5090_, v___y_5091_, v___y_5092_);
if (lean_obj_tag(v___x_5156_) == 0)
{
lean_object* v_a_5157_; lean_object* v___x_5158_; 
v_a_5157_ = lean_ctor_get(v___x_5156_, 0);
lean_inc(v_a_5157_);
lean_dec_ref_known(v___x_5156_, 1);
v___x_5158_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___redArg(v_mvarId_5081_, v_a_5157_, v___y_5090_);
if (lean_obj_tag(v___x_5158_) == 0)
{
lean_object* v___x_5160_; uint8_t v_isShared_5161_; uint8_t v_isSharedCheck_5169_; 
v_isSharedCheck_5169_ = !lean_is_exclusive(v___x_5158_);
if (v_isSharedCheck_5169_ == 0)
{
lean_object* v_unused_5170_; 
v_unused_5170_ = lean_ctor_get(v___x_5158_, 0);
lean_dec(v_unused_5170_);
v___x_5160_ = v___x_5158_;
v_isShared_5161_ = v_isSharedCheck_5169_;
goto v_resetjp_5159_;
}
else
{
lean_dec(v___x_5158_);
v___x_5160_ = lean_box(0);
v_isShared_5161_ = v_isSharedCheck_5169_;
goto v_resetjp_5159_;
}
v_resetjp_5159_:
{
lean_object* v___x_5162_; lean_object* v___x_5164_; 
v___x_5162_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___closed__3));
if (v_isShared_5108_ == 0)
{
lean_ctor_set(v___x_5107_, 0, v___x_5162_);
v___x_5164_ = v___x_5107_;
goto v_reusejp_5163_;
}
else
{
lean_object* v_reuseFailAlloc_5168_; 
v_reuseFailAlloc_5168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5168_, 0, v___x_5162_);
lean_ctor_set(v_reuseFailAlloc_5168_, 1, v_snd_5105_);
v___x_5164_ = v_reuseFailAlloc_5168_;
goto v_reusejp_5163_;
}
v_reusejp_5163_:
{
lean_object* v___x_5166_; 
if (v_isShared_5161_ == 0)
{
lean_ctor_set(v___x_5160_, 0, v___x_5164_);
v___x_5166_ = v___x_5160_;
goto v_reusejp_5165_;
}
else
{
lean_object* v_reuseFailAlloc_5167_; 
v_reuseFailAlloc_5167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5167_, 0, v___x_5164_);
v___x_5166_ = v_reuseFailAlloc_5167_;
goto v_reusejp_5165_;
}
v_reusejp_5165_:
{
return v___x_5166_;
}
}
}
}
else
{
lean_object* v_a_5171_; lean_object* v___x_5173_; uint8_t v_isShared_5174_; uint8_t v_isSharedCheck_5178_; 
lean_del_object(v___x_5107_);
lean_dec(v_snd_5105_);
v_a_5171_ = lean_ctor_get(v___x_5158_, 0);
v_isSharedCheck_5178_ = !lean_is_exclusive(v___x_5158_);
if (v_isSharedCheck_5178_ == 0)
{
v___x_5173_ = v___x_5158_;
v_isShared_5174_ = v_isSharedCheck_5178_;
goto v_resetjp_5172_;
}
else
{
lean_inc(v_a_5171_);
lean_dec(v___x_5158_);
v___x_5173_ = lean_box(0);
v_isShared_5174_ = v_isSharedCheck_5178_;
goto v_resetjp_5172_;
}
v_resetjp_5172_:
{
lean_object* v___x_5176_; 
if (v_isShared_5174_ == 0)
{
v___x_5176_ = v___x_5173_;
goto v_reusejp_5175_;
}
else
{
lean_object* v_reuseFailAlloc_5177_; 
v_reuseFailAlloc_5177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5177_, 0, v_a_5171_);
v___x_5176_ = v_reuseFailAlloc_5177_;
goto v_reusejp_5175_;
}
v_reusejp_5175_:
{
return v___x_5176_;
}
}
}
}
else
{
lean_object* v_a_5179_; lean_object* v___x_5181_; uint8_t v_isShared_5182_; uint8_t v_isSharedCheck_5186_; 
lean_del_object(v___x_5107_);
lean_dec(v_snd_5105_);
lean_dec(v_mvarId_5081_);
v_a_5179_ = lean_ctor_get(v___x_5156_, 0);
v_isSharedCheck_5186_ = !lean_is_exclusive(v___x_5156_);
if (v_isSharedCheck_5186_ == 0)
{
v___x_5181_ = v___x_5156_;
v_isShared_5182_ = v_isSharedCheck_5186_;
goto v_resetjp_5180_;
}
else
{
lean_inc(v_a_5179_);
lean_dec(v___x_5156_);
v___x_5181_ = lean_box(0);
v_isShared_5182_ = v_isSharedCheck_5186_;
goto v_resetjp_5180_;
}
v_resetjp_5180_:
{
lean_object* v___x_5184_; 
if (v_isShared_5182_ == 0)
{
v___x_5184_ = v___x_5181_;
goto v_reusejp_5183_;
}
else
{
lean_object* v_reuseFailAlloc_5185_; 
v_reuseFailAlloc_5185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5185_, 0, v_a_5179_);
v___x_5184_ = v_reuseFailAlloc_5185_;
goto v_reusejp_5183_;
}
v_reusejp_5183_:
{
return v___x_5184_;
}
}
}
}
else
{
lean_object* v_a_5187_; lean_object* v___x_5189_; uint8_t v_isShared_5190_; uint8_t v_isSharedCheck_5194_; 
lean_dec(v_a_5147_);
lean_dec_ref(v_proof_5120_);
lean_dec_ref(v_e_x27_5119_);
lean_dec_ref(v___x_5112_);
lean_del_object(v___x_5107_);
lean_dec(v_snd_5105_);
lean_dec(v_mvarId_5081_);
v_a_5187_ = lean_ctor_get(v___x_5148_, 0);
v_isSharedCheck_5194_ = !lean_is_exclusive(v___x_5148_);
if (v_isSharedCheck_5194_ == 0)
{
v___x_5189_ = v___x_5148_;
v_isShared_5190_ = v_isSharedCheck_5194_;
goto v_resetjp_5188_;
}
else
{
lean_inc(v_a_5187_);
lean_dec(v___x_5148_);
v___x_5189_ = lean_box(0);
v_isShared_5190_ = v_isSharedCheck_5194_;
goto v_resetjp_5188_;
}
v_resetjp_5188_:
{
lean_object* v___x_5192_; 
if (v_isShared_5190_ == 0)
{
v___x_5192_ = v___x_5189_;
goto v_reusejp_5191_;
}
else
{
lean_object* v_reuseFailAlloc_5193_; 
v_reuseFailAlloc_5193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5193_, 0, v_a_5187_);
v___x_5192_ = v_reuseFailAlloc_5193_;
goto v_reusejp_5191_;
}
v_reusejp_5191_:
{
return v___x_5192_;
}
}
}
}
else
{
lean_object* v_a_5195_; lean_object* v___x_5197_; uint8_t v_isShared_5198_; uint8_t v_isSharedCheck_5202_; 
lean_dec_ref(v_proof_5120_);
lean_dec_ref(v_e_x27_5119_);
lean_dec_ref(v___x_5112_);
lean_del_object(v___x_5107_);
lean_dec(v_snd_5105_);
lean_dec(v_mvarId_5081_);
v_a_5195_ = lean_ctor_get(v___x_5146_, 0);
v_isSharedCheck_5202_ = !lean_is_exclusive(v___x_5146_);
if (v_isSharedCheck_5202_ == 0)
{
v___x_5197_ = v___x_5146_;
v_isShared_5198_ = v_isSharedCheck_5202_;
goto v_resetjp_5196_;
}
else
{
lean_inc(v_a_5195_);
lean_dec(v___x_5146_);
v___x_5197_ = lean_box(0);
v_isShared_5198_ = v_isSharedCheck_5202_;
goto v_resetjp_5196_;
}
v_resetjp_5196_:
{
lean_object* v___x_5200_; 
if (v_isShared_5198_ == 0)
{
v___x_5200_ = v___x_5197_;
goto v_reusejp_5199_;
}
else
{
lean_object* v_reuseFailAlloc_5201_; 
v_reuseFailAlloc_5201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5201_, 0, v_a_5195_);
v___x_5200_ = v_reuseFailAlloc_5201_;
goto v_reusejp_5199_;
}
v_reusejp_5199_:
{
return v___x_5200_;
}
}
}
}
}
}
else
{
lean_object* v_a_5203_; lean_object* v___x_5205_; uint8_t v_isShared_5206_; uint8_t v_isSharedCheck_5210_; 
lean_dec_ref(v___x_5112_);
lean_del_object(v___x_5107_);
lean_dec(v_snd_5105_);
lean_dec(v_a_5104_);
lean_dec_ref(v_config_5082_);
lean_dec(v_mvarId_5081_);
v_a_5203_ = lean_ctor_get(v___y_5114_, 0);
v_isSharedCheck_5210_ = !lean_is_exclusive(v___y_5114_);
if (v_isSharedCheck_5210_ == 0)
{
v___x_5205_ = v___y_5114_;
v_isShared_5206_ = v_isSharedCheck_5210_;
goto v_resetjp_5204_;
}
else
{
lean_inc(v_a_5203_);
lean_dec(v___y_5114_);
v___x_5205_ = lean_box(0);
v_isShared_5206_ = v_isSharedCheck_5210_;
goto v_resetjp_5204_;
}
v_resetjp_5204_:
{
lean_object* v___x_5208_; 
if (v_isShared_5206_ == 0)
{
v___x_5208_ = v___x_5205_;
goto v_reusejp_5207_;
}
else
{
lean_object* v_reuseFailAlloc_5209_; 
v_reuseFailAlloc_5209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5209_, 0, v_a_5203_);
v___x_5208_ = v_reuseFailAlloc_5209_;
goto v_reusejp_5207_;
}
v_reusejp_5207_:
{
return v___x_5208_;
}
}
}
}
}
}
else
{
lean_object* v_a_5298_; lean_object* v___x_5300_; uint8_t v_isShared_5301_; uint8_t v_isSharedCheck_5305_; 
lean_dec_ref(v_b_5086_);
lean_dec_ref(v_config_5082_);
lean_dec(v_mvarId_5081_);
v_a_5298_ = lean_ctor_get(v___x_5102_, 0);
v_isSharedCheck_5305_ = !lean_is_exclusive(v___x_5102_);
if (v_isSharedCheck_5305_ == 0)
{
v___x_5300_ = v___x_5102_;
v_isShared_5301_ = v_isSharedCheck_5305_;
goto v_resetjp_5299_;
}
else
{
lean_inc(v_a_5298_);
lean_dec(v___x_5102_);
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
v___jp_5094_:
{
size_t v___x_5096_; size_t v___x_5097_; 
v___x_5096_ = ((size_t)1ULL);
v___x_5097_ = lean_usize_add(v_i_5085_, v___x_5096_);
v_i_5085_ = v___x_5097_;
v_b_5086_ = v_a_5095_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___boxed(lean_object* v_mvarId_5306_, lean_object* v_config_5307_, lean_object* v_as_5308_, lean_object* v_sz_5309_, lean_object* v_i_5310_, lean_object* v_b_5311_, lean_object* v___y_5312_, lean_object* v___y_5313_, lean_object* v___y_5314_, lean_object* v___y_5315_, lean_object* v___y_5316_, lean_object* v___y_5317_, lean_object* v___y_5318_){
_start:
{
size_t v_sz_boxed_5319_; size_t v_i_boxed_5320_; lean_object* v_res_5321_; 
v_sz_boxed_5319_ = lean_unbox_usize(v_sz_5309_);
lean_dec(v_sz_5309_);
v_i_boxed_5320_ = lean_unbox_usize(v_i_5310_);
lean_dec(v_i_5310_);
v_res_5321_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3(v_mvarId_5306_, v_config_5307_, v_as_5308_, v_sz_boxed_5319_, v_i_boxed_5320_, v_b_5311_, v___y_5312_, v___y_5313_, v___y_5314_, v___y_5315_, v___y_5316_, v___y_5317_);
lean_dec(v___y_5317_);
lean_dec_ref(v___y_5316_);
lean_dec(v___y_5315_);
lean_dec_ref(v___y_5314_);
lean_dec(v___y_5313_);
lean_dec_ref(v___y_5312_);
lean_dec_ref(v_as_5308_);
return v_res_5321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__1(lean_object* v_mvarId_5322_, lean_object* v_config_5323_, lean_object* v_fvarIdsToSimp_5324_, size_t v_sz_5325_, size_t v___x_5326_, lean_object* v___x_5327_, uint8_t v_simplifyTarget_5328_, lean_object* v___y_5329_, lean_object* v___y_5330_, lean_object* v___y_5331_, lean_object* v___y_5332_, lean_object* v___y_5333_, lean_object* v___y_5334_){
_start:
{
lean_object* v___y_5337_; lean_object* v___y_5338_; lean_object* v___y_5339_; lean_object* v___y_5340_; lean_object* v___y_5341_; uint8_t v___y_5342_; lean_object* v___x_5362_; 
lean_inc_ref(v_config_5323_);
lean_inc(v_mvarId_5322_);
v___x_5362_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3(v_mvarId_5322_, v_config_5323_, v_fvarIdsToSimp_5324_, v_sz_5325_, v___x_5326_, v___x_5327_, v___y_5329_, v___y_5330_, v___y_5331_, v___y_5332_, v___y_5333_, v___y_5334_);
if (lean_obj_tag(v___x_5362_) == 0)
{
lean_object* v_a_5363_; lean_object* v___x_5365_; uint8_t v_isShared_5366_; uint8_t v_isSharedCheck_5565_; 
v_a_5363_ = lean_ctor_get(v___x_5362_, 0);
v_isSharedCheck_5565_ = !lean_is_exclusive(v___x_5362_);
if (v_isSharedCheck_5565_ == 0)
{
v___x_5365_ = v___x_5362_;
v_isShared_5366_ = v_isSharedCheck_5565_;
goto v_resetjp_5364_;
}
else
{
lean_inc(v_a_5363_);
lean_dec(v___x_5362_);
v___x_5365_ = lean_box(0);
v_isShared_5366_ = v_isSharedCheck_5565_;
goto v_resetjp_5364_;
}
v_resetjp_5364_:
{
lean_object* v_fst_5367_; lean_object* v_snd_5368_; lean_object* v___x_5370_; uint8_t v_isShared_5371_; uint8_t v_isSharedCheck_5564_; 
v_fst_5367_ = lean_ctor_get(v_a_5363_, 0);
v_snd_5368_ = lean_ctor_get(v_a_5363_, 1);
v_isSharedCheck_5564_ = !lean_is_exclusive(v_a_5363_);
if (v_isSharedCheck_5564_ == 0)
{
v___x_5370_ = v_a_5363_;
v_isShared_5371_ = v_isSharedCheck_5564_;
goto v_resetjp_5369_;
}
else
{
lean_inc(v_snd_5368_);
lean_inc(v_fst_5367_);
lean_dec(v_a_5363_);
v___x_5370_ = lean_box(0);
v_isShared_5371_ = v_isSharedCheck_5564_;
goto v_resetjp_5369_;
}
v_resetjp_5369_:
{
lean_object* v_mvarIdNew_5373_; lean_object* v___y_5374_; lean_object* v___y_5375_; lean_object* v___y_5376_; lean_object* v___y_5377_; lean_object* v___y_5424_; 
if (lean_obj_tag(v_fst_5367_) == 0)
{
lean_del_object(v___x_5365_);
if (v_simplifyTarget_5328_ == 0)
{
lean_del_object(v___x_5370_);
lean_dec_ref(v_config_5323_);
v_mvarIdNew_5373_ = v_mvarId_5322_;
v___y_5374_ = v___y_5331_;
v___y_5375_ = v___y_5332_;
v___y_5376_ = v___y_5333_;
v___y_5377_ = v___y_5334_;
goto v___jp_5372_;
}
else
{
lean_object* v___x_5467_; 
lean_inc(v_mvarId_5322_);
v___x_5467_ = l_Lean_MVarId_getType(v_mvarId_5322_, v___y_5331_, v___y_5332_, v___y_5333_, v___y_5334_);
if (lean_obj_tag(v___x_5467_) == 0)
{
lean_object* v_options_5468_; uint8_t v_hasTrace_5469_; 
v_options_5468_ = lean_ctor_get(v___y_5333_, 2);
v_hasTrace_5469_ = lean_ctor_get_uint8(v_options_5468_, sizeof(void*)*1);
if (v_hasTrace_5469_ == 0)
{
lean_object* v_a_5470_; lean_object* v___x_5471_; 
lean_del_object(v___x_5370_);
v_a_5470_ = lean_ctor_get(v___x_5467_, 0);
lean_inc(v_a_5470_);
lean_dec_ref_known(v___x_5467_, 1);
v___x_5471_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v_a_5470_, v_config_5323_, v___y_5329_, v___y_5330_, v___y_5331_, v___y_5332_, v___y_5333_, v___y_5334_);
v___y_5424_ = v___x_5471_;
goto v___jp_5423_;
}
else
{
lean_object* v_a_5472_; lean_object* v_inheritedTraceOptions_5473_; lean_object* v___f_5474_; lean_object* v___x_5475_; lean_object* v___x_5476_; lean_object* v___x_5477_; uint8_t v___x_5478_; lean_object* v___y_5480_; lean_object* v___y_5481_; lean_object* v_a_5482_; lean_object* v___y_5497_; lean_object* v___y_5498_; lean_object* v_a_5499_; 
v_a_5472_ = lean_ctor_get(v___x_5467_, 0);
lean_inc_n(v_a_5472_, 2);
lean_dec_ref_known(v___x_5467_, 1);
v_inheritedTraceOptions_5473_ = lean_ctor_get(v___y_5333_, 13);
v___f_5474_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___boxed), 9, 1);
lean_closure_set(v___f_5474_, 0, v_a_5472_);
v___x_5475_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0));
v___x_5476_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__1));
v___x_5477_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1);
v___x_5478_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5473_, v_options_5468_, v___x_5477_);
if (v___x_5478_ == 0)
{
lean_object* v___x_5549_; uint8_t v___x_5550_; 
v___x_5549_ = l_Lean_trace_profiler;
v___x_5550_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_5468_, v___x_5549_);
if (v___x_5550_ == 0)
{
lean_object* v___x_5551_; 
lean_dec_ref(v___f_5474_);
lean_del_object(v___x_5370_);
v___x_5551_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v_a_5472_, v_config_5323_, v___y_5329_, v___y_5330_, v___y_5331_, v___y_5332_, v___y_5333_, v___y_5334_);
v___y_5424_ = v___x_5551_;
goto v___jp_5423_;
}
else
{
goto v___jp_5508_;
}
}
else
{
goto v___jp_5508_;
}
v___jp_5479_:
{
lean_object* v___x_5483_; double v___x_5484_; double v___x_5485_; double v___x_5486_; double v___x_5487_; double v___x_5488_; lean_object* v___x_5489_; lean_object* v___x_5490_; lean_object* v___x_5492_; 
v___x_5483_ = lean_io_mono_nanos_now();
v___x_5484_ = lean_float_of_nat(v___y_5481_);
v___x_5485_ = lean_float_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9);
v___x_5486_ = lean_float_div(v___x_5484_, v___x_5485_);
v___x_5487_ = lean_float_of_nat(v___x_5483_);
v___x_5488_ = lean_float_div(v___x_5487_, v___x_5485_);
v___x_5489_ = lean_box_float(v___x_5486_);
v___x_5490_ = lean_box_float(v___x_5488_);
if (v_isShared_5371_ == 0)
{
lean_ctor_set(v___x_5370_, 1, v___x_5490_);
lean_ctor_set(v___x_5370_, 0, v___x_5489_);
v___x_5492_ = v___x_5370_;
goto v_reusejp_5491_;
}
else
{
lean_object* v_reuseFailAlloc_5495_; 
v_reuseFailAlloc_5495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5495_, 0, v___x_5489_);
lean_ctor_set(v_reuseFailAlloc_5495_, 1, v___x_5490_);
v___x_5492_ = v_reuseFailAlloc_5495_;
goto v_reusejp_5491_;
}
v_reusejp_5491_:
{
lean_object* v___x_5493_; lean_object* v___x_5494_; 
v___x_5493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5493_, 0, v_a_5482_);
lean_ctor_set(v___x_5493_, 1, v___x_5492_);
v___x_5494_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2(v___x_5475_, v_hasTrace_5469_, v___x_5476_, v_options_5468_, v___x_5478_, v___y_5480_, v___f_5474_, v___x_5493_, v___y_5329_, v___y_5330_, v___y_5331_, v___y_5332_, v___y_5333_, v___y_5334_);
v___y_5424_ = v___x_5494_;
goto v___jp_5423_;
}
}
v___jp_5496_:
{
lean_object* v___x_5500_; double v___x_5501_; double v___x_5502_; lean_object* v___x_5503_; lean_object* v___x_5504_; lean_object* v___x_5505_; lean_object* v___x_5506_; lean_object* v___x_5507_; 
v___x_5500_ = lean_io_get_num_heartbeats();
v___x_5501_ = lean_float_of_nat(v___y_5498_);
v___x_5502_ = lean_float_of_nat(v___x_5500_);
v___x_5503_ = lean_box_float(v___x_5501_);
v___x_5504_ = lean_box_float(v___x_5502_);
v___x_5505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5505_, 0, v___x_5503_);
lean_ctor_set(v___x_5505_, 1, v___x_5504_);
v___x_5506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5506_, 0, v_a_5499_);
lean_ctor_set(v___x_5506_, 1, v___x_5505_);
v___x_5507_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2(v___x_5475_, v_hasTrace_5469_, v___x_5476_, v_options_5468_, v___x_5478_, v___y_5497_, v___f_5474_, v___x_5506_, v___y_5329_, v___y_5330_, v___y_5331_, v___y_5332_, v___y_5333_, v___y_5334_);
v___y_5424_ = v___x_5507_;
goto v___jp_5423_;
}
v___jp_5508_:
{
lean_object* v___x_5509_; lean_object* v_a_5510_; lean_object* v___x_5511_; uint8_t v___x_5512_; 
v___x_5509_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1___redArg(v___y_5334_);
v_a_5510_ = lean_ctor_get(v___x_5509_, 0);
lean_inc(v_a_5510_);
lean_dec_ref(v___x_5509_);
v___x_5511_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5512_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_5468_, v___x_5511_);
if (v___x_5512_ == 0)
{
lean_object* v___x_5513_; lean_object* v___x_5514_; 
v___x_5513_ = lean_io_mono_nanos_now();
v___x_5514_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v_a_5472_, v_config_5323_, v___y_5329_, v___y_5330_, v___y_5331_, v___y_5332_, v___y_5333_, v___y_5334_);
if (lean_obj_tag(v___x_5514_) == 0)
{
lean_object* v_a_5515_; lean_object* v___x_5517_; uint8_t v_isShared_5518_; uint8_t v_isSharedCheck_5522_; 
v_a_5515_ = lean_ctor_get(v___x_5514_, 0);
v_isSharedCheck_5522_ = !lean_is_exclusive(v___x_5514_);
if (v_isSharedCheck_5522_ == 0)
{
v___x_5517_ = v___x_5514_;
v_isShared_5518_ = v_isSharedCheck_5522_;
goto v_resetjp_5516_;
}
else
{
lean_inc(v_a_5515_);
lean_dec(v___x_5514_);
v___x_5517_ = lean_box(0);
v_isShared_5518_ = v_isSharedCheck_5522_;
goto v_resetjp_5516_;
}
v_resetjp_5516_:
{
lean_object* v___x_5520_; 
if (v_isShared_5518_ == 0)
{
lean_ctor_set_tag(v___x_5517_, 1);
v___x_5520_ = v___x_5517_;
goto v_reusejp_5519_;
}
else
{
lean_object* v_reuseFailAlloc_5521_; 
v_reuseFailAlloc_5521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5521_, 0, v_a_5515_);
v___x_5520_ = v_reuseFailAlloc_5521_;
goto v_reusejp_5519_;
}
v_reusejp_5519_:
{
v___y_5480_ = v_a_5510_;
v___y_5481_ = v___x_5513_;
v_a_5482_ = v___x_5520_;
goto v___jp_5479_;
}
}
}
else
{
lean_object* v_a_5523_; lean_object* v___x_5525_; uint8_t v_isShared_5526_; uint8_t v_isSharedCheck_5530_; 
v_a_5523_ = lean_ctor_get(v___x_5514_, 0);
v_isSharedCheck_5530_ = !lean_is_exclusive(v___x_5514_);
if (v_isSharedCheck_5530_ == 0)
{
v___x_5525_ = v___x_5514_;
v_isShared_5526_ = v_isSharedCheck_5530_;
goto v_resetjp_5524_;
}
else
{
lean_inc(v_a_5523_);
lean_dec(v___x_5514_);
v___x_5525_ = lean_box(0);
v_isShared_5526_ = v_isSharedCheck_5530_;
goto v_resetjp_5524_;
}
v_resetjp_5524_:
{
lean_object* v___x_5528_; 
if (v_isShared_5526_ == 0)
{
lean_ctor_set_tag(v___x_5525_, 0);
v___x_5528_ = v___x_5525_;
goto v_reusejp_5527_;
}
else
{
lean_object* v_reuseFailAlloc_5529_; 
v_reuseFailAlloc_5529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5529_, 0, v_a_5523_);
v___x_5528_ = v_reuseFailAlloc_5529_;
goto v_reusejp_5527_;
}
v_reusejp_5527_:
{
v___y_5480_ = v_a_5510_;
v___y_5481_ = v___x_5513_;
v_a_5482_ = v___x_5528_;
goto v___jp_5479_;
}
}
}
}
else
{
lean_object* v___x_5531_; lean_object* v___x_5532_; 
lean_del_object(v___x_5370_);
v___x_5531_ = lean_io_get_num_heartbeats();
v___x_5532_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v_a_5472_, v_config_5323_, v___y_5329_, v___y_5330_, v___y_5331_, v___y_5332_, v___y_5333_, v___y_5334_);
if (lean_obj_tag(v___x_5532_) == 0)
{
lean_object* v_a_5533_; lean_object* v___x_5535_; uint8_t v_isShared_5536_; uint8_t v_isSharedCheck_5540_; 
v_a_5533_ = lean_ctor_get(v___x_5532_, 0);
v_isSharedCheck_5540_ = !lean_is_exclusive(v___x_5532_);
if (v_isSharedCheck_5540_ == 0)
{
v___x_5535_ = v___x_5532_;
v_isShared_5536_ = v_isSharedCheck_5540_;
goto v_resetjp_5534_;
}
else
{
lean_inc(v_a_5533_);
lean_dec(v___x_5532_);
v___x_5535_ = lean_box(0);
v_isShared_5536_ = v_isSharedCheck_5540_;
goto v_resetjp_5534_;
}
v_resetjp_5534_:
{
lean_object* v___x_5538_; 
if (v_isShared_5536_ == 0)
{
lean_ctor_set_tag(v___x_5535_, 1);
v___x_5538_ = v___x_5535_;
goto v_reusejp_5537_;
}
else
{
lean_object* v_reuseFailAlloc_5539_; 
v_reuseFailAlloc_5539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5539_, 0, v_a_5533_);
v___x_5538_ = v_reuseFailAlloc_5539_;
goto v_reusejp_5537_;
}
v_reusejp_5537_:
{
v___y_5497_ = v_a_5510_;
v___y_5498_ = v___x_5531_;
v_a_5499_ = v___x_5538_;
goto v___jp_5496_;
}
}
}
else
{
lean_object* v_a_5541_; lean_object* v___x_5543_; uint8_t v_isShared_5544_; uint8_t v_isSharedCheck_5548_; 
v_a_5541_ = lean_ctor_get(v___x_5532_, 0);
v_isSharedCheck_5548_ = !lean_is_exclusive(v___x_5532_);
if (v_isSharedCheck_5548_ == 0)
{
v___x_5543_ = v___x_5532_;
v_isShared_5544_ = v_isSharedCheck_5548_;
goto v_resetjp_5542_;
}
else
{
lean_inc(v_a_5541_);
lean_dec(v___x_5532_);
v___x_5543_ = lean_box(0);
v_isShared_5544_ = v_isSharedCheck_5548_;
goto v_resetjp_5542_;
}
v_resetjp_5542_:
{
lean_object* v___x_5546_; 
if (v_isShared_5544_ == 0)
{
lean_ctor_set_tag(v___x_5543_, 0);
v___x_5546_ = v___x_5543_;
goto v_reusejp_5545_;
}
else
{
lean_object* v_reuseFailAlloc_5547_; 
v_reuseFailAlloc_5547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5547_, 0, v_a_5541_);
v___x_5546_ = v_reuseFailAlloc_5547_;
goto v_reusejp_5545_;
}
v_reusejp_5545_:
{
v___y_5497_ = v_a_5510_;
v___y_5498_ = v___x_5531_;
v_a_5499_ = v___x_5546_;
goto v___jp_5496_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5552_; lean_object* v___x_5554_; uint8_t v_isShared_5555_; uint8_t v_isSharedCheck_5559_; 
lean_del_object(v___x_5370_);
lean_dec(v_snd_5368_);
lean_dec_ref(v_config_5323_);
lean_dec(v_mvarId_5322_);
v_a_5552_ = lean_ctor_get(v___x_5467_, 0);
v_isSharedCheck_5559_ = !lean_is_exclusive(v___x_5467_);
if (v_isSharedCheck_5559_ == 0)
{
v___x_5554_ = v___x_5467_;
v_isShared_5555_ = v_isSharedCheck_5559_;
goto v_resetjp_5553_;
}
else
{
lean_inc(v_a_5552_);
lean_dec(v___x_5467_);
v___x_5554_ = lean_box(0);
v_isShared_5555_ = v_isSharedCheck_5559_;
goto v_resetjp_5553_;
}
v_resetjp_5553_:
{
lean_object* v___x_5557_; 
if (v_isShared_5555_ == 0)
{
v___x_5557_ = v___x_5554_;
goto v_reusejp_5556_;
}
else
{
lean_object* v_reuseFailAlloc_5558_; 
v_reuseFailAlloc_5558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5558_, 0, v_a_5552_);
v___x_5557_ = v_reuseFailAlloc_5558_;
goto v_reusejp_5556_;
}
v_reusejp_5556_:
{
return v___x_5557_;
}
}
}
}
}
else
{
lean_object* v_val_5560_; lean_object* v___x_5562_; 
lean_del_object(v___x_5370_);
lean_dec(v_snd_5368_);
lean_dec_ref(v_config_5323_);
lean_dec(v_mvarId_5322_);
v_val_5560_ = lean_ctor_get(v_fst_5367_, 0);
lean_inc(v_val_5560_);
lean_dec_ref_known(v_fst_5367_, 1);
if (v_isShared_5366_ == 0)
{
lean_ctor_set(v___x_5365_, 0, v_val_5560_);
v___x_5562_ = v___x_5365_;
goto v_reusejp_5561_;
}
else
{
lean_object* v_reuseFailAlloc_5563_; 
v_reuseFailAlloc_5563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5563_, 0, v_val_5560_);
v___x_5562_ = v_reuseFailAlloc_5563_;
goto v_reusejp_5561_;
}
v_reusejp_5561_:
{
return v___x_5562_;
}
}
v___jp_5372_:
{
lean_object* v___x_5378_; 
v___x_5378_ = l_Lean_MVarId_assertHypotheses(v_mvarIdNew_5373_, v_snd_5368_, v___y_5374_, v___y_5375_, v___y_5376_, v___y_5377_);
if (lean_obj_tag(v___x_5378_) == 0)
{
lean_object* v_a_5379_; lean_object* v_snd_5380_; lean_object* v___x_5381_; 
v_a_5379_ = lean_ctor_get(v___x_5378_, 0);
lean_inc(v_a_5379_);
lean_dec_ref_known(v___x_5378_, 1);
v_snd_5380_ = lean_ctor_get(v_a_5379_, 1);
lean_inc(v_snd_5380_);
lean_dec(v_a_5379_);
v___x_5381_ = l_Lean_MVarId_tryClearMany(v_snd_5380_, v_fvarIdsToSimp_5324_, v___y_5374_, v___y_5375_, v___y_5376_, v___y_5377_);
if (lean_obj_tag(v___x_5381_) == 0)
{
lean_object* v_a_5382_; lean_object* v___x_5383_; 
v_a_5382_ = lean_ctor_get(v___x_5381_, 0);
lean_inc(v_a_5382_);
lean_dec_ref_known(v___x_5381_, 1);
v___x_5383_ = l_Lean_Meta_saveState___redArg(v___y_5375_, v___y_5377_);
if (lean_obj_tag(v___x_5383_) == 0)
{
lean_object* v_a_5384_; uint8_t v___x_5385_; lean_object* v___x_5386_; 
v_a_5384_ = lean_ctor_get(v___x_5383_, 0);
lean_inc(v_a_5384_);
lean_dec_ref_known(v___x_5383_, 1);
v___x_5385_ = 1;
lean_inc(v_a_5382_);
v___x_5386_ = l_Lean_MVarId_refl(v_a_5382_, v___x_5385_, v___y_5374_, v___y_5375_, v___y_5376_, v___y_5377_);
if (lean_obj_tag(v___x_5386_) == 0)
{
lean_object* v___x_5388_; uint8_t v_isShared_5389_; uint8_t v_isSharedCheck_5394_; 
lean_dec(v_a_5384_);
lean_dec(v_a_5382_);
v_isSharedCheck_5394_ = !lean_is_exclusive(v___x_5386_);
if (v_isSharedCheck_5394_ == 0)
{
lean_object* v_unused_5395_; 
v_unused_5395_ = lean_ctor_get(v___x_5386_, 0);
lean_dec(v_unused_5395_);
v___x_5388_ = v___x_5386_;
v_isShared_5389_ = v_isSharedCheck_5394_;
goto v_resetjp_5387_;
}
else
{
lean_dec(v___x_5386_);
v___x_5388_ = lean_box(0);
v_isShared_5389_ = v_isSharedCheck_5394_;
goto v_resetjp_5387_;
}
v_resetjp_5387_:
{
lean_object* v___x_5390_; lean_object* v___x_5392_; 
v___x_5390_ = lean_box(0);
if (v_isShared_5389_ == 0)
{
lean_ctor_set(v___x_5388_, 0, v___x_5390_);
v___x_5392_ = v___x_5388_;
goto v_reusejp_5391_;
}
else
{
lean_object* v_reuseFailAlloc_5393_; 
v_reuseFailAlloc_5393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5393_, 0, v___x_5390_);
v___x_5392_ = v_reuseFailAlloc_5393_;
goto v_reusejp_5391_;
}
v_reusejp_5391_:
{
return v___x_5392_;
}
}
}
else
{
lean_object* v_a_5396_; uint8_t v___x_5397_; 
v_a_5396_ = lean_ctor_get(v___x_5386_, 0);
lean_inc(v_a_5396_);
lean_dec_ref_known(v___x_5386_, 1);
v___x_5397_ = l_Lean_Exception_isInterrupt(v_a_5396_);
if (v___x_5397_ == 0)
{
uint8_t v___x_5398_; 
lean_inc(v_a_5396_);
v___x_5398_ = l_Lean_Exception_isRuntime(v_a_5396_);
v___y_5337_ = v___y_5377_;
v___y_5338_ = v_a_5382_;
v___y_5339_ = v___y_5375_;
v___y_5340_ = v_a_5384_;
v___y_5341_ = v_a_5396_;
v___y_5342_ = v___x_5398_;
goto v___jp_5336_;
}
else
{
v___y_5337_ = v___y_5377_;
v___y_5338_ = v_a_5382_;
v___y_5339_ = v___y_5375_;
v___y_5340_ = v_a_5384_;
v___y_5341_ = v_a_5396_;
v___y_5342_ = v___x_5397_;
goto v___jp_5336_;
}
}
}
else
{
lean_object* v_a_5399_; lean_object* v___x_5401_; uint8_t v_isShared_5402_; uint8_t v_isSharedCheck_5406_; 
lean_dec(v_a_5382_);
v_a_5399_ = lean_ctor_get(v___x_5383_, 0);
v_isSharedCheck_5406_ = !lean_is_exclusive(v___x_5383_);
if (v_isSharedCheck_5406_ == 0)
{
v___x_5401_ = v___x_5383_;
v_isShared_5402_ = v_isSharedCheck_5406_;
goto v_resetjp_5400_;
}
else
{
lean_inc(v_a_5399_);
lean_dec(v___x_5383_);
v___x_5401_ = lean_box(0);
v_isShared_5402_ = v_isSharedCheck_5406_;
goto v_resetjp_5400_;
}
v_resetjp_5400_:
{
lean_object* v___x_5404_; 
if (v_isShared_5402_ == 0)
{
v___x_5404_ = v___x_5401_;
goto v_reusejp_5403_;
}
else
{
lean_object* v_reuseFailAlloc_5405_; 
v_reuseFailAlloc_5405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5405_, 0, v_a_5399_);
v___x_5404_ = v_reuseFailAlloc_5405_;
goto v_reusejp_5403_;
}
v_reusejp_5403_:
{
return v___x_5404_;
}
}
}
}
else
{
lean_object* v_a_5407_; lean_object* v___x_5409_; uint8_t v_isShared_5410_; uint8_t v_isSharedCheck_5414_; 
v_a_5407_ = lean_ctor_get(v___x_5381_, 0);
v_isSharedCheck_5414_ = !lean_is_exclusive(v___x_5381_);
if (v_isSharedCheck_5414_ == 0)
{
v___x_5409_ = v___x_5381_;
v_isShared_5410_ = v_isSharedCheck_5414_;
goto v_resetjp_5408_;
}
else
{
lean_inc(v_a_5407_);
lean_dec(v___x_5381_);
v___x_5409_ = lean_box(0);
v_isShared_5410_ = v_isSharedCheck_5414_;
goto v_resetjp_5408_;
}
v_resetjp_5408_:
{
lean_object* v___x_5412_; 
if (v_isShared_5410_ == 0)
{
v___x_5412_ = v___x_5409_;
goto v_reusejp_5411_;
}
else
{
lean_object* v_reuseFailAlloc_5413_; 
v_reuseFailAlloc_5413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5413_, 0, v_a_5407_);
v___x_5412_ = v_reuseFailAlloc_5413_;
goto v_reusejp_5411_;
}
v_reusejp_5411_:
{
return v___x_5412_;
}
}
}
}
else
{
lean_object* v_a_5415_; lean_object* v___x_5417_; uint8_t v_isShared_5418_; uint8_t v_isSharedCheck_5422_; 
v_a_5415_ = lean_ctor_get(v___x_5378_, 0);
v_isSharedCheck_5422_ = !lean_is_exclusive(v___x_5378_);
if (v_isSharedCheck_5422_ == 0)
{
v___x_5417_ = v___x_5378_;
v_isShared_5418_ = v_isSharedCheck_5422_;
goto v_resetjp_5416_;
}
else
{
lean_inc(v_a_5415_);
lean_dec(v___x_5378_);
v___x_5417_ = lean_box(0);
v_isShared_5418_ = v_isSharedCheck_5422_;
goto v_resetjp_5416_;
}
v_resetjp_5416_:
{
lean_object* v___x_5420_; 
if (v_isShared_5418_ == 0)
{
v___x_5420_ = v___x_5417_;
goto v_reusejp_5419_;
}
else
{
lean_object* v_reuseFailAlloc_5421_; 
v_reuseFailAlloc_5421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5421_, 0, v_a_5415_);
v___x_5420_ = v_reuseFailAlloc_5421_;
goto v_reusejp_5419_;
}
v_reusejp_5419_:
{
return v___x_5420_;
}
}
}
}
v___jp_5423_:
{
if (lean_obj_tag(v___y_5424_) == 0)
{
lean_object* v_a_5425_; 
v_a_5425_ = lean_ctor_get(v___y_5424_, 0);
lean_inc(v_a_5425_);
lean_dec_ref_known(v___y_5424_, 1);
if (lean_obj_tag(v_a_5425_) == 0)
{
lean_dec_ref_known(v_a_5425_, 0);
v_mvarIdNew_5373_ = v_mvarId_5322_;
v___y_5374_ = v___y_5331_;
v___y_5375_ = v___y_5332_;
v___y_5376_ = v___y_5333_;
v___y_5377_ = v___y_5334_;
goto v___jp_5372_;
}
else
{
lean_object* v_e_x27_5426_; lean_object* v_proof_5427_; uint8_t v___x_5428_; 
v_e_x27_5426_ = lean_ctor_get(v_a_5425_, 0);
lean_inc_ref_n(v_e_x27_5426_, 2);
v_proof_5427_ = lean_ctor_get(v_a_5425_, 1);
lean_inc_ref(v_proof_5427_);
lean_dec_ref_known(v_a_5425_, 2);
v___x_5428_ = l_Lean_Expr_isTrue(v_e_x27_5426_);
if (v___x_5428_ == 0)
{
lean_object* v___x_5429_; 
v___x_5429_ = l_Lean_MVarId_replaceTargetEq(v_mvarId_5322_, v_e_x27_5426_, v_proof_5427_, v___y_5331_, v___y_5332_, v___y_5333_, v___y_5334_);
if (lean_obj_tag(v___x_5429_) == 0)
{
lean_object* v_a_5430_; 
v_a_5430_ = lean_ctor_get(v___x_5429_, 0);
lean_inc(v_a_5430_);
lean_dec_ref_known(v___x_5429_, 1);
v_mvarIdNew_5373_ = v_a_5430_;
v___y_5374_ = v___y_5331_;
v___y_5375_ = v___y_5332_;
v___y_5376_ = v___y_5333_;
v___y_5377_ = v___y_5334_;
goto v___jp_5372_;
}
else
{
lean_object* v_a_5431_; lean_object* v___x_5433_; uint8_t v_isShared_5434_; uint8_t v_isSharedCheck_5438_; 
lean_dec(v_snd_5368_);
v_a_5431_ = lean_ctor_get(v___x_5429_, 0);
v_isSharedCheck_5438_ = !lean_is_exclusive(v___x_5429_);
if (v_isSharedCheck_5438_ == 0)
{
v___x_5433_ = v___x_5429_;
v_isShared_5434_ = v_isSharedCheck_5438_;
goto v_resetjp_5432_;
}
else
{
lean_inc(v_a_5431_);
lean_dec(v___x_5429_);
v___x_5433_ = lean_box(0);
v_isShared_5434_ = v_isSharedCheck_5438_;
goto v_resetjp_5432_;
}
v_resetjp_5432_:
{
lean_object* v___x_5436_; 
if (v_isShared_5434_ == 0)
{
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
return v___x_5436_;
}
}
}
}
else
{
lean_object* v___x_5439_; 
lean_dec_ref(v_e_x27_5426_);
lean_dec(v_snd_5368_);
v___x_5439_ = l_Lean_Meta_mkOfEqTrue(v_proof_5427_, v___y_5331_, v___y_5332_, v___y_5333_, v___y_5334_);
if (lean_obj_tag(v___x_5439_) == 0)
{
lean_object* v_a_5440_; lean_object* v___x_5441_; lean_object* v___x_5443_; uint8_t v_isShared_5444_; uint8_t v_isSharedCheck_5449_; 
v_a_5440_ = lean_ctor_get(v___x_5439_, 0);
lean_inc(v_a_5440_);
lean_dec_ref_known(v___x_5439_, 1);
v___x_5441_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___redArg(v_mvarId_5322_, v_a_5440_, v___y_5332_);
v_isSharedCheck_5449_ = !lean_is_exclusive(v___x_5441_);
if (v_isSharedCheck_5449_ == 0)
{
lean_object* v_unused_5450_; 
v_unused_5450_ = lean_ctor_get(v___x_5441_, 0);
lean_dec(v_unused_5450_);
v___x_5443_ = v___x_5441_;
v_isShared_5444_ = v_isSharedCheck_5449_;
goto v_resetjp_5442_;
}
else
{
lean_dec(v___x_5441_);
v___x_5443_ = lean_box(0);
v_isShared_5444_ = v_isSharedCheck_5449_;
goto v_resetjp_5442_;
}
v_resetjp_5442_:
{
lean_object* v___x_5445_; lean_object* v___x_5447_; 
v___x_5445_ = lean_box(0);
if (v_isShared_5444_ == 0)
{
lean_ctor_set(v___x_5443_, 0, v___x_5445_);
v___x_5447_ = v___x_5443_;
goto v_reusejp_5446_;
}
else
{
lean_object* v_reuseFailAlloc_5448_; 
v_reuseFailAlloc_5448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5448_, 0, v___x_5445_);
v___x_5447_ = v_reuseFailAlloc_5448_;
goto v_reusejp_5446_;
}
v_reusejp_5446_:
{
return v___x_5447_;
}
}
}
else
{
lean_object* v_a_5451_; lean_object* v___x_5453_; uint8_t v_isShared_5454_; uint8_t v_isSharedCheck_5458_; 
lean_dec(v_mvarId_5322_);
v_a_5451_ = lean_ctor_get(v___x_5439_, 0);
v_isSharedCheck_5458_ = !lean_is_exclusive(v___x_5439_);
if (v_isSharedCheck_5458_ == 0)
{
v___x_5453_ = v___x_5439_;
v_isShared_5454_ = v_isSharedCheck_5458_;
goto v_resetjp_5452_;
}
else
{
lean_inc(v_a_5451_);
lean_dec(v___x_5439_);
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
}
}
else
{
lean_object* v_a_5459_; lean_object* v___x_5461_; uint8_t v_isShared_5462_; uint8_t v_isSharedCheck_5466_; 
lean_dec(v_snd_5368_);
lean_dec(v_mvarId_5322_);
v_a_5459_ = lean_ctor_get(v___y_5424_, 0);
v_isSharedCheck_5466_ = !lean_is_exclusive(v___y_5424_);
if (v_isSharedCheck_5466_ == 0)
{
v___x_5461_ = v___y_5424_;
v_isShared_5462_ = v_isSharedCheck_5466_;
goto v_resetjp_5460_;
}
else
{
lean_inc(v_a_5459_);
lean_dec(v___y_5424_);
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
}
}
}
else
{
lean_object* v_a_5566_; lean_object* v___x_5568_; uint8_t v_isShared_5569_; uint8_t v_isSharedCheck_5573_; 
lean_dec_ref(v_config_5323_);
lean_dec(v_mvarId_5322_);
v_a_5566_ = lean_ctor_get(v___x_5362_, 0);
v_isSharedCheck_5573_ = !lean_is_exclusive(v___x_5362_);
if (v_isSharedCheck_5573_ == 0)
{
v___x_5568_ = v___x_5362_;
v_isShared_5569_ = v_isSharedCheck_5573_;
goto v_resetjp_5567_;
}
else
{
lean_inc(v_a_5566_);
lean_dec(v___x_5362_);
v___x_5568_ = lean_box(0);
v_isShared_5569_ = v_isSharedCheck_5573_;
goto v_resetjp_5567_;
}
v_resetjp_5567_:
{
lean_object* v___x_5571_; 
if (v_isShared_5569_ == 0)
{
v___x_5571_ = v___x_5568_;
goto v_reusejp_5570_;
}
else
{
lean_object* v_reuseFailAlloc_5572_; 
v_reuseFailAlloc_5572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5572_, 0, v_a_5566_);
v___x_5571_ = v_reuseFailAlloc_5572_;
goto v_reusejp_5570_;
}
v_reusejp_5570_:
{
return v___x_5571_;
}
}
}
v___jp_5336_:
{
if (v___y_5342_ == 0)
{
lean_object* v___x_5343_; 
lean_dec_ref(v___y_5341_);
v___x_5343_ = l_Lean_Meta_SavedState_restore___redArg(v___y_5340_, v___y_5339_, v___y_5337_);
lean_dec_ref(v___y_5340_);
if (lean_obj_tag(v___x_5343_) == 0)
{
lean_object* v___x_5345_; uint8_t v_isShared_5346_; uint8_t v_isSharedCheck_5351_; 
v_isSharedCheck_5351_ = !lean_is_exclusive(v___x_5343_);
if (v_isSharedCheck_5351_ == 0)
{
lean_object* v_unused_5352_; 
v_unused_5352_ = lean_ctor_get(v___x_5343_, 0);
lean_dec(v_unused_5352_);
v___x_5345_ = v___x_5343_;
v_isShared_5346_ = v_isSharedCheck_5351_;
goto v_resetjp_5344_;
}
else
{
lean_dec(v___x_5343_);
v___x_5345_ = lean_box(0);
v_isShared_5346_ = v_isSharedCheck_5351_;
goto v_resetjp_5344_;
}
v_resetjp_5344_:
{
lean_object* v___x_5347_; lean_object* v___x_5349_; 
v___x_5347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5347_, 0, v___y_5338_);
if (v_isShared_5346_ == 0)
{
lean_ctor_set(v___x_5345_, 0, v___x_5347_);
v___x_5349_ = v___x_5345_;
goto v_reusejp_5348_;
}
else
{
lean_object* v_reuseFailAlloc_5350_; 
v_reuseFailAlloc_5350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5350_, 0, v___x_5347_);
v___x_5349_ = v_reuseFailAlloc_5350_;
goto v_reusejp_5348_;
}
v_reusejp_5348_:
{
return v___x_5349_;
}
}
}
else
{
lean_object* v_a_5353_; lean_object* v___x_5355_; uint8_t v_isShared_5356_; uint8_t v_isSharedCheck_5360_; 
lean_dec(v___y_5338_);
v_a_5353_ = lean_ctor_get(v___x_5343_, 0);
v_isSharedCheck_5360_ = !lean_is_exclusive(v___x_5343_);
if (v_isSharedCheck_5360_ == 0)
{
v___x_5355_ = v___x_5343_;
v_isShared_5356_ = v_isSharedCheck_5360_;
goto v_resetjp_5354_;
}
else
{
lean_inc(v_a_5353_);
lean_dec(v___x_5343_);
v___x_5355_ = lean_box(0);
v_isShared_5356_ = v_isSharedCheck_5360_;
goto v_resetjp_5354_;
}
v_resetjp_5354_:
{
lean_object* v___x_5358_; 
if (v_isShared_5356_ == 0)
{
v___x_5358_ = v___x_5355_;
goto v_reusejp_5357_;
}
else
{
lean_object* v_reuseFailAlloc_5359_; 
v_reuseFailAlloc_5359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5359_, 0, v_a_5353_);
v___x_5358_ = v_reuseFailAlloc_5359_;
goto v_reusejp_5357_;
}
v_reusejp_5357_:
{
return v___x_5358_;
}
}
}
}
else
{
lean_object* v___x_5361_; 
lean_dec_ref(v___y_5340_);
lean_dec(v___y_5338_);
v___x_5361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5361_, 0, v___y_5341_);
return v___x_5361_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__1___boxed(lean_object* v_mvarId_5574_, lean_object* v_config_5575_, lean_object* v_fvarIdsToSimp_5576_, lean_object* v_sz_5577_, lean_object* v___x_5578_, lean_object* v___x_5579_, lean_object* v_simplifyTarget_5580_, lean_object* v___y_5581_, lean_object* v___y_5582_, lean_object* v___y_5583_, lean_object* v___y_5584_, lean_object* v___y_5585_, lean_object* v___y_5586_, lean_object* v___y_5587_){
_start:
{
size_t v_sz_boxed_5588_; size_t v___x_49233__boxed_5589_; uint8_t v_simplifyTarget_boxed_5590_; lean_object* v_res_5591_; 
v_sz_boxed_5588_ = lean_unbox_usize(v_sz_5577_);
lean_dec(v_sz_5577_);
v___x_49233__boxed_5589_ = lean_unbox_usize(v___x_5578_);
lean_dec(v___x_5578_);
v_simplifyTarget_boxed_5590_ = lean_unbox(v_simplifyTarget_5580_);
v_res_5591_ = l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__1(v_mvarId_5574_, v_config_5575_, v_fvarIdsToSimp_5576_, v_sz_boxed_5588_, v___x_49233__boxed_5589_, v___x_5579_, v_simplifyTarget_boxed_5590_, v___y_5581_, v___y_5582_, v___y_5583_, v___y_5584_, v___y_5585_, v___y_5586_);
lean_dec(v___y_5586_);
lean_dec_ref(v___y_5585_);
lean_dec(v___y_5584_);
lean_dec_ref(v___y_5583_);
lean_dec(v___y_5582_);
lean_dec_ref(v___y_5581_);
lean_dec_ref(v_fvarIdsToSimp_5576_);
return v_res_5591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__2(lean_object* v_fvarIdsToSimp_5599_, lean_object* v_mvarId_5600_, uint8_t v_simplifyTarget_5601_, lean_object* v___y_5602_, lean_object* v___y_5603_, lean_object* v___y_5604_, lean_object* v___y_5605_, lean_object* v___y_5606_, lean_object* v___y_5607_){
_start:
{
lean_object* v_options_5609_; lean_object* v___x_5610_; lean_object* v___x_5611_; lean_object* v___x_5612_; lean_object* v_config_5613_; lean_object* v___x_5614_; size_t v_sz_5615_; lean_object* v___x_5616_; lean_object* v___x_5617_; lean_object* v___x_5618_; lean_object* v___f_5619_; lean_object* v___x_5620_; 
v_options_5609_ = lean_ctor_get(v___y_5606_, 2);
v___x_5610_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_5611_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_5609_, v___x_5610_);
v___x_5612_ = lean_unsigned_to_nat(2u);
v_config_5613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_config_5613_, 0, v___x_5611_);
lean_ctor_set(v_config_5613_, 1, v___x_5612_);
v___x_5614_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__2___closed__1));
v_sz_5615_ = lean_array_size(v_fvarIdsToSimp_5599_);
v___x_5616_ = lean_box_usize(v_sz_5615_);
v___x_5617_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__2___boxed__const__1));
v___x_5618_ = lean_box(v_simplifyTarget_5601_);
lean_inc(v_mvarId_5600_);
v___f_5619_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__1___boxed), 14, 7);
lean_closure_set(v___f_5619_, 0, v_mvarId_5600_);
lean_closure_set(v___f_5619_, 1, v_config_5613_);
lean_closure_set(v___f_5619_, 2, v_fvarIdsToSimp_5599_);
lean_closure_set(v___f_5619_, 3, v___x_5616_);
lean_closure_set(v___f_5619_, 4, v___x_5617_);
lean_closure_set(v___f_5619_, 5, v___x_5614_);
lean_closure_set(v___f_5619_, 6, v___x_5618_);
v___x_5620_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg(v_mvarId_5600_, v___f_5619_, v___y_5602_, v___y_5603_, v___y_5604_, v___y_5605_, v___y_5606_, v___y_5607_);
return v___x_5620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__2___boxed(lean_object* v_fvarIdsToSimp_5621_, lean_object* v_mvarId_5622_, lean_object* v_simplifyTarget_5623_, lean_object* v___y_5624_, lean_object* v___y_5625_, lean_object* v___y_5626_, lean_object* v___y_5627_, lean_object* v___y_5628_, lean_object* v___y_5629_, lean_object* v___y_5630_){
_start:
{
uint8_t v_simplifyTarget_boxed_5631_; lean_object* v_res_5632_; 
v_simplifyTarget_boxed_5631_ = lean_unbox(v_simplifyTarget_5623_);
v_res_5632_ = l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__2(v_fvarIdsToSimp_5621_, v_mvarId_5622_, v_simplifyTarget_boxed_5631_, v___y_5624_, v___y_5625_, v___y_5626_, v___y_5627_, v___y_5628_, v___y_5629_);
lean_dec(v___y_5629_);
lean_dec_ref(v___y_5628_);
lean_dec(v___y_5627_);
lean_dec_ref(v___y_5626_);
lean_dec(v___y_5625_);
lean_dec_ref(v___y_5624_);
return v_res_5632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore(lean_object* v_mvarId_5633_, uint8_t v_simplifyTarget_5634_, lean_object* v_fvarIdsToSimp_5635_, lean_object* v_a_5636_, lean_object* v_a_5637_, lean_object* v_a_5638_, lean_object* v_a_5639_, lean_object* v_a_5640_, lean_object* v_a_5641_){
_start:
{
lean_object* v___x_5643_; lean_object* v___f_5644_; lean_object* v___x_5645_; 
v___x_5643_ = lean_box(v_simplifyTarget_5634_);
v___f_5644_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__2___boxed), 10, 3);
lean_closure_set(v___f_5644_, 0, v_fvarIdsToSimp_5635_);
lean_closure_set(v___f_5644_, 1, v_mvarId_5633_);
lean_closure_set(v___f_5644_, 2, v___x_5643_);
v___x_5645_ = l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0___redArg(v___f_5644_, v_a_5636_, v_a_5637_, v_a_5638_, v_a_5639_, v_a_5640_, v_a_5641_);
return v___x_5645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___boxed(lean_object* v_mvarId_5646_, lean_object* v_simplifyTarget_5647_, lean_object* v_fvarIdsToSimp_5648_, lean_object* v_a_5649_, lean_object* v_a_5650_, lean_object* v_a_5651_, lean_object* v_a_5652_, lean_object* v_a_5653_, lean_object* v_a_5654_, lean_object* v_a_5655_){
_start:
{
uint8_t v_simplifyTarget_boxed_5656_; lean_object* v_res_5657_; 
v_simplifyTarget_boxed_5656_ = lean_unbox(v_simplifyTarget_5647_);
v_res_5657_ = l_Lean_Meta_Tactic_Cbv_cbvGoalCore(v_mvarId_5646_, v_simplifyTarget_boxed_5656_, v_fvarIdsToSimp_5648_, v_a_5649_, v_a_5650_, v_a_5651_, v_a_5652_, v_a_5653_, v_a_5654_);
lean_dec(v_a_5654_);
lean_dec_ref(v_a_5653_);
lean_dec(v_a_5652_);
lean_dec_ref(v_a_5651_);
lean_dec(v_a_5650_);
lean_dec_ref(v_a_5649_);
return v_res_5657_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0(lean_object* v_mvarId_5658_, lean_object* v_val_5659_, lean_object* v___y_5660_, lean_object* v___y_5661_, lean_object* v___y_5662_, lean_object* v___y_5663_, lean_object* v___y_5664_, lean_object* v___y_5665_){
_start:
{
lean_object* v___x_5667_; 
v___x_5667_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___redArg(v_mvarId_5658_, v_val_5659_, v___y_5663_);
return v___x_5667_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___boxed(lean_object* v_mvarId_5668_, lean_object* v_val_5669_, lean_object* v___y_5670_, lean_object* v___y_5671_, lean_object* v___y_5672_, lean_object* v___y_5673_, lean_object* v___y_5674_, lean_object* v___y_5675_, lean_object* v___y_5676_){
_start:
{
lean_object* v_res_5677_; 
v_res_5677_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0(v_mvarId_5668_, v_val_5669_, v___y_5670_, v___y_5671_, v___y_5672_, v___y_5673_, v___y_5674_, v___y_5675_);
lean_dec(v___y_5675_);
lean_dec_ref(v___y_5674_);
lean_dec(v___y_5673_);
lean_dec_ref(v___y_5672_);
lean_dec(v___y_5671_);
lean_dec_ref(v___y_5670_);
return v_res_5677_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4(lean_object* v_00_u03b1_5678_, lean_object* v_x_5679_, lean_object* v___y_5680_, lean_object* v___y_5681_, lean_object* v___y_5682_, lean_object* v___y_5683_, lean_object* v___y_5684_, lean_object* v___y_5685_){
_start:
{
lean_object* v___x_5687_; 
v___x_5687_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4___redArg(v_x_5679_);
return v___x_5687_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4___boxed(lean_object* v_00_u03b1_5688_, lean_object* v_x_5689_, lean_object* v___y_5690_, lean_object* v___y_5691_, lean_object* v___y_5692_, lean_object* v___y_5693_, lean_object* v___y_5694_, lean_object* v___y_5695_, lean_object* v___y_5696_){
_start:
{
lean_object* v_res_5697_; 
v_res_5697_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4(v_00_u03b1_5688_, v_x_5689_, v___y_5690_, v___y_5691_, v___y_5692_, v___y_5693_, v___y_5694_, v___y_5695_);
lean_dec(v___y_5695_);
lean_dec_ref(v___y_5694_);
lean_dec(v___y_5693_);
lean_dec_ref(v___y_5692_);
lean_dec(v___y_5691_);
lean_dec_ref(v___y_5690_);
return v_res_5697_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0(lean_object* v_00_u03b2_5698_, lean_object* v_x_5699_, lean_object* v_x_5700_, lean_object* v_x_5701_){
_start:
{
lean_object* v___x_5702_; 
v___x_5702_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0___redArg(v_x_5699_, v_x_5700_, v_x_5701_);
return v___x_5702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__3(lean_object* v_oldTraces_5703_, lean_object* v_data_5704_, lean_object* v_ref_5705_, lean_object* v_msg_5706_, lean_object* v___y_5707_, lean_object* v___y_5708_, lean_object* v___y_5709_, lean_object* v___y_5710_, lean_object* v___y_5711_, lean_object* v___y_5712_){
_start:
{
lean_object* v___x_5714_; 
v___x_5714_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__3___redArg(v_oldTraces_5703_, v_data_5704_, v_ref_5705_, v_msg_5706_, v___y_5709_, v___y_5710_, v___y_5711_, v___y_5712_);
return v___x_5714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__3___boxed(lean_object* v_oldTraces_5715_, lean_object* v_data_5716_, lean_object* v_ref_5717_, lean_object* v_msg_5718_, lean_object* v___y_5719_, lean_object* v___y_5720_, lean_object* v___y_5721_, lean_object* v___y_5722_, lean_object* v___y_5723_, lean_object* v___y_5724_, lean_object* v___y_5725_){
_start:
{
lean_object* v_res_5726_; 
v_res_5726_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__3(v_oldTraces_5715_, v_data_5716_, v_ref_5717_, v_msg_5718_, v___y_5719_, v___y_5720_, v___y_5721_, v___y_5722_, v___y_5723_, v___y_5724_);
lean_dec(v___y_5724_);
lean_dec_ref(v___y_5723_);
lean_dec(v___y_5722_);
lean_dec_ref(v___y_5721_);
lean_dec(v___y_5720_);
lean_dec_ref(v___y_5719_);
return v_res_5726_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_5727_, lean_object* v_x_5728_, size_t v_x_5729_, size_t v_x_5730_, lean_object* v_x_5731_, lean_object* v_x_5732_){
_start:
{
lean_object* v___x_5733_; 
v___x_5733_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg(v_x_5728_, v_x_5729_, v_x_5730_, v_x_5731_, v_x_5732_);
return v___x_5733_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_5734_, lean_object* v_x_5735_, lean_object* v_x_5736_, lean_object* v_x_5737_, lean_object* v_x_5738_, lean_object* v_x_5739_){
_start:
{
size_t v_x_49883__boxed_5740_; size_t v_x_49884__boxed_5741_; lean_object* v_res_5742_; 
v_x_49883__boxed_5740_ = lean_unbox_usize(v_x_5736_);
lean_dec(v_x_5736_);
v_x_49884__boxed_5741_ = lean_unbox_usize(v_x_5737_);
lean_dec(v_x_5737_);
v_res_5742_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3(v_00_u03b2_5734_, v_x_5735_, v_x_49883__boxed_5740_, v_x_49884__boxed_5741_, v_x_5738_, v_x_5739_);
return v_res_5742_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__7(lean_object* v_00_u03b2_5743_, lean_object* v_n_5744_, lean_object* v_k_5745_, lean_object* v_v_5746_){
_start:
{
lean_object* v___x_5747_; 
v___x_5747_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__7___redArg(v_n_5744_, v_k_5745_, v_v_5746_);
return v___x_5747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__8(lean_object* v_00_u03b2_5748_, size_t v_depth_5749_, lean_object* v_keys_5750_, lean_object* v_vals_5751_, lean_object* v_heq_5752_, lean_object* v_i_5753_, lean_object* v_entries_5754_){
_start:
{
lean_object* v___x_5755_; 
v___x_5755_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__8___redArg(v_depth_5749_, v_keys_5750_, v_vals_5751_, v_i_5753_, v_entries_5754_);
return v___x_5755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__8___boxed(lean_object* v_00_u03b2_5756_, lean_object* v_depth_5757_, lean_object* v_keys_5758_, lean_object* v_vals_5759_, lean_object* v_heq_5760_, lean_object* v_i_5761_, lean_object* v_entries_5762_){
_start:
{
size_t v_depth_boxed_5763_; lean_object* v_res_5764_; 
v_depth_boxed_5763_ = lean_unbox_usize(v_depth_5757_);
lean_dec(v_depth_5757_);
v_res_5764_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__8(v_00_u03b2_5756_, v_depth_boxed_5763_, v_keys_5758_, v_vals_5759_, v_heq_5760_, v_i_5761_, v_entries_5762_);
lean_dec_ref(v_vals_5759_);
lean_dec_ref(v_keys_5758_);
return v_res_5764_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__7_spec__9(lean_object* v_00_u03b2_5765_, lean_object* v_x_5766_, lean_object* v_x_5767_, lean_object* v_x_5768_, lean_object* v_x_5769_){
_start:
{
lean_object* v___x_5770_; 
v___x_5770_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__7_spec__9___redArg(v_x_5766_, v_x_5767_, v_x_5768_, v_x_5769_);
return v___x_5770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0(lean_object* v_mvarId_5771_, uint8_t v_simplifyTarget_5772_, lean_object* v_fvarIdsToSimp_5773_, lean_object* v___y_5774_, lean_object* v___y_5775_, lean_object* v___y_5776_, lean_object* v___y_5777_, lean_object* v___y_5778_, lean_object* v___y_5779_){
_start:
{
lean_object* v___x_5781_; 
v___x_5781_ = l_Lean_Meta_Sym_preprocessMVar(v_mvarId_5771_, v___y_5774_, v___y_5775_, v___y_5776_, v___y_5777_, v___y_5778_, v___y_5779_);
if (lean_obj_tag(v___x_5781_) == 0)
{
lean_object* v_a_5782_; lean_object* v___x_5783_; 
v_a_5782_ = lean_ctor_get(v___x_5781_, 0);
lean_inc(v_a_5782_);
lean_dec_ref_known(v___x_5781_, 1);
v___x_5783_ = l_Lean_Meta_Tactic_Cbv_cbvGoalCore(v_a_5782_, v_simplifyTarget_5772_, v_fvarIdsToSimp_5773_, v___y_5774_, v___y_5775_, v___y_5776_, v___y_5777_, v___y_5778_, v___y_5779_);
return v___x_5783_;
}
else
{
lean_object* v_a_5784_; lean_object* v___x_5786_; uint8_t v_isShared_5787_; uint8_t v_isSharedCheck_5791_; 
lean_dec_ref(v_fvarIdsToSimp_5773_);
v_a_5784_ = lean_ctor_get(v___x_5781_, 0);
v_isSharedCheck_5791_ = !lean_is_exclusive(v___x_5781_);
if (v_isSharedCheck_5791_ == 0)
{
v___x_5786_ = v___x_5781_;
v_isShared_5787_ = v_isSharedCheck_5791_;
goto v_resetjp_5785_;
}
else
{
lean_inc(v_a_5784_);
lean_dec(v___x_5781_);
v___x_5786_ = lean_box(0);
v_isShared_5787_ = v_isSharedCheck_5791_;
goto v_resetjp_5785_;
}
v_resetjp_5785_:
{
lean_object* v___x_5789_; 
if (v_isShared_5787_ == 0)
{
v___x_5789_ = v___x_5786_;
goto v_reusejp_5788_;
}
else
{
lean_object* v_reuseFailAlloc_5790_; 
v_reuseFailAlloc_5790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5790_, 0, v_a_5784_);
v___x_5789_ = v_reuseFailAlloc_5790_;
goto v_reusejp_5788_;
}
v_reusejp_5788_:
{
return v___x_5789_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___boxed(lean_object* v_mvarId_5792_, lean_object* v_simplifyTarget_5793_, lean_object* v_fvarIdsToSimp_5794_, lean_object* v___y_5795_, lean_object* v___y_5796_, lean_object* v___y_5797_, lean_object* v___y_5798_, lean_object* v___y_5799_, lean_object* v___y_5800_, lean_object* v___y_5801_){
_start:
{
uint8_t v_simplifyTarget_boxed_5802_; lean_object* v_res_5803_; 
v_simplifyTarget_boxed_5802_ = lean_unbox(v_simplifyTarget_5793_);
v_res_5803_ = l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0(v_mvarId_5792_, v_simplifyTarget_boxed_5802_, v_fvarIdsToSimp_5794_, v___y_5795_, v___y_5796_, v___y_5797_, v___y_5798_, v___y_5799_, v___y_5800_);
lean_dec(v___y_5800_);
lean_dec_ref(v___y_5799_);
lean_dec(v___y_5798_);
lean_dec_ref(v___y_5797_);
lean_dec(v___y_5796_);
lean_dec_ref(v___y_5795_);
return v_res_5803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal(lean_object* v_mvarId_5804_, uint8_t v_simplifyTarget_5805_, lean_object* v_fvarIdsToSimp_5806_, lean_object* v_a_5807_, lean_object* v_a_5808_, lean_object* v_a_5809_, lean_object* v_a_5810_){
_start:
{
lean_object* v___x_5812_; lean_object* v___f_5813_; lean_object* v___x_5814_; 
v___x_5812_ = lean_box(v_simplifyTarget_5805_);
v___f_5813_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___boxed), 10, 3);
lean_closure_set(v___f_5813_, 0, v_mvarId_5804_);
lean_closure_set(v___f_5813_, 1, v___x_5812_);
lean_closure_set(v___f_5813_, 2, v_fvarIdsToSimp_5806_);
v___x_5814_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_5813_, v_a_5807_, v_a_5808_, v_a_5809_, v_a_5810_);
return v___x_5814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___boxed(lean_object* v_mvarId_5815_, lean_object* v_simplifyTarget_5816_, lean_object* v_fvarIdsToSimp_5817_, lean_object* v_a_5818_, lean_object* v_a_5819_, lean_object* v_a_5820_, lean_object* v_a_5821_, lean_object* v_a_5822_){
_start:
{
uint8_t v_simplifyTarget_boxed_5823_; lean_object* v_res_5824_; 
v_simplifyTarget_boxed_5823_ = lean_unbox(v_simplifyTarget_5816_);
v_res_5824_ = l_Lean_Meta_Tactic_Cbv_cbvGoal(v_mvarId_5815_, v_simplifyTarget_boxed_5823_, v_fvarIdsToSimp_5817_, v_a_5818_, v_a_5819_, v_a_5820_, v_a_5821_);
lean_dec(v_a_5821_);
lean_dec_ref(v_a_5820_);
lean_dec(v_a_5819_);
lean_dec_ref(v_a_5818_);
return v_res_5824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0(lean_object* v_a_5825_, uint8_t v___x_5826_, lean_object* v___y_5827_, lean_object* v___y_5828_, lean_object* v___y_5829_, lean_object* v___y_5830_, lean_object* v___y_5831_, lean_object* v___y_5832_){
_start:
{
lean_object* v___x_5834_; 
v___x_5834_ = l_Lean_MVarId_refl(v_a_5825_, v___x_5826_, v___y_5829_, v___y_5830_, v___y_5831_, v___y_5832_);
return v___x_5834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0___boxed(lean_object* v_a_5835_, lean_object* v___x_5836_, lean_object* v___y_5837_, lean_object* v___y_5838_, lean_object* v___y_5839_, lean_object* v___y_5840_, lean_object* v___y_5841_, lean_object* v___y_5842_, lean_object* v___y_5843_){
_start:
{
uint8_t v___x_25154__boxed_5844_; lean_object* v_res_5845_; 
v___x_25154__boxed_5844_ = lean_unbox(v___x_5836_);
v_res_5845_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0(v_a_5835_, v___x_25154__boxed_5844_, v___y_5837_, v___y_5838_, v___y_5839_, v___y_5840_, v___y_5841_, v___y_5842_);
lean_dec(v___y_5842_);
lean_dec_ref(v___y_5841_);
lean_dec(v___y_5840_);
lean_dec_ref(v___y_5839_);
lean_dec(v___y_5838_);
lean_dec_ref(v___y_5837_);
return v_res_5845_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(lean_object* v_cls_5846_, lean_object* v_msg_5847_, lean_object* v___y_5848_, lean_object* v___y_5849_, lean_object* v___y_5850_, lean_object* v___y_5851_){
_start:
{
lean_object* v_ref_5853_; lean_object* v___x_5854_; lean_object* v_a_5855_; lean_object* v___x_5857_; uint8_t v_isShared_5858_; uint8_t v_isSharedCheck_5899_; 
v_ref_5853_ = lean_ctor_get(v___y_5850_, 5);
v___x_5854_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0_spec__0(v_msg_5847_, v___y_5848_, v___y_5849_, v___y_5850_, v___y_5851_);
v_a_5855_ = lean_ctor_get(v___x_5854_, 0);
v_isSharedCheck_5899_ = !lean_is_exclusive(v___x_5854_);
if (v_isSharedCheck_5899_ == 0)
{
v___x_5857_ = v___x_5854_;
v_isShared_5858_ = v_isSharedCheck_5899_;
goto v_resetjp_5856_;
}
else
{
lean_inc(v_a_5855_);
lean_dec(v___x_5854_);
v___x_5857_ = lean_box(0);
v_isShared_5858_ = v_isSharedCheck_5899_;
goto v_resetjp_5856_;
}
v_resetjp_5856_:
{
lean_object* v___x_5859_; lean_object* v_traceState_5860_; lean_object* v_env_5861_; lean_object* v_nextMacroScope_5862_; lean_object* v_ngen_5863_; lean_object* v_auxDeclNGen_5864_; lean_object* v_cache_5865_; lean_object* v_messages_5866_; lean_object* v_infoState_5867_; lean_object* v_snapshotTasks_5868_; lean_object* v___x_5870_; uint8_t v_isShared_5871_; uint8_t v_isSharedCheck_5898_; 
v___x_5859_ = lean_st_ref_take(v___y_5851_);
v_traceState_5860_ = lean_ctor_get(v___x_5859_, 4);
v_env_5861_ = lean_ctor_get(v___x_5859_, 0);
v_nextMacroScope_5862_ = lean_ctor_get(v___x_5859_, 1);
v_ngen_5863_ = lean_ctor_get(v___x_5859_, 2);
v_auxDeclNGen_5864_ = lean_ctor_get(v___x_5859_, 3);
v_cache_5865_ = lean_ctor_get(v___x_5859_, 5);
v_messages_5866_ = lean_ctor_get(v___x_5859_, 6);
v_infoState_5867_ = lean_ctor_get(v___x_5859_, 7);
v_snapshotTasks_5868_ = lean_ctor_get(v___x_5859_, 8);
v_isSharedCheck_5898_ = !lean_is_exclusive(v___x_5859_);
if (v_isSharedCheck_5898_ == 0)
{
v___x_5870_ = v___x_5859_;
v_isShared_5871_ = v_isSharedCheck_5898_;
goto v_resetjp_5869_;
}
else
{
lean_inc(v_snapshotTasks_5868_);
lean_inc(v_infoState_5867_);
lean_inc(v_messages_5866_);
lean_inc(v_cache_5865_);
lean_inc(v_traceState_5860_);
lean_inc(v_auxDeclNGen_5864_);
lean_inc(v_ngen_5863_);
lean_inc(v_nextMacroScope_5862_);
lean_inc(v_env_5861_);
lean_dec(v___x_5859_);
v___x_5870_ = lean_box(0);
v_isShared_5871_ = v_isSharedCheck_5898_;
goto v_resetjp_5869_;
}
v_resetjp_5869_:
{
uint64_t v_tid_5872_; lean_object* v_traces_5873_; lean_object* v___x_5875_; uint8_t v_isShared_5876_; uint8_t v_isSharedCheck_5897_; 
v_tid_5872_ = lean_ctor_get_uint64(v_traceState_5860_, sizeof(void*)*1);
v_traces_5873_ = lean_ctor_get(v_traceState_5860_, 0);
v_isSharedCheck_5897_ = !lean_is_exclusive(v_traceState_5860_);
if (v_isSharedCheck_5897_ == 0)
{
v___x_5875_ = v_traceState_5860_;
v_isShared_5876_ = v_isSharedCheck_5897_;
goto v_resetjp_5874_;
}
else
{
lean_inc(v_traces_5873_);
lean_dec(v_traceState_5860_);
v___x_5875_ = lean_box(0);
v_isShared_5876_ = v_isSharedCheck_5897_;
goto v_resetjp_5874_;
}
v_resetjp_5874_:
{
lean_object* v___x_5877_; double v___x_5878_; uint8_t v___x_5879_; lean_object* v___x_5880_; lean_object* v___x_5881_; lean_object* v___x_5882_; lean_object* v___x_5883_; lean_object* v___x_5884_; lean_object* v___x_5885_; lean_object* v___x_5887_; 
v___x_5877_ = lean_box(0);
v___x_5878_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0);
v___x_5879_ = 0;
v___x_5880_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__1));
v___x_5881_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_5881_, 0, v_cls_5846_);
lean_ctor_set(v___x_5881_, 1, v___x_5877_);
lean_ctor_set(v___x_5881_, 2, v___x_5880_);
lean_ctor_set_float(v___x_5881_, sizeof(void*)*3, v___x_5878_);
lean_ctor_set_float(v___x_5881_, sizeof(void*)*3 + 8, v___x_5878_);
lean_ctor_set_uint8(v___x_5881_, sizeof(void*)*3 + 16, v___x_5879_);
v___x_5882_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__2));
v___x_5883_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_5883_, 0, v___x_5881_);
lean_ctor_set(v___x_5883_, 1, v_a_5855_);
lean_ctor_set(v___x_5883_, 2, v___x_5882_);
lean_inc(v_ref_5853_);
v___x_5884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5884_, 0, v_ref_5853_);
lean_ctor_set(v___x_5884_, 1, v___x_5883_);
v___x_5885_ = l_Lean_PersistentArray_push___redArg(v_traces_5873_, v___x_5884_);
if (v_isShared_5876_ == 0)
{
lean_ctor_set(v___x_5875_, 0, v___x_5885_);
v___x_5887_ = v___x_5875_;
goto v_reusejp_5886_;
}
else
{
lean_object* v_reuseFailAlloc_5896_; 
v_reuseFailAlloc_5896_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5896_, 0, v___x_5885_);
lean_ctor_set_uint64(v_reuseFailAlloc_5896_, sizeof(void*)*1, v_tid_5872_);
v___x_5887_ = v_reuseFailAlloc_5896_;
goto v_reusejp_5886_;
}
v_reusejp_5886_:
{
lean_object* v___x_5889_; 
if (v_isShared_5871_ == 0)
{
lean_ctor_set(v___x_5870_, 4, v___x_5887_);
v___x_5889_ = v___x_5870_;
goto v_reusejp_5888_;
}
else
{
lean_object* v_reuseFailAlloc_5895_; 
v_reuseFailAlloc_5895_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5895_, 0, v_env_5861_);
lean_ctor_set(v_reuseFailAlloc_5895_, 1, v_nextMacroScope_5862_);
lean_ctor_set(v_reuseFailAlloc_5895_, 2, v_ngen_5863_);
lean_ctor_set(v_reuseFailAlloc_5895_, 3, v_auxDeclNGen_5864_);
lean_ctor_set(v_reuseFailAlloc_5895_, 4, v___x_5887_);
lean_ctor_set(v_reuseFailAlloc_5895_, 5, v_cache_5865_);
lean_ctor_set(v_reuseFailAlloc_5895_, 6, v_messages_5866_);
lean_ctor_set(v_reuseFailAlloc_5895_, 7, v_infoState_5867_);
lean_ctor_set(v_reuseFailAlloc_5895_, 8, v_snapshotTasks_5868_);
v___x_5889_ = v_reuseFailAlloc_5895_;
goto v_reusejp_5888_;
}
v_reusejp_5888_:
{
lean_object* v___x_5890_; lean_object* v___x_5891_; lean_object* v___x_5893_; 
v___x_5890_ = lean_st_ref_set(v___y_5851_, v___x_5889_);
v___x_5891_ = lean_box(0);
if (v_isShared_5858_ == 0)
{
lean_ctor_set(v___x_5857_, 0, v___x_5891_);
v___x_5893_ = v___x_5857_;
goto v_reusejp_5892_;
}
else
{
lean_object* v_reuseFailAlloc_5894_; 
v_reuseFailAlloc_5894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5894_, 0, v___x_5891_);
v___x_5893_ = v_reuseFailAlloc_5894_;
goto v_reusejp_5892_;
}
v_reusejp_5892_:
{
return v___x_5893_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg___boxed(lean_object* v_cls_5900_, lean_object* v_msg_5901_, lean_object* v___y_5902_, lean_object* v___y_5903_, lean_object* v___y_5904_, lean_object* v___y_5905_, lean_object* v___y_5906_){
_start:
{
lean_object* v_res_5907_; 
v_res_5907_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(v_cls_5900_, v_msg_5901_, v___y_5902_, v___y_5903_, v___y_5904_, v___y_5905_);
lean_dec(v___y_5905_);
lean_dec_ref(v___y_5904_);
lean_dec(v___y_5903_);
lean_dec_ref(v___y_5902_);
return v_res_5907_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(lean_object* v_msg_5908_, lean_object* v___y_5909_, lean_object* v___y_5910_, lean_object* v___y_5911_, lean_object* v___y_5912_){
_start:
{
lean_object* v_ref_5914_; lean_object* v___x_5915_; lean_object* v_a_5916_; lean_object* v___x_5918_; uint8_t v_isShared_5919_; uint8_t v_isSharedCheck_5924_; 
v_ref_5914_ = lean_ctor_get(v___y_5911_, 5);
v___x_5915_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0_spec__0(v_msg_5908_, v___y_5909_, v___y_5910_, v___y_5911_, v___y_5912_);
v_a_5916_ = lean_ctor_get(v___x_5915_, 0);
v_isSharedCheck_5924_ = !lean_is_exclusive(v___x_5915_);
if (v_isSharedCheck_5924_ == 0)
{
v___x_5918_ = v___x_5915_;
v_isShared_5919_ = v_isSharedCheck_5924_;
goto v_resetjp_5917_;
}
else
{
lean_inc(v_a_5916_);
lean_dec(v___x_5915_);
v___x_5918_ = lean_box(0);
v_isShared_5919_ = v_isSharedCheck_5924_;
goto v_resetjp_5917_;
}
v_resetjp_5917_:
{
lean_object* v___x_5920_; lean_object* v___x_5922_; 
lean_inc(v_ref_5914_);
v___x_5920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5920_, 0, v_ref_5914_);
lean_ctor_set(v___x_5920_, 1, v_a_5916_);
if (v_isShared_5919_ == 0)
{
lean_ctor_set_tag(v___x_5918_, 1);
lean_ctor_set(v___x_5918_, 0, v___x_5920_);
v___x_5922_ = v___x_5918_;
goto v_reusejp_5921_;
}
else
{
lean_object* v_reuseFailAlloc_5923_; 
v_reuseFailAlloc_5923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5923_, 0, v___x_5920_);
v___x_5922_ = v_reuseFailAlloc_5923_;
goto v_reusejp_5921_;
}
v_reusejp_5921_:
{
return v___x_5922_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg___boxed(lean_object* v_msg_5925_, lean_object* v___y_5926_, lean_object* v___y_5927_, lean_object* v___y_5928_, lean_object* v___y_5929_, lean_object* v___y_5930_){
_start:
{
lean_object* v_res_5931_; 
v_res_5931_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v_msg_5925_, v___y_5926_, v___y_5927_, v___y_5928_, v___y_5929_);
lean_dec(v___y_5929_);
lean_dec_ref(v___y_5928_);
lean_dec(v___y_5927_);
lean_dec_ref(v___y_5926_);
return v_res_5931_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1(void){
_start:
{
lean_object* v___x_5933_; lean_object* v___x_5934_; 
v___x_5933_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__0));
v___x_5934_ = l_Lean_stringToMessageData(v___x_5933_);
return v___x_5934_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3(void){
_start:
{
lean_object* v___x_5936_; lean_object* v___x_5937_; 
v___x_5936_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__2));
v___x_5937_ = l_Lean_stringToMessageData(v___x_5936_);
return v___x_5937_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6(void){
_start:
{
lean_object* v___x_5941_; lean_object* v___x_5942_; 
v___x_5941_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__5));
v___x_5942_ = l_Lean_stringToMessageData(v___x_5941_);
return v___x_5942_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8(void){
_start:
{
lean_object* v___x_5944_; lean_object* v___x_5945_; 
v___x_5944_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__7));
v___x_5945_ = l_Lean_stringToMessageData(v___x_5944_);
return v___x_5945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1(lean_object* v_m_5946_, lean_object* v___x_5947_, lean_object* v_cls_5948_, lean_object* v___y_5949_, lean_object* v___y_5950_, lean_object* v___y_5951_, lean_object* v___y_5952_, lean_object* v___y_5953_, lean_object* v___y_5954_){
_start:
{
lean_object* v_e_5957_; lean_object* v_onTrue_5958_; lean_object* v___y_5959_; lean_object* v___y_5960_; lean_object* v___y_5961_; lean_object* v___y_5962_; lean_object* v___y_5963_; lean_object* v___y_5964_; lean_object* v___x_5994_; 
v___x_5994_ = l_Lean_Meta_Sym_preprocessMVar(v_m_5946_, v___y_5949_, v___y_5950_, v___y_5951_, v___y_5952_, v___y_5953_, v___y_5954_);
if (lean_obj_tag(v___x_5994_) == 0)
{
lean_object* v_a_5995_; lean_object* v___x_5996_; 
v_a_5995_ = lean_ctor_get(v___x_5994_, 0);
lean_inc_n(v_a_5995_, 2);
lean_dec_ref_known(v___x_5994_, 1);
v___x_5996_ = l_Lean_MVarId_getType(v_a_5995_, v___y_5951_, v___y_5952_, v___y_5953_, v___y_5954_);
if (lean_obj_tag(v___x_5996_) == 0)
{
lean_object* v_a_5997_; lean_object* v___x_5998_; lean_object* v___x_5999_; uint8_t v___x_6000_; 
v_a_5997_ = lean_ctor_get(v___x_5996_, 0);
lean_inc(v_a_5997_);
lean_dec_ref_known(v___x_5996_, 1);
v___x_5998_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__4));
v___x_5999_ = lean_unsigned_to_nat(3u);
v___x_6000_ = l_Lean_Expr_isAppOfArity(v_a_5997_, v___x_5998_, v___x_5999_);
if (v___x_6000_ == 0)
{
lean_object* v___x_6001_; lean_object* v___x_6002_; lean_object* v___x_6003_; lean_object* v___x_6004_; 
lean_dec(v_a_5995_);
lean_dec(v_cls_5948_);
lean_dec_ref(v___x_5947_);
v___x_6001_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6);
v___x_6002_ = l_Lean_indentExpr(v_a_5997_);
v___x_6003_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6003_, 0, v___x_6001_);
lean_ctor_set(v___x_6003_, 1, v___x_6002_);
v___x_6004_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_6003_, v___y_5951_, v___y_5952_, v___y_5953_, v___y_5954_);
return v___x_6004_;
}
else
{
lean_object* v___x_6005_; lean_object* v___x_6006_; lean_object* v___x_6007_; 
v___x_6005_ = l_Lean_Expr_appFn_x21(v_a_5997_);
lean_dec(v_a_5997_);
v___x_6006_ = l_Lean_Expr_appArg_x21(v___x_6005_);
lean_dec_ref(v___x_6005_);
lean_inc_ref(v___x_6006_);
v___x_6007_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_6006_, v___x_5947_, v___y_5949_, v___y_5950_, v___y_5951_, v___y_5952_, v___y_5953_, v___y_5954_);
if (lean_obj_tag(v___x_6007_) == 0)
{
lean_object* v_options_6008_; lean_object* v_a_6009_; lean_object* v_inheritedTraceOptions_6010_; uint8_t v_hasTrace_6011_; lean_object* v___x_6012_; lean_object* v___f_6013_; lean_object* v___y_6015_; lean_object* v___y_6016_; lean_object* v___y_6017_; lean_object* v___y_6018_; lean_object* v___y_6019_; lean_object* v___y_6020_; 
v_options_6008_ = lean_ctor_get(v___y_5953_, 2);
v_a_6009_ = lean_ctor_get(v___x_6007_, 0);
lean_inc(v_a_6009_);
lean_dec_ref_known(v___x_6007_, 1);
v_inheritedTraceOptions_6010_ = lean_ctor_get(v___y_5953_, 13);
v_hasTrace_6011_ = lean_ctor_get_uint8(v_options_6008_, sizeof(void*)*1);
v___x_6012_ = lean_box(v___x_6000_);
lean_inc(v_a_5995_);
v___f_6013_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0___boxed), 9, 2);
lean_closure_set(v___f_6013_, 0, v_a_5995_);
lean_closure_set(v___f_6013_, 1, v___x_6012_);
if (v_hasTrace_6011_ == 0)
{
lean_dec(v_cls_5948_);
v___y_6015_ = v___y_5949_;
v___y_6016_ = v___y_5950_;
v___y_6017_ = v___y_5951_;
v___y_6018_ = v___y_5952_;
v___y_6019_ = v___y_5953_;
v___y_6020_ = v___y_5954_;
goto v___jp_6014_;
}
else
{
lean_object* v___x_6024_; lean_object* v___x_6025_; uint8_t v___x_6026_; 
v___x_6024_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__3));
lean_inc(v_cls_5948_);
v___x_6025_ = l_Lean_Name_append(v___x_6024_, v_cls_5948_);
v___x_6026_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6010_, v_options_6008_, v___x_6025_);
lean_dec(v___x_6025_);
if (v___x_6026_ == 0)
{
lean_dec(v_cls_5948_);
v___y_6015_ = v___y_5949_;
v___y_6016_ = v___y_5950_;
v___y_6017_ = v___y_5951_;
v___y_6018_ = v___y_5952_;
v___y_6019_ = v___y_5953_;
v___y_6020_ = v___y_5954_;
goto v___jp_6014_;
}
else
{
lean_object* v___x_6027_; lean_object* v___x_6028_; lean_object* v___x_6029_; lean_object* v___x_6030_; lean_object* v___x_6031_; lean_object* v___x_6032_; lean_object* v___x_6033_; lean_object* v___x_6034_; lean_object* v___x_6035_; 
v___x_6027_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8);
lean_inc_ref(v___x_6006_);
v___x_6028_ = l_Lean_indentExpr(v___x_6006_);
v___x_6029_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6029_, 0, v___x_6027_);
lean_ctor_set(v___x_6029_, 1, v___x_6028_);
v___x_6030_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_6031_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6031_, 0, v___x_6029_);
lean_ctor_set(v___x_6031_, 1, v___x_6030_);
v___x_6032_ = l_Lean_Meta_Sym_Simp_Result_getResultExpr(v___x_6006_, v_a_6009_);
v___x_6033_ = l_Lean_indentExpr(v___x_6032_);
v___x_6034_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6034_, 0, v___x_6031_);
lean_ctor_set(v___x_6034_, 1, v___x_6033_);
v___x_6035_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(v_cls_5948_, v___x_6034_, v___y_5951_, v___y_5952_, v___y_5953_, v___y_5954_);
if (lean_obj_tag(v___x_6035_) == 0)
{
lean_dec_ref_known(v___x_6035_, 1);
v___y_6015_ = v___y_5949_;
v___y_6016_ = v___y_5950_;
v___y_6017_ = v___y_5951_;
v___y_6018_ = v___y_5952_;
v___y_6019_ = v___y_5953_;
v___y_6020_ = v___y_5954_;
goto v___jp_6014_;
}
else
{
lean_dec_ref(v___f_6013_);
lean_dec(v_a_6009_);
lean_dec_ref(v___x_6006_);
lean_dec(v_a_5995_);
return v___x_6035_;
}
}
}
v___jp_6014_:
{
if (lean_obj_tag(v_a_6009_) == 0)
{
lean_dec_ref_known(v_a_6009_, 0);
lean_dec(v_a_5995_);
v_e_5957_ = v___x_6006_;
v_onTrue_5958_ = v___f_6013_;
v___y_5959_ = v___y_6015_;
v___y_5960_ = v___y_6016_;
v___y_5961_ = v___y_6017_;
v___y_5962_ = v___y_6018_;
v___y_5963_ = v___y_6019_;
v___y_5964_ = v___y_6020_;
goto v___jp_5956_;
}
else
{
lean_object* v_e_x27_6021_; lean_object* v_proof_6022_; lean_object* v___x_6023_; 
lean_dec_ref(v___f_6013_);
lean_dec_ref(v___x_6006_);
v_e_x27_6021_ = lean_ctor_get(v_a_6009_, 0);
lean_inc_ref(v_e_x27_6021_);
v_proof_6022_ = lean_ctor_get(v_a_6009_, 1);
lean_inc_ref(v_proof_6022_);
lean_dec_ref_known(v_a_6009_, 2);
v___x_6023_ = lean_alloc_closure((void*)(l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___boxed), 9, 2);
lean_closure_set(v___x_6023_, 0, v_a_5995_);
lean_closure_set(v___x_6023_, 1, v_proof_6022_);
v_e_5957_ = v_e_x27_6021_;
v_onTrue_5958_ = v___x_6023_;
v___y_5959_ = v___y_6015_;
v___y_5960_ = v___y_6016_;
v___y_5961_ = v___y_6017_;
v___y_5962_ = v___y_6018_;
v___y_5963_ = v___y_6019_;
v___y_5964_ = v___y_6020_;
goto v___jp_5956_;
}
}
}
else
{
lean_object* v_a_6036_; lean_object* v___x_6038_; uint8_t v_isShared_6039_; uint8_t v_isSharedCheck_6043_; 
lean_dec_ref(v___x_6006_);
lean_dec(v_a_5995_);
lean_dec(v_cls_5948_);
v_a_6036_ = lean_ctor_get(v___x_6007_, 0);
v_isSharedCheck_6043_ = !lean_is_exclusive(v___x_6007_);
if (v_isSharedCheck_6043_ == 0)
{
v___x_6038_ = v___x_6007_;
v_isShared_6039_ = v_isSharedCheck_6043_;
goto v_resetjp_6037_;
}
else
{
lean_inc(v_a_6036_);
lean_dec(v___x_6007_);
v___x_6038_ = lean_box(0);
v_isShared_6039_ = v_isSharedCheck_6043_;
goto v_resetjp_6037_;
}
v_resetjp_6037_:
{
lean_object* v___x_6041_; 
if (v_isShared_6039_ == 0)
{
v___x_6041_ = v___x_6038_;
goto v_reusejp_6040_;
}
else
{
lean_object* v_reuseFailAlloc_6042_; 
v_reuseFailAlloc_6042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6042_, 0, v_a_6036_);
v___x_6041_ = v_reuseFailAlloc_6042_;
goto v_reusejp_6040_;
}
v_reusejp_6040_:
{
return v___x_6041_;
}
}
}
}
}
else
{
lean_object* v_a_6044_; lean_object* v___x_6046_; uint8_t v_isShared_6047_; uint8_t v_isSharedCheck_6051_; 
lean_dec(v_a_5995_);
lean_dec(v_cls_5948_);
lean_dec_ref(v___x_5947_);
v_a_6044_ = lean_ctor_get(v___x_5996_, 0);
v_isSharedCheck_6051_ = !lean_is_exclusive(v___x_5996_);
if (v_isSharedCheck_6051_ == 0)
{
v___x_6046_ = v___x_5996_;
v_isShared_6047_ = v_isSharedCheck_6051_;
goto v_resetjp_6045_;
}
else
{
lean_inc(v_a_6044_);
lean_dec(v___x_5996_);
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
else
{
lean_object* v_a_6052_; lean_object* v___x_6054_; uint8_t v_isShared_6055_; uint8_t v_isSharedCheck_6059_; 
lean_dec(v_cls_5948_);
lean_dec_ref(v___x_5947_);
v_a_6052_ = lean_ctor_get(v___x_5994_, 0);
v_isSharedCheck_6059_ = !lean_is_exclusive(v___x_5994_);
if (v_isSharedCheck_6059_ == 0)
{
v___x_6054_ = v___x_5994_;
v_isShared_6055_ = v_isSharedCheck_6059_;
goto v_resetjp_6053_;
}
else
{
lean_inc(v_a_6052_);
lean_dec(v___x_5994_);
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
v___jp_5956_:
{
lean_object* v___x_5965_; 
v___x_5965_ = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(v_e_5957_, v___y_5959_);
if (lean_obj_tag(v___x_5965_) == 0)
{
lean_object* v_a_5966_; uint8_t v___x_5967_; 
v_a_5966_ = lean_ctor_get(v___x_5965_, 0);
lean_inc(v_a_5966_);
lean_dec_ref_known(v___x_5965_, 1);
v___x_5967_ = lean_unbox(v_a_5966_);
lean_dec(v_a_5966_);
if (v___x_5967_ == 0)
{
lean_object* v___x_5968_; 
lean_dec_ref(v_onTrue_5958_);
v___x_5968_ = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(v_e_5957_, v___y_5959_);
if (lean_obj_tag(v___x_5968_) == 0)
{
lean_object* v_a_5969_; uint8_t v___x_5970_; 
v_a_5969_ = lean_ctor_get(v___x_5968_, 0);
lean_inc(v_a_5969_);
lean_dec_ref_known(v___x_5968_, 1);
v___x_5970_ = lean_unbox(v_a_5969_);
lean_dec(v_a_5969_);
if (v___x_5970_ == 0)
{
lean_object* v___x_5971_; lean_object* v___x_5972_; lean_object* v___x_5973_; lean_object* v___x_5974_; 
v___x_5971_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1);
v___x_5972_ = l_Lean_indentExpr(v_e_5957_);
v___x_5973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5973_, 0, v___x_5971_);
lean_ctor_set(v___x_5973_, 1, v___x_5972_);
v___x_5974_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_5973_, v___y_5961_, v___y_5962_, v___y_5963_, v___y_5964_);
return v___x_5974_;
}
else
{
lean_object* v___x_5975_; lean_object* v___x_5976_; 
lean_dec_ref(v_e_5957_);
v___x_5975_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3);
v___x_5976_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_5975_, v___y_5961_, v___y_5962_, v___y_5963_, v___y_5964_);
return v___x_5976_;
}
}
else
{
lean_object* v_a_5977_; lean_object* v___x_5979_; uint8_t v_isShared_5980_; uint8_t v_isSharedCheck_5984_; 
lean_dec_ref(v_e_5957_);
v_a_5977_ = lean_ctor_get(v___x_5968_, 0);
v_isSharedCheck_5984_ = !lean_is_exclusive(v___x_5968_);
if (v_isSharedCheck_5984_ == 0)
{
v___x_5979_ = v___x_5968_;
v_isShared_5980_ = v_isSharedCheck_5984_;
goto v_resetjp_5978_;
}
else
{
lean_inc(v_a_5977_);
lean_dec(v___x_5968_);
v___x_5979_ = lean_box(0);
v_isShared_5980_ = v_isSharedCheck_5984_;
goto v_resetjp_5978_;
}
v_resetjp_5978_:
{
lean_object* v___x_5982_; 
if (v_isShared_5980_ == 0)
{
v___x_5982_ = v___x_5979_;
goto v_reusejp_5981_;
}
else
{
lean_object* v_reuseFailAlloc_5983_; 
v_reuseFailAlloc_5983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5983_, 0, v_a_5977_);
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
else
{
lean_object* v___x_5985_; 
lean_dec_ref(v_e_5957_);
lean_inc(v___y_5964_);
lean_inc_ref(v___y_5963_);
lean_inc(v___y_5962_);
lean_inc_ref(v___y_5961_);
lean_inc(v___y_5960_);
lean_inc_ref(v___y_5959_);
v___x_5985_ = lean_apply_7(v_onTrue_5958_, v___y_5959_, v___y_5960_, v___y_5961_, v___y_5962_, v___y_5963_, v___y_5964_, lean_box(0));
return v___x_5985_;
}
}
else
{
lean_object* v_a_5986_; lean_object* v___x_5988_; uint8_t v_isShared_5989_; uint8_t v_isSharedCheck_5993_; 
lean_dec_ref(v_onTrue_5958_);
lean_dec_ref(v_e_5957_);
v_a_5986_ = lean_ctor_get(v___x_5965_, 0);
v_isSharedCheck_5993_ = !lean_is_exclusive(v___x_5965_);
if (v_isSharedCheck_5993_ == 0)
{
v___x_5988_ = v___x_5965_;
v_isShared_5989_ = v_isSharedCheck_5993_;
goto v_resetjp_5987_;
}
else
{
lean_inc(v_a_5986_);
lean_dec(v___x_5965_);
v___x_5988_ = lean_box(0);
v_isShared_5989_ = v_isSharedCheck_5993_;
goto v_resetjp_5987_;
}
v_resetjp_5987_:
{
lean_object* v___x_5991_; 
if (v_isShared_5989_ == 0)
{
v___x_5991_ = v___x_5988_;
goto v_reusejp_5990_;
}
else
{
lean_object* v_reuseFailAlloc_5992_; 
v_reuseFailAlloc_5992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5992_, 0, v_a_5986_);
v___x_5991_ = v_reuseFailAlloc_5992_;
goto v_reusejp_5990_;
}
v_reusejp_5990_:
{
return v___x_5991_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___boxed(lean_object* v_m_6060_, lean_object* v___x_6061_, lean_object* v_cls_6062_, lean_object* v___y_6063_, lean_object* v___y_6064_, lean_object* v___y_6065_, lean_object* v___y_6066_, lean_object* v___y_6067_, lean_object* v___y_6068_, lean_object* v___y_6069_){
_start:
{
lean_object* v_res_6070_; 
v_res_6070_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1(v_m_6060_, v___x_6061_, v_cls_6062_, v___y_6063_, v___y_6064_, v___y_6065_, v___y_6066_, v___y_6067_, v___y_6068_);
lean_dec(v___y_6068_);
lean_dec_ref(v___y_6067_);
lean_dec(v___y_6066_);
lean_dec_ref(v___y_6065_);
lean_dec(v___y_6064_);
lean_dec_ref(v___y_6063_);
return v_res_6070_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__1(void){
_start:
{
lean_object* v___x_6072_; lean_object* v___x_6073_; 
v___x_6072_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__0));
v___x_6073_ = l_Lean_stringToMessageData(v___x_6072_);
return v___x_6073_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__3(void){
_start:
{
lean_object* v___x_6075_; lean_object* v___x_6076_; 
v___x_6075_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__2));
v___x_6076_ = l_Lean_stringToMessageData(v___x_6075_);
return v___x_6076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2(lean_object* v_x_6077_, lean_object* v___y_6078_, lean_object* v___y_6079_, lean_object* v___y_6080_, lean_object* v___y_6081_){
_start:
{
if (lean_obj_tag(v_x_6077_) == 0)
{
lean_object* v_a_6083_; lean_object* v___x_6085_; uint8_t v_isShared_6086_; uint8_t v_isSharedCheck_6093_; 
v_a_6083_ = lean_ctor_get(v_x_6077_, 0);
v_isSharedCheck_6093_ = !lean_is_exclusive(v_x_6077_);
if (v_isSharedCheck_6093_ == 0)
{
v___x_6085_ = v_x_6077_;
v_isShared_6086_ = v_isSharedCheck_6093_;
goto v_resetjp_6084_;
}
else
{
lean_inc(v_a_6083_);
lean_dec(v_x_6077_);
v___x_6085_ = lean_box(0);
v_isShared_6086_ = v_isSharedCheck_6093_;
goto v_resetjp_6084_;
}
v_resetjp_6084_:
{
lean_object* v___x_6087_; lean_object* v___x_6088_; lean_object* v___x_6089_; lean_object* v___x_6091_; 
v___x_6087_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__1);
v___x_6088_ = l_Lean_Exception_toMessageData(v_a_6083_);
v___x_6089_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6089_, 0, v___x_6087_);
lean_ctor_set(v___x_6089_, 1, v___x_6088_);
if (v_isShared_6086_ == 0)
{
lean_ctor_set(v___x_6085_, 0, v___x_6089_);
v___x_6091_ = v___x_6085_;
goto v_reusejp_6090_;
}
else
{
lean_object* v_reuseFailAlloc_6092_; 
v_reuseFailAlloc_6092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6092_, 0, v___x_6089_);
v___x_6091_ = v_reuseFailAlloc_6092_;
goto v_reusejp_6090_;
}
v_reusejp_6090_:
{
return v___x_6091_;
}
}
}
else
{
lean_object* v___x_6095_; uint8_t v_isShared_6096_; uint8_t v_isSharedCheck_6101_; 
v_isSharedCheck_6101_ = !lean_is_exclusive(v_x_6077_);
if (v_isSharedCheck_6101_ == 0)
{
lean_object* v_unused_6102_; 
v_unused_6102_ = lean_ctor_get(v_x_6077_, 0);
lean_dec(v_unused_6102_);
v___x_6095_ = v_x_6077_;
v_isShared_6096_ = v_isSharedCheck_6101_;
goto v_resetjp_6094_;
}
else
{
lean_dec(v_x_6077_);
v___x_6095_ = lean_box(0);
v_isShared_6096_ = v_isSharedCheck_6101_;
goto v_resetjp_6094_;
}
v_resetjp_6094_:
{
lean_object* v___x_6097_; lean_object* v___x_6099_; 
v___x_6097_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__3, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__3);
if (v_isShared_6096_ == 0)
{
lean_ctor_set_tag(v___x_6095_, 0);
lean_ctor_set(v___x_6095_, 0, v___x_6097_);
v___x_6099_ = v___x_6095_;
goto v_reusejp_6098_;
}
else
{
lean_object* v_reuseFailAlloc_6100_; 
v_reuseFailAlloc_6100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6100_, 0, v___x_6097_);
v___x_6099_ = v_reuseFailAlloc_6100_;
goto v_reusejp_6098_;
}
v_reusejp_6098_:
{
return v___x_6099_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___boxed(lean_object* v_x_6103_, lean_object* v___y_6104_, lean_object* v___y_6105_, lean_object* v___y_6106_, lean_object* v___y_6107_, lean_object* v___y_6108_){
_start:
{
lean_object* v_res_6109_; 
v_res_6109_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2(v_x_6103_, v___y_6104_, v___y_6105_, v___y_6106_, v___y_6107_);
lean_dec(v___y_6107_);
lean_dec_ref(v___y_6106_);
lean_dec(v___y_6105_);
lean_dec_ref(v___y_6104_);
return v_res_6109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__3(lean_object* v_a_6110_, uint8_t v_hasTrace_6111_, lean_object* v___y_6112_, lean_object* v___y_6113_, lean_object* v___y_6114_, lean_object* v___y_6115_, lean_object* v___y_6116_, lean_object* v___y_6117_){
_start:
{
lean_object* v___x_6119_; 
v___x_6119_ = l_Lean_MVarId_refl(v_a_6110_, v_hasTrace_6111_, v___y_6114_, v___y_6115_, v___y_6116_, v___y_6117_);
return v___x_6119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__3___boxed(lean_object* v_a_6120_, lean_object* v_hasTrace_6121_, lean_object* v___y_6122_, lean_object* v___y_6123_, lean_object* v___y_6124_, lean_object* v___y_6125_, lean_object* v___y_6126_, lean_object* v___y_6127_, lean_object* v___y_6128_){
_start:
{
uint8_t v_hasTrace_boxed_6129_; lean_object* v_res_6130_; 
v_hasTrace_boxed_6129_ = lean_unbox(v_hasTrace_6121_);
v_res_6130_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__3(v_a_6120_, v_hasTrace_boxed_6129_, v___y_6122_, v___y_6123_, v___y_6124_, v___y_6125_, v___y_6126_, v___y_6127_);
lean_dec(v___y_6127_);
lean_dec_ref(v___y_6126_);
lean_dec(v___y_6125_);
lean_dec_ref(v___y_6124_);
lean_dec(v___y_6123_);
lean_dec_ref(v___y_6122_);
return v_res_6130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__4(lean_object* v_m_6131_, lean_object* v___x_6132_, uint8_t v_hasTrace_6133_, lean_object* v_cls_6134_, lean_object* v___y_6135_, lean_object* v___y_6136_, lean_object* v___y_6137_, lean_object* v___y_6138_, lean_object* v___y_6139_, lean_object* v___y_6140_){
_start:
{
lean_object* v_e_6143_; lean_object* v_onTrue_6144_; lean_object* v___y_6145_; lean_object* v___y_6146_; lean_object* v___y_6147_; lean_object* v___y_6148_; lean_object* v___y_6149_; lean_object* v___y_6150_; lean_object* v___x_6180_; 
v___x_6180_ = l_Lean_Meta_Sym_preprocessMVar(v_m_6131_, v___y_6135_, v___y_6136_, v___y_6137_, v___y_6138_, v___y_6139_, v___y_6140_);
if (lean_obj_tag(v___x_6180_) == 0)
{
lean_object* v_a_6181_; lean_object* v___x_6182_; 
v_a_6181_ = lean_ctor_get(v___x_6180_, 0);
lean_inc_n(v_a_6181_, 2);
lean_dec_ref_known(v___x_6180_, 1);
v___x_6182_ = l_Lean_MVarId_getType(v_a_6181_, v___y_6137_, v___y_6138_, v___y_6139_, v___y_6140_);
if (lean_obj_tag(v___x_6182_) == 0)
{
lean_object* v_a_6183_; lean_object* v___x_6184_; lean_object* v___x_6185_; uint8_t v___x_6186_; 
v_a_6183_ = lean_ctor_get(v___x_6182_, 0);
lean_inc(v_a_6183_);
lean_dec_ref_known(v___x_6182_, 1);
v___x_6184_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__4));
v___x_6185_ = lean_unsigned_to_nat(3u);
v___x_6186_ = l_Lean_Expr_isAppOfArity(v_a_6183_, v___x_6184_, v___x_6185_);
if (v___x_6186_ == 0)
{
lean_object* v___x_6187_; lean_object* v___x_6188_; lean_object* v___x_6189_; lean_object* v___x_6190_; 
lean_dec(v_a_6181_);
lean_dec(v_cls_6134_);
lean_dec_ref(v___x_6132_);
v___x_6187_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6);
v___x_6188_ = l_Lean_indentExpr(v_a_6183_);
v___x_6189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6189_, 0, v___x_6187_);
lean_ctor_set(v___x_6189_, 1, v___x_6188_);
v___x_6190_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_6189_, v___y_6137_, v___y_6138_, v___y_6139_, v___y_6140_);
return v___x_6190_;
}
else
{
lean_object* v___x_6191_; lean_object* v___x_6192_; lean_object* v___x_6193_; 
v___x_6191_ = l_Lean_Expr_appFn_x21(v_a_6183_);
lean_dec(v_a_6183_);
v___x_6192_ = l_Lean_Expr_appArg_x21(v___x_6191_);
lean_dec_ref(v___x_6191_);
lean_inc_ref(v___x_6192_);
v___x_6193_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_6192_, v___x_6132_, v___y_6135_, v___y_6136_, v___y_6137_, v___y_6138_, v___y_6139_, v___y_6140_);
if (lean_obj_tag(v___x_6193_) == 0)
{
lean_object* v_options_6194_; lean_object* v_a_6195_; lean_object* v_inheritedTraceOptions_6196_; uint8_t v_hasTrace_6197_; lean_object* v___x_6198_; lean_object* v___f_6199_; lean_object* v___y_6201_; lean_object* v___y_6202_; lean_object* v___y_6203_; lean_object* v___y_6204_; lean_object* v___y_6205_; lean_object* v___y_6206_; 
v_options_6194_ = lean_ctor_get(v___y_6139_, 2);
v_a_6195_ = lean_ctor_get(v___x_6193_, 0);
lean_inc(v_a_6195_);
lean_dec_ref_known(v___x_6193_, 1);
v_inheritedTraceOptions_6196_ = lean_ctor_get(v___y_6139_, 13);
v_hasTrace_6197_ = lean_ctor_get_uint8(v_options_6194_, sizeof(void*)*1);
v___x_6198_ = lean_box(v_hasTrace_6133_);
lean_inc(v_a_6181_);
v___f_6199_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__3___boxed), 9, 2);
lean_closure_set(v___f_6199_, 0, v_a_6181_);
lean_closure_set(v___f_6199_, 1, v___x_6198_);
if (v_hasTrace_6197_ == 0)
{
lean_dec(v_cls_6134_);
v___y_6201_ = v___y_6135_;
v___y_6202_ = v___y_6136_;
v___y_6203_ = v___y_6137_;
v___y_6204_ = v___y_6138_;
v___y_6205_ = v___y_6139_;
v___y_6206_ = v___y_6140_;
goto v___jp_6200_;
}
else
{
lean_object* v___x_6210_; lean_object* v___x_6211_; uint8_t v___x_6212_; 
v___x_6210_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__3));
lean_inc(v_cls_6134_);
v___x_6211_ = l_Lean_Name_append(v___x_6210_, v_cls_6134_);
v___x_6212_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6196_, v_options_6194_, v___x_6211_);
lean_dec(v___x_6211_);
if (v___x_6212_ == 0)
{
lean_dec(v_cls_6134_);
v___y_6201_ = v___y_6135_;
v___y_6202_ = v___y_6136_;
v___y_6203_ = v___y_6137_;
v___y_6204_ = v___y_6138_;
v___y_6205_ = v___y_6139_;
v___y_6206_ = v___y_6140_;
goto v___jp_6200_;
}
else
{
lean_object* v___x_6213_; lean_object* v___x_6214_; lean_object* v___x_6215_; lean_object* v___x_6216_; lean_object* v___x_6217_; lean_object* v___x_6218_; lean_object* v___x_6219_; lean_object* v___x_6220_; lean_object* v___x_6221_; 
v___x_6213_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8);
lean_inc_ref(v___x_6192_);
v___x_6214_ = l_Lean_indentExpr(v___x_6192_);
v___x_6215_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6215_, 0, v___x_6213_);
lean_ctor_set(v___x_6215_, 1, v___x_6214_);
v___x_6216_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_6217_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6217_, 0, v___x_6215_);
lean_ctor_set(v___x_6217_, 1, v___x_6216_);
v___x_6218_ = l_Lean_Meta_Sym_Simp_Result_getResultExpr(v___x_6192_, v_a_6195_);
v___x_6219_ = l_Lean_indentExpr(v___x_6218_);
v___x_6220_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6220_, 0, v___x_6217_);
lean_ctor_set(v___x_6220_, 1, v___x_6219_);
v___x_6221_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(v_cls_6134_, v___x_6220_, v___y_6137_, v___y_6138_, v___y_6139_, v___y_6140_);
if (lean_obj_tag(v___x_6221_) == 0)
{
lean_dec_ref_known(v___x_6221_, 1);
v___y_6201_ = v___y_6135_;
v___y_6202_ = v___y_6136_;
v___y_6203_ = v___y_6137_;
v___y_6204_ = v___y_6138_;
v___y_6205_ = v___y_6139_;
v___y_6206_ = v___y_6140_;
goto v___jp_6200_;
}
else
{
lean_dec_ref(v___f_6199_);
lean_dec(v_a_6195_);
lean_dec_ref(v___x_6192_);
lean_dec(v_a_6181_);
return v___x_6221_;
}
}
}
v___jp_6200_:
{
if (lean_obj_tag(v_a_6195_) == 0)
{
lean_dec_ref_known(v_a_6195_, 0);
lean_dec(v_a_6181_);
v_e_6143_ = v___x_6192_;
v_onTrue_6144_ = v___f_6199_;
v___y_6145_ = v___y_6201_;
v___y_6146_ = v___y_6202_;
v___y_6147_ = v___y_6203_;
v___y_6148_ = v___y_6204_;
v___y_6149_ = v___y_6205_;
v___y_6150_ = v___y_6206_;
goto v___jp_6142_;
}
else
{
lean_object* v_e_x27_6207_; lean_object* v_proof_6208_; lean_object* v___x_6209_; 
lean_dec_ref(v___f_6199_);
lean_dec_ref(v___x_6192_);
v_e_x27_6207_ = lean_ctor_get(v_a_6195_, 0);
lean_inc_ref(v_e_x27_6207_);
v_proof_6208_ = lean_ctor_get(v_a_6195_, 1);
lean_inc_ref(v_proof_6208_);
lean_dec_ref_known(v_a_6195_, 2);
v___x_6209_ = lean_alloc_closure((void*)(l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___boxed), 9, 2);
lean_closure_set(v___x_6209_, 0, v_a_6181_);
lean_closure_set(v___x_6209_, 1, v_proof_6208_);
v_e_6143_ = v_e_x27_6207_;
v_onTrue_6144_ = v___x_6209_;
v___y_6145_ = v___y_6201_;
v___y_6146_ = v___y_6202_;
v___y_6147_ = v___y_6203_;
v___y_6148_ = v___y_6204_;
v___y_6149_ = v___y_6205_;
v___y_6150_ = v___y_6206_;
goto v___jp_6142_;
}
}
}
else
{
lean_object* v_a_6222_; lean_object* v___x_6224_; uint8_t v_isShared_6225_; uint8_t v_isSharedCheck_6229_; 
lean_dec_ref(v___x_6192_);
lean_dec(v_a_6181_);
lean_dec(v_cls_6134_);
v_a_6222_ = lean_ctor_get(v___x_6193_, 0);
v_isSharedCheck_6229_ = !lean_is_exclusive(v___x_6193_);
if (v_isSharedCheck_6229_ == 0)
{
v___x_6224_ = v___x_6193_;
v_isShared_6225_ = v_isSharedCheck_6229_;
goto v_resetjp_6223_;
}
else
{
lean_inc(v_a_6222_);
lean_dec(v___x_6193_);
v___x_6224_ = lean_box(0);
v_isShared_6225_ = v_isSharedCheck_6229_;
goto v_resetjp_6223_;
}
v_resetjp_6223_:
{
lean_object* v___x_6227_; 
if (v_isShared_6225_ == 0)
{
v___x_6227_ = v___x_6224_;
goto v_reusejp_6226_;
}
else
{
lean_object* v_reuseFailAlloc_6228_; 
v_reuseFailAlloc_6228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6228_, 0, v_a_6222_);
v___x_6227_ = v_reuseFailAlloc_6228_;
goto v_reusejp_6226_;
}
v_reusejp_6226_:
{
return v___x_6227_;
}
}
}
}
}
else
{
lean_object* v_a_6230_; lean_object* v___x_6232_; uint8_t v_isShared_6233_; uint8_t v_isSharedCheck_6237_; 
lean_dec(v_a_6181_);
lean_dec(v_cls_6134_);
lean_dec_ref(v___x_6132_);
v_a_6230_ = lean_ctor_get(v___x_6182_, 0);
v_isSharedCheck_6237_ = !lean_is_exclusive(v___x_6182_);
if (v_isSharedCheck_6237_ == 0)
{
v___x_6232_ = v___x_6182_;
v_isShared_6233_ = v_isSharedCheck_6237_;
goto v_resetjp_6231_;
}
else
{
lean_inc(v_a_6230_);
lean_dec(v___x_6182_);
v___x_6232_ = lean_box(0);
v_isShared_6233_ = v_isSharedCheck_6237_;
goto v_resetjp_6231_;
}
v_resetjp_6231_:
{
lean_object* v___x_6235_; 
if (v_isShared_6233_ == 0)
{
v___x_6235_ = v___x_6232_;
goto v_reusejp_6234_;
}
else
{
lean_object* v_reuseFailAlloc_6236_; 
v_reuseFailAlloc_6236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6236_, 0, v_a_6230_);
v___x_6235_ = v_reuseFailAlloc_6236_;
goto v_reusejp_6234_;
}
v_reusejp_6234_:
{
return v___x_6235_;
}
}
}
}
else
{
lean_object* v_a_6238_; lean_object* v___x_6240_; uint8_t v_isShared_6241_; uint8_t v_isSharedCheck_6245_; 
lean_dec(v_cls_6134_);
lean_dec_ref(v___x_6132_);
v_a_6238_ = lean_ctor_get(v___x_6180_, 0);
v_isSharedCheck_6245_ = !lean_is_exclusive(v___x_6180_);
if (v_isSharedCheck_6245_ == 0)
{
v___x_6240_ = v___x_6180_;
v_isShared_6241_ = v_isSharedCheck_6245_;
goto v_resetjp_6239_;
}
else
{
lean_inc(v_a_6238_);
lean_dec(v___x_6180_);
v___x_6240_ = lean_box(0);
v_isShared_6241_ = v_isSharedCheck_6245_;
goto v_resetjp_6239_;
}
v_resetjp_6239_:
{
lean_object* v___x_6243_; 
if (v_isShared_6241_ == 0)
{
v___x_6243_ = v___x_6240_;
goto v_reusejp_6242_;
}
else
{
lean_object* v_reuseFailAlloc_6244_; 
v_reuseFailAlloc_6244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6244_, 0, v_a_6238_);
v___x_6243_ = v_reuseFailAlloc_6244_;
goto v_reusejp_6242_;
}
v_reusejp_6242_:
{
return v___x_6243_;
}
}
}
v___jp_6142_:
{
lean_object* v___x_6151_; 
v___x_6151_ = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(v_e_6143_, v___y_6145_);
if (lean_obj_tag(v___x_6151_) == 0)
{
lean_object* v_a_6152_; uint8_t v___x_6153_; 
v_a_6152_ = lean_ctor_get(v___x_6151_, 0);
lean_inc(v_a_6152_);
lean_dec_ref_known(v___x_6151_, 1);
v___x_6153_ = lean_unbox(v_a_6152_);
lean_dec(v_a_6152_);
if (v___x_6153_ == 0)
{
lean_object* v___x_6154_; 
lean_dec_ref(v_onTrue_6144_);
v___x_6154_ = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(v_e_6143_, v___y_6145_);
if (lean_obj_tag(v___x_6154_) == 0)
{
lean_object* v_a_6155_; uint8_t v___x_6156_; 
v_a_6155_ = lean_ctor_get(v___x_6154_, 0);
lean_inc(v_a_6155_);
lean_dec_ref_known(v___x_6154_, 1);
v___x_6156_ = lean_unbox(v_a_6155_);
lean_dec(v_a_6155_);
if (v___x_6156_ == 0)
{
lean_object* v___x_6157_; lean_object* v___x_6158_; lean_object* v___x_6159_; lean_object* v___x_6160_; 
v___x_6157_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1);
v___x_6158_ = l_Lean_indentExpr(v_e_6143_);
v___x_6159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6159_, 0, v___x_6157_);
lean_ctor_set(v___x_6159_, 1, v___x_6158_);
v___x_6160_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_6159_, v___y_6147_, v___y_6148_, v___y_6149_, v___y_6150_);
return v___x_6160_;
}
else
{
lean_object* v___x_6161_; lean_object* v___x_6162_; 
lean_dec_ref(v_e_6143_);
v___x_6161_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3);
v___x_6162_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_6161_, v___y_6147_, v___y_6148_, v___y_6149_, v___y_6150_);
return v___x_6162_;
}
}
else
{
lean_object* v_a_6163_; lean_object* v___x_6165_; uint8_t v_isShared_6166_; uint8_t v_isSharedCheck_6170_; 
lean_dec_ref(v_e_6143_);
v_a_6163_ = lean_ctor_get(v___x_6154_, 0);
v_isSharedCheck_6170_ = !lean_is_exclusive(v___x_6154_);
if (v_isSharedCheck_6170_ == 0)
{
v___x_6165_ = v___x_6154_;
v_isShared_6166_ = v_isSharedCheck_6170_;
goto v_resetjp_6164_;
}
else
{
lean_inc(v_a_6163_);
lean_dec(v___x_6154_);
v___x_6165_ = lean_box(0);
v_isShared_6166_ = v_isSharedCheck_6170_;
goto v_resetjp_6164_;
}
v_resetjp_6164_:
{
lean_object* v___x_6168_; 
if (v_isShared_6166_ == 0)
{
v___x_6168_ = v___x_6165_;
goto v_reusejp_6167_;
}
else
{
lean_object* v_reuseFailAlloc_6169_; 
v_reuseFailAlloc_6169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6169_, 0, v_a_6163_);
v___x_6168_ = v_reuseFailAlloc_6169_;
goto v_reusejp_6167_;
}
v_reusejp_6167_:
{
return v___x_6168_;
}
}
}
}
else
{
lean_object* v___x_6171_; 
lean_dec_ref(v_e_6143_);
lean_inc(v___y_6150_);
lean_inc_ref(v___y_6149_);
lean_inc(v___y_6148_);
lean_inc_ref(v___y_6147_);
lean_inc(v___y_6146_);
lean_inc_ref(v___y_6145_);
v___x_6171_ = lean_apply_7(v_onTrue_6144_, v___y_6145_, v___y_6146_, v___y_6147_, v___y_6148_, v___y_6149_, v___y_6150_, lean_box(0));
return v___x_6171_;
}
}
else
{
lean_object* v_a_6172_; lean_object* v___x_6174_; uint8_t v_isShared_6175_; uint8_t v_isSharedCheck_6179_; 
lean_dec_ref(v_onTrue_6144_);
lean_dec_ref(v_e_6143_);
v_a_6172_ = lean_ctor_get(v___x_6151_, 0);
v_isSharedCheck_6179_ = !lean_is_exclusive(v___x_6151_);
if (v_isSharedCheck_6179_ == 0)
{
v___x_6174_ = v___x_6151_;
v_isShared_6175_ = v_isSharedCheck_6179_;
goto v_resetjp_6173_;
}
else
{
lean_inc(v_a_6172_);
lean_dec(v___x_6151_);
v___x_6174_ = lean_box(0);
v_isShared_6175_ = v_isSharedCheck_6179_;
goto v_resetjp_6173_;
}
v_resetjp_6173_:
{
lean_object* v___x_6177_; 
if (v_isShared_6175_ == 0)
{
v___x_6177_ = v___x_6174_;
goto v_reusejp_6176_;
}
else
{
lean_object* v_reuseFailAlloc_6178_; 
v_reuseFailAlloc_6178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6178_, 0, v_a_6172_);
v___x_6177_ = v_reuseFailAlloc_6178_;
goto v_reusejp_6176_;
}
v_reusejp_6176_:
{
return v___x_6177_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__4___boxed(lean_object* v_m_6246_, lean_object* v___x_6247_, lean_object* v_hasTrace_6248_, lean_object* v_cls_6249_, lean_object* v___y_6250_, lean_object* v___y_6251_, lean_object* v___y_6252_, lean_object* v___y_6253_, lean_object* v___y_6254_, lean_object* v___y_6255_, lean_object* v___y_6256_){
_start:
{
uint8_t v_hasTrace_boxed_6257_; lean_object* v_res_6258_; 
v_hasTrace_boxed_6257_ = lean_unbox(v_hasTrace_6248_);
v_res_6258_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__4(v_m_6246_, v___x_6247_, v_hasTrace_boxed_6257_, v_cls_6249_, v___y_6250_, v___y_6251_, v___y_6252_, v___y_6253_, v___y_6254_, v___y_6255_);
lean_dec(v___y_6255_);
lean_dec_ref(v___y_6254_);
lean_dec(v___y_6253_);
lean_dec_ref(v___y_6252_);
lean_dec(v___y_6251_);
lean_dec_ref(v___y_6250_);
return v_res_6258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__6(lean_object* v_m_6259_, lean_object* v___x_6260_, uint8_t v___x_6261_, lean_object* v_cls_6262_, lean_object* v___y_6263_, lean_object* v___y_6264_, lean_object* v___y_6265_, lean_object* v___y_6266_, lean_object* v___y_6267_, lean_object* v___y_6268_){
_start:
{
lean_object* v_e_6271_; lean_object* v_onTrue_6272_; lean_object* v___y_6273_; lean_object* v___y_6274_; lean_object* v___y_6275_; lean_object* v___y_6276_; lean_object* v___y_6277_; lean_object* v___y_6278_; lean_object* v___x_6308_; 
v___x_6308_ = l_Lean_Meta_Sym_preprocessMVar(v_m_6259_, v___y_6263_, v___y_6264_, v___y_6265_, v___y_6266_, v___y_6267_, v___y_6268_);
if (lean_obj_tag(v___x_6308_) == 0)
{
lean_object* v_a_6309_; lean_object* v___x_6310_; 
v_a_6309_ = lean_ctor_get(v___x_6308_, 0);
lean_inc_n(v_a_6309_, 2);
lean_dec_ref_known(v___x_6308_, 1);
v___x_6310_ = l_Lean_MVarId_getType(v_a_6309_, v___y_6265_, v___y_6266_, v___y_6267_, v___y_6268_);
if (lean_obj_tag(v___x_6310_) == 0)
{
lean_object* v_a_6311_; lean_object* v___x_6312_; lean_object* v___x_6313_; uint8_t v___x_6314_; 
v_a_6311_ = lean_ctor_get(v___x_6310_, 0);
lean_inc(v_a_6311_);
lean_dec_ref_known(v___x_6310_, 1);
v___x_6312_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__4));
v___x_6313_ = lean_unsigned_to_nat(3u);
v___x_6314_ = l_Lean_Expr_isAppOfArity(v_a_6311_, v___x_6312_, v___x_6313_);
if (v___x_6314_ == 0)
{
lean_object* v___x_6315_; lean_object* v___x_6316_; lean_object* v___x_6317_; lean_object* v___x_6318_; 
lean_dec(v_a_6309_);
lean_dec(v_cls_6262_);
lean_dec_ref(v___x_6260_);
v___x_6315_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6);
v___x_6316_ = l_Lean_indentExpr(v_a_6311_);
v___x_6317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6317_, 0, v___x_6315_);
lean_ctor_set(v___x_6317_, 1, v___x_6316_);
v___x_6318_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_6317_, v___y_6265_, v___y_6266_, v___y_6267_, v___y_6268_);
return v___x_6318_;
}
else
{
lean_object* v___x_6319_; lean_object* v___x_6320_; lean_object* v___x_6321_; 
v___x_6319_ = l_Lean_Expr_appFn_x21(v_a_6311_);
lean_dec(v_a_6311_);
v___x_6320_ = l_Lean_Expr_appArg_x21(v___x_6319_);
lean_dec_ref(v___x_6319_);
lean_inc_ref(v___x_6320_);
v___x_6321_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_6320_, v___x_6260_, v___y_6263_, v___y_6264_, v___y_6265_, v___y_6266_, v___y_6267_, v___y_6268_);
if (lean_obj_tag(v___x_6321_) == 0)
{
lean_object* v_options_6322_; lean_object* v_a_6323_; lean_object* v_inheritedTraceOptions_6324_; uint8_t v_hasTrace_6325_; lean_object* v___x_6326_; lean_object* v___f_6327_; lean_object* v___y_6329_; lean_object* v___y_6330_; lean_object* v___y_6331_; lean_object* v___y_6332_; lean_object* v___y_6333_; lean_object* v___y_6334_; 
v_options_6322_ = lean_ctor_get(v___y_6267_, 2);
v_a_6323_ = lean_ctor_get(v___x_6321_, 0);
lean_inc(v_a_6323_);
lean_dec_ref_known(v___x_6321_, 1);
v_inheritedTraceOptions_6324_ = lean_ctor_get(v___y_6267_, 13);
v_hasTrace_6325_ = lean_ctor_get_uint8(v_options_6322_, sizeof(void*)*1);
v___x_6326_ = lean_box(v___x_6261_);
lean_inc(v_a_6309_);
v___f_6327_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0___boxed), 9, 2);
lean_closure_set(v___f_6327_, 0, v_a_6309_);
lean_closure_set(v___f_6327_, 1, v___x_6326_);
if (v_hasTrace_6325_ == 0)
{
lean_dec(v_cls_6262_);
v___y_6329_ = v___y_6263_;
v___y_6330_ = v___y_6264_;
v___y_6331_ = v___y_6265_;
v___y_6332_ = v___y_6266_;
v___y_6333_ = v___y_6267_;
v___y_6334_ = v___y_6268_;
goto v___jp_6328_;
}
else
{
lean_object* v___x_6338_; lean_object* v___x_6339_; uint8_t v___x_6340_; 
v___x_6338_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__3));
lean_inc(v_cls_6262_);
v___x_6339_ = l_Lean_Name_append(v___x_6338_, v_cls_6262_);
v___x_6340_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6324_, v_options_6322_, v___x_6339_);
lean_dec(v___x_6339_);
if (v___x_6340_ == 0)
{
lean_dec(v_cls_6262_);
v___y_6329_ = v___y_6263_;
v___y_6330_ = v___y_6264_;
v___y_6331_ = v___y_6265_;
v___y_6332_ = v___y_6266_;
v___y_6333_ = v___y_6267_;
v___y_6334_ = v___y_6268_;
goto v___jp_6328_;
}
else
{
lean_object* v___x_6341_; lean_object* v___x_6342_; lean_object* v___x_6343_; lean_object* v___x_6344_; lean_object* v___x_6345_; lean_object* v___x_6346_; lean_object* v___x_6347_; lean_object* v___x_6348_; lean_object* v___x_6349_; 
v___x_6341_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8);
lean_inc_ref(v___x_6320_);
v___x_6342_ = l_Lean_indentExpr(v___x_6320_);
v___x_6343_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6343_, 0, v___x_6341_);
lean_ctor_set(v___x_6343_, 1, v___x_6342_);
v___x_6344_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_6345_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6345_, 0, v___x_6343_);
lean_ctor_set(v___x_6345_, 1, v___x_6344_);
v___x_6346_ = l_Lean_Meta_Sym_Simp_Result_getResultExpr(v___x_6320_, v_a_6323_);
v___x_6347_ = l_Lean_indentExpr(v___x_6346_);
v___x_6348_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6348_, 0, v___x_6345_);
lean_ctor_set(v___x_6348_, 1, v___x_6347_);
v___x_6349_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(v_cls_6262_, v___x_6348_, v___y_6265_, v___y_6266_, v___y_6267_, v___y_6268_);
if (lean_obj_tag(v___x_6349_) == 0)
{
lean_dec_ref_known(v___x_6349_, 1);
v___y_6329_ = v___y_6263_;
v___y_6330_ = v___y_6264_;
v___y_6331_ = v___y_6265_;
v___y_6332_ = v___y_6266_;
v___y_6333_ = v___y_6267_;
v___y_6334_ = v___y_6268_;
goto v___jp_6328_;
}
else
{
lean_dec_ref(v___f_6327_);
lean_dec(v_a_6323_);
lean_dec_ref(v___x_6320_);
lean_dec(v_a_6309_);
return v___x_6349_;
}
}
}
v___jp_6328_:
{
if (lean_obj_tag(v_a_6323_) == 0)
{
lean_dec_ref_known(v_a_6323_, 0);
lean_dec(v_a_6309_);
v_e_6271_ = v___x_6320_;
v_onTrue_6272_ = v___f_6327_;
v___y_6273_ = v___y_6329_;
v___y_6274_ = v___y_6330_;
v___y_6275_ = v___y_6331_;
v___y_6276_ = v___y_6332_;
v___y_6277_ = v___y_6333_;
v___y_6278_ = v___y_6334_;
goto v___jp_6270_;
}
else
{
lean_object* v_e_x27_6335_; lean_object* v_proof_6336_; lean_object* v___x_6337_; 
lean_dec_ref(v___f_6327_);
lean_dec_ref(v___x_6320_);
v_e_x27_6335_ = lean_ctor_get(v_a_6323_, 0);
lean_inc_ref(v_e_x27_6335_);
v_proof_6336_ = lean_ctor_get(v_a_6323_, 1);
lean_inc_ref(v_proof_6336_);
lean_dec_ref_known(v_a_6323_, 2);
v___x_6337_ = lean_alloc_closure((void*)(l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___boxed), 9, 2);
lean_closure_set(v___x_6337_, 0, v_a_6309_);
lean_closure_set(v___x_6337_, 1, v_proof_6336_);
v_e_6271_ = v_e_x27_6335_;
v_onTrue_6272_ = v___x_6337_;
v___y_6273_ = v___y_6329_;
v___y_6274_ = v___y_6330_;
v___y_6275_ = v___y_6331_;
v___y_6276_ = v___y_6332_;
v___y_6277_ = v___y_6333_;
v___y_6278_ = v___y_6334_;
goto v___jp_6270_;
}
}
}
else
{
lean_object* v_a_6350_; lean_object* v___x_6352_; uint8_t v_isShared_6353_; uint8_t v_isSharedCheck_6357_; 
lean_dec_ref(v___x_6320_);
lean_dec(v_a_6309_);
lean_dec(v_cls_6262_);
v_a_6350_ = lean_ctor_get(v___x_6321_, 0);
v_isSharedCheck_6357_ = !lean_is_exclusive(v___x_6321_);
if (v_isSharedCheck_6357_ == 0)
{
v___x_6352_ = v___x_6321_;
v_isShared_6353_ = v_isSharedCheck_6357_;
goto v_resetjp_6351_;
}
else
{
lean_inc(v_a_6350_);
lean_dec(v___x_6321_);
v___x_6352_ = lean_box(0);
v_isShared_6353_ = v_isSharedCheck_6357_;
goto v_resetjp_6351_;
}
v_resetjp_6351_:
{
lean_object* v___x_6355_; 
if (v_isShared_6353_ == 0)
{
v___x_6355_ = v___x_6352_;
goto v_reusejp_6354_;
}
else
{
lean_object* v_reuseFailAlloc_6356_; 
v_reuseFailAlloc_6356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6356_, 0, v_a_6350_);
v___x_6355_ = v_reuseFailAlloc_6356_;
goto v_reusejp_6354_;
}
v_reusejp_6354_:
{
return v___x_6355_;
}
}
}
}
}
else
{
lean_object* v_a_6358_; lean_object* v___x_6360_; uint8_t v_isShared_6361_; uint8_t v_isSharedCheck_6365_; 
lean_dec(v_a_6309_);
lean_dec(v_cls_6262_);
lean_dec_ref(v___x_6260_);
v_a_6358_ = lean_ctor_get(v___x_6310_, 0);
v_isSharedCheck_6365_ = !lean_is_exclusive(v___x_6310_);
if (v_isSharedCheck_6365_ == 0)
{
v___x_6360_ = v___x_6310_;
v_isShared_6361_ = v_isSharedCheck_6365_;
goto v_resetjp_6359_;
}
else
{
lean_inc(v_a_6358_);
lean_dec(v___x_6310_);
v___x_6360_ = lean_box(0);
v_isShared_6361_ = v_isSharedCheck_6365_;
goto v_resetjp_6359_;
}
v_resetjp_6359_:
{
lean_object* v___x_6363_; 
if (v_isShared_6361_ == 0)
{
v___x_6363_ = v___x_6360_;
goto v_reusejp_6362_;
}
else
{
lean_object* v_reuseFailAlloc_6364_; 
v_reuseFailAlloc_6364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6364_, 0, v_a_6358_);
v___x_6363_ = v_reuseFailAlloc_6364_;
goto v_reusejp_6362_;
}
v_reusejp_6362_:
{
return v___x_6363_;
}
}
}
}
else
{
lean_object* v_a_6366_; lean_object* v___x_6368_; uint8_t v_isShared_6369_; uint8_t v_isSharedCheck_6373_; 
lean_dec(v_cls_6262_);
lean_dec_ref(v___x_6260_);
v_a_6366_ = lean_ctor_get(v___x_6308_, 0);
v_isSharedCheck_6373_ = !lean_is_exclusive(v___x_6308_);
if (v_isSharedCheck_6373_ == 0)
{
v___x_6368_ = v___x_6308_;
v_isShared_6369_ = v_isSharedCheck_6373_;
goto v_resetjp_6367_;
}
else
{
lean_inc(v_a_6366_);
lean_dec(v___x_6308_);
v___x_6368_ = lean_box(0);
v_isShared_6369_ = v_isSharedCheck_6373_;
goto v_resetjp_6367_;
}
v_resetjp_6367_:
{
lean_object* v___x_6371_; 
if (v_isShared_6369_ == 0)
{
v___x_6371_ = v___x_6368_;
goto v_reusejp_6370_;
}
else
{
lean_object* v_reuseFailAlloc_6372_; 
v_reuseFailAlloc_6372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6372_, 0, v_a_6366_);
v___x_6371_ = v_reuseFailAlloc_6372_;
goto v_reusejp_6370_;
}
v_reusejp_6370_:
{
return v___x_6371_;
}
}
}
v___jp_6270_:
{
lean_object* v___x_6279_; 
v___x_6279_ = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(v_e_6271_, v___y_6273_);
if (lean_obj_tag(v___x_6279_) == 0)
{
lean_object* v_a_6280_; uint8_t v___x_6281_; 
v_a_6280_ = lean_ctor_get(v___x_6279_, 0);
lean_inc(v_a_6280_);
lean_dec_ref_known(v___x_6279_, 1);
v___x_6281_ = lean_unbox(v_a_6280_);
lean_dec(v_a_6280_);
if (v___x_6281_ == 0)
{
lean_object* v___x_6282_; 
lean_dec_ref(v_onTrue_6272_);
v___x_6282_ = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(v_e_6271_, v___y_6273_);
if (lean_obj_tag(v___x_6282_) == 0)
{
lean_object* v_a_6283_; uint8_t v___x_6284_; 
v_a_6283_ = lean_ctor_get(v___x_6282_, 0);
lean_inc(v_a_6283_);
lean_dec_ref_known(v___x_6282_, 1);
v___x_6284_ = lean_unbox(v_a_6283_);
lean_dec(v_a_6283_);
if (v___x_6284_ == 0)
{
lean_object* v___x_6285_; lean_object* v___x_6286_; lean_object* v___x_6287_; lean_object* v___x_6288_; 
v___x_6285_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1);
v___x_6286_ = l_Lean_indentExpr(v_e_6271_);
v___x_6287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6287_, 0, v___x_6285_);
lean_ctor_set(v___x_6287_, 1, v___x_6286_);
v___x_6288_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_6287_, v___y_6275_, v___y_6276_, v___y_6277_, v___y_6278_);
return v___x_6288_;
}
else
{
lean_object* v___x_6289_; lean_object* v___x_6290_; 
lean_dec_ref(v_e_6271_);
v___x_6289_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3);
v___x_6290_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_6289_, v___y_6275_, v___y_6276_, v___y_6277_, v___y_6278_);
return v___x_6290_;
}
}
else
{
lean_object* v_a_6291_; lean_object* v___x_6293_; uint8_t v_isShared_6294_; uint8_t v_isSharedCheck_6298_; 
lean_dec_ref(v_e_6271_);
v_a_6291_ = lean_ctor_get(v___x_6282_, 0);
v_isSharedCheck_6298_ = !lean_is_exclusive(v___x_6282_);
if (v_isSharedCheck_6298_ == 0)
{
v___x_6293_ = v___x_6282_;
v_isShared_6294_ = v_isSharedCheck_6298_;
goto v_resetjp_6292_;
}
else
{
lean_inc(v_a_6291_);
lean_dec(v___x_6282_);
v___x_6293_ = lean_box(0);
v_isShared_6294_ = v_isSharedCheck_6298_;
goto v_resetjp_6292_;
}
v_resetjp_6292_:
{
lean_object* v___x_6296_; 
if (v_isShared_6294_ == 0)
{
v___x_6296_ = v___x_6293_;
goto v_reusejp_6295_;
}
else
{
lean_object* v_reuseFailAlloc_6297_; 
v_reuseFailAlloc_6297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6297_, 0, v_a_6291_);
v___x_6296_ = v_reuseFailAlloc_6297_;
goto v_reusejp_6295_;
}
v_reusejp_6295_:
{
return v___x_6296_;
}
}
}
}
else
{
lean_object* v___x_6299_; 
lean_dec_ref(v_e_6271_);
lean_inc(v___y_6278_);
lean_inc_ref(v___y_6277_);
lean_inc(v___y_6276_);
lean_inc_ref(v___y_6275_);
lean_inc(v___y_6274_);
lean_inc_ref(v___y_6273_);
v___x_6299_ = lean_apply_7(v_onTrue_6272_, v___y_6273_, v___y_6274_, v___y_6275_, v___y_6276_, v___y_6277_, v___y_6278_, lean_box(0));
return v___x_6299_;
}
}
else
{
lean_object* v_a_6300_; lean_object* v___x_6302_; uint8_t v_isShared_6303_; uint8_t v_isSharedCheck_6307_; 
lean_dec_ref(v_onTrue_6272_);
lean_dec_ref(v_e_6271_);
v_a_6300_ = lean_ctor_get(v___x_6279_, 0);
v_isSharedCheck_6307_ = !lean_is_exclusive(v___x_6279_);
if (v_isSharedCheck_6307_ == 0)
{
v___x_6302_ = v___x_6279_;
v_isShared_6303_ = v_isSharedCheck_6307_;
goto v_resetjp_6301_;
}
else
{
lean_inc(v_a_6300_);
lean_dec(v___x_6279_);
v___x_6302_ = lean_box(0);
v_isShared_6303_ = v_isSharedCheck_6307_;
goto v_resetjp_6301_;
}
v_resetjp_6301_:
{
lean_object* v___x_6305_; 
if (v_isShared_6303_ == 0)
{
v___x_6305_ = v___x_6302_;
goto v_reusejp_6304_;
}
else
{
lean_object* v_reuseFailAlloc_6306_; 
v_reuseFailAlloc_6306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6306_, 0, v_a_6300_);
v___x_6305_ = v_reuseFailAlloc_6306_;
goto v_reusejp_6304_;
}
v_reusejp_6304_:
{
return v___x_6305_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__6___boxed(lean_object* v_m_6374_, lean_object* v___x_6375_, lean_object* v___x_6376_, lean_object* v_cls_6377_, lean_object* v___y_6378_, lean_object* v___y_6379_, lean_object* v___y_6380_, lean_object* v___y_6381_, lean_object* v___y_6382_, lean_object* v___y_6383_, lean_object* v___y_6384_){
_start:
{
uint8_t v___x_25974__boxed_6385_; lean_object* v_res_6386_; 
v___x_25974__boxed_6385_ = lean_unbox(v___x_6376_);
v_res_6386_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__6(v_m_6374_, v___x_6375_, v___x_25974__boxed_6385_, v_cls_6377_, v___y_6378_, v___y_6379_, v___y_6380_, v___y_6381_, v___y_6382_, v___y_6383_);
lean_dec(v___y_6383_);
lean_dec_ref(v___y_6382_);
lean_dec(v___y_6381_);
lean_dec_ref(v___y_6380_);
lean_dec(v___y_6379_);
lean_dec_ref(v___y_6378_);
return v_res_6386_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2_spec__2(lean_object* v_e_6387_){
_start:
{
if (lean_obj_tag(v_e_6387_) == 0)
{
uint8_t v___x_6388_; 
v___x_6388_ = 2;
return v___x_6388_;
}
else
{
uint8_t v___x_6389_; 
v___x_6389_ = 0;
return v___x_6389_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2_spec__2___boxed(lean_object* v_e_6390_){
_start:
{
uint8_t v_res_6391_; lean_object* v_r_6392_; 
v_res_6391_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2_spec__2(v_e_6390_);
lean_dec_ref(v_e_6390_);
v_r_6392_ = lean_box(v_res_6391_);
return v_r_6392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2(lean_object* v_cls_6393_, uint8_t v_collapsed_6394_, lean_object* v_tag_6395_, lean_object* v_opts_6396_, uint8_t v_clsEnabled_6397_, lean_object* v_oldTraces_6398_, lean_object* v_msg_6399_, lean_object* v_resStartStop_6400_, lean_object* v___y_6401_, lean_object* v___y_6402_, lean_object* v___y_6403_, lean_object* v___y_6404_){
_start:
{
lean_object* v_fst_6406_; lean_object* v_snd_6407_; lean_object* v___y_6409_; lean_object* v___y_6410_; lean_object* v_data_6411_; lean_object* v_fst_6414_; lean_object* v_snd_6415_; lean_object* v___x_6416_; uint8_t v___x_6417_; lean_object* v___y_6419_; lean_object* v_a_6420_; uint8_t v___y_6435_; double v___y_6466_; 
v_fst_6406_ = lean_ctor_get(v_resStartStop_6400_, 0);
lean_inc(v_fst_6406_);
v_snd_6407_ = lean_ctor_get(v_resStartStop_6400_, 1);
lean_inc(v_snd_6407_);
lean_dec_ref(v_resStartStop_6400_);
v_fst_6414_ = lean_ctor_get(v_snd_6407_, 0);
lean_inc(v_fst_6414_);
v_snd_6415_ = lean_ctor_get(v_snd_6407_, 1);
lean_inc(v_snd_6415_);
lean_dec(v_snd_6407_);
v___x_6416_ = l_Lean_trace_profiler;
v___x_6417_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_6396_, v___x_6416_);
if (v___x_6417_ == 0)
{
v___y_6435_ = v___x_6417_;
goto v___jp_6434_;
}
else
{
lean_object* v___x_6471_; uint8_t v___x_6472_; 
v___x_6471_ = l_Lean_trace_profiler_useHeartbeats;
v___x_6472_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_6396_, v___x_6471_);
if (v___x_6472_ == 0)
{
lean_object* v___x_6473_; lean_object* v___x_6474_; double v___x_6475_; double v___x_6476_; double v___x_6477_; 
v___x_6473_ = l_Lean_trace_profiler_threshold;
v___x_6474_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_6396_, v___x_6473_);
v___x_6475_ = lean_float_of_nat(v___x_6474_);
v___x_6476_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2);
v___x_6477_ = lean_float_div(v___x_6475_, v___x_6476_);
v___y_6466_ = v___x_6477_;
goto v___jp_6465_;
}
else
{
lean_object* v___x_6478_; lean_object* v___x_6479_; double v___x_6480_; 
v___x_6478_ = l_Lean_trace_profiler_threshold;
v___x_6479_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_6396_, v___x_6478_);
v___x_6480_ = lean_float_of_nat(v___x_6479_);
v___y_6466_ = v___x_6480_;
goto v___jp_6465_;
}
}
v___jp_6408_:
{
lean_object* v___x_6412_; 
lean_inc(v___y_6410_);
v___x_6412_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__1(v_oldTraces_6398_, v_data_6411_, v___y_6410_, v___y_6409_, v___y_6401_, v___y_6402_, v___y_6403_, v___y_6404_);
if (lean_obj_tag(v___x_6412_) == 0)
{
lean_object* v___x_6413_; 
lean_dec_ref_known(v___x_6412_, 1);
v___x_6413_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg(v_fst_6406_);
return v___x_6413_;
}
else
{
lean_dec(v_fst_6406_);
return v___x_6412_;
}
}
v___jp_6418_:
{
uint8_t v_result_6421_; lean_object* v___x_6422_; lean_object* v___x_6423_; double v___x_6424_; lean_object* v_data_6425_; 
v_result_6421_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2_spec__2(v_fst_6406_);
v___x_6422_ = lean_box(v_result_6421_);
v___x_6423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6423_, 0, v___x_6422_);
v___x_6424_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_6395_);
lean_inc_ref(v___x_6423_);
lean_inc(v_cls_6393_);
v_data_6425_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_6425_, 0, v_cls_6393_);
lean_ctor_set(v_data_6425_, 1, v___x_6423_);
lean_ctor_set(v_data_6425_, 2, v_tag_6395_);
lean_ctor_set_float(v_data_6425_, sizeof(void*)*3, v___x_6424_);
lean_ctor_set_float(v_data_6425_, sizeof(void*)*3 + 8, v___x_6424_);
lean_ctor_set_uint8(v_data_6425_, sizeof(void*)*3 + 16, v_collapsed_6394_);
if (v___x_6417_ == 0)
{
lean_dec_ref_known(v___x_6423_, 1);
lean_dec(v_snd_6415_);
lean_dec(v_fst_6414_);
lean_dec_ref(v_tag_6395_);
lean_dec(v_cls_6393_);
v___y_6409_ = v_a_6420_;
v___y_6410_ = v___y_6419_;
v_data_6411_ = v_data_6425_;
goto v___jp_6408_;
}
else
{
lean_object* v_data_6426_; double v___x_6427_; double v___x_6428_; 
lean_dec_ref_known(v_data_6425_, 3);
v_data_6426_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_6426_, 0, v_cls_6393_);
lean_ctor_set(v_data_6426_, 1, v___x_6423_);
lean_ctor_set(v_data_6426_, 2, v_tag_6395_);
v___x_6427_ = lean_unbox_float(v_fst_6414_);
lean_dec(v_fst_6414_);
lean_ctor_set_float(v_data_6426_, sizeof(void*)*3, v___x_6427_);
v___x_6428_ = lean_unbox_float(v_snd_6415_);
lean_dec(v_snd_6415_);
lean_ctor_set_float(v_data_6426_, sizeof(void*)*3 + 8, v___x_6428_);
lean_ctor_set_uint8(v_data_6426_, sizeof(void*)*3 + 16, v_collapsed_6394_);
v___y_6409_ = v_a_6420_;
v___y_6410_ = v___y_6419_;
v_data_6411_ = v_data_6426_;
goto v___jp_6408_;
}
}
v___jp_6429_:
{
lean_object* v_ref_6430_; lean_object* v___x_6431_; 
v_ref_6430_ = lean_ctor_get(v___y_6403_, 5);
lean_inc(v___y_6404_);
lean_inc_ref(v___y_6403_);
lean_inc(v___y_6402_);
lean_inc_ref(v___y_6401_);
lean_inc(v_fst_6406_);
v___x_6431_ = lean_apply_6(v_msg_6399_, v_fst_6406_, v___y_6401_, v___y_6402_, v___y_6403_, v___y_6404_, lean_box(0));
if (lean_obj_tag(v___x_6431_) == 0)
{
lean_object* v_a_6432_; 
v_a_6432_ = lean_ctor_get(v___x_6431_, 0);
lean_inc(v_a_6432_);
lean_dec_ref_known(v___x_6431_, 1);
v___y_6419_ = v_ref_6430_;
v_a_6420_ = v_a_6432_;
goto v___jp_6418_;
}
else
{
lean_object* v___x_6433_; 
lean_dec_ref_known(v___x_6431_, 1);
v___x_6433_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1);
v___y_6419_ = v_ref_6430_;
v_a_6420_ = v___x_6433_;
goto v___jp_6418_;
}
}
v___jp_6434_:
{
if (v_clsEnabled_6397_ == 0)
{
if (v___y_6435_ == 0)
{
lean_object* v___x_6436_; lean_object* v_traceState_6437_; lean_object* v_env_6438_; lean_object* v_nextMacroScope_6439_; lean_object* v_ngen_6440_; lean_object* v_auxDeclNGen_6441_; lean_object* v_cache_6442_; lean_object* v_messages_6443_; lean_object* v_infoState_6444_; lean_object* v_snapshotTasks_6445_; lean_object* v___x_6447_; uint8_t v_isShared_6448_; uint8_t v_isSharedCheck_6464_; 
lean_dec(v_snd_6415_);
lean_dec(v_fst_6414_);
lean_dec_ref(v_msg_6399_);
lean_dec_ref(v_tag_6395_);
lean_dec(v_cls_6393_);
v___x_6436_ = lean_st_ref_take(v___y_6404_);
v_traceState_6437_ = lean_ctor_get(v___x_6436_, 4);
v_env_6438_ = lean_ctor_get(v___x_6436_, 0);
v_nextMacroScope_6439_ = lean_ctor_get(v___x_6436_, 1);
v_ngen_6440_ = lean_ctor_get(v___x_6436_, 2);
v_auxDeclNGen_6441_ = lean_ctor_get(v___x_6436_, 3);
v_cache_6442_ = lean_ctor_get(v___x_6436_, 5);
v_messages_6443_ = lean_ctor_get(v___x_6436_, 6);
v_infoState_6444_ = lean_ctor_get(v___x_6436_, 7);
v_snapshotTasks_6445_ = lean_ctor_get(v___x_6436_, 8);
v_isSharedCheck_6464_ = !lean_is_exclusive(v___x_6436_);
if (v_isSharedCheck_6464_ == 0)
{
v___x_6447_ = v___x_6436_;
v_isShared_6448_ = v_isSharedCheck_6464_;
goto v_resetjp_6446_;
}
else
{
lean_inc(v_snapshotTasks_6445_);
lean_inc(v_infoState_6444_);
lean_inc(v_messages_6443_);
lean_inc(v_cache_6442_);
lean_inc(v_traceState_6437_);
lean_inc(v_auxDeclNGen_6441_);
lean_inc(v_ngen_6440_);
lean_inc(v_nextMacroScope_6439_);
lean_inc(v_env_6438_);
lean_dec(v___x_6436_);
v___x_6447_ = lean_box(0);
v_isShared_6448_ = v_isSharedCheck_6464_;
goto v_resetjp_6446_;
}
v_resetjp_6446_:
{
uint64_t v_tid_6449_; lean_object* v_traces_6450_; lean_object* v___x_6452_; uint8_t v_isShared_6453_; uint8_t v_isSharedCheck_6463_; 
v_tid_6449_ = lean_ctor_get_uint64(v_traceState_6437_, sizeof(void*)*1);
v_traces_6450_ = lean_ctor_get(v_traceState_6437_, 0);
v_isSharedCheck_6463_ = !lean_is_exclusive(v_traceState_6437_);
if (v_isSharedCheck_6463_ == 0)
{
v___x_6452_ = v_traceState_6437_;
v_isShared_6453_ = v_isSharedCheck_6463_;
goto v_resetjp_6451_;
}
else
{
lean_inc(v_traces_6450_);
lean_dec(v_traceState_6437_);
v___x_6452_ = lean_box(0);
v_isShared_6453_ = v_isSharedCheck_6463_;
goto v_resetjp_6451_;
}
v_resetjp_6451_:
{
lean_object* v___x_6454_; lean_object* v___x_6456_; 
v___x_6454_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_6398_, v_traces_6450_);
lean_dec_ref(v_traces_6450_);
if (v_isShared_6453_ == 0)
{
lean_ctor_set(v___x_6452_, 0, v___x_6454_);
v___x_6456_ = v___x_6452_;
goto v_reusejp_6455_;
}
else
{
lean_object* v_reuseFailAlloc_6462_; 
v_reuseFailAlloc_6462_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6462_, 0, v___x_6454_);
lean_ctor_set_uint64(v_reuseFailAlloc_6462_, sizeof(void*)*1, v_tid_6449_);
v___x_6456_ = v_reuseFailAlloc_6462_;
goto v_reusejp_6455_;
}
v_reusejp_6455_:
{
lean_object* v___x_6458_; 
if (v_isShared_6448_ == 0)
{
lean_ctor_set(v___x_6447_, 4, v___x_6456_);
v___x_6458_ = v___x_6447_;
goto v_reusejp_6457_;
}
else
{
lean_object* v_reuseFailAlloc_6461_; 
v_reuseFailAlloc_6461_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6461_, 0, v_env_6438_);
lean_ctor_set(v_reuseFailAlloc_6461_, 1, v_nextMacroScope_6439_);
lean_ctor_set(v_reuseFailAlloc_6461_, 2, v_ngen_6440_);
lean_ctor_set(v_reuseFailAlloc_6461_, 3, v_auxDeclNGen_6441_);
lean_ctor_set(v_reuseFailAlloc_6461_, 4, v___x_6456_);
lean_ctor_set(v_reuseFailAlloc_6461_, 5, v_cache_6442_);
lean_ctor_set(v_reuseFailAlloc_6461_, 6, v_messages_6443_);
lean_ctor_set(v_reuseFailAlloc_6461_, 7, v_infoState_6444_);
lean_ctor_set(v_reuseFailAlloc_6461_, 8, v_snapshotTasks_6445_);
v___x_6458_ = v_reuseFailAlloc_6461_;
goto v_reusejp_6457_;
}
v_reusejp_6457_:
{
lean_object* v___x_6459_; lean_object* v___x_6460_; 
v___x_6459_ = lean_st_ref_set(v___y_6404_, v___x_6458_);
v___x_6460_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg(v_fst_6406_);
return v___x_6460_;
}
}
}
}
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
}
v___jp_6465_:
{
double v___x_6467_; double v___x_6468_; double v___x_6469_; uint8_t v___x_6470_; 
v___x_6467_ = lean_unbox_float(v_snd_6415_);
v___x_6468_ = lean_unbox_float(v_fst_6414_);
v___x_6469_ = lean_float_sub(v___x_6467_, v___x_6468_);
v___x_6470_ = lean_float_decLt(v___y_6466_, v___x_6469_);
v___y_6435_ = v___x_6470_;
goto v___jp_6434_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2___boxed(lean_object* v_cls_6481_, lean_object* v_collapsed_6482_, lean_object* v_tag_6483_, lean_object* v_opts_6484_, lean_object* v_clsEnabled_6485_, lean_object* v_oldTraces_6486_, lean_object* v_msg_6487_, lean_object* v_resStartStop_6488_, lean_object* v___y_6489_, lean_object* v___y_6490_, lean_object* v___y_6491_, lean_object* v___y_6492_, lean_object* v___y_6493_){
_start:
{
uint8_t v_collapsed_boxed_6494_; uint8_t v_clsEnabled_boxed_6495_; lean_object* v_res_6496_; 
v_collapsed_boxed_6494_ = lean_unbox(v_collapsed_6482_);
v_clsEnabled_boxed_6495_ = lean_unbox(v_clsEnabled_6485_);
v_res_6496_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2(v_cls_6481_, v_collapsed_boxed_6494_, v_tag_6483_, v_opts_6484_, v_clsEnabled_boxed_6495_, v_oldTraces_6486_, v_msg_6487_, v_resStartStop_6488_, v___y_6489_, v___y_6490_, v___y_6491_, v___y_6492_);
lean_dec(v___y_6492_);
lean_dec_ref(v___y_6491_);
lean_dec(v___y_6490_);
lean_dec_ref(v___y_6489_);
lean_dec_ref(v_opts_6484_);
return v_res_6496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal(lean_object* v_m_6498_, lean_object* v_a_6499_, lean_object* v_a_6500_, lean_object* v_a_6501_, lean_object* v_a_6502_){
_start:
{
lean_object* v_options_6504_; lean_object* v_inheritedTraceOptions_6505_; uint8_t v_hasTrace_6506_; lean_object* v_cls_6507_; 
v_options_6504_ = lean_ctor_get(v_a_6501_, 2);
v_inheritedTraceOptions_6505_ = lean_ctor_get(v_a_6501_, 13);
v_hasTrace_6506_ = lean_ctor_get_uint8(v_options_6504_, sizeof(void*)*1);
v_cls_6507_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0));
if (v_hasTrace_6506_ == 0)
{
lean_object* v___x_6508_; lean_object* v___x_6509_; lean_object* v___x_6510_; lean_object* v___x_6511_; lean_object* v___f_6512_; lean_object* v___x_6513_; 
v___x_6508_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_6509_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_6504_, v___x_6508_);
v___x_6510_ = lean_unsigned_to_nat(2u);
v___x_6511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6511_, 0, v___x_6509_);
lean_ctor_set(v___x_6511_, 1, v___x_6510_);
v___f_6512_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___boxed), 10, 3);
lean_closure_set(v___f_6512_, 0, v_m_6498_);
lean_closure_set(v___f_6512_, 1, v___x_6511_);
lean_closure_set(v___f_6512_, 2, v_cls_6507_);
v___x_6513_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_6512_, v_a_6499_, v_a_6500_, v_a_6501_, v_a_6502_);
return v___x_6513_;
}
else
{
lean_object* v___f_6514_; lean_object* v___x_6515_; lean_object* v___x_6516_; uint8_t v___x_6517_; lean_object* v___y_6519_; lean_object* v___y_6520_; lean_object* v_a_6521_; lean_object* v___y_6534_; lean_object* v___y_6535_; lean_object* v_a_6536_; 
v___f_6514_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___closed__0));
v___x_6515_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__1));
v___x_6516_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1);
v___x_6517_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6505_, v_options_6504_, v___x_6516_);
if (v___x_6517_ == 0)
{
lean_object* v___x_6598_; uint8_t v___x_6599_; 
v___x_6598_ = l_Lean_trace_profiler;
v___x_6599_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_6504_, v___x_6598_);
if (v___x_6599_ == 0)
{
lean_object* v___x_6600_; lean_object* v___x_6601_; lean_object* v___x_6602_; lean_object* v___x_6603_; lean_object* v___x_6604_; lean_object* v___f_6605_; lean_object* v___x_6606_; 
v___x_6600_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_6601_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_6504_, v___x_6600_);
v___x_6602_ = lean_unsigned_to_nat(2u);
v___x_6603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6603_, 0, v___x_6601_);
lean_ctor_set(v___x_6603_, 1, v___x_6602_);
v___x_6604_ = lean_box(v_hasTrace_6506_);
v___f_6605_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__4___boxed), 11, 4);
lean_closure_set(v___f_6605_, 0, v_m_6498_);
lean_closure_set(v___f_6605_, 1, v___x_6603_);
lean_closure_set(v___f_6605_, 2, v___x_6604_);
lean_closure_set(v___f_6605_, 3, v_cls_6507_);
v___x_6606_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_6605_, v_a_6499_, v_a_6500_, v_a_6501_, v_a_6502_);
return v___x_6606_;
}
else
{
goto v___jp_6545_;
}
}
else
{
goto v___jp_6545_;
}
v___jp_6518_:
{
lean_object* v___x_6522_; double v___x_6523_; double v___x_6524_; double v___x_6525_; double v___x_6526_; double v___x_6527_; lean_object* v___x_6528_; lean_object* v___x_6529_; lean_object* v___x_6530_; lean_object* v___x_6531_; lean_object* v___x_6532_; 
v___x_6522_ = lean_io_mono_nanos_now();
v___x_6523_ = lean_float_of_nat(v___y_6520_);
v___x_6524_ = lean_float_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9);
v___x_6525_ = lean_float_div(v___x_6523_, v___x_6524_);
v___x_6526_ = lean_float_of_nat(v___x_6522_);
v___x_6527_ = lean_float_div(v___x_6526_, v___x_6524_);
v___x_6528_ = lean_box_float(v___x_6525_);
v___x_6529_ = lean_box_float(v___x_6527_);
v___x_6530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6530_, 0, v___x_6528_);
lean_ctor_set(v___x_6530_, 1, v___x_6529_);
v___x_6531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6531_, 0, v_a_6521_);
lean_ctor_set(v___x_6531_, 1, v___x_6530_);
v___x_6532_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2(v_cls_6507_, v_hasTrace_6506_, v___x_6515_, v_options_6504_, v___x_6517_, v___y_6519_, v___f_6514_, v___x_6531_, v_a_6499_, v_a_6500_, v_a_6501_, v_a_6502_);
return v___x_6532_;
}
v___jp_6533_:
{
lean_object* v___x_6537_; double v___x_6538_; double v___x_6539_; lean_object* v___x_6540_; lean_object* v___x_6541_; lean_object* v___x_6542_; lean_object* v___x_6543_; lean_object* v___x_6544_; 
v___x_6537_ = lean_io_get_num_heartbeats();
v___x_6538_ = lean_float_of_nat(v___y_6535_);
v___x_6539_ = lean_float_of_nat(v___x_6537_);
v___x_6540_ = lean_box_float(v___x_6538_);
v___x_6541_ = lean_box_float(v___x_6539_);
v___x_6542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6542_, 0, v___x_6540_);
lean_ctor_set(v___x_6542_, 1, v___x_6541_);
v___x_6543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6543_, 0, v_a_6536_);
lean_ctor_set(v___x_6543_, 1, v___x_6542_);
v___x_6544_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2(v_cls_6507_, v_hasTrace_6506_, v___x_6515_, v_options_6504_, v___x_6517_, v___y_6534_, v___f_6514_, v___x_6543_, v_a_6499_, v_a_6500_, v_a_6501_, v_a_6502_);
return v___x_6544_;
}
v___jp_6545_:
{
lean_object* v___x_6546_; lean_object* v_a_6547_; lean_object* v___x_6548_; uint8_t v___x_6549_; 
v___x_6546_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg(v_a_6502_);
v_a_6547_ = lean_ctor_get(v___x_6546_, 0);
lean_inc(v_a_6547_);
lean_dec_ref(v___x_6546_);
v___x_6548_ = l_Lean_trace_profiler_useHeartbeats;
v___x_6549_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_6504_, v___x_6548_);
if (v___x_6549_ == 0)
{
lean_object* v___x_6550_; lean_object* v___x_6551_; lean_object* v___x_6552_; lean_object* v___x_6553_; lean_object* v___x_6554_; lean_object* v___x_6555_; lean_object* v___f_6556_; lean_object* v___x_6557_; 
v___x_6550_ = lean_io_mono_nanos_now();
v___x_6551_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_6552_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_6504_, v___x_6551_);
v___x_6553_ = lean_unsigned_to_nat(2u);
v___x_6554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6554_, 0, v___x_6552_);
lean_ctor_set(v___x_6554_, 1, v___x_6553_);
v___x_6555_ = lean_box(v_hasTrace_6506_);
v___f_6556_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__4___boxed), 11, 4);
lean_closure_set(v___f_6556_, 0, v_m_6498_);
lean_closure_set(v___f_6556_, 1, v___x_6554_);
lean_closure_set(v___f_6556_, 2, v___x_6555_);
lean_closure_set(v___f_6556_, 3, v_cls_6507_);
v___x_6557_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_6556_, v_a_6499_, v_a_6500_, v_a_6501_, v_a_6502_);
if (lean_obj_tag(v___x_6557_) == 0)
{
lean_object* v_a_6558_; lean_object* v___x_6560_; uint8_t v_isShared_6561_; uint8_t v_isSharedCheck_6565_; 
v_a_6558_ = lean_ctor_get(v___x_6557_, 0);
v_isSharedCheck_6565_ = !lean_is_exclusive(v___x_6557_);
if (v_isSharedCheck_6565_ == 0)
{
v___x_6560_ = v___x_6557_;
v_isShared_6561_ = v_isSharedCheck_6565_;
goto v_resetjp_6559_;
}
else
{
lean_inc(v_a_6558_);
lean_dec(v___x_6557_);
v___x_6560_ = lean_box(0);
v_isShared_6561_ = v_isSharedCheck_6565_;
goto v_resetjp_6559_;
}
v_resetjp_6559_:
{
lean_object* v___x_6563_; 
if (v_isShared_6561_ == 0)
{
lean_ctor_set_tag(v___x_6560_, 1);
v___x_6563_ = v___x_6560_;
goto v_reusejp_6562_;
}
else
{
lean_object* v_reuseFailAlloc_6564_; 
v_reuseFailAlloc_6564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6564_, 0, v_a_6558_);
v___x_6563_ = v_reuseFailAlloc_6564_;
goto v_reusejp_6562_;
}
v_reusejp_6562_:
{
v___y_6519_ = v_a_6547_;
v___y_6520_ = v___x_6550_;
v_a_6521_ = v___x_6563_;
goto v___jp_6518_;
}
}
}
else
{
lean_object* v_a_6566_; lean_object* v___x_6568_; uint8_t v_isShared_6569_; uint8_t v_isSharedCheck_6573_; 
v_a_6566_ = lean_ctor_get(v___x_6557_, 0);
v_isSharedCheck_6573_ = !lean_is_exclusive(v___x_6557_);
if (v_isSharedCheck_6573_ == 0)
{
v___x_6568_ = v___x_6557_;
v_isShared_6569_ = v_isSharedCheck_6573_;
goto v_resetjp_6567_;
}
else
{
lean_inc(v_a_6566_);
lean_dec(v___x_6557_);
v___x_6568_ = lean_box(0);
v_isShared_6569_ = v_isSharedCheck_6573_;
goto v_resetjp_6567_;
}
v_resetjp_6567_:
{
lean_object* v___x_6571_; 
if (v_isShared_6569_ == 0)
{
lean_ctor_set_tag(v___x_6568_, 0);
v___x_6571_ = v___x_6568_;
goto v_reusejp_6570_;
}
else
{
lean_object* v_reuseFailAlloc_6572_; 
v_reuseFailAlloc_6572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6572_, 0, v_a_6566_);
v___x_6571_ = v_reuseFailAlloc_6572_;
goto v_reusejp_6570_;
}
v_reusejp_6570_:
{
v___y_6519_ = v_a_6547_;
v___y_6520_ = v___x_6550_;
v_a_6521_ = v___x_6571_;
goto v___jp_6518_;
}
}
}
}
else
{
lean_object* v___x_6574_; lean_object* v___x_6575_; lean_object* v___x_6576_; lean_object* v___x_6577_; lean_object* v___x_6578_; lean_object* v___x_6579_; lean_object* v___f_6580_; lean_object* v___x_6581_; 
v___x_6574_ = lean_io_get_num_heartbeats();
v___x_6575_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_6576_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_6504_, v___x_6575_);
v___x_6577_ = lean_unsigned_to_nat(2u);
v___x_6578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6578_, 0, v___x_6576_);
lean_ctor_set(v___x_6578_, 1, v___x_6577_);
v___x_6579_ = lean_box(v___x_6549_);
v___f_6580_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__6___boxed), 11, 4);
lean_closure_set(v___f_6580_, 0, v_m_6498_);
lean_closure_set(v___f_6580_, 1, v___x_6578_);
lean_closure_set(v___f_6580_, 2, v___x_6579_);
lean_closure_set(v___f_6580_, 3, v_cls_6507_);
v___x_6581_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_6580_, v_a_6499_, v_a_6500_, v_a_6501_, v_a_6502_);
if (lean_obj_tag(v___x_6581_) == 0)
{
lean_object* v_a_6582_; lean_object* v___x_6584_; uint8_t v_isShared_6585_; uint8_t v_isSharedCheck_6589_; 
v_a_6582_ = lean_ctor_get(v___x_6581_, 0);
v_isSharedCheck_6589_ = !lean_is_exclusive(v___x_6581_);
if (v_isSharedCheck_6589_ == 0)
{
v___x_6584_ = v___x_6581_;
v_isShared_6585_ = v_isSharedCheck_6589_;
goto v_resetjp_6583_;
}
else
{
lean_inc(v_a_6582_);
lean_dec(v___x_6581_);
v___x_6584_ = lean_box(0);
v_isShared_6585_ = v_isSharedCheck_6589_;
goto v_resetjp_6583_;
}
v_resetjp_6583_:
{
lean_object* v___x_6587_; 
if (v_isShared_6585_ == 0)
{
lean_ctor_set_tag(v___x_6584_, 1);
v___x_6587_ = v___x_6584_;
goto v_reusejp_6586_;
}
else
{
lean_object* v_reuseFailAlloc_6588_; 
v_reuseFailAlloc_6588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6588_, 0, v_a_6582_);
v___x_6587_ = v_reuseFailAlloc_6588_;
goto v_reusejp_6586_;
}
v_reusejp_6586_:
{
v___y_6534_ = v_a_6547_;
v___y_6535_ = v___x_6574_;
v_a_6536_ = v___x_6587_;
goto v___jp_6533_;
}
}
}
else
{
lean_object* v_a_6590_; lean_object* v___x_6592_; uint8_t v_isShared_6593_; uint8_t v_isSharedCheck_6597_; 
v_a_6590_ = lean_ctor_get(v___x_6581_, 0);
v_isSharedCheck_6597_ = !lean_is_exclusive(v___x_6581_);
if (v_isSharedCheck_6597_ == 0)
{
v___x_6592_ = v___x_6581_;
v_isShared_6593_ = v_isSharedCheck_6597_;
goto v_resetjp_6591_;
}
else
{
lean_inc(v_a_6590_);
lean_dec(v___x_6581_);
v___x_6592_ = lean_box(0);
v_isShared_6593_ = v_isSharedCheck_6597_;
goto v_resetjp_6591_;
}
v_resetjp_6591_:
{
lean_object* v___x_6595_; 
if (v_isShared_6593_ == 0)
{
lean_ctor_set_tag(v___x_6592_, 0);
v___x_6595_ = v___x_6592_;
goto v_reusejp_6594_;
}
else
{
lean_object* v_reuseFailAlloc_6596_; 
v_reuseFailAlloc_6596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6596_, 0, v_a_6590_);
v___x_6595_ = v_reuseFailAlloc_6596_;
goto v_reusejp_6594_;
}
v_reusejp_6594_:
{
v___y_6534_ = v_a_6547_;
v___y_6535_ = v___x_6574_;
v_a_6536_ = v___x_6595_;
goto v___jp_6533_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___boxed(lean_object* v_m_6607_, lean_object* v_a_6608_, lean_object* v_a_6609_, lean_object* v_a_6610_, lean_object* v_a_6611_, lean_object* v_a_6612_){
_start:
{
lean_object* v_res_6613_; 
v_res_6613_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal(v_m_6607_, v_a_6608_, v_a_6609_, v_a_6610_, v_a_6611_);
lean_dec(v_a_6611_);
lean_dec_ref(v_a_6610_);
lean_dec(v_a_6609_);
lean_dec_ref(v_a_6608_);
return v_res_6613_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0(lean_object* v_00_u03b1_6614_, lean_object* v_msg_6615_, lean_object* v___y_6616_, lean_object* v___y_6617_, lean_object* v___y_6618_, lean_object* v___y_6619_, lean_object* v___y_6620_, lean_object* v___y_6621_){
_start:
{
lean_object* v___x_6623_; 
v___x_6623_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v_msg_6615_, v___y_6618_, v___y_6619_, v___y_6620_, v___y_6621_);
return v___x_6623_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___boxed(lean_object* v_00_u03b1_6624_, lean_object* v_msg_6625_, lean_object* v___y_6626_, lean_object* v___y_6627_, lean_object* v___y_6628_, lean_object* v___y_6629_, lean_object* v___y_6630_, lean_object* v___y_6631_, lean_object* v___y_6632_){
_start:
{
lean_object* v_res_6633_; 
v_res_6633_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0(v_00_u03b1_6624_, v_msg_6625_, v___y_6626_, v___y_6627_, v___y_6628_, v___y_6629_, v___y_6630_, v___y_6631_);
lean_dec(v___y_6631_);
lean_dec_ref(v___y_6630_);
lean_dec(v___y_6629_);
lean_dec_ref(v___y_6628_);
lean_dec(v___y_6627_);
lean_dec_ref(v___y_6626_);
return v_res_6633_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1(lean_object* v_cls_6634_, lean_object* v_msg_6635_, lean_object* v___y_6636_, lean_object* v___y_6637_, lean_object* v___y_6638_, lean_object* v___y_6639_, lean_object* v___y_6640_, lean_object* v___y_6641_){
_start:
{
lean_object* v___x_6643_; 
v___x_6643_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(v_cls_6634_, v_msg_6635_, v___y_6638_, v___y_6639_, v___y_6640_, v___y_6641_);
return v___x_6643_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___boxed(lean_object* v_cls_6644_, lean_object* v_msg_6645_, lean_object* v___y_6646_, lean_object* v___y_6647_, lean_object* v___y_6648_, lean_object* v___y_6649_, lean_object* v___y_6650_, lean_object* v___y_6651_, lean_object* v___y_6652_){
_start:
{
lean_object* v_res_6653_; 
v_res_6653_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1(v_cls_6644_, v_msg_6645_, v___y_6646_, v___y_6647_, v___y_6648_, v___y_6649_, v___y_6650_, v___y_6651_);
lean_dec(v___y_6651_);
lean_dec_ref(v___y_6650_);
lean_dec(v___y_6649_);
lean_dec_ref(v___y_6648_);
lean_dec(v___y_6647_);
lean_dec_ref(v___y_6646_);
return v_res_6653_;
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

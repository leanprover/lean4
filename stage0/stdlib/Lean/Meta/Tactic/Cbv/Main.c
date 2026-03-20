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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_isBoolTrueExpr___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_isBoolFalseExpr___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_preprocessMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(lean_object*);
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_reduceProj_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_inferType___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isArrow(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqOfHEq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_sym_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_io_mono_nanos_now();
double lean_float_div(double, double);
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
lean_object* l_Lean_Meta_Sym_Simp_Result_markAsDone(lean_object*);
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
lean_object* l_Lean_Core_instantiateValueLevelParams(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Tactic_Cbv_mkAppNS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Result_getResultExpr(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_SymM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
uint8_t l_Lean_Expr_isFalse(lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Sym_unfoldReducible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "cbv"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "warning"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(97, 111, 157, 173, 138, 2, 95, 98)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(151, 83, 180, 186, 68, 143, 69, 30)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "disable `cbv` usage warning"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Cbv"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(7, 212, 55, 101, 104, 194, 19, 213)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(113, 161, 104, 89, 81, 29, 125, 142)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(163, 5, 44, 111, 124, 235, 200, 112)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value_aux_4),((lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(173, 215, 55, 92, 108, 32, 177, 243)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbv_warning;
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Main_3491633865____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Main_3491633865____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_Main_3491633865____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "maxSteps"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_Main_3491633865____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_Main_3491633865____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_Main_3491633865____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(97, 111, 157, 173, 138, 2, 95, 98)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_Main_3491633865____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_Main_3491633865____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_Main_3491633865____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(101, 44, 76, 26, 207, 29, 243, 115)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_Main_3491633865____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_Main_3491633865____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_Main_3491633865____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "maximum number of steps for the `cbv` tactic"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_Main_3491633865____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_Main_3491633865____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_Main_3491633865____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_Main_3491633865____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_Main_3491633865____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_Main_3491633865____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_Main_3491633865____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_Main_3491633865____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_Main_3491633865____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_Main_3491633865____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_Main_3491633865____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(7, 212, 55, 101, 104, 194, 19, 213)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_Main_3491633865____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_Main_3491633865____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(113, 161, 104, 89, 81, 29, 125, 142)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_Main_3491633865____hygCtx___hyg_4__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_Main_3491633865____hygCtx___hyg_4__value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(163, 5, 44, 111, 124, 235, 200, 112)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_Main_3491633865____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_Main_3491633865____hygCtx___hyg_4__value_aux_4),((lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_Main_3491633865____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(79, 184, 28, 112, 238, 206, 34, 246)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_Main_3491633865____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_Main_3491633865____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Main_3491633865____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Main_3491633865____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "rewrite"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(180, 58, 216, 170, 2, 199, 127, 134)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__0_value),LEAN_SCALAR_PTR_LITERAL(174, 58, 109, 183, 100, 138, 243, 210)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "equation `"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`:"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__5;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "\n==>"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7;
static const lean_closure_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_dischargeNone___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__9_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "unfold"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(180, 58, 216, 170, 2, 199, 127, 134)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__0_value),LEAN_SCALAR_PTR_LITERAL(162, 17, 43, 156, 90, 102, 144, 138)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "unfold `"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Debug"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "reduce"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(167, 248, 27, 31, 3, 126, 142, 13)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(119, 140, 6, 58, 231, 192, 8, 160)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(246, 39, 251, 153, 6, 255, 160, 132)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(16, 195, 245, 152, 44, 204, 206, 86)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(200, 16, 126, 88, 211, 46, 70, 55)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "beta:"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__4;
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
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__4_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__3___boxed(lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__1;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__2 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__2_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__3;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___boxed(lean_object**);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__1_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__3;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__0;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "simplifyAppFn:"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "const `"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPre(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPre___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPost(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPost___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__2_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(180, 58, 216, 170, 2, 199, 127, 134)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "hypothesis `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "`: "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "`: no change"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__5;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4_spec__8_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4_spec__8___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4_spec__9___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mp"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___closed__2_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___closed__1_value),LEAN_SCALAR_PTR_LITERAL(183, 66, 254, 161, 210, 133, 94, 78)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___closed__3_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4_spec__9(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4_spec__8_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__6(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_33_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_isSharedCheck_33_ = !lean_is_exclusive(v_decl_2_);
if (v_isSharedCheck_33_ == 0)
{
v___x_8_ = v_decl_2_;
v_isShared_9_ = v_isSharedCheck_33_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_descr_6_);
lean_inc(v_defValue_5_);
lean_dec(v_decl_2_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_33_;
goto v_resetjp_7_;
}
v_resetjp_7_:
{
lean_object* v___x_10_; uint8_t v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_10_ = lean_alloc_ctor(1, 0, 1);
v___x_11_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_10_, 0, v___x_11_);
lean_inc(v_name_1_);
v___x_12_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_12_, 0, v_name_1_);
lean_ctor_set(v___x_12_, 1, v_ref_3_);
lean_ctor_set(v___x_12_, 2, v___x_10_);
lean_ctor_set(v___x_12_, 3, v_descr_6_);
lean_inc(v_name_1_);
v___x_13_ = lean_register_option(v_name_1_, v___x_12_);
if (lean_obj_tag(v___x_13_) == 0)
{
lean_object* v___x_15_; uint8_t v_isShared_16_; uint8_t v_isSharedCheck_23_; 
v_isSharedCheck_23_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_23_ == 0)
{
lean_object* v_unused_24_; 
v_unused_24_ = lean_ctor_get(v___x_13_, 0);
lean_dec(v_unused_24_);
v___x_15_ = v___x_13_;
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
else
{
lean_dec(v___x_13_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
v_resetjp_14_:
{
lean_object* v___x_18_; 
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 1, v_defValue_5_);
lean_ctor_set(v___x_8_, 0, v_name_1_);
v___x_18_ = v___x_8_;
goto v_reusejp_17_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v_name_1_);
lean_ctor_set(v_reuseFailAlloc_22_, 1, v_defValue_5_);
v___x_18_ = v_reuseFailAlloc_22_;
goto v_reusejp_17_;
}
v_reusejp_17_:
{
lean_object* v___x_20_; 
if (v_isShared_16_ == 0)
{
lean_ctor_set(v___x_15_, 0, v___x_18_);
v___x_20_ = v___x_15_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v___x_18_);
v___x_20_ = v_reuseFailAlloc_21_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
return v___x_20_;
}
}
}
}
else
{
lean_object* v_a_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_32_; 
lean_del_object(v___x_8_);
lean_dec(v_defValue_5_);
lean_dec(v_name_1_);
v_a_25_ = lean_ctor_get(v___x_13_, 0);
v_isSharedCheck_32_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_32_ == 0)
{
v___x_27_ = v___x_13_;
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_a_25_);
lean_dec(v___x_13_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v___x_30_; 
if (v_isShared_28_ == 0)
{
v___x_30_ = v___x_27_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v_a_25_);
v___x_30_ = v_reuseFailAlloc_31_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
return v___x_30_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_34_, lean_object* v_decl_35_, lean_object* v_ref_36_, lean_object* v_a_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Option_register___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__spec__0(v_name_34_, v_decl_35_, v_ref_36_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_61_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4_));
v___x_62_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4_));
v___x_63_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4_));
v___x_64_ = l_Lean_Option_register___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4__spec__0(v___x_61_, v___x_62_, v___x_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4____boxed(lean_object* v_a_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4_();
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Main_3491633865____hygCtx___hyg_4__spec__0(lean_object* v_name_67_, lean_object* v_decl_68_, lean_object* v_ref_69_){
_start:
{
lean_object* v_defValue_71_; lean_object* v_descr_72_; lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_98_; 
v_defValue_71_ = lean_ctor_get(v_decl_68_, 0);
v_descr_72_ = lean_ctor_get(v_decl_68_, 1);
v_isSharedCheck_98_ = !lean_is_exclusive(v_decl_68_);
if (v_isSharedCheck_98_ == 0)
{
v___x_74_ = v_decl_68_;
v_isShared_75_ = v_isSharedCheck_98_;
goto v_resetjp_73_;
}
else
{
lean_inc(v_descr_72_);
lean_inc(v_defValue_71_);
lean_dec(v_decl_68_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_98_;
goto v_resetjp_73_;
}
v_resetjp_73_:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
lean_inc(v_defValue_71_);
v___x_76_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_76_, 0, v_defValue_71_);
lean_inc(v_name_67_);
v___x_77_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_77_, 0, v_name_67_);
lean_ctor_set(v___x_77_, 1, v_ref_69_);
lean_ctor_set(v___x_77_, 2, v___x_76_);
lean_ctor_set(v___x_77_, 3, v_descr_72_);
lean_inc(v_name_67_);
v___x_78_ = lean_register_option(v_name_67_, v___x_77_);
if (lean_obj_tag(v___x_78_) == 0)
{
lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_88_; 
v_isSharedCheck_88_ = !lean_is_exclusive(v___x_78_);
if (v_isSharedCheck_88_ == 0)
{
lean_object* v_unused_89_; 
v_unused_89_ = lean_ctor_get(v___x_78_, 0);
lean_dec(v_unused_89_);
v___x_80_ = v___x_78_;
v_isShared_81_ = v_isSharedCheck_88_;
goto v_resetjp_79_;
}
else
{
lean_dec(v___x_78_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_88_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v___x_83_; 
if (v_isShared_75_ == 0)
{
lean_ctor_set(v___x_74_, 1, v_defValue_71_);
lean_ctor_set(v___x_74_, 0, v_name_67_);
v___x_83_ = v___x_74_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v_name_67_);
lean_ctor_set(v_reuseFailAlloc_87_, 1, v_defValue_71_);
v___x_83_ = v_reuseFailAlloc_87_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
lean_object* v___x_85_; 
if (v_isShared_81_ == 0)
{
lean_ctor_set(v___x_80_, 0, v___x_83_);
v___x_85_ = v___x_80_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v___x_83_);
v___x_85_ = v_reuseFailAlloc_86_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
return v___x_85_;
}
}
}
}
else
{
lean_object* v_a_90_; lean_object* v___x_92_; uint8_t v_isShared_93_; uint8_t v_isSharedCheck_97_; 
lean_del_object(v___x_74_);
lean_dec(v_defValue_71_);
lean_dec(v_name_67_);
v_a_90_ = lean_ctor_get(v___x_78_, 0);
v_isSharedCheck_97_ = !lean_is_exclusive(v___x_78_);
if (v_isSharedCheck_97_ == 0)
{
v___x_92_ = v___x_78_;
v_isShared_93_ = v_isSharedCheck_97_;
goto v_resetjp_91_;
}
else
{
lean_inc(v_a_90_);
lean_dec(v___x_78_);
v___x_92_ = lean_box(0);
v_isShared_93_ = v_isSharedCheck_97_;
goto v_resetjp_91_;
}
v_resetjp_91_:
{
lean_object* v___x_95_; 
if (v_isShared_93_ == 0)
{
v___x_95_ = v___x_92_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v_a_90_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Main_3491633865____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_99_, lean_object* v_decl_100_, lean_object* v_ref_101_, lean_object* v_a_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_Lean_Option_register___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Main_3491633865____hygCtx___hyg_4__spec__0(v_name_99_, v_decl_100_, v_ref_101_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Main_3491633865____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_120_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_Main_3491633865____hygCtx___hyg_4_));
v___x_121_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_Main_3491633865____hygCtx___hyg_4_));
v___x_122_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_Main_3491633865____hygCtx___hyg_4_));
v___x_123_ = l_Lean_Option_register___at___00Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Main_3491633865____hygCtx___hyg_4__spec__0(v___x_120_, v___x_121_, v___x_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Main_3491633865____hygCtx___hyg_4____boxed(lean_object* v_a_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Main_3491633865____hygCtx___hyg_4_();
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(lean_object* v_cls_129_, lean_object* v___y_130_){
_start:
{
lean_object* v_options_132_; uint8_t v_hasTrace_133_; 
v_options_132_ = lean_ctor_get(v___y_130_, 2);
v_hasTrace_133_ = lean_ctor_get_uint8(v_options_132_, sizeof(void*)*1);
if (v_hasTrace_133_ == 0)
{
lean_object* v___x_134_; lean_object* v___x_135_; 
lean_dec(v_cls_129_);
v___x_134_ = lean_box(v_hasTrace_133_);
v___x_135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
return v___x_135_;
}
else
{
lean_object* v_inheritedTraceOptions_136_; lean_object* v___x_137_; lean_object* v___x_138_; uint8_t v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v_inheritedTraceOptions_136_ = lean_ctor_get(v___y_130_, 13);
v___x_137_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__1));
v___x_138_ = l_Lean_Name_append(v___x_137_, v_cls_129_);
v___x_139_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_136_, v_options_132_, v___x_138_);
lean_dec(v___x_138_);
v___x_140_ = lean_box(v___x_139_);
v___x_141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_141_, 0, v___x_140_);
return v___x_141_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___boxed(lean_object* v_cls_142_, lean_object* v___y_143_, lean_object* v___y_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(v_cls_142_, v___y_143_);
lean_dec_ref(v___y_143_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0(lean_object* v_cls_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(v_cls_146_, v___y_154_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___boxed(lean_object* v_cls_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0(v_cls_158_, v___y_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
lean_dec(v___y_161_);
lean_dec_ref(v___y_160_);
lean_dec(v___y_159_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1_spec__1(lean_object* v_msgData_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_){
_start:
{
lean_object* v___x_176_; lean_object* v_env_177_; lean_object* v___x_178_; lean_object* v_mctx_179_; lean_object* v_lctx_180_; lean_object* v_options_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_176_ = lean_st_ref_get(v___y_174_);
v_env_177_ = lean_ctor_get(v___x_176_, 0);
lean_inc_ref(v_env_177_);
lean_dec(v___x_176_);
v___x_178_ = lean_st_ref_get(v___y_172_);
v_mctx_179_ = lean_ctor_get(v___x_178_, 0);
lean_inc_ref(v_mctx_179_);
lean_dec(v___x_178_);
v_lctx_180_ = lean_ctor_get(v___y_171_, 2);
v_options_181_ = lean_ctor_get(v___y_173_, 2);
lean_inc_ref(v_options_181_);
lean_inc_ref(v_lctx_180_);
v___x_182_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_182_, 0, v_env_177_);
lean_ctor_set(v___x_182_, 1, v_mctx_179_);
lean_ctor_set(v___x_182_, 2, v_lctx_180_);
lean_ctor_set(v___x_182_, 3, v_options_181_);
v___x_183_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
lean_ctor_set(v___x_183_, 1, v_msgData_170_);
v___x_184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1_spec__1___boxed(lean_object* v_msgData_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1_spec__1(v_msgData_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_);
lean_dec(v___y_189_);
lean_dec_ref(v___y_188_);
lean_dec(v___y_187_);
lean_dec_ref(v___y_186_);
return v_res_191_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_192_; double v___x_193_; 
v___x_192_ = lean_unsigned_to_nat(0u);
v___x_193_ = lean_float_of_nat(v___x_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg(lean_object* v_cls_197_, lean_object* v_msg_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_){
_start:
{
lean_object* v_ref_204_; lean_object* v___x_205_; lean_object* v_a_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_250_; 
v_ref_204_ = lean_ctor_get(v___y_201_, 5);
v___x_205_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1_spec__1(v_msg_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_);
v_a_206_ = lean_ctor_get(v___x_205_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_250_ == 0)
{
v___x_208_ = v___x_205_;
v_isShared_209_ = v_isSharedCheck_250_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_a_206_);
lean_dec(v___x_205_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_250_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_210_; lean_object* v_traceState_211_; lean_object* v_env_212_; lean_object* v_nextMacroScope_213_; lean_object* v_ngen_214_; lean_object* v_auxDeclNGen_215_; lean_object* v_cache_216_; lean_object* v_messages_217_; lean_object* v_infoState_218_; lean_object* v_snapshotTasks_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_249_; 
v___x_210_ = lean_st_ref_take(v___y_202_);
v_traceState_211_ = lean_ctor_get(v___x_210_, 4);
v_env_212_ = lean_ctor_get(v___x_210_, 0);
v_nextMacroScope_213_ = lean_ctor_get(v___x_210_, 1);
v_ngen_214_ = lean_ctor_get(v___x_210_, 2);
v_auxDeclNGen_215_ = lean_ctor_get(v___x_210_, 3);
v_cache_216_ = lean_ctor_get(v___x_210_, 5);
v_messages_217_ = lean_ctor_get(v___x_210_, 6);
v_infoState_218_ = lean_ctor_get(v___x_210_, 7);
v_snapshotTasks_219_ = lean_ctor_get(v___x_210_, 8);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_249_ == 0)
{
v___x_221_ = v___x_210_;
v_isShared_222_ = v_isSharedCheck_249_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_snapshotTasks_219_);
lean_inc(v_infoState_218_);
lean_inc(v_messages_217_);
lean_inc(v_cache_216_);
lean_inc(v_traceState_211_);
lean_inc(v_auxDeclNGen_215_);
lean_inc(v_ngen_214_);
lean_inc(v_nextMacroScope_213_);
lean_inc(v_env_212_);
lean_dec(v___x_210_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_249_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
uint64_t v_tid_223_; lean_object* v_traces_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_248_; 
v_tid_223_ = lean_ctor_get_uint64(v_traceState_211_, sizeof(void*)*1);
v_traces_224_ = lean_ctor_get(v_traceState_211_, 0);
v_isSharedCheck_248_ = !lean_is_exclusive(v_traceState_211_);
if (v_isSharedCheck_248_ == 0)
{
v___x_226_ = v_traceState_211_;
v_isShared_227_ = v_isSharedCheck_248_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_traces_224_);
lean_dec(v_traceState_211_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_248_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_228_; double v___x_229_; uint8_t v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_238_; 
v___x_228_ = lean_box(0);
v___x_229_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__0);
v___x_230_ = 0;
v___x_231_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__1));
v___x_232_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_232_, 0, v_cls_197_);
lean_ctor_set(v___x_232_, 1, v___x_228_);
lean_ctor_set(v___x_232_, 2, v___x_231_);
lean_ctor_set_float(v___x_232_, sizeof(void*)*3, v___x_229_);
lean_ctor_set_float(v___x_232_, sizeof(void*)*3 + 8, v___x_229_);
lean_ctor_set_uint8(v___x_232_, sizeof(void*)*3 + 16, v___x_230_);
v___x_233_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__2));
v___x_234_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_234_, 0, v___x_232_);
lean_ctor_set(v___x_234_, 1, v_a_206_);
lean_ctor_set(v___x_234_, 2, v___x_233_);
lean_inc(v_ref_204_);
v___x_235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_235_, 0, v_ref_204_);
lean_ctor_set(v___x_235_, 1, v___x_234_);
v___x_236_ = l_Lean_PersistentArray_push___redArg(v_traces_224_, v___x_235_);
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 0, v___x_236_);
v___x_238_ = v___x_226_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v___x_236_);
lean_ctor_set_uint64(v_reuseFailAlloc_247_, sizeof(void*)*1, v_tid_223_);
v___x_238_ = v_reuseFailAlloc_247_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
lean_object* v___x_240_; 
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 4, v___x_238_);
v___x_240_ = v___x_221_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_env_212_);
lean_ctor_set(v_reuseFailAlloc_246_, 1, v_nextMacroScope_213_);
lean_ctor_set(v_reuseFailAlloc_246_, 2, v_ngen_214_);
lean_ctor_set(v_reuseFailAlloc_246_, 3, v_auxDeclNGen_215_);
lean_ctor_set(v_reuseFailAlloc_246_, 4, v___x_238_);
lean_ctor_set(v_reuseFailAlloc_246_, 5, v_cache_216_);
lean_ctor_set(v_reuseFailAlloc_246_, 6, v_messages_217_);
lean_ctor_set(v_reuseFailAlloc_246_, 7, v_infoState_218_);
lean_ctor_set(v_reuseFailAlloc_246_, 8, v_snapshotTasks_219_);
v___x_240_ = v_reuseFailAlloc_246_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_244_; 
v___x_241_ = lean_st_ref_set(v___y_202_, v___x_240_);
v___x_242_ = lean_box(0);
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 0, v___x_242_);
v___x_244_ = v___x_208_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v___x_242_);
v___x_244_ = v_reuseFailAlloc_245_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
return v___x_244_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___boxed(lean_object* v_cls_251_, lean_object* v_msg_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg(v_cls_251_, v_msg_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_);
lean_dec(v___y_256_);
lean_dec_ref(v___y_255_);
lean_dec(v___y_254_);
lean_dec_ref(v___y_253_);
return v_res_258_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__3(void){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_266_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__2));
v___x_267_ = l_Lean_stringToMessageData(v___x_266_);
return v___x_267_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__5(void){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_269_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__4));
v___x_270_ = l_Lean_stringToMessageData(v___x_269_);
return v___x_270_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7(void){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__6));
v___x_273_ = l_Lean_stringToMessageData(v___x_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations(lean_object* v_e_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_){
_start:
{
uint8_t v___x_288_; 
v___x_288_ = l_Lean_Expr_isApp(v_e_277_);
if (v___x_288_ == 0)
{
lean_object* v___x_289_; lean_object* v___x_290_; 
lean_dec(v_a_286_);
lean_dec_ref(v_a_285_);
lean_dec(v_a_284_);
lean_dec_ref(v_a_283_);
lean_dec(v_a_282_);
lean_dec_ref(v_a_281_);
lean_dec(v_a_280_);
lean_dec_ref(v_a_279_);
lean_dec(v_a_278_);
lean_dec_ref(v_e_277_);
v___x_289_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_289_, 0, v___x_288_);
v___x_290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
return v___x_290_;
}
else
{
lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_291_ = l_Lean_Expr_getAppFn(v_e_277_);
v___x_292_ = l_Lean_Expr_constName_x3f(v___x_291_);
lean_dec_ref(v___x_291_);
if (lean_obj_tag(v___x_292_) == 1)
{
lean_object* v_val_293_; lean_object* v___y_295_; lean_object* v___x_337_; 
v_val_293_ = lean_ctor_get(v___x_292_, 0);
lean_inc(v_val_293_);
lean_dec_ref(v___x_292_);
lean_inc(v_a_286_);
lean_inc_ref(v_a_285_);
lean_inc(v_a_284_);
lean_inc_ref(v_a_283_);
lean_inc(v_val_293_);
v___x_337_ = l_Lean_Meta_Tactic_Cbv_getEqnTheorems(v_val_293_, v_a_283_, v_a_284_, v_a_285_, v_a_286_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v_a_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v_a_338_ = lean_ctor_get(v___x_337_, 0);
lean_inc(v_a_338_);
lean_dec_ref(v___x_337_);
v___x_339_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8));
lean_inc(v_a_286_);
lean_inc_ref(v_a_285_);
lean_inc(v_a_284_);
lean_inc_ref(v_a_283_);
lean_inc_ref(v_e_277_);
v___x_340_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_a_338_, v___x_339_, v_e_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_, v_a_286_);
if (lean_obj_tag(v___x_340_) == 0)
{
v___y_295_ = v___x_340_;
goto v___jp_294_;
}
else
{
lean_object* v_a_341_; uint8_t v___y_343_; uint8_t v___x_353_; 
v_a_341_ = lean_ctor_get(v___x_340_, 0);
lean_inc(v_a_341_);
v___x_353_ = l_Lean_Exception_isInterrupt(v_a_341_);
if (v___x_353_ == 0)
{
uint8_t v___x_354_; 
v___x_354_ = l_Lean_Exception_isRuntime(v_a_341_);
v___y_343_ = v___x_354_;
goto v___jp_342_;
}
else
{
lean_dec(v_a_341_);
v___y_343_ = v___x_353_;
goto v___jp_342_;
}
v___jp_342_:
{
if (v___y_343_ == 0)
{
lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_351_; 
lean_dec(v_val_293_);
lean_dec(v_a_286_);
lean_dec_ref(v_a_285_);
lean_dec(v_a_284_);
lean_dec_ref(v_a_283_);
lean_dec_ref(v_e_277_);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_340_);
if (v_isSharedCheck_351_ == 0)
{
lean_object* v_unused_352_; 
v_unused_352_ = lean_ctor_get(v___x_340_, 0);
lean_dec(v_unused_352_);
v___x_345_ = v___x_340_;
v_isShared_346_ = v_isSharedCheck_351_;
goto v_resetjp_344_;
}
else
{
lean_dec(v___x_340_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_351_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_347_; lean_object* v___x_349_; 
v___x_347_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_347_, 0, v___y_343_);
if (v_isShared_346_ == 0)
{
lean_ctor_set_tag(v___x_345_, 0);
lean_ctor_set(v___x_345_, 0, v___x_347_);
v___x_349_ = v___x_345_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v___x_347_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
else
{
v___y_295_ = v___x_340_;
goto v___jp_294_;
}
}
}
}
else
{
lean_object* v_a_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_362_; 
lean_dec(v_val_293_);
lean_dec(v_a_286_);
lean_dec_ref(v_a_285_);
lean_dec(v_a_284_);
lean_dec_ref(v_a_283_);
lean_dec(v_a_282_);
lean_dec_ref(v_a_281_);
lean_dec(v_a_280_);
lean_dec_ref(v_a_279_);
lean_dec(v_a_278_);
lean_dec_ref(v_e_277_);
v_a_355_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_362_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_362_ == 0)
{
v___x_357_ = v___x_337_;
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_a_355_);
lean_dec(v___x_337_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_360_; 
if (v_isShared_358_ == 0)
{
v___x_360_ = v___x_357_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_a_355_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
}
v___jp_294_:
{
if (lean_obj_tag(v___y_295_) == 0)
{
lean_object* v_a_296_; 
v_a_296_ = lean_ctor_get(v___y_295_, 0);
if (lean_obj_tag(v_a_296_) == 1)
{
lean_object* v_e_x27_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v_a_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_336_; 
lean_inc_ref(v_a_296_);
lean_dec_ref(v___y_295_);
v_e_x27_297_ = lean_ctor_get(v_a_296_, 0);
v___x_298_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__1));
v___x_299_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(v___x_298_, v_a_285_);
v_a_300_ = lean_ctor_get(v___x_299_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v___x_299_);
if (v_isSharedCheck_336_ == 0)
{
v___x_302_ = v___x_299_;
v_isShared_303_ = v_isSharedCheck_336_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_a_300_);
lean_dec(v___x_299_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_336_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
uint8_t v___x_304_; 
v___x_304_ = lean_unbox(v_a_300_);
lean_dec(v_a_300_);
if (v___x_304_ == 0)
{
lean_object* v___x_306_; 
lean_dec(v_val_293_);
lean_dec(v_a_286_);
lean_dec_ref(v_a_285_);
lean_dec(v_a_284_);
lean_dec_ref(v_a_283_);
lean_dec_ref(v_e_277_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 0, v_a_296_);
v___x_306_ = v___x_302_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_a_296_);
v___x_306_ = v_reuseFailAlloc_307_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
return v___x_306_;
}
}
else
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
lean_del_object(v___x_302_);
v___x_308_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__3, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__3_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__3);
v___x_309_ = l_Lean_MessageData_ofName(v_val_293_);
v___x_310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_310_, 0, v___x_308_);
lean_ctor_set(v___x_310_, 1, v___x_309_);
v___x_311_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__5, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__5_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__5);
v___x_312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_312_, 0, v___x_310_);
lean_ctor_set(v___x_312_, 1, v___x_311_);
v___x_313_ = l_Lean_indentExpr(v_e_277_);
v___x_314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_314_, 0, v___x_312_);
lean_ctor_set(v___x_314_, 1, v___x_313_);
v___x_315_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7);
v___x_316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_316_, 0, v___x_314_);
lean_ctor_set(v___x_316_, 1, v___x_315_);
lean_inc_ref(v_e_x27_297_);
v___x_317_ = l_Lean_indentExpr(v_e_x27_297_);
v___x_318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_316_);
lean_ctor_set(v___x_318_, 1, v___x_317_);
v___x_319_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg(v___x_298_, v___x_318_, v_a_283_, v_a_284_, v_a_285_, v_a_286_);
lean_dec(v_a_286_);
lean_dec_ref(v_a_285_);
lean_dec(v_a_284_);
lean_dec_ref(v_a_283_);
if (lean_obj_tag(v___x_319_) == 0)
{
lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_326_; 
v_isSharedCheck_326_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_326_ == 0)
{
lean_object* v_unused_327_; 
v_unused_327_ = lean_ctor_get(v___x_319_, 0);
lean_dec(v_unused_327_);
v___x_321_ = v___x_319_;
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
else
{
lean_dec(v___x_319_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_324_; 
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 0, v_a_296_);
v___x_324_ = v___x_321_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_a_296_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
else
{
lean_object* v_a_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_335_; 
lean_dec_ref(v_a_296_);
v_a_328_ = lean_ctor_get(v___x_319_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_335_ == 0)
{
v___x_330_ = v___x_319_;
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_a_328_);
lean_dec(v___x_319_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_333_; 
if (v_isShared_331_ == 0)
{
v___x_333_ = v___x_330_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_a_328_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
}
}
}
else
{
lean_dec(v_val_293_);
lean_dec(v_a_286_);
lean_dec_ref(v_a_285_);
lean_dec(v_a_284_);
lean_dec_ref(v_a_283_);
lean_dec_ref(v_e_277_);
return v___y_295_;
}
}
else
{
lean_dec(v_val_293_);
lean_dec(v_a_286_);
lean_dec_ref(v_a_285_);
lean_dec(v_a_284_);
lean_dec_ref(v_a_283_);
lean_dec_ref(v_e_277_);
return v___y_295_;
}
}
}
else
{
lean_object* v___x_363_; lean_object* v___x_364_; 
lean_dec(v___x_292_);
lean_dec(v_a_286_);
lean_dec_ref(v_a_285_);
lean_dec(v_a_284_);
lean_dec_ref(v_a_283_);
lean_dec(v_a_282_);
lean_dec_ref(v_a_281_);
lean_dec(v_a_280_);
lean_dec_ref(v_a_279_);
lean_dec(v_a_278_);
lean_dec_ref(v_e_277_);
v___x_363_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__9));
v___x_364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_364_, 0, v___x_363_);
return v___x_364_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___boxed(lean_object* v_e_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations(v_e_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_, v_a_374_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1(lean_object* v_cls_377_, lean_object* v_msg_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg(v_cls_377_, v_msg_378_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___boxed(lean_object* v_cls_390_, lean_object* v_msg_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1(v_cls_390_, v_msg_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
lean_dec(v___y_392_);
return v_res_402_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__3(void){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_410_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__2));
v___x_411_ = l_Lean_stringToMessageData(v___x_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold(lean_object* v_e_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_){
_start:
{
uint8_t v___x_423_; 
v___x_423_ = l_Lean_Expr_isApp(v_e_412_);
if (v___x_423_ == 0)
{
lean_object* v___x_424_; lean_object* v___x_425_; 
lean_dec(v_a_421_);
lean_dec_ref(v_a_420_);
lean_dec(v_a_419_);
lean_dec_ref(v_a_418_);
lean_dec(v_a_417_);
lean_dec_ref(v_a_416_);
lean_dec(v_a_415_);
lean_dec_ref(v_a_414_);
lean_dec(v_a_413_);
lean_dec_ref(v_e_412_);
v___x_424_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_424_, 0, v___x_423_);
v___x_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_425_, 0, v___x_424_);
return v___x_425_;
}
else
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = l_Lean_Expr_getAppFn(v_e_412_);
v___x_427_ = l_Lean_Expr_constName_x3f(v___x_426_);
lean_dec_ref(v___x_426_);
if (lean_obj_tag(v___x_427_) == 1)
{
lean_object* v_val_428_; lean_object* v___y_430_; lean_object* v___x_472_; 
v_val_428_ = lean_ctor_get(v___x_427_, 0);
lean_inc(v_val_428_);
lean_dec_ref(v___x_427_);
lean_inc(v_a_421_);
lean_inc_ref(v_a_420_);
lean_inc(v_a_419_);
lean_inc_ref(v_a_418_);
lean_inc(v_val_428_);
v___x_472_ = l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem(v_val_428_, v_a_418_, v_a_419_, v_a_420_, v_a_421_);
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_498_; 
v_a_473_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_498_ == 0)
{
v___x_475_ = v___x_472_;
v_isShared_476_ = v_isSharedCheck_498_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_dec(v___x_472_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_498_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
if (lean_obj_tag(v_a_473_) == 1)
{
lean_object* v_val_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
lean_del_object(v___x_475_);
v_val_477_ = lean_ctor_get(v_a_473_, 0);
lean_inc(v_val_477_);
lean_dec_ref(v_a_473_);
v___x_478_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8));
lean_inc(v_a_421_);
lean_inc_ref(v_a_420_);
lean_inc(v_a_419_);
lean_inc_ref(v_a_418_);
lean_inc_ref(v_e_412_);
v___x_479_ = l_Lean_Meta_Sym_Simp_Theorem_rewrite(v_val_477_, v_e_412_, v___x_478_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_);
if (lean_obj_tag(v___x_479_) == 0)
{
v___y_430_ = v___x_479_;
goto v___jp_429_;
}
else
{
lean_object* v_a_480_; uint8_t v___y_482_; uint8_t v___x_492_; 
v_a_480_ = lean_ctor_get(v___x_479_, 0);
lean_inc(v_a_480_);
v___x_492_ = l_Lean_Exception_isInterrupt(v_a_480_);
if (v___x_492_ == 0)
{
uint8_t v___x_493_; 
v___x_493_ = l_Lean_Exception_isRuntime(v_a_480_);
v___y_482_ = v___x_493_;
goto v___jp_481_;
}
else
{
lean_dec(v_a_480_);
v___y_482_ = v___x_492_;
goto v___jp_481_;
}
v___jp_481_:
{
if (v___y_482_ == 0)
{
lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_490_; 
lean_dec(v_val_428_);
lean_dec(v_a_421_);
lean_dec_ref(v_a_420_);
lean_dec(v_a_419_);
lean_dec_ref(v_a_418_);
lean_dec_ref(v_e_412_);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_490_ == 0)
{
lean_object* v_unused_491_; 
v_unused_491_ = lean_ctor_get(v___x_479_, 0);
lean_dec(v_unused_491_);
v___x_484_ = v___x_479_;
v_isShared_485_ = v_isSharedCheck_490_;
goto v_resetjp_483_;
}
else
{
lean_dec(v___x_479_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_490_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_486_; lean_object* v___x_488_; 
v___x_486_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_486_, 0, v___y_482_);
if (v_isShared_485_ == 0)
{
lean_ctor_set_tag(v___x_484_, 0);
lean_ctor_set(v___x_484_, 0, v___x_486_);
v___x_488_ = v___x_484_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v___x_486_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
else
{
v___y_430_ = v___x_479_;
goto v___jp_429_;
}
}
}
}
else
{
lean_object* v___x_494_; lean_object* v___x_496_; 
lean_dec(v_a_473_);
lean_dec(v_val_428_);
lean_dec(v_a_421_);
lean_dec_ref(v_a_420_);
lean_dec(v_a_419_);
lean_dec_ref(v_a_418_);
lean_dec(v_a_417_);
lean_dec_ref(v_a_416_);
lean_dec(v_a_415_);
lean_dec_ref(v_a_414_);
lean_dec(v_a_413_);
lean_dec_ref(v_e_412_);
v___x_494_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__9));
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 0, v___x_494_);
v___x_496_ = v___x_475_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v___x_494_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
}
else
{
lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_506_; 
lean_dec(v_val_428_);
lean_dec(v_a_421_);
lean_dec_ref(v_a_420_);
lean_dec(v_a_419_);
lean_dec_ref(v_a_418_);
lean_dec(v_a_417_);
lean_dec_ref(v_a_416_);
lean_dec(v_a_415_);
lean_dec_ref(v_a_414_);
lean_dec(v_a_413_);
lean_dec_ref(v_e_412_);
v_a_499_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_506_ == 0)
{
v___x_501_ = v___x_472_;
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v___x_472_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_506_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_504_; 
if (v_isShared_502_ == 0)
{
v___x_504_ = v___x_501_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_a_499_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
v___jp_429_:
{
if (lean_obj_tag(v___y_430_) == 0)
{
lean_object* v_a_431_; 
v_a_431_ = lean_ctor_get(v___y_430_, 0);
if (lean_obj_tag(v_a_431_) == 1)
{
lean_object* v_e_x27_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v_a_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_471_; 
lean_inc_ref(v_a_431_);
lean_dec_ref(v___y_430_);
v_e_x27_432_ = lean_ctor_get(v_a_431_, 0);
v___x_433_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__1));
v___x_434_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(v___x_433_, v_a_420_);
v_a_435_ = lean_ctor_get(v___x_434_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_471_ == 0)
{
v___x_437_ = v___x_434_;
v_isShared_438_ = v_isSharedCheck_471_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_a_435_);
lean_dec(v___x_434_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_471_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
uint8_t v___x_439_; 
v___x_439_ = lean_unbox(v_a_435_);
lean_dec(v_a_435_);
if (v___x_439_ == 0)
{
lean_object* v___x_441_; 
lean_dec(v_val_428_);
lean_dec(v_a_421_);
lean_dec_ref(v_a_420_);
lean_dec(v_a_419_);
lean_dec_ref(v_a_418_);
lean_dec_ref(v_e_412_);
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 0, v_a_431_);
v___x_441_ = v___x_437_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_a_431_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
else
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
lean_del_object(v___x_437_);
v___x_443_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__3, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__3_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__3);
v___x_444_ = l_Lean_MessageData_ofName(v_val_428_);
v___x_445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_445_, 0, v___x_443_);
lean_ctor_set(v___x_445_, 1, v___x_444_);
v___x_446_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__5, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__5_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__5);
v___x_447_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_447_, 0, v___x_445_);
lean_ctor_set(v___x_447_, 1, v___x_446_);
v___x_448_ = l_Lean_indentExpr(v_e_412_);
v___x_449_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_449_, 0, v___x_447_);
lean_ctor_set(v___x_449_, 1, v___x_448_);
v___x_450_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7);
v___x_451_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_451_, 0, v___x_449_);
lean_ctor_set(v___x_451_, 1, v___x_450_);
lean_inc_ref(v_e_x27_432_);
v___x_452_ = l_Lean_indentExpr(v_e_x27_432_);
v___x_453_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_453_, 0, v___x_451_);
lean_ctor_set(v___x_453_, 1, v___x_452_);
v___x_454_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg(v___x_433_, v___x_453_, v_a_418_, v_a_419_, v_a_420_, v_a_421_);
lean_dec(v_a_421_);
lean_dec_ref(v_a_420_);
lean_dec(v_a_419_);
lean_dec_ref(v_a_418_);
if (lean_obj_tag(v___x_454_) == 0)
{
lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_461_; 
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_454_);
if (v_isSharedCheck_461_ == 0)
{
lean_object* v_unused_462_; 
v_unused_462_ = lean_ctor_get(v___x_454_, 0);
lean_dec(v_unused_462_);
v___x_456_ = v___x_454_;
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
else
{
lean_dec(v___x_454_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_459_; 
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 0, v_a_431_);
v___x_459_ = v___x_456_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_a_431_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
else
{
lean_object* v_a_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_470_; 
lean_dec_ref(v_a_431_);
v_a_463_ = lean_ctor_get(v___x_454_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_454_);
if (v_isSharedCheck_470_ == 0)
{
v___x_465_ = v___x_454_;
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_a_463_);
lean_dec(v___x_454_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_468_; 
if (v_isShared_466_ == 0)
{
v___x_468_ = v___x_465_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_a_463_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
}
}
}
else
{
lean_dec(v_val_428_);
lean_dec(v_a_421_);
lean_dec_ref(v_a_420_);
lean_dec(v_a_419_);
lean_dec_ref(v_a_418_);
lean_dec_ref(v_e_412_);
return v___y_430_;
}
}
else
{
lean_dec(v_val_428_);
lean_dec(v_a_421_);
lean_dec_ref(v_a_420_);
lean_dec(v_a_419_);
lean_dec_ref(v_a_418_);
lean_dec_ref(v_e_412_);
return v___y_430_;
}
}
}
else
{
lean_object* v___x_507_; lean_object* v___x_508_; 
lean_dec(v___x_427_);
lean_dec(v_a_421_);
lean_dec_ref(v_a_420_);
lean_dec(v_a_419_);
lean_dec_ref(v_a_418_);
lean_dec(v_a_417_);
lean_dec_ref(v_a_416_);
lean_dec(v_a_415_);
lean_dec_ref(v_a_414_);
lean_dec(v_a_413_);
lean_dec_ref(v_e_412_);
v___x_507_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__9));
v___x_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_508_, 0, v___x_507_);
return v___x_508_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___boxed(lean_object* v_e_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold(v_e_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_);
return v_res_520_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__4(void){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3));
v___x_531_ = l_Lean_stringToMessageData(v___x_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg(lean_object* v_e_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_){
_start:
{
lean_object* v_new_539_; lean_object* v___x_540_; 
lean_inc_ref(v_e_532_);
v_new_539_ = l_Lean_Expr_headBeta(v_e_532_);
v___x_540_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_new_539_, v_a_533_);
if (lean_obj_tag(v___x_540_) == 0)
{
lean_object* v_a_541_; lean_object* v___y_543_; lean_object* v___y_544_; lean_object* v___y_545_; lean_object* v___y_546_; lean_object* v___y_547_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v_a_569_; uint8_t v___x_570_; 
v_a_541_ = lean_ctor_get(v___x_540_, 0);
lean_inc(v_a_541_);
lean_dec_ref(v___x_540_);
v___x_567_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2));
v___x_568_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(v___x_567_, v_a_536_);
v_a_569_ = lean_ctor_get(v___x_568_, 0);
lean_inc(v_a_569_);
lean_dec_ref(v___x_568_);
v___x_570_ = lean_unbox(v_a_569_);
lean_dec(v_a_569_);
if (v___x_570_ == 0)
{
lean_dec_ref(v_e_532_);
v___y_543_ = v_a_533_;
v___y_544_ = v_a_534_;
v___y_545_ = v_a_535_;
v___y_546_ = v_a_536_;
v___y_547_ = v_a_537_;
goto v___jp_542_;
}
else
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_571_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__4, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__4_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__4);
v___x_572_ = l_Lean_indentExpr(v_e_532_);
v___x_573_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_573_, 0, v___x_571_);
lean_ctor_set(v___x_573_, 1, v___x_572_);
v___x_574_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7);
v___x_575_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_575_, 0, v___x_573_);
lean_ctor_set(v___x_575_, 1, v___x_574_);
lean_inc(v_a_541_);
v___x_576_ = l_Lean_indentExpr(v_a_541_);
v___x_577_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_575_);
lean_ctor_set(v___x_577_, 1, v___x_576_);
v___x_578_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg(v___x_567_, v___x_577_, v_a_534_, v_a_535_, v_a_536_, v_a_537_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_dec_ref(v___x_578_);
v___y_543_ = v_a_533_;
v___y_544_ = v_a_534_;
v___y_545_ = v_a_535_;
v___y_546_ = v_a_536_;
v___y_547_ = v_a_537_;
goto v___jp_542_;
}
else
{
lean_object* v_a_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_586_; 
lean_dec(v_a_541_);
lean_dec(v_a_537_);
lean_dec_ref(v_a_536_);
lean_dec(v_a_535_);
lean_dec_ref(v_a_534_);
v_a_579_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_586_ == 0)
{
v___x_581_ = v___x_578_;
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_a_579_);
lean_dec(v___x_578_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_584_; 
if (v_isShared_582_ == 0)
{
v___x_584_ = v___x_581_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_a_579_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
}
}
v___jp_542_:
{
lean_object* v___x_548_; 
lean_inc(v_a_541_);
v___x_548_ = l_Lean_Meta_Sym_mkEqRefl___redArg(v_a_541_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_);
if (lean_obj_tag(v___x_548_) == 0)
{
lean_object* v_a_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_558_; 
v_a_549_ = lean_ctor_get(v___x_548_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_548_);
if (v_isSharedCheck_558_ == 0)
{
v___x_551_ = v___x_548_;
v_isShared_552_ = v_isSharedCheck_558_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_a_549_);
lean_dec(v___x_548_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_558_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
uint8_t v___x_553_; lean_object* v___x_554_; lean_object* v___x_556_; 
v___x_553_ = 0;
v___x_554_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_554_, 0, v_a_541_);
lean_ctor_set(v___x_554_, 1, v_a_549_);
lean_ctor_set_uint8(v___x_554_, sizeof(void*)*2, v___x_553_);
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 0, v___x_554_);
v___x_556_ = v___x_551_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v___x_554_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
else
{
lean_object* v_a_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_566_; 
lean_dec(v_a_541_);
v_a_559_ = lean_ctor_get(v___x_548_, 0);
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_548_);
if (v_isSharedCheck_566_ == 0)
{
v___x_561_ = v___x_548_;
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_a_559_);
lean_dec(v___x_548_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_564_; 
if (v_isShared_562_ == 0)
{
v___x_564_ = v___x_561_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_a_559_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
}
}
}
else
{
lean_object* v_a_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_594_; 
lean_dec(v_a_537_);
lean_dec_ref(v_a_536_);
lean_dec(v_a_535_);
lean_dec_ref(v_a_534_);
lean_dec_ref(v_e_532_);
v_a_587_ = lean_ctor_get(v___x_540_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_594_ == 0)
{
v___x_589_ = v___x_540_;
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_a_587_);
lean_dec(v___x_540_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_592_; 
if (v_isShared_590_ == 0)
{
v___x_592_ = v___x_589_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_a_587_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___boxed(lean_object* v_e_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg(v_e_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_);
lean_dec(v_a_596_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce(lean_object* v_e_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg(v_e_603_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___boxed(lean_object* v_e_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce(v_e_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_);
lean_dec(v_a_620_);
lean_dec_ref(v_a_619_);
lean_dec(v_a_618_);
lean_dec_ref(v_a_617_);
lean_dec(v_a_616_);
return v_res_626_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems___closed__1(void){
_start:
{
lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_628_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems___closed__0));
v___x_629_ = l_Lean_stringToMessageData(v___x_628_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems(lean_object* v_e_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_641_ = l_Lean_Expr_getAppFn(v_e_630_);
v___x_642_ = l_Lean_Expr_constName_x3f(v___x_641_);
lean_dec_ref(v___x_641_);
if (lean_obj_tag(v___x_642_) == 1)
{
lean_object* v_val_643_; lean_object* v___y_645_; lean_object* v___x_687_; 
v_val_643_ = lean_ctor_get(v___x_642_, 0);
lean_inc(v_val_643_);
lean_dec_ref(v___x_642_);
v___x_687_ = l_Lean_Meta_Tactic_Cbv_getCbvEvalLemmas___redArg(v_val_643_, v_a_639_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v_a_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_713_; 
v_a_688_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_713_ == 0)
{
v___x_690_ = v___x_687_;
v_isShared_691_ = v_isSharedCheck_713_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_a_688_);
lean_dec(v___x_687_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_713_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
if (lean_obj_tag(v_a_688_) == 1)
{
lean_object* v_val_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
lean_del_object(v___x_690_);
v_val_692_ = lean_ctor_get(v_a_688_, 0);
lean_inc(v_val_692_);
lean_dec_ref(v_a_688_);
v___x_693_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8));
lean_inc(v_a_639_);
lean_inc_ref(v_a_638_);
lean_inc(v_a_637_);
lean_inc_ref(v_a_636_);
lean_inc_ref(v_e_630_);
v___x_694_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_val_692_, v___x_693_, v_e_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_);
if (lean_obj_tag(v___x_694_) == 0)
{
v___y_645_ = v___x_694_;
goto v___jp_644_;
}
else
{
lean_object* v_a_695_; uint8_t v___y_697_; uint8_t v___x_707_; 
v_a_695_ = lean_ctor_get(v___x_694_, 0);
lean_inc(v_a_695_);
v___x_707_ = l_Lean_Exception_isInterrupt(v_a_695_);
if (v___x_707_ == 0)
{
uint8_t v___x_708_; 
v___x_708_ = l_Lean_Exception_isRuntime(v_a_695_);
v___y_697_ = v___x_708_;
goto v___jp_696_;
}
else
{
lean_dec(v_a_695_);
v___y_697_ = v___x_707_;
goto v___jp_696_;
}
v___jp_696_:
{
if (v___y_697_ == 0)
{
lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_705_; 
lean_dec(v_val_643_);
lean_dec(v_a_639_);
lean_dec_ref(v_a_638_);
lean_dec(v_a_637_);
lean_dec_ref(v_a_636_);
lean_dec_ref(v_e_630_);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_705_ == 0)
{
lean_object* v_unused_706_; 
v_unused_706_ = lean_ctor_get(v___x_694_, 0);
lean_dec(v_unused_706_);
v___x_699_ = v___x_694_;
v_isShared_700_ = v_isSharedCheck_705_;
goto v_resetjp_698_;
}
else
{
lean_dec(v___x_694_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_705_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_701_; lean_object* v___x_703_; 
v___x_701_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_701_, 0, v___y_697_);
if (v_isShared_700_ == 0)
{
lean_ctor_set_tag(v___x_699_, 0);
lean_ctor_set(v___x_699_, 0, v___x_701_);
v___x_703_ = v___x_699_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_701_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
else
{
v___y_645_ = v___x_694_;
goto v___jp_644_;
}
}
}
}
else
{
lean_object* v___x_709_; lean_object* v___x_711_; 
lean_dec(v_a_688_);
lean_dec(v_val_643_);
lean_dec(v_a_639_);
lean_dec_ref(v_a_638_);
lean_dec(v_a_637_);
lean_dec_ref(v_a_636_);
lean_dec(v_a_635_);
lean_dec_ref(v_a_634_);
lean_dec(v_a_633_);
lean_dec_ref(v_a_632_);
lean_dec(v_a_631_);
lean_dec_ref(v_e_630_);
v___x_709_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__9));
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 0, v___x_709_);
v___x_711_ = v___x_690_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v___x_709_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
else
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_721_; 
lean_dec(v_val_643_);
lean_dec(v_a_639_);
lean_dec_ref(v_a_638_);
lean_dec(v_a_637_);
lean_dec_ref(v_a_636_);
lean_dec(v_a_635_);
lean_dec_ref(v_a_634_);
lean_dec(v_a_633_);
lean_dec_ref(v_a_632_);
lean_dec(v_a_631_);
lean_dec_ref(v_e_630_);
v_a_714_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_721_ == 0)
{
v___x_716_ = v___x_687_;
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_687_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_719_; 
if (v_isShared_717_ == 0)
{
v___x_719_ = v___x_716_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_a_714_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
v___jp_644_:
{
if (lean_obj_tag(v___y_645_) == 0)
{
lean_object* v_a_646_; 
v_a_646_ = lean_ctor_get(v___y_645_, 0);
if (lean_obj_tag(v_a_646_) == 1)
{
lean_object* v_e_x27_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_686_; 
lean_inc_ref(v_a_646_);
lean_dec_ref(v___y_645_);
v_e_x27_647_ = lean_ctor_get(v_a_646_, 0);
v___x_648_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__1));
v___x_649_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(v___x_648_, v_a_638_);
v_a_650_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_686_ == 0)
{
v___x_652_ = v___x_649_;
v_isShared_653_ = v_isSharedCheck_686_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_dec(v___x_649_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_686_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
uint8_t v___x_654_; 
v___x_654_ = lean_unbox(v_a_650_);
lean_dec(v_a_650_);
if (v___x_654_ == 0)
{
lean_object* v___x_656_; 
lean_dec(v_val_643_);
lean_dec(v_a_639_);
lean_dec_ref(v_a_638_);
lean_dec(v_a_637_);
lean_dec_ref(v_a_636_);
lean_dec_ref(v_e_630_);
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 0, v_a_646_);
v___x_656_ = v___x_652_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_a_646_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
else
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
lean_del_object(v___x_652_);
v___x_658_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems___closed__1, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems___closed__1);
v___x_659_ = l_Lean_MessageData_ofName(v_val_643_);
v___x_660_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_660_, 0, v___x_658_);
lean_ctor_set(v___x_660_, 1, v___x_659_);
v___x_661_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__5, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__5_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__5);
v___x_662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_662_, 0, v___x_660_);
lean_ctor_set(v___x_662_, 1, v___x_661_);
v___x_663_ = l_Lean_indentExpr(v_e_630_);
v___x_664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_664_, 0, v___x_662_);
lean_ctor_set(v___x_664_, 1, v___x_663_);
v___x_665_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7);
v___x_666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_666_, 0, v___x_664_);
lean_ctor_set(v___x_666_, 1, v___x_665_);
lean_inc_ref(v_e_x27_647_);
v___x_667_ = l_Lean_indentExpr(v_e_x27_647_);
v___x_668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_668_, 0, v___x_666_);
lean_ctor_set(v___x_668_, 1, v___x_667_);
v___x_669_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg(v___x_648_, v___x_668_, v_a_636_, v_a_637_, v_a_638_, v_a_639_);
lean_dec(v_a_639_);
lean_dec_ref(v_a_638_);
lean_dec(v_a_637_);
lean_dec_ref(v_a_636_);
if (lean_obj_tag(v___x_669_) == 0)
{
lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_676_; 
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_676_ == 0)
{
lean_object* v_unused_677_; 
v_unused_677_ = lean_ctor_get(v___x_669_, 0);
lean_dec(v_unused_677_);
v___x_671_ = v___x_669_;
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
else
{
lean_dec(v___x_669_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_674_; 
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 0, v_a_646_);
v___x_674_ = v___x_671_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_a_646_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
else
{
lean_object* v_a_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_685_; 
lean_dec_ref(v_a_646_);
v_a_678_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_685_ == 0)
{
v___x_680_ = v___x_669_;
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_a_678_);
lean_dec(v___x_669_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_683_; 
if (v_isShared_681_ == 0)
{
v___x_683_ = v___x_680_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v_a_678_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
return v___x_683_;
}
}
}
}
}
}
else
{
lean_dec(v_val_643_);
lean_dec(v_a_639_);
lean_dec_ref(v_a_638_);
lean_dec(v_a_637_);
lean_dec_ref(v_a_636_);
lean_dec_ref(v_e_630_);
return v___y_645_;
}
}
else
{
lean_dec(v_val_643_);
lean_dec(v_a_639_);
lean_dec_ref(v_a_638_);
lean_dec(v_a_637_);
lean_dec_ref(v_a_636_);
lean_dec_ref(v_e_630_);
return v___y_645_;
}
}
}
else
{
lean_object* v___x_722_; lean_object* v___x_723_; 
lean_dec(v___x_642_);
lean_dec(v_a_639_);
lean_dec_ref(v_a_638_);
lean_dec(v_a_637_);
lean_dec_ref(v_a_636_);
lean_dec(v_a_635_);
lean_dec_ref(v_a_634_);
lean_dec(v_a_633_);
lean_dec_ref(v_a_632_);
lean_dec(v_a_631_);
lean_dec_ref(v_e_630_);
v___x_722_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__9));
v___x_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_723_, 0, v___x_722_);
return v___x_723_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems___boxed(lean_object* v_e_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems(v_e_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConstApp(lean_object* v_e_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_){
_start:
{
lean_object* v___x_747_; 
lean_inc(v_a_745_);
lean_inc_ref(v_a_744_);
lean_inc(v_a_743_);
lean_inc_ref(v_a_742_);
lean_inc(v_a_741_);
lean_inc_ref(v_a_740_);
lean_inc(v_a_739_);
lean_inc_ref(v_a_738_);
lean_inc(v_a_737_);
lean_inc_ref(v_e_736_);
v___x_747_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations(v_e_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_, v_a_745_);
if (lean_obj_tag(v___x_747_) == 0)
{
lean_object* v_a_748_; 
v_a_748_ = lean_ctor_get(v___x_747_, 0);
lean_inc(v_a_748_);
if (lean_obj_tag(v_a_748_) == 0)
{
uint8_t v_done_749_; 
v_done_749_ = lean_ctor_get_uint8(v_a_748_, 0);
lean_dec_ref(v_a_748_);
if (v_done_749_ == 0)
{
lean_object* v___x_750_; 
lean_dec_ref(v___x_747_);
v___x_750_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold(v_e_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_, v_a_745_);
return v___x_750_;
}
else
{
lean_dec(v_a_745_);
lean_dec_ref(v_a_744_);
lean_dec(v_a_743_);
lean_dec_ref(v_a_742_);
lean_dec(v_a_741_);
lean_dec_ref(v_a_740_);
lean_dec(v_a_739_);
lean_dec_ref(v_a_738_);
lean_dec(v_a_737_);
lean_dec_ref(v_e_736_);
return v___x_747_;
}
}
else
{
lean_dec_ref(v_a_748_);
lean_dec(v_a_745_);
lean_dec_ref(v_a_744_);
lean_dec(v_a_743_);
lean_dec_ref(v_a_742_);
lean_dec(v_a_741_);
lean_dec_ref(v_a_740_);
lean_dec(v_a_739_);
lean_dec_ref(v_a_738_);
lean_dec(v_a_737_);
lean_dec_ref(v_e_736_);
return v___x_747_;
}
}
else
{
lean_dec(v_a_745_);
lean_dec_ref(v_a_744_);
lean_dec(v_a_743_);
lean_dec_ref(v_a_742_);
lean_dec(v_a_741_);
lean_dec_ref(v_a_740_);
lean_dec(v_a_739_);
lean_dec_ref(v_a_738_);
lean_dec(v_a_737_);
lean_dec_ref(v_e_736_);
return v___x_747_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConstApp___boxed(lean_object* v_e_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConstApp(v_e_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_);
return v_res_762_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp___lam__0(lean_object* v_a_763_, uint8_t v_done_764_, lean_object* v_x_765_){
_start:
{
uint8_t v___x_766_; 
v___x_766_ = l_Lean_ConstantInfo_hasValue(v_a_763_, v_done_764_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp___lam__0___boxed(lean_object* v_a_767_, lean_object* v_done_768_, lean_object* v_x_769_){
_start:
{
uint8_t v_done_16222__boxed_770_; uint8_t v_res_771_; lean_object* v_r_772_; 
v_done_16222__boxed_770_ = lean_unbox(v_done_768_);
v_res_771_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp___lam__0(v_a_767_, v_done_16222__boxed_770_, v_x_769_);
lean_dec_ref(v_x_769_);
lean_dec_ref(v_a_767_);
v_r_772_ = lean_box(v_res_771_);
return v_r_772_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_773_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_774_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_775_, 0, v___x_774_);
return v___x_775_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_776_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_777_ = lean_unsigned_to_nat(0u);
v___x_778_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
lean_ctor_set(v___x_778_, 1, v___x_777_);
lean_ctor_set(v___x_778_, 2, v___x_777_);
lean_ctor_set(v___x_778_, 3, v___x_776_);
lean_ctor_set(v___x_778_, 4, v___x_776_);
lean_ctor_set(v___x_778_, 5, v___x_776_);
lean_ctor_set(v___x_778_, 6, v___x_776_);
lean_ctor_set(v___x_778_, 7, v___x_776_);
lean_ctor_set(v___x_778_, 8, v___x_776_);
return v___x_778_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_779_ = lean_unsigned_to_nat(32u);
v___x_780_ = lean_mk_empty_array_with_capacity(v___x_779_);
v___x_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
return v___x_781_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_782_ = ((size_t)5ULL);
v___x_783_ = lean_unsigned_to_nat(0u);
v___x_784_ = lean_unsigned_to_nat(32u);
v___x_785_ = lean_mk_empty_array_with_capacity(v___x_784_);
v___x_786_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_787_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_787_, 0, v___x_786_);
lean_ctor_set(v___x_787_, 1, v___x_785_);
lean_ctor_set(v___x_787_, 2, v___x_783_);
lean_ctor_set(v___x_787_, 3, v___x_783_);
lean_ctor_set_usize(v___x_787_, 4, v___x_782_);
return v___x_787_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_788_ = lean_box(1);
v___x_789_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_790_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_791_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_791_, 0, v___x_790_);
lean_ctor_set(v___x_791_, 1, v___x_789_);
lean_ctor_set(v___x_791_, 2, v___x_788_);
return v___x_791_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_793_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6));
v___x_794_ = l_Lean_stringToMessageData(v___x_793_);
return v___x_794_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_796_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8));
v___x_797_ = l_Lean_stringToMessageData(v___x_796_);
return v___x_797_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_799_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10));
v___x_800_ = l_Lean_stringToMessageData(v___x_799_);
return v___x_800_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_802_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12));
v___x_803_ = l_Lean_stringToMessageData(v___x_802_);
return v___x_803_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15(void){
_start:
{
lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_805_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14));
v___x_806_ = l_Lean_stringToMessageData(v___x_805_);
return v___x_806_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17(void){
_start:
{
lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_808_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16));
v___x_809_ = l_Lean_stringToMessageData(v___x_808_);
return v___x_809_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19(void){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_811_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18));
v___x_812_ = l_Lean_stringToMessageData(v___x_811_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_msg_813_, lean_object* v_declHint_814_, lean_object* v___y_815_){
_start:
{
lean_object* v___x_817_; lean_object* v_env_818_; uint8_t v___x_819_; 
v___x_817_ = lean_st_ref_get(v___y_815_);
v_env_818_ = lean_ctor_get(v___x_817_, 0);
lean_inc_ref(v_env_818_);
lean_dec(v___x_817_);
v___x_819_ = l_Lean_Name_isAnonymous(v_declHint_814_);
if (v___x_819_ == 0)
{
uint8_t v_isExporting_820_; 
v_isExporting_820_ = lean_ctor_get_uint8(v_env_818_, sizeof(void*)*8);
if (v_isExporting_820_ == 0)
{
lean_object* v___x_821_; 
lean_dec_ref(v_env_818_);
lean_dec(v_declHint_814_);
v___x_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_821_, 0, v_msg_813_);
return v___x_821_;
}
else
{
lean_object* v___x_822_; uint8_t v___x_823_; 
lean_inc_ref(v_env_818_);
v___x_822_ = l_Lean_Environment_setExporting(v_env_818_, v___x_819_);
lean_inc(v_declHint_814_);
lean_inc_ref(v___x_822_);
v___x_823_ = l_Lean_Environment_contains(v___x_822_, v_declHint_814_, v_isExporting_820_);
if (v___x_823_ == 0)
{
lean_object* v___x_824_; 
lean_dec_ref(v___x_822_);
lean_dec_ref(v_env_818_);
lean_dec(v_declHint_814_);
v___x_824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_824_, 0, v_msg_813_);
return v___x_824_;
}
else
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v_c_830_; lean_object* v___x_831_; 
v___x_825_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_826_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_827_ = l_Lean_Options_empty;
v___x_828_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_828_, 0, v___x_822_);
lean_ctor_set(v___x_828_, 1, v___x_825_);
lean_ctor_set(v___x_828_, 2, v___x_826_);
lean_ctor_set(v___x_828_, 3, v___x_827_);
lean_inc(v_declHint_814_);
v___x_829_ = l_Lean_MessageData_ofConstName(v_declHint_814_, v___x_819_);
v_c_830_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_830_, 0, v___x_828_);
lean_ctor_set(v_c_830_, 1, v___x_829_);
v___x_831_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_818_, v_declHint_814_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
lean_dec_ref(v_env_818_);
lean_dec(v_declHint_814_);
v___x_832_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_833_, 0, v___x_832_);
lean_ctor_set(v___x_833_, 1, v_c_830_);
v___x_834_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_835_, 0, v___x_833_);
lean_ctor_set(v___x_835_, 1, v___x_834_);
v___x_836_ = l_Lean_MessageData_note(v___x_835_);
v___x_837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_837_, 0, v_msg_813_);
lean_ctor_set(v___x_837_, 1, v___x_836_);
v___x_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
return v___x_838_;
}
else
{
lean_object* v_val_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_874_; 
v_val_839_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_874_ == 0)
{
v___x_841_ = v___x_831_;
v_isShared_842_ = v_isSharedCheck_874_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_val_839_);
lean_dec(v___x_831_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_874_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v_mod_846_; uint8_t v___x_847_; 
v___x_843_ = lean_box(0);
v___x_844_ = l_Lean_Environment_header(v_env_818_);
lean_dec_ref(v_env_818_);
v___x_845_ = l_Lean_EnvironmentHeader_moduleNames(v___x_844_);
v_mod_846_ = lean_array_get(v___x_843_, v___x_845_, v_val_839_);
lean_dec(v_val_839_);
lean_dec_ref(v___x_845_);
v___x_847_ = l_Lean_isPrivateName(v_declHint_814_);
lean_dec(v_declHint_814_);
if (v___x_847_ == 0)
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_859_; 
v___x_848_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_849_, 0, v___x_848_);
lean_ctor_set(v___x_849_, 1, v_c_830_);
v___x_850_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_851_, 0, v___x_849_);
lean_ctor_set(v___x_851_, 1, v___x_850_);
v___x_852_ = l_Lean_MessageData_ofName(v_mod_846_);
v___x_853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_853_, 0, v___x_851_);
lean_ctor_set(v___x_853_, 1, v___x_852_);
v___x_854_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_855_, 0, v___x_853_);
lean_ctor_set(v___x_855_, 1, v___x_854_);
v___x_856_ = l_Lean_MessageData_note(v___x_855_);
v___x_857_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_857_, 0, v_msg_813_);
lean_ctor_set(v___x_857_, 1, v___x_856_);
if (v_isShared_842_ == 0)
{
lean_ctor_set_tag(v___x_841_, 0);
lean_ctor_set(v___x_841_, 0, v___x_857_);
v___x_859_ = v___x_841_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v___x_857_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
else
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_872_; 
v___x_861_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_862_, 0, v___x_861_);
lean_ctor_set(v___x_862_, 1, v_c_830_);
v___x_863_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_862_);
lean_ctor_set(v___x_864_, 1, v___x_863_);
v___x_865_ = l_Lean_MessageData_ofName(v_mod_846_);
v___x_866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_866_, 0, v___x_864_);
lean_ctor_set(v___x_866_, 1, v___x_865_);
v___x_867_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
v___x_868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_868_, 0, v___x_866_);
lean_ctor_set(v___x_868_, 1, v___x_867_);
v___x_869_ = l_Lean_MessageData_note(v___x_868_);
v___x_870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_870_, 0, v_msg_813_);
lean_ctor_set(v___x_870_, 1, v___x_869_);
if (v_isShared_842_ == 0)
{
lean_ctor_set_tag(v___x_841_, 0);
lean_ctor_set(v___x_841_, 0, v___x_870_);
v___x_872_ = v___x_841_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_870_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_875_; 
lean_dec_ref(v_env_818_);
lean_dec(v_declHint_814_);
v___x_875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_875_, 0, v_msg_813_);
return v___x_875_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msg_876_, lean_object* v_declHint_877_, lean_object* v___y_878_, lean_object* v___y_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_876_, v_declHint_877_, v___y_878_);
lean_dec(v___y_878_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_msg_881_, lean_object* v_declHint_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
lean_object* v___x_893_; lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_903_; 
v___x_893_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_881_, v_declHint_882_, v___y_891_);
v_a_894_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_903_ == 0)
{
v___x_896_ = v___x_893_;
v_isShared_897_ = v_isSharedCheck_903_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_893_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_903_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_901_; 
v___x_898_ = l_Lean_unknownIdentifierMessageTag;
v___x_899_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_898_);
lean_ctor_set(v___x_899_, 1, v_a_894_);
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 0, v___x_899_);
v___x_901_ = v___x_896_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_msg_904_, lean_object* v_declHint_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_904_, v_declHint_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
lean_dec(v___y_906_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_msg_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v_ref_923_; lean_object* v___x_924_; lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_933_; 
v_ref_923_ = lean_ctor_get(v___y_920_, 5);
v___x_924_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1_spec__1(v_msg_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
v_a_925_ = lean_ctor_get(v___x_924_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_933_ == 0)
{
v___x_927_ = v___x_924_;
v_isShared_928_ = v_isSharedCheck_933_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_924_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_933_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_929_; lean_object* v___x_931_; 
lean_inc(v_ref_923_);
v___x_929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_929_, 0, v_ref_923_);
lean_ctor_set(v___x_929_, 1, v_a_925_);
if (v_isShared_928_ == 0)
{
lean_ctor_set_tag(v___x_927_, 1);
lean_ctor_set(v___x_927_, 0, v___x_929_);
v___x_931_ = v___x_927_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v___x_929_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_msg_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_941_, lean_object* v_msg_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_){
_start:
{
lean_object* v_fileName_953_; lean_object* v_fileMap_954_; lean_object* v_options_955_; lean_object* v_currRecDepth_956_; lean_object* v_maxRecDepth_957_; lean_object* v_ref_958_; lean_object* v_currNamespace_959_; lean_object* v_openDecls_960_; lean_object* v_initHeartbeats_961_; lean_object* v_maxHeartbeats_962_; lean_object* v_quotContext_963_; lean_object* v_currMacroScope_964_; uint8_t v_diag_965_; lean_object* v_cancelTk_x3f_966_; uint8_t v_suppressElabErrors_967_; lean_object* v_inheritedTraceOptions_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_977_; 
v_fileName_953_ = lean_ctor_get(v___y_950_, 0);
v_fileMap_954_ = lean_ctor_get(v___y_950_, 1);
v_options_955_ = lean_ctor_get(v___y_950_, 2);
v_currRecDepth_956_ = lean_ctor_get(v___y_950_, 3);
v_maxRecDepth_957_ = lean_ctor_get(v___y_950_, 4);
v_ref_958_ = lean_ctor_get(v___y_950_, 5);
v_currNamespace_959_ = lean_ctor_get(v___y_950_, 6);
v_openDecls_960_ = lean_ctor_get(v___y_950_, 7);
v_initHeartbeats_961_ = lean_ctor_get(v___y_950_, 8);
v_maxHeartbeats_962_ = lean_ctor_get(v___y_950_, 9);
v_quotContext_963_ = lean_ctor_get(v___y_950_, 10);
v_currMacroScope_964_ = lean_ctor_get(v___y_950_, 11);
v_diag_965_ = lean_ctor_get_uint8(v___y_950_, sizeof(void*)*14);
v_cancelTk_x3f_966_ = lean_ctor_get(v___y_950_, 12);
v_suppressElabErrors_967_ = lean_ctor_get_uint8(v___y_950_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_968_ = lean_ctor_get(v___y_950_, 13);
v_isSharedCheck_977_ = !lean_is_exclusive(v___y_950_);
if (v_isSharedCheck_977_ == 0)
{
v___x_970_ = v___y_950_;
v_isShared_971_ = v_isSharedCheck_977_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_inheritedTraceOptions_968_);
lean_inc(v_cancelTk_x3f_966_);
lean_inc(v_currMacroScope_964_);
lean_inc(v_quotContext_963_);
lean_inc(v_maxHeartbeats_962_);
lean_inc(v_initHeartbeats_961_);
lean_inc(v_openDecls_960_);
lean_inc(v_currNamespace_959_);
lean_inc(v_ref_958_);
lean_inc(v_maxRecDepth_957_);
lean_inc(v_currRecDepth_956_);
lean_inc(v_options_955_);
lean_inc(v_fileMap_954_);
lean_inc(v_fileName_953_);
lean_dec(v___y_950_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_977_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v_ref_972_; lean_object* v___x_974_; 
v_ref_972_ = l_Lean_replaceRef(v_ref_941_, v_ref_958_);
lean_dec(v_ref_958_);
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 5, v_ref_972_);
v___x_974_ = v___x_970_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_fileName_953_);
lean_ctor_set(v_reuseFailAlloc_976_, 1, v_fileMap_954_);
lean_ctor_set(v_reuseFailAlloc_976_, 2, v_options_955_);
lean_ctor_set(v_reuseFailAlloc_976_, 3, v_currRecDepth_956_);
lean_ctor_set(v_reuseFailAlloc_976_, 4, v_maxRecDepth_957_);
lean_ctor_set(v_reuseFailAlloc_976_, 5, v_ref_972_);
lean_ctor_set(v_reuseFailAlloc_976_, 6, v_currNamespace_959_);
lean_ctor_set(v_reuseFailAlloc_976_, 7, v_openDecls_960_);
lean_ctor_set(v_reuseFailAlloc_976_, 8, v_initHeartbeats_961_);
lean_ctor_set(v_reuseFailAlloc_976_, 9, v_maxHeartbeats_962_);
lean_ctor_set(v_reuseFailAlloc_976_, 10, v_quotContext_963_);
lean_ctor_set(v_reuseFailAlloc_976_, 11, v_currMacroScope_964_);
lean_ctor_set(v_reuseFailAlloc_976_, 12, v_cancelTk_x3f_966_);
lean_ctor_set(v_reuseFailAlloc_976_, 13, v_inheritedTraceOptions_968_);
lean_ctor_set_uint8(v_reuseFailAlloc_976_, sizeof(void*)*14, v_diag_965_);
lean_ctor_set_uint8(v_reuseFailAlloc_976_, sizeof(void*)*14 + 1, v_suppressElabErrors_967_);
v___x_974_ = v_reuseFailAlloc_976_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
lean_object* v___x_975_; 
v___x_975_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_942_, v___y_948_, v___y_949_, v___x_974_, v___y_951_);
lean_dec_ref(v___x_974_);
return v___x_975_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_978_, lean_object* v_msg_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_978_, v_msg_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_);
lean_dec(v___y_988_);
lean_dec(v___y_986_);
lean_dec_ref(v___y_985_);
lean_dec(v___y_984_);
lean_dec_ref(v___y_983_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
lean_dec(v___y_980_);
lean_dec(v_ref_978_);
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_991_, lean_object* v_msg_992_, lean_object* v_declHint_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v___x_1004_; lean_object* v_a_1005_; lean_object* v___x_1006_; 
v___x_1004_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_992_, v_declHint_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_);
v_a_1005_ = lean_ctor_get(v___x_1004_, 0);
lean_inc(v_a_1005_);
lean_dec_ref(v___x_1004_);
v___x_1006_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_991_, v_a_1005_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_1007_, lean_object* v_msg_1008_, lean_object* v_declHint_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
lean_object* v_res_1020_; 
v_res_1020_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1007_, v_msg_1008_, v_declHint_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_);
lean_dec(v___y_1018_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
lean_dec(v___y_1010_);
lean_dec(v_ref_1007_);
return v_res_1020_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1022_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1023_ = l_Lean_stringToMessageData(v___x_1022_);
return v___x_1023_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_1026_ = l_Lean_stringToMessageData(v___x_1025_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1027_, lean_object* v_constName_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
lean_object* v___x_1039_; uint8_t v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1039_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1040_ = 0;
lean_inc(v_constName_1028_);
v___x_1041_ = l_Lean_MessageData_ofConstName(v_constName_1028_, v___x_1040_);
v___x_1042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1039_);
lean_ctor_set(v___x_1042_, 1, v___x_1041_);
v___x_1043_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_1044_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1042_);
lean_ctor_set(v___x_1044_, 1, v___x_1043_);
v___x_1045_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1027_, v___x_1044_, v_constName_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1046_, lean_object* v_constName_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg(v_ref_1046_, v_constName_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_);
lean_dec(v___y_1056_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v___y_1048_);
lean_dec(v_ref_1046_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0___redArg(lean_object* v_constName_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_){
_start:
{
lean_object* v_ref_1070_; lean_object* v___x_1071_; 
v_ref_1070_ = lean_ctor_get(v___y_1067_, 5);
lean_inc(v_ref_1070_);
v___x_1071_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg(v_ref_1070_, v_constName_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
lean_dec(v_ref_1070_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_){
_start:
{
lean_object* v_res_1083_; 
v_res_1083_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0___redArg(v_constName_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_);
lean_dec(v___y_1081_);
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
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0(lean_object* v_constName_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_){
_start:
{
lean_object* v___x_1095_; lean_object* v_env_1096_; uint8_t v___x_1097_; lean_object* v___x_1098_; 
v___x_1095_ = lean_st_ref_get(v___y_1093_);
v_env_1096_ = lean_ctor_get(v___x_1095_, 0);
lean_inc_ref(v_env_1096_);
lean_dec(v___x_1095_);
v___x_1097_ = 0;
lean_inc(v_constName_1084_);
v___x_1098_ = l_Lean_Environment_find_x3f(v_env_1096_, v_constName_1084_, v___x_1097_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_object* v___x_1099_; 
v___x_1099_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0___redArg(v_constName_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_);
return v___x_1099_;
}
else
{
lean_object* v_val_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
lean_dec_ref(v___y_1092_);
lean_dec(v_constName_1084_);
v_val_1100_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v___x_1098_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_val_1100_);
lean_dec(v___x_1098_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
lean_ctor_set_tag(v___x_1102_, 0);
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_val_1100_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0___boxed(lean_object* v_constName_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0(v_constName_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
lean_dec(v___y_1117_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
lean_dec(v___y_1113_);
lean_dec_ref(v___y_1112_);
lean_dec(v___y_1111_);
lean_dec_ref(v___y_1110_);
lean_dec(v___y_1109_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp(lean_object* v_e_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_){
_start:
{
uint8_t v___x_1131_; 
v___x_1131_ = l_Lean_Expr_isApp(v_e_1120_);
if (v___x_1131_ == 0)
{
lean_object* v___x_1132_; lean_object* v___x_1133_; 
lean_dec(v_a_1129_);
lean_dec_ref(v_a_1128_);
lean_dec(v_a_1127_);
lean_dec_ref(v_a_1126_);
lean_dec(v_a_1125_);
lean_dec_ref(v_a_1124_);
lean_dec(v_a_1123_);
lean_dec_ref(v_a_1122_);
lean_dec(v_a_1121_);
lean_dec_ref(v_e_1120_);
v___x_1132_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_1132_, 0, v___x_1131_);
v___x_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1132_);
return v___x_1133_;
}
else
{
lean_object* v_fn_1134_; 
v_fn_1134_ = l_Lean_Expr_getAppFn(v_e_1120_);
switch(lean_obj_tag(v_fn_1134_))
{
case 4:
{
lean_object* v_declName_1135_; lean_object* v___x_1136_; 
v_declName_1135_ = lean_ctor_get(v_fn_1134_, 0);
lean_inc(v_declName_1135_);
lean_dec_ref(v_fn_1134_);
v___x_1136_ = l_Lean_Meta_Tactic_Cbv_isCbvOpaque___redArg(v_declName_1135_, v_a_1129_);
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_object* v_a_1137_; uint8_t v___x_1138_; 
v_a_1137_ = lean_ctor_get(v___x_1136_, 0);
lean_inc(v_a_1137_);
lean_dec_ref(v___x_1136_);
v___x_1138_ = lean_unbox(v_a_1137_);
lean_dec(v_a_1137_);
if (v___x_1138_ == 0)
{
lean_object* v___x_1139_; 
lean_inc_ref(v_a_1128_);
v___x_1139_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0(v_declName_1135_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v_a_1140_; lean_object* v___x_1141_; 
v_a_1140_ = lean_ctor_get(v___x_1139_, 0);
lean_inc(v_a_1140_);
lean_dec_ref(v___x_1139_);
lean_inc(v_a_1129_);
lean_inc_ref(v_a_1128_);
lean_inc(v_a_1127_);
lean_inc_ref(v_a_1126_);
lean_inc(v_a_1125_);
lean_inc_ref(v_a_1124_);
lean_inc(v_a_1123_);
lean_inc_ref(v_a_1122_);
lean_inc(v_a_1121_);
lean_inc_ref(v_e_1120_);
v___x_1141_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems(v_e_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v_a_1142_; 
v_a_1142_ = lean_ctor_get(v___x_1141_, 0);
lean_inc(v_a_1142_);
if (lean_obj_tag(v_a_1142_) == 0)
{
uint8_t v_done_1143_; 
v_done_1143_ = lean_ctor_get_uint8(v_a_1142_, 0);
lean_dec_ref(v_a_1142_);
if (v_done_1143_ == 0)
{
lean_object* v___x_1144_; lean_object* v___f_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
lean_dec_ref(v___x_1141_);
v___x_1144_ = lean_box(v_done_1143_);
v___f_1145_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1145_, 0, v_a_1140_);
lean_closure_set(v___f_1145_, 1, v___x_1144_);
v___x_1146_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConstApp___boxed), 11, 0);
lean_inc(v_a_1129_);
lean_inc_ref(v_a_1128_);
lean_inc(v_a_1127_);
lean_inc_ref(v_a_1126_);
lean_inc(v_a_1125_);
lean_inc_ref(v_a_1124_);
lean_inc(v_a_1123_);
lean_inc_ref(v_a_1122_);
lean_inc(v_a_1121_);
lean_inc_ref(v_e_1120_);
v___x_1147_ = l_Lean_Meta_Tactic_Cbv_guardSimproc(v___f_1145_, v___x_1146_, v_e_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_);
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v_a_1148_; 
v_a_1148_ = lean_ctor_get(v___x_1147_, 0);
lean_inc(v_a_1148_);
if (lean_obj_tag(v_a_1148_) == 0)
{
uint8_t v_done_1149_; 
v_done_1149_ = lean_ctor_get_uint8(v_a_1148_, 0);
lean_dec_ref(v_a_1148_);
if (v_done_1149_ == 0)
{
lean_object* v___x_1150_; 
lean_dec_ref(v___x_1147_);
v___x_1150_ = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher(v_e_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_);
lean_dec(v_a_1125_);
lean_dec_ref(v_a_1124_);
lean_dec(v_a_1123_);
lean_dec_ref(v_a_1122_);
lean_dec(v_a_1121_);
return v___x_1150_;
}
else
{
lean_dec(v_a_1129_);
lean_dec_ref(v_a_1128_);
lean_dec(v_a_1127_);
lean_dec_ref(v_a_1126_);
lean_dec(v_a_1125_);
lean_dec_ref(v_a_1124_);
lean_dec(v_a_1123_);
lean_dec_ref(v_a_1122_);
lean_dec(v_a_1121_);
lean_dec_ref(v_e_1120_);
return v___x_1147_;
}
}
else
{
lean_dec_ref(v_a_1148_);
lean_dec(v_a_1129_);
lean_dec_ref(v_a_1128_);
lean_dec(v_a_1127_);
lean_dec_ref(v_a_1126_);
lean_dec(v_a_1125_);
lean_dec_ref(v_a_1124_);
lean_dec(v_a_1123_);
lean_dec_ref(v_a_1122_);
lean_dec(v_a_1121_);
lean_dec_ref(v_e_1120_);
return v___x_1147_;
}
}
else
{
lean_dec(v_a_1129_);
lean_dec_ref(v_a_1128_);
lean_dec(v_a_1127_);
lean_dec_ref(v_a_1126_);
lean_dec(v_a_1125_);
lean_dec_ref(v_a_1124_);
lean_dec(v_a_1123_);
lean_dec_ref(v_a_1122_);
lean_dec(v_a_1121_);
lean_dec_ref(v_e_1120_);
return v___x_1147_;
}
}
else
{
lean_dec(v_a_1140_);
lean_dec(v_a_1129_);
lean_dec_ref(v_a_1128_);
lean_dec(v_a_1127_);
lean_dec_ref(v_a_1126_);
lean_dec(v_a_1125_);
lean_dec_ref(v_a_1124_);
lean_dec(v_a_1123_);
lean_dec_ref(v_a_1122_);
lean_dec(v_a_1121_);
lean_dec_ref(v_e_1120_);
return v___x_1141_;
}
}
else
{
lean_dec_ref(v_a_1142_);
lean_dec(v_a_1140_);
lean_dec(v_a_1129_);
lean_dec_ref(v_a_1128_);
lean_dec(v_a_1127_);
lean_dec_ref(v_a_1126_);
lean_dec(v_a_1125_);
lean_dec_ref(v_a_1124_);
lean_dec(v_a_1123_);
lean_dec_ref(v_a_1122_);
lean_dec(v_a_1121_);
lean_dec_ref(v_e_1120_);
return v___x_1141_;
}
}
else
{
lean_dec(v_a_1140_);
lean_dec(v_a_1129_);
lean_dec_ref(v_a_1128_);
lean_dec(v_a_1127_);
lean_dec_ref(v_a_1126_);
lean_dec(v_a_1125_);
lean_dec_ref(v_a_1124_);
lean_dec(v_a_1123_);
lean_dec_ref(v_a_1122_);
lean_dec(v_a_1121_);
lean_dec_ref(v_e_1120_);
return v___x_1141_;
}
}
else
{
lean_object* v_a_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1158_; 
lean_dec(v_a_1129_);
lean_dec_ref(v_a_1128_);
lean_dec(v_a_1127_);
lean_dec_ref(v_a_1126_);
lean_dec(v_a_1125_);
lean_dec_ref(v_a_1124_);
lean_dec(v_a_1123_);
lean_dec_ref(v_a_1122_);
lean_dec(v_a_1121_);
lean_dec_ref(v_e_1120_);
v_a_1151_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1153_ = v___x_1139_;
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_a_1151_);
lean_dec(v___x_1139_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1156_; 
if (v_isShared_1154_ == 0)
{
v___x_1156_ = v___x_1153_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_a_1151_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
}
else
{
lean_object* v___x_1159_; 
lean_dec(v_declName_1135_);
v___x_1159_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems(v_e_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_);
if (lean_obj_tag(v___x_1159_) == 0)
{
lean_object* v_a_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1168_; 
v_a_1160_ = lean_ctor_get(v___x_1159_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1162_ = v___x_1159_;
v_isShared_1163_ = v_isSharedCheck_1168_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_a_1160_);
lean_dec(v___x_1159_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1168_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1164_; lean_object* v___x_1166_; 
v___x_1164_ = l_Lean_Meta_Sym_Simp_Result_markAsDone(v_a_1160_);
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 0, v___x_1164_);
v___x_1166_ = v___x_1162_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v___x_1164_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
else
{
return v___x_1159_;
}
}
}
else
{
lean_object* v_a_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1176_; 
lean_dec(v_declName_1135_);
lean_dec(v_a_1129_);
lean_dec_ref(v_a_1128_);
lean_dec(v_a_1127_);
lean_dec_ref(v_a_1126_);
lean_dec(v_a_1125_);
lean_dec_ref(v_a_1124_);
lean_dec(v_a_1123_);
lean_dec_ref(v_a_1122_);
lean_dec(v_a_1121_);
lean_dec_ref(v_e_1120_);
v_a_1169_ = lean_ctor_get(v___x_1136_, 0);
v_isSharedCheck_1176_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1171_ = v___x_1136_;
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_a_1169_);
lean_dec(v___x_1136_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v___x_1174_; 
if (v_isShared_1172_ == 0)
{
v___x_1174_ = v___x_1171_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v_a_1169_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
return v___x_1174_;
}
}
}
}
case 6:
{
lean_object* v___x_1177_; 
lean_dec_ref(v_fn_1134_);
lean_dec_ref(v_a_1124_);
lean_dec(v_a_1123_);
lean_dec_ref(v_a_1122_);
lean_dec(v_a_1121_);
v___x_1177_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg(v_e_1120_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_);
lean_dec(v_a_1125_);
return v___x_1177_;
}
default: 
{
lean_object* v___x_1178_; lean_object* v___x_1179_; 
lean_dec_ref(v_fn_1134_);
lean_dec(v_a_1129_);
lean_dec_ref(v_a_1128_);
lean_dec(v_a_1127_);
lean_dec_ref(v_a_1126_);
lean_dec(v_a_1125_);
lean_dec_ref(v_a_1124_);
lean_dec(v_a_1123_);
lean_dec_ref(v_a_1122_);
lean_dec(v_a_1121_);
lean_dec_ref(v_e_1120_);
v___x_1178_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__9));
v___x_1179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1178_);
return v___x_1179_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp___boxed(lean_object* v_e_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp(v_e_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0(lean_object* v_00_u03b1_1192_, lean_object* v_constName_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_){
_start:
{
lean_object* v___x_1204_; 
v___x_1204_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0___redArg(v_constName_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1205_, lean_object* v_constName_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0(v_00_u03b1_1205_, v_constName_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_);
lean_dec(v___y_1215_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1212_);
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_dec(v___y_1209_);
lean_dec_ref(v___y_1208_);
lean_dec(v___y_1207_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1218_, lean_object* v_ref_1219_, lean_object* v_constName_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v___x_1231_; 
v___x_1231_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg(v_ref_1219_, v_constName_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1232_, lean_object* v_ref_1233_, lean_object* v_constName_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1(v_00_u03b1_1232_, v_ref_1233_, v_constName_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
lean_dec(v___y_1243_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec(v___y_1235_);
lean_dec(v_ref_1233_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1246_, lean_object* v_ref_1247_, lean_object* v_msg_1248_, lean_object* v_declHint_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
lean_object* v___x_1260_; 
v___x_1260_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1247_, v_msg_1248_, v_declHint_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1261_, lean_object* v_ref_1262_, lean_object* v_msg_1263_, lean_object* v_declHint_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1261_, v_ref_1262_, v_msg_1263_, v_declHint_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
lean_dec(v___y_1273_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
lean_dec(v___y_1265_);
lean_dec(v_ref_1262_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_1276_, lean_object* v_declHint_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_){
_start:
{
lean_object* v___x_1288_; 
v___x_1288_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1276_, v_declHint_1277_, v___y_1286_);
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_1289_, lean_object* v_declHint_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_1289_, v_declHint_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
lean_dec(v___y_1293_);
lean_dec_ref(v___y_1292_);
lean_dec(v___y_1291_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_1302_, lean_object* v_ref_1303_, lean_object* v_msg_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_){
_start:
{
lean_object* v___x_1315_; 
v___x_1315_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1303_, v_msg_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_1316_, lean_object* v_ref_1317_, lean_object* v_msg_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_1316_, v_ref_1317_, v_msg_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
lean_dec(v___y_1327_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec(v___y_1319_);
lean_dec(v_ref_1317_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_1330_, lean_object* v_msg_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
lean_object* v___x_1342_; 
v___x_1342_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_1331_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1343_, lean_object* v_msg_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_){
_start:
{
lean_object* v_res_1355_; 
v_res_1355_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(v_00_u03b1_1343_, v_msg_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_);
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
lean_dec(v___y_1345_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleOpaqueConst(lean_object* v_e_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_){
_start:
{
if (lean_obj_tag(v_e_1356_) == 4)
{
lean_object* v_declName_1367_; lean_object* v___x_1368_; 
v_declName_1367_ = lean_ctor_get(v_e_1356_, 0);
v___x_1368_ = l_Lean_Meta_Tactic_Cbv_isCbvOpaque___redArg(v_declName_1367_, v_a_1365_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1389_; 
v_a_1369_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1371_ = v___x_1368_;
v_isShared_1372_ = v_isSharedCheck_1389_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_dec(v___x_1368_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1389_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
uint8_t v___x_1373_; 
v___x_1373_ = lean_unbox(v_a_1369_);
if (v___x_1373_ == 0)
{
lean_object* v___x_1374_; uint8_t v___x_1375_; lean_object* v___x_1377_; 
lean_dec_ref(v_e_1356_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_a_1363_);
lean_dec_ref(v_a_1362_);
lean_dec(v_a_1361_);
lean_dec_ref(v_a_1360_);
lean_dec(v_a_1359_);
lean_dec_ref(v_a_1358_);
lean_dec(v_a_1357_);
v___x_1374_ = lean_alloc_ctor(0, 0, 1);
v___x_1375_ = lean_unbox(v_a_1369_);
lean_dec(v_a_1369_);
lean_ctor_set_uint8(v___x_1374_, 0, v___x_1375_);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 0, v___x_1374_);
v___x_1377_ = v___x_1371_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v___x_1374_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
else
{
lean_object* v___x_1379_; 
lean_del_object(v___x_1371_);
lean_dec(v_a_1369_);
v___x_1379_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems(v_e_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1388_; 
v_a_1380_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1382_ = v___x_1379_;
v_isShared_1383_ = v_isSharedCheck_1388_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1379_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1388_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1384_; lean_object* v___x_1386_; 
v___x_1384_ = l_Lean_Meta_Sym_Simp_Result_markAsDone(v_a_1380_);
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 0, v___x_1384_);
v___x_1386_ = v___x_1382_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v___x_1384_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
}
else
{
return v___x_1379_;
}
}
}
}
else
{
lean_object* v_a_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1397_; 
lean_dec_ref(v_e_1356_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_a_1363_);
lean_dec_ref(v_a_1362_);
lean_dec(v_a_1361_);
lean_dec_ref(v_a_1360_);
lean_dec(v_a_1359_);
lean_dec_ref(v_a_1358_);
lean_dec(v_a_1357_);
v_a_1390_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1392_ = v___x_1368_;
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_a_1390_);
lean_dec(v___x_1368_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1395_; 
if (v_isShared_1393_ == 0)
{
v___x_1395_ = v___x_1392_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_a_1390_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
}
else
{
lean_object* v___x_1398_; lean_object* v___x_1399_; 
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_a_1363_);
lean_dec_ref(v_a_1362_);
lean_dec(v_a_1361_);
lean_dec_ref(v_a_1360_);
lean_dec(v_a_1359_);
lean_dec_ref(v_a_1358_);
lean_dec(v_a_1357_);
lean_dec_ref(v_e_1356_);
v___x_1398_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__9));
v___x_1399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1399_, 0, v___x_1398_);
return v___x_1399_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleOpaqueConst___boxed(lean_object* v_e_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_){
_start:
{
lean_object* v_res_1411_; 
v_res_1411_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleOpaqueConst(v_e_1400_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_);
return v_res_1411_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__1(void){
_start:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1413_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__0));
v___x_1414_ = l_Lean_stringToMessageData(v___x_1413_);
return v___x_1414_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__3(void){
_start:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1416_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__2));
v___x_1417_ = l_Lean_stringToMessageData(v___x_1416_);
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg(lean_object* v_e_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_){
_start:
{
lean_object* v___x_1425_; 
lean_inc_ref(v_e_1418_);
v___x_1425_ = l_Lean_Expr_rawNatLit_x3f(v_e_1418_);
if (lean_obj_tag(v___x_1425_) == 1)
{
lean_object* v_val_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
v_val_1426_ = lean_ctor_get(v___x_1425_, 0);
lean_inc(v_val_1426_);
lean_dec_ref(v___x_1425_);
v___x_1427_ = l_Lean_mkNatLit(v_val_1426_);
v___x_1428_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_1427_, v_a_1419_);
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_object* v_a_1429_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1435_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v_a_1457_; uint8_t v___x_1458_; 
v_a_1429_ = lean_ctor_get(v___x_1428_, 0);
lean_inc(v_a_1429_);
lean_dec_ref(v___x_1428_);
v___x_1455_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2));
v___x_1456_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(v___x_1455_, v_a_1422_);
v_a_1457_ = lean_ctor_get(v___x_1456_, 0);
lean_inc(v_a_1457_);
lean_dec_ref(v___x_1456_);
v___x_1458_ = lean_unbox(v_a_1457_);
lean_dec(v_a_1457_);
if (v___x_1458_ == 0)
{
v___y_1431_ = v_a_1419_;
v___y_1432_ = v_a_1420_;
v___y_1433_ = v_a_1421_;
v___y_1434_ = v_a_1422_;
v___y_1435_ = v_a_1423_;
goto v___jp_1430_;
}
else
{
lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1459_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__1, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__1);
lean_inc_ref(v_e_1418_);
v___x_1460_ = l_Lean_MessageData_ofExpr(v_e_1418_);
v___x_1461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1459_);
lean_ctor_set(v___x_1461_, 1, v___x_1460_);
v___x_1462_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__3, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__3);
v___x_1463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1461_);
lean_ctor_set(v___x_1463_, 1, v___x_1462_);
lean_inc(v_a_1429_);
v___x_1464_ = l_Lean_MessageData_ofExpr(v_a_1429_);
v___x_1465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1465_, 0, v___x_1463_);
lean_ctor_set(v___x_1465_, 1, v___x_1464_);
v___x_1466_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg(v___x_1455_, v___x_1465_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_);
if (lean_obj_tag(v___x_1466_) == 0)
{
lean_dec_ref(v___x_1466_);
v___y_1431_ = v_a_1419_;
v___y_1432_ = v_a_1420_;
v___y_1433_ = v_a_1421_;
v___y_1434_ = v_a_1422_;
v___y_1435_ = v_a_1423_;
goto v___jp_1430_;
}
else
{
lean_object* v_a_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1474_; 
lean_dec(v_a_1429_);
lean_dec(v_a_1423_);
lean_dec_ref(v_a_1422_);
lean_dec(v_a_1421_);
lean_dec_ref(v_a_1420_);
lean_dec_ref(v_e_1418_);
v_a_1467_ = lean_ctor_get(v___x_1466_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1466_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1469_ = v___x_1466_;
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_a_1467_);
lean_dec(v___x_1466_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1472_; 
if (v_isShared_1470_ == 0)
{
v___x_1472_ = v___x_1469_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_a_1467_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
}
}
v___jp_1430_:
{
lean_object* v___x_1436_; 
v___x_1436_ = l_Lean_Meta_Sym_mkEqRefl___redArg(v_e_1418_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_);
if (lean_obj_tag(v___x_1436_) == 0)
{
lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1446_; 
v_a_1437_ = lean_ctor_get(v___x_1436_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1439_ = v___x_1436_;
v_isShared_1440_ = v_isSharedCheck_1446_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_dec(v___x_1436_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1446_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
uint8_t v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1444_; 
v___x_1441_ = 0;
v___x_1442_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_1442_, 0, v_a_1429_);
lean_ctor_set(v___x_1442_, 1, v_a_1437_);
lean_ctor_set_uint8(v___x_1442_, sizeof(void*)*2, v___x_1441_);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 0, v___x_1442_);
v___x_1444_ = v___x_1439_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1442_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
else
{
lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1454_; 
lean_dec(v_a_1429_);
v_a_1447_ = lean_ctor_get(v___x_1436_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1449_ = v___x_1436_;
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v___x_1436_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1452_; 
if (v_isShared_1450_ == 0)
{
v___x_1452_ = v___x_1449_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_a_1447_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
}
}
else
{
lean_object* v_a_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1482_; 
lean_dec(v_a_1423_);
lean_dec_ref(v_a_1422_);
lean_dec(v_a_1421_);
lean_dec_ref(v_a_1420_);
lean_dec_ref(v_e_1418_);
v_a_1475_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1477_ = v___x_1428_;
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_a_1475_);
lean_dec(v___x_1428_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1480_; 
if (v_isShared_1478_ == 0)
{
v___x_1480_ = v___x_1477_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_a_1475_);
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
lean_object* v___x_1483_; lean_object* v___x_1484_; 
lean_dec(v___x_1425_);
lean_dec(v_a_1423_);
lean_dec_ref(v_a_1422_);
lean_dec(v_a_1421_);
lean_dec_ref(v_a_1420_);
lean_dec_ref(v_e_1418_);
v___x_1483_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__9));
v___x_1484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1483_);
return v___x_1484_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___boxed(lean_object* v_e_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg(v_e_1485_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_);
lean_dec(v_a_1486_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit(lean_object* v_e_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_){
_start:
{
lean_object* v___x_1504_; 
v___x_1504_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg(v_e_1493_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___boxed(lean_object* v_e_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_){
_start:
{
lean_object* v_res_1516_; 
v_res_1516_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit(v_e_1505_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
lean_dec(v_a_1510_);
lean_dec_ref(v_a_1509_);
lean_dec(v_a_1508_);
lean_dec_ref(v_a_1507_);
lean_dec(v_a_1506_);
return v_res_1516_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg___closed__1(void){
_start:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1518_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg___closed__0));
v___x_1519_ = l_Lean_stringToMessageData(v___x_1518_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg(lean_object* v_e_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_){
_start:
{
if (lean_obj_tag(v_e_1520_) == 8)
{
lean_object* v_value_1527_; lean_object* v_body_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; uint8_t v___x_1532_; lean_object* v_new_1533_; lean_object* v___x_1534_; 
v_value_1527_ = lean_ctor_get(v_e_1520_, 2);
v_body_1528_ = lean_ctor_get(v_e_1520_, 3);
v___x_1529_ = lean_unsigned_to_nat(1u);
v___x_1530_ = lean_mk_empty_array_with_capacity(v___x_1529_);
lean_inc_ref(v_value_1527_);
v___x_1531_ = lean_array_push(v___x_1530_, v_value_1527_);
v___x_1532_ = 1;
v_new_1533_ = l_Lean_Meta_expandLet(v_body_1528_, v___x_1531_, v___x_1532_);
v___x_1534_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_new_1533_, v_a_1521_);
if (lean_obj_tag(v___x_1534_) == 0)
{
lean_object* v_a_1535_; lean_object* v___y_1537_; lean_object* v___y_1538_; lean_object* v___y_1539_; lean_object* v___y_1540_; lean_object* v___y_1541_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v_a_1563_; uint8_t v___x_1564_; 
v_a_1535_ = lean_ctor_get(v___x_1534_, 0);
lean_inc(v_a_1535_);
lean_dec_ref(v___x_1534_);
v___x_1561_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2));
v___x_1562_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(v___x_1561_, v_a_1524_);
v_a_1563_ = lean_ctor_get(v___x_1562_, 0);
lean_inc(v_a_1563_);
lean_dec_ref(v___x_1562_);
v___x_1564_ = lean_unbox(v_a_1563_);
lean_dec(v_a_1563_);
if (v___x_1564_ == 0)
{
lean_dec_ref(v_e_1520_);
v___y_1537_ = v_a_1521_;
v___y_1538_ = v_a_1522_;
v___y_1539_ = v_a_1523_;
v___y_1540_ = v_a_1524_;
v___y_1541_ = v_a_1525_;
goto v___jp_1536_;
}
else
{
lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1565_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg___closed__1, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg___closed__1);
v___x_1566_ = l_Lean_indentExpr(v_e_1520_);
v___x_1567_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1565_);
lean_ctor_set(v___x_1567_, 1, v___x_1566_);
v___x_1568_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7);
v___x_1569_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1569_, 0, v___x_1567_);
lean_ctor_set(v___x_1569_, 1, v___x_1568_);
lean_inc(v_a_1535_);
v___x_1570_ = l_Lean_indentExpr(v_a_1535_);
v___x_1571_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1569_);
lean_ctor_set(v___x_1571_, 1, v___x_1570_);
v___x_1572_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg(v___x_1561_, v___x_1571_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_dec_ref(v___x_1572_);
v___y_1537_ = v_a_1521_;
v___y_1538_ = v_a_1522_;
v___y_1539_ = v_a_1523_;
v___y_1540_ = v_a_1524_;
v___y_1541_ = v_a_1525_;
goto v___jp_1536_;
}
else
{
lean_object* v_a_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1580_; 
lean_dec(v_a_1535_);
lean_dec(v_a_1525_);
lean_dec_ref(v_a_1524_);
lean_dec(v_a_1523_);
lean_dec_ref(v_a_1522_);
v_a_1573_ = lean_ctor_get(v___x_1572_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1575_ = v___x_1572_;
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_a_1573_);
lean_dec(v___x_1572_);
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
v___jp_1536_:
{
lean_object* v___x_1542_; 
lean_inc(v_a_1535_);
v___x_1542_ = l_Lean_Meta_Sym_mkEqRefl___redArg(v_a_1535_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1552_; 
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1552_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1545_ = v___x_1542_;
v_isShared_1546_ = v_isSharedCheck_1552_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_dec(v___x_1542_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1552_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
uint8_t v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1550_; 
v___x_1547_ = 0;
v___x_1548_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_1548_, 0, v_a_1535_);
lean_ctor_set(v___x_1548_, 1, v_a_1543_);
lean_ctor_set_uint8(v___x_1548_, sizeof(void*)*2, v___x_1547_);
if (v_isShared_1546_ == 0)
{
lean_ctor_set(v___x_1545_, 0, v___x_1548_);
v___x_1550_ = v___x_1545_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v___x_1548_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
return v___x_1550_;
}
}
}
else
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1560_; 
lean_dec(v_a_1535_);
v_a_1553_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1555_ = v___x_1542_;
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___x_1542_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1558_; 
if (v_isShared_1556_ == 0)
{
v___x_1558_ = v___x_1555_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_a_1553_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
}
}
else
{
lean_object* v_a_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1588_; 
lean_dec_ref(v_e_1520_);
lean_dec(v_a_1525_);
lean_dec_ref(v_a_1524_);
lean_dec(v_a_1523_);
lean_dec_ref(v_a_1522_);
v_a_1581_ = lean_ctor_get(v___x_1534_, 0);
v_isSharedCheck_1588_ = !lean_is_exclusive(v___x_1534_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1583_ = v___x_1534_;
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_a_1581_);
lean_dec(v___x_1534_);
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
else
{
lean_object* v___x_1589_; lean_object* v___x_1590_; 
lean_dec(v_a_1525_);
lean_dec_ref(v_a_1524_);
lean_dec(v_a_1523_);
lean_dec_ref(v_a_1522_);
lean_dec_ref(v_e_1520_);
v___x_1589_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__9));
v___x_1590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1589_);
return v___x_1590_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg___boxed(lean_object* v_e_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_){
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg(v_e_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_);
lean_dec(v_a_1592_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce(lean_object* v_e_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_){
_start:
{
lean_object* v___x_1610_; 
v___x_1610_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg(v_e_1599_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_);
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___boxed(lean_object* v_e_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_){
_start:
{
lean_object* v_res_1622_; 
v_res_1622_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce(v_e_1611_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_, v_a_1619_, v_a_1620_);
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
v_debug_1638_ = lean_ctor_get_uint8(v___x_1637_, sizeof(void*)*7);
lean_dec(v___x_1637_);
if (v_debug_1638_ == 0)
{
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1628_);
lean_dec_ref(v___y_1626_);
v___y_1634_ = v___y_1627_;
goto v___jp_1633_;
}
else
{
lean_object* v___x_1639_; 
lean_inc(v___y_1627_);
lean_inc_ref(v_struct_1625_);
v___x_1639_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_struct_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_dec_ref(v___x_1639_);
v___y_1634_ = v___y_1627_;
goto v___jp_1633_;
}
else
{
lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1647_; 
lean_dec(v___y_1627_);
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
lean_dec(v___y_1634_);
return v___x_1636_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg___boxed(lean_object* v_structName_1648_, lean_object* v_idx_1649_, lean_object* v_struct_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_){
_start:
{
lean_object* v_res_1658_; 
v_res_1658_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_structName_1648_, v_idx_1649_, v_struct_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_);
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
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
lean_dec(v___y_1676_);
return v_res_1686_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1687_ = lean_unsigned_to_nat(32u);
v___x_1688_ = lean_mk_empty_array_with_capacity(v___x_1687_);
v___x_1689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1689_, 0, v___x_1688_);
return v___x_1689_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1690_ = ((size_t)5ULL);
v___x_1691_ = lean_unsigned_to_nat(0u);
v___x_1692_ = lean_unsigned_to_nat(32u);
v___x_1693_ = lean_mk_empty_array_with_capacity(v___x_1692_);
v___x_1694_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___redArg___closed__0);
v___x_1695_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1695_, 0, v___x_1694_);
lean_ctor_set(v___x_1695_, 1, v___x_1693_);
lean_ctor_set(v___x_1695_, 2, v___x_1691_);
lean_ctor_set(v___x_1695_, 3, v___x_1691_);
lean_ctor_set_usize(v___x_1695_, 4, v___x_1690_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___redArg(lean_object* v___y_1696_){
_start:
{
lean_object* v___x_1698_; lean_object* v_traceState_1699_; lean_object* v_traces_1700_; lean_object* v___x_1701_; lean_object* v_traceState_1702_; lean_object* v_env_1703_; lean_object* v_nextMacroScope_1704_; lean_object* v_ngen_1705_; lean_object* v_auxDeclNGen_1706_; lean_object* v_cache_1707_; lean_object* v_messages_1708_; lean_object* v_infoState_1709_; lean_object* v_snapshotTasks_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1729_; 
v___x_1698_ = lean_st_ref_get(v___y_1696_);
v_traceState_1699_ = lean_ctor_get(v___x_1698_, 4);
lean_inc_ref(v_traceState_1699_);
lean_dec(v___x_1698_);
v_traces_1700_ = lean_ctor_get(v_traceState_1699_, 0);
lean_inc_ref(v_traces_1700_);
lean_dec_ref(v_traceState_1699_);
v___x_1701_ = lean_st_ref_take(v___y_1696_);
v_traceState_1702_ = lean_ctor_get(v___x_1701_, 4);
v_env_1703_ = lean_ctor_get(v___x_1701_, 0);
v_nextMacroScope_1704_ = lean_ctor_get(v___x_1701_, 1);
v_ngen_1705_ = lean_ctor_get(v___x_1701_, 2);
v_auxDeclNGen_1706_ = lean_ctor_get(v___x_1701_, 3);
v_cache_1707_ = lean_ctor_get(v___x_1701_, 5);
v_messages_1708_ = lean_ctor_get(v___x_1701_, 6);
v_infoState_1709_ = lean_ctor_get(v___x_1701_, 7);
v_snapshotTasks_1710_ = lean_ctor_get(v___x_1701_, 8);
v_isSharedCheck_1729_ = !lean_is_exclusive(v___x_1701_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1712_ = v___x_1701_;
v_isShared_1713_ = v_isSharedCheck_1729_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_snapshotTasks_1710_);
lean_inc(v_infoState_1709_);
lean_inc(v_messages_1708_);
lean_inc(v_cache_1707_);
lean_inc(v_traceState_1702_);
lean_inc(v_auxDeclNGen_1706_);
lean_inc(v_ngen_1705_);
lean_inc(v_nextMacroScope_1704_);
lean_inc(v_env_1703_);
lean_dec(v___x_1701_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1729_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
uint64_t v_tid_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1727_; 
v_tid_1714_ = lean_ctor_get_uint64(v_traceState_1702_, sizeof(void*)*1);
v_isSharedCheck_1727_ = !lean_is_exclusive(v_traceState_1702_);
if (v_isSharedCheck_1727_ == 0)
{
lean_object* v_unused_1728_; 
v_unused_1728_ = lean_ctor_get(v_traceState_1702_, 0);
lean_dec(v_unused_1728_);
v___x_1716_ = v_traceState_1702_;
v_isShared_1717_ = v_isSharedCheck_1727_;
goto v_resetjp_1715_;
}
else
{
lean_dec(v_traceState_1702_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1727_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1718_; lean_object* v___x_1720_; 
v___x_1718_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___redArg___closed__1);
if (v_isShared_1717_ == 0)
{
lean_ctor_set(v___x_1716_, 0, v___x_1718_);
v___x_1720_ = v___x_1716_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v___x_1718_);
lean_ctor_set_uint64(v_reuseFailAlloc_1726_, sizeof(void*)*1, v_tid_1714_);
v___x_1720_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
lean_object* v___x_1722_; 
if (v_isShared_1713_ == 0)
{
lean_ctor_set(v___x_1712_, 4, v___x_1720_);
v___x_1722_ = v___x_1712_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_env_1703_);
lean_ctor_set(v_reuseFailAlloc_1725_, 1, v_nextMacroScope_1704_);
lean_ctor_set(v_reuseFailAlloc_1725_, 2, v_ngen_1705_);
lean_ctor_set(v_reuseFailAlloc_1725_, 3, v_auxDeclNGen_1706_);
lean_ctor_set(v_reuseFailAlloc_1725_, 4, v___x_1720_);
lean_ctor_set(v_reuseFailAlloc_1725_, 5, v_cache_1707_);
lean_ctor_set(v_reuseFailAlloc_1725_, 6, v_messages_1708_);
lean_ctor_set(v_reuseFailAlloc_1725_, 7, v_infoState_1709_);
lean_ctor_set(v_reuseFailAlloc_1725_, 8, v_snapshotTasks_1710_);
v___x_1722_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1723_ = lean_st_ref_set(v___y_1696_, v___x_1722_);
v___x_1724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1724_, 0, v_traces_1700_);
return v___x_1724_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___redArg___boxed(lean_object* v___y_1730_, lean_object* v___y_1731_){
_start:
{
lean_object* v_res_1732_; 
v_res_1732_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___redArg(v___y_1730_);
lean_dec(v___y_1730_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1(lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
lean_object* v___x_1743_; 
v___x_1743_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___redArg(v___y_1741_);
return v___x_1743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___boxed(lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_){
_start:
{
lean_object* v_res_1754_; 
v_res_1754_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1(v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
lean_dec(v___y_1752_);
lean_dec_ref(v___y_1751_);
lean_dec(v___y_1750_);
lean_dec_ref(v___y_1749_);
lean_dec(v___y_1748_);
lean_dec_ref(v___y_1747_);
lean_dec(v___y_1746_);
lean_dec_ref(v___y_1745_);
lean_dec(v___y_1744_);
return v_res_1754_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2(lean_object* v_opts_1755_, lean_object* v_opt_1756_){
_start:
{
lean_object* v_name_1757_; lean_object* v_defValue_1758_; lean_object* v_map_1759_; lean_object* v___x_1760_; 
v_name_1757_ = lean_ctor_get(v_opt_1756_, 0);
v_defValue_1758_ = lean_ctor_get(v_opt_1756_, 1);
v_map_1759_ = lean_ctor_get(v_opts_1755_, 0);
v___x_1760_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1759_, v_name_1757_);
if (lean_obj_tag(v___x_1760_) == 0)
{
uint8_t v___x_1761_; 
v___x_1761_ = lean_unbox(v_defValue_1758_);
return v___x_1761_;
}
else
{
lean_object* v_val_1762_; 
v_val_1762_ = lean_ctor_get(v___x_1760_, 0);
lean_inc(v_val_1762_);
lean_dec_ref(v___x_1760_);
if (lean_obj_tag(v_val_1762_) == 1)
{
uint8_t v_v_1763_; 
v_v_1763_ = lean_ctor_get_uint8(v_val_1762_, 0);
lean_dec_ref(v_val_1762_);
return v_v_1763_;
}
else
{
uint8_t v___x_1764_; 
lean_dec(v_val_1762_);
v___x_1764_ = lean_unbox(v_defValue_1758_);
return v___x_1764_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___boxed(lean_object* v_opts_1765_, lean_object* v_opt_1766_){
_start:
{
uint8_t v_res_1767_; lean_object* v_r_1768_; 
v_res_1767_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2(v_opts_1765_, v_opt_1766_);
lean_dec_ref(v_opt_1766_);
lean_dec_ref(v_opts_1765_);
v_r_1768_ = lean_box(v_res_1767_);
return v_r_1768_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1770_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__0));
v___x_1771_ = l_Lean_stringToMessageData(v___x_1770_);
return v___x_1771_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; 
v___x_1773_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__2));
v___x_1774_ = l_Lean_stringToMessageData(v___x_1773_);
return v___x_1774_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__5(void){
_start:
{
lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1776_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__4));
v___x_1777_ = l_Lean_stringToMessageData(v___x_1776_);
return v___x_1777_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__7(void){
_start:
{
lean_object* v___x_1779_; lean_object* v___x_1780_; 
v___x_1779_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__6));
v___x_1780_ = l_Lean_stringToMessageData(v___x_1779_);
return v___x_1780_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__9(void){
_start:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1782_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__8));
v___x_1783_ = l_Lean_stringToMessageData(v___x_1782_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0(lean_object* v_typeName_1784_, lean_object* v_idx_1785_, lean_object* v_e_1786_, lean_object* v_x_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_){
_start:
{
if (lean_obj_tag(v_x_1787_) == 0)
{
lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1818_; 
lean_dec_ref(v_e_1786_);
v_a_1798_ = lean_ctor_get(v_x_1787_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v_x_1787_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1800_ = v_x_1787_;
v_isShared_1801_ = v_isSharedCheck_1818_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v_x_1787_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1818_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1809_; 
v___x_1802_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__1);
v___x_1803_ = l_Lean_MessageData_ofName(v_typeName_1784_);
v___x_1804_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1804_, 0, v___x_1802_);
lean_ctor_set(v___x_1804_, 1, v___x_1803_);
v___x_1805_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_1806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1804_);
lean_ctor_set(v___x_1806_, 1, v___x_1805_);
v___x_1807_ = l_Nat_reprFast(v_idx_1785_);
if (v_isShared_1801_ == 0)
{
lean_ctor_set_tag(v___x_1800_, 3);
lean_ctor_set(v___x_1800_, 0, v___x_1807_);
v___x_1809_ = v___x_1800_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v___x_1807_);
v___x_1809_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1810_ = l_Lean_MessageData_ofFormat(v___x_1809_);
v___x_1811_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1806_);
lean_ctor_set(v___x_1811_, 1, v___x_1810_);
v___x_1812_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__3);
v___x_1813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1811_);
lean_ctor_set(v___x_1813_, 1, v___x_1812_);
v___x_1814_ = l_Lean_Exception_toMessageData(v_a_1798_);
v___x_1815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1815_, 0, v___x_1813_);
lean_ctor_set(v___x_1815_, 1, v___x_1814_);
v___x_1816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1815_);
return v___x_1816_;
}
}
}
else
{
lean_object* v_a_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1875_; 
v_a_1819_ = lean_ctor_get(v_x_1787_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v_x_1787_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1821_ = v_x_1787_;
v_isShared_1822_ = v_isSharedCheck_1875_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_a_1819_);
lean_dec(v_x_1787_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1875_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
if (lean_obj_tag(v_a_1819_) == 0)
{
uint8_t v_done_1823_; 
v_done_1823_ = lean_ctor_get_uint8(v_a_1819_, 0);
lean_dec_ref(v_a_1819_);
if (v_done_1823_ == 1)
{
lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1831_; 
v___x_1824_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__1);
v___x_1825_ = l_Lean_MessageData_ofName(v_typeName_1784_);
v___x_1826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1824_);
lean_ctor_set(v___x_1826_, 1, v___x_1825_);
v___x_1827_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_1828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1826_);
lean_ctor_set(v___x_1828_, 1, v___x_1827_);
v___x_1829_ = l_Nat_reprFast(v_idx_1785_);
if (v_isShared_1822_ == 0)
{
lean_ctor_set_tag(v___x_1821_, 3);
lean_ctor_set(v___x_1821_, 0, v___x_1829_);
v___x_1831_ = v___x_1821_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v___x_1829_);
v___x_1831_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; 
v___x_1832_ = l_Lean_MessageData_ofFormat(v___x_1831_);
v___x_1833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1828_);
lean_ctor_set(v___x_1833_, 1, v___x_1832_);
v___x_1834_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__5, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__5_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__5);
v___x_1835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1833_);
lean_ctor_set(v___x_1835_, 1, v___x_1834_);
v___x_1836_ = l_Lean_indentExpr(v_e_1786_);
v___x_1837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1835_);
lean_ctor_set(v___x_1837_, 1, v___x_1836_);
v___x_1838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1837_);
return v___x_1838_;
}
}
else
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1847_; 
lean_dec_ref(v_e_1786_);
v___x_1840_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__1);
v___x_1841_ = l_Lean_MessageData_ofName(v_typeName_1784_);
v___x_1842_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1840_);
lean_ctor_set(v___x_1842_, 1, v___x_1841_);
v___x_1843_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_1844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1842_);
lean_ctor_set(v___x_1844_, 1, v___x_1843_);
v___x_1845_ = l_Nat_reprFast(v_idx_1785_);
if (v_isShared_1822_ == 0)
{
lean_ctor_set_tag(v___x_1821_, 3);
lean_ctor_set(v___x_1821_, 0, v___x_1845_);
v___x_1847_ = v___x_1821_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v___x_1845_);
v___x_1847_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1848_ = l_Lean_MessageData_ofFormat(v___x_1847_);
v___x_1849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1844_);
lean_ctor_set(v___x_1849_, 1, v___x_1848_);
v___x_1850_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__7, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__7_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__7);
v___x_1851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1849_);
lean_ctor_set(v___x_1851_, 1, v___x_1850_);
v___x_1852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1851_);
return v___x_1852_;
}
}
}
else
{
lean_object* v_e_x27_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1862_; 
v_e_x27_1854_ = lean_ctor_get(v_a_1819_, 0);
lean_inc_ref(v_e_x27_1854_);
lean_dec_ref(v_a_1819_);
v___x_1855_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__1);
v___x_1856_ = l_Lean_MessageData_ofName(v_typeName_1784_);
v___x_1857_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1855_);
lean_ctor_set(v___x_1857_, 1, v___x_1856_);
v___x_1858_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_1859_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1857_);
lean_ctor_set(v___x_1859_, 1, v___x_1858_);
v___x_1860_ = l_Nat_reprFast(v_idx_1785_);
if (v_isShared_1822_ == 0)
{
lean_ctor_set_tag(v___x_1821_, 3);
lean_ctor_set(v___x_1821_, 0, v___x_1860_);
v___x_1862_ = v___x_1821_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v___x_1860_);
v___x_1862_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1863_ = l_Lean_MessageData_ofFormat(v___x_1862_);
v___x_1864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1859_);
lean_ctor_set(v___x_1864_, 1, v___x_1863_);
v___x_1865_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__9, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__9_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__9);
v___x_1866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1864_);
lean_ctor_set(v___x_1866_, 1, v___x_1865_);
v___x_1867_ = l_Lean_indentExpr(v_e_1786_);
v___x_1868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1868_, 0, v___x_1866_);
lean_ctor_set(v___x_1868_, 1, v___x_1867_);
v___x_1869_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7);
v___x_1870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1868_);
lean_ctor_set(v___x_1870_, 1, v___x_1869_);
v___x_1871_ = l_Lean_indentExpr(v_e_x27_1854_);
v___x_1872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1870_);
lean_ctor_set(v___x_1872_, 1, v___x_1871_);
v___x_1873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1872_);
return v___x_1873_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___boxed(lean_object* v_typeName_1876_, lean_object* v_idx_1877_, lean_object* v_e_1878_, lean_object* v_x_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_){
_start:
{
lean_object* v_res_1890_; 
v_res_1890_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0(v_typeName_1876_, v_idx_1877_, v_e_1878_, v_x_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_);
lean_dec(v___y_1888_);
lean_dec_ref(v___y_1887_);
lean_dec(v___y_1886_);
lean_dec_ref(v___y_1885_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v___y_1880_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__4_spec__5(size_t v_sz_1891_, size_t v_i_1892_, lean_object* v_bs_1893_){
_start:
{
uint8_t v___x_1894_; 
v___x_1894_ = lean_usize_dec_lt(v_i_1892_, v_sz_1891_);
if (v___x_1894_ == 0)
{
return v_bs_1893_;
}
else
{
lean_object* v_v_1895_; lean_object* v_msg_1896_; lean_object* v___x_1897_; lean_object* v_bs_x27_1898_; size_t v___x_1899_; size_t v___x_1900_; lean_object* v___x_1901_; 
v_v_1895_ = lean_array_uget_borrowed(v_bs_1893_, v_i_1892_);
v_msg_1896_ = lean_ctor_get(v_v_1895_, 1);
lean_inc_ref(v_msg_1896_);
v___x_1897_ = lean_unsigned_to_nat(0u);
v_bs_x27_1898_ = lean_array_uset(v_bs_1893_, v_i_1892_, v___x_1897_);
v___x_1899_ = ((size_t)1ULL);
v___x_1900_ = lean_usize_add(v_i_1892_, v___x_1899_);
v___x_1901_ = lean_array_uset(v_bs_x27_1898_, v_i_1892_, v_msg_1896_);
v_i_1892_ = v___x_1900_;
v_bs_1893_ = v___x_1901_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__4_spec__5___boxed(lean_object* v_sz_1903_, lean_object* v_i_1904_, lean_object* v_bs_1905_){
_start:
{
size_t v_sz_boxed_1906_; size_t v_i_boxed_1907_; lean_object* v_res_1908_; 
v_sz_boxed_1906_ = lean_unbox_usize(v_sz_1903_);
lean_dec(v_sz_1903_);
v_i_boxed_1907_ = lean_unbox_usize(v_i_1904_);
lean_dec(v_i_1904_);
v_res_1908_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__4_spec__5(v_sz_boxed_1906_, v_i_boxed_1907_, v_bs_1905_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__4___redArg(lean_object* v_oldTraces_1909_, lean_object* v_data_1910_, lean_object* v_ref_1911_, lean_object* v_msg_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_){
_start:
{
lean_object* v_fileName_1918_; lean_object* v_fileMap_1919_; lean_object* v_options_1920_; lean_object* v_currRecDepth_1921_; lean_object* v_maxRecDepth_1922_; lean_object* v_ref_1923_; lean_object* v_currNamespace_1924_; lean_object* v_openDecls_1925_; lean_object* v_initHeartbeats_1926_; lean_object* v_maxHeartbeats_1927_; lean_object* v_quotContext_1928_; lean_object* v_currMacroScope_1929_; uint8_t v_diag_1930_; lean_object* v_cancelTk_x3f_1931_; uint8_t v_suppressElabErrors_1932_; lean_object* v_inheritedTraceOptions_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1988_; 
v_fileName_1918_ = lean_ctor_get(v___y_1915_, 0);
v_fileMap_1919_ = lean_ctor_get(v___y_1915_, 1);
v_options_1920_ = lean_ctor_get(v___y_1915_, 2);
v_currRecDepth_1921_ = lean_ctor_get(v___y_1915_, 3);
v_maxRecDepth_1922_ = lean_ctor_get(v___y_1915_, 4);
v_ref_1923_ = lean_ctor_get(v___y_1915_, 5);
v_currNamespace_1924_ = lean_ctor_get(v___y_1915_, 6);
v_openDecls_1925_ = lean_ctor_get(v___y_1915_, 7);
v_initHeartbeats_1926_ = lean_ctor_get(v___y_1915_, 8);
v_maxHeartbeats_1927_ = lean_ctor_get(v___y_1915_, 9);
v_quotContext_1928_ = lean_ctor_get(v___y_1915_, 10);
v_currMacroScope_1929_ = lean_ctor_get(v___y_1915_, 11);
v_diag_1930_ = lean_ctor_get_uint8(v___y_1915_, sizeof(void*)*14);
v_cancelTk_x3f_1931_ = lean_ctor_get(v___y_1915_, 12);
v_suppressElabErrors_1932_ = lean_ctor_get_uint8(v___y_1915_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1933_ = lean_ctor_get(v___y_1915_, 13);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___y_1915_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1935_ = v___y_1915_;
v_isShared_1936_ = v_isSharedCheck_1988_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_inheritedTraceOptions_1933_);
lean_inc(v_cancelTk_x3f_1931_);
lean_inc(v_currMacroScope_1929_);
lean_inc(v_quotContext_1928_);
lean_inc(v_maxHeartbeats_1927_);
lean_inc(v_initHeartbeats_1926_);
lean_inc(v_openDecls_1925_);
lean_inc(v_currNamespace_1924_);
lean_inc(v_ref_1923_);
lean_inc(v_maxRecDepth_1922_);
lean_inc(v_currRecDepth_1921_);
lean_inc(v_options_1920_);
lean_inc(v_fileMap_1919_);
lean_inc(v_fileName_1918_);
lean_dec(v___y_1915_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1988_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1937_; lean_object* v_traceState_1938_; lean_object* v_traces_1939_; lean_object* v_ref_1940_; lean_object* v___x_1942_; 
v___x_1937_ = lean_st_ref_get(v___y_1916_);
v_traceState_1938_ = lean_ctor_get(v___x_1937_, 4);
lean_inc_ref(v_traceState_1938_);
lean_dec(v___x_1937_);
v_traces_1939_ = lean_ctor_get(v_traceState_1938_, 0);
lean_inc_ref(v_traces_1939_);
lean_dec_ref(v_traceState_1938_);
v_ref_1940_ = l_Lean_replaceRef(v_ref_1911_, v_ref_1923_);
lean_dec(v_ref_1923_);
if (v_isShared_1936_ == 0)
{
lean_ctor_set(v___x_1935_, 5, v_ref_1940_);
v___x_1942_ = v___x_1935_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_fileName_1918_);
lean_ctor_set(v_reuseFailAlloc_1987_, 1, v_fileMap_1919_);
lean_ctor_set(v_reuseFailAlloc_1987_, 2, v_options_1920_);
lean_ctor_set(v_reuseFailAlloc_1987_, 3, v_currRecDepth_1921_);
lean_ctor_set(v_reuseFailAlloc_1987_, 4, v_maxRecDepth_1922_);
lean_ctor_set(v_reuseFailAlloc_1987_, 5, v_ref_1940_);
lean_ctor_set(v_reuseFailAlloc_1987_, 6, v_currNamespace_1924_);
lean_ctor_set(v_reuseFailAlloc_1987_, 7, v_openDecls_1925_);
lean_ctor_set(v_reuseFailAlloc_1987_, 8, v_initHeartbeats_1926_);
lean_ctor_set(v_reuseFailAlloc_1987_, 9, v_maxHeartbeats_1927_);
lean_ctor_set(v_reuseFailAlloc_1987_, 10, v_quotContext_1928_);
lean_ctor_set(v_reuseFailAlloc_1987_, 11, v_currMacroScope_1929_);
lean_ctor_set(v_reuseFailAlloc_1987_, 12, v_cancelTk_x3f_1931_);
lean_ctor_set(v_reuseFailAlloc_1987_, 13, v_inheritedTraceOptions_1933_);
lean_ctor_set_uint8(v_reuseFailAlloc_1987_, sizeof(void*)*14, v_diag_1930_);
lean_ctor_set_uint8(v_reuseFailAlloc_1987_, sizeof(void*)*14 + 1, v_suppressElabErrors_1932_);
v___x_1942_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
lean_object* v___x_1943_; size_t v_sz_1944_; size_t v___x_1945_; lean_object* v___x_1946_; lean_object* v_msg_1947_; lean_object* v___x_1948_; lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1986_; 
v___x_1943_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1939_);
lean_dec_ref(v_traces_1939_);
v_sz_1944_ = lean_array_size(v___x_1943_);
v___x_1945_ = ((size_t)0ULL);
v___x_1946_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__4_spec__5(v_sz_1944_, v___x_1945_, v___x_1943_);
v_msg_1947_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1947_, 0, v_data_1910_);
lean_ctor_set(v_msg_1947_, 1, v_msg_1912_);
lean_ctor_set(v_msg_1947_, 2, v___x_1946_);
v___x_1948_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1_spec__1(v_msg_1947_, v___y_1913_, v___y_1914_, v___x_1942_, v___y_1916_);
lean_dec_ref(v___x_1942_);
v_a_1949_ = lean_ctor_get(v___x_1948_, 0);
v_isSharedCheck_1986_ = !lean_is_exclusive(v___x_1948_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1951_ = v___x_1948_;
v_isShared_1952_ = v_isSharedCheck_1986_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___x_1948_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1986_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1953_; lean_object* v_traceState_1954_; lean_object* v_env_1955_; lean_object* v_nextMacroScope_1956_; lean_object* v_ngen_1957_; lean_object* v_auxDeclNGen_1958_; lean_object* v_cache_1959_; lean_object* v_messages_1960_; lean_object* v_infoState_1961_; lean_object* v_snapshotTasks_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1985_; 
v___x_1953_ = lean_st_ref_take(v___y_1916_);
v_traceState_1954_ = lean_ctor_get(v___x_1953_, 4);
v_env_1955_ = lean_ctor_get(v___x_1953_, 0);
v_nextMacroScope_1956_ = lean_ctor_get(v___x_1953_, 1);
v_ngen_1957_ = lean_ctor_get(v___x_1953_, 2);
v_auxDeclNGen_1958_ = lean_ctor_get(v___x_1953_, 3);
v_cache_1959_ = lean_ctor_get(v___x_1953_, 5);
v_messages_1960_ = lean_ctor_get(v___x_1953_, 6);
v_infoState_1961_ = lean_ctor_get(v___x_1953_, 7);
v_snapshotTasks_1962_ = lean_ctor_get(v___x_1953_, 8);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1953_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1964_ = v___x_1953_;
v_isShared_1965_ = v_isSharedCheck_1985_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_snapshotTasks_1962_);
lean_inc(v_infoState_1961_);
lean_inc(v_messages_1960_);
lean_inc(v_cache_1959_);
lean_inc(v_traceState_1954_);
lean_inc(v_auxDeclNGen_1958_);
lean_inc(v_ngen_1957_);
lean_inc(v_nextMacroScope_1956_);
lean_inc(v_env_1955_);
lean_dec(v___x_1953_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1985_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
uint64_t v_tid_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1983_; 
v_tid_1966_ = lean_ctor_get_uint64(v_traceState_1954_, sizeof(void*)*1);
v_isSharedCheck_1983_ = !lean_is_exclusive(v_traceState_1954_);
if (v_isSharedCheck_1983_ == 0)
{
lean_object* v_unused_1984_; 
v_unused_1984_ = lean_ctor_get(v_traceState_1954_, 0);
lean_dec(v_unused_1984_);
v___x_1968_ = v_traceState_1954_;
v_isShared_1969_ = v_isSharedCheck_1983_;
goto v_resetjp_1967_;
}
else
{
lean_dec(v_traceState_1954_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1983_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1973_; 
v___x_1970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1970_, 0, v_ref_1911_);
lean_ctor_set(v___x_1970_, 1, v_a_1949_);
v___x_1971_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1909_, v___x_1970_);
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 0, v___x_1971_);
v___x_1973_ = v___x_1968_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v___x_1971_);
lean_ctor_set_uint64(v_reuseFailAlloc_1982_, sizeof(void*)*1, v_tid_1966_);
v___x_1973_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
lean_object* v___x_1975_; 
if (v_isShared_1965_ == 0)
{
lean_ctor_set(v___x_1964_, 4, v___x_1973_);
v___x_1975_ = v___x_1964_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_env_1955_);
lean_ctor_set(v_reuseFailAlloc_1981_, 1, v_nextMacroScope_1956_);
lean_ctor_set(v_reuseFailAlloc_1981_, 2, v_ngen_1957_);
lean_ctor_set(v_reuseFailAlloc_1981_, 3, v_auxDeclNGen_1958_);
lean_ctor_set(v_reuseFailAlloc_1981_, 4, v___x_1973_);
lean_ctor_set(v_reuseFailAlloc_1981_, 5, v_cache_1959_);
lean_ctor_set(v_reuseFailAlloc_1981_, 6, v_messages_1960_);
lean_ctor_set(v_reuseFailAlloc_1981_, 7, v_infoState_1961_);
lean_ctor_set(v_reuseFailAlloc_1981_, 8, v_snapshotTasks_1962_);
v___x_1975_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1979_; 
v___x_1976_ = lean_st_ref_set(v___y_1916_, v___x_1975_);
v___x_1977_ = lean_box(0);
if (v_isShared_1952_ == 0)
{
lean_ctor_set(v___x_1951_, 0, v___x_1977_);
v___x_1979_ = v___x_1951_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v___x_1977_);
v___x_1979_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
return v___x_1979_;
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__4___redArg___boxed(lean_object* v_oldTraces_1989_, lean_object* v_data_1990_, lean_object* v_ref_1991_, lean_object* v_msg_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_){
_start:
{
lean_object* v_res_1998_; 
v_res_1998_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__4___redArg(v_oldTraces_1989_, v_data_1990_, v_ref_1991_, v_msg_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
lean_dec(v___y_1996_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
return v_res_1998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__6(lean_object* v_opts_1999_, lean_object* v_opt_2000_){
_start:
{
lean_object* v_name_2001_; lean_object* v_defValue_2002_; lean_object* v_map_2003_; lean_object* v___x_2004_; 
v_name_2001_ = lean_ctor_get(v_opt_2000_, 0);
v_defValue_2002_ = lean_ctor_get(v_opt_2000_, 1);
v_map_2003_ = lean_ctor_get(v_opts_1999_, 0);
v___x_2004_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2003_, v_name_2001_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_inc(v_defValue_2002_);
return v_defValue_2002_;
}
else
{
lean_object* v_val_2005_; 
v_val_2005_ = lean_ctor_get(v___x_2004_, 0);
lean_inc(v_val_2005_);
lean_dec_ref(v___x_2004_);
if (lean_obj_tag(v_val_2005_) == 3)
{
lean_object* v_v_2006_; 
v_v_2006_ = lean_ctor_get(v_val_2005_, 0);
lean_inc(v_v_2006_);
lean_dec_ref(v_val_2005_);
return v_v_2006_;
}
else
{
lean_dec(v_val_2005_);
lean_inc(v_defValue_2002_);
return v_defValue_2002_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__6___boxed(lean_object* v_opts_2007_, lean_object* v_opt_2008_){
_start:
{
lean_object* v_res_2009_; 
v_res_2009_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__6(v_opts_2007_, v_opt_2008_);
lean_dec_ref(v_opt_2008_);
lean_dec_ref(v_opts_2007_);
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__5___redArg(lean_object* v_x_2010_){
_start:
{
if (lean_obj_tag(v_x_2010_) == 0)
{
lean_object* v_a_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2019_; 
v_a_2012_ = lean_ctor_get(v_x_2010_, 0);
v_isSharedCheck_2019_ = !lean_is_exclusive(v_x_2010_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2014_ = v_x_2010_;
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_a_2012_);
lean_dec(v_x_2010_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2017_; 
if (v_isShared_2015_ == 0)
{
lean_ctor_set_tag(v___x_2014_, 1);
v___x_2017_ = v___x_2014_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_a_2012_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
return v___x_2017_;
}
}
}
else
{
lean_object* v_a_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2027_; 
v_a_2020_ = lean_ctor_get(v_x_2010_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v_x_2010_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2022_ = v_x_2010_;
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_a_2020_);
lean_dec(v_x_2010_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2025_; 
if (v_isShared_2023_ == 0)
{
lean_ctor_set_tag(v___x_2022_, 0);
v___x_2025_ = v___x_2022_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_a_2020_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
return v___x_2025_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__5___redArg___boxed(lean_object* v_x_2028_, lean_object* v___y_2029_){
_start:
{
lean_object* v_res_2030_; 
v_res_2030_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__5___redArg(v_x_2028_);
return v_res_2030_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__3(lean_object* v_e_2031_){
_start:
{
if (lean_obj_tag(v_e_2031_) == 0)
{
uint8_t v___x_2032_; 
v___x_2032_ = 2;
return v___x_2032_;
}
else
{
uint8_t v___x_2033_; 
v___x_2033_ = 0;
return v___x_2033_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__3___boxed(lean_object* v_e_2034_){
_start:
{
uint8_t v_res_2035_; lean_object* v_r_2036_; 
v_res_2035_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__3(v_e_2034_);
lean_dec_ref(v_e_2034_);
v_r_2036_ = lean_box(v_res_2035_);
return v_r_2036_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__1(void){
_start:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2038_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__0));
v___x_2039_ = l_Lean_stringToMessageData(v___x_2038_);
return v___x_2039_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__3(void){
_start:
{
lean_object* v___x_2041_; lean_object* v___x_2042_; 
v___x_2041_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__2));
v___x_2042_ = l_Lean_stringToMessageData(v___x_2041_);
return v___x_2042_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__4(void){
_start:
{
lean_object* v___x_2043_; double v___x_2044_; 
v___x_2043_ = lean_unsigned_to_nat(1000u);
v___x_2044_ = lean_float_of_nat(v___x_2043_);
return v___x_2044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(lean_object* v_cls_2045_, uint8_t v_collapsed_2046_, lean_object* v_tag_2047_, lean_object* v_opts_2048_, uint8_t v_clsEnabled_2049_, lean_object* v_oldTraces_2050_, lean_object* v_msg_2051_, lean_object* v_resStartStop_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_){
_start:
{
lean_object* v_fst_2063_; lean_object* v_snd_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2162_; 
v_fst_2063_ = lean_ctor_get(v_resStartStop_2052_, 0);
v_snd_2064_ = lean_ctor_get(v_resStartStop_2052_, 1);
v_isSharedCheck_2162_ = !lean_is_exclusive(v_resStartStop_2052_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2066_ = v_resStartStop_2052_;
v_isShared_2067_ = v_isSharedCheck_2162_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_snd_2064_);
lean_inc(v_fst_2063_);
lean_dec(v_resStartStop_2052_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2162_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___y_2069_; lean_object* v___y_2070_; lean_object* v_data_2071_; lean_object* v_fst_2082_; lean_object* v_snd_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2161_; 
v_fst_2082_ = lean_ctor_get(v_snd_2064_, 0);
v_snd_2083_ = lean_ctor_get(v_snd_2064_, 1);
v_isSharedCheck_2161_ = !lean_is_exclusive(v_snd_2064_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2085_ = v_snd_2064_;
v_isShared_2086_ = v_isSharedCheck_2161_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_snd_2083_);
lean_inc(v_fst_2082_);
lean_dec(v_snd_2064_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2161_;
goto v_resetjp_2084_;
}
v___jp_2068_:
{
lean_object* v___x_2072_; 
v___x_2072_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__4___redArg(v_oldTraces_2050_, v_data_2071_, v___y_2069_, v___y_2070_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_);
lean_dec(v___y_2061_);
lean_dec(v___y_2059_);
lean_dec_ref(v___y_2058_);
if (lean_obj_tag(v___x_2072_) == 0)
{
lean_object* v___x_2073_; 
lean_dec_ref(v___x_2072_);
v___x_2073_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__5___redArg(v_fst_2063_);
return v___x_2073_;
}
else
{
lean_object* v_a_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2081_; 
lean_dec(v_fst_2063_);
v_a_2074_ = lean_ctor_get(v___x_2072_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2076_ = v___x_2072_;
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_a_2074_);
lean_dec(v___x_2072_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2079_; 
if (v_isShared_2077_ == 0)
{
v___x_2079_ = v___x_2076_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_a_2074_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
return v___x_2079_;
}
}
}
}
v_resetjp_2084_:
{
lean_object* v___x_2087_; uint8_t v___x_2088_; lean_object* v___y_2090_; lean_object* v_a_2091_; uint8_t v___y_2115_; double v___y_2146_; 
v___x_2087_ = l_Lean_trace_profiler;
v___x_2088_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2(v_opts_2048_, v___x_2087_);
if (v___x_2088_ == 0)
{
v___y_2115_ = v___x_2088_;
goto v___jp_2114_;
}
else
{
lean_object* v___x_2151_; uint8_t v___x_2152_; 
v___x_2151_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2152_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2(v_opts_2048_, v___x_2151_);
if (v___x_2152_ == 0)
{
lean_object* v___x_2153_; lean_object* v___x_2154_; double v___x_2155_; double v___x_2156_; double v___x_2157_; 
v___x_2153_ = l_Lean_trace_profiler_threshold;
v___x_2154_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__6(v_opts_2048_, v___x_2153_);
v___x_2155_ = lean_float_of_nat(v___x_2154_);
v___x_2156_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__4);
v___x_2157_ = lean_float_div(v___x_2155_, v___x_2156_);
v___y_2146_ = v___x_2157_;
goto v___jp_2145_;
}
else
{
lean_object* v___x_2158_; lean_object* v___x_2159_; double v___x_2160_; 
v___x_2158_ = l_Lean_trace_profiler_threshold;
v___x_2159_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__6(v_opts_2048_, v___x_2158_);
v___x_2160_ = lean_float_of_nat(v___x_2159_);
v___y_2146_ = v___x_2160_;
goto v___jp_2145_;
}
}
v___jp_2089_:
{
uint8_t v_result_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2097_; 
v_result_2092_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__3(v_fst_2063_);
v___x_2093_ = l_Lean_TraceResult_toEmoji(v_result_2092_);
v___x_2094_ = l_Lean_stringToMessageData(v___x_2093_);
v___x_2095_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__1);
if (v_isShared_2086_ == 0)
{
lean_ctor_set_tag(v___x_2085_, 7);
lean_ctor_set(v___x_2085_, 1, v___x_2095_);
lean_ctor_set(v___x_2085_, 0, v___x_2094_);
v___x_2097_ = v___x_2085_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v___x_2094_);
lean_ctor_set(v_reuseFailAlloc_2108_, 1, v___x_2095_);
v___x_2097_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
lean_object* v_m_2099_; 
if (v_isShared_2067_ == 0)
{
lean_ctor_set_tag(v___x_2066_, 7);
lean_ctor_set(v___x_2066_, 1, v_a_2091_);
lean_ctor_set(v___x_2066_, 0, v___x_2097_);
v_m_2099_ = v___x_2066_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v___x_2097_);
lean_ctor_set(v_reuseFailAlloc_2107_, 1, v_a_2091_);
v_m_2099_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
lean_object* v___x_2100_; lean_object* v___x_2101_; double v___x_2102_; lean_object* v_data_2103_; 
v___x_2100_ = lean_box(v_result_2092_);
v___x_2101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2100_);
v___x_2102_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__0);
lean_inc_ref(v_tag_2047_);
lean_inc_ref(v___x_2101_);
lean_inc(v_cls_2045_);
v_data_2103_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2103_, 0, v_cls_2045_);
lean_ctor_set(v_data_2103_, 1, v___x_2101_);
lean_ctor_set(v_data_2103_, 2, v_tag_2047_);
lean_ctor_set_float(v_data_2103_, sizeof(void*)*3, v___x_2102_);
lean_ctor_set_float(v_data_2103_, sizeof(void*)*3 + 8, v___x_2102_);
lean_ctor_set_uint8(v_data_2103_, sizeof(void*)*3 + 16, v_collapsed_2046_);
if (v___x_2088_ == 0)
{
lean_dec_ref(v___x_2101_);
lean_dec(v_snd_2083_);
lean_dec(v_fst_2082_);
lean_dec_ref(v_tag_2047_);
lean_dec(v_cls_2045_);
v___y_2069_ = v___y_2090_;
v___y_2070_ = v_m_2099_;
v_data_2071_ = v_data_2103_;
goto v___jp_2068_;
}
else
{
lean_object* v_data_2104_; double v___x_2105_; double v___x_2106_; 
lean_dec_ref(v_data_2103_);
v_data_2104_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2104_, 0, v_cls_2045_);
lean_ctor_set(v_data_2104_, 1, v___x_2101_);
lean_ctor_set(v_data_2104_, 2, v_tag_2047_);
v___x_2105_ = lean_unbox_float(v_fst_2082_);
lean_dec(v_fst_2082_);
lean_ctor_set_float(v_data_2104_, sizeof(void*)*3, v___x_2105_);
v___x_2106_ = lean_unbox_float(v_snd_2083_);
lean_dec(v_snd_2083_);
lean_ctor_set_float(v_data_2104_, sizeof(void*)*3 + 8, v___x_2106_);
lean_ctor_set_uint8(v_data_2104_, sizeof(void*)*3 + 16, v_collapsed_2046_);
v___y_2069_ = v___y_2090_;
v___y_2070_ = v_m_2099_;
v_data_2071_ = v_data_2104_;
goto v___jp_2068_;
}
}
}
}
v___jp_2109_:
{
lean_object* v_ref_2110_; lean_object* v___x_2111_; 
v_ref_2110_ = lean_ctor_get(v___y_2060_, 5);
lean_inc(v___y_2061_);
lean_inc_ref(v___y_2060_);
lean_inc(v___y_2059_);
lean_inc_ref(v___y_2058_);
lean_inc(v_fst_2063_);
v___x_2111_ = lean_apply_11(v_msg_2051_, v_fst_2063_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_, lean_box(0));
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_object* v_a_2112_; 
v_a_2112_ = lean_ctor_get(v___x_2111_, 0);
lean_inc(v_a_2112_);
lean_dec_ref(v___x_2111_);
lean_inc(v_ref_2110_);
v___y_2090_ = v_ref_2110_;
v_a_2091_ = v_a_2112_;
goto v___jp_2089_;
}
else
{
lean_object* v___x_2113_; 
lean_dec_ref(v___x_2111_);
v___x_2113_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__3);
lean_inc(v_ref_2110_);
v___y_2090_ = v_ref_2110_;
v_a_2091_ = v___x_2113_;
goto v___jp_2089_;
}
}
v___jp_2114_:
{
if (v_clsEnabled_2049_ == 0)
{
if (v___y_2115_ == 0)
{
lean_object* v___x_2116_; lean_object* v_traceState_2117_; lean_object* v_env_2118_; lean_object* v_nextMacroScope_2119_; lean_object* v_ngen_2120_; lean_object* v_auxDeclNGen_2121_; lean_object* v_cache_2122_; lean_object* v_messages_2123_; lean_object* v_infoState_2124_; lean_object* v_snapshotTasks_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2144_; 
lean_del_object(v___x_2085_);
lean_dec(v_snd_2083_);
lean_dec(v_fst_2082_);
lean_del_object(v___x_2066_);
lean_dec_ref(v___y_2060_);
lean_dec(v___y_2059_);
lean_dec_ref(v___y_2058_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
lean_dec(v___y_2053_);
lean_dec_ref(v_msg_2051_);
lean_dec_ref(v_tag_2047_);
lean_dec(v_cls_2045_);
v___x_2116_ = lean_st_ref_take(v___y_2061_);
v_traceState_2117_ = lean_ctor_get(v___x_2116_, 4);
v_env_2118_ = lean_ctor_get(v___x_2116_, 0);
v_nextMacroScope_2119_ = lean_ctor_get(v___x_2116_, 1);
v_ngen_2120_ = lean_ctor_get(v___x_2116_, 2);
v_auxDeclNGen_2121_ = lean_ctor_get(v___x_2116_, 3);
v_cache_2122_ = lean_ctor_get(v___x_2116_, 5);
v_messages_2123_ = lean_ctor_get(v___x_2116_, 6);
v_infoState_2124_ = lean_ctor_get(v___x_2116_, 7);
v_snapshotTasks_2125_ = lean_ctor_get(v___x_2116_, 8);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2127_ = v___x_2116_;
v_isShared_2128_ = v_isSharedCheck_2144_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_snapshotTasks_2125_);
lean_inc(v_infoState_2124_);
lean_inc(v_messages_2123_);
lean_inc(v_cache_2122_);
lean_inc(v_traceState_2117_);
lean_inc(v_auxDeclNGen_2121_);
lean_inc(v_ngen_2120_);
lean_inc(v_nextMacroScope_2119_);
lean_inc(v_env_2118_);
lean_dec(v___x_2116_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2144_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
uint64_t v_tid_2129_; lean_object* v_traces_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2143_; 
v_tid_2129_ = lean_ctor_get_uint64(v_traceState_2117_, sizeof(void*)*1);
v_traces_2130_ = lean_ctor_get(v_traceState_2117_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v_traceState_2117_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2132_ = v_traceState_2117_;
v_isShared_2133_ = v_isSharedCheck_2143_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_traces_2130_);
lean_dec(v_traceState_2117_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2143_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2134_; lean_object* v___x_2136_; 
v___x_2134_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2050_, v_traces_2130_);
lean_dec_ref(v_traces_2130_);
if (v_isShared_2133_ == 0)
{
lean_ctor_set(v___x_2132_, 0, v___x_2134_);
v___x_2136_ = v___x_2132_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v___x_2134_);
lean_ctor_set_uint64(v_reuseFailAlloc_2142_, sizeof(void*)*1, v_tid_2129_);
v___x_2136_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
lean_object* v___x_2138_; 
if (v_isShared_2128_ == 0)
{
lean_ctor_set(v___x_2127_, 4, v___x_2136_);
v___x_2138_ = v___x_2127_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_env_2118_);
lean_ctor_set(v_reuseFailAlloc_2141_, 1, v_nextMacroScope_2119_);
lean_ctor_set(v_reuseFailAlloc_2141_, 2, v_ngen_2120_);
lean_ctor_set(v_reuseFailAlloc_2141_, 3, v_auxDeclNGen_2121_);
lean_ctor_set(v_reuseFailAlloc_2141_, 4, v___x_2136_);
lean_ctor_set(v_reuseFailAlloc_2141_, 5, v_cache_2122_);
lean_ctor_set(v_reuseFailAlloc_2141_, 6, v_messages_2123_);
lean_ctor_set(v_reuseFailAlloc_2141_, 7, v_infoState_2124_);
lean_ctor_set(v_reuseFailAlloc_2141_, 8, v_snapshotTasks_2125_);
v___x_2138_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___x_2139_ = lean_st_ref_set(v___y_2061_, v___x_2138_);
lean_dec(v___y_2061_);
v___x_2140_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__5___redArg(v_fst_2063_);
return v___x_2140_;
}
}
}
}
}
else
{
goto v___jp_2109_;
}
}
else
{
goto v___jp_2109_;
}
}
v___jp_2145_:
{
double v___x_2147_; double v___x_2148_; double v___x_2149_; uint8_t v___x_2150_; 
v___x_2147_ = lean_unbox_float(v_snd_2083_);
v___x_2148_ = lean_unbox_float(v_fst_2082_);
v___x_2149_ = lean_float_sub(v___x_2147_, v___x_2148_);
v___x_2150_ = lean_float_decLt(v___y_2146_, v___x_2149_);
v___y_2115_ = v___x_2150_;
goto v___jp_2114_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___boxed(lean_object** _args){
lean_object* v_cls_2163_ = _args[0];
lean_object* v_collapsed_2164_ = _args[1];
lean_object* v_tag_2165_ = _args[2];
lean_object* v_opts_2166_ = _args[3];
lean_object* v_clsEnabled_2167_ = _args[4];
lean_object* v_oldTraces_2168_ = _args[5];
lean_object* v_msg_2169_ = _args[6];
lean_object* v_resStartStop_2170_ = _args[7];
lean_object* v___y_2171_ = _args[8];
lean_object* v___y_2172_ = _args[9];
lean_object* v___y_2173_ = _args[10];
lean_object* v___y_2174_ = _args[11];
lean_object* v___y_2175_ = _args[12];
lean_object* v___y_2176_ = _args[13];
lean_object* v___y_2177_ = _args[14];
lean_object* v___y_2178_ = _args[15];
lean_object* v___y_2179_ = _args[16];
lean_object* v___y_2180_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_2181_; uint8_t v_clsEnabled_boxed_2182_; lean_object* v_res_2183_; 
v_collapsed_boxed_2181_ = lean_unbox(v_collapsed_2164_);
v_clsEnabled_boxed_2182_ = lean_unbox(v_clsEnabled_2167_);
v_res_2183_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_cls_2163_, v_collapsed_boxed_2181_, v_tag_2165_, v_opts_2166_, v_clsEnabled_boxed_2182_, v_oldTraces_2168_, v_msg_2169_, v_resStartStop_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_);
lean_dec_ref(v_opts_2166_);
return v_res_2183_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__3(void){
_start:
{
lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2189_ = lean_unsigned_to_nat(0u);
v___x_2190_ = l_Lean_Expr_bvar___override(v___x_2189_);
return v___x_2190_;
}
}
static double _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4(void){
_start:
{
lean_object* v___x_2191_; double v___x_2192_; 
v___x_2191_ = lean_unsigned_to_nat(1000000000u);
v___x_2192_ = lean_float_of_nat(v___x_2191_);
return v___x_2192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj(lean_object* v_e_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_){
_start:
{
lean_object* v___y_2205_; uint8_t v___y_2206_; lean_object* v_a_2207_; lean_object* v___y_2211_; lean_object* v_a_2212_; 
if (lean_obj_tag(v_e_2193_) == 11)
{
lean_object* v_typeName_2216_; lean_object* v_idx_2217_; lean_object* v_struct_2218_; lean_object* v_res_2220_; lean_object* v___y_2221_; lean_object* v___y_2222_; lean_object* v___y_2223_; lean_object* v___y_2224_; lean_object* v___y_2225_; lean_object* v___y_2226_; lean_object* v___y_2227_; lean_object* v___y_2228_; lean_object* v___y_2229_; lean_object* v_options_2426_; uint8_t v_hasTrace_2427_; 
v_typeName_2216_ = lean_ctor_get(v_e_2193_, 0);
v_idx_2217_ = lean_ctor_get(v_e_2193_, 1);
v_struct_2218_ = lean_ctor_get(v_e_2193_, 2);
v_options_2426_ = lean_ctor_get(v_a_2201_, 2);
v_hasTrace_2427_ = lean_ctor_get_uint8(v_options_2426_, sizeof(void*)*1);
if (v_hasTrace_2427_ == 0)
{
lean_object* v___x_2428_; 
lean_inc(v_a_2202_);
lean_inc_ref(v_a_2201_);
lean_inc(v_a_2200_);
lean_inc_ref(v_a_2199_);
lean_inc(v_a_2198_);
lean_inc_ref(v_a_2197_);
lean_inc(v_a_2196_);
lean_inc_ref(v_a_2195_);
lean_inc(v_a_2194_);
lean_inc_ref(v_struct_2218_);
v___x_2428_ = lean_sym_simp(v_struct_2218_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_);
if (lean_obj_tag(v___x_2428_) == 0)
{
lean_object* v_a_2429_; 
v_a_2429_ = lean_ctor_get(v___x_2428_, 0);
lean_inc(v_a_2429_);
lean_dec_ref(v___x_2428_);
v_res_2220_ = v_a_2429_;
v___y_2221_ = v_a_2194_;
v___y_2222_ = v_a_2195_;
v___y_2223_ = v_a_2196_;
v___y_2224_ = v_a_2197_;
v___y_2225_ = v_a_2198_;
v___y_2226_ = v_a_2199_;
v___y_2227_ = v_a_2200_;
v___y_2228_ = v_a_2201_;
v___y_2229_ = v_a_2202_;
goto v___jp_2219_;
}
else
{
lean_dec_ref(v_e_2193_);
lean_dec(v_a_2202_);
lean_dec_ref(v_a_2201_);
lean_dec(v_a_2200_);
lean_dec_ref(v_a_2199_);
lean_dec(v_a_2198_);
lean_dec_ref(v_a_2197_);
lean_dec(v_a_2196_);
lean_dec_ref(v_a_2195_);
lean_dec(v_a_2194_);
return v___x_2428_;
}
}
else
{
lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v_a_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2688_; 
v___x_2430_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2));
v___x_2431_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(v___x_2430_, v_a_2201_);
v_a_2432_ = lean_ctor_get(v___x_2431_, 0);
v_isSharedCheck_2688_ = !lean_is_exclusive(v___x_2431_);
if (v_isSharedCheck_2688_ == 0)
{
v___x_2434_ = v___x_2431_;
v_isShared_2435_ = v_isSharedCheck_2688_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_a_2432_);
lean_dec(v___x_2431_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2688_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v___f_2436_; lean_object* v___x_2437_; lean_object* v___y_2439_; lean_object* v___y_2440_; lean_object* v_a_2441_; lean_object* v___y_2455_; lean_object* v___y_2456_; lean_object* v_a_2457_; lean_object* v___y_2462_; lean_object* v___y_2463_; lean_object* v_a_2464_; lean_object* v___y_2467_; lean_object* v___y_2468_; lean_object* v___y_2469_; uint8_t v___y_2470_; lean_object* v_a_2471_; lean_object* v___y_2474_; lean_object* v___y_2475_; lean_object* v___y_2476_; uint8_t v___y_2477_; lean_object* v_a_2478_; lean_object* v___y_2481_; lean_object* v___y_2482_; lean_object* v_a_2483_; lean_object* v___y_2494_; lean_object* v___y_2495_; lean_object* v_a_2496_; lean_object* v___y_2499_; lean_object* v___y_2500_; lean_object* v_a_2501_; uint8_t v___y_2504_; lean_object* v___y_2505_; lean_object* v___y_2506_; lean_object* v___y_2507_; lean_object* v_a_2508_; lean_object* v___y_2511_; lean_object* v___y_2512_; lean_object* v___y_2513_; lean_object* v_a_2514_; uint8_t v___x_2683_; 
lean_inc_ref(v_e_2193_);
lean_inc(v_idx_2217_);
lean_inc(v_typeName_2216_);
v___f_2436_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___boxed), 14, 3);
lean_closure_set(v___f_2436_, 0, v_typeName_2216_);
lean_closure_set(v___f_2436_, 1, v_idx_2217_);
lean_closure_set(v___f_2436_, 2, v_e_2193_);
v___x_2437_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__1));
v___x_2683_ = lean_unbox(v_a_2432_);
if (v___x_2683_ == 0)
{
lean_object* v___x_2684_; uint8_t v___x_2685_; 
v___x_2684_ = l_Lean_trace_profiler;
v___x_2685_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2(v_options_2426_, v___x_2684_);
if (v___x_2685_ == 0)
{
lean_object* v___x_2686_; 
lean_dec_ref(v___f_2436_);
lean_del_object(v___x_2434_);
lean_dec(v_a_2432_);
lean_inc(v_a_2202_);
lean_inc_ref(v_a_2201_);
lean_inc(v_a_2200_);
lean_inc_ref(v_a_2199_);
lean_inc(v_a_2198_);
lean_inc_ref(v_a_2197_);
lean_inc(v_a_2196_);
lean_inc_ref(v_a_2195_);
lean_inc(v_a_2194_);
lean_inc_ref(v_struct_2218_);
v___x_2686_ = lean_sym_simp(v_struct_2218_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_);
if (lean_obj_tag(v___x_2686_) == 0)
{
lean_object* v_a_2687_; 
v_a_2687_ = lean_ctor_get(v___x_2686_, 0);
lean_inc(v_a_2687_);
lean_dec_ref(v___x_2686_);
v_res_2220_ = v_a_2687_;
v___y_2221_ = v_a_2194_;
v___y_2222_ = v_a_2195_;
v___y_2223_ = v_a_2196_;
v___y_2224_ = v_a_2197_;
v___y_2225_ = v_a_2198_;
v___y_2226_ = v_a_2199_;
v___y_2227_ = v_a_2200_;
v___y_2228_ = v_a_2201_;
v___y_2229_ = v_a_2202_;
goto v___jp_2219_;
}
else
{
lean_dec_ref(v_e_2193_);
lean_dec(v_a_2202_);
lean_dec_ref(v_a_2201_);
lean_dec(v_a_2200_);
lean_dec_ref(v_a_2199_);
lean_dec(v_a_2198_);
lean_dec_ref(v_a_2197_);
lean_dec(v_a_2196_);
lean_dec_ref(v_a_2195_);
lean_dec(v_a_2194_);
return v___x_2686_;
}
}
else
{
lean_inc_ref(v_options_2426_);
goto v___jp_2517_;
}
}
else
{
lean_inc_ref(v_options_2426_);
goto v___jp_2517_;
}
v___jp_2438_:
{
lean_object* v___x_2442_; double v___x_2443_; double v___x_2444_; double v___x_2445_; double v___x_2446_; double v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; uint8_t v___x_2452_; lean_object* v___x_2453_; 
v___x_2442_ = lean_io_mono_nanos_now();
v___x_2443_ = lean_float_of_nat(v___y_2439_);
v___x_2444_ = lean_float_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4);
v___x_2445_ = lean_float_div(v___x_2443_, v___x_2444_);
v___x_2446_ = lean_float_of_nat(v___x_2442_);
v___x_2447_ = lean_float_div(v___x_2446_, v___x_2444_);
v___x_2448_ = lean_box_float(v___x_2445_);
v___x_2449_ = lean_box_float(v___x_2447_);
v___x_2450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2450_, 0, v___x_2448_);
lean_ctor_set(v___x_2450_, 1, v___x_2449_);
v___x_2451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2451_, 0, v_a_2441_);
lean_ctor_set(v___x_2451_, 1, v___x_2450_);
v___x_2452_ = lean_unbox(v_a_2432_);
lean_dec(v_a_2432_);
v___x_2453_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v___x_2430_, v_hasTrace_2427_, v___x_2437_, v_options_2426_, v___x_2452_, v___y_2440_, v___f_2436_, v___x_2451_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_);
lean_dec_ref(v_options_2426_);
return v___x_2453_;
}
v___jp_2454_:
{
lean_object* v___x_2459_; 
if (v_isShared_2435_ == 0)
{
lean_ctor_set(v___x_2434_, 0, v_a_2457_);
v___x_2459_ = v___x_2434_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v_a_2457_);
v___x_2459_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
v___y_2439_ = v___y_2455_;
v___y_2440_ = v___y_2456_;
v_a_2441_ = v___x_2459_;
goto v___jp_2438_;
}
}
v___jp_2461_:
{
lean_object* v___x_2465_; 
v___x_2465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2465_, 0, v_a_2464_);
v___y_2439_ = v___y_2462_;
v___y_2440_ = v___y_2463_;
v_a_2441_ = v___x_2465_;
goto v___jp_2438_;
}
v___jp_2466_:
{
lean_object* v___x_2472_; 
v___x_2472_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_2472_, 0, v_a_2471_);
lean_ctor_set(v___x_2472_, 1, v___y_2468_);
lean_ctor_set_uint8(v___x_2472_, sizeof(void*)*2, v___y_2470_);
v___y_2462_ = v___y_2467_;
v___y_2463_ = v___y_2469_;
v_a_2464_ = v___x_2472_;
goto v___jp_2461_;
}
v___jp_2473_:
{
lean_object* v___x_2479_; 
v___x_2479_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_2479_, 0, v_a_2478_);
lean_ctor_set(v___x_2479_, 1, v___y_2475_);
lean_ctor_set_uint8(v___x_2479_, sizeof(void*)*2, v___y_2477_);
v___y_2462_ = v___y_2474_;
v___y_2463_ = v___y_2476_;
v_a_2464_ = v___x_2479_;
goto v___jp_2461_;
}
v___jp_2480_:
{
lean_object* v___x_2484_; double v___x_2485_; double v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; uint8_t v___x_2491_; lean_object* v___x_2492_; 
v___x_2484_ = lean_io_get_num_heartbeats();
v___x_2485_ = lean_float_of_nat(v___y_2481_);
v___x_2486_ = lean_float_of_nat(v___x_2484_);
v___x_2487_ = lean_box_float(v___x_2485_);
v___x_2488_ = lean_box_float(v___x_2486_);
v___x_2489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2489_, 0, v___x_2487_);
lean_ctor_set(v___x_2489_, 1, v___x_2488_);
v___x_2490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2490_, 0, v_a_2483_);
lean_ctor_set(v___x_2490_, 1, v___x_2489_);
v___x_2491_ = lean_unbox(v_a_2432_);
lean_dec(v_a_2432_);
v___x_2492_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v___x_2430_, v_hasTrace_2427_, v___x_2437_, v_options_2426_, v___x_2491_, v___y_2482_, v___f_2436_, v___x_2490_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_);
lean_dec_ref(v_options_2426_);
return v___x_2492_;
}
v___jp_2493_:
{
lean_object* v___x_2497_; 
v___x_2497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2497_, 0, v_a_2496_);
v___y_2481_ = v___y_2494_;
v___y_2482_ = v___y_2495_;
v_a_2483_ = v___x_2497_;
goto v___jp_2480_;
}
v___jp_2498_:
{
lean_object* v___x_2502_; 
v___x_2502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2502_, 0, v_a_2501_);
v___y_2481_ = v___y_2499_;
v___y_2482_ = v___y_2500_;
v_a_2483_ = v___x_2502_;
goto v___jp_2480_;
}
v___jp_2503_:
{
lean_object* v___x_2509_; 
v___x_2509_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_2509_, 0, v_a_2508_);
lean_ctor_set(v___x_2509_, 1, v___y_2505_);
lean_ctor_set_uint8(v___x_2509_, sizeof(void*)*2, v___y_2504_);
v___y_2499_ = v___y_2506_;
v___y_2500_ = v___y_2507_;
v_a_2501_ = v___x_2509_;
goto v___jp_2498_;
}
v___jp_2510_:
{
uint8_t v___x_2515_; lean_object* v___x_2516_; 
v___x_2515_ = 0;
v___x_2516_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_2516_, 0, v_a_2514_);
lean_ctor_set(v___x_2516_, 1, v___y_2512_);
lean_ctor_set_uint8(v___x_2516_, sizeof(void*)*2, v___x_2515_);
v___y_2499_ = v___y_2511_;
v___y_2500_ = v___y_2513_;
v_a_2501_ = v___x_2516_;
goto v___jp_2498_;
}
v___jp_2517_:
{
lean_object* v___x_2518_; lean_object* v_a_2519_; lean_object* v___x_2520_; uint8_t v___x_2521_; 
v___x_2518_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___redArg(v_a_2202_);
v_a_2519_ = lean_ctor_get(v___x_2518_, 0);
lean_inc(v_a_2519_);
lean_dec_ref(v___x_2518_);
v___x_2520_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2521_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2(v_options_2426_, v___x_2520_);
if (v___x_2521_ == 0)
{
lean_object* v___x_2522_; lean_object* v___x_2523_; 
v___x_2522_ = lean_io_mono_nanos_now();
lean_inc(v_a_2202_);
lean_inc_ref(v_a_2201_);
lean_inc(v_a_2200_);
lean_inc_ref(v_a_2199_);
lean_inc(v_a_2198_);
lean_inc_ref(v_a_2197_);
lean_inc(v_a_2196_);
lean_inc_ref(v_a_2195_);
lean_inc(v_a_2194_);
lean_inc_ref(v_struct_2218_);
v___x_2523_ = lean_sym_simp(v_struct_2218_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_);
if (lean_obj_tag(v___x_2523_) == 0)
{
lean_object* v_a_2524_; 
v_a_2524_ = lean_ctor_get(v___x_2523_, 0);
lean_inc(v_a_2524_);
lean_dec_ref(v___x_2523_);
if (lean_obj_tag(v_a_2524_) == 0)
{
lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2543_; 
v_isSharedCheck_2543_ = !lean_is_exclusive(v_a_2524_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2526_ = v_a_2524_;
v_isShared_2527_ = v_isSharedCheck_2543_;
goto v_resetjp_2525_;
}
else
{
lean_dec(v_a_2524_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2543_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2528_; lean_object* v___x_2529_; 
v___x_2528_ = lean_alloc_closure((void*)(l_Lean_Meta_reduceProj_x3f___boxed), 6, 1);
lean_closure_set(v___x_2528_, 0, v_e_2193_);
lean_inc(v_a_2202_);
lean_inc_ref(v_a_2201_);
lean_inc(v_a_2200_);
lean_inc_ref(v_a_2199_);
v___x_2529_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___x_2528_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_);
if (lean_obj_tag(v___x_2529_) == 0)
{
lean_object* v_a_2530_; 
v_a_2530_ = lean_ctor_get(v___x_2529_, 0);
lean_inc(v_a_2530_);
lean_dec_ref(v___x_2529_);
if (lean_obj_tag(v_a_2530_) == 1)
{
lean_object* v_val_2531_; lean_object* v___x_2532_; 
lean_del_object(v___x_2526_);
v_val_2531_ = lean_ctor_get(v_a_2530_, 0);
lean_inc(v_val_2531_);
lean_dec_ref(v_a_2530_);
v___x_2532_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_val_2531_, v_a_2198_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_object* v_a_2533_; lean_object* v___x_2534_; 
v_a_2533_ = lean_ctor_get(v___x_2532_, 0);
lean_inc(v_a_2533_);
lean_dec_ref(v___x_2532_);
lean_inc(v_a_2202_);
lean_inc_ref(v_a_2201_);
lean_inc(v_a_2200_);
lean_inc_ref(v_a_2199_);
lean_inc(v_a_2533_);
v___x_2534_ = l_Lean_Meta_Sym_mkEqRefl___redArg(v_a_2533_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_);
if (lean_obj_tag(v___x_2534_) == 0)
{
lean_object* v_a_2535_; lean_object* v___x_2536_; 
lean_del_object(v___x_2434_);
v_a_2535_ = lean_ctor_get(v___x_2534_, 0);
lean_inc(v_a_2535_);
lean_dec_ref(v___x_2534_);
v___x_2536_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_2536_, 0, v_a_2533_);
lean_ctor_set(v___x_2536_, 1, v_a_2535_);
lean_ctor_set_uint8(v___x_2536_, sizeof(void*)*2, v___x_2521_);
v___y_2462_ = v___x_2522_;
v___y_2463_ = v_a_2519_;
v_a_2464_ = v___x_2536_;
goto v___jp_2461_;
}
else
{
lean_object* v_a_2537_; 
lean_dec(v_a_2533_);
v_a_2537_ = lean_ctor_get(v___x_2534_, 0);
lean_inc(v_a_2537_);
lean_dec_ref(v___x_2534_);
v___y_2455_ = v___x_2522_;
v___y_2456_ = v_a_2519_;
v_a_2457_ = v_a_2537_;
goto v___jp_2454_;
}
}
else
{
lean_object* v_a_2538_; 
v_a_2538_ = lean_ctor_get(v___x_2532_, 0);
lean_inc(v_a_2538_);
lean_dec_ref(v___x_2532_);
v___y_2455_ = v___x_2522_;
v___y_2456_ = v_a_2519_;
v_a_2457_ = v_a_2538_;
goto v___jp_2454_;
}
}
else
{
lean_object* v___x_2540_; 
lean_dec(v_a_2530_);
lean_del_object(v___x_2434_);
if (v_isShared_2527_ == 0)
{
v___x_2540_ = v___x_2526_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(0, 0, 1);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
lean_ctor_set_uint8(v___x_2540_, 0, v_hasTrace_2427_);
v___y_2462_ = v___x_2522_;
v___y_2463_ = v_a_2519_;
v_a_2464_ = v___x_2540_;
goto v___jp_2461_;
}
}
}
else
{
lean_object* v_a_2542_; 
lean_del_object(v___x_2526_);
v_a_2542_ = lean_ctor_get(v___x_2529_, 0);
lean_inc(v_a_2542_);
lean_dec_ref(v___x_2529_);
v___y_2455_ = v___x_2522_;
v___y_2456_ = v_a_2519_;
v_a_2457_ = v_a_2542_;
goto v___jp_2454_;
}
}
}
else
{
lean_object* v_e_x27_2544_; lean_object* v_proof_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2599_; 
v_e_x27_2544_ = lean_ctor_get(v_a_2524_, 0);
v_proof_2545_ = lean_ctor_get(v_a_2524_, 1);
v_isSharedCheck_2599_ = !lean_is_exclusive(v_a_2524_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2547_ = v_a_2524_;
v_isShared_2548_ = v_isSharedCheck_2599_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_proof_2545_);
lean_inc(v_e_x27_2544_);
lean_dec(v_a_2524_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2599_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v___x_2549_; 
lean_inc(v_a_2202_);
lean_inc_ref(v_a_2201_);
lean_inc(v_a_2200_);
lean_inc_ref(v_a_2199_);
lean_inc_ref(v_e_x27_2544_);
v___x_2549_ = l_Lean_Meta_Sym_inferType___redArg(v_e_x27_2544_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_);
if (lean_obj_tag(v___x_2549_) == 0)
{
lean_object* v_a_2550_; lean_object* v___x_2551_; uint8_t v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; 
v_a_2550_ = lean_ctor_get(v___x_2549_, 0);
lean_inc(v_a_2550_);
lean_dec_ref(v___x_2549_);
v___x_2551_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2));
v___x_2552_ = 0;
v___x_2553_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__3, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__3_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__3);
lean_inc(v_idx_2217_);
lean_inc(v_typeName_2216_);
v___x_2554_ = l_Lean_Expr_proj___override(v_typeName_2216_, v_idx_2217_, v___x_2553_);
v___x_2555_ = l_Lean_mkLambda(v___x_2551_, v___x_2552_, v_a_2550_, v___x_2554_);
lean_inc(v_a_2202_);
lean_inc_ref(v_a_2201_);
lean_inc(v_a_2200_);
lean_inc_ref(v_a_2199_);
lean_inc_ref(v___x_2555_);
v___x_2556_ = lean_infer_type(v___x_2555_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_);
if (lean_obj_tag(v___x_2556_) == 0)
{
lean_object* v_a_2557_; uint8_t v___x_2558_; 
v_a_2557_ = lean_ctor_get(v___x_2556_, 0);
lean_inc(v_a_2557_);
lean_dec_ref(v___x_2556_);
v___x_2558_ = l_Lean_Expr_isArrow(v_a_2557_);
lean_dec(v_a_2557_);
if (v___x_2558_ == 0)
{
lean_object* v___x_2559_; lean_object* v___x_2560_; 
lean_inc_ref(v_e_2193_);
v___x_2559_ = lean_alloc_closure((void*)(l_Lean_Meta_reduceProj_x3f___boxed), 6, 1);
lean_closure_set(v___x_2559_, 0, v_e_2193_);
lean_inc(v_a_2202_);
lean_inc_ref(v_a_2201_);
lean_inc(v_a_2200_);
lean_inc_ref(v_a_2199_);
v___x_2560_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___x_2559_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_);
if (lean_obj_tag(v___x_2560_) == 0)
{
lean_object* v_a_2561_; 
v_a_2561_ = lean_ctor_get(v___x_2560_, 0);
lean_inc(v_a_2561_);
lean_dec_ref(v___x_2560_);
if (lean_obj_tag(v_a_2561_) == 0)
{
lean_object* v___x_2562_; 
lean_del_object(v___x_2547_);
lean_inc(v_a_2202_);
lean_inc_ref(v_a_2201_);
lean_inc(v_a_2200_);
lean_inc_ref(v_a_2199_);
lean_inc_ref(v_e_x27_2544_);
lean_inc_ref(v_struct_2218_);
v___x_2562_ = l_Lean_Meta_isExprDefEq(v_struct_2218_, v_e_x27_2544_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_);
if (lean_obj_tag(v___x_2562_) == 0)
{
lean_object* v_a_2563_; uint8_t v___x_2564_; 
v_a_2563_ = lean_ctor_get(v___x_2562_, 0);
lean_inc(v_a_2563_);
lean_dec_ref(v___x_2562_);
v___x_2564_ = lean_unbox(v_a_2563_);
lean_dec(v_a_2563_);
if (v___x_2564_ == 0)
{
lean_object* v___x_2565_; 
lean_dec_ref(v___x_2555_);
lean_dec_ref(v_proof_2545_);
lean_dec_ref(v_e_x27_2544_);
lean_del_object(v___x_2434_);
lean_dec_ref(v_e_2193_);
v___x_2565_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_2565_, 0, v_hasTrace_2427_);
v___y_2462_ = v___x_2522_;
v___y_2463_ = v_a_2519_;
v_a_2464_ = v___x_2565_;
goto v___jp_2461_;
}
else
{
lean_object* v___x_2566_; 
lean_inc(v_a_2202_);
lean_inc_ref(v_a_2201_);
lean_inc(v_a_2200_);
lean_inc_ref(v_a_2199_);
v___x_2566_ = l_Lean_Meta_mkHCongr(v___x_2555_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v_a_2567_; lean_object* v_proof_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; 
v_a_2567_ = lean_ctor_get(v___x_2566_, 0);
lean_inc(v_a_2567_);
lean_dec_ref(v___x_2566_);
v_proof_2568_ = lean_ctor_get(v_a_2567_, 1);
lean_inc_ref(v_proof_2568_);
lean_dec(v_a_2567_);
lean_inc_ref(v_e_x27_2544_);
lean_inc_ref(v_struct_2218_);
v___x_2569_ = l_Lean_mkApp3(v_proof_2568_, v_struct_2218_, v_e_x27_2544_, v_proof_2545_);
lean_inc(v_a_2202_);
lean_inc_ref(v_a_2201_);
lean_inc(v_a_2200_);
lean_inc_ref(v_a_2199_);
v___x_2570_ = l_Lean_Meta_mkEqOfHEq(v___x_2569_, v___x_2521_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_);
if (lean_obj_tag(v___x_2570_) == 0)
{
lean_object* v_a_2571_; uint8_t v___x_2572_; 
v_a_2571_ = lean_ctor_get(v___x_2570_, 0);
lean_inc(v_a_2571_);
lean_dec_ref(v___x_2570_);
v___x_2572_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_2218_, v_e_x27_2544_);
if (v___x_2572_ == 0)
{
lean_object* v___x_2573_; 
lean_inc(v_idx_2217_);
lean_inc(v_typeName_2216_);
lean_dec_ref(v_e_2193_);
lean_inc(v_a_2202_);
lean_inc_ref(v_a_2201_);
lean_inc(v_a_2200_);
lean_inc_ref(v_a_2199_);
lean_inc(v_a_2198_);
lean_inc_ref(v_a_2197_);
v___x_2573_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_typeName_2216_, v_idx_2217_, v_e_x27_2544_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_);
if (lean_obj_tag(v___x_2573_) == 0)
{
lean_object* v_a_2574_; 
lean_del_object(v___x_2434_);
v_a_2574_ = lean_ctor_get(v___x_2573_, 0);
lean_inc(v_a_2574_);
lean_dec_ref(v___x_2573_);
v___y_2467_ = v___x_2522_;
v___y_2468_ = v_a_2571_;
v___y_2469_ = v_a_2519_;
v___y_2470_ = v___x_2521_;
v_a_2471_ = v_a_2574_;
goto v___jp_2466_;
}
else
{
lean_object* v_a_2575_; 
lean_dec(v_a_2571_);
v_a_2575_ = lean_ctor_get(v___x_2573_, 0);
lean_inc(v_a_2575_);
lean_dec_ref(v___x_2573_);
v___y_2455_ = v___x_2522_;
v___y_2456_ = v_a_2519_;
v_a_2457_ = v_a_2575_;
goto v___jp_2454_;
}
}
else
{
lean_dec_ref(v_e_x27_2544_);
lean_del_object(v___x_2434_);
v___y_2467_ = v___x_2522_;
v___y_2468_ = v_a_2571_;
v___y_2469_ = v_a_2519_;
v___y_2470_ = v___x_2521_;
v_a_2471_ = v_e_2193_;
goto v___jp_2466_;
}
}
else
{
lean_object* v_a_2576_; 
lean_dec_ref(v_e_x27_2544_);
lean_dec_ref(v_e_2193_);
v_a_2576_ = lean_ctor_get(v___x_2570_, 0);
lean_inc(v_a_2576_);
lean_dec_ref(v___x_2570_);
v___y_2455_ = v___x_2522_;
v___y_2456_ = v_a_2519_;
v_a_2457_ = v_a_2576_;
goto v___jp_2454_;
}
}
else
{
lean_object* v_a_2577_; 
lean_dec_ref(v_proof_2545_);
lean_dec_ref(v_e_x27_2544_);
lean_dec_ref(v_e_2193_);
v_a_2577_ = lean_ctor_get(v___x_2566_, 0);
lean_inc(v_a_2577_);
lean_dec_ref(v___x_2566_);
v___y_2455_ = v___x_2522_;
v___y_2456_ = v_a_2519_;
v_a_2457_ = v_a_2577_;
goto v___jp_2454_;
}
}
}
else
{
lean_object* v_a_2578_; 
lean_dec_ref(v___x_2555_);
lean_dec_ref(v_proof_2545_);
lean_dec_ref(v_e_x27_2544_);
lean_dec_ref(v_e_2193_);
v_a_2578_ = lean_ctor_get(v___x_2562_, 0);
lean_inc(v_a_2578_);
lean_dec_ref(v___x_2562_);
v___y_2455_ = v___x_2522_;
v___y_2456_ = v_a_2519_;
v_a_2457_ = v_a_2578_;
goto v___jp_2454_;
}
}
else
{
lean_object* v_val_2579_; lean_object* v___x_2580_; 
lean_dec_ref(v___x_2555_);
lean_dec_ref(v_proof_2545_);
lean_dec_ref(v_e_x27_2544_);
lean_dec_ref(v_e_2193_);
v_val_2579_ = lean_ctor_get(v_a_2561_, 0);
lean_inc(v_val_2579_);
lean_dec_ref(v_a_2561_);
v___x_2580_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_val_2579_, v_a_2198_);
if (lean_obj_tag(v___x_2580_) == 0)
{
lean_object* v_a_2581_; lean_object* v___x_2582_; 
v_a_2581_ = lean_ctor_get(v___x_2580_, 0);
lean_inc(v_a_2581_);
lean_dec_ref(v___x_2580_);
lean_inc(v_a_2202_);
lean_inc_ref(v_a_2201_);
lean_inc(v_a_2200_);
lean_inc_ref(v_a_2199_);
lean_inc(v_a_2581_);
v___x_2582_ = l_Lean_Meta_Sym_mkEqRefl___redArg(v_a_2581_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_);
if (lean_obj_tag(v___x_2582_) == 0)
{
lean_object* v_a_2583_; lean_object* v___x_2585_; 
lean_del_object(v___x_2434_);
v_a_2583_ = lean_ctor_get(v___x_2582_, 0);
lean_inc(v_a_2583_);
lean_dec_ref(v___x_2582_);
if (v_isShared_2548_ == 0)
{
lean_ctor_set(v___x_2547_, 1, v_a_2583_);
lean_ctor_set(v___x_2547_, 0, v_a_2581_);
v___x_2585_ = v___x_2547_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_a_2581_);
lean_ctor_set(v_reuseFailAlloc_2586_, 1, v_a_2583_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
lean_ctor_set_uint8(v___x_2585_, sizeof(void*)*2, v___x_2521_);
v___y_2462_ = v___x_2522_;
v___y_2463_ = v_a_2519_;
v_a_2464_ = v___x_2585_;
goto v___jp_2461_;
}
}
else
{
lean_object* v_a_2587_; 
lean_dec(v_a_2581_);
lean_del_object(v___x_2547_);
v_a_2587_ = lean_ctor_get(v___x_2582_, 0);
lean_inc(v_a_2587_);
lean_dec_ref(v___x_2582_);
v___y_2455_ = v___x_2522_;
v___y_2456_ = v_a_2519_;
v_a_2457_ = v_a_2587_;
goto v___jp_2454_;
}
}
else
{
lean_object* v_a_2588_; 
lean_del_object(v___x_2547_);
v_a_2588_ = lean_ctor_get(v___x_2580_, 0);
lean_inc(v_a_2588_);
lean_dec_ref(v___x_2580_);
v___y_2455_ = v___x_2522_;
v___y_2456_ = v_a_2519_;
v_a_2457_ = v_a_2588_;
goto v___jp_2454_;
}
}
}
else
{
lean_object* v_a_2589_; 
lean_dec_ref(v___x_2555_);
lean_del_object(v___x_2547_);
lean_dec_ref(v_proof_2545_);
lean_dec_ref(v_e_x27_2544_);
lean_dec_ref(v_e_2193_);
v_a_2589_ = lean_ctor_get(v___x_2560_, 0);
lean_inc(v_a_2589_);
lean_dec_ref(v___x_2560_);
v___y_2455_ = v___x_2522_;
v___y_2456_ = v_a_2519_;
v_a_2457_ = v_a_2589_;
goto v___jp_2454_;
}
}
else
{
lean_object* v___x_2590_; 
lean_del_object(v___x_2547_);
lean_inc(v_a_2202_);
lean_inc_ref(v_a_2201_);
lean_inc(v_a_2200_);
lean_inc_ref(v_a_2199_);
v___x_2590_ = l_Lean_Meta_mkCongrArg(v___x_2555_, v_proof_2545_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_);
if (lean_obj_tag(v___x_2590_) == 0)
{
lean_object* v_a_2591_; uint8_t v___x_2592_; 
v_a_2591_ = lean_ctor_get(v___x_2590_, 0);
lean_inc(v_a_2591_);
lean_dec_ref(v___x_2590_);
v___x_2592_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_2218_, v_e_x27_2544_);
if (v___x_2592_ == 0)
{
lean_object* v___x_2593_; 
lean_inc(v_idx_2217_);
lean_inc(v_typeName_2216_);
lean_dec_ref(v_e_2193_);
lean_inc(v_a_2202_);
lean_inc_ref(v_a_2201_);
lean_inc(v_a_2200_);
lean_inc_ref(v_a_2199_);
lean_inc(v_a_2198_);
lean_inc_ref(v_a_2197_);
v___x_2593_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_typeName_2216_, v_idx_2217_, v_e_x27_2544_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_);
if (lean_obj_tag(v___x_2593_) == 0)
{
lean_object* v_a_2594_; 
lean_del_object(v___x_2434_);
v_a_2594_ = lean_ctor_get(v___x_2593_, 0);
lean_inc(v_a_2594_);
lean_dec_ref(v___x_2593_);
v___y_2474_ = v___x_2522_;
v___y_2475_ = v_a_2591_;
v___y_2476_ = v_a_2519_;
v___y_2477_ = v___x_2521_;
v_a_2478_ = v_a_2594_;
goto v___jp_2473_;
}
else
{
lean_object* v_a_2595_; 
lean_dec(v_a_2591_);
v_a_2595_ = lean_ctor_get(v___x_2593_, 0);
lean_inc(v_a_2595_);
lean_dec_ref(v___x_2593_);
v___y_2455_ = v___x_2522_;
v___y_2456_ = v_a_2519_;
v_a_2457_ = v_a_2595_;
goto v___jp_2454_;
}
}
else
{
lean_dec_ref(v_e_x27_2544_);
lean_del_object(v___x_2434_);
v___y_2474_ = v___x_2522_;
v___y_2475_ = v_a_2591_;
v___y_2476_ = v_a_2519_;
v___y_2477_ = v___x_2521_;
v_a_2478_ = v_e_2193_;
goto v___jp_2473_;
}
}
else
{
lean_object* v_a_2596_; 
lean_dec_ref(v_e_x27_2544_);
lean_dec_ref(v_e_2193_);
v_a_2596_ = lean_ctor_get(v___x_2590_, 0);
lean_inc(v_a_2596_);
lean_dec_ref(v___x_2590_);
v___y_2455_ = v___x_2522_;
v___y_2456_ = v_a_2519_;
v_a_2457_ = v_a_2596_;
goto v___jp_2454_;
}
}
}
else
{
lean_object* v_a_2597_; 
lean_dec_ref(v___x_2555_);
lean_del_object(v___x_2547_);
lean_dec_ref(v_proof_2545_);
lean_dec_ref(v_e_x27_2544_);
lean_dec_ref(v_e_2193_);
v_a_2597_ = lean_ctor_get(v___x_2556_, 0);
lean_inc(v_a_2597_);
lean_dec_ref(v___x_2556_);
v___y_2455_ = v___x_2522_;
v___y_2456_ = v_a_2519_;
v_a_2457_ = v_a_2597_;
goto v___jp_2454_;
}
}
else
{
lean_object* v_a_2598_; 
lean_del_object(v___x_2547_);
lean_dec_ref(v_proof_2545_);
lean_dec_ref(v_e_x27_2544_);
lean_dec_ref(v_e_2193_);
v_a_2598_ = lean_ctor_get(v___x_2549_, 0);
lean_inc(v_a_2598_);
lean_dec_ref(v___x_2549_);
v___y_2455_ = v___x_2522_;
v___y_2456_ = v_a_2519_;
v_a_2457_ = v_a_2598_;
goto v___jp_2454_;
}
}
}
}
else
{
lean_dec_ref(v_e_2193_);
if (lean_obj_tag(v___x_2523_) == 0)
{
lean_object* v_a_2600_; 
lean_del_object(v___x_2434_);
v_a_2600_ = lean_ctor_get(v___x_2523_, 0);
lean_inc(v_a_2600_);
lean_dec_ref(v___x_2523_);
v___y_2462_ = v___x_2522_;
v___y_2463_ = v_a_2519_;
v_a_2464_ = v_a_2600_;
goto v___jp_2461_;
}
else
{
lean_object* v_a_2601_; 
v_a_2601_ = lean_ctor_get(v___x_2523_, 0);
lean_inc(v_a_2601_);
lean_dec_ref(v___x_2523_);
v___y_2455_ = v___x_2522_;
v___y_2456_ = v_a_2519_;
v_a_2457_ = v_a_2601_;
goto v___jp_2454_;
}
}
}
else
{
lean_object* v___x_2602_; lean_object* v___x_2603_; 
lean_del_object(v___x_2434_);
v___x_2602_ = lean_io_get_num_heartbeats();
lean_inc(v_a_2202_);
lean_inc_ref(v_a_2201_);
lean_inc(v_a_2200_);
lean_inc_ref(v_a_2199_);
lean_inc(v_a_2198_);
lean_inc_ref(v_a_2197_);
lean_inc(v_a_2196_);
lean_inc_ref(v_a_2195_);
lean_inc(v_a_2194_);
lean_inc_ref(v_struct_2218_);
v___x_2603_ = lean_sym_simp(v_struct_2218_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_);
if (lean_obj_tag(v___x_2603_) == 0)
{
lean_object* v_a_2604_; 
v_a_2604_ = lean_ctor_get(v___x_2603_, 0);
lean_inc(v_a_2604_);
lean_dec_ref(v___x_2603_);
if (lean_obj_tag(v_a_2604_) == 0)
{
lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2624_; 
v_isSharedCheck_2624_ = !lean_is_exclusive(v_a_2604_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2606_ = v_a_2604_;
v_isShared_2607_ = v_isSharedCheck_2624_;
goto v_resetjp_2605_;
}
else
{
lean_dec(v_a_2604_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2624_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v___x_2608_; lean_object* v___x_2609_; 
v___x_2608_ = lean_alloc_closure((void*)(l_Lean_Meta_reduceProj_x3f___boxed), 6, 1);
lean_closure_set(v___x_2608_, 0, v_e_2193_);
lean_inc(v_a_2202_);
lean_inc_ref(v_a_2201_);
lean_inc(v_a_2200_);
lean_inc_ref(v_a_2199_);
v___x_2609_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___x_2608_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_);
if (lean_obj_tag(v___x_2609_) == 0)
{
lean_object* v_a_2610_; 
v_a_2610_ = lean_ctor_get(v___x_2609_, 0);
lean_inc(v_a_2610_);
lean_dec_ref(v___x_2609_);
if (lean_obj_tag(v_a_2610_) == 1)
{
lean_object* v_val_2611_; lean_object* v___x_2612_; 
lean_del_object(v___x_2606_);
v_val_2611_ = lean_ctor_get(v_a_2610_, 0);
lean_inc(v_val_2611_);
lean_dec_ref(v_a_2610_);
v___x_2612_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_val_2611_, v_a_2198_);
if (lean_obj_tag(v___x_2612_) == 0)
{
lean_object* v_a_2613_; lean_object* v___x_2614_; 
v_a_2613_ = lean_ctor_get(v___x_2612_, 0);
lean_inc(v_a_2613_);
lean_dec_ref(v___x_2612_);
lean_inc(v_a_2202_);
lean_inc_ref(v_a_2201_);
lean_inc(v_a_2200_);
lean_inc_ref(v_a_2199_);
lean_inc(v_a_2613_);
v___x_2614_ = l_Lean_Meta_Sym_mkEqRefl___redArg(v_a_2613_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_);
if (lean_obj_tag(v___x_2614_) == 0)
{
lean_object* v_a_2615_; uint8_t v___x_2616_; lean_object* v___x_2617_; 
v_a_2615_ = lean_ctor_get(v___x_2614_, 0);
lean_inc(v_a_2615_);
lean_dec_ref(v___x_2614_);
v___x_2616_ = 0;
v___x_2617_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_2617_, 0, v_a_2613_);
lean_ctor_set(v___x_2617_, 1, v_a_2615_);
lean_ctor_set_uint8(v___x_2617_, sizeof(void*)*2, v___x_2616_);
v___y_2499_ = v___x_2602_;
v___y_2500_ = v_a_2519_;
v_a_2501_ = v___x_2617_;
goto v___jp_2498_;
}
else
{
lean_object* v_a_2618_; 
lean_dec(v_a_2613_);
v_a_2618_ = lean_ctor_get(v___x_2614_, 0);
lean_inc(v_a_2618_);
lean_dec_ref(v___x_2614_);
v___y_2494_ = v___x_2602_;
v___y_2495_ = v_a_2519_;
v_a_2496_ = v_a_2618_;
goto v___jp_2493_;
}
}
else
{
lean_object* v_a_2619_; 
v_a_2619_ = lean_ctor_get(v___x_2612_, 0);
lean_inc(v_a_2619_);
lean_dec_ref(v___x_2612_);
v___y_2494_ = v___x_2602_;
v___y_2495_ = v_a_2519_;
v_a_2496_ = v_a_2619_;
goto v___jp_2493_;
}
}
else
{
lean_object* v___x_2621_; 
lean_dec(v_a_2610_);
if (v_isShared_2607_ == 0)
{
v___x_2621_ = v___x_2606_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(0, 0, 1);
v___x_2621_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
lean_ctor_set_uint8(v___x_2621_, 0, v___x_2521_);
v___y_2499_ = v___x_2602_;
v___y_2500_ = v_a_2519_;
v_a_2501_ = v___x_2621_;
goto v___jp_2498_;
}
}
}
else
{
lean_object* v_a_2623_; 
lean_del_object(v___x_2606_);
v_a_2623_ = lean_ctor_get(v___x_2609_, 0);
lean_inc(v_a_2623_);
lean_dec_ref(v___x_2609_);
v___y_2494_ = v___x_2602_;
v___y_2495_ = v_a_2519_;
v_a_2496_ = v_a_2623_;
goto v___jp_2493_;
}
}
}
else
{
lean_object* v_e_x27_2625_; lean_object* v_proof_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2680_; 
v_e_x27_2625_ = lean_ctor_get(v_a_2604_, 0);
v_proof_2626_ = lean_ctor_get(v_a_2604_, 1);
v_isSharedCheck_2680_ = !lean_is_exclusive(v_a_2604_);
if (v_isSharedCheck_2680_ == 0)
{
v___x_2628_ = v_a_2604_;
v_isShared_2629_ = v_isSharedCheck_2680_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_proof_2626_);
lean_inc(v_e_x27_2625_);
lean_dec(v_a_2604_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2680_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
lean_object* v___x_2630_; 
lean_inc(v_a_2202_);
lean_inc_ref(v_a_2201_);
lean_inc(v_a_2200_);
lean_inc_ref(v_a_2199_);
lean_inc_ref(v_e_x27_2625_);
v___x_2630_ = l_Lean_Meta_Sym_inferType___redArg(v_e_x27_2625_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_);
if (lean_obj_tag(v___x_2630_) == 0)
{
lean_object* v_a_2631_; lean_object* v___x_2632_; uint8_t v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; 
v_a_2631_ = lean_ctor_get(v___x_2630_, 0);
lean_inc(v_a_2631_);
lean_dec_ref(v___x_2630_);
v___x_2632_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2));
v___x_2633_ = 0;
v___x_2634_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__3, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__3_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__3);
lean_inc(v_idx_2217_);
lean_inc(v_typeName_2216_);
v___x_2635_ = l_Lean_Expr_proj___override(v_typeName_2216_, v_idx_2217_, v___x_2634_);
v___x_2636_ = l_Lean_mkLambda(v___x_2632_, v___x_2633_, v_a_2631_, v___x_2635_);
lean_inc(v_a_2202_);
lean_inc_ref(v_a_2201_);
lean_inc(v_a_2200_);
lean_inc_ref(v_a_2199_);
lean_inc_ref(v___x_2636_);
v___x_2637_ = lean_infer_type(v___x_2636_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_);
if (lean_obj_tag(v___x_2637_) == 0)
{
lean_object* v_a_2638_; uint8_t v___x_2639_; 
v_a_2638_ = lean_ctor_get(v___x_2637_, 0);
lean_inc(v_a_2638_);
lean_dec_ref(v___x_2637_);
v___x_2639_ = l_Lean_Expr_isArrow(v_a_2638_);
lean_dec(v_a_2638_);
if (v___x_2639_ == 0)
{
lean_object* v___x_2640_; lean_object* v___x_2641_; 
lean_inc_ref(v_e_2193_);
v___x_2640_ = lean_alloc_closure((void*)(l_Lean_Meta_reduceProj_x3f___boxed), 6, 1);
lean_closure_set(v___x_2640_, 0, v_e_2193_);
lean_inc(v_a_2202_);
lean_inc_ref(v_a_2201_);
lean_inc(v_a_2200_);
lean_inc_ref(v_a_2199_);
v___x_2641_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___x_2640_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_);
if (lean_obj_tag(v___x_2641_) == 0)
{
lean_object* v_a_2642_; 
v_a_2642_ = lean_ctor_get(v___x_2641_, 0);
lean_inc(v_a_2642_);
lean_dec_ref(v___x_2641_);
if (lean_obj_tag(v_a_2642_) == 0)
{
lean_object* v___x_2643_; 
lean_del_object(v___x_2628_);
lean_inc(v_a_2202_);
lean_inc_ref(v_a_2201_);
lean_inc(v_a_2200_);
lean_inc_ref(v_a_2199_);
lean_inc_ref(v_e_x27_2625_);
lean_inc_ref(v_struct_2218_);
v___x_2643_ = l_Lean_Meta_isExprDefEq(v_struct_2218_, v_e_x27_2625_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_);
if (lean_obj_tag(v___x_2643_) == 0)
{
lean_object* v_a_2644_; uint8_t v___x_2645_; 
v_a_2644_ = lean_ctor_get(v___x_2643_, 0);
lean_inc(v_a_2644_);
lean_dec_ref(v___x_2643_);
v___x_2645_ = lean_unbox(v_a_2644_);
lean_dec(v_a_2644_);
if (v___x_2645_ == 0)
{
lean_object* v___x_2646_; 
lean_dec_ref(v___x_2636_);
lean_dec_ref(v_proof_2626_);
lean_dec_ref(v_e_x27_2625_);
lean_dec_ref(v_e_2193_);
v___x_2646_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_2646_, 0, v___x_2521_);
v___y_2499_ = v___x_2602_;
v___y_2500_ = v_a_2519_;
v_a_2501_ = v___x_2646_;
goto v___jp_2498_;
}
else
{
lean_object* v___x_2647_; 
lean_inc(v_a_2202_);
lean_inc_ref(v_a_2201_);
lean_inc(v_a_2200_);
lean_inc_ref(v_a_2199_);
v___x_2647_ = l_Lean_Meta_mkHCongr(v___x_2636_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_);
if (lean_obj_tag(v___x_2647_) == 0)
{
lean_object* v_a_2648_; lean_object* v_proof_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; 
v_a_2648_ = lean_ctor_get(v___x_2647_, 0);
lean_inc(v_a_2648_);
lean_dec_ref(v___x_2647_);
v_proof_2649_ = lean_ctor_get(v_a_2648_, 1);
lean_inc_ref(v_proof_2649_);
lean_dec(v_a_2648_);
lean_inc_ref(v_e_x27_2625_);
lean_inc_ref(v_struct_2218_);
v___x_2650_ = l_Lean_mkApp3(v_proof_2649_, v_struct_2218_, v_e_x27_2625_, v_proof_2626_);
lean_inc(v_a_2202_);
lean_inc_ref(v_a_2201_);
lean_inc(v_a_2200_);
lean_inc_ref(v_a_2199_);
v___x_2651_ = l_Lean_Meta_mkEqOfHEq(v___x_2650_, v___x_2639_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_);
if (lean_obj_tag(v___x_2651_) == 0)
{
lean_object* v_a_2652_; uint8_t v___x_2653_; 
v_a_2652_ = lean_ctor_get(v___x_2651_, 0);
lean_inc(v_a_2652_);
lean_dec_ref(v___x_2651_);
v___x_2653_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_2218_, v_e_x27_2625_);
if (v___x_2653_ == 0)
{
lean_object* v___x_2654_; 
lean_inc(v_idx_2217_);
lean_inc(v_typeName_2216_);
lean_dec_ref(v_e_2193_);
lean_inc(v_a_2202_);
lean_inc_ref(v_a_2201_);
lean_inc(v_a_2200_);
lean_inc_ref(v_a_2199_);
lean_inc(v_a_2198_);
lean_inc_ref(v_a_2197_);
v___x_2654_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_typeName_2216_, v_idx_2217_, v_e_x27_2625_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_);
if (lean_obj_tag(v___x_2654_) == 0)
{
lean_object* v_a_2655_; 
v_a_2655_ = lean_ctor_get(v___x_2654_, 0);
lean_inc(v_a_2655_);
lean_dec_ref(v___x_2654_);
v___y_2504_ = v___x_2639_;
v___y_2505_ = v_a_2652_;
v___y_2506_ = v___x_2602_;
v___y_2507_ = v_a_2519_;
v_a_2508_ = v_a_2655_;
goto v___jp_2503_;
}
else
{
lean_object* v_a_2656_; 
lean_dec(v_a_2652_);
v_a_2656_ = lean_ctor_get(v___x_2654_, 0);
lean_inc(v_a_2656_);
lean_dec_ref(v___x_2654_);
v___y_2494_ = v___x_2602_;
v___y_2495_ = v_a_2519_;
v_a_2496_ = v_a_2656_;
goto v___jp_2493_;
}
}
else
{
lean_dec_ref(v_e_x27_2625_);
v___y_2504_ = v___x_2639_;
v___y_2505_ = v_a_2652_;
v___y_2506_ = v___x_2602_;
v___y_2507_ = v_a_2519_;
v_a_2508_ = v_e_2193_;
goto v___jp_2503_;
}
}
else
{
lean_object* v_a_2657_; 
lean_dec_ref(v_e_x27_2625_);
lean_dec_ref(v_e_2193_);
v_a_2657_ = lean_ctor_get(v___x_2651_, 0);
lean_inc(v_a_2657_);
lean_dec_ref(v___x_2651_);
v___y_2494_ = v___x_2602_;
v___y_2495_ = v_a_2519_;
v_a_2496_ = v_a_2657_;
goto v___jp_2493_;
}
}
else
{
lean_object* v_a_2658_; 
lean_dec_ref(v_proof_2626_);
lean_dec_ref(v_e_x27_2625_);
lean_dec_ref(v_e_2193_);
v_a_2658_ = lean_ctor_get(v___x_2647_, 0);
lean_inc(v_a_2658_);
lean_dec_ref(v___x_2647_);
v___y_2494_ = v___x_2602_;
v___y_2495_ = v_a_2519_;
v_a_2496_ = v_a_2658_;
goto v___jp_2493_;
}
}
}
else
{
lean_object* v_a_2659_; 
lean_dec_ref(v___x_2636_);
lean_dec_ref(v_proof_2626_);
lean_dec_ref(v_e_x27_2625_);
lean_dec_ref(v_e_2193_);
v_a_2659_ = lean_ctor_get(v___x_2643_, 0);
lean_inc(v_a_2659_);
lean_dec_ref(v___x_2643_);
v___y_2494_ = v___x_2602_;
v___y_2495_ = v_a_2519_;
v_a_2496_ = v_a_2659_;
goto v___jp_2493_;
}
}
else
{
lean_object* v_val_2660_; lean_object* v___x_2661_; 
lean_dec_ref(v___x_2636_);
lean_dec_ref(v_proof_2626_);
lean_dec_ref(v_e_x27_2625_);
lean_dec_ref(v_e_2193_);
v_val_2660_ = lean_ctor_get(v_a_2642_, 0);
lean_inc(v_val_2660_);
lean_dec_ref(v_a_2642_);
v___x_2661_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_val_2660_, v_a_2198_);
if (lean_obj_tag(v___x_2661_) == 0)
{
lean_object* v_a_2662_; lean_object* v___x_2663_; 
v_a_2662_ = lean_ctor_get(v___x_2661_, 0);
lean_inc(v_a_2662_);
lean_dec_ref(v___x_2661_);
lean_inc(v_a_2202_);
lean_inc_ref(v_a_2201_);
lean_inc(v_a_2200_);
lean_inc_ref(v_a_2199_);
lean_inc(v_a_2662_);
v___x_2663_ = l_Lean_Meta_Sym_mkEqRefl___redArg(v_a_2662_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_);
if (lean_obj_tag(v___x_2663_) == 0)
{
lean_object* v_a_2664_; lean_object* v___x_2666_; 
v_a_2664_ = lean_ctor_get(v___x_2663_, 0);
lean_inc(v_a_2664_);
lean_dec_ref(v___x_2663_);
if (v_isShared_2629_ == 0)
{
lean_ctor_set(v___x_2628_, 1, v_a_2664_);
lean_ctor_set(v___x_2628_, 0, v_a_2662_);
v___x_2666_ = v___x_2628_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v_a_2662_);
lean_ctor_set(v_reuseFailAlloc_2667_, 1, v_a_2664_);
v___x_2666_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
lean_ctor_set_uint8(v___x_2666_, sizeof(void*)*2, v___x_2639_);
v___y_2499_ = v___x_2602_;
v___y_2500_ = v_a_2519_;
v_a_2501_ = v___x_2666_;
goto v___jp_2498_;
}
}
else
{
lean_object* v_a_2668_; 
lean_dec(v_a_2662_);
lean_del_object(v___x_2628_);
v_a_2668_ = lean_ctor_get(v___x_2663_, 0);
lean_inc(v_a_2668_);
lean_dec_ref(v___x_2663_);
v___y_2494_ = v___x_2602_;
v___y_2495_ = v_a_2519_;
v_a_2496_ = v_a_2668_;
goto v___jp_2493_;
}
}
else
{
lean_object* v_a_2669_; 
lean_del_object(v___x_2628_);
v_a_2669_ = lean_ctor_get(v___x_2661_, 0);
lean_inc(v_a_2669_);
lean_dec_ref(v___x_2661_);
v___y_2494_ = v___x_2602_;
v___y_2495_ = v_a_2519_;
v_a_2496_ = v_a_2669_;
goto v___jp_2493_;
}
}
}
else
{
lean_object* v_a_2670_; 
lean_dec_ref(v___x_2636_);
lean_del_object(v___x_2628_);
lean_dec_ref(v_proof_2626_);
lean_dec_ref(v_e_x27_2625_);
lean_dec_ref(v_e_2193_);
v_a_2670_ = lean_ctor_get(v___x_2641_, 0);
lean_inc(v_a_2670_);
lean_dec_ref(v___x_2641_);
v___y_2494_ = v___x_2602_;
v___y_2495_ = v_a_2519_;
v_a_2496_ = v_a_2670_;
goto v___jp_2493_;
}
}
else
{
lean_object* v___x_2671_; 
lean_del_object(v___x_2628_);
lean_inc(v_a_2202_);
lean_inc_ref(v_a_2201_);
lean_inc(v_a_2200_);
lean_inc_ref(v_a_2199_);
v___x_2671_ = l_Lean_Meta_mkCongrArg(v___x_2636_, v_proof_2626_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_);
if (lean_obj_tag(v___x_2671_) == 0)
{
lean_object* v_a_2672_; uint8_t v___x_2673_; 
v_a_2672_ = lean_ctor_get(v___x_2671_, 0);
lean_inc(v_a_2672_);
lean_dec_ref(v___x_2671_);
v___x_2673_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_2218_, v_e_x27_2625_);
if (v___x_2673_ == 0)
{
lean_object* v___x_2674_; 
lean_inc(v_idx_2217_);
lean_inc(v_typeName_2216_);
lean_dec_ref(v_e_2193_);
lean_inc(v_a_2202_);
lean_inc_ref(v_a_2201_);
lean_inc(v_a_2200_);
lean_inc_ref(v_a_2199_);
lean_inc(v_a_2198_);
lean_inc_ref(v_a_2197_);
v___x_2674_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_typeName_2216_, v_idx_2217_, v_e_x27_2625_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_);
if (lean_obj_tag(v___x_2674_) == 0)
{
lean_object* v_a_2675_; 
v_a_2675_ = lean_ctor_get(v___x_2674_, 0);
lean_inc(v_a_2675_);
lean_dec_ref(v___x_2674_);
v___y_2511_ = v___x_2602_;
v___y_2512_ = v_a_2672_;
v___y_2513_ = v_a_2519_;
v_a_2514_ = v_a_2675_;
goto v___jp_2510_;
}
else
{
lean_object* v_a_2676_; 
lean_dec(v_a_2672_);
v_a_2676_ = lean_ctor_get(v___x_2674_, 0);
lean_inc(v_a_2676_);
lean_dec_ref(v___x_2674_);
v___y_2494_ = v___x_2602_;
v___y_2495_ = v_a_2519_;
v_a_2496_ = v_a_2676_;
goto v___jp_2493_;
}
}
else
{
lean_dec_ref(v_e_x27_2625_);
v___y_2511_ = v___x_2602_;
v___y_2512_ = v_a_2672_;
v___y_2513_ = v_a_2519_;
v_a_2514_ = v_e_2193_;
goto v___jp_2510_;
}
}
else
{
lean_object* v_a_2677_; 
lean_dec_ref(v_e_x27_2625_);
lean_dec_ref(v_e_2193_);
v_a_2677_ = lean_ctor_get(v___x_2671_, 0);
lean_inc(v_a_2677_);
lean_dec_ref(v___x_2671_);
v___y_2494_ = v___x_2602_;
v___y_2495_ = v_a_2519_;
v_a_2496_ = v_a_2677_;
goto v___jp_2493_;
}
}
}
else
{
lean_object* v_a_2678_; 
lean_dec_ref(v___x_2636_);
lean_del_object(v___x_2628_);
lean_dec_ref(v_proof_2626_);
lean_dec_ref(v_e_x27_2625_);
lean_dec_ref(v_e_2193_);
v_a_2678_ = lean_ctor_get(v___x_2637_, 0);
lean_inc(v_a_2678_);
lean_dec_ref(v___x_2637_);
v___y_2494_ = v___x_2602_;
v___y_2495_ = v_a_2519_;
v_a_2496_ = v_a_2678_;
goto v___jp_2493_;
}
}
else
{
lean_object* v_a_2679_; 
lean_del_object(v___x_2628_);
lean_dec_ref(v_proof_2626_);
lean_dec_ref(v_e_x27_2625_);
lean_dec_ref(v_e_2193_);
v_a_2679_ = lean_ctor_get(v___x_2630_, 0);
lean_inc(v_a_2679_);
lean_dec_ref(v___x_2630_);
v___y_2494_ = v___x_2602_;
v___y_2495_ = v_a_2519_;
v_a_2496_ = v_a_2679_;
goto v___jp_2493_;
}
}
}
}
else
{
lean_dec_ref(v_e_2193_);
if (lean_obj_tag(v___x_2603_) == 0)
{
lean_object* v_a_2681_; 
v_a_2681_ = lean_ctor_get(v___x_2603_, 0);
lean_inc(v_a_2681_);
lean_dec_ref(v___x_2603_);
v___y_2499_ = v___x_2602_;
v___y_2500_ = v_a_2519_;
v_a_2501_ = v_a_2681_;
goto v___jp_2498_;
}
else
{
lean_object* v_a_2682_; 
v_a_2682_ = lean_ctor_get(v___x_2603_, 0);
lean_inc(v_a_2682_);
lean_dec_ref(v___x_2603_);
v___y_2494_ = v___x_2602_;
v___y_2495_ = v_a_2519_;
v_a_2496_ = v_a_2682_;
goto v___jp_2493_;
}
}
}
}
}
}
v___jp_2219_:
{
lean_dec(v___y_2223_);
lean_dec_ref(v___y_2222_);
lean_dec(v___y_2221_);
if (lean_obj_tag(v_res_2220_) == 0)
{
lean_object* v___x_2230_; lean_object* v___x_2231_; 
lean_dec_ref(v_res_2220_);
lean_dec_ref(v___y_2224_);
v___x_2230_ = lean_alloc_closure((void*)(l_Lean_Meta_reduceProj_x3f___boxed), 6, 1);
lean_closure_set(v___x_2230_, 0, v_e_2193_);
lean_inc(v___y_2229_);
lean_inc_ref(v___y_2228_);
lean_inc(v___y_2227_);
lean_inc_ref(v___y_2226_);
v___x_2231_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___x_2230_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_);
if (lean_obj_tag(v___x_2231_) == 0)
{
lean_object* v_a_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2270_; 
v_a_2232_ = lean_ctor_get(v___x_2231_, 0);
v_isSharedCheck_2270_ = !lean_is_exclusive(v___x_2231_);
if (v_isSharedCheck_2270_ == 0)
{
v___x_2234_ = v___x_2231_;
v_isShared_2235_ = v_isSharedCheck_2270_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_a_2232_);
lean_dec(v___x_2231_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2270_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
if (lean_obj_tag(v_a_2232_) == 1)
{
lean_object* v_val_2236_; lean_object* v___x_2237_; 
lean_del_object(v___x_2234_);
v_val_2236_ = lean_ctor_get(v_a_2232_, 0);
lean_inc(v_val_2236_);
lean_dec_ref(v_a_2232_);
v___x_2237_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_val_2236_, v___y_2225_);
if (lean_obj_tag(v___x_2237_) == 0)
{
lean_object* v_a_2238_; lean_object* v___x_2239_; 
v_a_2238_ = lean_ctor_get(v___x_2237_, 0);
lean_inc(v_a_2238_);
lean_dec_ref(v___x_2237_);
lean_inc(v_a_2238_);
v___x_2239_ = l_Lean_Meta_Sym_mkEqRefl___redArg(v_a_2238_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_);
lean_dec(v___y_2225_);
if (lean_obj_tag(v___x_2239_) == 0)
{
lean_object* v_a_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2249_; 
v_a_2240_ = lean_ctor_get(v___x_2239_, 0);
v_isSharedCheck_2249_ = !lean_is_exclusive(v___x_2239_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2242_ = v___x_2239_;
v_isShared_2243_ = v_isSharedCheck_2249_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_a_2240_);
lean_dec(v___x_2239_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2249_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
uint8_t v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2247_; 
v___x_2244_ = 0;
v___x_2245_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_2245_, 0, v_a_2238_);
lean_ctor_set(v___x_2245_, 1, v_a_2240_);
lean_ctor_set_uint8(v___x_2245_, sizeof(void*)*2, v___x_2244_);
if (v_isShared_2243_ == 0)
{
lean_ctor_set(v___x_2242_, 0, v___x_2245_);
v___x_2247_ = v___x_2242_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v___x_2245_);
v___x_2247_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
return v___x_2247_;
}
}
}
else
{
lean_object* v_a_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2257_; 
lean_dec(v_a_2238_);
v_a_2250_ = lean_ctor_get(v___x_2239_, 0);
v_isSharedCheck_2257_ = !lean_is_exclusive(v___x_2239_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2252_ = v___x_2239_;
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_a_2250_);
lean_dec(v___x_2239_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v___x_2255_; 
if (v_isShared_2253_ == 0)
{
v___x_2255_ = v___x_2252_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v_a_2250_);
v___x_2255_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
return v___x_2255_;
}
}
}
}
else
{
lean_object* v_a_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2265_; 
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec(v___y_2225_);
v_a_2258_ = lean_ctor_get(v___x_2237_, 0);
v_isSharedCheck_2265_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2260_ = v___x_2237_;
v_isShared_2261_ = v_isSharedCheck_2265_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_a_2258_);
lean_dec(v___x_2237_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2265_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
lean_object* v___x_2263_; 
if (v_isShared_2261_ == 0)
{
v___x_2263_ = v___x_2260_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v_a_2258_);
v___x_2263_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
return v___x_2263_;
}
}
}
}
else
{
lean_object* v___x_2266_; lean_object* v___x_2268_; 
lean_dec(v_a_2232_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec(v___y_2225_);
v___x_2266_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__0));
if (v_isShared_2235_ == 0)
{
lean_ctor_set(v___x_2234_, 0, v___x_2266_);
v___x_2268_ = v___x_2234_;
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
}
}
else
{
lean_object* v_a_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2278_; 
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec(v___y_2225_);
v_a_2271_ = lean_ctor_get(v___x_2231_, 0);
v_isSharedCheck_2278_ = !lean_is_exclusive(v___x_2231_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2273_ = v___x_2231_;
v_isShared_2274_ = v_isSharedCheck_2278_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_a_2271_);
lean_dec(v___x_2231_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2278_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
lean_object* v___x_2276_; 
if (v_isShared_2274_ == 0)
{
v___x_2276_ = v___x_2273_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v_a_2271_);
v___x_2276_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
return v___x_2276_;
}
}
}
}
else
{
lean_object* v_e_x27_2279_; lean_object* v_proof_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2425_; 
v_e_x27_2279_ = lean_ctor_get(v_res_2220_, 0);
v_proof_2280_ = lean_ctor_get(v_res_2220_, 1);
v_isSharedCheck_2425_ = !lean_is_exclusive(v_res_2220_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2282_ = v_res_2220_;
v_isShared_2283_ = v_isSharedCheck_2425_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_proof_2280_);
lean_inc(v_e_x27_2279_);
lean_dec(v_res_2220_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2425_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
lean_object* v___x_2284_; 
lean_inc(v___y_2229_);
lean_inc_ref(v___y_2228_);
lean_inc(v___y_2227_);
lean_inc_ref(v___y_2226_);
lean_inc_ref(v_e_x27_2279_);
v___x_2284_ = l_Lean_Meta_Sym_inferType___redArg(v_e_x27_2279_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_);
if (lean_obj_tag(v___x_2284_) == 0)
{
lean_object* v_a_2285_; lean_object* v___x_2286_; uint8_t v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; 
v_a_2285_ = lean_ctor_get(v___x_2284_, 0);
lean_inc(v_a_2285_);
lean_dec_ref(v___x_2284_);
v___x_2286_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2));
v___x_2287_ = 0;
v___x_2288_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__3, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__3_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__3);
lean_inc(v_idx_2217_);
lean_inc(v_typeName_2216_);
v___x_2289_ = l_Lean_Expr_proj___override(v_typeName_2216_, v_idx_2217_, v___x_2288_);
v___x_2290_ = l_Lean_mkLambda(v___x_2286_, v___x_2287_, v_a_2285_, v___x_2289_);
lean_inc(v___y_2229_);
lean_inc_ref(v___y_2228_);
lean_inc(v___y_2227_);
lean_inc_ref(v___y_2226_);
lean_inc_ref(v___x_2290_);
v___x_2291_ = lean_infer_type(v___x_2290_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_);
if (lean_obj_tag(v___x_2291_) == 0)
{
lean_object* v_a_2292_; uint8_t v___x_2293_; 
v_a_2292_ = lean_ctor_get(v___x_2291_, 0);
lean_inc(v_a_2292_);
lean_dec_ref(v___x_2291_);
v___x_2293_ = l_Lean_Expr_isArrow(v_a_2292_);
lean_dec(v_a_2292_);
if (v___x_2293_ == 0)
{
lean_object* v___x_2294_; lean_object* v___x_2295_; 
lean_inc_ref(v_e_2193_);
v___x_2294_ = lean_alloc_closure((void*)(l_Lean_Meta_reduceProj_x3f___boxed), 6, 1);
lean_closure_set(v___x_2294_, 0, v_e_2193_);
lean_inc(v___y_2229_);
lean_inc_ref(v___y_2228_);
lean_inc(v___y_2227_);
lean_inc_ref(v___y_2226_);
v___x_2295_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___x_2294_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_);
if (lean_obj_tag(v___x_2295_) == 0)
{
lean_object* v_a_2296_; 
v_a_2296_ = lean_ctor_get(v___x_2295_, 0);
lean_inc(v_a_2296_);
lean_dec_ref(v___x_2295_);
if (lean_obj_tag(v_a_2296_) == 0)
{
lean_object* v___x_2297_; 
lean_del_object(v___x_2282_);
lean_inc(v___y_2229_);
lean_inc_ref(v___y_2228_);
lean_inc(v___y_2227_);
lean_inc_ref(v___y_2226_);
lean_inc_ref(v_e_x27_2279_);
lean_inc_ref(v_struct_2218_);
v___x_2297_ = l_Lean_Meta_isExprDefEq(v_struct_2218_, v_e_x27_2279_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_);
if (lean_obj_tag(v___x_2297_) == 0)
{
lean_object* v_a_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2340_; 
v_a_2298_ = lean_ctor_get(v___x_2297_, 0);
v_isSharedCheck_2340_ = !lean_is_exclusive(v___x_2297_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2300_ = v___x_2297_;
v_isShared_2301_ = v_isSharedCheck_2340_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_a_2298_);
lean_dec(v___x_2297_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2340_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
uint8_t v___x_2302_; 
v___x_2302_ = lean_unbox(v_a_2298_);
lean_dec(v_a_2298_);
if (v___x_2302_ == 0)
{
lean_object* v___x_2303_; lean_object* v___x_2305_; 
lean_dec_ref(v___x_2290_);
lean_dec_ref(v_proof_2280_);
lean_dec_ref(v_e_x27_2279_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
lean_dec_ref(v_e_2193_);
v___x_2303_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__0));
if (v_isShared_2301_ == 0)
{
lean_ctor_set(v___x_2300_, 0, v___x_2303_);
v___x_2305_ = v___x_2300_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v___x_2303_);
v___x_2305_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
return v___x_2305_;
}
}
else
{
lean_object* v___x_2307_; 
lean_del_object(v___x_2300_);
lean_inc(v___y_2229_);
lean_inc_ref(v___y_2228_);
lean_inc(v___y_2227_);
lean_inc_ref(v___y_2226_);
v___x_2307_ = l_Lean_Meta_mkHCongr(v___x_2290_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_);
if (lean_obj_tag(v___x_2307_) == 0)
{
lean_object* v_a_2308_; lean_object* v_proof_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; 
v_a_2308_ = lean_ctor_get(v___x_2307_, 0);
lean_inc(v_a_2308_);
lean_dec_ref(v___x_2307_);
v_proof_2309_ = lean_ctor_get(v_a_2308_, 1);
lean_inc_ref(v_proof_2309_);
lean_dec(v_a_2308_);
lean_inc_ref(v_e_x27_2279_);
lean_inc_ref(v_struct_2218_);
v___x_2310_ = l_Lean_mkApp3(v_proof_2309_, v_struct_2218_, v_e_x27_2279_, v_proof_2280_);
lean_inc(v___y_2229_);
lean_inc_ref(v___y_2228_);
lean_inc(v___y_2227_);
lean_inc_ref(v___y_2226_);
v___x_2311_ = l_Lean_Meta_mkEqOfHEq(v___x_2310_, v___x_2293_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_);
if (lean_obj_tag(v___x_2311_) == 0)
{
lean_object* v_a_2312_; uint8_t v___x_2313_; 
v_a_2312_ = lean_ctor_get(v___x_2311_, 0);
lean_inc(v_a_2312_);
lean_dec_ref(v___x_2311_);
v___x_2313_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_2218_, v_e_x27_2279_);
if (v___x_2313_ == 0)
{
lean_object* v___x_2314_; 
lean_inc(v_idx_2217_);
lean_inc(v_typeName_2216_);
lean_dec_ref(v_e_2193_);
v___x_2314_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_typeName_2216_, v_idx_2217_, v_e_x27_2279_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_);
if (lean_obj_tag(v___x_2314_) == 0)
{
lean_object* v_a_2315_; 
v_a_2315_ = lean_ctor_get(v___x_2314_, 0);
lean_inc(v_a_2315_);
lean_dec_ref(v___x_2314_);
v___y_2205_ = v_a_2312_;
v___y_2206_ = v___x_2293_;
v_a_2207_ = v_a_2315_;
goto v___jp_2204_;
}
else
{
lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2323_; 
lean_dec(v_a_2312_);
v_a_2316_ = lean_ctor_get(v___x_2314_, 0);
v_isSharedCheck_2323_ = !lean_is_exclusive(v___x_2314_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2318_ = v___x_2314_;
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v___x_2314_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v___x_2321_; 
if (v_isShared_2319_ == 0)
{
v___x_2321_ = v___x_2318_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v_a_2316_);
v___x_2321_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
return v___x_2321_;
}
}
}
}
else
{
lean_dec_ref(v_e_x27_2279_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
v___y_2205_ = v_a_2312_;
v___y_2206_ = v___x_2293_;
v_a_2207_ = v_e_2193_;
goto v___jp_2204_;
}
}
else
{
lean_object* v_a_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2331_; 
lean_dec_ref(v_e_x27_2279_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
lean_dec_ref(v_e_2193_);
v_a_2324_ = lean_ctor_get(v___x_2311_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2311_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2326_ = v___x_2311_;
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_a_2324_);
lean_dec(v___x_2311_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v___x_2329_; 
if (v_isShared_2327_ == 0)
{
v___x_2329_ = v___x_2326_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_a_2324_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
return v___x_2329_;
}
}
}
}
else
{
lean_object* v_a_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2339_; 
lean_dec_ref(v_proof_2280_);
lean_dec_ref(v_e_x27_2279_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
lean_dec_ref(v_e_2193_);
v_a_2332_ = lean_ctor_get(v___x_2307_, 0);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2307_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2334_ = v___x_2307_;
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_a_2332_);
lean_dec(v___x_2307_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v___x_2337_; 
if (v_isShared_2335_ == 0)
{
v___x_2337_ = v___x_2334_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_a_2332_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
return v___x_2337_;
}
}
}
}
}
}
else
{
lean_object* v_a_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2348_; 
lean_dec_ref(v___x_2290_);
lean_dec_ref(v_proof_2280_);
lean_dec_ref(v_e_x27_2279_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
lean_dec_ref(v_e_2193_);
v_a_2341_ = lean_ctor_get(v___x_2297_, 0);
v_isSharedCheck_2348_ = !lean_is_exclusive(v___x_2297_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2343_ = v___x_2297_;
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_a_2341_);
lean_dec(v___x_2297_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v___x_2346_; 
if (v_isShared_2344_ == 0)
{
v___x_2346_ = v___x_2343_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v_a_2341_);
v___x_2346_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
return v___x_2346_;
}
}
}
}
else
{
lean_object* v_val_2349_; lean_object* v___x_2350_; 
lean_dec_ref(v___x_2290_);
lean_dec_ref(v_proof_2280_);
lean_dec_ref(v_e_x27_2279_);
lean_dec_ref(v___y_2224_);
lean_dec_ref(v_e_2193_);
v_val_2349_ = lean_ctor_get(v_a_2296_, 0);
lean_inc(v_val_2349_);
lean_dec_ref(v_a_2296_);
v___x_2350_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_val_2349_, v___y_2225_);
if (lean_obj_tag(v___x_2350_) == 0)
{
lean_object* v_a_2351_; lean_object* v___x_2352_; 
v_a_2351_ = lean_ctor_get(v___x_2350_, 0);
lean_inc(v_a_2351_);
lean_dec_ref(v___x_2350_);
lean_inc(v_a_2351_);
v___x_2352_ = l_Lean_Meta_Sym_mkEqRefl___redArg(v_a_2351_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_);
lean_dec(v___y_2225_);
if (lean_obj_tag(v___x_2352_) == 0)
{
lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2363_; 
v_a_2353_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2363_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2355_ = v___x_2352_;
v_isShared_2356_ = v_isSharedCheck_2363_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___x_2352_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2363_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2358_; 
if (v_isShared_2283_ == 0)
{
lean_ctor_set(v___x_2282_, 1, v_a_2353_);
lean_ctor_set(v___x_2282_, 0, v_a_2351_);
v___x_2358_ = v___x_2282_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_a_2351_);
lean_ctor_set(v_reuseFailAlloc_2362_, 1, v_a_2353_);
v___x_2358_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
lean_object* v___x_2360_; 
lean_ctor_set_uint8(v___x_2358_, sizeof(void*)*2, v___x_2293_);
if (v_isShared_2356_ == 0)
{
lean_ctor_set(v___x_2355_, 0, v___x_2358_);
v___x_2360_ = v___x_2355_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v___x_2358_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
}
else
{
lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2371_; 
lean_dec(v_a_2351_);
lean_del_object(v___x_2282_);
v_a_2364_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2366_ = v___x_2352_;
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v___x_2352_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2369_; 
if (v_isShared_2367_ == 0)
{
v___x_2369_ = v___x_2366_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_a_2364_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
}
}
}
}
else
{
lean_object* v_a_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2379_; 
lean_del_object(v___x_2282_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec(v___y_2225_);
v_a_2372_ = lean_ctor_get(v___x_2350_, 0);
v_isSharedCheck_2379_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2379_ == 0)
{
v___x_2374_ = v___x_2350_;
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_a_2372_);
lean_dec(v___x_2350_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v___x_2377_; 
if (v_isShared_2375_ == 0)
{
v___x_2377_ = v___x_2374_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v_a_2372_);
v___x_2377_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
return v___x_2377_;
}
}
}
}
}
else
{
lean_object* v_a_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2387_; 
lean_dec_ref(v___x_2290_);
lean_del_object(v___x_2282_);
lean_dec_ref(v_proof_2280_);
lean_dec_ref(v_e_x27_2279_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
lean_dec_ref(v_e_2193_);
v_a_2380_ = lean_ctor_get(v___x_2295_, 0);
v_isSharedCheck_2387_ = !lean_is_exclusive(v___x_2295_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2382_ = v___x_2295_;
v_isShared_2383_ = v_isSharedCheck_2387_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_a_2380_);
lean_dec(v___x_2295_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2387_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v___x_2385_; 
if (v_isShared_2383_ == 0)
{
v___x_2385_ = v___x_2382_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_a_2380_);
v___x_2385_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
return v___x_2385_;
}
}
}
}
else
{
lean_object* v___x_2388_; 
lean_del_object(v___x_2282_);
lean_inc(v___y_2229_);
lean_inc_ref(v___y_2228_);
lean_inc(v___y_2227_);
lean_inc_ref(v___y_2226_);
v___x_2388_ = l_Lean_Meta_mkCongrArg(v___x_2290_, v_proof_2280_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_);
if (lean_obj_tag(v___x_2388_) == 0)
{
lean_object* v_a_2389_; uint8_t v___x_2390_; 
v_a_2389_ = lean_ctor_get(v___x_2388_, 0);
lean_inc(v_a_2389_);
lean_dec_ref(v___x_2388_);
v___x_2390_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_2218_, v_e_x27_2279_);
if (v___x_2390_ == 0)
{
lean_object* v___x_2391_; 
lean_inc(v_idx_2217_);
lean_inc(v_typeName_2216_);
lean_dec_ref(v_e_2193_);
v___x_2391_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_typeName_2216_, v_idx_2217_, v_e_x27_2279_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_);
if (lean_obj_tag(v___x_2391_) == 0)
{
lean_object* v_a_2392_; 
v_a_2392_ = lean_ctor_get(v___x_2391_, 0);
lean_inc(v_a_2392_);
lean_dec_ref(v___x_2391_);
v___y_2211_ = v_a_2389_;
v_a_2212_ = v_a_2392_;
goto v___jp_2210_;
}
else
{
lean_object* v_a_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2400_; 
lean_dec(v_a_2389_);
v_a_2393_ = lean_ctor_get(v___x_2391_, 0);
v_isSharedCheck_2400_ = !lean_is_exclusive(v___x_2391_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2395_ = v___x_2391_;
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_a_2393_);
lean_dec(v___x_2391_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v___x_2398_; 
if (v_isShared_2396_ == 0)
{
v___x_2398_ = v___x_2395_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v_a_2393_);
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
lean_dec_ref(v_e_x27_2279_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
v___y_2211_ = v_a_2389_;
v_a_2212_ = v_e_2193_;
goto v___jp_2210_;
}
}
else
{
lean_object* v_a_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2408_; 
lean_dec_ref(v_e_x27_2279_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
lean_dec_ref(v_e_2193_);
v_a_2401_ = lean_ctor_get(v___x_2388_, 0);
v_isSharedCheck_2408_ = !lean_is_exclusive(v___x_2388_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2403_ = v___x_2388_;
v_isShared_2404_ = v_isSharedCheck_2408_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_a_2401_);
lean_dec(v___x_2388_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2408_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
lean_object* v___x_2406_; 
if (v_isShared_2404_ == 0)
{
v___x_2406_ = v___x_2403_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v_a_2401_);
v___x_2406_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
return v___x_2406_;
}
}
}
}
}
else
{
lean_object* v_a_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2416_; 
lean_dec_ref(v___x_2290_);
lean_del_object(v___x_2282_);
lean_dec_ref(v_proof_2280_);
lean_dec_ref(v_e_x27_2279_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
lean_dec_ref(v_e_2193_);
v_a_2409_ = lean_ctor_get(v___x_2291_, 0);
v_isSharedCheck_2416_ = !lean_is_exclusive(v___x_2291_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2411_ = v___x_2291_;
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_a_2409_);
lean_dec(v___x_2291_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v___x_2414_; 
if (v_isShared_2412_ == 0)
{
v___x_2414_ = v___x_2411_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v_a_2409_);
v___x_2414_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
return v___x_2414_;
}
}
}
}
else
{
lean_object* v_a_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2424_; 
lean_del_object(v___x_2282_);
lean_dec_ref(v_proof_2280_);
lean_dec_ref(v_e_x27_2279_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
lean_dec_ref(v_e_2193_);
v_a_2417_ = lean_ctor_get(v___x_2284_, 0);
v_isSharedCheck_2424_ = !lean_is_exclusive(v___x_2284_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2419_ = v___x_2284_;
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_a_2417_);
lean_dec(v___x_2284_);
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
}
}
}
else
{
lean_object* v___x_2689_; lean_object* v___x_2690_; 
lean_dec(v_a_2202_);
lean_dec_ref(v_a_2201_);
lean_dec(v_a_2200_);
lean_dec_ref(v_a_2199_);
lean_dec(v_a_2198_);
lean_dec_ref(v_a_2197_);
lean_dec(v_a_2196_);
lean_dec_ref(v_a_2195_);
lean_dec(v_a_2194_);
lean_dec_ref(v_e_2193_);
v___x_2689_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__9));
v___x_2690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2690_, 0, v___x_2689_);
return v___x_2690_;
}
v___jp_2204_:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2208_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_2208_, 0, v_a_2207_);
lean_ctor_set(v___x_2208_, 1, v___y_2205_);
lean_ctor_set_uint8(v___x_2208_, sizeof(void*)*2, v___y_2206_);
v___x_2209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2208_);
return v___x_2209_;
}
v___jp_2210_:
{
uint8_t v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; 
v___x_2213_ = 0;
v___x_2214_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_2214_, 0, v_a_2212_);
lean_ctor_set(v___x_2214_, 1, v___y_2211_);
lean_ctor_set_uint8(v___x_2214_, sizeof(void*)*2, v___x_2213_);
v___x_2215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2214_);
return v___x_2215_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___boxed(lean_object* v_e_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_){
_start:
{
lean_object* v_res_2702_; 
v_res_2702_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj(v_e_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_);
return v_res_2702_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__5(lean_object* v_00_u03b1_2703_, lean_object* v_x_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_){
_start:
{
lean_object* v___x_2715_; 
v___x_2715_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__5___redArg(v_x_2704_);
return v___x_2715_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2716_, lean_object* v_x_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_){
_start:
{
lean_object* v_res_2728_; 
v_res_2728_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__5(v_00_u03b1_2716_, v_x_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_);
lean_dec(v___y_2726_);
lean_dec_ref(v___y_2725_);
lean_dec(v___y_2724_);
lean_dec_ref(v___y_2723_);
lean_dec(v___y_2722_);
lean_dec_ref(v___y_2721_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
lean_dec(v___y_2718_);
return v_res_2728_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__4(lean_object* v_oldTraces_2729_, lean_object* v_data_2730_, lean_object* v_ref_2731_, lean_object* v_msg_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_){
_start:
{
lean_object* v___x_2743_; 
v___x_2743_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__4___redArg(v_oldTraces_2729_, v_data_2730_, v_ref_2731_, v_msg_2732_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_);
return v___x_2743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__4___boxed(lean_object* v_oldTraces_2744_, lean_object* v_data_2745_, lean_object* v_ref_2746_, lean_object* v_msg_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_){
_start:
{
lean_object* v_res_2758_; 
v_res_2758_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__4(v_oldTraces_2744_, v_data_2745_, v_ref_2746_, v_msg_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_);
lean_dec(v___y_2756_);
lean_dec(v___y_2754_);
lean_dec_ref(v___y_2753_);
lean_dec(v___y_2752_);
lean_dec_ref(v___y_2751_);
lean_dec(v___y_2750_);
lean_dec_ref(v___y_2749_);
lean_dec(v___y_2748_);
return v_res_2758_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__0(void){
_start:
{
lean_object* v___x_2759_; lean_object* v_dummy_2760_; 
v___x_2759_ = lean_box(0);
v_dummy_2760_ = l_Lean_Expr_sort___override(v___x_2759_);
return v_dummy_2760_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__2(void){
_start:
{
lean_object* v___x_2762_; lean_object* v___x_2763_; 
v___x_2762_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__1));
v___x_2763_ = l_Lean_stringToMessageData(v___x_2762_);
return v___x_2763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn(lean_object* v_e_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_){
_start:
{
uint8_t v___x_2778_; 
v___x_2778_ = l_Lean_Expr_isApp(v_e_2764_);
if (v___x_2778_ == 0)
{
lean_object* v___x_2779_; lean_object* v___x_2780_; 
lean_dec(v_a_2773_);
lean_dec_ref(v_a_2772_);
lean_dec(v_a_2771_);
lean_dec_ref(v_a_2770_);
lean_dec(v_a_2769_);
lean_dec_ref(v_a_2768_);
lean_dec(v_a_2767_);
lean_dec_ref(v_a_2766_);
lean_dec(v_a_2765_);
lean_dec_ref(v_e_2764_);
v___x_2779_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_2779_, 0, v___x_2778_);
v___x_2780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2780_, 0, v___x_2779_);
return v___x_2780_;
}
else
{
lean_object* v_fn_2781_; uint8_t v___x_2782_; 
v_fn_2781_ = l_Lean_Expr_getAppFn(v_e_2764_);
v___x_2782_ = l_Lean_Expr_isLambda(v_fn_2781_);
if (v___x_2782_ == 0)
{
uint8_t v___x_2783_; 
v___x_2783_ = l_Lean_Expr_isConst(v_fn_2781_);
if (v___x_2783_ == 0)
{
lean_object* v___x_2784_; 
lean_inc(v_a_2773_);
lean_inc_ref(v_a_2772_);
lean_inc(v_a_2771_);
lean_inc_ref(v_a_2770_);
lean_inc(v_a_2769_);
lean_inc_ref(v_a_2768_);
v___x_2784_ = lean_sym_simp(v_fn_2781_, v_a_2765_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_, v_a_2771_, v_a_2772_, v_a_2773_);
if (lean_obj_tag(v___x_2784_) == 0)
{
lean_object* v_a_2785_; 
v_a_2785_ = lean_ctor_get(v___x_2784_, 0);
lean_inc(v_a_2785_);
if (lean_obj_tag(v_a_2785_) == 0)
{
lean_dec_ref(v_a_2785_);
lean_dec(v_a_2773_);
lean_dec_ref(v_a_2772_);
lean_dec(v_a_2771_);
lean_dec_ref(v_a_2770_);
lean_dec(v_a_2769_);
lean_dec_ref(v_a_2768_);
lean_dec_ref(v_e_2764_);
return v___x_2784_;
}
else
{
lean_object* v_e_x27_2786_; lean_object* v_proof_2787_; lean_object* v___x_2789_; uint8_t v_isShared_2790_; uint8_t v_isSharedCheck_2863_; 
lean_dec_ref(v___x_2784_);
v_e_x27_2786_ = lean_ctor_get(v_a_2785_, 0);
v_proof_2787_ = lean_ctor_get(v_a_2785_, 1);
v_isSharedCheck_2863_ = !lean_is_exclusive(v_a_2785_);
if (v_isSharedCheck_2863_ == 0)
{
v___x_2789_ = v_a_2785_;
v_isShared_2790_ = v_isSharedCheck_2863_;
goto v_resetjp_2788_;
}
else
{
lean_inc(v_proof_2787_);
lean_inc(v_e_x27_2786_);
lean_dec(v_a_2785_);
v___x_2789_ = lean_box(0);
v_isShared_2790_ = v_isSharedCheck_2863_;
goto v_resetjp_2788_;
}
v_resetjp_2788_:
{
lean_object* v___x_2791_; 
lean_inc(v_a_2773_);
lean_inc_ref(v_a_2772_);
lean_inc(v_a_2771_);
lean_inc_ref(v_a_2770_);
lean_inc_ref(v_e_x27_2786_);
v___x_2791_ = l_Lean_Meta_Sym_inferType___redArg(v_e_x27_2786_, v_a_2769_, v_a_2770_, v_a_2771_, v_a_2772_, v_a_2773_);
if (lean_obj_tag(v___x_2791_) == 0)
{
lean_object* v_a_2792_; lean_object* v_dummy_2793_; lean_object* v_nargs_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; 
v_a_2792_ = lean_ctor_get(v___x_2791_, 0);
lean_inc(v_a_2792_);
lean_dec_ref(v___x_2791_);
v_dummy_2793_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__0, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__0_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__0);
v_nargs_2794_ = l_Lean_Expr_getAppNumArgs(v_e_2764_);
lean_inc(v_nargs_2794_);
v___x_2795_ = lean_mk_array(v_nargs_2794_, v_dummy_2793_);
v___x_2796_ = lean_unsigned_to_nat(1u);
v___x_2797_ = lean_nat_sub(v_nargs_2794_, v___x_2796_);
lean_dec(v_nargs_2794_);
lean_inc_ref(v_e_2764_);
v___x_2798_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2764_, v___x_2795_, v___x_2797_);
lean_inc(v_a_2773_);
lean_inc_ref(v_a_2772_);
lean_inc(v_a_2771_);
lean_inc_ref(v_a_2770_);
v___x_2799_ = l_Lean_Meta_Tactic_Cbv_mkAppNS(v_e_x27_2786_, v___x_2798_, v_a_2768_, v_a_2769_, v_a_2770_, v_a_2771_, v_a_2772_, v_a_2773_);
if (lean_obj_tag(v___x_2799_) == 0)
{
lean_object* v_a_2800_; lean_object* v___x_2801_; uint8_t v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; 
v_a_2800_ = lean_ctor_get(v___x_2799_, 0);
lean_inc(v_a_2800_);
lean_dec_ref(v___x_2799_);
v___x_2801_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2));
v___x_2802_ = 0;
v___x_2803_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__3, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__3_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__3);
v___x_2804_ = l_Lean_mkAppN(v___x_2803_, v___x_2798_);
lean_dec_ref(v___x_2798_);
v___x_2805_ = l_Lean_mkLambda(v___x_2801_, v___x_2802_, v_a_2792_, v___x_2804_);
lean_inc(v_a_2773_);
lean_inc_ref(v_a_2772_);
lean_inc(v_a_2771_);
lean_inc_ref(v_a_2770_);
v___x_2806_ = l_Lean_Meta_mkCongrArg(v___x_2805_, v_proof_2787_, v_a_2770_, v_a_2771_, v_a_2772_, v_a_2773_);
if (lean_obj_tag(v___x_2806_) == 0)
{
lean_object* v_a_2807_; lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2838_; 
v_a_2807_ = lean_ctor_get(v___x_2806_, 0);
v_isSharedCheck_2838_ = !lean_is_exclusive(v___x_2806_);
if (v_isSharedCheck_2838_ == 0)
{
v___x_2809_ = v___x_2806_;
v_isShared_2810_ = v_isSharedCheck_2838_;
goto v_resetjp_2808_;
}
else
{
lean_inc(v_a_2807_);
lean_dec(v___x_2806_);
v___x_2809_ = lean_box(0);
v_isShared_2810_ = v_isSharedCheck_2838_;
goto v_resetjp_2808_;
}
v_resetjp_2808_:
{
lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v_a_2820_; uint8_t v___x_2821_; 
v___x_2818_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2));
v___x_2819_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(v___x_2818_, v_a_2772_);
v_a_2820_ = lean_ctor_get(v___x_2819_, 0);
lean_inc(v_a_2820_);
lean_dec_ref(v___x_2819_);
v___x_2821_ = lean_unbox(v_a_2820_);
lean_dec(v_a_2820_);
if (v___x_2821_ == 0)
{
lean_dec(v_a_2773_);
lean_dec_ref(v_a_2772_);
lean_dec(v_a_2771_);
lean_dec_ref(v_a_2770_);
lean_dec_ref(v_e_2764_);
goto v___jp_2811_;
}
else
{
lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; 
v___x_2822_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__2, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__2);
v___x_2823_ = l_Lean_indentExpr(v_e_2764_);
v___x_2824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2824_, 0, v___x_2822_);
lean_ctor_set(v___x_2824_, 1, v___x_2823_);
v___x_2825_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7);
v___x_2826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2826_, 0, v___x_2824_);
lean_ctor_set(v___x_2826_, 1, v___x_2825_);
lean_inc(v_a_2800_);
v___x_2827_ = l_Lean_indentExpr(v_a_2800_);
v___x_2828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2828_, 0, v___x_2826_);
lean_ctor_set(v___x_2828_, 1, v___x_2827_);
v___x_2829_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg(v___x_2818_, v___x_2828_, v_a_2770_, v_a_2771_, v_a_2772_, v_a_2773_);
lean_dec(v_a_2773_);
lean_dec_ref(v_a_2772_);
lean_dec(v_a_2771_);
lean_dec_ref(v_a_2770_);
if (lean_obj_tag(v___x_2829_) == 0)
{
lean_dec_ref(v___x_2829_);
goto v___jp_2811_;
}
else
{
lean_object* v_a_2830_; lean_object* v___x_2832_; uint8_t v_isShared_2833_; uint8_t v_isSharedCheck_2837_; 
lean_del_object(v___x_2809_);
lean_dec(v_a_2807_);
lean_dec(v_a_2800_);
lean_del_object(v___x_2789_);
v_a_2830_ = lean_ctor_get(v___x_2829_, 0);
v_isSharedCheck_2837_ = !lean_is_exclusive(v___x_2829_);
if (v_isSharedCheck_2837_ == 0)
{
v___x_2832_ = v___x_2829_;
v_isShared_2833_ = v_isSharedCheck_2837_;
goto v_resetjp_2831_;
}
else
{
lean_inc(v_a_2830_);
lean_dec(v___x_2829_);
v___x_2832_ = lean_box(0);
v_isShared_2833_ = v_isSharedCheck_2837_;
goto v_resetjp_2831_;
}
v_resetjp_2831_:
{
lean_object* v___x_2835_; 
if (v_isShared_2833_ == 0)
{
v___x_2835_ = v___x_2832_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v_a_2830_);
v___x_2835_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
return v___x_2835_;
}
}
}
}
v___jp_2811_:
{
lean_object* v___x_2813_; 
if (v_isShared_2790_ == 0)
{
lean_ctor_set(v___x_2789_, 1, v_a_2807_);
lean_ctor_set(v___x_2789_, 0, v_a_2800_);
v___x_2813_ = v___x_2789_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v_a_2800_);
lean_ctor_set(v_reuseFailAlloc_2817_, 1, v_a_2807_);
v___x_2813_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
lean_object* v___x_2815_; 
lean_ctor_set_uint8(v___x_2813_, sizeof(void*)*2, v___x_2783_);
if (v_isShared_2810_ == 0)
{
lean_ctor_set(v___x_2809_, 0, v___x_2813_);
v___x_2815_ = v___x_2809_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v___x_2813_);
v___x_2815_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
return v___x_2815_;
}
}
}
}
}
else
{
lean_object* v_a_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2846_; 
lean_dec(v_a_2800_);
lean_del_object(v___x_2789_);
lean_dec(v_a_2773_);
lean_dec_ref(v_a_2772_);
lean_dec(v_a_2771_);
lean_dec_ref(v_a_2770_);
lean_dec_ref(v_e_2764_);
v_a_2839_ = lean_ctor_get(v___x_2806_, 0);
v_isSharedCheck_2846_ = !lean_is_exclusive(v___x_2806_);
if (v_isSharedCheck_2846_ == 0)
{
v___x_2841_ = v___x_2806_;
v_isShared_2842_ = v_isSharedCheck_2846_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_a_2839_);
lean_dec(v___x_2806_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2846_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v___x_2844_; 
if (v_isShared_2842_ == 0)
{
v___x_2844_ = v___x_2841_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v_a_2839_);
v___x_2844_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
return v___x_2844_;
}
}
}
}
else
{
lean_object* v_a_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2854_; 
lean_dec_ref(v___x_2798_);
lean_dec(v_a_2792_);
lean_del_object(v___x_2789_);
lean_dec_ref(v_proof_2787_);
lean_dec(v_a_2773_);
lean_dec_ref(v_a_2772_);
lean_dec(v_a_2771_);
lean_dec_ref(v_a_2770_);
lean_dec_ref(v_e_2764_);
v_a_2847_ = lean_ctor_get(v___x_2799_, 0);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___x_2799_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2849_ = v___x_2799_;
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_a_2847_);
lean_dec(v___x_2799_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v___x_2852_; 
if (v_isShared_2850_ == 0)
{
v___x_2852_ = v___x_2849_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_a_2847_);
v___x_2852_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
return v___x_2852_;
}
}
}
}
else
{
lean_object* v_a_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2862_; 
lean_del_object(v___x_2789_);
lean_dec_ref(v_proof_2787_);
lean_dec_ref(v_e_x27_2786_);
lean_dec(v_a_2773_);
lean_dec_ref(v_a_2772_);
lean_dec(v_a_2771_);
lean_dec_ref(v_a_2770_);
lean_dec(v_a_2769_);
lean_dec_ref(v_a_2768_);
lean_dec_ref(v_e_2764_);
v_a_2855_ = lean_ctor_get(v___x_2791_, 0);
v_isSharedCheck_2862_ = !lean_is_exclusive(v___x_2791_);
if (v_isSharedCheck_2862_ == 0)
{
v___x_2857_ = v___x_2791_;
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_a_2855_);
lean_dec(v___x_2791_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v___x_2860_; 
if (v_isShared_2858_ == 0)
{
v___x_2860_ = v___x_2857_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v_a_2855_);
v___x_2860_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
return v___x_2860_;
}
}
}
}
}
}
else
{
lean_dec(v_a_2773_);
lean_dec_ref(v_a_2772_);
lean_dec(v_a_2771_);
lean_dec_ref(v_a_2770_);
lean_dec(v_a_2769_);
lean_dec_ref(v_a_2768_);
lean_dec_ref(v_e_2764_);
return v___x_2784_;
}
}
else
{
lean_dec_ref(v_fn_2781_);
lean_dec(v_a_2773_);
lean_dec_ref(v_a_2772_);
lean_dec(v_a_2771_);
lean_dec_ref(v_a_2770_);
lean_dec(v_a_2769_);
lean_dec_ref(v_a_2768_);
lean_dec(v_a_2767_);
lean_dec_ref(v_a_2766_);
lean_dec(v_a_2765_);
lean_dec_ref(v_e_2764_);
goto v___jp_2775_;
}
}
else
{
lean_dec_ref(v_fn_2781_);
lean_dec(v_a_2773_);
lean_dec_ref(v_a_2772_);
lean_dec(v_a_2771_);
lean_dec_ref(v_a_2770_);
lean_dec(v_a_2769_);
lean_dec_ref(v_a_2768_);
lean_dec(v_a_2767_);
lean_dec_ref(v_a_2766_);
lean_dec(v_a_2765_);
lean_dec_ref(v_e_2764_);
goto v___jp_2775_;
}
}
v___jp_2775_:
{
lean_object* v___x_2776_; lean_object* v___x_2777_; 
v___x_2776_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__9));
v___x_2777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2777_, 0, v___x_2776_);
return v___x_2777_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___boxed(lean_object* v_e_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_){
_start:
{
lean_object* v_res_2875_; 
v_res_2875_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn(v_e_2864_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_);
return v_res_2875_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___closed__1(void){
_start:
{
lean_object* v___x_2877_; lean_object* v___x_2878_; 
v___x_2877_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___closed__0));
v___x_2878_ = l_Lean_stringToMessageData(v___x_2877_);
return v___x_2878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst(lean_object* v_e_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_){
_start:
{
if (lean_obj_tag(v_e_2879_) == 4)
{
lean_object* v_declName_2890_; lean_object* v_us_2891_; lean_object* v___x_2892_; 
v_declName_2890_ = lean_ctor_get(v_e_2879_, 0);
v_us_2891_ = lean_ctor_get(v_e_2879_, 1);
lean_inc_ref(v_a_2887_);
lean_inc(v_declName_2890_);
v___x_2892_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0(v_declName_2890_, v_a_2880_, v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_);
if (lean_obj_tag(v___x_2892_) == 0)
{
lean_object* v_a_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_3011_; 
v_a_2893_ = lean_ctor_get(v___x_2892_, 0);
v_isSharedCheck_3011_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_3011_ == 0)
{
v___x_2895_ = v___x_2892_;
v_isShared_2896_ = v_isSharedCheck_3011_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_a_2893_);
lean_dec(v___x_2892_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_3011_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
uint8_t v___x_2897_; 
v___x_2897_ = l_Lean_ConstantInfo_isDefinition(v_a_2893_);
if (v___x_2897_ == 0)
{
lean_object* v___x_2898_; lean_object* v___x_2900_; 
lean_dec(v_a_2893_);
lean_dec_ref(v_e_2879_);
lean_dec(v_a_2888_);
lean_dec_ref(v_a_2887_);
lean_dec(v_a_2886_);
lean_dec_ref(v_a_2885_);
v___x_2898_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_2898_, 0, v___x_2897_);
if (v_isShared_2896_ == 0)
{
lean_ctor_set(v___x_2895_, 0, v___x_2898_);
v___x_2900_ = v___x_2895_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v___x_2898_);
v___x_2900_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
return v___x_2900_;
}
}
else
{
lean_object* v___x_2902_; 
lean_del_object(v___x_2895_);
lean_inc(v_a_2888_);
lean_inc_ref(v_a_2887_);
lean_inc(v_a_2886_);
lean_inc_ref(v_a_2885_);
lean_inc_ref(v_e_2879_);
v___x_2902_ = l_Lean_Meta_Sym_inferType___redArg(v_e_2879_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_);
if (lean_obj_tag(v___x_2902_) == 0)
{
lean_object* v_a_2903_; lean_object* v___x_2904_; 
v_a_2903_ = lean_ctor_get(v___x_2902_, 0);
lean_inc(v_a_2903_);
lean_dec_ref(v___x_2902_);
lean_inc(v_a_2888_);
lean_inc_ref(v_a_2887_);
lean_inc(v_a_2886_);
lean_inc_ref(v_a_2885_);
v___x_2904_ = l_Lean_Meta_whnfD(v_a_2903_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_);
if (lean_obj_tag(v___x_2904_) == 0)
{
lean_object* v_a_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2994_; 
v_a_2905_ = lean_ctor_get(v___x_2904_, 0);
v_isSharedCheck_2994_ = !lean_is_exclusive(v___x_2904_);
if (v_isSharedCheck_2994_ == 0)
{
v___x_2907_ = v___x_2904_;
v_isShared_2908_ = v_isSharedCheck_2994_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_a_2905_);
lean_dec(v___x_2904_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2994_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
if (lean_obj_tag(v_a_2905_) == 7)
{
lean_object* v___x_2909_; lean_object* v___x_2911_; 
lean_dec_ref(v_a_2905_);
lean_dec(v_a_2893_);
lean_dec_ref(v_e_2879_);
lean_dec(v_a_2888_);
lean_dec_ref(v_a_2887_);
lean_dec(v_a_2886_);
lean_dec_ref(v_a_2885_);
v___x_2909_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__9));
if (v_isShared_2908_ == 0)
{
lean_ctor_set(v___x_2907_, 0, v___x_2909_);
v___x_2911_ = v___x_2907_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v___x_2909_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
else
{
uint8_t v___x_2913_; lean_object* v___y_2915_; lean_object* v___y_2916_; lean_object* v___y_2917_; lean_object* v___y_2918_; lean_object* v___y_2919_; lean_object* v___y_2920_; uint8_t v___y_2940_; uint8_t v___x_2989_; 
lean_dec(v_a_2905_);
v___x_2913_ = 0;
v___x_2989_ = l_Lean_ConstantInfo_hasValue(v_a_2893_, v___x_2913_);
if (v___x_2989_ == 0)
{
v___y_2940_ = v___x_2989_;
goto v___jp_2939_;
}
else
{
lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; uint8_t v___x_2993_; 
v___x_2990_ = l_Lean_ConstantInfo_levelParams(v_a_2893_);
v___x_2991_ = l_List_lengthTR___redArg(v___x_2990_);
lean_dec(v___x_2990_);
v___x_2992_ = l_List_lengthTR___redArg(v_us_2891_);
v___x_2993_ = lean_nat_dec_eq(v___x_2991_, v___x_2992_);
lean_dec(v___x_2992_);
lean_dec(v___x_2991_);
v___y_2940_ = v___x_2993_;
goto v___jp_2939_;
}
v___jp_2914_:
{
lean_object* v___x_2921_; 
lean_inc_ref(v___y_2915_);
v___x_2921_ = l_Lean_Meta_Sym_mkEqRefl___redArg(v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_);
if (lean_obj_tag(v___x_2921_) == 0)
{
lean_object* v_a_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2930_; 
v_a_2922_ = lean_ctor_get(v___x_2921_, 0);
v_isSharedCheck_2930_ = !lean_is_exclusive(v___x_2921_);
if (v_isSharedCheck_2930_ == 0)
{
v___x_2924_ = v___x_2921_;
v_isShared_2925_ = v_isSharedCheck_2930_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_a_2922_);
lean_dec(v___x_2921_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2930_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v___x_2926_; lean_object* v___x_2928_; 
v___x_2926_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_2926_, 0, v___y_2915_);
lean_ctor_set(v___x_2926_, 1, v_a_2922_);
lean_ctor_set_uint8(v___x_2926_, sizeof(void*)*2, v___x_2913_);
if (v_isShared_2925_ == 0)
{
lean_ctor_set(v___x_2924_, 0, v___x_2926_);
v___x_2928_ = v___x_2924_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v___x_2926_);
v___x_2928_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
return v___x_2928_;
}
}
}
else
{
lean_object* v_a_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2938_; 
lean_dec_ref(v___y_2915_);
v_a_2931_ = lean_ctor_get(v___x_2921_, 0);
v_isSharedCheck_2938_ = !lean_is_exclusive(v___x_2921_);
if (v_isSharedCheck_2938_ == 0)
{
v___x_2933_ = v___x_2921_;
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_a_2931_);
lean_dec(v___x_2921_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v___x_2936_; 
if (v_isShared_2934_ == 0)
{
v___x_2936_ = v___x_2933_;
goto v_reusejp_2935_;
}
else
{
lean_object* v_reuseFailAlloc_2937_; 
v_reuseFailAlloc_2937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2937_, 0, v_a_2931_);
v___x_2936_ = v_reuseFailAlloc_2937_;
goto v_reusejp_2935_;
}
v_reusejp_2935_:
{
return v___x_2936_;
}
}
}
}
v___jp_2939_:
{
if (v___y_2940_ == 0)
{
lean_object* v___x_2941_; lean_object* v___x_2943_; 
lean_dec(v_a_2893_);
lean_dec_ref(v_e_2879_);
lean_dec(v_a_2888_);
lean_dec_ref(v_a_2887_);
lean_dec(v_a_2886_);
lean_dec_ref(v_a_2885_);
v___x_2941_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__9));
if (v_isShared_2908_ == 0)
{
lean_ctor_set(v___x_2907_, 0, v___x_2941_);
v___x_2943_ = v___x_2907_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v___x_2941_);
v___x_2943_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2942_;
}
v_reusejp_2942_:
{
return v___x_2943_;
}
}
else
{
lean_object* v___x_2945_; 
lean_del_object(v___x_2907_);
lean_inc(v_us_2891_);
v___x_2945_ = l_Lean_Core_instantiateValueLevelParams(v_a_2893_, v_us_2891_, v_a_2887_, v_a_2888_);
lean_dec(v_a_2893_);
if (lean_obj_tag(v___x_2945_) == 0)
{
lean_object* v_a_2946_; lean_object* v___x_2947_; 
v_a_2946_ = lean_ctor_get(v___x_2945_, 0);
lean_inc(v_a_2946_);
lean_dec_ref(v___x_2945_);
v___x_2947_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_a_2946_, v_a_2884_);
if (lean_obj_tag(v___x_2947_) == 0)
{
lean_object* v_a_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v_a_2951_; uint8_t v___x_2952_; 
v_a_2948_ = lean_ctor_get(v___x_2947_, 0);
lean_inc(v_a_2948_);
lean_dec_ref(v___x_2947_);
v___x_2949_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__1));
v___x_2950_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(v___x_2949_, v_a_2887_);
v_a_2951_ = lean_ctor_get(v___x_2950_, 0);
lean_inc(v_a_2951_);
lean_dec_ref(v___x_2950_);
v___x_2952_ = lean_unbox(v_a_2951_);
lean_dec(v_a_2951_);
if (v___x_2952_ == 0)
{
lean_dec_ref(v_e_2879_);
v___y_2915_ = v_a_2948_;
v___y_2916_ = v_a_2884_;
v___y_2917_ = v_a_2885_;
v___y_2918_ = v_a_2886_;
v___y_2919_ = v_a_2887_;
v___y_2920_ = v_a_2888_;
goto v___jp_2914_;
}
else
{
lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; 
v___x_2953_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___closed__1, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___closed__1);
lean_inc(v_declName_2890_);
v___x_2954_ = l_Lean_MessageData_ofName(v_declName_2890_);
v___x_2955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2955_, 0, v___x_2953_);
lean_ctor_set(v___x_2955_, 1, v___x_2954_);
v___x_2956_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__5, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__5_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__5);
v___x_2957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2957_, 0, v___x_2955_);
lean_ctor_set(v___x_2957_, 1, v___x_2956_);
v___x_2958_ = l_Lean_indentExpr(v_e_2879_);
v___x_2959_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2959_, 0, v___x_2957_);
lean_ctor_set(v___x_2959_, 1, v___x_2958_);
v___x_2960_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7);
v___x_2961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2961_, 0, v___x_2959_);
lean_ctor_set(v___x_2961_, 1, v___x_2960_);
lean_inc(v_a_2948_);
v___x_2962_ = l_Lean_indentExpr(v_a_2948_);
v___x_2963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2963_, 0, v___x_2961_);
lean_ctor_set(v___x_2963_, 1, v___x_2962_);
v___x_2964_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg(v___x_2949_, v___x_2963_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_);
if (lean_obj_tag(v___x_2964_) == 0)
{
lean_dec_ref(v___x_2964_);
v___y_2915_ = v_a_2948_;
v___y_2916_ = v_a_2884_;
v___y_2917_ = v_a_2885_;
v___y_2918_ = v_a_2886_;
v___y_2919_ = v_a_2887_;
v___y_2920_ = v_a_2888_;
goto v___jp_2914_;
}
else
{
lean_object* v_a_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_2972_; 
lean_dec(v_a_2948_);
lean_dec(v_a_2888_);
lean_dec_ref(v_a_2887_);
lean_dec(v_a_2886_);
lean_dec_ref(v_a_2885_);
v_a_2965_ = lean_ctor_get(v___x_2964_, 0);
v_isSharedCheck_2972_ = !lean_is_exclusive(v___x_2964_);
if (v_isSharedCheck_2972_ == 0)
{
v___x_2967_ = v___x_2964_;
v_isShared_2968_ = v_isSharedCheck_2972_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_a_2965_);
lean_dec(v___x_2964_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_2972_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
lean_object* v___x_2970_; 
if (v_isShared_2968_ == 0)
{
v___x_2970_ = v___x_2967_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v_a_2965_);
v___x_2970_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
return v___x_2970_;
}
}
}
}
}
else
{
lean_object* v_a_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_2980_; 
lean_dec_ref(v_e_2879_);
lean_dec(v_a_2888_);
lean_dec_ref(v_a_2887_);
lean_dec(v_a_2886_);
lean_dec_ref(v_a_2885_);
v_a_2973_ = lean_ctor_get(v___x_2947_, 0);
v_isSharedCheck_2980_ = !lean_is_exclusive(v___x_2947_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2975_ = v___x_2947_;
v_isShared_2976_ = v_isSharedCheck_2980_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_a_2973_);
lean_dec(v___x_2947_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_2980_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
lean_object* v___x_2978_; 
if (v_isShared_2976_ == 0)
{
v___x_2978_ = v___x_2975_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v_a_2973_);
v___x_2978_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
return v___x_2978_;
}
}
}
}
else
{
lean_object* v_a_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_2988_; 
lean_dec_ref(v_e_2879_);
lean_dec(v_a_2888_);
lean_dec_ref(v_a_2887_);
lean_dec(v_a_2886_);
lean_dec_ref(v_a_2885_);
v_a_2981_ = lean_ctor_get(v___x_2945_, 0);
v_isSharedCheck_2988_ = !lean_is_exclusive(v___x_2945_);
if (v_isSharedCheck_2988_ == 0)
{
v___x_2983_ = v___x_2945_;
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_a_2981_);
lean_dec(v___x_2945_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v___x_2986_; 
if (v_isShared_2984_ == 0)
{
v___x_2986_ = v___x_2983_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v_a_2981_);
v___x_2986_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
return v___x_2986_;
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
lean_object* v_a_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3002_; 
lean_dec(v_a_2893_);
lean_dec_ref(v_e_2879_);
lean_dec(v_a_2888_);
lean_dec_ref(v_a_2887_);
lean_dec(v_a_2886_);
lean_dec_ref(v_a_2885_);
v_a_2995_ = lean_ctor_get(v___x_2904_, 0);
v_isSharedCheck_3002_ = !lean_is_exclusive(v___x_2904_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2997_ = v___x_2904_;
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
else
{
lean_inc(v_a_2995_);
lean_dec(v___x_2904_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
lean_object* v___x_3000_; 
if (v_isShared_2998_ == 0)
{
v___x_3000_ = v___x_2997_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v_a_2995_);
v___x_3000_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
return v___x_3000_;
}
}
}
}
else
{
lean_object* v_a_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3010_; 
lean_dec(v_a_2893_);
lean_dec_ref(v_e_2879_);
lean_dec(v_a_2888_);
lean_dec_ref(v_a_2887_);
lean_dec(v_a_2886_);
lean_dec_ref(v_a_2885_);
v_a_3003_ = lean_ctor_get(v___x_2902_, 0);
v_isSharedCheck_3010_ = !lean_is_exclusive(v___x_2902_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_3005_ = v___x_2902_;
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_a_3003_);
lean_dec(v___x_2902_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3008_; 
if (v_isShared_3006_ == 0)
{
v___x_3008_ = v___x_3005_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_a_3003_);
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
else
{
lean_object* v_a_3012_; lean_object* v___x_3014_; uint8_t v_isShared_3015_; uint8_t v_isSharedCheck_3019_; 
lean_dec_ref(v_e_2879_);
lean_dec(v_a_2888_);
lean_dec_ref(v_a_2887_);
lean_dec(v_a_2886_);
lean_dec_ref(v_a_2885_);
v_a_3012_ = lean_ctor_get(v___x_2892_, 0);
v_isSharedCheck_3019_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_3019_ == 0)
{
v___x_3014_ = v___x_2892_;
v_isShared_3015_ = v_isSharedCheck_3019_;
goto v_resetjp_3013_;
}
else
{
lean_inc(v_a_3012_);
lean_dec(v___x_2892_);
v___x_3014_ = lean_box(0);
v_isShared_3015_ = v_isSharedCheck_3019_;
goto v_resetjp_3013_;
}
v_resetjp_3013_:
{
lean_object* v___x_3017_; 
if (v_isShared_3015_ == 0)
{
v___x_3017_ = v___x_3014_;
goto v_reusejp_3016_;
}
else
{
lean_object* v_reuseFailAlloc_3018_; 
v_reuseFailAlloc_3018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3018_, 0, v_a_3012_);
v___x_3017_ = v_reuseFailAlloc_3018_;
goto v_reusejp_3016_;
}
v_reusejp_3016_:
{
return v___x_3017_;
}
}
}
}
else
{
lean_object* v___x_3020_; lean_object* v___x_3021_; 
lean_dec(v_a_2888_);
lean_dec_ref(v_a_2887_);
lean_dec(v_a_2886_);
lean_dec_ref(v_a_2885_);
lean_dec_ref(v_e_2879_);
v___x_3020_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__9));
v___x_3021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3021_, 0, v___x_3020_);
return v___x_3021_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___boxed(lean_object* v_e_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_){
_start:
{
lean_object* v_res_3033_; 
v_res_3033_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst(v_e_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_);
lean_dec(v_a_3027_);
lean_dec_ref(v_a_3026_);
lean_dec(v_a_3025_);
lean_dec_ref(v_a_3024_);
lean_dec(v_a_3023_);
return v_res_3033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___lam__0(lean_object* v_x_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_){
_start:
{
lean_object* v___x_3046_; 
lean_inc(v___y_3044_);
lean_inc_ref(v___y_3043_);
lean_inc(v___y_3042_);
lean_inc_ref(v___y_3041_);
lean_inc(v___y_3040_);
lean_inc_ref(v___y_3039_);
lean_inc(v___y_3038_);
lean_inc_ref(v___y_3037_);
lean_inc(v___y_3036_);
lean_inc_ref(v___y_3035_);
v___x_3046_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems(v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_);
if (lean_obj_tag(v___x_3046_) == 0)
{
lean_object* v_a_3047_; 
v_a_3047_ = lean_ctor_get(v___x_3046_, 0);
lean_inc(v_a_3047_);
if (lean_obj_tag(v_a_3047_) == 0)
{
uint8_t v_done_3048_; 
v_done_3048_ = lean_ctor_get_uint8(v_a_3047_, 0);
lean_dec_ref(v_a_3047_);
if (v_done_3048_ == 0)
{
lean_object* v___x_3049_; 
lean_dec_ref(v___x_3046_);
v___x_3049_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst(v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_);
lean_dec(v___y_3040_);
lean_dec_ref(v___y_3039_);
lean_dec(v___y_3038_);
lean_dec_ref(v___y_3037_);
lean_dec(v___y_3036_);
return v___x_3049_;
}
else
{
lean_dec(v___y_3044_);
lean_dec_ref(v___y_3043_);
lean_dec(v___y_3042_);
lean_dec_ref(v___y_3041_);
lean_dec(v___y_3040_);
lean_dec_ref(v___y_3039_);
lean_dec(v___y_3038_);
lean_dec_ref(v___y_3037_);
lean_dec(v___y_3036_);
lean_dec_ref(v___y_3035_);
return v___x_3046_;
}
}
else
{
lean_dec_ref(v_a_3047_);
lean_dec(v___y_3044_);
lean_dec_ref(v___y_3043_);
lean_dec(v___y_3042_);
lean_dec_ref(v___y_3041_);
lean_dec(v___y_3040_);
lean_dec_ref(v___y_3039_);
lean_dec(v___y_3038_);
lean_dec_ref(v___y_3037_);
lean_dec(v___y_3036_);
lean_dec_ref(v___y_3035_);
return v___x_3046_;
}
}
else
{
lean_dec(v___y_3044_);
lean_dec_ref(v___y_3043_);
lean_dec(v___y_3042_);
lean_dec_ref(v___y_3041_);
lean_dec(v___y_3040_);
lean_dec_ref(v___y_3039_);
lean_dec(v___y_3038_);
lean_dec_ref(v___y_3037_);
lean_dec(v___y_3036_);
lean_dec_ref(v___y_3035_);
return v___x_3046_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___lam__0___boxed(lean_object* v_x_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_){
_start:
{
lean_object* v_res_3062_; 
v_res_3062_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___lam__0(v_x_3050_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_);
return v_res_3062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep(lean_object* v_e_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_){
_start:
{
switch(lean_obj_tag(v_e_3063_))
{
case 9:
{
lean_object* v___x_3077_; 
lean_dec_ref(v_a_3067_);
lean_dec(v_a_3066_);
lean_dec_ref(v_a_3065_);
lean_dec(v_a_3064_);
v___x_3077_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg(v_e_3063_, v_a_3068_, v_a_3069_, v_a_3070_, v_a_3071_, v_a_3072_);
lean_dec(v_a_3068_);
return v___x_3077_;
}
case 11:
{
lean_object* v___x_3078_; 
v___x_3078_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj(v_e_3063_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_, v_a_3070_, v_a_3071_, v_a_3072_);
return v___x_3078_;
}
case 4:
{
lean_object* v___x_3079_; 
lean_inc(v_a_3072_);
lean_inc_ref(v_a_3071_);
lean_inc(v_a_3070_);
lean_inc_ref(v_a_3069_);
lean_inc(v_a_3068_);
lean_inc_ref(v_a_3067_);
lean_inc(v_a_3066_);
lean_inc_ref(v_a_3065_);
lean_inc(v_a_3064_);
lean_inc_ref(v_e_3063_);
v___x_3079_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleOpaqueConst(v_e_3063_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_, v_a_3070_, v_a_3071_, v_a_3072_);
if (lean_obj_tag(v___x_3079_) == 0)
{
lean_object* v_a_3080_; lean_object* v___x_3081_; 
v_a_3080_ = lean_ctor_get(v___x_3079_, 0);
lean_inc(v_a_3080_);
v___x_3081_ = lean_box(0);
if (lean_obj_tag(v_a_3080_) == 0)
{
uint8_t v_done_3082_; 
v_done_3082_ = lean_ctor_get_uint8(v_a_3080_, 0);
lean_dec_ref(v_a_3080_);
if (v_done_3082_ == 0)
{
lean_object* v___x_3083_; 
lean_dec_ref(v___x_3079_);
v___x_3083_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___lam__0(v___x_3081_, v_e_3063_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_, v_a_3070_, v_a_3071_, v_a_3072_);
return v___x_3083_;
}
else
{
lean_dec_ref(v_e_3063_);
lean_dec(v_a_3072_);
lean_dec_ref(v_a_3071_);
lean_dec(v_a_3070_);
lean_dec_ref(v_a_3069_);
lean_dec(v_a_3068_);
lean_dec_ref(v_a_3067_);
lean_dec(v_a_3066_);
lean_dec_ref(v_a_3065_);
lean_dec(v_a_3064_);
return v___x_3079_;
}
}
else
{
uint8_t v_done_3084_; 
v_done_3084_ = lean_ctor_get_uint8(v_a_3080_, sizeof(void*)*2);
if (v_done_3084_ == 0)
{
lean_object* v_e_x27_3085_; lean_object* v_proof_3086_; lean_object* v___x_3088_; uint8_t v_isShared_3089_; uint8_t v_isSharedCheck_3130_; 
lean_dec_ref(v___x_3079_);
v_e_x27_3085_ = lean_ctor_get(v_a_3080_, 0);
v_proof_3086_ = lean_ctor_get(v_a_3080_, 1);
v_isSharedCheck_3130_ = !lean_is_exclusive(v_a_3080_);
if (v_isSharedCheck_3130_ == 0)
{
v___x_3088_ = v_a_3080_;
v_isShared_3089_ = v_isSharedCheck_3130_;
goto v_resetjp_3087_;
}
else
{
lean_inc(v_proof_3086_);
lean_inc(v_e_x27_3085_);
lean_dec(v_a_3080_);
v___x_3088_ = lean_box(0);
v_isShared_3089_ = v_isSharedCheck_3130_;
goto v_resetjp_3087_;
}
v_resetjp_3087_:
{
lean_object* v___x_3090_; 
lean_inc(v_a_3072_);
lean_inc_ref(v_a_3071_);
lean_inc(v_a_3070_);
lean_inc_ref(v_a_3069_);
lean_inc(v_a_3068_);
lean_inc_ref(v_e_x27_3085_);
v___x_3090_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___lam__0(v___x_3081_, v_e_x27_3085_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_, v_a_3070_, v_a_3071_, v_a_3072_);
if (lean_obj_tag(v___x_3090_) == 0)
{
lean_object* v_a_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3129_; 
v_a_3091_ = lean_ctor_get(v___x_3090_, 0);
v_isSharedCheck_3129_ = !lean_is_exclusive(v___x_3090_);
if (v_isSharedCheck_3129_ == 0)
{
v___x_3093_ = v___x_3090_;
v_isShared_3094_ = v_isSharedCheck_3129_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_a_3091_);
lean_dec(v___x_3090_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3129_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
if (lean_obj_tag(v_a_3091_) == 0)
{
uint8_t v_done_3095_; lean_object* v___x_3097_; 
lean_dec_ref(v_e_3063_);
lean_dec(v_a_3072_);
lean_dec_ref(v_a_3071_);
lean_dec(v_a_3070_);
lean_dec_ref(v_a_3069_);
lean_dec(v_a_3068_);
v_done_3095_ = lean_ctor_get_uint8(v_a_3091_, 0);
lean_dec_ref(v_a_3091_);
if (v_isShared_3089_ == 0)
{
v___x_3097_ = v___x_3088_;
goto v_reusejp_3096_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v_e_x27_3085_);
lean_ctor_set(v_reuseFailAlloc_3101_, 1, v_proof_3086_);
v___x_3097_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3096_;
}
v_reusejp_3096_:
{
lean_object* v___x_3099_; 
lean_ctor_set_uint8(v___x_3097_, sizeof(void*)*2, v_done_3095_);
if (v_isShared_3094_ == 0)
{
lean_ctor_set(v___x_3093_, 0, v___x_3097_);
v___x_3099_ = v___x_3093_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v___x_3097_);
v___x_3099_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
return v___x_3099_;
}
}
}
else
{
lean_object* v_e_x27_3102_; lean_object* v_proof_3103_; uint8_t v_done_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3128_; 
lean_del_object(v___x_3093_);
lean_del_object(v___x_3088_);
v_e_x27_3102_ = lean_ctor_get(v_a_3091_, 0);
v_proof_3103_ = lean_ctor_get(v_a_3091_, 1);
v_done_3104_ = lean_ctor_get_uint8(v_a_3091_, sizeof(void*)*2);
v_isSharedCheck_3128_ = !lean_is_exclusive(v_a_3091_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3106_ = v_a_3091_;
v_isShared_3107_ = v_isSharedCheck_3128_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_proof_3103_);
lean_inc(v_e_x27_3102_);
lean_dec(v_a_3091_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3128_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
lean_object* v___x_3108_; 
lean_inc_ref(v_e_x27_3102_);
v___x_3108_ = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(v_e_3063_, v_e_x27_3085_, v_proof_3086_, v_e_x27_3102_, v_proof_3103_, v_a_3068_, v_a_3069_, v_a_3070_, v_a_3071_, v_a_3072_);
lean_dec(v_a_3068_);
if (lean_obj_tag(v___x_3108_) == 0)
{
lean_object* v_a_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3119_; 
v_a_3109_ = lean_ctor_get(v___x_3108_, 0);
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_3108_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3111_ = v___x_3108_;
v_isShared_3112_ = v_isSharedCheck_3119_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_a_3109_);
lean_dec(v___x_3108_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3119_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
lean_object* v___x_3114_; 
if (v_isShared_3107_ == 0)
{
lean_ctor_set(v___x_3106_, 1, v_a_3109_);
v___x_3114_ = v___x_3106_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_e_x27_3102_);
lean_ctor_set(v_reuseFailAlloc_3118_, 1, v_a_3109_);
lean_ctor_set_uint8(v_reuseFailAlloc_3118_, sizeof(void*)*2, v_done_3104_);
v___x_3114_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
lean_object* v___x_3116_; 
if (v_isShared_3112_ == 0)
{
lean_ctor_set(v___x_3111_, 0, v___x_3114_);
v___x_3116_ = v___x_3111_;
goto v_reusejp_3115_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v___x_3114_);
v___x_3116_ = v_reuseFailAlloc_3117_;
goto v_reusejp_3115_;
}
v_reusejp_3115_:
{
return v___x_3116_;
}
}
}
}
else
{
lean_object* v_a_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3127_; 
lean_del_object(v___x_3106_);
lean_dec_ref(v_e_x27_3102_);
v_a_3120_ = lean_ctor_get(v___x_3108_, 0);
v_isSharedCheck_3127_ = !lean_is_exclusive(v___x_3108_);
if (v_isSharedCheck_3127_ == 0)
{
v___x_3122_ = v___x_3108_;
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_a_3120_);
lean_dec(v___x_3108_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
lean_object* v___x_3125_; 
if (v_isShared_3123_ == 0)
{
v___x_3125_ = v___x_3122_;
goto v_reusejp_3124_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v_a_3120_);
v___x_3125_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3124_;
}
v_reusejp_3124_:
{
return v___x_3125_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_3088_);
lean_dec_ref(v_proof_3086_);
lean_dec_ref(v_e_x27_3085_);
lean_dec_ref(v_e_3063_);
lean_dec(v_a_3072_);
lean_dec_ref(v_a_3071_);
lean_dec(v_a_3070_);
lean_dec_ref(v_a_3069_);
lean_dec(v_a_3068_);
return v___x_3090_;
}
}
}
else
{
lean_dec_ref(v_a_3080_);
lean_dec_ref(v_e_3063_);
lean_dec(v_a_3072_);
lean_dec_ref(v_a_3071_);
lean_dec(v_a_3070_);
lean_dec_ref(v_a_3069_);
lean_dec(v_a_3068_);
lean_dec_ref(v_a_3067_);
lean_dec(v_a_3066_);
lean_dec_ref(v_a_3065_);
lean_dec(v_a_3064_);
return v___x_3079_;
}
}
}
else
{
lean_dec_ref(v_e_3063_);
lean_dec(v_a_3072_);
lean_dec_ref(v_a_3071_);
lean_dec(v_a_3070_);
lean_dec_ref(v_a_3069_);
lean_dec(v_a_3068_);
lean_dec_ref(v_a_3067_);
lean_dec(v_a_3066_);
lean_dec_ref(v_a_3065_);
lean_dec(v_a_3064_);
return v___x_3079_;
}
}
case 5:
{
lean_object* v___x_3131_; 
lean_inc(v_a_3072_);
lean_inc_ref(v_a_3071_);
lean_inc(v_a_3070_);
lean_inc_ref(v_a_3069_);
lean_inc(v_a_3068_);
lean_inc_ref(v_a_3067_);
lean_inc(v_a_3066_);
lean_inc_ref(v_a_3065_);
lean_inc(v_a_3064_);
lean_inc_ref(v_e_3063_);
v___x_3131_ = l_Lean_Meta_Tactic_Cbv_tryMatcher(v_e_3063_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_, v_a_3070_, v_a_3071_, v_a_3072_);
if (lean_obj_tag(v___x_3131_) == 0)
{
lean_object* v_a_3132_; 
v_a_3132_ = lean_ctor_get(v___x_3131_, 0);
lean_inc(v_a_3132_);
if (lean_obj_tag(v_a_3132_) == 0)
{
uint8_t v_done_3133_; 
v_done_3133_ = lean_ctor_get_uint8(v_a_3132_, 0);
lean_dec_ref(v_a_3132_);
if (v_done_3133_ == 0)
{
lean_object* v___x_3134_; 
lean_dec_ref(v___x_3131_);
v___x_3134_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn(v_e_3063_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_, v_a_3070_, v_a_3071_, v_a_3072_);
return v___x_3134_;
}
else
{
lean_dec_ref(v_e_3063_);
lean_dec(v_a_3072_);
lean_dec_ref(v_a_3071_);
lean_dec(v_a_3070_);
lean_dec_ref(v_a_3069_);
lean_dec(v_a_3068_);
lean_dec_ref(v_a_3067_);
lean_dec(v_a_3066_);
lean_dec_ref(v_a_3065_);
lean_dec(v_a_3064_);
return v___x_3131_;
}
}
else
{
lean_dec_ref(v_a_3132_);
lean_dec_ref(v_e_3063_);
lean_dec(v_a_3072_);
lean_dec_ref(v_a_3071_);
lean_dec(v_a_3070_);
lean_dec_ref(v_a_3069_);
lean_dec(v_a_3068_);
lean_dec_ref(v_a_3067_);
lean_dec(v_a_3066_);
lean_dec_ref(v_a_3065_);
lean_dec(v_a_3064_);
return v___x_3131_;
}
}
else
{
lean_dec_ref(v_e_3063_);
lean_dec(v_a_3072_);
lean_dec_ref(v_a_3071_);
lean_dec(v_a_3070_);
lean_dec_ref(v_a_3069_);
lean_dec(v_a_3068_);
lean_dec_ref(v_a_3067_);
lean_dec(v_a_3066_);
lean_dec_ref(v_a_3065_);
lean_dec(v_a_3064_);
return v___x_3131_;
}
}
case 8:
{
uint8_t v___x_3135_; 
lean_dec(v_a_3066_);
lean_dec_ref(v_a_3065_);
lean_dec(v_a_3064_);
v___x_3135_ = l_Lean_Expr_letNondep_x21(v_e_3063_);
if (v___x_3135_ == 0)
{
lean_object* v___x_3136_; 
lean_dec_ref(v_a_3067_);
v___x_3136_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg(v_e_3063_, v_a_3068_, v_a_3069_, v_a_3070_, v_a_3071_, v_a_3072_);
lean_dec(v_a_3068_);
return v___x_3136_;
}
else
{
lean_object* v___x_3137_; 
v___x_3137_ = l_Lean_Meta_Sym_Simp_toBetaApp(v_e_3063_, v_a_3067_, v_a_3068_, v_a_3069_, v_a_3070_, v_a_3071_, v_a_3072_);
if (lean_obj_tag(v___x_3137_) == 0)
{
lean_object* v_a_3138_; lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3149_; 
v_a_3138_ = lean_ctor_get(v___x_3137_, 0);
v_isSharedCheck_3149_ = !lean_is_exclusive(v___x_3137_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3140_ = v___x_3137_;
v_isShared_3141_ = v_isSharedCheck_3149_;
goto v_resetjp_3139_;
}
else
{
lean_inc(v_a_3138_);
lean_dec(v___x_3137_);
v___x_3140_ = lean_box(0);
v_isShared_3141_ = v_isSharedCheck_3149_;
goto v_resetjp_3139_;
}
v_resetjp_3139_:
{
lean_object* v_e_3142_; lean_object* v_h_3143_; uint8_t v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3147_; 
v_e_3142_ = lean_ctor_get(v_a_3138_, 2);
lean_inc_ref(v_e_3142_);
v_h_3143_ = lean_ctor_get(v_a_3138_, 3);
lean_inc_ref(v_h_3143_);
lean_dec(v_a_3138_);
v___x_3144_ = 0;
v___x_3145_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_3145_, 0, v_e_3142_);
lean_ctor_set(v___x_3145_, 1, v_h_3143_);
lean_ctor_set_uint8(v___x_3145_, sizeof(void*)*2, v___x_3144_);
if (v_isShared_3141_ == 0)
{
lean_ctor_set(v___x_3140_, 0, v___x_3145_);
v___x_3147_ = v___x_3140_;
goto v_reusejp_3146_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v___x_3145_);
v___x_3147_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3146_;
}
v_reusejp_3146_:
{
return v___x_3147_;
}
}
}
else
{
lean_object* v_a_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3157_; 
v_a_3150_ = lean_ctor_get(v___x_3137_, 0);
v_isSharedCheck_3157_ = !lean_is_exclusive(v___x_3137_);
if (v_isSharedCheck_3157_ == 0)
{
v___x_3152_ = v___x_3137_;
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_a_3150_);
lean_dec(v___x_3137_);
v___x_3152_ = lean_box(0);
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
v_resetjp_3151_:
{
lean_object* v___x_3155_; 
if (v_isShared_3153_ == 0)
{
v___x_3155_ = v___x_3152_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v_a_3150_);
v___x_3155_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
return v___x_3155_;
}
}
}
}
}
case 7:
{
lean_dec_ref(v_e_3063_);
lean_dec(v_a_3072_);
lean_dec_ref(v_a_3071_);
lean_dec(v_a_3070_);
lean_dec_ref(v_a_3069_);
lean_dec(v_a_3068_);
lean_dec_ref(v_a_3067_);
lean_dec(v_a_3066_);
lean_dec_ref(v_a_3065_);
lean_dec(v_a_3064_);
goto v___jp_3074_;
}
case 6:
{
lean_dec_ref(v_e_3063_);
lean_dec(v_a_3072_);
lean_dec_ref(v_a_3071_);
lean_dec(v_a_3070_);
lean_dec_ref(v_a_3069_);
lean_dec(v_a_3068_);
lean_dec_ref(v_a_3067_);
lean_dec(v_a_3066_);
lean_dec_ref(v_a_3065_);
lean_dec(v_a_3064_);
goto v___jp_3074_;
}
case 1:
{
lean_object* v___x_3158_; lean_object* v___x_3159_; 
lean_dec_ref(v_e_3063_);
lean_dec(v_a_3072_);
lean_dec_ref(v_a_3071_);
lean_dec(v_a_3070_);
lean_dec_ref(v_a_3069_);
lean_dec(v_a_3068_);
lean_dec_ref(v_a_3067_);
lean_dec(v_a_3066_);
lean_dec_ref(v_a_3065_);
lean_dec(v_a_3064_);
v___x_3158_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__0));
v___x_3159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3159_, 0, v___x_3158_);
return v___x_3159_;
}
case 2:
{
lean_object* v___x_3160_; lean_object* v___x_3161_; 
lean_dec_ref(v_e_3063_);
lean_dec(v_a_3072_);
lean_dec_ref(v_a_3071_);
lean_dec(v_a_3070_);
lean_dec_ref(v_a_3069_);
lean_dec(v_a_3068_);
lean_dec_ref(v_a_3067_);
lean_dec(v_a_3066_);
lean_dec_ref(v_a_3065_);
lean_dec(v_a_3064_);
v___x_3160_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__0));
v___x_3161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3161_, 0, v___x_3160_);
return v___x_3161_;
}
case 0:
{
lean_object* v___x_3162_; lean_object* v___x_3163_; 
lean_dec_ref(v_e_3063_);
lean_dec(v_a_3072_);
lean_dec_ref(v_a_3071_);
lean_dec(v_a_3070_);
lean_dec_ref(v_a_3069_);
lean_dec(v_a_3068_);
lean_dec_ref(v_a_3067_);
lean_dec(v_a_3066_);
lean_dec_ref(v_a_3065_);
lean_dec(v_a_3064_);
v___x_3162_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__0));
v___x_3163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3163_, 0, v___x_3162_);
return v___x_3163_;
}
case 3:
{
lean_object* v___x_3164_; lean_object* v___x_3165_; 
lean_dec_ref(v_e_3063_);
lean_dec(v_a_3072_);
lean_dec_ref(v_a_3071_);
lean_dec(v_a_3070_);
lean_dec_ref(v_a_3069_);
lean_dec(v_a_3068_);
lean_dec_ref(v_a_3067_);
lean_dec(v_a_3066_);
lean_dec_ref(v_a_3065_);
lean_dec(v_a_3064_);
v___x_3164_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__0));
v___x_3165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3165_, 0, v___x_3164_);
return v___x_3165_;
}
default: 
{
lean_object* v___x_3166_; lean_object* v___x_3167_; 
lean_dec(v_a_3072_);
lean_dec_ref(v_a_3071_);
lean_dec(v_a_3070_);
lean_dec_ref(v_a_3069_);
lean_dec(v_a_3068_);
lean_dec_ref(v_a_3067_);
lean_dec(v_a_3066_);
lean_dec_ref(v_a_3065_);
lean_dec(v_a_3064_);
lean_dec_ref(v_e_3063_);
v___x_3166_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__9));
v___x_3167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3167_, 0, v___x_3166_);
return v___x_3167_;
}
}
v___jp_3074_:
{
lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3075_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__0));
v___x_3076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3076_, 0, v___x_3075_);
return v___x_3076_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___boxed(lean_object* v_e_3168_, lean_object* v_a_3169_, lean_object* v_a_3170_, lean_object* v_a_3171_, lean_object* v_a_3172_, lean_object* v_a_3173_, lean_object* v_a_3174_, lean_object* v_a_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_, lean_object* v_a_3178_){
_start:
{
lean_object* v_res_3179_; 
v_res_3179_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep(v_e_3168_, v_a_3169_, v_a_3170_, v_a_3171_, v_a_3172_, v_a_3173_, v_a_3174_, v_a_3175_, v_a_3176_, v_a_3177_);
return v_res_3179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPre(lean_object* v_simprocs_3180_, lean_object* v_a_3181_, lean_object* v_a_3182_, lean_object* v_a_3183_, lean_object* v_a_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_){
_start:
{
lean_object* v___x_3192_; 
lean_inc_ref(v_a_3181_);
v___x_3192_ = l_Lean_Meta_Tactic_Cbv_isBuiltinValue___redArg(v_a_3181_);
if (lean_obj_tag(v___x_3192_) == 0)
{
lean_object* v_a_3193_; 
v_a_3193_ = lean_ctor_get(v___x_3192_, 0);
lean_inc(v_a_3193_);
if (lean_obj_tag(v_a_3193_) == 0)
{
uint8_t v_done_3194_; 
v_done_3194_ = lean_ctor_get_uint8(v_a_3193_, 0);
lean_dec_ref(v_a_3193_);
if (v_done_3194_ == 0)
{
lean_object* v___x_3195_; 
lean_dec_ref(v___x_3192_);
lean_inc(v_a_3190_);
lean_inc_ref(v_a_3189_);
lean_inc(v_a_3188_);
lean_inc_ref(v_a_3187_);
lean_inc_ref(v_a_3181_);
v___x_3195_ = l_Lean_Meta_Tactic_Cbv_isProofTerm___redArg(v_a_3181_, v_a_3185_, v_a_3186_, v_a_3187_, v_a_3188_, v_a_3189_, v_a_3190_);
if (lean_obj_tag(v___x_3195_) == 0)
{
lean_object* v_a_3196_; 
v_a_3196_ = lean_ctor_get(v___x_3195_, 0);
lean_inc(v_a_3196_);
if (lean_obj_tag(v_a_3196_) == 0)
{
uint8_t v_done_3197_; 
v_done_3197_ = lean_ctor_get_uint8(v_a_3196_, 0);
lean_dec_ref(v_a_3196_);
if (v_done_3197_ == 0)
{
lean_object* v_pre_3198_; lean_object* v_erased_3199_; lean_object* v___x_3200_; 
lean_dec_ref(v___x_3195_);
v_pre_3198_ = lean_ctor_get(v_simprocs_3180_, 0);
lean_inc_ref(v_pre_3198_);
v_erased_3199_ = lean_ctor_get(v_simprocs_3180_, 4);
lean_inc_ref(v_erased_3199_);
lean_dec_ref(v_simprocs_3180_);
lean_inc(v_a_3190_);
lean_inc_ref(v_a_3189_);
lean_inc(v_a_3188_);
lean_inc_ref(v_a_3187_);
lean_inc(v_a_3186_);
lean_inc_ref(v_a_3185_);
lean_inc(v_a_3184_);
lean_inc_ref(v_a_3183_);
lean_inc(v_a_3182_);
lean_inc_ref(v_a_3181_);
v___x_3200_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch(v_pre_3198_, v_erased_3199_, v_a_3181_, v_a_3182_, v_a_3183_, v_a_3184_, v_a_3185_, v_a_3186_, v_a_3187_, v_a_3188_, v_a_3189_, v_a_3190_);
if (lean_obj_tag(v___x_3200_) == 0)
{
lean_object* v_a_3201_; 
v_a_3201_ = lean_ctor_get(v___x_3200_, 0);
lean_inc(v_a_3201_);
if (lean_obj_tag(v_a_3201_) == 0)
{
uint8_t v_done_3202_; 
v_done_3202_ = lean_ctor_get_uint8(v_a_3201_, 0);
lean_dec_ref(v_a_3201_);
if (v_done_3202_ == 0)
{
lean_object* v___x_3203_; 
lean_dec_ref(v___x_3200_);
v___x_3203_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep(v_a_3181_, v_a_3182_, v_a_3183_, v_a_3184_, v_a_3185_, v_a_3186_, v_a_3187_, v_a_3188_, v_a_3189_, v_a_3190_);
return v___x_3203_;
}
else
{
lean_dec(v_a_3190_);
lean_dec_ref(v_a_3189_);
lean_dec(v_a_3188_);
lean_dec_ref(v_a_3187_);
lean_dec(v_a_3186_);
lean_dec_ref(v_a_3185_);
lean_dec(v_a_3184_);
lean_dec_ref(v_a_3183_);
lean_dec(v_a_3182_);
lean_dec_ref(v_a_3181_);
return v___x_3200_;
}
}
else
{
lean_dec_ref(v_a_3201_);
lean_dec(v_a_3190_);
lean_dec_ref(v_a_3189_);
lean_dec(v_a_3188_);
lean_dec_ref(v_a_3187_);
lean_dec(v_a_3186_);
lean_dec_ref(v_a_3185_);
lean_dec(v_a_3184_);
lean_dec_ref(v_a_3183_);
lean_dec(v_a_3182_);
lean_dec_ref(v_a_3181_);
return v___x_3200_;
}
}
else
{
lean_dec(v_a_3190_);
lean_dec_ref(v_a_3189_);
lean_dec(v_a_3188_);
lean_dec_ref(v_a_3187_);
lean_dec(v_a_3186_);
lean_dec_ref(v_a_3185_);
lean_dec(v_a_3184_);
lean_dec_ref(v_a_3183_);
lean_dec(v_a_3182_);
lean_dec_ref(v_a_3181_);
return v___x_3200_;
}
}
else
{
lean_dec(v_a_3190_);
lean_dec_ref(v_a_3189_);
lean_dec(v_a_3188_);
lean_dec_ref(v_a_3187_);
lean_dec(v_a_3186_);
lean_dec_ref(v_a_3185_);
lean_dec(v_a_3184_);
lean_dec_ref(v_a_3183_);
lean_dec(v_a_3182_);
lean_dec_ref(v_a_3181_);
lean_dec_ref(v_simprocs_3180_);
return v___x_3195_;
}
}
else
{
lean_dec_ref(v_a_3196_);
lean_dec(v_a_3190_);
lean_dec_ref(v_a_3189_);
lean_dec(v_a_3188_);
lean_dec_ref(v_a_3187_);
lean_dec(v_a_3186_);
lean_dec_ref(v_a_3185_);
lean_dec(v_a_3184_);
lean_dec_ref(v_a_3183_);
lean_dec(v_a_3182_);
lean_dec_ref(v_a_3181_);
lean_dec_ref(v_simprocs_3180_);
return v___x_3195_;
}
}
else
{
lean_dec(v_a_3190_);
lean_dec_ref(v_a_3189_);
lean_dec(v_a_3188_);
lean_dec_ref(v_a_3187_);
lean_dec(v_a_3186_);
lean_dec_ref(v_a_3185_);
lean_dec(v_a_3184_);
lean_dec_ref(v_a_3183_);
lean_dec(v_a_3182_);
lean_dec_ref(v_a_3181_);
lean_dec_ref(v_simprocs_3180_);
return v___x_3195_;
}
}
else
{
lean_dec(v_a_3190_);
lean_dec_ref(v_a_3189_);
lean_dec(v_a_3188_);
lean_dec_ref(v_a_3187_);
lean_dec(v_a_3186_);
lean_dec_ref(v_a_3185_);
lean_dec(v_a_3184_);
lean_dec_ref(v_a_3183_);
lean_dec(v_a_3182_);
lean_dec_ref(v_a_3181_);
lean_dec_ref(v_simprocs_3180_);
return v___x_3192_;
}
}
else
{
lean_dec_ref(v_a_3193_);
lean_dec(v_a_3190_);
lean_dec_ref(v_a_3189_);
lean_dec(v_a_3188_);
lean_dec_ref(v_a_3187_);
lean_dec(v_a_3186_);
lean_dec_ref(v_a_3185_);
lean_dec(v_a_3184_);
lean_dec_ref(v_a_3183_);
lean_dec(v_a_3182_);
lean_dec_ref(v_a_3181_);
lean_dec_ref(v_simprocs_3180_);
return v___x_3192_;
}
}
else
{
lean_dec(v_a_3190_);
lean_dec_ref(v_a_3189_);
lean_dec(v_a_3188_);
lean_dec_ref(v_a_3187_);
lean_dec(v_a_3186_);
lean_dec_ref(v_a_3185_);
lean_dec(v_a_3184_);
lean_dec_ref(v_a_3183_);
lean_dec(v_a_3182_);
lean_dec_ref(v_a_3181_);
lean_dec_ref(v_simprocs_3180_);
return v___x_3192_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPre___boxed(lean_object* v_simprocs_3204_, lean_object* v_a_3205_, lean_object* v_a_3206_, lean_object* v_a_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_, lean_object* v_a_3215_){
_start:
{
lean_object* v_res_3216_; 
v_res_3216_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPre(v_simprocs_3204_, v_a_3205_, v_a_3206_, v_a_3207_, v_a_3208_, v_a_3209_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_);
return v_res_3216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPost(lean_object* v_simprocs_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_, lean_object* v_a_3227_){
_start:
{
lean_object* v___x_3229_; lean_object* v___x_3230_; 
v___x_3229_ = lean_unsigned_to_nat(255u);
lean_inc(v_a_3227_);
lean_inc_ref(v_a_3226_);
lean_inc(v_a_3225_);
lean_inc_ref(v_a_3224_);
lean_inc_ref(v_a_3218_);
v___x_3230_ = l_Lean_Meta_Sym_Simp_evalGround___redArg(v___x_3229_, v_a_3218_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_);
if (lean_obj_tag(v___x_3230_) == 0)
{
lean_object* v_a_3231_; 
v_a_3231_ = lean_ctor_get(v___x_3230_, 0);
lean_inc(v_a_3231_);
if (lean_obj_tag(v_a_3231_) == 0)
{
uint8_t v_done_3232_; 
v_done_3232_ = lean_ctor_get_uint8(v_a_3231_, 0);
lean_dec_ref(v_a_3231_);
if (v_done_3232_ == 0)
{
lean_object* v_eval_3233_; lean_object* v_post_3234_; lean_object* v_erased_3235_; lean_object* v___x_3236_; 
lean_dec_ref(v___x_3230_);
v_eval_3233_ = lean_ctor_get(v_simprocs_3217_, 1);
lean_inc_ref(v_eval_3233_);
v_post_3234_ = lean_ctor_get(v_simprocs_3217_, 2);
lean_inc_ref(v_post_3234_);
v_erased_3235_ = lean_ctor_get(v_simprocs_3217_, 4);
lean_inc_ref(v_erased_3235_);
lean_dec_ref(v_simprocs_3217_);
lean_inc(v_a_3227_);
lean_inc_ref(v_a_3226_);
lean_inc(v_a_3225_);
lean_inc_ref(v_a_3224_);
lean_inc(v_a_3223_);
lean_inc_ref(v_a_3222_);
lean_inc(v_a_3221_);
lean_inc_ref(v_a_3220_);
lean_inc(v_a_3219_);
lean_inc_ref(v_a_3218_);
lean_inc_ref(v_erased_3235_);
v___x_3236_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch(v_eval_3233_, v_erased_3235_, v_a_3218_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_);
if (lean_obj_tag(v___x_3236_) == 0)
{
lean_object* v_a_3237_; 
v_a_3237_ = lean_ctor_get(v___x_3236_, 0);
lean_inc(v_a_3237_);
if (lean_obj_tag(v_a_3237_) == 0)
{
uint8_t v_done_3238_; 
v_done_3238_ = lean_ctor_get_uint8(v_a_3237_, 0);
lean_dec_ref(v_a_3237_);
if (v_done_3238_ == 0)
{
lean_object* v___x_3239_; 
lean_dec_ref(v___x_3236_);
lean_inc(v_a_3227_);
lean_inc_ref(v_a_3226_);
lean_inc(v_a_3225_);
lean_inc_ref(v_a_3224_);
lean_inc(v_a_3223_);
lean_inc_ref(v_a_3222_);
lean_inc(v_a_3221_);
lean_inc_ref(v_a_3220_);
lean_inc(v_a_3219_);
lean_inc_ref(v_a_3218_);
v___x_3239_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp(v_a_3218_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_);
if (lean_obj_tag(v___x_3239_) == 0)
{
lean_object* v_a_3240_; 
v_a_3240_ = lean_ctor_get(v___x_3239_, 0);
lean_inc(v_a_3240_);
if (lean_obj_tag(v_a_3240_) == 0)
{
uint8_t v_done_3241_; 
v_done_3241_ = lean_ctor_get_uint8(v_a_3240_, 0);
lean_dec_ref(v_a_3240_);
if (v_done_3241_ == 0)
{
lean_object* v___x_3242_; 
lean_dec_ref(v___x_3239_);
v___x_3242_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch(v_post_3234_, v_erased_3235_, v_a_3218_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_);
return v___x_3242_;
}
else
{
lean_dec_ref(v_erased_3235_);
lean_dec_ref(v_post_3234_);
lean_dec(v_a_3227_);
lean_dec_ref(v_a_3226_);
lean_dec(v_a_3225_);
lean_dec_ref(v_a_3224_);
lean_dec(v_a_3223_);
lean_dec_ref(v_a_3222_);
lean_dec(v_a_3221_);
lean_dec_ref(v_a_3220_);
lean_dec(v_a_3219_);
lean_dec_ref(v_a_3218_);
return v___x_3239_;
}
}
else
{
lean_dec_ref(v_a_3240_);
lean_dec_ref(v_erased_3235_);
lean_dec_ref(v_post_3234_);
lean_dec(v_a_3227_);
lean_dec_ref(v_a_3226_);
lean_dec(v_a_3225_);
lean_dec_ref(v_a_3224_);
lean_dec(v_a_3223_);
lean_dec_ref(v_a_3222_);
lean_dec(v_a_3221_);
lean_dec_ref(v_a_3220_);
lean_dec(v_a_3219_);
lean_dec_ref(v_a_3218_);
return v___x_3239_;
}
}
else
{
lean_dec_ref(v_erased_3235_);
lean_dec_ref(v_post_3234_);
lean_dec(v_a_3227_);
lean_dec_ref(v_a_3226_);
lean_dec(v_a_3225_);
lean_dec_ref(v_a_3224_);
lean_dec(v_a_3223_);
lean_dec_ref(v_a_3222_);
lean_dec(v_a_3221_);
lean_dec_ref(v_a_3220_);
lean_dec(v_a_3219_);
lean_dec_ref(v_a_3218_);
return v___x_3239_;
}
}
else
{
lean_dec_ref(v_erased_3235_);
lean_dec_ref(v_post_3234_);
lean_dec(v_a_3227_);
lean_dec_ref(v_a_3226_);
lean_dec(v_a_3225_);
lean_dec_ref(v_a_3224_);
lean_dec(v_a_3223_);
lean_dec_ref(v_a_3222_);
lean_dec(v_a_3221_);
lean_dec_ref(v_a_3220_);
lean_dec(v_a_3219_);
lean_dec_ref(v_a_3218_);
return v___x_3236_;
}
}
else
{
lean_dec_ref(v_a_3237_);
lean_dec_ref(v_erased_3235_);
lean_dec_ref(v_post_3234_);
lean_dec(v_a_3227_);
lean_dec_ref(v_a_3226_);
lean_dec(v_a_3225_);
lean_dec_ref(v_a_3224_);
lean_dec(v_a_3223_);
lean_dec_ref(v_a_3222_);
lean_dec(v_a_3221_);
lean_dec_ref(v_a_3220_);
lean_dec(v_a_3219_);
lean_dec_ref(v_a_3218_);
return v___x_3236_;
}
}
else
{
lean_dec_ref(v_erased_3235_);
lean_dec_ref(v_post_3234_);
lean_dec(v_a_3227_);
lean_dec_ref(v_a_3226_);
lean_dec(v_a_3225_);
lean_dec_ref(v_a_3224_);
lean_dec(v_a_3223_);
lean_dec_ref(v_a_3222_);
lean_dec(v_a_3221_);
lean_dec_ref(v_a_3220_);
lean_dec(v_a_3219_);
lean_dec_ref(v_a_3218_);
return v___x_3236_;
}
}
else
{
lean_dec(v_a_3227_);
lean_dec_ref(v_a_3226_);
lean_dec(v_a_3225_);
lean_dec_ref(v_a_3224_);
lean_dec(v_a_3223_);
lean_dec_ref(v_a_3222_);
lean_dec(v_a_3221_);
lean_dec_ref(v_a_3220_);
lean_dec(v_a_3219_);
lean_dec_ref(v_a_3218_);
lean_dec_ref(v_simprocs_3217_);
return v___x_3230_;
}
}
else
{
lean_dec_ref(v_a_3231_);
lean_dec(v_a_3227_);
lean_dec_ref(v_a_3226_);
lean_dec(v_a_3225_);
lean_dec_ref(v_a_3224_);
lean_dec(v_a_3223_);
lean_dec_ref(v_a_3222_);
lean_dec(v_a_3221_);
lean_dec_ref(v_a_3220_);
lean_dec(v_a_3219_);
lean_dec_ref(v_a_3218_);
lean_dec_ref(v_simprocs_3217_);
return v___x_3230_;
}
}
else
{
lean_dec(v_a_3227_);
lean_dec_ref(v_a_3226_);
lean_dec(v_a_3225_);
lean_dec_ref(v_a_3224_);
lean_dec(v_a_3223_);
lean_dec_ref(v_a_3222_);
lean_dec(v_a_3221_);
lean_dec_ref(v_a_3220_);
lean_dec(v_a_3219_);
lean_dec_ref(v_a_3218_);
lean_dec_ref(v_simprocs_3217_);
return v___x_3230_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPost___boxed(lean_object* v_simprocs_3243_, lean_object* v_a_3244_, lean_object* v_a_3245_, lean_object* v_a_3246_, lean_object* v_a_3247_, lean_object* v_a_3248_, lean_object* v_a_3249_, lean_object* v_a_3250_, lean_object* v_a_3251_, lean_object* v_a_3252_, lean_object* v_a_3253_, lean_object* v_a_3254_){
_start:
{
lean_object* v_res_3255_; 
v_res_3255_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPost(v_simprocs_3243_, v_a_3244_, v_a_3245_, v_a_3246_, v_a_3247_, v_a_3248_, v_a_3249_, v_a_3250_, v_a_3251_, v_a_3252_, v_a_3253_);
return v_res_3255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(lean_object* v_simprocs_3256_){
_start:
{
lean_object* v___x_3257_; lean_object* v___x_3258_; uint8_t v___x_3259_; lean_object* v___x_3260_; 
lean_inc_ref(v_simprocs_3256_);
v___x_3257_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPre___boxed), 12, 1);
lean_closure_set(v___x_3257_, 0, v_simprocs_3256_);
v___x_3258_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPost___boxed), 12, 1);
lean_closure_set(v___x_3258_, 0, v_simprocs_3256_);
v___x_3259_ = 1;
v___x_3260_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3260_, 0, v___x_3257_);
lean_ctor_set(v___x_3260_, 1, v___x_3258_);
lean_ctor_set_uint8(v___x_3260_, sizeof(void*)*2, v___x_3259_);
return v___x_3260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(lean_object* v_e_3261_, lean_object* v_config_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_, lean_object* v_a_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_){
_start:
{
lean_object* v___x_3270_; 
v___x_3270_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_3268_);
if (lean_obj_tag(v___x_3270_) == 0)
{
lean_object* v_a_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; 
v_a_3271_ = lean_ctor_get(v___x_3270_, 0);
lean_inc(v_a_3271_);
lean_dec_ref(v___x_3270_);
v___x_3272_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(v_a_3271_);
v___x_3273_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_3273_, 0, v_e_3261_);
v___x_3274_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v___x_3273_, v___x_3272_, v_config_3262_, v_a_3263_, v_a_3264_, v_a_3265_, v_a_3266_, v_a_3267_, v_a_3268_);
return v___x_3274_;
}
else
{
lean_object* v_a_3275_; lean_object* v___x_3277_; uint8_t v_isShared_3278_; uint8_t v_isSharedCheck_3282_; 
lean_dec(v_a_3268_);
lean_dec_ref(v_a_3267_);
lean_dec(v_a_3266_);
lean_dec_ref(v_a_3265_);
lean_dec(v_a_3264_);
lean_dec_ref(v_a_3263_);
lean_dec_ref(v_config_3262_);
lean_dec_ref(v_e_3261_);
v_a_3275_ = lean_ctor_get(v___x_3270_, 0);
v_isSharedCheck_3282_ = !lean_is_exclusive(v___x_3270_);
if (v_isSharedCheck_3282_ == 0)
{
v___x_3277_ = v___x_3270_;
v_isShared_3278_ = v_isSharedCheck_3282_;
goto v_resetjp_3276_;
}
else
{
lean_inc(v_a_3275_);
lean_dec(v___x_3270_);
v___x_3277_ = lean_box(0);
v_isShared_3278_ = v_isSharedCheck_3282_;
goto v_resetjp_3276_;
}
v_resetjp_3276_:
{
lean_object* v___x_3280_; 
if (v_isShared_3278_ == 0)
{
v___x_3280_ = v___x_3277_;
goto v_reusejp_3279_;
}
else
{
lean_object* v_reuseFailAlloc_3281_; 
v_reuseFailAlloc_3281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3281_, 0, v_a_3275_);
v___x_3280_ = v_reuseFailAlloc_3281_;
goto v_reusejp_3279_;
}
v_reusejp_3279_:
{
return v___x_3280_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore___boxed(lean_object* v_e_3283_, lean_object* v_config_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_, lean_object* v_a_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_){
_start:
{
lean_object* v_res_3292_; 
v_res_3292_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v_e_3283_, v_config_3284_, v_a_3285_, v_a_3286_, v_a_3287_, v_a_3288_, v_a_3289_, v_a_3290_);
return v_res_3292_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg(lean_object* v_cls_3293_, lean_object* v___y_3294_){
_start:
{
lean_object* v_options_3296_; uint8_t v_hasTrace_3297_; 
v_options_3296_ = lean_ctor_get(v___y_3294_, 2);
v_hasTrace_3297_ = lean_ctor_get_uint8(v_options_3296_, sizeof(void*)*1);
if (v_hasTrace_3297_ == 0)
{
lean_object* v___x_3298_; lean_object* v___x_3299_; 
lean_dec(v_cls_3293_);
v___x_3298_ = lean_box(v_hasTrace_3297_);
v___x_3299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3299_, 0, v___x_3298_);
return v___x_3299_;
}
else
{
lean_object* v_inheritedTraceOptions_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; uint8_t v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; 
v_inheritedTraceOptions_3300_ = lean_ctor_get(v___y_3294_, 13);
v___x_3301_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__1));
v___x_3302_ = l_Lean_Name_append(v___x_3301_, v_cls_3293_);
v___x_3303_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3300_, v_options_3296_, v___x_3302_);
lean_dec(v___x_3302_);
v___x_3304_ = lean_box(v___x_3303_);
v___x_3305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3305_, 0, v___x_3304_);
return v___x_3305_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg___boxed(lean_object* v_cls_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_){
_start:
{
lean_object* v_res_3309_; 
v_res_3309_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg(v_cls_3306_, v___y_3307_);
lean_dec_ref(v___y_3307_);
return v_res_3309_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0(lean_object* v_cls_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_){
_start:
{
lean_object* v___x_3316_; 
v___x_3316_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg(v_cls_3310_, v___y_3313_);
return v___x_3316_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___boxed(lean_object* v_cls_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_){
_start:
{
lean_object* v_res_3323_; 
v_res_3323_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0(v_cls_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_);
lean_dec(v___y_3321_);
lean_dec_ref(v___y_3320_);
lean_dec(v___y_3319_);
lean_dec_ref(v___y_3318_);
return v_res_3323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1___redArg(lean_object* v___y_3324_){
_start:
{
lean_object* v___x_3326_; lean_object* v_traceState_3327_; lean_object* v_traces_3328_; lean_object* v___x_3329_; lean_object* v_traceState_3330_; lean_object* v_env_3331_; lean_object* v_nextMacroScope_3332_; lean_object* v_ngen_3333_; lean_object* v_auxDeclNGen_3334_; lean_object* v_cache_3335_; lean_object* v_messages_3336_; lean_object* v_infoState_3337_; lean_object* v_snapshotTasks_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3359_; 
v___x_3326_ = lean_st_ref_get(v___y_3324_);
v_traceState_3327_ = lean_ctor_get(v___x_3326_, 4);
lean_inc_ref(v_traceState_3327_);
lean_dec(v___x_3326_);
v_traces_3328_ = lean_ctor_get(v_traceState_3327_, 0);
lean_inc_ref(v_traces_3328_);
lean_dec_ref(v_traceState_3327_);
v___x_3329_ = lean_st_ref_take(v___y_3324_);
v_traceState_3330_ = lean_ctor_get(v___x_3329_, 4);
v_env_3331_ = lean_ctor_get(v___x_3329_, 0);
v_nextMacroScope_3332_ = lean_ctor_get(v___x_3329_, 1);
v_ngen_3333_ = lean_ctor_get(v___x_3329_, 2);
v_auxDeclNGen_3334_ = lean_ctor_get(v___x_3329_, 3);
v_cache_3335_ = lean_ctor_get(v___x_3329_, 5);
v_messages_3336_ = lean_ctor_get(v___x_3329_, 6);
v_infoState_3337_ = lean_ctor_get(v___x_3329_, 7);
v_snapshotTasks_3338_ = lean_ctor_get(v___x_3329_, 8);
v_isSharedCheck_3359_ = !lean_is_exclusive(v___x_3329_);
if (v_isSharedCheck_3359_ == 0)
{
v___x_3340_ = v___x_3329_;
v_isShared_3341_ = v_isSharedCheck_3359_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_snapshotTasks_3338_);
lean_inc(v_infoState_3337_);
lean_inc(v_messages_3336_);
lean_inc(v_cache_3335_);
lean_inc(v_traceState_3330_);
lean_inc(v_auxDeclNGen_3334_);
lean_inc(v_ngen_3333_);
lean_inc(v_nextMacroScope_3332_);
lean_inc(v_env_3331_);
lean_dec(v___x_3329_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3359_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
uint64_t v_tid_3342_; lean_object* v___x_3344_; uint8_t v_isShared_3345_; uint8_t v_isSharedCheck_3357_; 
v_tid_3342_ = lean_ctor_get_uint64(v_traceState_3330_, sizeof(void*)*1);
v_isSharedCheck_3357_ = !lean_is_exclusive(v_traceState_3330_);
if (v_isSharedCheck_3357_ == 0)
{
lean_object* v_unused_3358_; 
v_unused_3358_ = lean_ctor_get(v_traceState_3330_, 0);
lean_dec(v_unused_3358_);
v___x_3344_ = v_traceState_3330_;
v_isShared_3345_ = v_isSharedCheck_3357_;
goto v_resetjp_3343_;
}
else
{
lean_dec(v_traceState_3330_);
v___x_3344_ = lean_box(0);
v_isShared_3345_ = v_isSharedCheck_3357_;
goto v_resetjp_3343_;
}
v_resetjp_3343_:
{
lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3350_; 
v___x_3346_ = lean_unsigned_to_nat(32u);
v___x_3347_ = lean_mk_empty_array_with_capacity(v___x_3346_);
lean_dec_ref(v___x_3347_);
v___x_3348_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___redArg___closed__1);
if (v_isShared_3345_ == 0)
{
lean_ctor_set(v___x_3344_, 0, v___x_3348_);
v___x_3350_ = v___x_3344_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v___x_3348_);
lean_ctor_set_uint64(v_reuseFailAlloc_3356_, sizeof(void*)*1, v_tid_3342_);
v___x_3350_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
lean_object* v___x_3352_; 
if (v_isShared_3341_ == 0)
{
lean_ctor_set(v___x_3340_, 4, v___x_3350_);
v___x_3352_ = v___x_3340_;
goto v_reusejp_3351_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v_env_3331_);
lean_ctor_set(v_reuseFailAlloc_3355_, 1, v_nextMacroScope_3332_);
lean_ctor_set(v_reuseFailAlloc_3355_, 2, v_ngen_3333_);
lean_ctor_set(v_reuseFailAlloc_3355_, 3, v_auxDeclNGen_3334_);
lean_ctor_set(v_reuseFailAlloc_3355_, 4, v___x_3350_);
lean_ctor_set(v_reuseFailAlloc_3355_, 5, v_cache_3335_);
lean_ctor_set(v_reuseFailAlloc_3355_, 6, v_messages_3336_);
lean_ctor_set(v_reuseFailAlloc_3355_, 7, v_infoState_3337_);
lean_ctor_set(v_reuseFailAlloc_3355_, 8, v_snapshotTasks_3338_);
v___x_3352_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3351_;
}
v_reusejp_3351_:
{
lean_object* v___x_3353_; lean_object* v___x_3354_; 
v___x_3353_ = lean_st_ref_set(v___y_3324_, v___x_3352_);
v___x_3354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3354_, 0, v_traces_3328_);
return v___x_3354_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1___redArg___boxed(lean_object* v___y_3360_, lean_object* v___y_3361_){
_start:
{
lean_object* v_res_3362_; 
v_res_3362_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1___redArg(v___y_3360_);
lean_dec(v___y_3360_);
return v_res_3362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1(lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_){
_start:
{
lean_object* v___x_3368_; 
v___x_3368_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1___redArg(v___y_3366_);
return v___x_3368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1___boxed(lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_){
_start:
{
lean_object* v_res_3374_; 
v_res_3374_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1(v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_);
lean_dec(v___y_3372_);
lean_dec_ref(v___y_3371_);
lean_dec(v___y_3370_);
lean_dec_ref(v___y_3369_);
return v_res_3374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0(lean_object* v_a_3375_, lean_object* v___x_3376_, lean_object* v___x_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_){
_start:
{
lean_object* v___x_3385_; 
v___x_3385_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_3375_, v___y_3379_);
if (lean_obj_tag(v___x_3385_) == 0)
{
lean_object* v_a_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; 
v_a_3386_ = lean_ctor_get(v___x_3385_, 0);
lean_inc(v_a_3386_);
lean_dec_ref(v___x_3385_);
v___x_3387_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_3387_, 0, v_a_3386_);
v___x_3388_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v___x_3387_, v___x_3376_, v___x_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_);
return v___x_3388_;
}
else
{
lean_object* v_a_3389_; lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3396_; 
lean_dec(v___y_3383_);
lean_dec_ref(v___y_3382_);
lean_dec(v___y_3381_);
lean_dec_ref(v___y_3380_);
lean_dec(v___y_3379_);
lean_dec_ref(v___y_3378_);
lean_dec_ref(v___x_3377_);
lean_dec_ref(v___x_3376_);
v_a_3389_ = lean_ctor_get(v___x_3385_, 0);
v_isSharedCheck_3396_ = !lean_is_exclusive(v___x_3385_);
if (v_isSharedCheck_3396_ == 0)
{
v___x_3391_ = v___x_3385_;
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
else
{
lean_inc(v_a_3389_);
lean_dec(v___x_3385_);
v___x_3391_ = lean_box(0);
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
v_resetjp_3390_:
{
lean_object* v___x_3394_; 
if (v_isShared_3392_ == 0)
{
v___x_3394_ = v___x_3391_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v_a_3389_);
v___x_3394_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
return v___x_3394_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___boxed(lean_object* v_a_3397_, lean_object* v___x_3398_, lean_object* v___x_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_){
_start:
{
lean_object* v_res_3407_; 
v_res_3407_ = l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0(v_a_3397_, v___x_3398_, v___x_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_);
return v_res_3407_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___x_3409_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__0));
v___x_3410_ = l_Lean_stringToMessageData(v___x_3409_);
return v___x_3410_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3412_; lean_object* v___x_3413_; 
v___x_3412_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__2));
v___x_3413_ = l_Lean_stringToMessageData(v___x_3412_);
return v___x_3413_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__5(void){
_start:
{
lean_object* v___x_3415_; lean_object* v___x_3416_; 
v___x_3415_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__4));
v___x_3416_ = l_Lean_stringToMessageData(v___x_3415_);
return v___x_3416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1(lean_object* v_e_3417_, lean_object* v_x_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_){
_start:
{
if (lean_obj_tag(v_x_3418_) == 0)
{
lean_object* v_a_3424_; lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3434_; 
lean_dec_ref(v_e_3417_);
v_a_3424_ = lean_ctor_get(v_x_3418_, 0);
v_isSharedCheck_3434_ = !lean_is_exclusive(v_x_3418_);
if (v_isSharedCheck_3434_ == 0)
{
v___x_3426_ = v_x_3418_;
v_isShared_3427_ = v_isSharedCheck_3434_;
goto v_resetjp_3425_;
}
else
{
lean_inc(v_a_3424_);
lean_dec(v_x_3418_);
v___x_3426_ = lean_box(0);
v_isShared_3427_ = v_isSharedCheck_3434_;
goto v_resetjp_3425_;
}
v_resetjp_3425_:
{
lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3432_; 
v___x_3428_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__1);
v___x_3429_ = l_Lean_Exception_toMessageData(v_a_3424_);
v___x_3430_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3430_, 0, v___x_3428_);
lean_ctor_set(v___x_3430_, 1, v___x_3429_);
if (v_isShared_3427_ == 0)
{
lean_ctor_set(v___x_3426_, 0, v___x_3430_);
v___x_3432_ = v___x_3426_;
goto v_reusejp_3431_;
}
else
{
lean_object* v_reuseFailAlloc_3433_; 
v_reuseFailAlloc_3433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3433_, 0, v___x_3430_);
v___x_3432_ = v_reuseFailAlloc_3433_;
goto v_reusejp_3431_;
}
v_reusejp_3431_:
{
return v___x_3432_;
}
}
}
else
{
lean_object* v_a_3435_; lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3456_; 
v_a_3435_ = lean_ctor_get(v_x_3418_, 0);
v_isSharedCheck_3456_ = !lean_is_exclusive(v_x_3418_);
if (v_isSharedCheck_3456_ == 0)
{
v___x_3437_ = v_x_3418_;
v_isShared_3438_ = v_isSharedCheck_3456_;
goto v_resetjp_3436_;
}
else
{
lean_inc(v_a_3435_);
lean_dec(v_x_3418_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3456_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
if (lean_obj_tag(v_a_3435_) == 0)
{
lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3443_; 
lean_dec_ref(v_a_3435_);
v___x_3439_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__3, &l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__3);
v___x_3440_ = l_Lean_indentExpr(v_e_3417_);
v___x_3441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3441_, 0, v___x_3439_);
lean_ctor_set(v___x_3441_, 1, v___x_3440_);
if (v_isShared_3438_ == 0)
{
lean_ctor_set_tag(v___x_3437_, 0);
lean_ctor_set(v___x_3437_, 0, v___x_3441_);
v___x_3443_ = v___x_3437_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v___x_3441_);
v___x_3443_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
return v___x_3443_;
}
}
else
{
lean_object* v_e_x27_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3454_; 
v_e_x27_3445_ = lean_ctor_get(v_a_3435_, 0);
lean_inc_ref(v_e_x27_3445_);
lean_dec_ref(v_a_3435_);
v___x_3446_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__5, &l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__5_once, _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__5);
v___x_3447_ = l_Lean_indentExpr(v_e_3417_);
v___x_3448_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3448_, 0, v___x_3446_);
lean_ctor_set(v___x_3448_, 1, v___x_3447_);
v___x_3449_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7);
v___x_3450_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3450_, 0, v___x_3448_);
lean_ctor_set(v___x_3450_, 1, v___x_3449_);
v___x_3451_ = l_Lean_indentExpr(v_e_x27_3445_);
v___x_3452_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3452_, 0, v___x_3450_);
lean_ctor_set(v___x_3452_, 1, v___x_3451_);
if (v_isShared_3438_ == 0)
{
lean_ctor_set_tag(v___x_3437_, 0);
lean_ctor_set(v___x_3437_, 0, v___x_3452_);
v___x_3454_ = v___x_3437_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v___x_3452_);
v___x_3454_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3453_;
}
v_reusejp_3453_:
{
return v___x_3454_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___boxed(lean_object* v_e_3457_, lean_object* v_x_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_){
_start:
{
lean_object* v_res_3464_; 
v_res_3464_ = l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1(v_e_3457_, v_x_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_);
lean_dec(v___y_3462_);
lean_dec_ref(v___y_3461_);
lean_dec(v___y_3460_);
lean_dec_ref(v___y_3459_);
return v_res_3464_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__2_spec__3___redArg(lean_object* v_x_3465_){
_start:
{
if (lean_obj_tag(v_x_3465_) == 0)
{
lean_object* v_a_3467_; lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3474_; 
v_a_3467_ = lean_ctor_get(v_x_3465_, 0);
v_isSharedCheck_3474_ = !lean_is_exclusive(v_x_3465_);
if (v_isSharedCheck_3474_ == 0)
{
v___x_3469_ = v_x_3465_;
v_isShared_3470_ = v_isSharedCheck_3474_;
goto v_resetjp_3468_;
}
else
{
lean_inc(v_a_3467_);
lean_dec(v_x_3465_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3474_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
lean_object* v___x_3472_; 
if (v_isShared_3470_ == 0)
{
lean_ctor_set_tag(v___x_3469_, 1);
v___x_3472_ = v___x_3469_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v_a_3467_);
v___x_3472_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
return v___x_3472_;
}
}
}
else
{
lean_object* v_a_3475_; lean_object* v___x_3477_; uint8_t v_isShared_3478_; uint8_t v_isSharedCheck_3482_; 
v_a_3475_ = lean_ctor_get(v_x_3465_, 0);
v_isSharedCheck_3482_ = !lean_is_exclusive(v_x_3465_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3477_ = v_x_3465_;
v_isShared_3478_ = v_isSharedCheck_3482_;
goto v_resetjp_3476_;
}
else
{
lean_inc(v_a_3475_);
lean_dec(v_x_3465_);
v___x_3477_ = lean_box(0);
v_isShared_3478_ = v_isSharedCheck_3482_;
goto v_resetjp_3476_;
}
v_resetjp_3476_:
{
lean_object* v___x_3480_; 
if (v_isShared_3478_ == 0)
{
lean_ctor_set_tag(v___x_3477_, 0);
v___x_3480_ = v___x_3477_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v_a_3475_);
v___x_3480_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
return v___x_3480_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__2_spec__3___redArg___boxed(lean_object* v_x_3483_, lean_object* v___y_3484_){
_start:
{
lean_object* v_res_3485_; 
v_res_3485_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__2_spec__3___redArg(v_x_3483_);
return v_res_3485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__2_spec__2(lean_object* v_oldTraces_3486_, lean_object* v_data_3487_, lean_object* v_ref_3488_, lean_object* v_msg_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_){
_start:
{
lean_object* v_fileName_3495_; lean_object* v_fileMap_3496_; lean_object* v_options_3497_; lean_object* v_currRecDepth_3498_; lean_object* v_maxRecDepth_3499_; lean_object* v_ref_3500_; lean_object* v_currNamespace_3501_; lean_object* v_openDecls_3502_; lean_object* v_initHeartbeats_3503_; lean_object* v_maxHeartbeats_3504_; lean_object* v_quotContext_3505_; lean_object* v_currMacroScope_3506_; uint8_t v_diag_3507_; lean_object* v_cancelTk_x3f_3508_; uint8_t v_suppressElabErrors_3509_; lean_object* v_inheritedTraceOptions_3510_; lean_object* v___x_3512_; uint8_t v_isShared_3513_; uint8_t v_isSharedCheck_3565_; 
v_fileName_3495_ = lean_ctor_get(v___y_3492_, 0);
v_fileMap_3496_ = lean_ctor_get(v___y_3492_, 1);
v_options_3497_ = lean_ctor_get(v___y_3492_, 2);
v_currRecDepth_3498_ = lean_ctor_get(v___y_3492_, 3);
v_maxRecDepth_3499_ = lean_ctor_get(v___y_3492_, 4);
v_ref_3500_ = lean_ctor_get(v___y_3492_, 5);
v_currNamespace_3501_ = lean_ctor_get(v___y_3492_, 6);
v_openDecls_3502_ = lean_ctor_get(v___y_3492_, 7);
v_initHeartbeats_3503_ = lean_ctor_get(v___y_3492_, 8);
v_maxHeartbeats_3504_ = lean_ctor_get(v___y_3492_, 9);
v_quotContext_3505_ = lean_ctor_get(v___y_3492_, 10);
v_currMacroScope_3506_ = lean_ctor_get(v___y_3492_, 11);
v_diag_3507_ = lean_ctor_get_uint8(v___y_3492_, sizeof(void*)*14);
v_cancelTk_x3f_3508_ = lean_ctor_get(v___y_3492_, 12);
v_suppressElabErrors_3509_ = lean_ctor_get_uint8(v___y_3492_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3510_ = lean_ctor_get(v___y_3492_, 13);
v_isSharedCheck_3565_ = !lean_is_exclusive(v___y_3492_);
if (v_isSharedCheck_3565_ == 0)
{
v___x_3512_ = v___y_3492_;
v_isShared_3513_ = v_isSharedCheck_3565_;
goto v_resetjp_3511_;
}
else
{
lean_inc(v_inheritedTraceOptions_3510_);
lean_inc(v_cancelTk_x3f_3508_);
lean_inc(v_currMacroScope_3506_);
lean_inc(v_quotContext_3505_);
lean_inc(v_maxHeartbeats_3504_);
lean_inc(v_initHeartbeats_3503_);
lean_inc(v_openDecls_3502_);
lean_inc(v_currNamespace_3501_);
lean_inc(v_ref_3500_);
lean_inc(v_maxRecDepth_3499_);
lean_inc(v_currRecDepth_3498_);
lean_inc(v_options_3497_);
lean_inc(v_fileMap_3496_);
lean_inc(v_fileName_3495_);
lean_dec(v___y_3492_);
v___x_3512_ = lean_box(0);
v_isShared_3513_ = v_isSharedCheck_3565_;
goto v_resetjp_3511_;
}
v_resetjp_3511_:
{
lean_object* v___x_3514_; lean_object* v_traceState_3515_; lean_object* v_traces_3516_; lean_object* v_ref_3517_; lean_object* v___x_3519_; 
v___x_3514_ = lean_st_ref_get(v___y_3493_);
v_traceState_3515_ = lean_ctor_get(v___x_3514_, 4);
lean_inc_ref(v_traceState_3515_);
lean_dec(v___x_3514_);
v_traces_3516_ = lean_ctor_get(v_traceState_3515_, 0);
lean_inc_ref(v_traces_3516_);
lean_dec_ref(v_traceState_3515_);
v_ref_3517_ = l_Lean_replaceRef(v_ref_3488_, v_ref_3500_);
lean_dec(v_ref_3500_);
if (v_isShared_3513_ == 0)
{
lean_ctor_set(v___x_3512_, 5, v_ref_3517_);
v___x_3519_ = v___x_3512_;
goto v_reusejp_3518_;
}
else
{
lean_object* v_reuseFailAlloc_3564_; 
v_reuseFailAlloc_3564_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_3564_, 0, v_fileName_3495_);
lean_ctor_set(v_reuseFailAlloc_3564_, 1, v_fileMap_3496_);
lean_ctor_set(v_reuseFailAlloc_3564_, 2, v_options_3497_);
lean_ctor_set(v_reuseFailAlloc_3564_, 3, v_currRecDepth_3498_);
lean_ctor_set(v_reuseFailAlloc_3564_, 4, v_maxRecDepth_3499_);
lean_ctor_set(v_reuseFailAlloc_3564_, 5, v_ref_3517_);
lean_ctor_set(v_reuseFailAlloc_3564_, 6, v_currNamespace_3501_);
lean_ctor_set(v_reuseFailAlloc_3564_, 7, v_openDecls_3502_);
lean_ctor_set(v_reuseFailAlloc_3564_, 8, v_initHeartbeats_3503_);
lean_ctor_set(v_reuseFailAlloc_3564_, 9, v_maxHeartbeats_3504_);
lean_ctor_set(v_reuseFailAlloc_3564_, 10, v_quotContext_3505_);
lean_ctor_set(v_reuseFailAlloc_3564_, 11, v_currMacroScope_3506_);
lean_ctor_set(v_reuseFailAlloc_3564_, 12, v_cancelTk_x3f_3508_);
lean_ctor_set(v_reuseFailAlloc_3564_, 13, v_inheritedTraceOptions_3510_);
lean_ctor_set_uint8(v_reuseFailAlloc_3564_, sizeof(void*)*14, v_diag_3507_);
lean_ctor_set_uint8(v_reuseFailAlloc_3564_, sizeof(void*)*14 + 1, v_suppressElabErrors_3509_);
v___x_3519_ = v_reuseFailAlloc_3564_;
goto v_reusejp_3518_;
}
v_reusejp_3518_:
{
lean_object* v___x_3520_; size_t v_sz_3521_; size_t v___x_3522_; lean_object* v___x_3523_; lean_object* v_msg_3524_; lean_object* v___x_3525_; lean_object* v_a_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3563_; 
v___x_3520_ = l_Lean_PersistentArray_toArray___redArg(v_traces_3516_);
lean_dec_ref(v_traces_3516_);
v_sz_3521_ = lean_array_size(v___x_3520_);
v___x_3522_ = ((size_t)0ULL);
v___x_3523_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__4_spec__5(v_sz_3521_, v___x_3522_, v___x_3520_);
v_msg_3524_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_3524_, 0, v_data_3487_);
lean_ctor_set(v_msg_3524_, 1, v_msg_3489_);
lean_ctor_set(v_msg_3524_, 2, v___x_3523_);
v___x_3525_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1_spec__1(v_msg_3524_, v___y_3490_, v___y_3491_, v___x_3519_, v___y_3493_);
lean_dec_ref(v___x_3519_);
v_a_3526_ = lean_ctor_get(v___x_3525_, 0);
v_isSharedCheck_3563_ = !lean_is_exclusive(v___x_3525_);
if (v_isSharedCheck_3563_ == 0)
{
v___x_3528_ = v___x_3525_;
v_isShared_3529_ = v_isSharedCheck_3563_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_a_3526_);
lean_dec(v___x_3525_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3563_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v___x_3530_; lean_object* v_traceState_3531_; lean_object* v_env_3532_; lean_object* v_nextMacroScope_3533_; lean_object* v_ngen_3534_; lean_object* v_auxDeclNGen_3535_; lean_object* v_cache_3536_; lean_object* v_messages_3537_; lean_object* v_infoState_3538_; lean_object* v_snapshotTasks_3539_; lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3562_; 
v___x_3530_ = lean_st_ref_take(v___y_3493_);
v_traceState_3531_ = lean_ctor_get(v___x_3530_, 4);
v_env_3532_ = lean_ctor_get(v___x_3530_, 0);
v_nextMacroScope_3533_ = lean_ctor_get(v___x_3530_, 1);
v_ngen_3534_ = lean_ctor_get(v___x_3530_, 2);
v_auxDeclNGen_3535_ = lean_ctor_get(v___x_3530_, 3);
v_cache_3536_ = lean_ctor_get(v___x_3530_, 5);
v_messages_3537_ = lean_ctor_get(v___x_3530_, 6);
v_infoState_3538_ = lean_ctor_get(v___x_3530_, 7);
v_snapshotTasks_3539_ = lean_ctor_get(v___x_3530_, 8);
v_isSharedCheck_3562_ = !lean_is_exclusive(v___x_3530_);
if (v_isSharedCheck_3562_ == 0)
{
v___x_3541_ = v___x_3530_;
v_isShared_3542_ = v_isSharedCheck_3562_;
goto v_resetjp_3540_;
}
else
{
lean_inc(v_snapshotTasks_3539_);
lean_inc(v_infoState_3538_);
lean_inc(v_messages_3537_);
lean_inc(v_cache_3536_);
lean_inc(v_traceState_3531_);
lean_inc(v_auxDeclNGen_3535_);
lean_inc(v_ngen_3534_);
lean_inc(v_nextMacroScope_3533_);
lean_inc(v_env_3532_);
lean_dec(v___x_3530_);
v___x_3541_ = lean_box(0);
v_isShared_3542_ = v_isSharedCheck_3562_;
goto v_resetjp_3540_;
}
v_resetjp_3540_:
{
uint64_t v_tid_3543_; lean_object* v___x_3545_; uint8_t v_isShared_3546_; uint8_t v_isSharedCheck_3560_; 
v_tid_3543_ = lean_ctor_get_uint64(v_traceState_3531_, sizeof(void*)*1);
v_isSharedCheck_3560_ = !lean_is_exclusive(v_traceState_3531_);
if (v_isSharedCheck_3560_ == 0)
{
lean_object* v_unused_3561_; 
v_unused_3561_ = lean_ctor_get(v_traceState_3531_, 0);
lean_dec(v_unused_3561_);
v___x_3545_ = v_traceState_3531_;
v_isShared_3546_ = v_isSharedCheck_3560_;
goto v_resetjp_3544_;
}
else
{
lean_dec(v_traceState_3531_);
v___x_3545_ = lean_box(0);
v_isShared_3546_ = v_isSharedCheck_3560_;
goto v_resetjp_3544_;
}
v_resetjp_3544_:
{
lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3550_; 
v___x_3547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3547_, 0, v_ref_3488_);
lean_ctor_set(v___x_3547_, 1, v_a_3526_);
v___x_3548_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_3486_, v___x_3547_);
if (v_isShared_3546_ == 0)
{
lean_ctor_set(v___x_3545_, 0, v___x_3548_);
v___x_3550_ = v___x_3545_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v___x_3548_);
lean_ctor_set_uint64(v_reuseFailAlloc_3559_, sizeof(void*)*1, v_tid_3543_);
v___x_3550_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
lean_object* v___x_3552_; 
if (v_isShared_3542_ == 0)
{
lean_ctor_set(v___x_3541_, 4, v___x_3550_);
v___x_3552_ = v___x_3541_;
goto v_reusejp_3551_;
}
else
{
lean_object* v_reuseFailAlloc_3558_; 
v_reuseFailAlloc_3558_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3558_, 0, v_env_3532_);
lean_ctor_set(v_reuseFailAlloc_3558_, 1, v_nextMacroScope_3533_);
lean_ctor_set(v_reuseFailAlloc_3558_, 2, v_ngen_3534_);
lean_ctor_set(v_reuseFailAlloc_3558_, 3, v_auxDeclNGen_3535_);
lean_ctor_set(v_reuseFailAlloc_3558_, 4, v___x_3550_);
lean_ctor_set(v_reuseFailAlloc_3558_, 5, v_cache_3536_);
lean_ctor_set(v_reuseFailAlloc_3558_, 6, v_messages_3537_);
lean_ctor_set(v_reuseFailAlloc_3558_, 7, v_infoState_3538_);
lean_ctor_set(v_reuseFailAlloc_3558_, 8, v_snapshotTasks_3539_);
v___x_3552_ = v_reuseFailAlloc_3558_;
goto v_reusejp_3551_;
}
v_reusejp_3551_:
{
lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3556_; 
v___x_3553_ = lean_st_ref_set(v___y_3493_, v___x_3552_);
v___x_3554_ = lean_box(0);
if (v_isShared_3529_ == 0)
{
lean_ctor_set(v___x_3528_, 0, v___x_3554_);
v___x_3556_ = v___x_3528_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v___x_3554_);
v___x_3556_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
return v___x_3556_;
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__2_spec__2___boxed(lean_object* v_oldTraces_3566_, lean_object* v_data_3567_, lean_object* v_ref_3568_, lean_object* v_msg_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_){
_start:
{
lean_object* v_res_3575_; 
v_res_3575_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__2_spec__2(v_oldTraces_3566_, v_data_3567_, v_ref_3568_, v_msg_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_);
lean_dec(v___y_3573_);
lean_dec(v___y_3571_);
lean_dec_ref(v___y_3570_);
return v_res_3575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__2(lean_object* v_cls_3576_, uint8_t v_collapsed_3577_, lean_object* v_tag_3578_, lean_object* v_opts_3579_, uint8_t v_clsEnabled_3580_, lean_object* v_oldTraces_3581_, lean_object* v_msg_3582_, lean_object* v_resStartStop_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_){
_start:
{
lean_object* v_fst_3589_; lean_object* v_snd_3590_; lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3688_; 
v_fst_3589_ = lean_ctor_get(v_resStartStop_3583_, 0);
v_snd_3590_ = lean_ctor_get(v_resStartStop_3583_, 1);
v_isSharedCheck_3688_ = !lean_is_exclusive(v_resStartStop_3583_);
if (v_isSharedCheck_3688_ == 0)
{
v___x_3592_ = v_resStartStop_3583_;
v_isShared_3593_ = v_isSharedCheck_3688_;
goto v_resetjp_3591_;
}
else
{
lean_inc(v_snd_3590_);
lean_inc(v_fst_3589_);
lean_dec(v_resStartStop_3583_);
v___x_3592_ = lean_box(0);
v_isShared_3593_ = v_isSharedCheck_3688_;
goto v_resetjp_3591_;
}
v_resetjp_3591_:
{
lean_object* v___y_3595_; lean_object* v___y_3596_; lean_object* v_data_3597_; lean_object* v_fst_3608_; lean_object* v_snd_3609_; lean_object* v___x_3611_; uint8_t v_isShared_3612_; uint8_t v_isSharedCheck_3687_; 
v_fst_3608_ = lean_ctor_get(v_snd_3590_, 0);
v_snd_3609_ = lean_ctor_get(v_snd_3590_, 1);
v_isSharedCheck_3687_ = !lean_is_exclusive(v_snd_3590_);
if (v_isSharedCheck_3687_ == 0)
{
v___x_3611_ = v_snd_3590_;
v_isShared_3612_ = v_isSharedCheck_3687_;
goto v_resetjp_3610_;
}
else
{
lean_inc(v_snd_3609_);
lean_inc(v_fst_3608_);
lean_dec(v_snd_3590_);
v___x_3611_ = lean_box(0);
v_isShared_3612_ = v_isSharedCheck_3687_;
goto v_resetjp_3610_;
}
v___jp_3594_:
{
lean_object* v___x_3598_; 
v___x_3598_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__2_spec__2(v_oldTraces_3581_, v_data_3597_, v___y_3595_, v___y_3596_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_);
lean_dec(v___y_3587_);
lean_dec(v___y_3585_);
lean_dec_ref(v___y_3584_);
if (lean_obj_tag(v___x_3598_) == 0)
{
lean_object* v___x_3599_; 
lean_dec_ref(v___x_3598_);
v___x_3599_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__2_spec__3___redArg(v_fst_3589_);
return v___x_3599_;
}
else
{
lean_object* v_a_3600_; lean_object* v___x_3602_; uint8_t v_isShared_3603_; uint8_t v_isSharedCheck_3607_; 
lean_dec(v_fst_3589_);
v_a_3600_ = lean_ctor_get(v___x_3598_, 0);
v_isSharedCheck_3607_ = !lean_is_exclusive(v___x_3598_);
if (v_isSharedCheck_3607_ == 0)
{
v___x_3602_ = v___x_3598_;
v_isShared_3603_ = v_isSharedCheck_3607_;
goto v_resetjp_3601_;
}
else
{
lean_inc(v_a_3600_);
lean_dec(v___x_3598_);
v___x_3602_ = lean_box(0);
v_isShared_3603_ = v_isSharedCheck_3607_;
goto v_resetjp_3601_;
}
v_resetjp_3601_:
{
lean_object* v___x_3605_; 
if (v_isShared_3603_ == 0)
{
v___x_3605_ = v___x_3602_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3606_; 
v_reuseFailAlloc_3606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3606_, 0, v_a_3600_);
v___x_3605_ = v_reuseFailAlloc_3606_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
return v___x_3605_;
}
}
}
}
v_resetjp_3610_:
{
lean_object* v___x_3613_; uint8_t v___x_3614_; lean_object* v___y_3616_; lean_object* v_a_3617_; uint8_t v___y_3641_; double v___y_3672_; 
v___x_3613_ = l_Lean_trace_profiler;
v___x_3614_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2(v_opts_3579_, v___x_3613_);
if (v___x_3614_ == 0)
{
v___y_3641_ = v___x_3614_;
goto v___jp_3640_;
}
else
{
lean_object* v___x_3677_; uint8_t v___x_3678_; 
v___x_3677_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3678_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2(v_opts_3579_, v___x_3677_);
if (v___x_3678_ == 0)
{
lean_object* v___x_3679_; lean_object* v___x_3680_; double v___x_3681_; double v___x_3682_; double v___x_3683_; 
v___x_3679_ = l_Lean_trace_profiler_threshold;
v___x_3680_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__6(v_opts_3579_, v___x_3679_);
v___x_3681_ = lean_float_of_nat(v___x_3680_);
v___x_3682_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__4);
v___x_3683_ = lean_float_div(v___x_3681_, v___x_3682_);
v___y_3672_ = v___x_3683_;
goto v___jp_3671_;
}
else
{
lean_object* v___x_3684_; lean_object* v___x_3685_; double v___x_3686_; 
v___x_3684_ = l_Lean_trace_profiler_threshold;
v___x_3685_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__6(v_opts_3579_, v___x_3684_);
v___x_3686_ = lean_float_of_nat(v___x_3685_);
v___y_3672_ = v___x_3686_;
goto v___jp_3671_;
}
}
v___jp_3615_:
{
uint8_t v_result_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3623_; 
v_result_3618_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__3(v_fst_3589_);
v___x_3619_ = l_Lean_TraceResult_toEmoji(v_result_3618_);
v___x_3620_ = l_Lean_stringToMessageData(v___x_3619_);
v___x_3621_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__1);
if (v_isShared_3612_ == 0)
{
lean_ctor_set_tag(v___x_3611_, 7);
lean_ctor_set(v___x_3611_, 1, v___x_3621_);
lean_ctor_set(v___x_3611_, 0, v___x_3620_);
v___x_3623_ = v___x_3611_;
goto v_reusejp_3622_;
}
else
{
lean_object* v_reuseFailAlloc_3634_; 
v_reuseFailAlloc_3634_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3634_, 0, v___x_3620_);
lean_ctor_set(v_reuseFailAlloc_3634_, 1, v___x_3621_);
v___x_3623_ = v_reuseFailAlloc_3634_;
goto v_reusejp_3622_;
}
v_reusejp_3622_:
{
lean_object* v_m_3625_; 
if (v_isShared_3593_ == 0)
{
lean_ctor_set_tag(v___x_3592_, 7);
lean_ctor_set(v___x_3592_, 1, v_a_3617_);
lean_ctor_set(v___x_3592_, 0, v___x_3623_);
v_m_3625_ = v___x_3592_;
goto v_reusejp_3624_;
}
else
{
lean_object* v_reuseFailAlloc_3633_; 
v_reuseFailAlloc_3633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3633_, 0, v___x_3623_);
lean_ctor_set(v_reuseFailAlloc_3633_, 1, v_a_3617_);
v_m_3625_ = v_reuseFailAlloc_3633_;
goto v_reusejp_3624_;
}
v_reusejp_3624_:
{
lean_object* v___x_3626_; lean_object* v___x_3627_; double v___x_3628_; lean_object* v_data_3629_; 
v___x_3626_ = lean_box(v_result_3618_);
v___x_3627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3627_, 0, v___x_3626_);
v___x_3628_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__0);
lean_inc_ref(v_tag_3578_);
lean_inc_ref(v___x_3627_);
lean_inc(v_cls_3576_);
v_data_3629_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3629_, 0, v_cls_3576_);
lean_ctor_set(v_data_3629_, 1, v___x_3627_);
lean_ctor_set(v_data_3629_, 2, v_tag_3578_);
lean_ctor_set_float(v_data_3629_, sizeof(void*)*3, v___x_3628_);
lean_ctor_set_float(v_data_3629_, sizeof(void*)*3 + 8, v___x_3628_);
lean_ctor_set_uint8(v_data_3629_, sizeof(void*)*3 + 16, v_collapsed_3577_);
if (v___x_3614_ == 0)
{
lean_dec_ref(v___x_3627_);
lean_dec(v_snd_3609_);
lean_dec(v_fst_3608_);
lean_dec_ref(v_tag_3578_);
lean_dec(v_cls_3576_);
v___y_3595_ = v___y_3616_;
v___y_3596_ = v_m_3625_;
v_data_3597_ = v_data_3629_;
goto v___jp_3594_;
}
else
{
lean_object* v_data_3630_; double v___x_3631_; double v___x_3632_; 
lean_dec_ref(v_data_3629_);
v_data_3630_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3630_, 0, v_cls_3576_);
lean_ctor_set(v_data_3630_, 1, v___x_3627_);
lean_ctor_set(v_data_3630_, 2, v_tag_3578_);
v___x_3631_ = lean_unbox_float(v_fst_3608_);
lean_dec(v_fst_3608_);
lean_ctor_set_float(v_data_3630_, sizeof(void*)*3, v___x_3631_);
v___x_3632_ = lean_unbox_float(v_snd_3609_);
lean_dec(v_snd_3609_);
lean_ctor_set_float(v_data_3630_, sizeof(void*)*3 + 8, v___x_3632_);
lean_ctor_set_uint8(v_data_3630_, sizeof(void*)*3 + 16, v_collapsed_3577_);
v___y_3595_ = v___y_3616_;
v___y_3596_ = v_m_3625_;
v_data_3597_ = v_data_3630_;
goto v___jp_3594_;
}
}
}
}
v___jp_3635_:
{
lean_object* v_ref_3636_; lean_object* v___x_3637_; 
v_ref_3636_ = lean_ctor_get(v___y_3586_, 5);
lean_inc(v___y_3587_);
lean_inc_ref(v___y_3586_);
lean_inc(v___y_3585_);
lean_inc_ref(v___y_3584_);
lean_inc(v_fst_3589_);
v___x_3637_ = lean_apply_6(v_msg_3582_, v_fst_3589_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_, lean_box(0));
if (lean_obj_tag(v___x_3637_) == 0)
{
lean_object* v_a_3638_; 
v_a_3638_ = lean_ctor_get(v___x_3637_, 0);
lean_inc(v_a_3638_);
lean_dec_ref(v___x_3637_);
lean_inc(v_ref_3636_);
v___y_3616_ = v_ref_3636_;
v_a_3617_ = v_a_3638_;
goto v___jp_3615_;
}
else
{
lean_object* v___x_3639_; 
lean_dec_ref(v___x_3637_);
v___x_3639_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__3);
lean_inc(v_ref_3636_);
v___y_3616_ = v_ref_3636_;
v_a_3617_ = v___x_3639_;
goto v___jp_3615_;
}
}
v___jp_3640_:
{
if (v_clsEnabled_3580_ == 0)
{
if (v___y_3641_ == 0)
{
lean_object* v___x_3642_; lean_object* v_traceState_3643_; lean_object* v_env_3644_; lean_object* v_nextMacroScope_3645_; lean_object* v_ngen_3646_; lean_object* v_auxDeclNGen_3647_; lean_object* v_cache_3648_; lean_object* v_messages_3649_; lean_object* v_infoState_3650_; lean_object* v_snapshotTasks_3651_; lean_object* v___x_3653_; uint8_t v_isShared_3654_; uint8_t v_isSharedCheck_3670_; 
lean_del_object(v___x_3611_);
lean_dec(v_snd_3609_);
lean_dec(v_fst_3608_);
lean_del_object(v___x_3592_);
lean_dec_ref(v___y_3586_);
lean_dec(v___y_3585_);
lean_dec_ref(v___y_3584_);
lean_dec_ref(v_msg_3582_);
lean_dec_ref(v_tag_3578_);
lean_dec(v_cls_3576_);
v___x_3642_ = lean_st_ref_take(v___y_3587_);
v_traceState_3643_ = lean_ctor_get(v___x_3642_, 4);
v_env_3644_ = lean_ctor_get(v___x_3642_, 0);
v_nextMacroScope_3645_ = lean_ctor_get(v___x_3642_, 1);
v_ngen_3646_ = lean_ctor_get(v___x_3642_, 2);
v_auxDeclNGen_3647_ = lean_ctor_get(v___x_3642_, 3);
v_cache_3648_ = lean_ctor_get(v___x_3642_, 5);
v_messages_3649_ = lean_ctor_get(v___x_3642_, 6);
v_infoState_3650_ = lean_ctor_get(v___x_3642_, 7);
v_snapshotTasks_3651_ = lean_ctor_get(v___x_3642_, 8);
v_isSharedCheck_3670_ = !lean_is_exclusive(v___x_3642_);
if (v_isSharedCheck_3670_ == 0)
{
v___x_3653_ = v___x_3642_;
v_isShared_3654_ = v_isSharedCheck_3670_;
goto v_resetjp_3652_;
}
else
{
lean_inc(v_snapshotTasks_3651_);
lean_inc(v_infoState_3650_);
lean_inc(v_messages_3649_);
lean_inc(v_cache_3648_);
lean_inc(v_traceState_3643_);
lean_inc(v_auxDeclNGen_3647_);
lean_inc(v_ngen_3646_);
lean_inc(v_nextMacroScope_3645_);
lean_inc(v_env_3644_);
lean_dec(v___x_3642_);
v___x_3653_ = lean_box(0);
v_isShared_3654_ = v_isSharedCheck_3670_;
goto v_resetjp_3652_;
}
v_resetjp_3652_:
{
uint64_t v_tid_3655_; lean_object* v_traces_3656_; lean_object* v___x_3658_; uint8_t v_isShared_3659_; uint8_t v_isSharedCheck_3669_; 
v_tid_3655_ = lean_ctor_get_uint64(v_traceState_3643_, sizeof(void*)*1);
v_traces_3656_ = lean_ctor_get(v_traceState_3643_, 0);
v_isSharedCheck_3669_ = !lean_is_exclusive(v_traceState_3643_);
if (v_isSharedCheck_3669_ == 0)
{
v___x_3658_ = v_traceState_3643_;
v_isShared_3659_ = v_isSharedCheck_3669_;
goto v_resetjp_3657_;
}
else
{
lean_inc(v_traces_3656_);
lean_dec(v_traceState_3643_);
v___x_3658_ = lean_box(0);
v_isShared_3659_ = v_isSharedCheck_3669_;
goto v_resetjp_3657_;
}
v_resetjp_3657_:
{
lean_object* v___x_3660_; lean_object* v___x_3662_; 
v___x_3660_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3581_, v_traces_3656_);
lean_dec_ref(v_traces_3656_);
if (v_isShared_3659_ == 0)
{
lean_ctor_set(v___x_3658_, 0, v___x_3660_);
v___x_3662_ = v___x_3658_;
goto v_reusejp_3661_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v___x_3660_);
lean_ctor_set_uint64(v_reuseFailAlloc_3668_, sizeof(void*)*1, v_tid_3655_);
v___x_3662_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3661_;
}
v_reusejp_3661_:
{
lean_object* v___x_3664_; 
if (v_isShared_3654_ == 0)
{
lean_ctor_set(v___x_3653_, 4, v___x_3662_);
v___x_3664_ = v___x_3653_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v_env_3644_);
lean_ctor_set(v_reuseFailAlloc_3667_, 1, v_nextMacroScope_3645_);
lean_ctor_set(v_reuseFailAlloc_3667_, 2, v_ngen_3646_);
lean_ctor_set(v_reuseFailAlloc_3667_, 3, v_auxDeclNGen_3647_);
lean_ctor_set(v_reuseFailAlloc_3667_, 4, v___x_3662_);
lean_ctor_set(v_reuseFailAlloc_3667_, 5, v_cache_3648_);
lean_ctor_set(v_reuseFailAlloc_3667_, 6, v_messages_3649_);
lean_ctor_set(v_reuseFailAlloc_3667_, 7, v_infoState_3650_);
lean_ctor_set(v_reuseFailAlloc_3667_, 8, v_snapshotTasks_3651_);
v___x_3664_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
lean_object* v___x_3665_; lean_object* v___x_3666_; 
v___x_3665_ = lean_st_ref_set(v___y_3587_, v___x_3664_);
lean_dec(v___y_3587_);
v___x_3666_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__2_spec__3___redArg(v_fst_3589_);
return v___x_3666_;
}
}
}
}
}
else
{
goto v___jp_3635_;
}
}
else
{
goto v___jp_3635_;
}
}
v___jp_3671_:
{
double v___x_3673_; double v___x_3674_; double v___x_3675_; uint8_t v___x_3676_; 
v___x_3673_ = lean_unbox_float(v_snd_3609_);
v___x_3674_ = lean_unbox_float(v_fst_3608_);
v___x_3675_ = lean_float_sub(v___x_3673_, v___x_3674_);
v___x_3676_ = lean_float_decLt(v___y_3672_, v___x_3675_);
v___y_3641_ = v___x_3676_;
goto v___jp_3640_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__2___boxed(lean_object* v_cls_3689_, lean_object* v_collapsed_3690_, lean_object* v_tag_3691_, lean_object* v_opts_3692_, lean_object* v_clsEnabled_3693_, lean_object* v_oldTraces_3694_, lean_object* v_msg_3695_, lean_object* v_resStartStop_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_){
_start:
{
uint8_t v_collapsed_boxed_3702_; uint8_t v_clsEnabled_boxed_3703_; lean_object* v_res_3704_; 
v_collapsed_boxed_3702_ = lean_unbox(v_collapsed_3690_);
v_clsEnabled_boxed_3703_ = lean_unbox(v_clsEnabled_3693_);
v_res_3704_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__2(v_cls_3689_, v_collapsed_boxed_3702_, v_tag_3691_, v_opts_3692_, v_clsEnabled_boxed_3703_, v_oldTraces_3694_, v_msg_3695_, v_resStartStop_3696_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_);
lean_dec_ref(v_opts_3692_);
return v_res_3704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry(lean_object* v_e_3709_, lean_object* v_a_3710_, lean_object* v_a_3711_, lean_object* v_a_3712_, lean_object* v_a_3713_){
_start:
{
lean_object* v_options_3715_; uint8_t v_hasTrace_3716_; 
v_options_3715_ = lean_ctor_get(v_a_3712_, 2);
v_hasTrace_3716_ = lean_ctor_get_uint8(v_options_3715_, sizeof(void*)*1);
if (v_hasTrace_3716_ == 0)
{
lean_object* v___x_3717_; 
v___x_3717_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_3713_);
if (lean_obj_tag(v___x_3717_) == 0)
{
lean_object* v_a_3718_; lean_object* v___x_3719_; 
v_a_3718_ = lean_ctor_get(v___x_3717_, 0);
lean_inc(v_a_3718_);
lean_dec_ref(v___x_3717_);
lean_inc(v_a_3713_);
lean_inc_ref(v_a_3712_);
lean_inc(v_a_3711_);
lean_inc_ref(v_a_3710_);
v___x_3719_ = l_Lean_Meta_Sym_unfoldReducible(v_e_3709_, v_a_3710_, v_a_3711_, v_a_3712_, v_a_3713_);
if (lean_obj_tag(v___x_3719_) == 0)
{
lean_object* v_a_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___f_3726_; lean_object* v___x_3727_; 
v_a_3720_ = lean_ctor_get(v___x_3719_, 0);
lean_inc(v_a_3720_);
lean_dec_ref(v___x_3719_);
v___x_3721_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_3722_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__6(v_options_3715_, v___x_3721_);
v___x_3723_ = lean_unsigned_to_nat(2u);
v___x_3724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3724_, 0, v___x_3722_);
lean_ctor_set(v___x_3724_, 1, v___x_3723_);
v___x_3725_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(v_a_3718_);
v___f_3726_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3726_, 0, v_a_3720_);
lean_closure_set(v___f_3726_, 1, v___x_3725_);
lean_closure_set(v___f_3726_, 2, v___x_3724_);
v___x_3727_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_3726_, v_a_3710_, v_a_3711_, v_a_3712_, v_a_3713_);
return v___x_3727_;
}
else
{
lean_object* v_a_3728_; lean_object* v___x_3730_; uint8_t v_isShared_3731_; uint8_t v_isSharedCheck_3735_; 
lean_dec(v_a_3718_);
lean_dec(v_a_3713_);
lean_dec_ref(v_a_3712_);
lean_dec(v_a_3711_);
lean_dec_ref(v_a_3710_);
v_a_3728_ = lean_ctor_get(v___x_3719_, 0);
v_isSharedCheck_3735_ = !lean_is_exclusive(v___x_3719_);
if (v_isSharedCheck_3735_ == 0)
{
v___x_3730_ = v___x_3719_;
v_isShared_3731_ = v_isSharedCheck_3735_;
goto v_resetjp_3729_;
}
else
{
lean_inc(v_a_3728_);
lean_dec(v___x_3719_);
v___x_3730_ = lean_box(0);
v_isShared_3731_ = v_isSharedCheck_3735_;
goto v_resetjp_3729_;
}
v_resetjp_3729_:
{
lean_object* v___x_3733_; 
if (v_isShared_3731_ == 0)
{
v___x_3733_ = v___x_3730_;
goto v_reusejp_3732_;
}
else
{
lean_object* v_reuseFailAlloc_3734_; 
v_reuseFailAlloc_3734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3734_, 0, v_a_3728_);
v___x_3733_ = v_reuseFailAlloc_3734_;
goto v_reusejp_3732_;
}
v_reusejp_3732_:
{
return v___x_3733_;
}
}
}
}
else
{
lean_object* v_a_3736_; lean_object* v___x_3738_; uint8_t v_isShared_3739_; uint8_t v_isSharedCheck_3743_; 
lean_dec(v_a_3713_);
lean_dec_ref(v_a_3712_);
lean_dec(v_a_3711_);
lean_dec_ref(v_a_3710_);
lean_dec_ref(v_e_3709_);
v_a_3736_ = lean_ctor_get(v___x_3717_, 0);
v_isSharedCheck_3743_ = !lean_is_exclusive(v___x_3717_);
if (v_isSharedCheck_3743_ == 0)
{
v___x_3738_ = v___x_3717_;
v_isShared_3739_ = v_isSharedCheck_3743_;
goto v_resetjp_3737_;
}
else
{
lean_inc(v_a_3736_);
lean_dec(v___x_3717_);
v___x_3738_ = lean_box(0);
v_isShared_3739_ = v_isSharedCheck_3743_;
goto v_resetjp_3737_;
}
v_resetjp_3737_:
{
lean_object* v___x_3741_; 
if (v_isShared_3739_ == 0)
{
v___x_3741_ = v___x_3738_;
goto v_reusejp_3740_;
}
else
{
lean_object* v_reuseFailAlloc_3742_; 
v_reuseFailAlloc_3742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3742_, 0, v_a_3736_);
v___x_3741_ = v_reuseFailAlloc_3742_;
goto v_reusejp_3740_;
}
v_reusejp_3740_:
{
return v___x_3741_;
}
}
}
}
else
{
lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v_a_3746_; lean_object* v___x_3748_; uint8_t v_isShared_3749_; uint8_t v_isSharedCheck_3874_; 
v___x_3744_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0));
v___x_3745_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg(v___x_3744_, v_a_3712_);
v_a_3746_ = lean_ctor_get(v___x_3745_, 0);
v_isSharedCheck_3874_ = !lean_is_exclusive(v___x_3745_);
if (v_isSharedCheck_3874_ == 0)
{
v___x_3748_ = v___x_3745_;
v_isShared_3749_ = v_isSharedCheck_3874_;
goto v_resetjp_3747_;
}
else
{
lean_inc(v_a_3746_);
lean_dec(v___x_3745_);
v___x_3748_ = lean_box(0);
v_isShared_3749_ = v_isSharedCheck_3874_;
goto v_resetjp_3747_;
}
v_resetjp_3747_:
{
lean_object* v___f_3750_; lean_object* v___x_3751_; lean_object* v___y_3753_; lean_object* v___y_3754_; lean_object* v_a_3755_; lean_object* v___y_3769_; lean_object* v___y_3770_; lean_object* v_a_3771_; lean_object* v___y_3776_; lean_object* v___y_3777_; lean_object* v_a_3778_; lean_object* v___y_3789_; lean_object* v___y_3790_; lean_object* v_a_3791_; uint8_t v___x_3844_; 
lean_inc_ref(v_e_3709_);
v___f_3750_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___boxed), 7, 1);
lean_closure_set(v___f_3750_, 0, v_e_3709_);
v___x_3751_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__1));
v___x_3844_ = lean_unbox(v_a_3746_);
if (v___x_3844_ == 0)
{
lean_object* v___x_3845_; uint8_t v___x_3846_; 
v___x_3845_ = l_Lean_trace_profiler;
v___x_3846_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2(v_options_3715_, v___x_3845_);
if (v___x_3846_ == 0)
{
lean_object* v___x_3847_; 
lean_dec_ref(v___f_3750_);
lean_del_object(v___x_3748_);
lean_dec(v_a_3746_);
v___x_3847_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_3713_);
if (lean_obj_tag(v___x_3847_) == 0)
{
lean_object* v_a_3848_; lean_object* v___x_3849_; 
v_a_3848_ = lean_ctor_get(v___x_3847_, 0);
lean_inc(v_a_3848_);
lean_dec_ref(v___x_3847_);
lean_inc(v_a_3713_);
lean_inc_ref(v_a_3712_);
lean_inc(v_a_3711_);
lean_inc_ref(v_a_3710_);
v___x_3849_ = l_Lean_Meta_Sym_unfoldReducible(v_e_3709_, v_a_3710_, v_a_3711_, v_a_3712_, v_a_3713_);
if (lean_obj_tag(v___x_3849_) == 0)
{
lean_object* v_a_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___f_3856_; lean_object* v___x_3857_; 
v_a_3850_ = lean_ctor_get(v___x_3849_, 0);
lean_inc(v_a_3850_);
lean_dec_ref(v___x_3849_);
v___x_3851_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_3852_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__6(v_options_3715_, v___x_3851_);
v___x_3853_ = lean_unsigned_to_nat(2u);
v___x_3854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3854_, 0, v___x_3852_);
lean_ctor_set(v___x_3854_, 1, v___x_3853_);
v___x_3855_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(v_a_3848_);
v___f_3856_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3856_, 0, v_a_3850_);
lean_closure_set(v___f_3856_, 1, v___x_3855_);
lean_closure_set(v___f_3856_, 2, v___x_3854_);
v___x_3857_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_3856_, v_a_3710_, v_a_3711_, v_a_3712_, v_a_3713_);
return v___x_3857_;
}
else
{
lean_object* v_a_3858_; lean_object* v___x_3860_; uint8_t v_isShared_3861_; uint8_t v_isSharedCheck_3865_; 
lean_dec(v_a_3848_);
lean_dec(v_a_3713_);
lean_dec_ref(v_a_3712_);
lean_dec(v_a_3711_);
lean_dec_ref(v_a_3710_);
v_a_3858_ = lean_ctor_get(v___x_3849_, 0);
v_isSharedCheck_3865_ = !lean_is_exclusive(v___x_3849_);
if (v_isSharedCheck_3865_ == 0)
{
v___x_3860_ = v___x_3849_;
v_isShared_3861_ = v_isSharedCheck_3865_;
goto v_resetjp_3859_;
}
else
{
lean_inc(v_a_3858_);
lean_dec(v___x_3849_);
v___x_3860_ = lean_box(0);
v_isShared_3861_ = v_isSharedCheck_3865_;
goto v_resetjp_3859_;
}
v_resetjp_3859_:
{
lean_object* v___x_3863_; 
if (v_isShared_3861_ == 0)
{
v___x_3863_ = v___x_3860_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3864_; 
v_reuseFailAlloc_3864_ = lean_alloc_ctor(1, 1, 0);
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
else
{
lean_object* v_a_3866_; lean_object* v___x_3868_; uint8_t v_isShared_3869_; uint8_t v_isSharedCheck_3873_; 
lean_dec(v_a_3713_);
lean_dec_ref(v_a_3712_);
lean_dec(v_a_3711_);
lean_dec_ref(v_a_3710_);
lean_dec_ref(v_e_3709_);
v_a_3866_ = lean_ctor_get(v___x_3847_, 0);
v_isSharedCheck_3873_ = !lean_is_exclusive(v___x_3847_);
if (v_isSharedCheck_3873_ == 0)
{
v___x_3868_ = v___x_3847_;
v_isShared_3869_ = v_isSharedCheck_3873_;
goto v_resetjp_3867_;
}
else
{
lean_inc(v_a_3866_);
lean_dec(v___x_3847_);
v___x_3868_ = lean_box(0);
v_isShared_3869_ = v_isSharedCheck_3873_;
goto v_resetjp_3867_;
}
v_resetjp_3867_:
{
lean_object* v___x_3871_; 
if (v_isShared_3869_ == 0)
{
v___x_3871_ = v___x_3868_;
goto v_reusejp_3870_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v_a_3866_);
v___x_3871_ = v_reuseFailAlloc_3872_;
goto v_reusejp_3870_;
}
v_reusejp_3870_:
{
return v___x_3871_;
}
}
}
}
else
{
lean_inc_ref(v_options_3715_);
goto v___jp_3793_;
}
}
else
{
lean_inc_ref(v_options_3715_);
goto v___jp_3793_;
}
v___jp_3752_:
{
lean_object* v___x_3756_; double v___x_3757_; double v___x_3758_; double v___x_3759_; double v___x_3760_; double v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; uint8_t v___x_3766_; lean_object* v___x_3767_; 
v___x_3756_ = lean_io_mono_nanos_now();
v___x_3757_ = lean_float_of_nat(v___y_3754_);
v___x_3758_ = lean_float_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4);
v___x_3759_ = lean_float_div(v___x_3757_, v___x_3758_);
v___x_3760_ = lean_float_of_nat(v___x_3756_);
v___x_3761_ = lean_float_div(v___x_3760_, v___x_3758_);
v___x_3762_ = lean_box_float(v___x_3759_);
v___x_3763_ = lean_box_float(v___x_3761_);
v___x_3764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3764_, 0, v___x_3762_);
lean_ctor_set(v___x_3764_, 1, v___x_3763_);
v___x_3765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3765_, 0, v_a_3755_);
lean_ctor_set(v___x_3765_, 1, v___x_3764_);
v___x_3766_ = lean_unbox(v_a_3746_);
lean_dec(v_a_3746_);
v___x_3767_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__2(v___x_3744_, v_hasTrace_3716_, v___x_3751_, v_options_3715_, v___x_3766_, v___y_3753_, v___f_3750_, v___x_3765_, v_a_3710_, v_a_3711_, v_a_3712_, v_a_3713_);
lean_dec_ref(v_options_3715_);
return v___x_3767_;
}
v___jp_3768_:
{
lean_object* v___x_3773_; 
if (v_isShared_3749_ == 0)
{
lean_ctor_set(v___x_3748_, 0, v_a_3771_);
v___x_3773_ = v___x_3748_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v_a_3771_);
v___x_3773_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
v___y_3753_ = v___y_3769_;
v___y_3754_ = v___y_3770_;
v_a_3755_ = v___x_3773_;
goto v___jp_3752_;
}
}
v___jp_3775_:
{
lean_object* v___x_3779_; double v___x_3780_; double v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; uint8_t v___x_3786_; lean_object* v___x_3787_; 
v___x_3779_ = lean_io_get_num_heartbeats();
v___x_3780_ = lean_float_of_nat(v___y_3777_);
v___x_3781_ = lean_float_of_nat(v___x_3779_);
v___x_3782_ = lean_box_float(v___x_3780_);
v___x_3783_ = lean_box_float(v___x_3781_);
v___x_3784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3784_, 0, v___x_3782_);
lean_ctor_set(v___x_3784_, 1, v___x_3783_);
v___x_3785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3785_, 0, v_a_3778_);
lean_ctor_set(v___x_3785_, 1, v___x_3784_);
v___x_3786_ = lean_unbox(v_a_3746_);
lean_dec(v_a_3746_);
v___x_3787_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__2(v___x_3744_, v_hasTrace_3716_, v___x_3751_, v_options_3715_, v___x_3786_, v___y_3776_, v___f_3750_, v___x_3785_, v_a_3710_, v_a_3711_, v_a_3712_, v_a_3713_);
lean_dec_ref(v_options_3715_);
return v___x_3787_;
}
v___jp_3788_:
{
lean_object* v___x_3792_; 
v___x_3792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3792_, 0, v_a_3791_);
v___y_3776_ = v___y_3790_;
v___y_3777_ = v___y_3789_;
v_a_3778_ = v___x_3792_;
goto v___jp_3775_;
}
v___jp_3793_:
{
lean_object* v___x_3794_; lean_object* v_a_3795_; lean_object* v___x_3796_; uint8_t v___x_3797_; 
v___x_3794_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1___redArg(v_a_3713_);
v_a_3795_ = lean_ctor_get(v___x_3794_, 0);
lean_inc(v_a_3795_);
lean_dec_ref(v___x_3794_);
v___x_3796_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3797_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2(v_options_3715_, v___x_3796_);
if (v___x_3797_ == 0)
{
lean_object* v___x_3798_; lean_object* v___x_3799_; 
v___x_3798_ = lean_io_mono_nanos_now();
v___x_3799_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_3713_);
if (lean_obj_tag(v___x_3799_) == 0)
{
lean_object* v_a_3800_; lean_object* v___x_3801_; 
v_a_3800_ = lean_ctor_get(v___x_3799_, 0);
lean_inc(v_a_3800_);
lean_dec_ref(v___x_3799_);
lean_inc(v_a_3713_);
lean_inc_ref(v_a_3712_);
lean_inc(v_a_3711_);
lean_inc_ref(v_a_3710_);
v___x_3801_ = l_Lean_Meta_Sym_unfoldReducible(v_e_3709_, v_a_3710_, v_a_3711_, v_a_3712_, v_a_3713_);
if (lean_obj_tag(v___x_3801_) == 0)
{
lean_object* v_a_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___f_3808_; lean_object* v___x_3809_; 
v_a_3802_ = lean_ctor_get(v___x_3801_, 0);
lean_inc(v_a_3802_);
lean_dec_ref(v___x_3801_);
v___x_3803_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_3804_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__6(v_options_3715_, v___x_3803_);
v___x_3805_ = lean_unsigned_to_nat(2u);
v___x_3806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3806_, 0, v___x_3804_);
lean_ctor_set(v___x_3806_, 1, v___x_3805_);
v___x_3807_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(v_a_3800_);
v___f_3808_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3808_, 0, v_a_3802_);
lean_closure_set(v___f_3808_, 1, v___x_3807_);
lean_closure_set(v___f_3808_, 2, v___x_3806_);
lean_inc(v_a_3713_);
lean_inc_ref(v_a_3712_);
lean_inc(v_a_3711_);
lean_inc_ref(v_a_3710_);
v___x_3809_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_3808_, v_a_3710_, v_a_3711_, v_a_3712_, v_a_3713_);
if (lean_obj_tag(v___x_3809_) == 0)
{
lean_object* v_a_3810_; lean_object* v___x_3812_; uint8_t v_isShared_3813_; uint8_t v_isSharedCheck_3817_; 
lean_del_object(v___x_3748_);
v_a_3810_ = lean_ctor_get(v___x_3809_, 0);
v_isSharedCheck_3817_ = !lean_is_exclusive(v___x_3809_);
if (v_isSharedCheck_3817_ == 0)
{
v___x_3812_ = v___x_3809_;
v_isShared_3813_ = v_isSharedCheck_3817_;
goto v_resetjp_3811_;
}
else
{
lean_inc(v_a_3810_);
lean_dec(v___x_3809_);
v___x_3812_ = lean_box(0);
v_isShared_3813_ = v_isSharedCheck_3817_;
goto v_resetjp_3811_;
}
v_resetjp_3811_:
{
lean_object* v___x_3815_; 
if (v_isShared_3813_ == 0)
{
lean_ctor_set_tag(v___x_3812_, 1);
v___x_3815_ = v___x_3812_;
goto v_reusejp_3814_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v_a_3810_);
v___x_3815_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3814_;
}
v_reusejp_3814_:
{
v___y_3753_ = v_a_3795_;
v___y_3754_ = v___x_3798_;
v_a_3755_ = v___x_3815_;
goto v___jp_3752_;
}
}
}
else
{
lean_object* v_a_3818_; 
v_a_3818_ = lean_ctor_get(v___x_3809_, 0);
lean_inc(v_a_3818_);
lean_dec_ref(v___x_3809_);
v___y_3769_ = v_a_3795_;
v___y_3770_ = v___x_3798_;
v_a_3771_ = v_a_3818_;
goto v___jp_3768_;
}
}
else
{
lean_object* v_a_3819_; 
lean_dec(v_a_3800_);
v_a_3819_ = lean_ctor_get(v___x_3801_, 0);
lean_inc(v_a_3819_);
lean_dec_ref(v___x_3801_);
v___y_3769_ = v_a_3795_;
v___y_3770_ = v___x_3798_;
v_a_3771_ = v_a_3819_;
goto v___jp_3768_;
}
}
else
{
lean_object* v_a_3820_; 
lean_dec_ref(v_e_3709_);
v_a_3820_ = lean_ctor_get(v___x_3799_, 0);
lean_inc(v_a_3820_);
lean_dec_ref(v___x_3799_);
v___y_3769_ = v_a_3795_;
v___y_3770_ = v___x_3798_;
v_a_3771_ = v_a_3820_;
goto v___jp_3768_;
}
}
else
{
lean_object* v___x_3821_; lean_object* v___x_3822_; 
lean_del_object(v___x_3748_);
v___x_3821_ = lean_io_get_num_heartbeats();
v___x_3822_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_3713_);
if (lean_obj_tag(v___x_3822_) == 0)
{
lean_object* v_a_3823_; lean_object* v___x_3824_; 
v_a_3823_ = lean_ctor_get(v___x_3822_, 0);
lean_inc(v_a_3823_);
lean_dec_ref(v___x_3822_);
lean_inc(v_a_3713_);
lean_inc_ref(v_a_3712_);
lean_inc(v_a_3711_);
lean_inc_ref(v_a_3710_);
v___x_3824_ = l_Lean_Meta_Sym_unfoldReducible(v_e_3709_, v_a_3710_, v_a_3711_, v_a_3712_, v_a_3713_);
if (lean_obj_tag(v___x_3824_) == 0)
{
lean_object* v_a_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___f_3831_; lean_object* v___x_3832_; 
v_a_3825_ = lean_ctor_get(v___x_3824_, 0);
lean_inc(v_a_3825_);
lean_dec_ref(v___x_3824_);
v___x_3826_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_3827_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__6(v_options_3715_, v___x_3826_);
v___x_3828_ = lean_unsigned_to_nat(2u);
v___x_3829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3829_, 0, v___x_3827_);
lean_ctor_set(v___x_3829_, 1, v___x_3828_);
v___x_3830_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(v_a_3823_);
v___f_3831_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3831_, 0, v_a_3825_);
lean_closure_set(v___f_3831_, 1, v___x_3830_);
lean_closure_set(v___f_3831_, 2, v___x_3829_);
lean_inc(v_a_3713_);
lean_inc_ref(v_a_3712_);
lean_inc(v_a_3711_);
lean_inc_ref(v_a_3710_);
v___x_3832_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_3831_, v_a_3710_, v_a_3711_, v_a_3712_, v_a_3713_);
if (lean_obj_tag(v___x_3832_) == 0)
{
lean_object* v_a_3833_; lean_object* v___x_3835_; uint8_t v_isShared_3836_; uint8_t v_isSharedCheck_3840_; 
v_a_3833_ = lean_ctor_get(v___x_3832_, 0);
v_isSharedCheck_3840_ = !lean_is_exclusive(v___x_3832_);
if (v_isSharedCheck_3840_ == 0)
{
v___x_3835_ = v___x_3832_;
v_isShared_3836_ = v_isSharedCheck_3840_;
goto v_resetjp_3834_;
}
else
{
lean_inc(v_a_3833_);
lean_dec(v___x_3832_);
v___x_3835_ = lean_box(0);
v_isShared_3836_ = v_isSharedCheck_3840_;
goto v_resetjp_3834_;
}
v_resetjp_3834_:
{
lean_object* v___x_3838_; 
if (v_isShared_3836_ == 0)
{
lean_ctor_set_tag(v___x_3835_, 1);
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
v___y_3776_ = v_a_3795_;
v___y_3777_ = v___x_3821_;
v_a_3778_ = v___x_3838_;
goto v___jp_3775_;
}
}
}
else
{
lean_object* v_a_3841_; 
v_a_3841_ = lean_ctor_get(v___x_3832_, 0);
lean_inc(v_a_3841_);
lean_dec_ref(v___x_3832_);
v___y_3789_ = v___x_3821_;
v___y_3790_ = v_a_3795_;
v_a_3791_ = v_a_3841_;
goto v___jp_3788_;
}
}
else
{
lean_object* v_a_3842_; 
lean_dec(v_a_3823_);
v_a_3842_ = lean_ctor_get(v___x_3824_, 0);
lean_inc(v_a_3842_);
lean_dec_ref(v___x_3824_);
v___y_3789_ = v___x_3821_;
v___y_3790_ = v_a_3795_;
v_a_3791_ = v_a_3842_;
goto v___jp_3788_;
}
}
else
{
lean_object* v_a_3843_; 
lean_dec_ref(v_e_3709_);
v_a_3843_ = lean_ctor_get(v___x_3822_, 0);
lean_inc(v_a_3843_);
lean_dec_ref(v___x_3822_);
v___y_3789_ = v___x_3821_;
v___y_3790_ = v_a_3795_;
v_a_3791_ = v_a_3843_;
goto v___jp_3788_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___boxed(lean_object* v_e_3875_, lean_object* v_a_3876_, lean_object* v_a_3877_, lean_object* v_a_3878_, lean_object* v_a_3879_, lean_object* v_a_3880_){
_start:
{
lean_object* v_res_3881_; 
v_res_3881_ = l_Lean_Meta_Tactic_Cbv_cbvEntry(v_e_3875_, v_a_3876_, v_a_3877_, v_a_3878_, v_a_3879_);
return v_res_3881_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__2_spec__3(lean_object* v_00_u03b1_3882_, lean_object* v_x_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_){
_start:
{
lean_object* v___x_3889_; 
v___x_3889_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__2_spec__3___redArg(v_x_3883_);
return v___x_3889_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__2_spec__3___boxed(lean_object* v_00_u03b1_3890_, lean_object* v_x_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_){
_start:
{
lean_object* v_res_3897_; 
v_res_3897_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__2_spec__3(v_00_u03b1_3890_, v_x_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_);
lean_dec(v___y_3895_);
lean_dec_ref(v___y_3894_);
lean_dec(v___y_3893_);
lean_dec_ref(v___y_3892_);
return v_res_3897_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__1___redArg(lean_object* v_cls_3898_, lean_object* v___y_3899_){
_start:
{
lean_object* v_options_3901_; uint8_t v_hasTrace_3902_; 
v_options_3901_ = lean_ctor_get(v___y_3899_, 2);
v_hasTrace_3902_ = lean_ctor_get_uint8(v_options_3901_, sizeof(void*)*1);
if (v_hasTrace_3902_ == 0)
{
lean_object* v___x_3903_; lean_object* v___x_3904_; 
lean_dec(v_cls_3898_);
v___x_3903_ = lean_box(v_hasTrace_3902_);
v___x_3904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3904_, 0, v___x_3903_);
return v___x_3904_;
}
else
{
lean_object* v_inheritedTraceOptions_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; uint8_t v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; 
v_inheritedTraceOptions_3905_ = lean_ctor_get(v___y_3899_, 13);
v___x_3906_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__1));
v___x_3907_ = l_Lean_Name_append(v___x_3906_, v_cls_3898_);
v___x_3908_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3905_, v_options_3901_, v___x_3907_);
lean_dec(v___x_3907_);
v___x_3909_ = lean_box(v___x_3908_);
v___x_3910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3910_, 0, v___x_3909_);
return v___x_3910_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__1___redArg___boxed(lean_object* v_cls_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_){
_start:
{
lean_object* v_res_3914_; 
v_res_3914_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__1___redArg(v_cls_3911_, v___y_3912_);
lean_dec_ref(v___y_3912_);
return v_res_3914_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__1(lean_object* v_cls_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_){
_start:
{
lean_object* v___x_3923_; 
v___x_3923_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__1___redArg(v_cls_3915_, v___y_3920_);
return v___x_3923_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__1___boxed(lean_object* v_cls_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_){
_start:
{
lean_object* v_res_3932_; 
v_res_3932_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__1(v_cls_3924_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_);
lean_dec(v___y_3930_);
lean_dec_ref(v___y_3929_);
lean_dec(v___y_3928_);
lean_dec_ref(v___y_3927_);
lean_dec(v___y_3926_);
lean_dec_ref(v___y_3925_);
return v_res_3932_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2___redArg(lean_object* v___y_3933_){
_start:
{
lean_object* v___x_3935_; lean_object* v_traceState_3936_; lean_object* v_traces_3937_; lean_object* v___x_3938_; lean_object* v_traceState_3939_; lean_object* v_env_3940_; lean_object* v_nextMacroScope_3941_; lean_object* v_ngen_3942_; lean_object* v_auxDeclNGen_3943_; lean_object* v_cache_3944_; lean_object* v_messages_3945_; lean_object* v_infoState_3946_; lean_object* v_snapshotTasks_3947_; lean_object* v___x_3949_; uint8_t v_isShared_3950_; uint8_t v_isSharedCheck_3968_; 
v___x_3935_ = lean_st_ref_get(v___y_3933_);
v_traceState_3936_ = lean_ctor_get(v___x_3935_, 4);
lean_inc_ref(v_traceState_3936_);
lean_dec(v___x_3935_);
v_traces_3937_ = lean_ctor_get(v_traceState_3936_, 0);
lean_inc_ref(v_traces_3937_);
lean_dec_ref(v_traceState_3936_);
v___x_3938_ = lean_st_ref_take(v___y_3933_);
v_traceState_3939_ = lean_ctor_get(v___x_3938_, 4);
v_env_3940_ = lean_ctor_get(v___x_3938_, 0);
v_nextMacroScope_3941_ = lean_ctor_get(v___x_3938_, 1);
v_ngen_3942_ = lean_ctor_get(v___x_3938_, 2);
v_auxDeclNGen_3943_ = lean_ctor_get(v___x_3938_, 3);
v_cache_3944_ = lean_ctor_get(v___x_3938_, 5);
v_messages_3945_ = lean_ctor_get(v___x_3938_, 6);
v_infoState_3946_ = lean_ctor_get(v___x_3938_, 7);
v_snapshotTasks_3947_ = lean_ctor_get(v___x_3938_, 8);
v_isSharedCheck_3968_ = !lean_is_exclusive(v___x_3938_);
if (v_isSharedCheck_3968_ == 0)
{
v___x_3949_ = v___x_3938_;
v_isShared_3950_ = v_isSharedCheck_3968_;
goto v_resetjp_3948_;
}
else
{
lean_inc(v_snapshotTasks_3947_);
lean_inc(v_infoState_3946_);
lean_inc(v_messages_3945_);
lean_inc(v_cache_3944_);
lean_inc(v_traceState_3939_);
lean_inc(v_auxDeclNGen_3943_);
lean_inc(v_ngen_3942_);
lean_inc(v_nextMacroScope_3941_);
lean_inc(v_env_3940_);
lean_dec(v___x_3938_);
v___x_3949_ = lean_box(0);
v_isShared_3950_ = v_isSharedCheck_3968_;
goto v_resetjp_3948_;
}
v_resetjp_3948_:
{
uint64_t v_tid_3951_; lean_object* v___x_3953_; uint8_t v_isShared_3954_; uint8_t v_isSharedCheck_3966_; 
v_tid_3951_ = lean_ctor_get_uint64(v_traceState_3939_, sizeof(void*)*1);
v_isSharedCheck_3966_ = !lean_is_exclusive(v_traceState_3939_);
if (v_isSharedCheck_3966_ == 0)
{
lean_object* v_unused_3967_; 
v_unused_3967_ = lean_ctor_get(v_traceState_3939_, 0);
lean_dec(v_unused_3967_);
v___x_3953_ = v_traceState_3939_;
v_isShared_3954_ = v_isSharedCheck_3966_;
goto v_resetjp_3952_;
}
else
{
lean_dec(v_traceState_3939_);
v___x_3953_ = lean_box(0);
v_isShared_3954_ = v_isSharedCheck_3966_;
goto v_resetjp_3952_;
}
v_resetjp_3952_:
{
lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3959_; 
v___x_3955_ = lean_unsigned_to_nat(32u);
v___x_3956_ = lean_mk_empty_array_with_capacity(v___x_3955_);
lean_dec_ref(v___x_3956_);
v___x_3957_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___redArg___closed__1);
if (v_isShared_3954_ == 0)
{
lean_ctor_set(v___x_3953_, 0, v___x_3957_);
v___x_3959_ = v___x_3953_;
goto v_reusejp_3958_;
}
else
{
lean_object* v_reuseFailAlloc_3965_; 
v_reuseFailAlloc_3965_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3965_, 0, v___x_3957_);
lean_ctor_set_uint64(v_reuseFailAlloc_3965_, sizeof(void*)*1, v_tid_3951_);
v___x_3959_ = v_reuseFailAlloc_3965_;
goto v_reusejp_3958_;
}
v_reusejp_3958_:
{
lean_object* v___x_3961_; 
if (v_isShared_3950_ == 0)
{
lean_ctor_set(v___x_3949_, 4, v___x_3959_);
v___x_3961_ = v___x_3949_;
goto v_reusejp_3960_;
}
else
{
lean_object* v_reuseFailAlloc_3964_; 
v_reuseFailAlloc_3964_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3964_, 0, v_env_3940_);
lean_ctor_set(v_reuseFailAlloc_3964_, 1, v_nextMacroScope_3941_);
lean_ctor_set(v_reuseFailAlloc_3964_, 2, v_ngen_3942_);
lean_ctor_set(v_reuseFailAlloc_3964_, 3, v_auxDeclNGen_3943_);
lean_ctor_set(v_reuseFailAlloc_3964_, 4, v___x_3959_);
lean_ctor_set(v_reuseFailAlloc_3964_, 5, v_cache_3944_);
lean_ctor_set(v_reuseFailAlloc_3964_, 6, v_messages_3945_);
lean_ctor_set(v_reuseFailAlloc_3964_, 7, v_infoState_3946_);
lean_ctor_set(v_reuseFailAlloc_3964_, 8, v_snapshotTasks_3947_);
v___x_3961_ = v_reuseFailAlloc_3964_;
goto v_reusejp_3960_;
}
v_reusejp_3960_:
{
lean_object* v___x_3962_; lean_object* v___x_3963_; 
v___x_3962_ = lean_st_ref_set(v___y_3933_, v___x_3961_);
v___x_3963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3963_, 0, v_traces_3937_);
return v___x_3963_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2___redArg___boxed(lean_object* v___y_3969_, lean_object* v___y_3970_){
_start:
{
lean_object* v_res_3971_; 
v_res_3971_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2___redArg(v___y_3969_);
lean_dec(v___y_3969_);
return v_res_3971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2(lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_){
_start:
{
lean_object* v___x_3979_; 
v___x_3979_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2___redArg(v___y_3977_);
return v___x_3979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2___boxed(lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_){
_start:
{
lean_object* v_res_3987_; 
v_res_3987_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2(v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_);
lean_dec(v___y_3985_);
lean_dec_ref(v___y_3984_);
lean_dec(v___y_3983_);
lean_dec_ref(v___y_3982_);
lean_dec(v___y_3981_);
lean_dec_ref(v___y_3980_);
return v_res_3987_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__5___redArg___lam__0(lean_object* v_x_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_){
_start:
{
lean_object* v___x_3996_; 
v___x_3996_ = lean_apply_7(v_x_3988_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_, lean_box(0));
return v___x_3996_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__5___redArg___lam__0___boxed(lean_object* v_x_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_){
_start:
{
lean_object* v_res_4005_; 
v_res_4005_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__5___redArg___lam__0(v_x_3997_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_);
return v_res_4005_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__5___redArg(lean_object* v_mvarId_4006_, lean_object* v_x_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_){
_start:
{
lean_object* v___f_4015_; lean_object* v___x_4016_; 
v___f_4015_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__5___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4015_, 0, v_x_4007_);
lean_closure_set(v___f_4015_, 1, v___y_4008_);
lean_closure_set(v___f_4015_, 2, v___y_4009_);
v___x_4016_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_4006_, v___f_4015_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_);
if (lean_obj_tag(v___x_4016_) == 0)
{
return v___x_4016_;
}
else
{
lean_object* v_a_4017_; lean_object* v___x_4019_; uint8_t v_isShared_4020_; uint8_t v_isSharedCheck_4024_; 
v_a_4017_ = lean_ctor_get(v___x_4016_, 0);
v_isSharedCheck_4024_ = !lean_is_exclusive(v___x_4016_);
if (v_isSharedCheck_4024_ == 0)
{
v___x_4019_ = v___x_4016_;
v_isShared_4020_ = v_isSharedCheck_4024_;
goto v_resetjp_4018_;
}
else
{
lean_inc(v_a_4017_);
lean_dec(v___x_4016_);
v___x_4019_ = lean_box(0);
v_isShared_4020_ = v_isSharedCheck_4024_;
goto v_resetjp_4018_;
}
v_resetjp_4018_:
{
lean_object* v___x_4022_; 
if (v_isShared_4020_ == 0)
{
v___x_4022_ = v___x_4019_;
goto v_reusejp_4021_;
}
else
{
lean_object* v_reuseFailAlloc_4023_; 
v_reuseFailAlloc_4023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4023_, 0, v_a_4017_);
v___x_4022_ = v_reuseFailAlloc_4023_;
goto v_reusejp_4021_;
}
v_reusejp_4021_:
{
return v___x_4022_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__5___redArg___boxed(lean_object* v_mvarId_4025_, lean_object* v_x_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_){
_start:
{
lean_object* v_res_4034_; 
v_res_4034_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__5___redArg(v_mvarId_4025_, v_x_4026_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_);
return v_res_4034_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__5(lean_object* v_00_u03b1_4035_, lean_object* v_mvarId_4036_, lean_object* v_x_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_){
_start:
{
lean_object* v___x_4045_; 
v___x_4045_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__5___redArg(v_mvarId_4036_, v_x_4037_, v___y_4038_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_, v___y_4043_);
return v___x_4045_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__5___boxed(lean_object* v_00_u03b1_4046_, lean_object* v_mvarId_4047_, lean_object* v_x_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_){
_start:
{
lean_object* v_res_4056_; 
v_res_4056_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__5(v_00_u03b1_4046_, v_mvarId_4047_, v_x_4048_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_);
return v_res_4056_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4058_; lean_object* v___x_4059_; 
v___x_4058_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__0));
v___x_4059_ = l_Lean_stringToMessageData(v___x_4058_);
return v___x_4059_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4061_; lean_object* v___x_4062_; 
v___x_4061_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__2));
v___x_4062_ = l_Lean_stringToMessageData(v___x_4061_);
return v___x_4062_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4064_; lean_object* v___x_4065_; 
v___x_4064_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__4));
v___x_4065_ = l_Lean_stringToMessageData(v___x_4064_);
return v___x_4065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0(lean_object* v_a_4066_, lean_object* v_x_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_){
_start:
{
if (lean_obj_tag(v_x_4067_) == 0)
{
lean_object* v_a_4075_; lean_object* v___x_4077_; uint8_t v_isShared_4078_; uint8_t v_isSharedCheck_4085_; 
lean_dec_ref(v_a_4066_);
v_a_4075_ = lean_ctor_get(v_x_4067_, 0);
v_isSharedCheck_4085_ = !lean_is_exclusive(v_x_4067_);
if (v_isSharedCheck_4085_ == 0)
{
v___x_4077_ = v_x_4067_;
v_isShared_4078_ = v_isSharedCheck_4085_;
goto v_resetjp_4076_;
}
else
{
lean_inc(v_a_4075_);
lean_dec(v_x_4067_);
v___x_4077_ = lean_box(0);
v_isShared_4078_ = v_isSharedCheck_4085_;
goto v_resetjp_4076_;
}
v_resetjp_4076_:
{
lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4083_; 
v___x_4079_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__1);
v___x_4080_ = l_Lean_Exception_toMessageData(v_a_4075_);
v___x_4081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4081_, 0, v___x_4079_);
lean_ctor_set(v___x_4081_, 1, v___x_4080_);
if (v_isShared_4078_ == 0)
{
lean_ctor_set(v___x_4077_, 0, v___x_4081_);
v___x_4083_ = v___x_4077_;
goto v_reusejp_4082_;
}
else
{
lean_object* v_reuseFailAlloc_4084_; 
v_reuseFailAlloc_4084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4084_, 0, v___x_4081_);
v___x_4083_ = v_reuseFailAlloc_4084_;
goto v_reusejp_4082_;
}
v_reusejp_4082_:
{
return v___x_4083_;
}
}
}
else
{
lean_object* v_a_4086_; lean_object* v___x_4088_; uint8_t v_isShared_4089_; uint8_t v_isSharedCheck_4105_; 
v_a_4086_ = lean_ctor_get(v_x_4067_, 0);
v_isSharedCheck_4105_ = !lean_is_exclusive(v_x_4067_);
if (v_isSharedCheck_4105_ == 0)
{
v___x_4088_ = v_x_4067_;
v_isShared_4089_ = v_isSharedCheck_4105_;
goto v_resetjp_4087_;
}
else
{
lean_inc(v_a_4086_);
lean_dec(v_x_4067_);
v___x_4088_ = lean_box(0);
v_isShared_4089_ = v_isSharedCheck_4105_;
goto v_resetjp_4087_;
}
v_resetjp_4087_:
{
if (lean_obj_tag(v_a_4086_) == 0)
{
lean_object* v___x_4090_; lean_object* v___x_4092_; 
lean_dec_ref(v_a_4086_);
lean_dec_ref(v_a_4066_);
v___x_4090_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__3, &l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__3);
if (v_isShared_4089_ == 0)
{
lean_ctor_set_tag(v___x_4088_, 0);
lean_ctor_set(v___x_4088_, 0, v___x_4090_);
v___x_4092_ = v___x_4088_;
goto v_reusejp_4091_;
}
else
{
lean_object* v_reuseFailAlloc_4093_; 
v_reuseFailAlloc_4093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4093_, 0, v___x_4090_);
v___x_4092_ = v_reuseFailAlloc_4093_;
goto v_reusejp_4091_;
}
v_reusejp_4091_:
{
return v___x_4092_;
}
}
else
{
lean_object* v_e_x27_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4103_; 
v_e_x27_4094_ = lean_ctor_get(v_a_4086_, 0);
lean_inc_ref(v_e_x27_4094_);
lean_dec_ref(v_a_4086_);
v___x_4095_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__5, &l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__5_once, _init_l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__5);
v___x_4096_ = l_Lean_indentExpr(v_a_4066_);
v___x_4097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4097_, 0, v___x_4095_);
lean_ctor_set(v___x_4097_, 1, v___x_4096_);
v___x_4098_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7);
v___x_4099_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4099_, 0, v___x_4097_);
lean_ctor_set(v___x_4099_, 1, v___x_4098_);
v___x_4100_ = l_Lean_indentExpr(v_e_x27_4094_);
v___x_4101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4101_, 0, v___x_4099_);
lean_ctor_set(v___x_4101_, 1, v___x_4100_);
if (v_isShared_4089_ == 0)
{
lean_ctor_set_tag(v___x_4088_, 0);
lean_ctor_set(v___x_4088_, 0, v___x_4101_);
v___x_4103_ = v___x_4088_;
goto v_reusejp_4102_;
}
else
{
lean_object* v_reuseFailAlloc_4104_; 
v_reuseFailAlloc_4104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4104_, 0, v___x_4101_);
v___x_4103_ = v_reuseFailAlloc_4104_;
goto v_reusejp_4102_;
}
v_reusejp_4102_:
{
return v___x_4103_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___boxed(lean_object* v_a_4106_, lean_object* v_x_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_){
_start:
{
lean_object* v_res_4115_; 
v_res_4115_ = l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0(v_a_4106_, v_x_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_);
lean_dec(v___y_4113_);
lean_dec_ref(v___y_4112_);
lean_dec(v___y_4111_);
lean_dec_ref(v___y_4110_);
lean_dec(v___y_4109_);
lean_dec_ref(v___y_4108_);
return v_res_4115_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3_spec__5___redArg(lean_object* v_x_4116_){
_start:
{
if (lean_obj_tag(v_x_4116_) == 0)
{
lean_object* v_a_4118_; lean_object* v___x_4120_; uint8_t v_isShared_4121_; uint8_t v_isSharedCheck_4125_; 
v_a_4118_ = lean_ctor_get(v_x_4116_, 0);
v_isSharedCheck_4125_ = !lean_is_exclusive(v_x_4116_);
if (v_isSharedCheck_4125_ == 0)
{
v___x_4120_ = v_x_4116_;
v_isShared_4121_ = v_isSharedCheck_4125_;
goto v_resetjp_4119_;
}
else
{
lean_inc(v_a_4118_);
lean_dec(v_x_4116_);
v___x_4120_ = lean_box(0);
v_isShared_4121_ = v_isSharedCheck_4125_;
goto v_resetjp_4119_;
}
v_resetjp_4119_:
{
lean_object* v___x_4123_; 
if (v_isShared_4121_ == 0)
{
lean_ctor_set_tag(v___x_4120_, 1);
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
else
{
lean_object* v_a_4126_; lean_object* v___x_4128_; uint8_t v_isShared_4129_; uint8_t v_isSharedCheck_4133_; 
v_a_4126_ = lean_ctor_get(v_x_4116_, 0);
v_isSharedCheck_4133_ = !lean_is_exclusive(v_x_4116_);
if (v_isSharedCheck_4133_ == 0)
{
v___x_4128_ = v_x_4116_;
v_isShared_4129_ = v_isSharedCheck_4133_;
goto v_resetjp_4127_;
}
else
{
lean_inc(v_a_4126_);
lean_dec(v_x_4116_);
v___x_4128_ = lean_box(0);
v_isShared_4129_ = v_isSharedCheck_4133_;
goto v_resetjp_4127_;
}
v_resetjp_4127_:
{
lean_object* v___x_4131_; 
if (v_isShared_4129_ == 0)
{
lean_ctor_set_tag(v___x_4128_, 0);
v___x_4131_ = v___x_4128_;
goto v_reusejp_4130_;
}
else
{
lean_object* v_reuseFailAlloc_4132_; 
v_reuseFailAlloc_4132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4132_, 0, v_a_4126_);
v___x_4131_ = v_reuseFailAlloc_4132_;
goto v_reusejp_4130_;
}
v_reusejp_4130_:
{
return v___x_4131_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3_spec__5___redArg___boxed(lean_object* v_x_4134_, lean_object* v___y_4135_){
_start:
{
lean_object* v_res_4136_; 
v_res_4136_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3_spec__5___redArg(v_x_4134_);
return v_res_4136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3_spec__4___redArg(lean_object* v_oldTraces_4137_, lean_object* v_data_4138_, lean_object* v_ref_4139_, lean_object* v_msg_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_){
_start:
{
lean_object* v_fileName_4146_; lean_object* v_fileMap_4147_; lean_object* v_options_4148_; lean_object* v_currRecDepth_4149_; lean_object* v_maxRecDepth_4150_; lean_object* v_ref_4151_; lean_object* v_currNamespace_4152_; lean_object* v_openDecls_4153_; lean_object* v_initHeartbeats_4154_; lean_object* v_maxHeartbeats_4155_; lean_object* v_quotContext_4156_; lean_object* v_currMacroScope_4157_; uint8_t v_diag_4158_; lean_object* v_cancelTk_x3f_4159_; uint8_t v_suppressElabErrors_4160_; lean_object* v_inheritedTraceOptions_4161_; lean_object* v___x_4163_; uint8_t v_isShared_4164_; uint8_t v_isSharedCheck_4216_; 
v_fileName_4146_ = lean_ctor_get(v___y_4143_, 0);
v_fileMap_4147_ = lean_ctor_get(v___y_4143_, 1);
v_options_4148_ = lean_ctor_get(v___y_4143_, 2);
v_currRecDepth_4149_ = lean_ctor_get(v___y_4143_, 3);
v_maxRecDepth_4150_ = lean_ctor_get(v___y_4143_, 4);
v_ref_4151_ = lean_ctor_get(v___y_4143_, 5);
v_currNamespace_4152_ = lean_ctor_get(v___y_4143_, 6);
v_openDecls_4153_ = lean_ctor_get(v___y_4143_, 7);
v_initHeartbeats_4154_ = lean_ctor_get(v___y_4143_, 8);
v_maxHeartbeats_4155_ = lean_ctor_get(v___y_4143_, 9);
v_quotContext_4156_ = lean_ctor_get(v___y_4143_, 10);
v_currMacroScope_4157_ = lean_ctor_get(v___y_4143_, 11);
v_diag_4158_ = lean_ctor_get_uint8(v___y_4143_, sizeof(void*)*14);
v_cancelTk_x3f_4159_ = lean_ctor_get(v___y_4143_, 12);
v_suppressElabErrors_4160_ = lean_ctor_get_uint8(v___y_4143_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_4161_ = lean_ctor_get(v___y_4143_, 13);
v_isSharedCheck_4216_ = !lean_is_exclusive(v___y_4143_);
if (v_isSharedCheck_4216_ == 0)
{
v___x_4163_ = v___y_4143_;
v_isShared_4164_ = v_isSharedCheck_4216_;
goto v_resetjp_4162_;
}
else
{
lean_inc(v_inheritedTraceOptions_4161_);
lean_inc(v_cancelTk_x3f_4159_);
lean_inc(v_currMacroScope_4157_);
lean_inc(v_quotContext_4156_);
lean_inc(v_maxHeartbeats_4155_);
lean_inc(v_initHeartbeats_4154_);
lean_inc(v_openDecls_4153_);
lean_inc(v_currNamespace_4152_);
lean_inc(v_ref_4151_);
lean_inc(v_maxRecDepth_4150_);
lean_inc(v_currRecDepth_4149_);
lean_inc(v_options_4148_);
lean_inc(v_fileMap_4147_);
lean_inc(v_fileName_4146_);
lean_dec(v___y_4143_);
v___x_4163_ = lean_box(0);
v_isShared_4164_ = v_isSharedCheck_4216_;
goto v_resetjp_4162_;
}
v_resetjp_4162_:
{
lean_object* v___x_4165_; lean_object* v_traceState_4166_; lean_object* v_traces_4167_; lean_object* v_ref_4168_; lean_object* v___x_4170_; 
v___x_4165_ = lean_st_ref_get(v___y_4144_);
v_traceState_4166_ = lean_ctor_get(v___x_4165_, 4);
lean_inc_ref(v_traceState_4166_);
lean_dec(v___x_4165_);
v_traces_4167_ = lean_ctor_get(v_traceState_4166_, 0);
lean_inc_ref(v_traces_4167_);
lean_dec_ref(v_traceState_4166_);
v_ref_4168_ = l_Lean_replaceRef(v_ref_4139_, v_ref_4151_);
lean_dec(v_ref_4151_);
if (v_isShared_4164_ == 0)
{
lean_ctor_set(v___x_4163_, 5, v_ref_4168_);
v___x_4170_ = v___x_4163_;
goto v_reusejp_4169_;
}
else
{
lean_object* v_reuseFailAlloc_4215_; 
v_reuseFailAlloc_4215_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_4215_, 0, v_fileName_4146_);
lean_ctor_set(v_reuseFailAlloc_4215_, 1, v_fileMap_4147_);
lean_ctor_set(v_reuseFailAlloc_4215_, 2, v_options_4148_);
lean_ctor_set(v_reuseFailAlloc_4215_, 3, v_currRecDepth_4149_);
lean_ctor_set(v_reuseFailAlloc_4215_, 4, v_maxRecDepth_4150_);
lean_ctor_set(v_reuseFailAlloc_4215_, 5, v_ref_4168_);
lean_ctor_set(v_reuseFailAlloc_4215_, 6, v_currNamespace_4152_);
lean_ctor_set(v_reuseFailAlloc_4215_, 7, v_openDecls_4153_);
lean_ctor_set(v_reuseFailAlloc_4215_, 8, v_initHeartbeats_4154_);
lean_ctor_set(v_reuseFailAlloc_4215_, 9, v_maxHeartbeats_4155_);
lean_ctor_set(v_reuseFailAlloc_4215_, 10, v_quotContext_4156_);
lean_ctor_set(v_reuseFailAlloc_4215_, 11, v_currMacroScope_4157_);
lean_ctor_set(v_reuseFailAlloc_4215_, 12, v_cancelTk_x3f_4159_);
lean_ctor_set(v_reuseFailAlloc_4215_, 13, v_inheritedTraceOptions_4161_);
lean_ctor_set_uint8(v_reuseFailAlloc_4215_, sizeof(void*)*14, v_diag_4158_);
lean_ctor_set_uint8(v_reuseFailAlloc_4215_, sizeof(void*)*14 + 1, v_suppressElabErrors_4160_);
v___x_4170_ = v_reuseFailAlloc_4215_;
goto v_reusejp_4169_;
}
v_reusejp_4169_:
{
lean_object* v___x_4171_; size_t v_sz_4172_; size_t v___x_4173_; lean_object* v___x_4174_; lean_object* v_msg_4175_; lean_object* v___x_4176_; lean_object* v_a_4177_; lean_object* v___x_4179_; uint8_t v_isShared_4180_; uint8_t v_isSharedCheck_4214_; 
v___x_4171_ = l_Lean_PersistentArray_toArray___redArg(v_traces_4167_);
lean_dec_ref(v_traces_4167_);
v_sz_4172_ = lean_array_size(v___x_4171_);
v___x_4173_ = ((size_t)0ULL);
v___x_4174_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__4_spec__5(v_sz_4172_, v___x_4173_, v___x_4171_);
v_msg_4175_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_4175_, 0, v_data_4138_);
lean_ctor_set(v_msg_4175_, 1, v_msg_4140_);
lean_ctor_set(v_msg_4175_, 2, v___x_4174_);
v___x_4176_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1_spec__1(v_msg_4175_, v___y_4141_, v___y_4142_, v___x_4170_, v___y_4144_);
lean_dec_ref(v___x_4170_);
v_a_4177_ = lean_ctor_get(v___x_4176_, 0);
v_isSharedCheck_4214_ = !lean_is_exclusive(v___x_4176_);
if (v_isSharedCheck_4214_ == 0)
{
v___x_4179_ = v___x_4176_;
v_isShared_4180_ = v_isSharedCheck_4214_;
goto v_resetjp_4178_;
}
else
{
lean_inc(v_a_4177_);
lean_dec(v___x_4176_);
v___x_4179_ = lean_box(0);
v_isShared_4180_ = v_isSharedCheck_4214_;
goto v_resetjp_4178_;
}
v_resetjp_4178_:
{
lean_object* v___x_4181_; lean_object* v_traceState_4182_; lean_object* v_env_4183_; lean_object* v_nextMacroScope_4184_; lean_object* v_ngen_4185_; lean_object* v_auxDeclNGen_4186_; lean_object* v_cache_4187_; lean_object* v_messages_4188_; lean_object* v_infoState_4189_; lean_object* v_snapshotTasks_4190_; lean_object* v___x_4192_; uint8_t v_isShared_4193_; uint8_t v_isSharedCheck_4213_; 
v___x_4181_ = lean_st_ref_take(v___y_4144_);
v_traceState_4182_ = lean_ctor_get(v___x_4181_, 4);
v_env_4183_ = lean_ctor_get(v___x_4181_, 0);
v_nextMacroScope_4184_ = lean_ctor_get(v___x_4181_, 1);
v_ngen_4185_ = lean_ctor_get(v___x_4181_, 2);
v_auxDeclNGen_4186_ = lean_ctor_get(v___x_4181_, 3);
v_cache_4187_ = lean_ctor_get(v___x_4181_, 5);
v_messages_4188_ = lean_ctor_get(v___x_4181_, 6);
v_infoState_4189_ = lean_ctor_get(v___x_4181_, 7);
v_snapshotTasks_4190_ = lean_ctor_get(v___x_4181_, 8);
v_isSharedCheck_4213_ = !lean_is_exclusive(v___x_4181_);
if (v_isSharedCheck_4213_ == 0)
{
v___x_4192_ = v___x_4181_;
v_isShared_4193_ = v_isSharedCheck_4213_;
goto v_resetjp_4191_;
}
else
{
lean_inc(v_snapshotTasks_4190_);
lean_inc(v_infoState_4189_);
lean_inc(v_messages_4188_);
lean_inc(v_cache_4187_);
lean_inc(v_traceState_4182_);
lean_inc(v_auxDeclNGen_4186_);
lean_inc(v_ngen_4185_);
lean_inc(v_nextMacroScope_4184_);
lean_inc(v_env_4183_);
lean_dec(v___x_4181_);
v___x_4192_ = lean_box(0);
v_isShared_4193_ = v_isSharedCheck_4213_;
goto v_resetjp_4191_;
}
v_resetjp_4191_:
{
uint64_t v_tid_4194_; lean_object* v___x_4196_; uint8_t v_isShared_4197_; uint8_t v_isSharedCheck_4211_; 
v_tid_4194_ = lean_ctor_get_uint64(v_traceState_4182_, sizeof(void*)*1);
v_isSharedCheck_4211_ = !lean_is_exclusive(v_traceState_4182_);
if (v_isSharedCheck_4211_ == 0)
{
lean_object* v_unused_4212_; 
v_unused_4212_ = lean_ctor_get(v_traceState_4182_, 0);
lean_dec(v_unused_4212_);
v___x_4196_ = v_traceState_4182_;
v_isShared_4197_ = v_isSharedCheck_4211_;
goto v_resetjp_4195_;
}
else
{
lean_dec(v_traceState_4182_);
v___x_4196_ = lean_box(0);
v_isShared_4197_ = v_isSharedCheck_4211_;
goto v_resetjp_4195_;
}
v_resetjp_4195_:
{
lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4201_; 
v___x_4198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4198_, 0, v_ref_4139_);
lean_ctor_set(v___x_4198_, 1, v_a_4177_);
v___x_4199_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_4137_, v___x_4198_);
if (v_isShared_4197_ == 0)
{
lean_ctor_set(v___x_4196_, 0, v___x_4199_);
v___x_4201_ = v___x_4196_;
goto v_reusejp_4200_;
}
else
{
lean_object* v_reuseFailAlloc_4210_; 
v_reuseFailAlloc_4210_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4210_, 0, v___x_4199_);
lean_ctor_set_uint64(v_reuseFailAlloc_4210_, sizeof(void*)*1, v_tid_4194_);
v___x_4201_ = v_reuseFailAlloc_4210_;
goto v_reusejp_4200_;
}
v_reusejp_4200_:
{
lean_object* v___x_4203_; 
if (v_isShared_4193_ == 0)
{
lean_ctor_set(v___x_4192_, 4, v___x_4201_);
v___x_4203_ = v___x_4192_;
goto v_reusejp_4202_;
}
else
{
lean_object* v_reuseFailAlloc_4209_; 
v_reuseFailAlloc_4209_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4209_, 0, v_env_4183_);
lean_ctor_set(v_reuseFailAlloc_4209_, 1, v_nextMacroScope_4184_);
lean_ctor_set(v_reuseFailAlloc_4209_, 2, v_ngen_4185_);
lean_ctor_set(v_reuseFailAlloc_4209_, 3, v_auxDeclNGen_4186_);
lean_ctor_set(v_reuseFailAlloc_4209_, 4, v___x_4201_);
lean_ctor_set(v_reuseFailAlloc_4209_, 5, v_cache_4187_);
lean_ctor_set(v_reuseFailAlloc_4209_, 6, v_messages_4188_);
lean_ctor_set(v_reuseFailAlloc_4209_, 7, v_infoState_4189_);
lean_ctor_set(v_reuseFailAlloc_4209_, 8, v_snapshotTasks_4190_);
v___x_4203_ = v_reuseFailAlloc_4209_;
goto v_reusejp_4202_;
}
v_reusejp_4202_:
{
lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4207_; 
v___x_4204_ = lean_st_ref_set(v___y_4144_, v___x_4203_);
v___x_4205_ = lean_box(0);
if (v_isShared_4180_ == 0)
{
lean_ctor_set(v___x_4179_, 0, v___x_4205_);
v___x_4207_ = v___x_4179_;
goto v_reusejp_4206_;
}
else
{
lean_object* v_reuseFailAlloc_4208_; 
v_reuseFailAlloc_4208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4208_, 0, v___x_4205_);
v___x_4207_ = v_reuseFailAlloc_4208_;
goto v_reusejp_4206_;
}
v_reusejp_4206_:
{
return v___x_4207_;
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3_spec__4___redArg___boxed(lean_object* v_oldTraces_4217_, lean_object* v_data_4218_, lean_object* v_ref_4219_, lean_object* v_msg_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_){
_start:
{
lean_object* v_res_4226_; 
v_res_4226_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3_spec__4___redArg(v_oldTraces_4217_, v_data_4218_, v_ref_4219_, v_msg_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_);
lean_dec(v___y_4224_);
lean_dec(v___y_4222_);
lean_dec_ref(v___y_4221_);
return v_res_4226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3(lean_object* v_cls_4227_, uint8_t v_collapsed_4228_, lean_object* v_tag_4229_, lean_object* v_opts_4230_, uint8_t v_clsEnabled_4231_, lean_object* v_oldTraces_4232_, lean_object* v_msg_4233_, lean_object* v_resStartStop_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_){
_start:
{
lean_object* v_fst_4242_; lean_object* v_snd_4243_; lean_object* v___x_4245_; uint8_t v_isShared_4246_; uint8_t v_isSharedCheck_4341_; 
v_fst_4242_ = lean_ctor_get(v_resStartStop_4234_, 0);
v_snd_4243_ = lean_ctor_get(v_resStartStop_4234_, 1);
v_isSharedCheck_4341_ = !lean_is_exclusive(v_resStartStop_4234_);
if (v_isSharedCheck_4341_ == 0)
{
v___x_4245_ = v_resStartStop_4234_;
v_isShared_4246_ = v_isSharedCheck_4341_;
goto v_resetjp_4244_;
}
else
{
lean_inc(v_snd_4243_);
lean_inc(v_fst_4242_);
lean_dec(v_resStartStop_4234_);
v___x_4245_ = lean_box(0);
v_isShared_4246_ = v_isSharedCheck_4341_;
goto v_resetjp_4244_;
}
v_resetjp_4244_:
{
lean_object* v___y_4248_; lean_object* v___y_4249_; lean_object* v_data_4250_; lean_object* v_fst_4261_; lean_object* v_snd_4262_; lean_object* v___x_4264_; uint8_t v_isShared_4265_; uint8_t v_isSharedCheck_4340_; 
v_fst_4261_ = lean_ctor_get(v_snd_4243_, 0);
v_snd_4262_ = lean_ctor_get(v_snd_4243_, 1);
v_isSharedCheck_4340_ = !lean_is_exclusive(v_snd_4243_);
if (v_isSharedCheck_4340_ == 0)
{
v___x_4264_ = v_snd_4243_;
v_isShared_4265_ = v_isSharedCheck_4340_;
goto v_resetjp_4263_;
}
else
{
lean_inc(v_snd_4262_);
lean_inc(v_fst_4261_);
lean_dec(v_snd_4243_);
v___x_4264_ = lean_box(0);
v_isShared_4265_ = v_isSharedCheck_4340_;
goto v_resetjp_4263_;
}
v___jp_4247_:
{
lean_object* v___x_4251_; 
v___x_4251_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3_spec__4___redArg(v_oldTraces_4232_, v_data_4250_, v___y_4248_, v___y_4249_, v___y_4237_, v___y_4238_, v___y_4239_, v___y_4240_);
lean_dec(v___y_4240_);
lean_dec(v___y_4238_);
lean_dec_ref(v___y_4237_);
if (lean_obj_tag(v___x_4251_) == 0)
{
lean_object* v___x_4252_; 
lean_dec_ref(v___x_4251_);
v___x_4252_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3_spec__5___redArg(v_fst_4242_);
return v___x_4252_;
}
else
{
lean_object* v_a_4253_; lean_object* v___x_4255_; uint8_t v_isShared_4256_; uint8_t v_isSharedCheck_4260_; 
lean_dec(v_fst_4242_);
v_a_4253_ = lean_ctor_get(v___x_4251_, 0);
v_isSharedCheck_4260_ = !lean_is_exclusive(v___x_4251_);
if (v_isSharedCheck_4260_ == 0)
{
v___x_4255_ = v___x_4251_;
v_isShared_4256_ = v_isSharedCheck_4260_;
goto v_resetjp_4254_;
}
else
{
lean_inc(v_a_4253_);
lean_dec(v___x_4251_);
v___x_4255_ = lean_box(0);
v_isShared_4256_ = v_isSharedCheck_4260_;
goto v_resetjp_4254_;
}
v_resetjp_4254_:
{
lean_object* v___x_4258_; 
if (v_isShared_4256_ == 0)
{
v___x_4258_ = v___x_4255_;
goto v_reusejp_4257_;
}
else
{
lean_object* v_reuseFailAlloc_4259_; 
v_reuseFailAlloc_4259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4259_, 0, v_a_4253_);
v___x_4258_ = v_reuseFailAlloc_4259_;
goto v_reusejp_4257_;
}
v_reusejp_4257_:
{
return v___x_4258_;
}
}
}
}
v_resetjp_4263_:
{
lean_object* v___x_4266_; uint8_t v___x_4267_; lean_object* v___y_4269_; lean_object* v_a_4270_; uint8_t v___y_4294_; double v___y_4325_; 
v___x_4266_ = l_Lean_trace_profiler;
v___x_4267_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2(v_opts_4230_, v___x_4266_);
if (v___x_4267_ == 0)
{
v___y_4294_ = v___x_4267_;
goto v___jp_4293_;
}
else
{
lean_object* v___x_4330_; uint8_t v___x_4331_; 
v___x_4330_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4331_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2(v_opts_4230_, v___x_4330_);
if (v___x_4331_ == 0)
{
lean_object* v___x_4332_; lean_object* v___x_4333_; double v___x_4334_; double v___x_4335_; double v___x_4336_; 
v___x_4332_ = l_Lean_trace_profiler_threshold;
v___x_4333_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__6(v_opts_4230_, v___x_4332_);
v___x_4334_ = lean_float_of_nat(v___x_4333_);
v___x_4335_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__4);
v___x_4336_ = lean_float_div(v___x_4334_, v___x_4335_);
v___y_4325_ = v___x_4336_;
goto v___jp_4324_;
}
else
{
lean_object* v___x_4337_; lean_object* v___x_4338_; double v___x_4339_; 
v___x_4337_ = l_Lean_trace_profiler_threshold;
v___x_4338_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__6(v_opts_4230_, v___x_4337_);
v___x_4339_ = lean_float_of_nat(v___x_4338_);
v___y_4325_ = v___x_4339_;
goto v___jp_4324_;
}
}
v___jp_4268_:
{
uint8_t v_result_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4276_; 
v_result_4271_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__3(v_fst_4242_);
v___x_4272_ = l_Lean_TraceResult_toEmoji(v_result_4271_);
v___x_4273_ = l_Lean_stringToMessageData(v___x_4272_);
v___x_4274_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__1);
if (v_isShared_4265_ == 0)
{
lean_ctor_set_tag(v___x_4264_, 7);
lean_ctor_set(v___x_4264_, 1, v___x_4274_);
lean_ctor_set(v___x_4264_, 0, v___x_4273_);
v___x_4276_ = v___x_4264_;
goto v_reusejp_4275_;
}
else
{
lean_object* v_reuseFailAlloc_4287_; 
v_reuseFailAlloc_4287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4287_, 0, v___x_4273_);
lean_ctor_set(v_reuseFailAlloc_4287_, 1, v___x_4274_);
v___x_4276_ = v_reuseFailAlloc_4287_;
goto v_reusejp_4275_;
}
v_reusejp_4275_:
{
lean_object* v_m_4278_; 
if (v_isShared_4246_ == 0)
{
lean_ctor_set_tag(v___x_4245_, 7);
lean_ctor_set(v___x_4245_, 1, v_a_4270_);
lean_ctor_set(v___x_4245_, 0, v___x_4276_);
v_m_4278_ = v___x_4245_;
goto v_reusejp_4277_;
}
else
{
lean_object* v_reuseFailAlloc_4286_; 
v_reuseFailAlloc_4286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4286_, 0, v___x_4276_);
lean_ctor_set(v_reuseFailAlloc_4286_, 1, v_a_4270_);
v_m_4278_ = v_reuseFailAlloc_4286_;
goto v_reusejp_4277_;
}
v_reusejp_4277_:
{
lean_object* v___x_4279_; lean_object* v___x_4280_; double v___x_4281_; lean_object* v_data_4282_; 
v___x_4279_ = lean_box(v_result_4271_);
v___x_4280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4280_, 0, v___x_4279_);
v___x_4281_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__0);
lean_inc_ref(v_tag_4229_);
lean_inc_ref(v___x_4280_);
lean_inc(v_cls_4227_);
v_data_4282_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4282_, 0, v_cls_4227_);
lean_ctor_set(v_data_4282_, 1, v___x_4280_);
lean_ctor_set(v_data_4282_, 2, v_tag_4229_);
lean_ctor_set_float(v_data_4282_, sizeof(void*)*3, v___x_4281_);
lean_ctor_set_float(v_data_4282_, sizeof(void*)*3 + 8, v___x_4281_);
lean_ctor_set_uint8(v_data_4282_, sizeof(void*)*3 + 16, v_collapsed_4228_);
if (v___x_4267_ == 0)
{
lean_dec_ref(v___x_4280_);
lean_dec(v_snd_4262_);
lean_dec(v_fst_4261_);
lean_dec_ref(v_tag_4229_);
lean_dec(v_cls_4227_);
v___y_4248_ = v___y_4269_;
v___y_4249_ = v_m_4278_;
v_data_4250_ = v_data_4282_;
goto v___jp_4247_;
}
else
{
lean_object* v_data_4283_; double v___x_4284_; double v___x_4285_; 
lean_dec_ref(v_data_4282_);
v_data_4283_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4283_, 0, v_cls_4227_);
lean_ctor_set(v_data_4283_, 1, v___x_4280_);
lean_ctor_set(v_data_4283_, 2, v_tag_4229_);
v___x_4284_ = lean_unbox_float(v_fst_4261_);
lean_dec(v_fst_4261_);
lean_ctor_set_float(v_data_4283_, sizeof(void*)*3, v___x_4284_);
v___x_4285_ = lean_unbox_float(v_snd_4262_);
lean_dec(v_snd_4262_);
lean_ctor_set_float(v_data_4283_, sizeof(void*)*3 + 8, v___x_4285_);
lean_ctor_set_uint8(v_data_4283_, sizeof(void*)*3 + 16, v_collapsed_4228_);
v___y_4248_ = v___y_4269_;
v___y_4249_ = v_m_4278_;
v_data_4250_ = v_data_4283_;
goto v___jp_4247_;
}
}
}
}
v___jp_4288_:
{
lean_object* v_ref_4289_; lean_object* v___x_4290_; 
v_ref_4289_ = lean_ctor_get(v___y_4239_, 5);
lean_inc(v___y_4240_);
lean_inc_ref(v___y_4239_);
lean_inc(v___y_4238_);
lean_inc_ref(v___y_4237_);
lean_inc(v_fst_4242_);
v___x_4290_ = lean_apply_8(v_msg_4233_, v_fst_4242_, v___y_4235_, v___y_4236_, v___y_4237_, v___y_4238_, v___y_4239_, v___y_4240_, lean_box(0));
if (lean_obj_tag(v___x_4290_) == 0)
{
lean_object* v_a_4291_; 
v_a_4291_ = lean_ctor_get(v___x_4290_, 0);
lean_inc(v_a_4291_);
lean_dec_ref(v___x_4290_);
lean_inc(v_ref_4289_);
v___y_4269_ = v_ref_4289_;
v_a_4270_ = v_a_4291_;
goto v___jp_4268_;
}
else
{
lean_object* v___x_4292_; 
lean_dec_ref(v___x_4290_);
v___x_4292_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__3);
lean_inc(v_ref_4289_);
v___y_4269_ = v_ref_4289_;
v_a_4270_ = v___x_4292_;
goto v___jp_4268_;
}
}
v___jp_4293_:
{
if (v_clsEnabled_4231_ == 0)
{
if (v___y_4294_ == 0)
{
lean_object* v___x_4295_; lean_object* v_traceState_4296_; lean_object* v_env_4297_; lean_object* v_nextMacroScope_4298_; lean_object* v_ngen_4299_; lean_object* v_auxDeclNGen_4300_; lean_object* v_cache_4301_; lean_object* v_messages_4302_; lean_object* v_infoState_4303_; lean_object* v_snapshotTasks_4304_; lean_object* v___x_4306_; uint8_t v_isShared_4307_; uint8_t v_isSharedCheck_4323_; 
lean_del_object(v___x_4264_);
lean_dec(v_snd_4262_);
lean_dec(v_fst_4261_);
lean_del_object(v___x_4245_);
lean_dec_ref(v___y_4239_);
lean_dec(v___y_4238_);
lean_dec_ref(v___y_4237_);
lean_dec(v___y_4236_);
lean_dec_ref(v___y_4235_);
lean_dec_ref(v_msg_4233_);
lean_dec_ref(v_tag_4229_);
lean_dec(v_cls_4227_);
v___x_4295_ = lean_st_ref_take(v___y_4240_);
v_traceState_4296_ = lean_ctor_get(v___x_4295_, 4);
v_env_4297_ = lean_ctor_get(v___x_4295_, 0);
v_nextMacroScope_4298_ = lean_ctor_get(v___x_4295_, 1);
v_ngen_4299_ = lean_ctor_get(v___x_4295_, 2);
v_auxDeclNGen_4300_ = lean_ctor_get(v___x_4295_, 3);
v_cache_4301_ = lean_ctor_get(v___x_4295_, 5);
v_messages_4302_ = lean_ctor_get(v___x_4295_, 6);
v_infoState_4303_ = lean_ctor_get(v___x_4295_, 7);
v_snapshotTasks_4304_ = lean_ctor_get(v___x_4295_, 8);
v_isSharedCheck_4323_ = !lean_is_exclusive(v___x_4295_);
if (v_isSharedCheck_4323_ == 0)
{
v___x_4306_ = v___x_4295_;
v_isShared_4307_ = v_isSharedCheck_4323_;
goto v_resetjp_4305_;
}
else
{
lean_inc(v_snapshotTasks_4304_);
lean_inc(v_infoState_4303_);
lean_inc(v_messages_4302_);
lean_inc(v_cache_4301_);
lean_inc(v_traceState_4296_);
lean_inc(v_auxDeclNGen_4300_);
lean_inc(v_ngen_4299_);
lean_inc(v_nextMacroScope_4298_);
lean_inc(v_env_4297_);
lean_dec(v___x_4295_);
v___x_4306_ = lean_box(0);
v_isShared_4307_ = v_isSharedCheck_4323_;
goto v_resetjp_4305_;
}
v_resetjp_4305_:
{
uint64_t v_tid_4308_; lean_object* v_traces_4309_; lean_object* v___x_4311_; uint8_t v_isShared_4312_; uint8_t v_isSharedCheck_4322_; 
v_tid_4308_ = lean_ctor_get_uint64(v_traceState_4296_, sizeof(void*)*1);
v_traces_4309_ = lean_ctor_get(v_traceState_4296_, 0);
v_isSharedCheck_4322_ = !lean_is_exclusive(v_traceState_4296_);
if (v_isSharedCheck_4322_ == 0)
{
v___x_4311_ = v_traceState_4296_;
v_isShared_4312_ = v_isSharedCheck_4322_;
goto v_resetjp_4310_;
}
else
{
lean_inc(v_traces_4309_);
lean_dec(v_traceState_4296_);
v___x_4311_ = lean_box(0);
v_isShared_4312_ = v_isSharedCheck_4322_;
goto v_resetjp_4310_;
}
v_resetjp_4310_:
{
lean_object* v___x_4313_; lean_object* v___x_4315_; 
v___x_4313_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_4232_, v_traces_4309_);
lean_dec_ref(v_traces_4309_);
if (v_isShared_4312_ == 0)
{
lean_ctor_set(v___x_4311_, 0, v___x_4313_);
v___x_4315_ = v___x_4311_;
goto v_reusejp_4314_;
}
else
{
lean_object* v_reuseFailAlloc_4321_; 
v_reuseFailAlloc_4321_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4321_, 0, v___x_4313_);
lean_ctor_set_uint64(v_reuseFailAlloc_4321_, sizeof(void*)*1, v_tid_4308_);
v___x_4315_ = v_reuseFailAlloc_4321_;
goto v_reusejp_4314_;
}
v_reusejp_4314_:
{
lean_object* v___x_4317_; 
if (v_isShared_4307_ == 0)
{
lean_ctor_set(v___x_4306_, 4, v___x_4315_);
v___x_4317_ = v___x_4306_;
goto v_reusejp_4316_;
}
else
{
lean_object* v_reuseFailAlloc_4320_; 
v_reuseFailAlloc_4320_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4320_, 0, v_env_4297_);
lean_ctor_set(v_reuseFailAlloc_4320_, 1, v_nextMacroScope_4298_);
lean_ctor_set(v_reuseFailAlloc_4320_, 2, v_ngen_4299_);
lean_ctor_set(v_reuseFailAlloc_4320_, 3, v_auxDeclNGen_4300_);
lean_ctor_set(v_reuseFailAlloc_4320_, 4, v___x_4315_);
lean_ctor_set(v_reuseFailAlloc_4320_, 5, v_cache_4301_);
lean_ctor_set(v_reuseFailAlloc_4320_, 6, v_messages_4302_);
lean_ctor_set(v_reuseFailAlloc_4320_, 7, v_infoState_4303_);
lean_ctor_set(v_reuseFailAlloc_4320_, 8, v_snapshotTasks_4304_);
v___x_4317_ = v_reuseFailAlloc_4320_;
goto v_reusejp_4316_;
}
v_reusejp_4316_:
{
lean_object* v___x_4318_; lean_object* v___x_4319_; 
v___x_4318_ = lean_st_ref_set(v___y_4240_, v___x_4317_);
lean_dec(v___y_4240_);
v___x_4319_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3_spec__5___redArg(v_fst_4242_);
return v___x_4319_;
}
}
}
}
}
else
{
goto v___jp_4288_;
}
}
else
{
goto v___jp_4288_;
}
}
v___jp_4324_:
{
double v___x_4326_; double v___x_4327_; double v___x_4328_; uint8_t v___x_4329_; 
v___x_4326_ = lean_unbox_float(v_snd_4262_);
v___x_4327_ = lean_unbox_float(v_fst_4261_);
v___x_4328_ = lean_float_sub(v___x_4326_, v___x_4327_);
v___x_4329_ = lean_float_decLt(v___y_4325_, v___x_4328_);
v___y_4294_ = v___x_4329_;
goto v___jp_4293_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___boxed(lean_object* v_cls_4342_, lean_object* v_collapsed_4343_, lean_object* v_tag_4344_, lean_object* v_opts_4345_, lean_object* v_clsEnabled_4346_, lean_object* v_oldTraces_4347_, lean_object* v_msg_4348_, lean_object* v_resStartStop_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_){
_start:
{
uint8_t v_collapsed_boxed_4357_; uint8_t v_clsEnabled_boxed_4358_; lean_object* v_res_4359_; 
v_collapsed_boxed_4357_ = lean_unbox(v_collapsed_4343_);
v_clsEnabled_boxed_4358_ = lean_unbox(v_clsEnabled_4346_);
v_res_4359_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3(v_cls_4342_, v_collapsed_boxed_4357_, v_tag_4344_, v_opts_4345_, v_clsEnabled_boxed_4358_, v_oldTraces_4347_, v_msg_4348_, v_resStartStop_4349_, v___y_4350_, v___y_4351_, v___y_4352_, v___y_4353_, v___y_4354_, v___y_4355_);
lean_dec_ref(v_opts_4345_);
return v_res_4359_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4361_; lean_object* v___x_4362_; 
v___x_4361_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__0));
v___x_4362_ = l_Lean_stringToMessageData(v___x_4361_);
return v___x_4362_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4364_; lean_object* v___x_4365_; 
v___x_4364_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__2));
v___x_4365_ = l_Lean_stringToMessageData(v___x_4364_);
return v___x_4365_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4367_; lean_object* v___x_4368_; 
v___x_4367_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__4));
v___x_4368_ = l_Lean_stringToMessageData(v___x_4367_);
return v___x_4368_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0(lean_object* v_a_4369_, lean_object* v___x_4370_, lean_object* v_x_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_){
_start:
{
if (lean_obj_tag(v_x_4371_) == 0)
{
lean_object* v_a_4379_; lean_object* v___x_4381_; uint8_t v_isShared_4382_; uint8_t v_isSharedCheck_4394_; 
lean_dec_ref(v___x_4370_);
v_a_4379_ = lean_ctor_get(v_x_4371_, 0);
v_isSharedCheck_4394_ = !lean_is_exclusive(v_x_4371_);
if (v_isSharedCheck_4394_ == 0)
{
v___x_4381_ = v_x_4371_;
v_isShared_4382_ = v_isSharedCheck_4394_;
goto v_resetjp_4380_;
}
else
{
lean_inc(v_a_4379_);
lean_dec(v_x_4371_);
v___x_4381_ = lean_box(0);
v_isShared_4382_ = v_isSharedCheck_4394_;
goto v_resetjp_4380_;
}
v_resetjp_4380_:
{
lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4392_; 
v___x_4383_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__1);
v___x_4384_ = l_Lean_LocalDecl_userName(v_a_4369_);
v___x_4385_ = l_Lean_MessageData_ofName(v___x_4384_);
v___x_4386_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4386_, 0, v___x_4383_);
lean_ctor_set(v___x_4386_, 1, v___x_4385_);
v___x_4387_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__3);
v___x_4388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4388_, 0, v___x_4386_);
lean_ctor_set(v___x_4388_, 1, v___x_4387_);
v___x_4389_ = l_Lean_Exception_toMessageData(v_a_4379_);
v___x_4390_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4390_, 0, v___x_4388_);
lean_ctor_set(v___x_4390_, 1, v___x_4389_);
if (v_isShared_4382_ == 0)
{
lean_ctor_set(v___x_4381_, 0, v___x_4390_);
v___x_4392_ = v___x_4381_;
goto v_reusejp_4391_;
}
else
{
lean_object* v_reuseFailAlloc_4393_; 
v_reuseFailAlloc_4393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4393_, 0, v___x_4390_);
v___x_4392_ = v_reuseFailAlloc_4393_;
goto v_reusejp_4391_;
}
v_reusejp_4391_:
{
return v___x_4392_;
}
}
}
else
{
lean_object* v_a_4395_; lean_object* v___x_4397_; uint8_t v_isShared_4398_; uint8_t v_isSharedCheck_4424_; 
v_a_4395_ = lean_ctor_get(v_x_4371_, 0);
v_isSharedCheck_4424_ = !lean_is_exclusive(v_x_4371_);
if (v_isSharedCheck_4424_ == 0)
{
v___x_4397_ = v_x_4371_;
v_isShared_4398_ = v_isSharedCheck_4424_;
goto v_resetjp_4396_;
}
else
{
lean_inc(v_a_4395_);
lean_dec(v_x_4371_);
v___x_4397_ = lean_box(0);
v_isShared_4398_ = v_isSharedCheck_4424_;
goto v_resetjp_4396_;
}
v_resetjp_4396_:
{
if (lean_obj_tag(v_a_4395_) == 0)
{
lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4406_; 
lean_dec_ref(v_a_4395_);
lean_dec_ref(v___x_4370_);
v___x_4399_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__1);
v___x_4400_ = l_Lean_LocalDecl_userName(v_a_4369_);
v___x_4401_ = l_Lean_MessageData_ofName(v___x_4400_);
v___x_4402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4402_, 0, v___x_4399_);
lean_ctor_set(v___x_4402_, 1, v___x_4401_);
v___x_4403_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__5);
v___x_4404_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4404_, 0, v___x_4402_);
lean_ctor_set(v___x_4404_, 1, v___x_4403_);
if (v_isShared_4398_ == 0)
{
lean_ctor_set_tag(v___x_4397_, 0);
lean_ctor_set(v___x_4397_, 0, v___x_4404_);
v___x_4406_ = v___x_4397_;
goto v_reusejp_4405_;
}
else
{
lean_object* v_reuseFailAlloc_4407_; 
v_reuseFailAlloc_4407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4407_, 0, v___x_4404_);
v___x_4406_ = v_reuseFailAlloc_4407_;
goto v_reusejp_4405_;
}
v_reusejp_4405_:
{
return v___x_4406_;
}
}
else
{
lean_object* v_e_x27_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4422_; 
v_e_x27_4408_ = lean_ctor_get(v_a_4395_, 0);
lean_inc_ref(v_e_x27_4408_);
lean_dec_ref(v_a_4395_);
v___x_4409_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__1);
v___x_4410_ = l_Lean_LocalDecl_userName(v_a_4369_);
v___x_4411_ = l_Lean_MessageData_ofName(v___x_4410_);
v___x_4412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4412_, 0, v___x_4409_);
lean_ctor_set(v___x_4412_, 1, v___x_4411_);
v___x_4413_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__5, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__5_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__5);
v___x_4414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4414_, 0, v___x_4412_);
lean_ctor_set(v___x_4414_, 1, v___x_4413_);
v___x_4415_ = l_Lean_indentExpr(v___x_4370_);
v___x_4416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4416_, 0, v___x_4414_);
lean_ctor_set(v___x_4416_, 1, v___x_4415_);
v___x_4417_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7);
v___x_4418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4418_, 0, v___x_4416_);
lean_ctor_set(v___x_4418_, 1, v___x_4417_);
v___x_4419_ = l_Lean_indentExpr(v_e_x27_4408_);
v___x_4420_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4420_, 0, v___x_4418_);
lean_ctor_set(v___x_4420_, 1, v___x_4419_);
if (v_isShared_4398_ == 0)
{
lean_ctor_set_tag(v___x_4397_, 0);
lean_ctor_set(v___x_4397_, 0, v___x_4420_);
v___x_4422_ = v___x_4397_;
goto v_reusejp_4421_;
}
else
{
lean_object* v_reuseFailAlloc_4423_; 
v_reuseFailAlloc_4423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4423_, 0, v___x_4420_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___boxed(lean_object* v_a_4425_, lean_object* v___x_4426_, lean_object* v_x_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_){
_start:
{
lean_object* v_res_4435_; 
v_res_4435_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0(v_a_4425_, v___x_4426_, v_x_4427_, v___y_4428_, v___y_4429_, v___y_4430_, v___y_4431_, v___y_4432_, v___y_4433_);
lean_dec(v___y_4433_);
lean_dec_ref(v___y_4432_);
lean_dec(v___y_4431_);
lean_dec_ref(v___y_4430_);
lean_dec(v___y_4429_);
lean_dec_ref(v___y_4428_);
lean_dec_ref(v_a_4425_);
return v_res_4435_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4_spec__8_spec__10___redArg(lean_object* v_x_4436_, lean_object* v_x_4437_, lean_object* v_x_4438_, lean_object* v_x_4439_){
_start:
{
lean_object* v_ks_4440_; lean_object* v_vs_4441_; lean_object* v___x_4443_; uint8_t v_isShared_4444_; uint8_t v_isSharedCheck_4465_; 
v_ks_4440_ = lean_ctor_get(v_x_4436_, 0);
v_vs_4441_ = lean_ctor_get(v_x_4436_, 1);
v_isSharedCheck_4465_ = !lean_is_exclusive(v_x_4436_);
if (v_isSharedCheck_4465_ == 0)
{
v___x_4443_ = v_x_4436_;
v_isShared_4444_ = v_isSharedCheck_4465_;
goto v_resetjp_4442_;
}
else
{
lean_inc(v_vs_4441_);
lean_inc(v_ks_4440_);
lean_dec(v_x_4436_);
v___x_4443_ = lean_box(0);
v_isShared_4444_ = v_isSharedCheck_4465_;
goto v_resetjp_4442_;
}
v_resetjp_4442_:
{
lean_object* v___x_4445_; uint8_t v___x_4446_; 
v___x_4445_ = lean_array_get_size(v_ks_4440_);
v___x_4446_ = lean_nat_dec_lt(v_x_4437_, v___x_4445_);
if (v___x_4446_ == 0)
{
lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4450_; 
lean_dec(v_x_4437_);
v___x_4447_ = lean_array_push(v_ks_4440_, v_x_4438_);
v___x_4448_ = lean_array_push(v_vs_4441_, v_x_4439_);
if (v_isShared_4444_ == 0)
{
lean_ctor_set(v___x_4443_, 1, v___x_4448_);
lean_ctor_set(v___x_4443_, 0, v___x_4447_);
v___x_4450_ = v___x_4443_;
goto v_reusejp_4449_;
}
else
{
lean_object* v_reuseFailAlloc_4451_; 
v_reuseFailAlloc_4451_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4451_, 0, v___x_4447_);
lean_ctor_set(v_reuseFailAlloc_4451_, 1, v___x_4448_);
v___x_4450_ = v_reuseFailAlloc_4451_;
goto v_reusejp_4449_;
}
v_reusejp_4449_:
{
return v___x_4450_;
}
}
else
{
lean_object* v_k_x27_4452_; uint8_t v___x_4453_; 
v_k_x27_4452_ = lean_array_fget_borrowed(v_ks_4440_, v_x_4437_);
v___x_4453_ = l_Lean_instBEqMVarId_beq(v_x_4438_, v_k_x27_4452_);
if (v___x_4453_ == 0)
{
lean_object* v___x_4455_; 
if (v_isShared_4444_ == 0)
{
v___x_4455_ = v___x_4443_;
goto v_reusejp_4454_;
}
else
{
lean_object* v_reuseFailAlloc_4459_; 
v_reuseFailAlloc_4459_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4459_, 0, v_ks_4440_);
lean_ctor_set(v_reuseFailAlloc_4459_, 1, v_vs_4441_);
v___x_4455_ = v_reuseFailAlloc_4459_;
goto v_reusejp_4454_;
}
v_reusejp_4454_:
{
lean_object* v___x_4456_; lean_object* v___x_4457_; 
v___x_4456_ = lean_unsigned_to_nat(1u);
v___x_4457_ = lean_nat_add(v_x_4437_, v___x_4456_);
lean_dec(v_x_4437_);
v_x_4436_ = v___x_4455_;
v_x_4437_ = v___x_4457_;
goto _start;
}
}
else
{
lean_object* v___x_4460_; lean_object* v___x_4461_; lean_object* v___x_4463_; 
v___x_4460_ = lean_array_fset(v_ks_4440_, v_x_4437_, v_x_4438_);
v___x_4461_ = lean_array_fset(v_vs_4441_, v_x_4437_, v_x_4439_);
lean_dec(v_x_4437_);
if (v_isShared_4444_ == 0)
{
lean_ctor_set(v___x_4443_, 1, v___x_4461_);
lean_ctor_set(v___x_4443_, 0, v___x_4460_);
v___x_4463_ = v___x_4443_;
goto v_reusejp_4462_;
}
else
{
lean_object* v_reuseFailAlloc_4464_; 
v_reuseFailAlloc_4464_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4464_, 0, v___x_4460_);
lean_ctor_set(v_reuseFailAlloc_4464_, 1, v___x_4461_);
v___x_4463_ = v_reuseFailAlloc_4464_;
goto v_reusejp_4462_;
}
v_reusejp_4462_:
{
return v___x_4463_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4_spec__8___redArg(lean_object* v_n_4466_, lean_object* v_k_4467_, lean_object* v_v_4468_){
_start:
{
lean_object* v___x_4469_; lean_object* v___x_4470_; 
v___x_4469_ = lean_unsigned_to_nat(0u);
v___x_4470_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4_spec__8_spec__10___redArg(v_n_4466_, v___x_4469_, v_k_4467_, v_v_4468_);
return v___x_4470_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4___redArg___closed__0(void){
_start:
{
size_t v___x_4471_; size_t v___x_4472_; size_t v___x_4473_; 
v___x_4471_ = ((size_t)5ULL);
v___x_4472_ = ((size_t)1ULL);
v___x_4473_ = lean_usize_shift_left(v___x_4472_, v___x_4471_);
return v___x_4473_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_4474_; size_t v___x_4475_; size_t v___x_4476_; 
v___x_4474_ = ((size_t)1ULL);
v___x_4475_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4___redArg___closed__0);
v___x_4476_ = lean_usize_sub(v___x_4475_, v___x_4474_);
return v___x_4476_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_4477_; 
v___x_4477_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_4477_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4___redArg(lean_object* v_x_4478_, size_t v_x_4479_, size_t v_x_4480_, lean_object* v_x_4481_, lean_object* v_x_4482_){
_start:
{
if (lean_obj_tag(v_x_4478_) == 0)
{
lean_object* v_es_4483_; size_t v___x_4484_; size_t v___x_4485_; size_t v___x_4486_; size_t v___x_4487_; lean_object* v_j_4488_; lean_object* v___x_4489_; uint8_t v___x_4490_; 
v_es_4483_ = lean_ctor_get(v_x_4478_, 0);
v___x_4484_ = ((size_t)5ULL);
v___x_4485_ = ((size_t)1ULL);
v___x_4486_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4___redArg___closed__1);
v___x_4487_ = lean_usize_land(v_x_4479_, v___x_4486_);
v_j_4488_ = lean_usize_to_nat(v___x_4487_);
v___x_4489_ = lean_array_get_size(v_es_4483_);
v___x_4490_ = lean_nat_dec_lt(v_j_4488_, v___x_4489_);
if (v___x_4490_ == 0)
{
lean_dec(v_j_4488_);
lean_dec(v_x_4482_);
lean_dec(v_x_4481_);
return v_x_4478_;
}
else
{
lean_object* v___x_4492_; uint8_t v_isShared_4493_; uint8_t v_isSharedCheck_4527_; 
lean_inc_ref(v_es_4483_);
v_isSharedCheck_4527_ = !lean_is_exclusive(v_x_4478_);
if (v_isSharedCheck_4527_ == 0)
{
lean_object* v_unused_4528_; 
v_unused_4528_ = lean_ctor_get(v_x_4478_, 0);
lean_dec(v_unused_4528_);
v___x_4492_ = v_x_4478_;
v_isShared_4493_ = v_isSharedCheck_4527_;
goto v_resetjp_4491_;
}
else
{
lean_dec(v_x_4478_);
v___x_4492_ = lean_box(0);
v_isShared_4493_ = v_isSharedCheck_4527_;
goto v_resetjp_4491_;
}
v_resetjp_4491_:
{
lean_object* v_v_4494_; lean_object* v___x_4495_; lean_object* v_xs_x27_4496_; lean_object* v___y_4498_; 
v_v_4494_ = lean_array_fget(v_es_4483_, v_j_4488_);
v___x_4495_ = lean_box(0);
v_xs_x27_4496_ = lean_array_fset(v_es_4483_, v_j_4488_, v___x_4495_);
switch(lean_obj_tag(v_v_4494_))
{
case 0:
{
lean_object* v_key_4503_; lean_object* v_val_4504_; lean_object* v___x_4506_; uint8_t v_isShared_4507_; uint8_t v_isSharedCheck_4514_; 
v_key_4503_ = lean_ctor_get(v_v_4494_, 0);
v_val_4504_ = lean_ctor_get(v_v_4494_, 1);
v_isSharedCheck_4514_ = !lean_is_exclusive(v_v_4494_);
if (v_isSharedCheck_4514_ == 0)
{
v___x_4506_ = v_v_4494_;
v_isShared_4507_ = v_isSharedCheck_4514_;
goto v_resetjp_4505_;
}
else
{
lean_inc(v_val_4504_);
lean_inc(v_key_4503_);
lean_dec(v_v_4494_);
v___x_4506_ = lean_box(0);
v_isShared_4507_ = v_isSharedCheck_4514_;
goto v_resetjp_4505_;
}
v_resetjp_4505_:
{
uint8_t v___x_4508_; 
v___x_4508_ = l_Lean_instBEqMVarId_beq(v_x_4481_, v_key_4503_);
if (v___x_4508_ == 0)
{
lean_object* v___x_4509_; lean_object* v___x_4510_; 
lean_del_object(v___x_4506_);
v___x_4509_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_4503_, v_val_4504_, v_x_4481_, v_x_4482_);
v___x_4510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4510_, 0, v___x_4509_);
v___y_4498_ = v___x_4510_;
goto v___jp_4497_;
}
else
{
lean_object* v___x_4512_; 
lean_dec(v_val_4504_);
lean_dec(v_key_4503_);
if (v_isShared_4507_ == 0)
{
lean_ctor_set(v___x_4506_, 1, v_x_4482_);
lean_ctor_set(v___x_4506_, 0, v_x_4481_);
v___x_4512_ = v___x_4506_;
goto v_reusejp_4511_;
}
else
{
lean_object* v_reuseFailAlloc_4513_; 
v_reuseFailAlloc_4513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4513_, 0, v_x_4481_);
lean_ctor_set(v_reuseFailAlloc_4513_, 1, v_x_4482_);
v___x_4512_ = v_reuseFailAlloc_4513_;
goto v_reusejp_4511_;
}
v_reusejp_4511_:
{
v___y_4498_ = v___x_4512_;
goto v___jp_4497_;
}
}
}
}
case 1:
{
lean_object* v_node_4515_; lean_object* v___x_4517_; uint8_t v_isShared_4518_; uint8_t v_isSharedCheck_4525_; 
v_node_4515_ = lean_ctor_get(v_v_4494_, 0);
v_isSharedCheck_4525_ = !lean_is_exclusive(v_v_4494_);
if (v_isSharedCheck_4525_ == 0)
{
v___x_4517_ = v_v_4494_;
v_isShared_4518_ = v_isSharedCheck_4525_;
goto v_resetjp_4516_;
}
else
{
lean_inc(v_node_4515_);
lean_dec(v_v_4494_);
v___x_4517_ = lean_box(0);
v_isShared_4518_ = v_isSharedCheck_4525_;
goto v_resetjp_4516_;
}
v_resetjp_4516_:
{
size_t v___x_4519_; size_t v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_4523_; 
v___x_4519_ = lean_usize_shift_right(v_x_4479_, v___x_4484_);
v___x_4520_ = lean_usize_add(v_x_4480_, v___x_4485_);
v___x_4521_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4___redArg(v_node_4515_, v___x_4519_, v___x_4520_, v_x_4481_, v_x_4482_);
if (v_isShared_4518_ == 0)
{
lean_ctor_set(v___x_4517_, 0, v___x_4521_);
v___x_4523_ = v___x_4517_;
goto v_reusejp_4522_;
}
else
{
lean_object* v_reuseFailAlloc_4524_; 
v_reuseFailAlloc_4524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4524_, 0, v___x_4521_);
v___x_4523_ = v_reuseFailAlloc_4524_;
goto v_reusejp_4522_;
}
v_reusejp_4522_:
{
v___y_4498_ = v___x_4523_;
goto v___jp_4497_;
}
}
}
default: 
{
lean_object* v___x_4526_; 
v___x_4526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4526_, 0, v_x_4481_);
lean_ctor_set(v___x_4526_, 1, v_x_4482_);
v___y_4498_ = v___x_4526_;
goto v___jp_4497_;
}
}
v___jp_4497_:
{
lean_object* v___x_4499_; lean_object* v___x_4501_; 
v___x_4499_ = lean_array_fset(v_xs_x27_4496_, v_j_4488_, v___y_4498_);
lean_dec(v_j_4488_);
if (v_isShared_4493_ == 0)
{
lean_ctor_set(v___x_4492_, 0, v___x_4499_);
v___x_4501_ = v___x_4492_;
goto v_reusejp_4500_;
}
else
{
lean_object* v_reuseFailAlloc_4502_; 
v_reuseFailAlloc_4502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4502_, 0, v___x_4499_);
v___x_4501_ = v_reuseFailAlloc_4502_;
goto v_reusejp_4500_;
}
v_reusejp_4500_:
{
return v___x_4501_;
}
}
}
}
}
else
{
lean_object* v_ks_4529_; lean_object* v_vs_4530_; lean_object* v___x_4532_; uint8_t v_isShared_4533_; uint8_t v_isSharedCheck_4550_; 
v_ks_4529_ = lean_ctor_get(v_x_4478_, 0);
v_vs_4530_ = lean_ctor_get(v_x_4478_, 1);
v_isSharedCheck_4550_ = !lean_is_exclusive(v_x_4478_);
if (v_isSharedCheck_4550_ == 0)
{
v___x_4532_ = v_x_4478_;
v_isShared_4533_ = v_isSharedCheck_4550_;
goto v_resetjp_4531_;
}
else
{
lean_inc(v_vs_4530_);
lean_inc(v_ks_4529_);
lean_dec(v_x_4478_);
v___x_4532_ = lean_box(0);
v_isShared_4533_ = v_isSharedCheck_4550_;
goto v_resetjp_4531_;
}
v_resetjp_4531_:
{
lean_object* v___x_4535_; 
if (v_isShared_4533_ == 0)
{
v___x_4535_ = v___x_4532_;
goto v_reusejp_4534_;
}
else
{
lean_object* v_reuseFailAlloc_4549_; 
v_reuseFailAlloc_4549_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4549_, 0, v_ks_4529_);
lean_ctor_set(v_reuseFailAlloc_4549_, 1, v_vs_4530_);
v___x_4535_ = v_reuseFailAlloc_4549_;
goto v_reusejp_4534_;
}
v_reusejp_4534_:
{
lean_object* v_newNode_4536_; uint8_t v___y_4538_; size_t v___x_4544_; uint8_t v___x_4545_; 
v_newNode_4536_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4_spec__8___redArg(v___x_4535_, v_x_4481_, v_x_4482_);
v___x_4544_ = ((size_t)7ULL);
v___x_4545_ = lean_usize_dec_le(v___x_4544_, v_x_4480_);
if (v___x_4545_ == 0)
{
lean_object* v___x_4546_; lean_object* v___x_4547_; uint8_t v___x_4548_; 
v___x_4546_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4536_);
v___x_4547_ = lean_unsigned_to_nat(4u);
v___x_4548_ = lean_nat_dec_lt(v___x_4546_, v___x_4547_);
lean_dec(v___x_4546_);
v___y_4538_ = v___x_4548_;
goto v___jp_4537_;
}
else
{
v___y_4538_ = v___x_4545_;
goto v___jp_4537_;
}
v___jp_4537_:
{
if (v___y_4538_ == 0)
{
lean_object* v_ks_4539_; lean_object* v_vs_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; 
v_ks_4539_ = lean_ctor_get(v_newNode_4536_, 0);
lean_inc_ref(v_ks_4539_);
v_vs_4540_ = lean_ctor_get(v_newNode_4536_, 1);
lean_inc_ref(v_vs_4540_);
lean_dec_ref(v_newNode_4536_);
v___x_4541_ = lean_unsigned_to_nat(0u);
v___x_4542_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4___redArg___closed__2);
v___x_4543_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4_spec__9___redArg(v_x_4480_, v_ks_4539_, v_vs_4540_, v___x_4541_, v___x_4542_);
lean_dec_ref(v_vs_4540_);
lean_dec_ref(v_ks_4539_);
return v___x_4543_;
}
else
{
return v_newNode_4536_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4_spec__9___redArg(size_t v_depth_4551_, lean_object* v_keys_4552_, lean_object* v_vals_4553_, lean_object* v_i_4554_, lean_object* v_entries_4555_){
_start:
{
lean_object* v___x_4556_; uint8_t v___x_4557_; 
v___x_4556_ = lean_array_get_size(v_keys_4552_);
v___x_4557_ = lean_nat_dec_lt(v_i_4554_, v___x_4556_);
if (v___x_4557_ == 0)
{
lean_dec(v_i_4554_);
return v_entries_4555_;
}
else
{
lean_object* v_k_4558_; lean_object* v_v_4559_; uint64_t v___x_4560_; size_t v_h_4561_; size_t v___x_4562_; lean_object* v___x_4563_; size_t v___x_4564_; size_t v___x_4565_; size_t v___x_4566_; size_t v_h_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; 
v_k_4558_ = lean_array_fget_borrowed(v_keys_4552_, v_i_4554_);
v_v_4559_ = lean_array_fget_borrowed(v_vals_4553_, v_i_4554_);
v___x_4560_ = l_Lean_instHashableMVarId_hash(v_k_4558_);
v_h_4561_ = lean_uint64_to_usize(v___x_4560_);
v___x_4562_ = ((size_t)5ULL);
v___x_4563_ = lean_unsigned_to_nat(1u);
v___x_4564_ = ((size_t)1ULL);
v___x_4565_ = lean_usize_sub(v_depth_4551_, v___x_4564_);
v___x_4566_ = lean_usize_mul(v___x_4562_, v___x_4565_);
v_h_4567_ = lean_usize_shift_right(v_h_4561_, v___x_4566_);
v___x_4568_ = lean_nat_add(v_i_4554_, v___x_4563_);
lean_dec(v_i_4554_);
lean_inc(v_v_4559_);
lean_inc(v_k_4558_);
v___x_4569_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4___redArg(v_entries_4555_, v_h_4567_, v_depth_4551_, v_k_4558_, v_v_4559_);
v_i_4554_ = v___x_4568_;
v_entries_4555_ = v___x_4569_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4_spec__9___redArg___boxed(lean_object* v_depth_4571_, lean_object* v_keys_4572_, lean_object* v_vals_4573_, lean_object* v_i_4574_, lean_object* v_entries_4575_){
_start:
{
size_t v_depth_boxed_4576_; lean_object* v_res_4577_; 
v_depth_boxed_4576_ = lean_unbox_usize(v_depth_4571_);
lean_dec(v_depth_4571_);
v_res_4577_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4_spec__9___redArg(v_depth_boxed_4576_, v_keys_4572_, v_vals_4573_, v_i_4574_, v_entries_4575_);
lean_dec_ref(v_vals_4573_);
lean_dec_ref(v_keys_4572_);
return v_res_4577_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_x_4578_, lean_object* v_x_4579_, lean_object* v_x_4580_, lean_object* v_x_4581_, lean_object* v_x_4582_){
_start:
{
size_t v_x_46709__boxed_4583_; size_t v_x_46710__boxed_4584_; lean_object* v_res_4585_; 
v_x_46709__boxed_4583_ = lean_unbox_usize(v_x_4579_);
lean_dec(v_x_4579_);
v_x_46710__boxed_4584_ = lean_unbox_usize(v_x_4580_);
lean_dec(v_x_4580_);
v_res_4585_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4___redArg(v_x_4578_, v_x_46709__boxed_4583_, v_x_46710__boxed_4584_, v_x_4581_, v_x_4582_);
return v_res_4585_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0___redArg(lean_object* v_x_4586_, lean_object* v_x_4587_, lean_object* v_x_4588_){
_start:
{
uint64_t v___x_4589_; size_t v___x_4590_; size_t v___x_4591_; lean_object* v___x_4592_; 
v___x_4589_ = l_Lean_instHashableMVarId_hash(v_x_4587_);
v___x_4590_ = lean_uint64_to_usize(v___x_4589_);
v___x_4591_ = ((size_t)1ULL);
v___x_4592_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4___redArg(v_x_4586_, v___x_4590_, v___x_4591_, v_x_4587_, v_x_4588_);
return v___x_4592_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0___redArg(lean_object* v_mvarId_4593_, lean_object* v_val_4594_, lean_object* v___y_4595_){
_start:
{
lean_object* v___x_4597_; lean_object* v_mctx_4598_; lean_object* v_cache_4599_; lean_object* v_zetaDeltaFVarIds_4600_; lean_object* v_postponed_4601_; lean_object* v_diag_4602_; lean_object* v___x_4604_; uint8_t v_isShared_4605_; uint8_t v_isSharedCheck_4629_; 
v___x_4597_ = lean_st_ref_take(v___y_4595_);
v_mctx_4598_ = lean_ctor_get(v___x_4597_, 0);
v_cache_4599_ = lean_ctor_get(v___x_4597_, 1);
v_zetaDeltaFVarIds_4600_ = lean_ctor_get(v___x_4597_, 2);
v_postponed_4601_ = lean_ctor_get(v___x_4597_, 3);
v_diag_4602_ = lean_ctor_get(v___x_4597_, 4);
v_isSharedCheck_4629_ = !lean_is_exclusive(v___x_4597_);
if (v_isSharedCheck_4629_ == 0)
{
v___x_4604_ = v___x_4597_;
v_isShared_4605_ = v_isSharedCheck_4629_;
goto v_resetjp_4603_;
}
else
{
lean_inc(v_diag_4602_);
lean_inc(v_postponed_4601_);
lean_inc(v_zetaDeltaFVarIds_4600_);
lean_inc(v_cache_4599_);
lean_inc(v_mctx_4598_);
lean_dec(v___x_4597_);
v___x_4604_ = lean_box(0);
v_isShared_4605_ = v_isSharedCheck_4629_;
goto v_resetjp_4603_;
}
v_resetjp_4603_:
{
lean_object* v_depth_4606_; lean_object* v_levelAssignDepth_4607_; lean_object* v_mvarCounter_4608_; lean_object* v_lDepth_4609_; lean_object* v_decls_4610_; lean_object* v_userNames_4611_; lean_object* v_lAssignment_4612_; lean_object* v_eAssignment_4613_; lean_object* v_dAssignment_4614_; lean_object* v___x_4616_; uint8_t v_isShared_4617_; uint8_t v_isSharedCheck_4628_; 
v_depth_4606_ = lean_ctor_get(v_mctx_4598_, 0);
v_levelAssignDepth_4607_ = lean_ctor_get(v_mctx_4598_, 1);
v_mvarCounter_4608_ = lean_ctor_get(v_mctx_4598_, 2);
v_lDepth_4609_ = lean_ctor_get(v_mctx_4598_, 3);
v_decls_4610_ = lean_ctor_get(v_mctx_4598_, 4);
v_userNames_4611_ = lean_ctor_get(v_mctx_4598_, 5);
v_lAssignment_4612_ = lean_ctor_get(v_mctx_4598_, 6);
v_eAssignment_4613_ = lean_ctor_get(v_mctx_4598_, 7);
v_dAssignment_4614_ = lean_ctor_get(v_mctx_4598_, 8);
v_isSharedCheck_4628_ = !lean_is_exclusive(v_mctx_4598_);
if (v_isSharedCheck_4628_ == 0)
{
v___x_4616_ = v_mctx_4598_;
v_isShared_4617_ = v_isSharedCheck_4628_;
goto v_resetjp_4615_;
}
else
{
lean_inc(v_dAssignment_4614_);
lean_inc(v_eAssignment_4613_);
lean_inc(v_lAssignment_4612_);
lean_inc(v_userNames_4611_);
lean_inc(v_decls_4610_);
lean_inc(v_lDepth_4609_);
lean_inc(v_mvarCounter_4608_);
lean_inc(v_levelAssignDepth_4607_);
lean_inc(v_depth_4606_);
lean_dec(v_mctx_4598_);
v___x_4616_ = lean_box(0);
v_isShared_4617_ = v_isSharedCheck_4628_;
goto v_resetjp_4615_;
}
v_resetjp_4615_:
{
lean_object* v___x_4618_; lean_object* v___x_4620_; 
v___x_4618_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0___redArg(v_eAssignment_4613_, v_mvarId_4593_, v_val_4594_);
if (v_isShared_4617_ == 0)
{
lean_ctor_set(v___x_4616_, 7, v___x_4618_);
v___x_4620_ = v___x_4616_;
goto v_reusejp_4619_;
}
else
{
lean_object* v_reuseFailAlloc_4627_; 
v_reuseFailAlloc_4627_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4627_, 0, v_depth_4606_);
lean_ctor_set(v_reuseFailAlloc_4627_, 1, v_levelAssignDepth_4607_);
lean_ctor_set(v_reuseFailAlloc_4627_, 2, v_mvarCounter_4608_);
lean_ctor_set(v_reuseFailAlloc_4627_, 3, v_lDepth_4609_);
lean_ctor_set(v_reuseFailAlloc_4627_, 4, v_decls_4610_);
lean_ctor_set(v_reuseFailAlloc_4627_, 5, v_userNames_4611_);
lean_ctor_set(v_reuseFailAlloc_4627_, 6, v_lAssignment_4612_);
lean_ctor_set(v_reuseFailAlloc_4627_, 7, v___x_4618_);
lean_ctor_set(v_reuseFailAlloc_4627_, 8, v_dAssignment_4614_);
v___x_4620_ = v_reuseFailAlloc_4627_;
goto v_reusejp_4619_;
}
v_reusejp_4619_:
{
lean_object* v___x_4622_; 
if (v_isShared_4605_ == 0)
{
lean_ctor_set(v___x_4604_, 0, v___x_4620_);
v___x_4622_ = v___x_4604_;
goto v_reusejp_4621_;
}
else
{
lean_object* v_reuseFailAlloc_4626_; 
v_reuseFailAlloc_4626_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4626_, 0, v___x_4620_);
lean_ctor_set(v_reuseFailAlloc_4626_, 1, v_cache_4599_);
lean_ctor_set(v_reuseFailAlloc_4626_, 2, v_zetaDeltaFVarIds_4600_);
lean_ctor_set(v_reuseFailAlloc_4626_, 3, v_postponed_4601_);
lean_ctor_set(v_reuseFailAlloc_4626_, 4, v_diag_4602_);
v___x_4622_ = v_reuseFailAlloc_4626_;
goto v_reusejp_4621_;
}
v_reusejp_4621_:
{
lean_object* v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; 
v___x_4623_ = lean_st_ref_set(v___y_4595_, v___x_4622_);
v___x_4624_ = lean_box(0);
v___x_4625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4625_, 0, v___x_4624_);
return v___x_4625_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0___redArg___boxed(lean_object* v_mvarId_4630_, lean_object* v_val_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_){
_start:
{
lean_object* v_res_4634_; 
v_res_4634_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0___redArg(v_mvarId_4630_, v_val_4631_, v___y_4632_);
lean_dec(v___y_4632_);
return v_res_4634_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4(lean_object* v_a_4642_, lean_object* v___x_4643_, lean_object* v_as_4644_, size_t v_sz_4645_, size_t v_i_4646_, lean_object* v_b_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_){
_start:
{
lean_object* v_a_4656_; uint8_t v___x_4660_; 
v___x_4660_ = lean_usize_dec_lt(v_i_4646_, v_sz_4645_);
if (v___x_4660_ == 0)
{
lean_object* v___x_4661_; 
lean_dec(v___y_4653_);
lean_dec_ref(v___y_4652_);
lean_dec(v___y_4651_);
lean_dec_ref(v___y_4650_);
lean_dec(v___y_4649_);
lean_dec_ref(v___y_4648_);
lean_dec_ref(v___x_4643_);
lean_dec(v_a_4642_);
v___x_4661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4661_, 0, v_b_4647_);
return v___x_4661_;
}
else
{
lean_object* v_a_4662_; lean_object* v___x_4663_; 
v_a_4662_ = lean_array_uget_borrowed(v_as_4644_, v_i_4646_);
lean_inc_ref(v___y_4650_);
lean_inc(v_a_4662_);
v___x_4663_ = l_Lean_FVarId_getDecl___redArg(v_a_4662_, v___y_4650_, v___y_4652_, v___y_4653_);
if (lean_obj_tag(v___x_4663_) == 0)
{
lean_object* v_options_4664_; lean_object* v_a_4665_; lean_object* v_snd_4666_; lean_object* v___x_4668_; uint8_t v_isShared_4669_; uint8_t v_isSharedCheck_4867_; 
v_options_4664_ = lean_ctor_get(v___y_4652_, 2);
v_a_4665_ = lean_ctor_get(v___x_4663_, 0);
lean_inc(v_a_4665_);
lean_dec_ref(v___x_4663_);
v_snd_4666_ = lean_ctor_get(v_b_4647_, 1);
v_isSharedCheck_4867_ = !lean_is_exclusive(v_b_4647_);
if (v_isSharedCheck_4867_ == 0)
{
lean_object* v_unused_4868_; 
v_unused_4868_ = lean_ctor_get(v_b_4647_, 0);
lean_dec(v_unused_4868_);
v___x_4668_ = v_b_4647_;
v_isShared_4669_ = v_isSharedCheck_4867_;
goto v_resetjp_4667_;
}
else
{
lean_inc(v_snd_4666_);
lean_dec(v_b_4647_);
v___x_4668_ = lean_box(0);
v_isShared_4669_ = v_isSharedCheck_4867_;
goto v_resetjp_4667_;
}
v_resetjp_4667_:
{
uint8_t v_hasTrace_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; lean_object* v___y_4674_; 
v_hasTrace_4670_ = lean_ctor_get_uint8(v_options_4664_, sizeof(void*)*1);
v___x_4671_ = lean_box(0);
v___x_4672_ = l_Lean_LocalDecl_type(v_a_4665_);
if (v_hasTrace_4670_ == 0)
{
lean_object* v___x_4771_; 
lean_inc(v___y_4653_);
lean_inc_ref(v___y_4652_);
lean_inc(v___y_4651_);
lean_inc_ref(v___y_4650_);
lean_inc(v___y_4649_);
lean_inc_ref(v___y_4648_);
lean_inc_ref(v___x_4643_);
lean_inc_ref(v___x_4672_);
v___x_4771_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_4672_, v___x_4643_, v___y_4648_, v___y_4649_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_);
v___y_4674_ = v___x_4771_;
goto v___jp_4673_;
}
else
{
lean_object* v___x_4772_; lean_object* v___x_4773_; 
v___x_4772_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0));
v___x_4773_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__1___redArg(v___x_4772_, v___y_4652_);
if (lean_obj_tag(v___x_4773_) == 0)
{
lean_object* v_a_4774_; lean_object* v___f_4775_; lean_object* v___x_4776_; lean_object* v___y_4778_; lean_object* v___y_4779_; lean_object* v_a_4780_; lean_object* v___y_4794_; lean_object* v___y_4795_; lean_object* v_a_4796_; uint8_t v___x_4855_; 
v_a_4774_ = lean_ctor_get(v___x_4773_, 0);
lean_inc(v_a_4774_);
lean_dec_ref(v___x_4773_);
lean_inc_ref(v___x_4672_);
lean_inc(v_a_4665_);
v___f_4775_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___boxed), 10, 2);
lean_closure_set(v___f_4775_, 0, v_a_4665_);
lean_closure_set(v___f_4775_, 1, v___x_4672_);
v___x_4776_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__1));
v___x_4855_ = lean_unbox(v_a_4774_);
if (v___x_4855_ == 0)
{
lean_object* v___x_4856_; uint8_t v___x_4857_; 
v___x_4856_ = l_Lean_trace_profiler;
v___x_4857_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2(v_options_4664_, v___x_4856_);
if (v___x_4857_ == 0)
{
lean_object* v___x_4858_; 
lean_dec_ref(v___f_4775_);
lean_dec(v_a_4774_);
lean_inc(v___y_4653_);
lean_inc_ref(v___y_4652_);
lean_inc(v___y_4651_);
lean_inc_ref(v___y_4650_);
lean_inc(v___y_4649_);
lean_inc_ref(v___y_4648_);
lean_inc_ref(v___x_4643_);
lean_inc_ref(v___x_4672_);
v___x_4858_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_4672_, v___x_4643_, v___y_4648_, v___y_4649_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_);
v___y_4674_ = v___x_4858_;
goto v___jp_4673_;
}
else
{
goto v___jp_4806_;
}
}
else
{
goto v___jp_4806_;
}
v___jp_4777_:
{
lean_object* v___x_4781_; double v___x_4782_; double v___x_4783_; double v___x_4784_; double v___x_4785_; double v___x_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; uint8_t v___x_4791_; lean_object* v___x_4792_; 
v___x_4781_ = lean_io_mono_nanos_now();
v___x_4782_ = lean_float_of_nat(v___y_4778_);
v___x_4783_ = lean_float_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4);
v___x_4784_ = lean_float_div(v___x_4782_, v___x_4783_);
v___x_4785_ = lean_float_of_nat(v___x_4781_);
v___x_4786_ = lean_float_div(v___x_4785_, v___x_4783_);
v___x_4787_ = lean_box_float(v___x_4784_);
v___x_4788_ = lean_box_float(v___x_4786_);
v___x_4789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4789_, 0, v___x_4787_);
lean_ctor_set(v___x_4789_, 1, v___x_4788_);
v___x_4790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4790_, 0, v_a_4780_);
lean_ctor_set(v___x_4790_, 1, v___x_4789_);
v___x_4791_ = lean_unbox(v_a_4774_);
lean_dec(v_a_4774_);
lean_inc(v___y_4653_);
lean_inc_ref(v___y_4652_);
lean_inc(v___y_4651_);
lean_inc_ref(v___y_4650_);
lean_inc(v___y_4649_);
lean_inc_ref(v___y_4648_);
v___x_4792_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3(v___x_4772_, v_hasTrace_4670_, v___x_4776_, v_options_4664_, v___x_4791_, v___y_4779_, v___f_4775_, v___x_4790_, v___y_4648_, v___y_4649_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_);
v___y_4674_ = v___x_4792_;
goto v___jp_4673_;
}
v___jp_4793_:
{
lean_object* v___x_4797_; double v___x_4798_; double v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; lean_object* v___x_4802_; lean_object* v___x_4803_; uint8_t v___x_4804_; lean_object* v___x_4805_; 
v___x_4797_ = lean_io_get_num_heartbeats();
v___x_4798_ = lean_float_of_nat(v___y_4794_);
v___x_4799_ = lean_float_of_nat(v___x_4797_);
v___x_4800_ = lean_box_float(v___x_4798_);
v___x_4801_ = lean_box_float(v___x_4799_);
v___x_4802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4802_, 0, v___x_4800_);
lean_ctor_set(v___x_4802_, 1, v___x_4801_);
v___x_4803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4803_, 0, v_a_4796_);
lean_ctor_set(v___x_4803_, 1, v___x_4802_);
v___x_4804_ = lean_unbox(v_a_4774_);
lean_dec(v_a_4774_);
lean_inc(v___y_4653_);
lean_inc_ref(v___y_4652_);
lean_inc(v___y_4651_);
lean_inc_ref(v___y_4650_);
lean_inc(v___y_4649_);
lean_inc_ref(v___y_4648_);
v___x_4805_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3(v___x_4772_, v_hasTrace_4670_, v___x_4776_, v_options_4664_, v___x_4804_, v___y_4795_, v___f_4775_, v___x_4803_, v___y_4648_, v___y_4649_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_);
v___y_4674_ = v___x_4805_;
goto v___jp_4673_;
}
v___jp_4806_:
{
lean_object* v___x_4807_; 
v___x_4807_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2___redArg(v___y_4653_);
if (lean_obj_tag(v___x_4807_) == 0)
{
lean_object* v_a_4808_; lean_object* v___x_4809_; uint8_t v___x_4810_; 
v_a_4808_ = lean_ctor_get(v___x_4807_, 0);
lean_inc(v_a_4808_);
lean_dec_ref(v___x_4807_);
v___x_4809_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4810_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2(v_options_4664_, v___x_4809_);
if (v___x_4810_ == 0)
{
lean_object* v___x_4811_; lean_object* v___x_4812_; 
v___x_4811_ = lean_io_mono_nanos_now();
lean_inc(v___y_4653_);
lean_inc_ref(v___y_4652_);
lean_inc(v___y_4651_);
lean_inc_ref(v___y_4650_);
lean_inc(v___y_4649_);
lean_inc_ref(v___y_4648_);
lean_inc_ref(v___x_4643_);
lean_inc_ref(v___x_4672_);
v___x_4812_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_4672_, v___x_4643_, v___y_4648_, v___y_4649_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_);
if (lean_obj_tag(v___x_4812_) == 0)
{
lean_object* v_a_4813_; lean_object* v___x_4815_; uint8_t v_isShared_4816_; uint8_t v_isSharedCheck_4820_; 
v_a_4813_ = lean_ctor_get(v___x_4812_, 0);
v_isSharedCheck_4820_ = !lean_is_exclusive(v___x_4812_);
if (v_isSharedCheck_4820_ == 0)
{
v___x_4815_ = v___x_4812_;
v_isShared_4816_ = v_isSharedCheck_4820_;
goto v_resetjp_4814_;
}
else
{
lean_inc(v_a_4813_);
lean_dec(v___x_4812_);
v___x_4815_ = lean_box(0);
v_isShared_4816_ = v_isSharedCheck_4820_;
goto v_resetjp_4814_;
}
v_resetjp_4814_:
{
lean_object* v___x_4818_; 
if (v_isShared_4816_ == 0)
{
lean_ctor_set_tag(v___x_4815_, 1);
v___x_4818_ = v___x_4815_;
goto v_reusejp_4817_;
}
else
{
lean_object* v_reuseFailAlloc_4819_; 
v_reuseFailAlloc_4819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4819_, 0, v_a_4813_);
v___x_4818_ = v_reuseFailAlloc_4819_;
goto v_reusejp_4817_;
}
v_reusejp_4817_:
{
v___y_4778_ = v___x_4811_;
v___y_4779_ = v_a_4808_;
v_a_4780_ = v___x_4818_;
goto v___jp_4777_;
}
}
}
else
{
lean_object* v_a_4821_; lean_object* v___x_4823_; uint8_t v_isShared_4824_; uint8_t v_isSharedCheck_4828_; 
v_a_4821_ = lean_ctor_get(v___x_4812_, 0);
v_isSharedCheck_4828_ = !lean_is_exclusive(v___x_4812_);
if (v_isSharedCheck_4828_ == 0)
{
v___x_4823_ = v___x_4812_;
v_isShared_4824_ = v_isSharedCheck_4828_;
goto v_resetjp_4822_;
}
else
{
lean_inc(v_a_4821_);
lean_dec(v___x_4812_);
v___x_4823_ = lean_box(0);
v_isShared_4824_ = v_isSharedCheck_4828_;
goto v_resetjp_4822_;
}
v_resetjp_4822_:
{
lean_object* v___x_4826_; 
if (v_isShared_4824_ == 0)
{
lean_ctor_set_tag(v___x_4823_, 0);
v___x_4826_ = v___x_4823_;
goto v_reusejp_4825_;
}
else
{
lean_object* v_reuseFailAlloc_4827_; 
v_reuseFailAlloc_4827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4827_, 0, v_a_4821_);
v___x_4826_ = v_reuseFailAlloc_4827_;
goto v_reusejp_4825_;
}
v_reusejp_4825_:
{
v___y_4778_ = v___x_4811_;
v___y_4779_ = v_a_4808_;
v_a_4780_ = v___x_4826_;
goto v___jp_4777_;
}
}
}
}
else
{
lean_object* v___x_4829_; lean_object* v___x_4830_; 
v___x_4829_ = lean_io_get_num_heartbeats();
lean_inc(v___y_4653_);
lean_inc_ref(v___y_4652_);
lean_inc(v___y_4651_);
lean_inc_ref(v___y_4650_);
lean_inc(v___y_4649_);
lean_inc_ref(v___y_4648_);
lean_inc_ref(v___x_4643_);
lean_inc_ref(v___x_4672_);
v___x_4830_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_4672_, v___x_4643_, v___y_4648_, v___y_4649_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_);
if (lean_obj_tag(v___x_4830_) == 0)
{
lean_object* v_a_4831_; lean_object* v___x_4833_; uint8_t v_isShared_4834_; uint8_t v_isSharedCheck_4838_; 
v_a_4831_ = lean_ctor_get(v___x_4830_, 0);
v_isSharedCheck_4838_ = !lean_is_exclusive(v___x_4830_);
if (v_isSharedCheck_4838_ == 0)
{
v___x_4833_ = v___x_4830_;
v_isShared_4834_ = v_isSharedCheck_4838_;
goto v_resetjp_4832_;
}
else
{
lean_inc(v_a_4831_);
lean_dec(v___x_4830_);
v___x_4833_ = lean_box(0);
v_isShared_4834_ = v_isSharedCheck_4838_;
goto v_resetjp_4832_;
}
v_resetjp_4832_:
{
lean_object* v___x_4836_; 
if (v_isShared_4834_ == 0)
{
lean_ctor_set_tag(v___x_4833_, 1);
v___x_4836_ = v___x_4833_;
goto v_reusejp_4835_;
}
else
{
lean_object* v_reuseFailAlloc_4837_; 
v_reuseFailAlloc_4837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4837_, 0, v_a_4831_);
v___x_4836_ = v_reuseFailAlloc_4837_;
goto v_reusejp_4835_;
}
v_reusejp_4835_:
{
v___y_4794_ = v___x_4829_;
v___y_4795_ = v_a_4808_;
v_a_4796_ = v___x_4836_;
goto v___jp_4793_;
}
}
}
else
{
lean_object* v_a_4839_; lean_object* v___x_4841_; uint8_t v_isShared_4842_; uint8_t v_isSharedCheck_4846_; 
v_a_4839_ = lean_ctor_get(v___x_4830_, 0);
v_isSharedCheck_4846_ = !lean_is_exclusive(v___x_4830_);
if (v_isSharedCheck_4846_ == 0)
{
v___x_4841_ = v___x_4830_;
v_isShared_4842_ = v_isSharedCheck_4846_;
goto v_resetjp_4840_;
}
else
{
lean_inc(v_a_4839_);
lean_dec(v___x_4830_);
v___x_4841_ = lean_box(0);
v_isShared_4842_ = v_isSharedCheck_4846_;
goto v_resetjp_4840_;
}
v_resetjp_4840_:
{
lean_object* v___x_4844_; 
if (v_isShared_4842_ == 0)
{
lean_ctor_set_tag(v___x_4841_, 0);
v___x_4844_ = v___x_4841_;
goto v_reusejp_4843_;
}
else
{
lean_object* v_reuseFailAlloc_4845_; 
v_reuseFailAlloc_4845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4845_, 0, v_a_4839_);
v___x_4844_ = v_reuseFailAlloc_4845_;
goto v_reusejp_4843_;
}
v_reusejp_4843_:
{
v___y_4794_ = v___x_4829_;
v___y_4795_ = v_a_4808_;
v_a_4796_ = v___x_4844_;
goto v___jp_4793_;
}
}
}
}
}
else
{
lean_object* v_a_4847_; lean_object* v___x_4849_; uint8_t v_isShared_4850_; uint8_t v_isSharedCheck_4854_; 
lean_dec_ref(v___f_4775_);
lean_dec(v_a_4774_);
lean_dec_ref(v___x_4672_);
lean_del_object(v___x_4668_);
lean_dec(v_snd_4666_);
lean_dec(v_a_4665_);
lean_dec(v___y_4653_);
lean_dec_ref(v___y_4652_);
lean_dec(v___y_4651_);
lean_dec_ref(v___y_4650_);
lean_dec(v___y_4649_);
lean_dec_ref(v___y_4648_);
lean_dec_ref(v___x_4643_);
lean_dec(v_a_4642_);
v_a_4847_ = lean_ctor_get(v___x_4807_, 0);
v_isSharedCheck_4854_ = !lean_is_exclusive(v___x_4807_);
if (v_isSharedCheck_4854_ == 0)
{
v___x_4849_ = v___x_4807_;
v_isShared_4850_ = v_isSharedCheck_4854_;
goto v_resetjp_4848_;
}
else
{
lean_inc(v_a_4847_);
lean_dec(v___x_4807_);
v___x_4849_ = lean_box(0);
v_isShared_4850_ = v_isSharedCheck_4854_;
goto v_resetjp_4848_;
}
v_resetjp_4848_:
{
lean_object* v___x_4852_; 
if (v_isShared_4850_ == 0)
{
v___x_4852_ = v___x_4849_;
goto v_reusejp_4851_;
}
else
{
lean_object* v_reuseFailAlloc_4853_; 
v_reuseFailAlloc_4853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4853_, 0, v_a_4847_);
v___x_4852_ = v_reuseFailAlloc_4853_;
goto v_reusejp_4851_;
}
v_reusejp_4851_:
{
return v___x_4852_;
}
}
}
}
}
else
{
lean_object* v_a_4859_; lean_object* v___x_4861_; uint8_t v_isShared_4862_; uint8_t v_isSharedCheck_4866_; 
lean_dec_ref(v___x_4672_);
lean_del_object(v___x_4668_);
lean_dec(v_snd_4666_);
lean_dec(v_a_4665_);
lean_dec(v___y_4653_);
lean_dec_ref(v___y_4652_);
lean_dec(v___y_4651_);
lean_dec_ref(v___y_4650_);
lean_dec(v___y_4649_);
lean_dec_ref(v___y_4648_);
lean_dec_ref(v___x_4643_);
lean_dec(v_a_4642_);
v_a_4859_ = lean_ctor_get(v___x_4773_, 0);
v_isSharedCheck_4866_ = !lean_is_exclusive(v___x_4773_);
if (v_isSharedCheck_4866_ == 0)
{
v___x_4861_ = v___x_4773_;
v_isShared_4862_ = v_isSharedCheck_4866_;
goto v_resetjp_4860_;
}
else
{
lean_inc(v_a_4859_);
lean_dec(v___x_4773_);
v___x_4861_ = lean_box(0);
v_isShared_4862_ = v_isSharedCheck_4866_;
goto v_resetjp_4860_;
}
v_resetjp_4860_:
{
lean_object* v___x_4864_; 
if (v_isShared_4862_ == 0)
{
v___x_4864_ = v___x_4861_;
goto v_reusejp_4863_;
}
else
{
lean_object* v_reuseFailAlloc_4865_; 
v_reuseFailAlloc_4865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4865_, 0, v_a_4859_);
v___x_4864_ = v_reuseFailAlloc_4865_;
goto v_reusejp_4863_;
}
v_reusejp_4863_:
{
return v___x_4864_;
}
}
}
}
v___jp_4673_:
{
if (lean_obj_tag(v___y_4674_) == 0)
{
lean_object* v_a_4675_; 
v_a_4675_ = lean_ctor_get(v___y_4674_, 0);
lean_inc(v_a_4675_);
lean_dec_ref(v___y_4674_);
if (lean_obj_tag(v_a_4675_) == 0)
{
lean_object* v___x_4677_; 
lean_dec_ref(v_a_4675_);
lean_dec_ref(v___x_4672_);
lean_dec(v_a_4665_);
if (v_isShared_4669_ == 0)
{
lean_ctor_set(v___x_4668_, 0, v___x_4671_);
v___x_4677_ = v___x_4668_;
goto v_reusejp_4676_;
}
else
{
lean_object* v_reuseFailAlloc_4678_; 
v_reuseFailAlloc_4678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4678_, 0, v___x_4671_);
lean_ctor_set(v_reuseFailAlloc_4678_, 1, v_snd_4666_);
v___x_4677_ = v_reuseFailAlloc_4678_;
goto v_reusejp_4676_;
}
v_reusejp_4676_:
{
v_a_4656_ = v___x_4677_;
goto v___jp_4655_;
}
}
else
{
lean_object* v_e_x27_4679_; lean_object* v_proof_4680_; uint8_t v___x_4681_; 
v_e_x27_4679_ = lean_ctor_get(v_a_4675_, 0);
lean_inc_ref(v_e_x27_4679_);
v_proof_4680_ = lean_ctor_get(v_a_4675_, 1);
lean_inc_ref(v_proof_4680_);
lean_dec_ref(v_a_4675_);
lean_inc_ref(v_e_x27_4679_);
v___x_4681_ = l_Lean_Expr_isFalse(v_e_x27_4679_);
if (v___x_4681_ == 0)
{
lean_object* v___x_4682_; 
lean_inc(v___y_4653_);
lean_inc_ref(v___y_4652_);
lean_inc(v___y_4651_);
lean_inc_ref(v___y_4650_);
lean_inc_ref(v___x_4672_);
v___x_4682_ = l_Lean_Meta_getLevel(v___x_4672_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_);
if (lean_obj_tag(v___x_4682_) == 0)
{
lean_object* v_a_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; uint8_t v___x_4691_; uint8_t v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4696_; 
v_a_4683_ = lean_ctor_get(v___x_4682_, 0);
lean_inc(v_a_4683_);
lean_dec_ref(v___x_4682_);
v___x_4684_ = l_Lean_LocalDecl_userName(v_a_4665_);
lean_dec(v_a_4665_);
v___x_4685_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___closed__2));
v___x_4686_ = lean_box(0);
v___x_4687_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4687_, 0, v_a_4683_);
lean_ctor_set(v___x_4687_, 1, v___x_4686_);
v___x_4688_ = l_Lean_mkConst(v___x_4685_, v___x_4687_);
lean_inc(v_a_4662_);
v___x_4689_ = l_Lean_mkFVar(v_a_4662_);
lean_inc_ref(v_e_x27_4679_);
v___x_4690_ = l_Lean_mkApp4(v___x_4688_, v___x_4672_, v_e_x27_4679_, v_proof_4680_, v___x_4689_);
v___x_4691_ = 0;
v___x_4692_ = 0;
v___x_4693_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_4693_, 0, v___x_4684_);
lean_ctor_set(v___x_4693_, 1, v_e_x27_4679_);
lean_ctor_set(v___x_4693_, 2, v___x_4690_);
lean_ctor_set_uint8(v___x_4693_, sizeof(void*)*3, v___x_4691_);
lean_ctor_set_uint8(v___x_4693_, sizeof(void*)*3 + 1, v___x_4692_);
v___x_4694_ = lean_array_push(v_snd_4666_, v___x_4693_);
if (v_isShared_4669_ == 0)
{
lean_ctor_set(v___x_4668_, 1, v___x_4694_);
lean_ctor_set(v___x_4668_, 0, v___x_4671_);
v___x_4696_ = v___x_4668_;
goto v_reusejp_4695_;
}
else
{
lean_object* v_reuseFailAlloc_4697_; 
v_reuseFailAlloc_4697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4697_, 0, v___x_4671_);
lean_ctor_set(v_reuseFailAlloc_4697_, 1, v___x_4694_);
v___x_4696_ = v_reuseFailAlloc_4697_;
goto v_reusejp_4695_;
}
v_reusejp_4695_:
{
v_a_4656_ = v___x_4696_;
goto v___jp_4655_;
}
}
else
{
lean_object* v_a_4698_; lean_object* v___x_4700_; uint8_t v_isShared_4701_; uint8_t v_isSharedCheck_4705_; 
lean_dec_ref(v_proof_4680_);
lean_dec_ref(v_e_x27_4679_);
lean_dec_ref(v___x_4672_);
lean_del_object(v___x_4668_);
lean_dec(v_snd_4666_);
lean_dec(v_a_4665_);
lean_dec(v___y_4653_);
lean_dec_ref(v___y_4652_);
lean_dec(v___y_4651_);
lean_dec_ref(v___y_4650_);
lean_dec(v___y_4649_);
lean_dec_ref(v___y_4648_);
lean_dec_ref(v___x_4643_);
lean_dec(v_a_4642_);
v_a_4698_ = lean_ctor_get(v___x_4682_, 0);
v_isSharedCheck_4705_ = !lean_is_exclusive(v___x_4682_);
if (v_isSharedCheck_4705_ == 0)
{
v___x_4700_ = v___x_4682_;
v_isShared_4701_ = v_isSharedCheck_4705_;
goto v_resetjp_4699_;
}
else
{
lean_inc(v_a_4698_);
lean_dec(v___x_4682_);
v___x_4700_ = lean_box(0);
v_isShared_4701_ = v_isSharedCheck_4705_;
goto v_resetjp_4699_;
}
v_resetjp_4699_:
{
lean_object* v___x_4703_; 
if (v_isShared_4701_ == 0)
{
v___x_4703_ = v___x_4700_;
goto v_reusejp_4702_;
}
else
{
lean_object* v_reuseFailAlloc_4704_; 
v_reuseFailAlloc_4704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4704_, 0, v_a_4698_);
v___x_4703_ = v_reuseFailAlloc_4704_;
goto v_reusejp_4702_;
}
v_reusejp_4702_:
{
return v___x_4703_;
}
}
}
}
else
{
lean_object* v___x_4706_; 
lean_dec(v_a_4665_);
lean_dec(v___y_4649_);
lean_dec_ref(v___y_4648_);
lean_dec_ref(v___x_4643_);
lean_inc(v___y_4653_);
lean_inc_ref(v___y_4652_);
lean_inc(v___y_4651_);
lean_inc_ref(v___y_4650_);
lean_inc_ref(v___x_4672_);
v___x_4706_ = l_Lean_Meta_getLevel(v___x_4672_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_);
if (lean_obj_tag(v___x_4706_) == 0)
{
lean_object* v_a_4707_; lean_object* v___x_4708_; 
v_a_4707_ = lean_ctor_get(v___x_4706_, 0);
lean_inc(v_a_4707_);
lean_dec_ref(v___x_4706_);
lean_inc(v_a_4642_);
v___x_4708_ = l_Lean_MVarId_getType(v_a_4642_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_);
if (lean_obj_tag(v___x_4708_) == 0)
{
lean_object* v_a_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; 
v_a_4709_ = lean_ctor_get(v___x_4708_, 0);
lean_inc(v_a_4709_);
lean_dec_ref(v___x_4708_);
v___x_4710_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___closed__2));
v___x_4711_ = lean_box(0);
v___x_4712_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4712_, 0, v_a_4707_);
lean_ctor_set(v___x_4712_, 1, v___x_4711_);
v___x_4713_ = l_Lean_mkConst(v___x_4710_, v___x_4712_);
lean_inc(v_a_4662_);
v___x_4714_ = l_Lean_mkFVar(v_a_4662_);
v___x_4715_ = l_Lean_mkApp4(v___x_4713_, v___x_4672_, v_e_x27_4679_, v_proof_4680_, v___x_4714_);
lean_inc(v___y_4651_);
v___x_4716_ = l_Lean_Meta_mkFalseElim(v_a_4709_, v___x_4715_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_);
if (lean_obj_tag(v___x_4716_) == 0)
{
lean_object* v_a_4717_; lean_object* v___x_4718_; 
v_a_4717_ = lean_ctor_get(v___x_4716_, 0);
lean_inc(v_a_4717_);
lean_dec_ref(v___x_4716_);
v___x_4718_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0___redArg(v_a_4642_, v_a_4717_, v___y_4651_);
lean_dec(v___y_4651_);
if (lean_obj_tag(v___x_4718_) == 0)
{
lean_object* v___x_4720_; uint8_t v_isShared_4721_; uint8_t v_isSharedCheck_4729_; 
v_isSharedCheck_4729_ = !lean_is_exclusive(v___x_4718_);
if (v_isSharedCheck_4729_ == 0)
{
lean_object* v_unused_4730_; 
v_unused_4730_ = lean_ctor_get(v___x_4718_, 0);
lean_dec(v_unused_4730_);
v___x_4720_ = v___x_4718_;
v_isShared_4721_ = v_isSharedCheck_4729_;
goto v_resetjp_4719_;
}
else
{
lean_dec(v___x_4718_);
v___x_4720_ = lean_box(0);
v_isShared_4721_ = v_isSharedCheck_4729_;
goto v_resetjp_4719_;
}
v_resetjp_4719_:
{
lean_object* v___x_4722_; lean_object* v___x_4724_; 
v___x_4722_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___closed__3));
if (v_isShared_4669_ == 0)
{
lean_ctor_set(v___x_4668_, 0, v___x_4722_);
v___x_4724_ = v___x_4668_;
goto v_reusejp_4723_;
}
else
{
lean_object* v_reuseFailAlloc_4728_; 
v_reuseFailAlloc_4728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4728_, 0, v___x_4722_);
lean_ctor_set(v_reuseFailAlloc_4728_, 1, v_snd_4666_);
v___x_4724_ = v_reuseFailAlloc_4728_;
goto v_reusejp_4723_;
}
v_reusejp_4723_:
{
lean_object* v___x_4726_; 
if (v_isShared_4721_ == 0)
{
lean_ctor_set(v___x_4720_, 0, v___x_4724_);
v___x_4726_ = v___x_4720_;
goto v_reusejp_4725_;
}
else
{
lean_object* v_reuseFailAlloc_4727_; 
v_reuseFailAlloc_4727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4727_, 0, v___x_4724_);
v___x_4726_ = v_reuseFailAlloc_4727_;
goto v_reusejp_4725_;
}
v_reusejp_4725_:
{
return v___x_4726_;
}
}
}
}
else
{
lean_object* v_a_4731_; lean_object* v___x_4733_; uint8_t v_isShared_4734_; uint8_t v_isSharedCheck_4738_; 
lean_del_object(v___x_4668_);
lean_dec(v_snd_4666_);
v_a_4731_ = lean_ctor_get(v___x_4718_, 0);
v_isSharedCheck_4738_ = !lean_is_exclusive(v___x_4718_);
if (v_isSharedCheck_4738_ == 0)
{
v___x_4733_ = v___x_4718_;
v_isShared_4734_ = v_isSharedCheck_4738_;
goto v_resetjp_4732_;
}
else
{
lean_inc(v_a_4731_);
lean_dec(v___x_4718_);
v___x_4733_ = lean_box(0);
v_isShared_4734_ = v_isSharedCheck_4738_;
goto v_resetjp_4732_;
}
v_resetjp_4732_:
{
lean_object* v___x_4736_; 
if (v_isShared_4734_ == 0)
{
v___x_4736_ = v___x_4733_;
goto v_reusejp_4735_;
}
else
{
lean_object* v_reuseFailAlloc_4737_; 
v_reuseFailAlloc_4737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4737_, 0, v_a_4731_);
v___x_4736_ = v_reuseFailAlloc_4737_;
goto v_reusejp_4735_;
}
v_reusejp_4735_:
{
return v___x_4736_;
}
}
}
}
else
{
lean_object* v_a_4739_; lean_object* v___x_4741_; uint8_t v_isShared_4742_; uint8_t v_isSharedCheck_4746_; 
lean_del_object(v___x_4668_);
lean_dec(v_snd_4666_);
lean_dec(v___y_4651_);
lean_dec(v_a_4642_);
v_a_4739_ = lean_ctor_get(v___x_4716_, 0);
v_isSharedCheck_4746_ = !lean_is_exclusive(v___x_4716_);
if (v_isSharedCheck_4746_ == 0)
{
v___x_4741_ = v___x_4716_;
v_isShared_4742_ = v_isSharedCheck_4746_;
goto v_resetjp_4740_;
}
else
{
lean_inc(v_a_4739_);
lean_dec(v___x_4716_);
v___x_4741_ = lean_box(0);
v_isShared_4742_ = v_isSharedCheck_4746_;
goto v_resetjp_4740_;
}
v_resetjp_4740_:
{
lean_object* v___x_4744_; 
if (v_isShared_4742_ == 0)
{
v___x_4744_ = v___x_4741_;
goto v_reusejp_4743_;
}
else
{
lean_object* v_reuseFailAlloc_4745_; 
v_reuseFailAlloc_4745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4745_, 0, v_a_4739_);
v___x_4744_ = v_reuseFailAlloc_4745_;
goto v_reusejp_4743_;
}
v_reusejp_4743_:
{
return v___x_4744_;
}
}
}
}
else
{
lean_object* v_a_4747_; lean_object* v___x_4749_; uint8_t v_isShared_4750_; uint8_t v_isSharedCheck_4754_; 
lean_dec(v_a_4707_);
lean_dec_ref(v_proof_4680_);
lean_dec_ref(v_e_x27_4679_);
lean_dec_ref(v___x_4672_);
lean_del_object(v___x_4668_);
lean_dec(v_snd_4666_);
lean_dec(v___y_4653_);
lean_dec_ref(v___y_4652_);
lean_dec(v___y_4651_);
lean_dec_ref(v___y_4650_);
lean_dec(v_a_4642_);
v_a_4747_ = lean_ctor_get(v___x_4708_, 0);
v_isSharedCheck_4754_ = !lean_is_exclusive(v___x_4708_);
if (v_isSharedCheck_4754_ == 0)
{
v___x_4749_ = v___x_4708_;
v_isShared_4750_ = v_isSharedCheck_4754_;
goto v_resetjp_4748_;
}
else
{
lean_inc(v_a_4747_);
lean_dec(v___x_4708_);
v___x_4749_ = lean_box(0);
v_isShared_4750_ = v_isSharedCheck_4754_;
goto v_resetjp_4748_;
}
v_resetjp_4748_:
{
lean_object* v___x_4752_; 
if (v_isShared_4750_ == 0)
{
v___x_4752_ = v___x_4749_;
goto v_reusejp_4751_;
}
else
{
lean_object* v_reuseFailAlloc_4753_; 
v_reuseFailAlloc_4753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4753_, 0, v_a_4747_);
v___x_4752_ = v_reuseFailAlloc_4753_;
goto v_reusejp_4751_;
}
v_reusejp_4751_:
{
return v___x_4752_;
}
}
}
}
else
{
lean_object* v_a_4755_; lean_object* v___x_4757_; uint8_t v_isShared_4758_; uint8_t v_isSharedCheck_4762_; 
lean_dec_ref(v_proof_4680_);
lean_dec_ref(v_e_x27_4679_);
lean_dec_ref(v___x_4672_);
lean_del_object(v___x_4668_);
lean_dec(v_snd_4666_);
lean_dec(v___y_4653_);
lean_dec_ref(v___y_4652_);
lean_dec(v___y_4651_);
lean_dec_ref(v___y_4650_);
lean_dec(v_a_4642_);
v_a_4755_ = lean_ctor_get(v___x_4706_, 0);
v_isSharedCheck_4762_ = !lean_is_exclusive(v___x_4706_);
if (v_isSharedCheck_4762_ == 0)
{
v___x_4757_ = v___x_4706_;
v_isShared_4758_ = v_isSharedCheck_4762_;
goto v_resetjp_4756_;
}
else
{
lean_inc(v_a_4755_);
lean_dec(v___x_4706_);
v___x_4757_ = lean_box(0);
v_isShared_4758_ = v_isSharedCheck_4762_;
goto v_resetjp_4756_;
}
v_resetjp_4756_:
{
lean_object* v___x_4760_; 
if (v_isShared_4758_ == 0)
{
v___x_4760_ = v___x_4757_;
goto v_reusejp_4759_;
}
else
{
lean_object* v_reuseFailAlloc_4761_; 
v_reuseFailAlloc_4761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4761_, 0, v_a_4755_);
v___x_4760_ = v_reuseFailAlloc_4761_;
goto v_reusejp_4759_;
}
v_reusejp_4759_:
{
return v___x_4760_;
}
}
}
}
}
}
else
{
lean_object* v_a_4763_; lean_object* v___x_4765_; uint8_t v_isShared_4766_; uint8_t v_isSharedCheck_4770_; 
lean_dec_ref(v___x_4672_);
lean_del_object(v___x_4668_);
lean_dec(v_snd_4666_);
lean_dec(v_a_4665_);
lean_dec(v___y_4653_);
lean_dec_ref(v___y_4652_);
lean_dec(v___y_4651_);
lean_dec_ref(v___y_4650_);
lean_dec(v___y_4649_);
lean_dec_ref(v___y_4648_);
lean_dec_ref(v___x_4643_);
lean_dec(v_a_4642_);
v_a_4763_ = lean_ctor_get(v___y_4674_, 0);
v_isSharedCheck_4770_ = !lean_is_exclusive(v___y_4674_);
if (v_isSharedCheck_4770_ == 0)
{
v___x_4765_ = v___y_4674_;
v_isShared_4766_ = v_isSharedCheck_4770_;
goto v_resetjp_4764_;
}
else
{
lean_inc(v_a_4763_);
lean_dec(v___y_4674_);
v___x_4765_ = lean_box(0);
v_isShared_4766_ = v_isSharedCheck_4770_;
goto v_resetjp_4764_;
}
v_resetjp_4764_:
{
lean_object* v___x_4768_; 
if (v_isShared_4766_ == 0)
{
v___x_4768_ = v___x_4765_;
goto v_reusejp_4767_;
}
else
{
lean_object* v_reuseFailAlloc_4769_; 
v_reuseFailAlloc_4769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4769_, 0, v_a_4763_);
v___x_4768_ = v_reuseFailAlloc_4769_;
goto v_reusejp_4767_;
}
v_reusejp_4767_:
{
return v___x_4768_;
}
}
}
}
}
}
else
{
lean_object* v_a_4869_; lean_object* v___x_4871_; uint8_t v_isShared_4872_; uint8_t v_isSharedCheck_4876_; 
lean_dec(v___y_4653_);
lean_dec_ref(v___y_4652_);
lean_dec(v___y_4651_);
lean_dec_ref(v___y_4650_);
lean_dec(v___y_4649_);
lean_dec_ref(v___y_4648_);
lean_dec_ref(v_b_4647_);
lean_dec_ref(v___x_4643_);
lean_dec(v_a_4642_);
v_a_4869_ = lean_ctor_get(v___x_4663_, 0);
v_isSharedCheck_4876_ = !lean_is_exclusive(v___x_4663_);
if (v_isSharedCheck_4876_ == 0)
{
v___x_4871_ = v___x_4663_;
v_isShared_4872_ = v_isSharedCheck_4876_;
goto v_resetjp_4870_;
}
else
{
lean_inc(v_a_4869_);
lean_dec(v___x_4663_);
v___x_4871_ = lean_box(0);
v_isShared_4872_ = v_isSharedCheck_4876_;
goto v_resetjp_4870_;
}
v_resetjp_4870_:
{
lean_object* v___x_4874_; 
if (v_isShared_4872_ == 0)
{
v___x_4874_ = v___x_4871_;
goto v_reusejp_4873_;
}
else
{
lean_object* v_reuseFailAlloc_4875_; 
v_reuseFailAlloc_4875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4875_, 0, v_a_4869_);
v___x_4874_ = v_reuseFailAlloc_4875_;
goto v_reusejp_4873_;
}
v_reusejp_4873_:
{
return v___x_4874_;
}
}
}
}
v___jp_4655_:
{
size_t v___x_4657_; size_t v___x_4658_; 
v___x_4657_ = ((size_t)1ULL);
v___x_4658_ = lean_usize_add(v_i_4646_, v___x_4657_);
v_i_4646_ = v___x_4658_;
v_b_4647_ = v_a_4656_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___boxed(lean_object* v_a_4877_, lean_object* v___x_4878_, lean_object* v_as_4879_, lean_object* v_sz_4880_, lean_object* v_i_4881_, lean_object* v_b_4882_, lean_object* v___y_4883_, lean_object* v___y_4884_, lean_object* v___y_4885_, lean_object* v___y_4886_, lean_object* v___y_4887_, lean_object* v___y_4888_, lean_object* v___y_4889_){
_start:
{
size_t v_sz_boxed_4890_; size_t v_i_boxed_4891_; lean_object* v_res_4892_; 
v_sz_boxed_4890_ = lean_unbox_usize(v_sz_4880_);
lean_dec(v_sz_4880_);
v_i_boxed_4891_ = lean_unbox_usize(v_i_4881_);
lean_dec(v_i_4881_);
v_res_4892_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4(v_a_4877_, v___x_4878_, v_as_4879_, v_sz_boxed_4890_, v_i_boxed_4891_, v_b_4882_, v___y_4883_, v___y_4884_, v___y_4885_, v___y_4886_, v___y_4887_, v___y_4888_);
lean_dec_ref(v_as_4879_);
return v_res_4892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__1(lean_object* v_a_4893_, lean_object* v___x_4894_, lean_object* v_fvarIdsToSimp_4895_, size_t v_sz_4896_, size_t v___x_4897_, lean_object* v___x_4898_, uint8_t v_simplifyTarget_4899_, lean_object* v___y_4900_, lean_object* v___y_4901_, lean_object* v___y_4902_, lean_object* v___y_4903_, lean_object* v___y_4904_, lean_object* v___y_4905_){
_start:
{
lean_object* v___y_4908_; lean_object* v___y_4909_; lean_object* v___y_4910_; lean_object* v___y_4911_; lean_object* v___y_4912_; uint8_t v___y_4913_; lean_object* v___x_4933_; 
lean_inc(v___y_4905_);
lean_inc_ref(v___y_4904_);
lean_inc(v___y_4903_);
lean_inc_ref(v___y_4902_);
lean_inc(v___y_4901_);
lean_inc_ref(v___y_4900_);
lean_inc_ref(v___x_4894_);
lean_inc(v_a_4893_);
v___x_4933_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4(v_a_4893_, v___x_4894_, v_fvarIdsToSimp_4895_, v_sz_4896_, v___x_4897_, v___x_4898_, v___y_4900_, v___y_4901_, v___y_4902_, v___y_4903_, v___y_4904_, v___y_4905_);
if (lean_obj_tag(v___x_4933_) == 0)
{
lean_object* v_a_4934_; lean_object* v___x_4936_; uint8_t v_isShared_4937_; uint8_t v_isSharedCheck_5138_; 
v_a_4934_ = lean_ctor_get(v___x_4933_, 0);
v_isSharedCheck_5138_ = !lean_is_exclusive(v___x_4933_);
if (v_isSharedCheck_5138_ == 0)
{
v___x_4936_ = v___x_4933_;
v_isShared_4937_ = v_isSharedCheck_5138_;
goto v_resetjp_4935_;
}
else
{
lean_inc(v_a_4934_);
lean_dec(v___x_4933_);
v___x_4936_ = lean_box(0);
v_isShared_4937_ = v_isSharedCheck_5138_;
goto v_resetjp_4935_;
}
v_resetjp_4935_:
{
lean_object* v_fst_4938_; lean_object* v_snd_4939_; lean_object* v___x_4941_; uint8_t v_isShared_4942_; uint8_t v_isSharedCheck_5137_; 
v_fst_4938_ = lean_ctor_get(v_a_4934_, 0);
v_snd_4939_ = lean_ctor_get(v_a_4934_, 1);
v_isSharedCheck_5137_ = !lean_is_exclusive(v_a_4934_);
if (v_isSharedCheck_5137_ == 0)
{
v___x_4941_ = v_a_4934_;
v_isShared_4942_ = v_isSharedCheck_5137_;
goto v_resetjp_4940_;
}
else
{
lean_inc(v_snd_4939_);
lean_inc(v_fst_4938_);
lean_dec(v_a_4934_);
v___x_4941_ = lean_box(0);
v_isShared_4942_ = v_isSharedCheck_5137_;
goto v_resetjp_4940_;
}
v_resetjp_4940_:
{
lean_object* v_mvarIdNew_4944_; lean_object* v___y_4945_; lean_object* v___y_4946_; lean_object* v___y_4947_; lean_object* v___y_4948_; lean_object* v___y_4995_; 
if (lean_obj_tag(v_fst_4938_) == 0)
{
lean_del_object(v___x_4936_);
if (v_simplifyTarget_4899_ == 0)
{
lean_del_object(v___x_4941_);
lean_dec(v___y_4901_);
lean_dec_ref(v___y_4900_);
lean_dec_ref(v___x_4894_);
v_mvarIdNew_4944_ = v_a_4893_;
v___y_4945_ = v___y_4902_;
v___y_4946_ = v___y_4903_;
v___y_4947_ = v___y_4904_;
v___y_4948_ = v___y_4905_;
goto v___jp_4943_;
}
else
{
lean_object* v___x_5038_; 
lean_inc(v_a_4893_);
v___x_5038_ = l_Lean_MVarId_getType(v_a_4893_, v___y_4902_, v___y_4903_, v___y_4904_, v___y_4905_);
if (lean_obj_tag(v___x_5038_) == 0)
{
lean_object* v_options_5039_; uint8_t v_hasTrace_5040_; 
v_options_5039_ = lean_ctor_get(v___y_4904_, 2);
v_hasTrace_5040_ = lean_ctor_get_uint8(v_options_5039_, sizeof(void*)*1);
if (v_hasTrace_5040_ == 0)
{
lean_object* v_a_5041_; lean_object* v___x_5042_; 
lean_del_object(v___x_4941_);
v_a_5041_ = lean_ctor_get(v___x_5038_, 0);
lean_inc(v_a_5041_);
lean_dec_ref(v___x_5038_);
lean_inc(v___y_4905_);
lean_inc_ref(v___y_4904_);
lean_inc(v___y_4903_);
lean_inc_ref(v___y_4902_);
v___x_5042_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v_a_5041_, v___x_4894_, v___y_4900_, v___y_4901_, v___y_4902_, v___y_4903_, v___y_4904_, v___y_4905_);
v___y_4995_ = v___x_5042_;
goto v___jp_4994_;
}
else
{
lean_object* v_a_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; lean_object* v_a_5046_; lean_object* v___f_5047_; lean_object* v___x_5048_; lean_object* v___y_5050_; lean_object* v___y_5051_; lean_object* v_a_5052_; lean_object* v___y_5068_; lean_object* v___y_5069_; lean_object* v_a_5070_; uint8_t v___x_5121_; 
v_a_5043_ = lean_ctor_get(v___x_5038_, 0);
lean_inc(v_a_5043_);
lean_dec_ref(v___x_5038_);
v___x_5044_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0));
v___x_5045_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__1___redArg(v___x_5044_, v___y_4904_);
v_a_5046_ = lean_ctor_get(v___x_5045_, 0);
lean_inc(v_a_5046_);
lean_dec_ref(v___x_5045_);
lean_inc(v_a_5043_);
v___f_5047_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___boxed), 9, 1);
lean_closure_set(v___f_5047_, 0, v_a_5043_);
v___x_5048_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__1));
v___x_5121_ = lean_unbox(v_a_5046_);
if (v___x_5121_ == 0)
{
lean_object* v___x_5122_; uint8_t v___x_5123_; 
v___x_5122_ = l_Lean_trace_profiler;
v___x_5123_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2(v_options_5039_, v___x_5122_);
if (v___x_5123_ == 0)
{
lean_object* v___x_5124_; 
lean_dec_ref(v___f_5047_);
lean_dec(v_a_5046_);
lean_del_object(v___x_4941_);
lean_inc(v___y_4905_);
lean_inc_ref(v___y_4904_);
lean_inc(v___y_4903_);
lean_inc_ref(v___y_4902_);
v___x_5124_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v_a_5043_, v___x_4894_, v___y_4900_, v___y_4901_, v___y_4902_, v___y_4903_, v___y_4904_, v___y_4905_);
v___y_4995_ = v___x_5124_;
goto v___jp_4994_;
}
else
{
goto v___jp_5080_;
}
}
else
{
goto v___jp_5080_;
}
v___jp_5049_:
{
lean_object* v___x_5053_; double v___x_5054_; double v___x_5055_; double v___x_5056_; double v___x_5057_; double v___x_5058_; lean_object* v___x_5059_; lean_object* v___x_5060_; lean_object* v___x_5062_; 
v___x_5053_ = lean_io_mono_nanos_now();
v___x_5054_ = lean_float_of_nat(v___y_5050_);
v___x_5055_ = lean_float_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4);
v___x_5056_ = lean_float_div(v___x_5054_, v___x_5055_);
v___x_5057_ = lean_float_of_nat(v___x_5053_);
v___x_5058_ = lean_float_div(v___x_5057_, v___x_5055_);
v___x_5059_ = lean_box_float(v___x_5056_);
v___x_5060_ = lean_box_float(v___x_5058_);
if (v_isShared_4942_ == 0)
{
lean_ctor_set(v___x_4941_, 1, v___x_5060_);
lean_ctor_set(v___x_4941_, 0, v___x_5059_);
v___x_5062_ = v___x_4941_;
goto v_reusejp_5061_;
}
else
{
lean_object* v_reuseFailAlloc_5066_; 
v_reuseFailAlloc_5066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5066_, 0, v___x_5059_);
lean_ctor_set(v_reuseFailAlloc_5066_, 1, v___x_5060_);
v___x_5062_ = v_reuseFailAlloc_5066_;
goto v_reusejp_5061_;
}
v_reusejp_5061_:
{
lean_object* v___x_5063_; uint8_t v___x_5064_; lean_object* v___x_5065_; 
v___x_5063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5063_, 0, v_a_5052_);
lean_ctor_set(v___x_5063_, 1, v___x_5062_);
v___x_5064_ = lean_unbox(v_a_5046_);
lean_dec(v_a_5046_);
lean_inc(v___y_4905_);
lean_inc_ref(v___y_4904_);
lean_inc(v___y_4903_);
lean_inc_ref(v___y_4902_);
v___x_5065_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3(v___x_5044_, v_hasTrace_5040_, v___x_5048_, v_options_5039_, v___x_5064_, v___y_5051_, v___f_5047_, v___x_5063_, v___y_4900_, v___y_4901_, v___y_4902_, v___y_4903_, v___y_4904_, v___y_4905_);
v___y_4995_ = v___x_5065_;
goto v___jp_4994_;
}
}
v___jp_5067_:
{
lean_object* v___x_5071_; double v___x_5072_; double v___x_5073_; lean_object* v___x_5074_; lean_object* v___x_5075_; lean_object* v___x_5076_; lean_object* v___x_5077_; uint8_t v___x_5078_; lean_object* v___x_5079_; 
v___x_5071_ = lean_io_get_num_heartbeats();
v___x_5072_ = lean_float_of_nat(v___y_5068_);
v___x_5073_ = lean_float_of_nat(v___x_5071_);
v___x_5074_ = lean_box_float(v___x_5072_);
v___x_5075_ = lean_box_float(v___x_5073_);
v___x_5076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5076_, 0, v___x_5074_);
lean_ctor_set(v___x_5076_, 1, v___x_5075_);
v___x_5077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5077_, 0, v_a_5070_);
lean_ctor_set(v___x_5077_, 1, v___x_5076_);
v___x_5078_ = lean_unbox(v_a_5046_);
lean_dec(v_a_5046_);
lean_inc(v___y_4905_);
lean_inc_ref(v___y_4904_);
lean_inc(v___y_4903_);
lean_inc_ref(v___y_4902_);
v___x_5079_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3(v___x_5044_, v_hasTrace_5040_, v___x_5048_, v_options_5039_, v___x_5078_, v___y_5069_, v___f_5047_, v___x_5077_, v___y_4900_, v___y_4901_, v___y_4902_, v___y_4903_, v___y_4904_, v___y_4905_);
v___y_4995_ = v___x_5079_;
goto v___jp_4994_;
}
v___jp_5080_:
{
lean_object* v___x_5081_; lean_object* v_a_5082_; lean_object* v___x_5083_; uint8_t v___x_5084_; 
v___x_5081_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2___redArg(v___y_4905_);
v_a_5082_ = lean_ctor_get(v___x_5081_, 0);
lean_inc(v_a_5082_);
lean_dec_ref(v___x_5081_);
v___x_5083_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5084_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2(v_options_5039_, v___x_5083_);
if (v___x_5084_ == 0)
{
lean_object* v___x_5085_; lean_object* v___x_5086_; 
v___x_5085_ = lean_io_mono_nanos_now();
lean_inc(v___y_4905_);
lean_inc_ref(v___y_4904_);
lean_inc(v___y_4903_);
lean_inc_ref(v___y_4902_);
lean_inc(v___y_4901_);
lean_inc_ref(v___y_4900_);
v___x_5086_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v_a_5043_, v___x_4894_, v___y_4900_, v___y_4901_, v___y_4902_, v___y_4903_, v___y_4904_, v___y_4905_);
if (lean_obj_tag(v___x_5086_) == 0)
{
lean_object* v_a_5087_; lean_object* v___x_5089_; uint8_t v_isShared_5090_; uint8_t v_isSharedCheck_5094_; 
v_a_5087_ = lean_ctor_get(v___x_5086_, 0);
v_isSharedCheck_5094_ = !lean_is_exclusive(v___x_5086_);
if (v_isSharedCheck_5094_ == 0)
{
v___x_5089_ = v___x_5086_;
v_isShared_5090_ = v_isSharedCheck_5094_;
goto v_resetjp_5088_;
}
else
{
lean_inc(v_a_5087_);
lean_dec(v___x_5086_);
v___x_5089_ = lean_box(0);
v_isShared_5090_ = v_isSharedCheck_5094_;
goto v_resetjp_5088_;
}
v_resetjp_5088_:
{
lean_object* v___x_5092_; 
if (v_isShared_5090_ == 0)
{
lean_ctor_set_tag(v___x_5089_, 1);
v___x_5092_ = v___x_5089_;
goto v_reusejp_5091_;
}
else
{
lean_object* v_reuseFailAlloc_5093_; 
v_reuseFailAlloc_5093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5093_, 0, v_a_5087_);
v___x_5092_ = v_reuseFailAlloc_5093_;
goto v_reusejp_5091_;
}
v_reusejp_5091_:
{
v___y_5050_ = v___x_5085_;
v___y_5051_ = v_a_5082_;
v_a_5052_ = v___x_5092_;
goto v___jp_5049_;
}
}
}
else
{
lean_object* v_a_5095_; lean_object* v___x_5097_; uint8_t v_isShared_5098_; uint8_t v_isSharedCheck_5102_; 
v_a_5095_ = lean_ctor_get(v___x_5086_, 0);
v_isSharedCheck_5102_ = !lean_is_exclusive(v___x_5086_);
if (v_isSharedCheck_5102_ == 0)
{
v___x_5097_ = v___x_5086_;
v_isShared_5098_ = v_isSharedCheck_5102_;
goto v_resetjp_5096_;
}
else
{
lean_inc(v_a_5095_);
lean_dec(v___x_5086_);
v___x_5097_ = lean_box(0);
v_isShared_5098_ = v_isSharedCheck_5102_;
goto v_resetjp_5096_;
}
v_resetjp_5096_:
{
lean_object* v___x_5100_; 
if (v_isShared_5098_ == 0)
{
lean_ctor_set_tag(v___x_5097_, 0);
v___x_5100_ = v___x_5097_;
goto v_reusejp_5099_;
}
else
{
lean_object* v_reuseFailAlloc_5101_; 
v_reuseFailAlloc_5101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5101_, 0, v_a_5095_);
v___x_5100_ = v_reuseFailAlloc_5101_;
goto v_reusejp_5099_;
}
v_reusejp_5099_:
{
v___y_5050_ = v___x_5085_;
v___y_5051_ = v_a_5082_;
v_a_5052_ = v___x_5100_;
goto v___jp_5049_;
}
}
}
}
else
{
lean_object* v___x_5103_; lean_object* v___x_5104_; 
lean_del_object(v___x_4941_);
v___x_5103_ = lean_io_get_num_heartbeats();
lean_inc(v___y_4905_);
lean_inc_ref(v___y_4904_);
lean_inc(v___y_4903_);
lean_inc_ref(v___y_4902_);
lean_inc(v___y_4901_);
lean_inc_ref(v___y_4900_);
v___x_5104_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v_a_5043_, v___x_4894_, v___y_4900_, v___y_4901_, v___y_4902_, v___y_4903_, v___y_4904_, v___y_4905_);
if (lean_obj_tag(v___x_5104_) == 0)
{
lean_object* v_a_5105_; lean_object* v___x_5107_; uint8_t v_isShared_5108_; uint8_t v_isSharedCheck_5112_; 
v_a_5105_ = lean_ctor_get(v___x_5104_, 0);
v_isSharedCheck_5112_ = !lean_is_exclusive(v___x_5104_);
if (v_isSharedCheck_5112_ == 0)
{
v___x_5107_ = v___x_5104_;
v_isShared_5108_ = v_isSharedCheck_5112_;
goto v_resetjp_5106_;
}
else
{
lean_inc(v_a_5105_);
lean_dec(v___x_5104_);
v___x_5107_ = lean_box(0);
v_isShared_5108_ = v_isSharedCheck_5112_;
goto v_resetjp_5106_;
}
v_resetjp_5106_:
{
lean_object* v___x_5110_; 
if (v_isShared_5108_ == 0)
{
lean_ctor_set_tag(v___x_5107_, 1);
v___x_5110_ = v___x_5107_;
goto v_reusejp_5109_;
}
else
{
lean_object* v_reuseFailAlloc_5111_; 
v_reuseFailAlloc_5111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5111_, 0, v_a_5105_);
v___x_5110_ = v_reuseFailAlloc_5111_;
goto v_reusejp_5109_;
}
v_reusejp_5109_:
{
v___y_5068_ = v___x_5103_;
v___y_5069_ = v_a_5082_;
v_a_5070_ = v___x_5110_;
goto v___jp_5067_;
}
}
}
else
{
lean_object* v_a_5113_; lean_object* v___x_5115_; uint8_t v_isShared_5116_; uint8_t v_isSharedCheck_5120_; 
v_a_5113_ = lean_ctor_get(v___x_5104_, 0);
v_isSharedCheck_5120_ = !lean_is_exclusive(v___x_5104_);
if (v_isSharedCheck_5120_ == 0)
{
v___x_5115_ = v___x_5104_;
v_isShared_5116_ = v_isSharedCheck_5120_;
goto v_resetjp_5114_;
}
else
{
lean_inc(v_a_5113_);
lean_dec(v___x_5104_);
v___x_5115_ = lean_box(0);
v_isShared_5116_ = v_isSharedCheck_5120_;
goto v_resetjp_5114_;
}
v_resetjp_5114_:
{
lean_object* v___x_5118_; 
if (v_isShared_5116_ == 0)
{
lean_ctor_set_tag(v___x_5115_, 0);
v___x_5118_ = v___x_5115_;
goto v_reusejp_5117_;
}
else
{
lean_object* v_reuseFailAlloc_5119_; 
v_reuseFailAlloc_5119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5119_, 0, v_a_5113_);
v___x_5118_ = v_reuseFailAlloc_5119_;
goto v_reusejp_5117_;
}
v_reusejp_5117_:
{
v___y_5068_ = v___x_5103_;
v___y_5069_ = v_a_5082_;
v_a_5070_ = v___x_5118_;
goto v___jp_5067_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5125_; lean_object* v___x_5127_; uint8_t v_isShared_5128_; uint8_t v_isSharedCheck_5132_; 
lean_del_object(v___x_4941_);
lean_dec(v_snd_4939_);
lean_dec(v___y_4905_);
lean_dec_ref(v___y_4904_);
lean_dec(v___y_4903_);
lean_dec_ref(v___y_4902_);
lean_dec(v___y_4901_);
lean_dec_ref(v___y_4900_);
lean_dec_ref(v___x_4894_);
lean_dec(v_a_4893_);
v_a_5125_ = lean_ctor_get(v___x_5038_, 0);
v_isSharedCheck_5132_ = !lean_is_exclusive(v___x_5038_);
if (v_isSharedCheck_5132_ == 0)
{
v___x_5127_ = v___x_5038_;
v_isShared_5128_ = v_isSharedCheck_5132_;
goto v_resetjp_5126_;
}
else
{
lean_inc(v_a_5125_);
lean_dec(v___x_5038_);
v___x_5127_ = lean_box(0);
v_isShared_5128_ = v_isSharedCheck_5132_;
goto v_resetjp_5126_;
}
v_resetjp_5126_:
{
lean_object* v___x_5130_; 
if (v_isShared_5128_ == 0)
{
v___x_5130_ = v___x_5127_;
goto v_reusejp_5129_;
}
else
{
lean_object* v_reuseFailAlloc_5131_; 
v_reuseFailAlloc_5131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5131_, 0, v_a_5125_);
v___x_5130_ = v_reuseFailAlloc_5131_;
goto v_reusejp_5129_;
}
v_reusejp_5129_:
{
return v___x_5130_;
}
}
}
}
}
else
{
lean_object* v_val_5133_; lean_object* v___x_5135_; 
lean_del_object(v___x_4941_);
lean_dec(v_snd_4939_);
lean_dec(v___y_4905_);
lean_dec_ref(v___y_4904_);
lean_dec(v___y_4903_);
lean_dec_ref(v___y_4902_);
lean_dec(v___y_4901_);
lean_dec_ref(v___y_4900_);
lean_dec_ref(v___x_4894_);
lean_dec(v_a_4893_);
v_val_5133_ = lean_ctor_get(v_fst_4938_, 0);
lean_inc(v_val_5133_);
lean_dec_ref(v_fst_4938_);
if (v_isShared_4937_ == 0)
{
lean_ctor_set(v___x_4936_, 0, v_val_5133_);
v___x_5135_ = v___x_4936_;
goto v_reusejp_5134_;
}
else
{
lean_object* v_reuseFailAlloc_5136_; 
v_reuseFailAlloc_5136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5136_, 0, v_val_5133_);
v___x_5135_ = v_reuseFailAlloc_5136_;
goto v_reusejp_5134_;
}
v_reusejp_5134_:
{
return v___x_5135_;
}
}
v___jp_4943_:
{
lean_object* v___x_4949_; 
lean_inc(v___y_4948_);
lean_inc_ref(v___y_4947_);
lean_inc(v___y_4946_);
lean_inc_ref(v___y_4945_);
v___x_4949_ = l_Lean_MVarId_assertHypotheses(v_mvarIdNew_4944_, v_snd_4939_, v___y_4945_, v___y_4946_, v___y_4947_, v___y_4948_);
if (lean_obj_tag(v___x_4949_) == 0)
{
lean_object* v_a_4950_; lean_object* v_snd_4951_; lean_object* v___x_4952_; 
v_a_4950_ = lean_ctor_get(v___x_4949_, 0);
lean_inc(v_a_4950_);
lean_dec_ref(v___x_4949_);
v_snd_4951_ = lean_ctor_get(v_a_4950_, 1);
lean_inc(v_snd_4951_);
lean_dec(v_a_4950_);
lean_inc(v___y_4948_);
lean_inc_ref(v___y_4947_);
lean_inc(v___y_4946_);
lean_inc_ref(v___y_4945_);
v___x_4952_ = l_Lean_MVarId_tryClearMany(v_snd_4951_, v_fvarIdsToSimp_4895_, v___y_4945_, v___y_4946_, v___y_4947_, v___y_4948_);
if (lean_obj_tag(v___x_4952_) == 0)
{
lean_object* v_a_4953_; lean_object* v___x_4954_; 
v_a_4953_ = lean_ctor_get(v___x_4952_, 0);
lean_inc(v_a_4953_);
lean_dec_ref(v___x_4952_);
v___x_4954_ = l_Lean_Meta_saveState___redArg(v___y_4946_, v___y_4948_);
if (lean_obj_tag(v___x_4954_) == 0)
{
lean_object* v_a_4955_; uint8_t v___x_4956_; lean_object* v___x_4957_; 
v_a_4955_ = lean_ctor_get(v___x_4954_, 0);
lean_inc(v_a_4955_);
lean_dec_ref(v___x_4954_);
v___x_4956_ = 1;
lean_inc(v___y_4948_);
lean_inc(v___y_4946_);
lean_inc(v_a_4953_);
v___x_4957_ = l_Lean_MVarId_refl(v_a_4953_, v___x_4956_, v___y_4945_, v___y_4946_, v___y_4947_, v___y_4948_);
if (lean_obj_tag(v___x_4957_) == 0)
{
lean_object* v___x_4959_; uint8_t v_isShared_4960_; uint8_t v_isSharedCheck_4965_; 
lean_dec(v_a_4955_);
lean_dec(v_a_4953_);
lean_dec(v___y_4948_);
lean_dec(v___y_4946_);
v_isSharedCheck_4965_ = !lean_is_exclusive(v___x_4957_);
if (v_isSharedCheck_4965_ == 0)
{
lean_object* v_unused_4966_; 
v_unused_4966_ = lean_ctor_get(v___x_4957_, 0);
lean_dec(v_unused_4966_);
v___x_4959_ = v___x_4957_;
v_isShared_4960_ = v_isSharedCheck_4965_;
goto v_resetjp_4958_;
}
else
{
lean_dec(v___x_4957_);
v___x_4959_ = lean_box(0);
v_isShared_4960_ = v_isSharedCheck_4965_;
goto v_resetjp_4958_;
}
v_resetjp_4958_:
{
lean_object* v___x_4961_; lean_object* v___x_4963_; 
v___x_4961_ = lean_box(0);
if (v_isShared_4960_ == 0)
{
lean_ctor_set(v___x_4959_, 0, v___x_4961_);
v___x_4963_ = v___x_4959_;
goto v_reusejp_4962_;
}
else
{
lean_object* v_reuseFailAlloc_4964_; 
v_reuseFailAlloc_4964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4964_, 0, v___x_4961_);
v___x_4963_ = v_reuseFailAlloc_4964_;
goto v_reusejp_4962_;
}
v_reusejp_4962_:
{
return v___x_4963_;
}
}
}
else
{
lean_object* v_a_4967_; uint8_t v___x_4968_; 
v_a_4967_ = lean_ctor_get(v___x_4957_, 0);
lean_inc(v_a_4967_);
lean_dec_ref(v___x_4957_);
v___x_4968_ = l_Lean_Exception_isInterrupt(v_a_4967_);
if (v___x_4968_ == 0)
{
uint8_t v___x_4969_; 
lean_inc(v_a_4967_);
v___x_4969_ = l_Lean_Exception_isRuntime(v_a_4967_);
v___y_4908_ = v_a_4967_;
v___y_4909_ = v_a_4955_;
v___y_4910_ = v___y_4948_;
v___y_4911_ = v_a_4953_;
v___y_4912_ = v___y_4946_;
v___y_4913_ = v___x_4969_;
goto v___jp_4907_;
}
else
{
v___y_4908_ = v_a_4967_;
v___y_4909_ = v_a_4955_;
v___y_4910_ = v___y_4948_;
v___y_4911_ = v_a_4953_;
v___y_4912_ = v___y_4946_;
v___y_4913_ = v___x_4968_;
goto v___jp_4907_;
}
}
}
else
{
lean_object* v_a_4970_; lean_object* v___x_4972_; uint8_t v_isShared_4973_; uint8_t v_isSharedCheck_4977_; 
lean_dec(v_a_4953_);
lean_dec(v___y_4948_);
lean_dec_ref(v___y_4947_);
lean_dec(v___y_4946_);
lean_dec_ref(v___y_4945_);
v_a_4970_ = lean_ctor_get(v___x_4954_, 0);
v_isSharedCheck_4977_ = !lean_is_exclusive(v___x_4954_);
if (v_isSharedCheck_4977_ == 0)
{
v___x_4972_ = v___x_4954_;
v_isShared_4973_ = v_isSharedCheck_4977_;
goto v_resetjp_4971_;
}
else
{
lean_inc(v_a_4970_);
lean_dec(v___x_4954_);
v___x_4972_ = lean_box(0);
v_isShared_4973_ = v_isSharedCheck_4977_;
goto v_resetjp_4971_;
}
v_resetjp_4971_:
{
lean_object* v___x_4975_; 
if (v_isShared_4973_ == 0)
{
v___x_4975_ = v___x_4972_;
goto v_reusejp_4974_;
}
else
{
lean_object* v_reuseFailAlloc_4976_; 
v_reuseFailAlloc_4976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4976_, 0, v_a_4970_);
v___x_4975_ = v_reuseFailAlloc_4976_;
goto v_reusejp_4974_;
}
v_reusejp_4974_:
{
return v___x_4975_;
}
}
}
}
else
{
lean_object* v_a_4978_; lean_object* v___x_4980_; uint8_t v_isShared_4981_; uint8_t v_isSharedCheck_4985_; 
lean_dec(v___y_4948_);
lean_dec_ref(v___y_4947_);
lean_dec(v___y_4946_);
lean_dec_ref(v___y_4945_);
v_a_4978_ = lean_ctor_get(v___x_4952_, 0);
v_isSharedCheck_4985_ = !lean_is_exclusive(v___x_4952_);
if (v_isSharedCheck_4985_ == 0)
{
v___x_4980_ = v___x_4952_;
v_isShared_4981_ = v_isSharedCheck_4985_;
goto v_resetjp_4979_;
}
else
{
lean_inc(v_a_4978_);
lean_dec(v___x_4952_);
v___x_4980_ = lean_box(0);
v_isShared_4981_ = v_isSharedCheck_4985_;
goto v_resetjp_4979_;
}
v_resetjp_4979_:
{
lean_object* v___x_4983_; 
if (v_isShared_4981_ == 0)
{
v___x_4983_ = v___x_4980_;
goto v_reusejp_4982_;
}
else
{
lean_object* v_reuseFailAlloc_4984_; 
v_reuseFailAlloc_4984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4984_, 0, v_a_4978_);
v___x_4983_ = v_reuseFailAlloc_4984_;
goto v_reusejp_4982_;
}
v_reusejp_4982_:
{
return v___x_4983_;
}
}
}
}
else
{
lean_object* v_a_4986_; lean_object* v___x_4988_; uint8_t v_isShared_4989_; uint8_t v_isSharedCheck_4993_; 
lean_dec(v___y_4948_);
lean_dec_ref(v___y_4947_);
lean_dec(v___y_4946_);
lean_dec_ref(v___y_4945_);
v_a_4986_ = lean_ctor_get(v___x_4949_, 0);
v_isSharedCheck_4993_ = !lean_is_exclusive(v___x_4949_);
if (v_isSharedCheck_4993_ == 0)
{
v___x_4988_ = v___x_4949_;
v_isShared_4989_ = v_isSharedCheck_4993_;
goto v_resetjp_4987_;
}
else
{
lean_inc(v_a_4986_);
lean_dec(v___x_4949_);
v___x_4988_ = lean_box(0);
v_isShared_4989_ = v_isSharedCheck_4993_;
goto v_resetjp_4987_;
}
v_resetjp_4987_:
{
lean_object* v___x_4991_; 
if (v_isShared_4989_ == 0)
{
v___x_4991_ = v___x_4988_;
goto v_reusejp_4990_;
}
else
{
lean_object* v_reuseFailAlloc_4992_; 
v_reuseFailAlloc_4992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4992_, 0, v_a_4986_);
v___x_4991_ = v_reuseFailAlloc_4992_;
goto v_reusejp_4990_;
}
v_reusejp_4990_:
{
return v___x_4991_;
}
}
}
}
v___jp_4994_:
{
if (lean_obj_tag(v___y_4995_) == 0)
{
lean_object* v_a_4996_; 
v_a_4996_ = lean_ctor_get(v___y_4995_, 0);
lean_inc(v_a_4996_);
lean_dec_ref(v___y_4995_);
if (lean_obj_tag(v_a_4996_) == 0)
{
lean_dec_ref(v_a_4996_);
v_mvarIdNew_4944_ = v_a_4893_;
v___y_4945_ = v___y_4902_;
v___y_4946_ = v___y_4903_;
v___y_4947_ = v___y_4904_;
v___y_4948_ = v___y_4905_;
goto v___jp_4943_;
}
else
{
lean_object* v_e_x27_4997_; lean_object* v_proof_4998_; uint8_t v___x_4999_; 
v_e_x27_4997_ = lean_ctor_get(v_a_4996_, 0);
lean_inc_ref(v_e_x27_4997_);
v_proof_4998_ = lean_ctor_get(v_a_4996_, 1);
lean_inc_ref(v_proof_4998_);
lean_dec_ref(v_a_4996_);
lean_inc_ref(v_e_x27_4997_);
v___x_4999_ = l_Lean_Expr_isTrue(v_e_x27_4997_);
if (v___x_4999_ == 0)
{
lean_object* v___x_5000_; 
lean_inc(v___y_4905_);
lean_inc_ref(v___y_4904_);
lean_inc(v___y_4903_);
lean_inc_ref(v___y_4902_);
v___x_5000_ = l_Lean_MVarId_replaceTargetEq(v_a_4893_, v_e_x27_4997_, v_proof_4998_, v___y_4902_, v___y_4903_, v___y_4904_, v___y_4905_);
if (lean_obj_tag(v___x_5000_) == 0)
{
lean_object* v_a_5001_; 
v_a_5001_ = lean_ctor_get(v___x_5000_, 0);
lean_inc(v_a_5001_);
lean_dec_ref(v___x_5000_);
v_mvarIdNew_4944_ = v_a_5001_;
v___y_4945_ = v___y_4902_;
v___y_4946_ = v___y_4903_;
v___y_4947_ = v___y_4904_;
v___y_4948_ = v___y_4905_;
goto v___jp_4943_;
}
else
{
lean_object* v_a_5002_; lean_object* v___x_5004_; uint8_t v_isShared_5005_; uint8_t v_isSharedCheck_5009_; 
lean_dec(v_snd_4939_);
lean_dec(v___y_4905_);
lean_dec_ref(v___y_4904_);
lean_dec(v___y_4903_);
lean_dec_ref(v___y_4902_);
v_a_5002_ = lean_ctor_get(v___x_5000_, 0);
v_isSharedCheck_5009_ = !lean_is_exclusive(v___x_5000_);
if (v_isSharedCheck_5009_ == 0)
{
v___x_5004_ = v___x_5000_;
v_isShared_5005_ = v_isSharedCheck_5009_;
goto v_resetjp_5003_;
}
else
{
lean_inc(v_a_5002_);
lean_dec(v___x_5000_);
v___x_5004_ = lean_box(0);
v_isShared_5005_ = v_isSharedCheck_5009_;
goto v_resetjp_5003_;
}
v_resetjp_5003_:
{
lean_object* v___x_5007_; 
if (v_isShared_5005_ == 0)
{
v___x_5007_ = v___x_5004_;
goto v_reusejp_5006_;
}
else
{
lean_object* v_reuseFailAlloc_5008_; 
v_reuseFailAlloc_5008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5008_, 0, v_a_5002_);
v___x_5007_ = v_reuseFailAlloc_5008_;
goto v_reusejp_5006_;
}
v_reusejp_5006_:
{
return v___x_5007_;
}
}
}
}
else
{
lean_object* v___x_5010_; 
lean_dec_ref(v_e_x27_4997_);
lean_dec(v_snd_4939_);
lean_inc(v___y_4903_);
v___x_5010_ = l_Lean_Meta_mkOfEqTrue(v_proof_4998_, v___y_4902_, v___y_4903_, v___y_4904_, v___y_4905_);
if (lean_obj_tag(v___x_5010_) == 0)
{
lean_object* v_a_5011_; lean_object* v___x_5012_; lean_object* v___x_5014_; uint8_t v_isShared_5015_; uint8_t v_isSharedCheck_5020_; 
v_a_5011_ = lean_ctor_get(v___x_5010_, 0);
lean_inc(v_a_5011_);
lean_dec_ref(v___x_5010_);
v___x_5012_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0___redArg(v_a_4893_, v_a_5011_, v___y_4903_);
lean_dec(v___y_4903_);
v_isSharedCheck_5020_ = !lean_is_exclusive(v___x_5012_);
if (v_isSharedCheck_5020_ == 0)
{
lean_object* v_unused_5021_; 
v_unused_5021_ = lean_ctor_get(v___x_5012_, 0);
lean_dec(v_unused_5021_);
v___x_5014_ = v___x_5012_;
v_isShared_5015_ = v_isSharedCheck_5020_;
goto v_resetjp_5013_;
}
else
{
lean_dec(v___x_5012_);
v___x_5014_ = lean_box(0);
v_isShared_5015_ = v_isSharedCheck_5020_;
goto v_resetjp_5013_;
}
v_resetjp_5013_:
{
lean_object* v___x_5016_; lean_object* v___x_5018_; 
v___x_5016_ = lean_box(0);
if (v_isShared_5015_ == 0)
{
lean_ctor_set(v___x_5014_, 0, v___x_5016_);
v___x_5018_ = v___x_5014_;
goto v_reusejp_5017_;
}
else
{
lean_object* v_reuseFailAlloc_5019_; 
v_reuseFailAlloc_5019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5019_, 0, v___x_5016_);
v___x_5018_ = v_reuseFailAlloc_5019_;
goto v_reusejp_5017_;
}
v_reusejp_5017_:
{
return v___x_5018_;
}
}
}
else
{
lean_object* v_a_5022_; lean_object* v___x_5024_; uint8_t v_isShared_5025_; uint8_t v_isSharedCheck_5029_; 
lean_dec(v___y_4903_);
lean_dec(v_a_4893_);
v_a_5022_ = lean_ctor_get(v___x_5010_, 0);
v_isSharedCheck_5029_ = !lean_is_exclusive(v___x_5010_);
if (v_isSharedCheck_5029_ == 0)
{
v___x_5024_ = v___x_5010_;
v_isShared_5025_ = v_isSharedCheck_5029_;
goto v_resetjp_5023_;
}
else
{
lean_inc(v_a_5022_);
lean_dec(v___x_5010_);
v___x_5024_ = lean_box(0);
v_isShared_5025_ = v_isSharedCheck_5029_;
goto v_resetjp_5023_;
}
v_resetjp_5023_:
{
lean_object* v___x_5027_; 
if (v_isShared_5025_ == 0)
{
v___x_5027_ = v___x_5024_;
goto v_reusejp_5026_;
}
else
{
lean_object* v_reuseFailAlloc_5028_; 
v_reuseFailAlloc_5028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5028_, 0, v_a_5022_);
v___x_5027_ = v_reuseFailAlloc_5028_;
goto v_reusejp_5026_;
}
v_reusejp_5026_:
{
return v___x_5027_;
}
}
}
}
}
}
else
{
lean_object* v_a_5030_; lean_object* v___x_5032_; uint8_t v_isShared_5033_; uint8_t v_isSharedCheck_5037_; 
lean_dec(v_snd_4939_);
lean_dec(v___y_4905_);
lean_dec_ref(v___y_4904_);
lean_dec(v___y_4903_);
lean_dec_ref(v___y_4902_);
lean_dec(v_a_4893_);
v_a_5030_ = lean_ctor_get(v___y_4995_, 0);
v_isSharedCheck_5037_ = !lean_is_exclusive(v___y_4995_);
if (v_isSharedCheck_5037_ == 0)
{
v___x_5032_ = v___y_4995_;
v_isShared_5033_ = v_isSharedCheck_5037_;
goto v_resetjp_5031_;
}
else
{
lean_inc(v_a_5030_);
lean_dec(v___y_4995_);
v___x_5032_ = lean_box(0);
v_isShared_5033_ = v_isSharedCheck_5037_;
goto v_resetjp_5031_;
}
v_resetjp_5031_:
{
lean_object* v___x_5035_; 
if (v_isShared_5033_ == 0)
{
v___x_5035_ = v___x_5032_;
goto v_reusejp_5034_;
}
else
{
lean_object* v_reuseFailAlloc_5036_; 
v_reuseFailAlloc_5036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5036_, 0, v_a_5030_);
v___x_5035_ = v_reuseFailAlloc_5036_;
goto v_reusejp_5034_;
}
v_reusejp_5034_:
{
return v___x_5035_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5139_; lean_object* v___x_5141_; uint8_t v_isShared_5142_; uint8_t v_isSharedCheck_5146_; 
lean_dec(v___y_4905_);
lean_dec_ref(v___y_4904_);
lean_dec(v___y_4903_);
lean_dec_ref(v___y_4902_);
lean_dec(v___y_4901_);
lean_dec_ref(v___y_4900_);
lean_dec_ref(v___x_4894_);
lean_dec(v_a_4893_);
v_a_5139_ = lean_ctor_get(v___x_4933_, 0);
v_isSharedCheck_5146_ = !lean_is_exclusive(v___x_4933_);
if (v_isSharedCheck_5146_ == 0)
{
v___x_5141_ = v___x_4933_;
v_isShared_5142_ = v_isSharedCheck_5146_;
goto v_resetjp_5140_;
}
else
{
lean_inc(v_a_5139_);
lean_dec(v___x_4933_);
v___x_5141_ = lean_box(0);
v_isShared_5142_ = v_isSharedCheck_5146_;
goto v_resetjp_5140_;
}
v_resetjp_5140_:
{
lean_object* v___x_5144_; 
if (v_isShared_5142_ == 0)
{
v___x_5144_ = v___x_5141_;
goto v_reusejp_5143_;
}
else
{
lean_object* v_reuseFailAlloc_5145_; 
v_reuseFailAlloc_5145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5145_, 0, v_a_5139_);
v___x_5144_ = v_reuseFailAlloc_5145_;
goto v_reusejp_5143_;
}
v_reusejp_5143_:
{
return v___x_5144_;
}
}
}
v___jp_4907_:
{
if (v___y_4913_ == 0)
{
lean_object* v___x_4914_; 
lean_dec_ref(v___y_4908_);
v___x_4914_ = l_Lean_Meta_SavedState_restore___redArg(v___y_4909_, v___y_4912_, v___y_4910_);
lean_dec(v___y_4910_);
lean_dec(v___y_4912_);
lean_dec_ref(v___y_4909_);
if (lean_obj_tag(v___x_4914_) == 0)
{
lean_object* v___x_4916_; uint8_t v_isShared_4917_; uint8_t v_isSharedCheck_4922_; 
v_isSharedCheck_4922_ = !lean_is_exclusive(v___x_4914_);
if (v_isSharedCheck_4922_ == 0)
{
lean_object* v_unused_4923_; 
v_unused_4923_ = lean_ctor_get(v___x_4914_, 0);
lean_dec(v_unused_4923_);
v___x_4916_ = v___x_4914_;
v_isShared_4917_ = v_isSharedCheck_4922_;
goto v_resetjp_4915_;
}
else
{
lean_dec(v___x_4914_);
v___x_4916_ = lean_box(0);
v_isShared_4917_ = v_isSharedCheck_4922_;
goto v_resetjp_4915_;
}
v_resetjp_4915_:
{
lean_object* v___x_4918_; lean_object* v___x_4920_; 
v___x_4918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4918_, 0, v___y_4911_);
if (v_isShared_4917_ == 0)
{
lean_ctor_set(v___x_4916_, 0, v___x_4918_);
v___x_4920_ = v___x_4916_;
goto v_reusejp_4919_;
}
else
{
lean_object* v_reuseFailAlloc_4921_; 
v_reuseFailAlloc_4921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4921_, 0, v___x_4918_);
v___x_4920_ = v_reuseFailAlloc_4921_;
goto v_reusejp_4919_;
}
v_reusejp_4919_:
{
return v___x_4920_;
}
}
}
else
{
lean_object* v_a_4924_; lean_object* v___x_4926_; uint8_t v_isShared_4927_; uint8_t v_isSharedCheck_4931_; 
lean_dec(v___y_4911_);
v_a_4924_ = lean_ctor_get(v___x_4914_, 0);
v_isSharedCheck_4931_ = !lean_is_exclusive(v___x_4914_);
if (v_isSharedCheck_4931_ == 0)
{
v___x_4926_ = v___x_4914_;
v_isShared_4927_ = v_isSharedCheck_4931_;
goto v_resetjp_4925_;
}
else
{
lean_inc(v_a_4924_);
lean_dec(v___x_4914_);
v___x_4926_ = lean_box(0);
v_isShared_4927_ = v_isSharedCheck_4931_;
goto v_resetjp_4925_;
}
v_resetjp_4925_:
{
lean_object* v___x_4929_; 
if (v_isShared_4927_ == 0)
{
v___x_4929_ = v___x_4926_;
goto v_reusejp_4928_;
}
else
{
lean_object* v_reuseFailAlloc_4930_; 
v_reuseFailAlloc_4930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4930_, 0, v_a_4924_);
v___x_4929_ = v_reuseFailAlloc_4930_;
goto v_reusejp_4928_;
}
v_reusejp_4928_:
{
return v___x_4929_;
}
}
}
}
else
{
lean_object* v___x_4932_; 
lean_dec(v___y_4912_);
lean_dec(v___y_4911_);
lean_dec(v___y_4910_);
lean_dec_ref(v___y_4909_);
v___x_4932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4932_, 0, v___y_4908_);
return v___x_4932_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__1___boxed(lean_object* v_a_5147_, lean_object* v___x_5148_, lean_object* v_fvarIdsToSimp_5149_, lean_object* v_sz_5150_, lean_object* v___x_5151_, lean_object* v___x_5152_, lean_object* v_simplifyTarget_5153_, lean_object* v___y_5154_, lean_object* v___y_5155_, lean_object* v___y_5156_, lean_object* v___y_5157_, lean_object* v___y_5158_, lean_object* v___y_5159_, lean_object* v___y_5160_){
_start:
{
size_t v_sz_boxed_5161_; size_t v___x_47442__boxed_5162_; uint8_t v_simplifyTarget_boxed_5163_; lean_object* v_res_5164_; 
v_sz_boxed_5161_ = lean_unbox_usize(v_sz_5150_);
lean_dec(v_sz_5150_);
v___x_47442__boxed_5162_ = lean_unbox_usize(v___x_5151_);
lean_dec(v___x_5151_);
v_simplifyTarget_boxed_5163_ = lean_unbox(v_simplifyTarget_5153_);
v_res_5164_ = l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__1(v_a_5147_, v___x_5148_, v_fvarIdsToSimp_5149_, v_sz_boxed_5161_, v___x_47442__boxed_5162_, v___x_5152_, v_simplifyTarget_boxed_5163_, v___y_5154_, v___y_5155_, v___y_5156_, v___y_5157_, v___y_5158_, v___y_5159_);
lean_dec_ref(v_fvarIdsToSimp_5149_);
return v_res_5164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__2(lean_object* v_mvarId_5172_, lean_object* v_fvarIdsToSimp_5173_, lean_object* v___x_5174_, uint8_t v_simplifyTarget_5175_, lean_object* v___y_5176_, lean_object* v___y_5177_, lean_object* v___y_5178_, lean_object* v___y_5179_, lean_object* v___y_5180_, lean_object* v___y_5181_){
_start:
{
lean_object* v___x_5183_; 
lean_inc(v___y_5181_);
lean_inc_ref(v___y_5180_);
lean_inc(v___y_5179_);
lean_inc_ref(v___y_5178_);
v___x_5183_ = l_Lean_Meta_Sym_preprocessMVar(v_mvarId_5172_, v___y_5176_, v___y_5177_, v___y_5178_, v___y_5179_, v___y_5180_, v___y_5181_);
if (lean_obj_tag(v___x_5183_) == 0)
{
lean_object* v_a_5184_; lean_object* v___x_5185_; size_t v_sz_5186_; lean_object* v___x_5187_; lean_object* v___x_5188_; lean_object* v___x_5189_; lean_object* v___f_5190_; lean_object* v___x_5191_; 
v_a_5184_ = lean_ctor_get(v___x_5183_, 0);
lean_inc(v_a_5184_);
lean_dec_ref(v___x_5183_);
v___x_5185_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__2___closed__1));
v_sz_5186_ = lean_array_size(v_fvarIdsToSimp_5173_);
v___x_5187_ = lean_box_usize(v_sz_5186_);
v___x_5188_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__2___boxed__const__1));
v___x_5189_ = lean_box(v_simplifyTarget_5175_);
lean_inc(v_a_5184_);
v___f_5190_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__1___boxed), 14, 7);
lean_closure_set(v___f_5190_, 0, v_a_5184_);
lean_closure_set(v___f_5190_, 1, v___x_5174_);
lean_closure_set(v___f_5190_, 2, v_fvarIdsToSimp_5173_);
lean_closure_set(v___f_5190_, 3, v___x_5187_);
lean_closure_set(v___f_5190_, 4, v___x_5188_);
lean_closure_set(v___f_5190_, 5, v___x_5185_);
lean_closure_set(v___f_5190_, 6, v___x_5189_);
v___x_5191_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__5___redArg(v_a_5184_, v___f_5190_, v___y_5176_, v___y_5177_, v___y_5178_, v___y_5179_, v___y_5180_, v___y_5181_);
return v___x_5191_;
}
else
{
lean_object* v_a_5192_; lean_object* v___x_5194_; uint8_t v_isShared_5195_; uint8_t v_isSharedCheck_5199_; 
lean_dec(v___y_5181_);
lean_dec_ref(v___y_5180_);
lean_dec(v___y_5179_);
lean_dec_ref(v___y_5178_);
lean_dec(v___y_5177_);
lean_dec_ref(v___y_5176_);
lean_dec_ref(v___x_5174_);
lean_dec_ref(v_fvarIdsToSimp_5173_);
v_a_5192_ = lean_ctor_get(v___x_5183_, 0);
v_isSharedCheck_5199_ = !lean_is_exclusive(v___x_5183_);
if (v_isSharedCheck_5199_ == 0)
{
v___x_5194_ = v___x_5183_;
v_isShared_5195_ = v_isSharedCheck_5199_;
goto v_resetjp_5193_;
}
else
{
lean_inc(v_a_5192_);
lean_dec(v___x_5183_);
v___x_5194_ = lean_box(0);
v_isShared_5195_ = v_isSharedCheck_5199_;
goto v_resetjp_5193_;
}
v_resetjp_5193_:
{
lean_object* v___x_5197_; 
if (v_isShared_5195_ == 0)
{
v___x_5197_ = v___x_5194_;
goto v_reusejp_5196_;
}
else
{
lean_object* v_reuseFailAlloc_5198_; 
v_reuseFailAlloc_5198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5198_, 0, v_a_5192_);
v___x_5197_ = v_reuseFailAlloc_5198_;
goto v_reusejp_5196_;
}
v_reusejp_5196_:
{
return v___x_5197_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__2___boxed(lean_object* v_mvarId_5200_, lean_object* v_fvarIdsToSimp_5201_, lean_object* v___x_5202_, lean_object* v_simplifyTarget_5203_, lean_object* v___y_5204_, lean_object* v___y_5205_, lean_object* v___y_5206_, lean_object* v___y_5207_, lean_object* v___y_5208_, lean_object* v___y_5209_, lean_object* v___y_5210_){
_start:
{
uint8_t v_simplifyTarget_boxed_5211_; lean_object* v_res_5212_; 
v_simplifyTarget_boxed_5211_ = lean_unbox(v_simplifyTarget_5203_);
v_res_5212_ = l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__2(v_mvarId_5200_, v_fvarIdsToSimp_5201_, v___x_5202_, v_simplifyTarget_boxed_5211_, v___y_5204_, v___y_5205_, v___y_5206_, v___y_5207_, v___y_5208_, v___y_5209_);
return v_res_5212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal(lean_object* v_mvarId_5213_, uint8_t v_simplifyTarget_5214_, lean_object* v_fvarIdsToSimp_5215_, lean_object* v_a_5216_, lean_object* v_a_5217_, lean_object* v_a_5218_, lean_object* v_a_5219_){
_start:
{
lean_object* v_options_5221_; lean_object* v___x_5222_; lean_object* v___x_5223_; lean_object* v___x_5224_; lean_object* v___x_5225_; lean_object* v___x_5226_; lean_object* v___f_5227_; lean_object* v___x_5228_; 
v_options_5221_ = lean_ctor_get(v_a_5218_, 2);
v___x_5222_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_5223_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__6(v_options_5221_, v___x_5222_);
v___x_5224_ = lean_unsigned_to_nat(2u);
v___x_5225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5225_, 0, v___x_5223_);
lean_ctor_set(v___x_5225_, 1, v___x_5224_);
v___x_5226_ = lean_box(v_simplifyTarget_5214_);
v___f_5227_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__2___boxed), 11, 4);
lean_closure_set(v___f_5227_, 0, v_mvarId_5213_);
lean_closure_set(v___f_5227_, 1, v_fvarIdsToSimp_5215_);
lean_closure_set(v___f_5227_, 2, v___x_5225_);
lean_closure_set(v___f_5227_, 3, v___x_5226_);
v___x_5228_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_5227_, v_a_5216_, v_a_5217_, v_a_5218_, v_a_5219_);
return v___x_5228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___boxed(lean_object* v_mvarId_5229_, lean_object* v_simplifyTarget_5230_, lean_object* v_fvarIdsToSimp_5231_, lean_object* v_a_5232_, lean_object* v_a_5233_, lean_object* v_a_5234_, lean_object* v_a_5235_, lean_object* v_a_5236_){
_start:
{
uint8_t v_simplifyTarget_boxed_5237_; lean_object* v_res_5238_; 
v_simplifyTarget_boxed_5237_ = lean_unbox(v_simplifyTarget_5230_);
v_res_5238_ = l_Lean_Meta_Tactic_Cbv_cbvGoal(v_mvarId_5229_, v_simplifyTarget_boxed_5237_, v_fvarIdsToSimp_5231_, v_a_5232_, v_a_5233_, v_a_5234_, v_a_5235_);
return v_res_5238_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0(lean_object* v_mvarId_5239_, lean_object* v_val_5240_, lean_object* v___y_5241_, lean_object* v___y_5242_, lean_object* v___y_5243_, lean_object* v___y_5244_, lean_object* v___y_5245_, lean_object* v___y_5246_){
_start:
{
lean_object* v___x_5248_; 
v___x_5248_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0___redArg(v_mvarId_5239_, v_val_5240_, v___y_5244_);
return v___x_5248_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0___boxed(lean_object* v_mvarId_5249_, lean_object* v_val_5250_, lean_object* v___y_5251_, lean_object* v___y_5252_, lean_object* v___y_5253_, lean_object* v___y_5254_, lean_object* v___y_5255_, lean_object* v___y_5256_, lean_object* v___y_5257_){
_start:
{
lean_object* v_res_5258_; 
v_res_5258_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0(v_mvarId_5249_, v_val_5250_, v___y_5251_, v___y_5252_, v___y_5253_, v___y_5254_, v___y_5255_, v___y_5256_);
lean_dec(v___y_5256_);
lean_dec_ref(v___y_5255_);
lean_dec(v___y_5254_);
lean_dec_ref(v___y_5253_);
lean_dec(v___y_5252_);
lean_dec_ref(v___y_5251_);
return v_res_5258_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3_spec__5(lean_object* v_00_u03b1_5259_, lean_object* v_x_5260_, lean_object* v___y_5261_, lean_object* v___y_5262_, lean_object* v___y_5263_, lean_object* v___y_5264_, lean_object* v___y_5265_, lean_object* v___y_5266_){
_start:
{
lean_object* v___x_5268_; 
v___x_5268_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3_spec__5___redArg(v_x_5260_);
return v___x_5268_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3_spec__5___boxed(lean_object* v_00_u03b1_5269_, lean_object* v_x_5270_, lean_object* v___y_5271_, lean_object* v___y_5272_, lean_object* v___y_5273_, lean_object* v___y_5274_, lean_object* v___y_5275_, lean_object* v___y_5276_, lean_object* v___y_5277_){
_start:
{
lean_object* v_res_5278_; 
v_res_5278_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3_spec__5(v_00_u03b1_5269_, v_x_5270_, v___y_5271_, v___y_5272_, v___y_5273_, v___y_5274_, v___y_5275_, v___y_5276_);
lean_dec(v___y_5276_);
lean_dec_ref(v___y_5275_);
lean_dec(v___y_5274_);
lean_dec_ref(v___y_5273_);
lean_dec(v___y_5272_);
lean_dec_ref(v___y_5271_);
return v_res_5278_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0(lean_object* v_00_u03b2_5279_, lean_object* v_x_5280_, lean_object* v_x_5281_, lean_object* v_x_5282_){
_start:
{
lean_object* v___x_5283_; 
v___x_5283_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0___redArg(v_x_5280_, v_x_5281_, v_x_5282_);
return v___x_5283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3_spec__4(lean_object* v_oldTraces_5284_, lean_object* v_data_5285_, lean_object* v_ref_5286_, lean_object* v_msg_5287_, lean_object* v___y_5288_, lean_object* v___y_5289_, lean_object* v___y_5290_, lean_object* v___y_5291_, lean_object* v___y_5292_, lean_object* v___y_5293_){
_start:
{
lean_object* v___x_5295_; 
v___x_5295_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3_spec__4___redArg(v_oldTraces_5284_, v_data_5285_, v_ref_5286_, v_msg_5287_, v___y_5290_, v___y_5291_, v___y_5292_, v___y_5293_);
return v___x_5295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3_spec__4___boxed(lean_object* v_oldTraces_5296_, lean_object* v_data_5297_, lean_object* v_ref_5298_, lean_object* v_msg_5299_, lean_object* v___y_5300_, lean_object* v___y_5301_, lean_object* v___y_5302_, lean_object* v___y_5303_, lean_object* v___y_5304_, lean_object* v___y_5305_, lean_object* v___y_5306_){
_start:
{
lean_object* v_res_5307_; 
v_res_5307_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3_spec__4(v_oldTraces_5296_, v_data_5297_, v_ref_5298_, v_msg_5299_, v___y_5300_, v___y_5301_, v___y_5302_, v___y_5303_, v___y_5304_, v___y_5305_);
lean_dec(v___y_5305_);
lean_dec(v___y_5303_);
lean_dec_ref(v___y_5302_);
lean_dec(v___y_5301_);
lean_dec_ref(v___y_5300_);
return v_res_5307_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4(lean_object* v_00_u03b2_5308_, lean_object* v_x_5309_, size_t v_x_5310_, size_t v_x_5311_, lean_object* v_x_5312_, lean_object* v_x_5313_){
_start:
{
lean_object* v___x_5314_; 
v___x_5314_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4___redArg(v_x_5309_, v_x_5310_, v_x_5311_, v_x_5312_, v_x_5313_);
return v___x_5314_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b2_5315_, lean_object* v_x_5316_, lean_object* v_x_5317_, lean_object* v_x_5318_, lean_object* v_x_5319_, lean_object* v_x_5320_){
_start:
{
size_t v_x_48142__boxed_5321_; size_t v_x_48143__boxed_5322_; lean_object* v_res_5323_; 
v_x_48142__boxed_5321_ = lean_unbox_usize(v_x_5317_);
lean_dec(v_x_5317_);
v_x_48143__boxed_5322_ = lean_unbox_usize(v_x_5318_);
lean_dec(v_x_5318_);
v_res_5323_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4(v_00_u03b2_5315_, v_x_5316_, v_x_48142__boxed_5321_, v_x_48143__boxed_5322_, v_x_5319_, v_x_5320_);
return v_res_5323_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4_spec__8(lean_object* v_00_u03b2_5324_, lean_object* v_n_5325_, lean_object* v_k_5326_, lean_object* v_v_5327_){
_start:
{
lean_object* v___x_5328_; 
v___x_5328_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4_spec__8___redArg(v_n_5325_, v_k_5326_, v_v_5327_);
return v___x_5328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4_spec__9(lean_object* v_00_u03b2_5329_, size_t v_depth_5330_, lean_object* v_keys_5331_, lean_object* v_vals_5332_, lean_object* v_heq_5333_, lean_object* v_i_5334_, lean_object* v_entries_5335_){
_start:
{
lean_object* v___x_5336_; 
v___x_5336_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4_spec__9___redArg(v_depth_5330_, v_keys_5331_, v_vals_5332_, v_i_5334_, v_entries_5335_);
return v___x_5336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4_spec__9___boxed(lean_object* v_00_u03b2_5337_, lean_object* v_depth_5338_, lean_object* v_keys_5339_, lean_object* v_vals_5340_, lean_object* v_heq_5341_, lean_object* v_i_5342_, lean_object* v_entries_5343_){
_start:
{
size_t v_depth_boxed_5344_; lean_object* v_res_5345_; 
v_depth_boxed_5344_ = lean_unbox_usize(v_depth_5338_);
lean_dec(v_depth_5338_);
v_res_5345_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4_spec__9(v_00_u03b2_5337_, v_depth_boxed_5344_, v_keys_5339_, v_vals_5340_, v_heq_5341_, v_i_5342_, v_entries_5343_);
lean_dec_ref(v_vals_5340_);
lean_dec_ref(v_keys_5339_);
return v_res_5345_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4_spec__8_spec__10(lean_object* v_00_u03b2_5346_, lean_object* v_x_5347_, lean_object* v_x_5348_, lean_object* v_x_5349_, lean_object* v_x_5350_){
_start:
{
lean_object* v___x_5351_; 
v___x_5351_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4_spec__8_spec__10___redArg(v_x_5347_, v_x_5348_, v_x_5349_, v_x_5350_);
return v___x_5351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0(lean_object* v_a_5352_, uint8_t v___x_5353_, lean_object* v___y_5354_, lean_object* v___y_5355_, lean_object* v___y_5356_, lean_object* v___y_5357_, lean_object* v___y_5358_, lean_object* v___y_5359_){
_start:
{
lean_object* v___x_5361_; 
v___x_5361_ = l_Lean_MVarId_refl(v_a_5352_, v___x_5353_, v___y_5356_, v___y_5357_, v___y_5358_, v___y_5359_);
return v___x_5361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0___boxed(lean_object* v_a_5362_, lean_object* v___x_5363_, lean_object* v___y_5364_, lean_object* v___y_5365_, lean_object* v___y_5366_, lean_object* v___y_5367_, lean_object* v___y_5368_, lean_object* v___y_5369_, lean_object* v___y_5370_){
_start:
{
uint8_t v___x_21137__boxed_5371_; lean_object* v_res_5372_; 
v___x_21137__boxed_5371_ = lean_unbox(v___x_5363_);
v_res_5372_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0(v_a_5362_, v___x_21137__boxed_5371_, v___y_5364_, v___y_5365_, v___y_5366_, v___y_5367_, v___y_5368_, v___y_5369_);
lean_dec(v___y_5365_);
lean_dec_ref(v___y_5364_);
return v_res_5372_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(lean_object* v_cls_5373_, lean_object* v_msg_5374_, lean_object* v___y_5375_, lean_object* v___y_5376_, lean_object* v___y_5377_, lean_object* v___y_5378_){
_start:
{
lean_object* v_ref_5380_; lean_object* v___x_5381_; lean_object* v_a_5382_; lean_object* v___x_5384_; uint8_t v_isShared_5385_; uint8_t v_isSharedCheck_5426_; 
v_ref_5380_ = lean_ctor_get(v___y_5377_, 5);
v___x_5381_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1_spec__1(v_msg_5374_, v___y_5375_, v___y_5376_, v___y_5377_, v___y_5378_);
v_a_5382_ = lean_ctor_get(v___x_5381_, 0);
v_isSharedCheck_5426_ = !lean_is_exclusive(v___x_5381_);
if (v_isSharedCheck_5426_ == 0)
{
v___x_5384_ = v___x_5381_;
v_isShared_5385_ = v_isSharedCheck_5426_;
goto v_resetjp_5383_;
}
else
{
lean_inc(v_a_5382_);
lean_dec(v___x_5381_);
v___x_5384_ = lean_box(0);
v_isShared_5385_ = v_isSharedCheck_5426_;
goto v_resetjp_5383_;
}
v_resetjp_5383_:
{
lean_object* v___x_5386_; lean_object* v_traceState_5387_; lean_object* v_env_5388_; lean_object* v_nextMacroScope_5389_; lean_object* v_ngen_5390_; lean_object* v_auxDeclNGen_5391_; lean_object* v_cache_5392_; lean_object* v_messages_5393_; lean_object* v_infoState_5394_; lean_object* v_snapshotTasks_5395_; lean_object* v___x_5397_; uint8_t v_isShared_5398_; uint8_t v_isSharedCheck_5425_; 
v___x_5386_ = lean_st_ref_take(v___y_5378_);
v_traceState_5387_ = lean_ctor_get(v___x_5386_, 4);
v_env_5388_ = lean_ctor_get(v___x_5386_, 0);
v_nextMacroScope_5389_ = lean_ctor_get(v___x_5386_, 1);
v_ngen_5390_ = lean_ctor_get(v___x_5386_, 2);
v_auxDeclNGen_5391_ = lean_ctor_get(v___x_5386_, 3);
v_cache_5392_ = lean_ctor_get(v___x_5386_, 5);
v_messages_5393_ = lean_ctor_get(v___x_5386_, 6);
v_infoState_5394_ = lean_ctor_get(v___x_5386_, 7);
v_snapshotTasks_5395_ = lean_ctor_get(v___x_5386_, 8);
v_isSharedCheck_5425_ = !lean_is_exclusive(v___x_5386_);
if (v_isSharedCheck_5425_ == 0)
{
v___x_5397_ = v___x_5386_;
v_isShared_5398_ = v_isSharedCheck_5425_;
goto v_resetjp_5396_;
}
else
{
lean_inc(v_snapshotTasks_5395_);
lean_inc(v_infoState_5394_);
lean_inc(v_messages_5393_);
lean_inc(v_cache_5392_);
lean_inc(v_traceState_5387_);
lean_inc(v_auxDeclNGen_5391_);
lean_inc(v_ngen_5390_);
lean_inc(v_nextMacroScope_5389_);
lean_inc(v_env_5388_);
lean_dec(v___x_5386_);
v___x_5397_ = lean_box(0);
v_isShared_5398_ = v_isSharedCheck_5425_;
goto v_resetjp_5396_;
}
v_resetjp_5396_:
{
uint64_t v_tid_5399_; lean_object* v_traces_5400_; lean_object* v___x_5402_; uint8_t v_isShared_5403_; uint8_t v_isSharedCheck_5424_; 
v_tid_5399_ = lean_ctor_get_uint64(v_traceState_5387_, sizeof(void*)*1);
v_traces_5400_ = lean_ctor_get(v_traceState_5387_, 0);
v_isSharedCheck_5424_ = !lean_is_exclusive(v_traceState_5387_);
if (v_isSharedCheck_5424_ == 0)
{
v___x_5402_ = v_traceState_5387_;
v_isShared_5403_ = v_isSharedCheck_5424_;
goto v_resetjp_5401_;
}
else
{
lean_inc(v_traces_5400_);
lean_dec(v_traceState_5387_);
v___x_5402_ = lean_box(0);
v_isShared_5403_ = v_isSharedCheck_5424_;
goto v_resetjp_5401_;
}
v_resetjp_5401_:
{
lean_object* v___x_5404_; double v___x_5405_; uint8_t v___x_5406_; lean_object* v___x_5407_; lean_object* v___x_5408_; lean_object* v___x_5409_; lean_object* v___x_5410_; lean_object* v___x_5411_; lean_object* v___x_5412_; lean_object* v___x_5414_; 
v___x_5404_ = lean_box(0);
v___x_5405_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__0);
v___x_5406_ = 0;
v___x_5407_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__1));
v___x_5408_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_5408_, 0, v_cls_5373_);
lean_ctor_set(v___x_5408_, 1, v___x_5404_);
lean_ctor_set(v___x_5408_, 2, v___x_5407_);
lean_ctor_set_float(v___x_5408_, sizeof(void*)*3, v___x_5405_);
lean_ctor_set_float(v___x_5408_, sizeof(void*)*3 + 8, v___x_5405_);
lean_ctor_set_uint8(v___x_5408_, sizeof(void*)*3 + 16, v___x_5406_);
v___x_5409_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__2));
v___x_5410_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_5410_, 0, v___x_5408_);
lean_ctor_set(v___x_5410_, 1, v_a_5382_);
lean_ctor_set(v___x_5410_, 2, v___x_5409_);
lean_inc(v_ref_5380_);
v___x_5411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5411_, 0, v_ref_5380_);
lean_ctor_set(v___x_5411_, 1, v___x_5410_);
v___x_5412_ = l_Lean_PersistentArray_push___redArg(v_traces_5400_, v___x_5411_);
if (v_isShared_5403_ == 0)
{
lean_ctor_set(v___x_5402_, 0, v___x_5412_);
v___x_5414_ = v___x_5402_;
goto v_reusejp_5413_;
}
else
{
lean_object* v_reuseFailAlloc_5423_; 
v_reuseFailAlloc_5423_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5423_, 0, v___x_5412_);
lean_ctor_set_uint64(v_reuseFailAlloc_5423_, sizeof(void*)*1, v_tid_5399_);
v___x_5414_ = v_reuseFailAlloc_5423_;
goto v_reusejp_5413_;
}
v_reusejp_5413_:
{
lean_object* v___x_5416_; 
if (v_isShared_5398_ == 0)
{
lean_ctor_set(v___x_5397_, 4, v___x_5414_);
v___x_5416_ = v___x_5397_;
goto v_reusejp_5415_;
}
else
{
lean_object* v_reuseFailAlloc_5422_; 
v_reuseFailAlloc_5422_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5422_, 0, v_env_5388_);
lean_ctor_set(v_reuseFailAlloc_5422_, 1, v_nextMacroScope_5389_);
lean_ctor_set(v_reuseFailAlloc_5422_, 2, v_ngen_5390_);
lean_ctor_set(v_reuseFailAlloc_5422_, 3, v_auxDeclNGen_5391_);
lean_ctor_set(v_reuseFailAlloc_5422_, 4, v___x_5414_);
lean_ctor_set(v_reuseFailAlloc_5422_, 5, v_cache_5392_);
lean_ctor_set(v_reuseFailAlloc_5422_, 6, v_messages_5393_);
lean_ctor_set(v_reuseFailAlloc_5422_, 7, v_infoState_5394_);
lean_ctor_set(v_reuseFailAlloc_5422_, 8, v_snapshotTasks_5395_);
v___x_5416_ = v_reuseFailAlloc_5422_;
goto v_reusejp_5415_;
}
v_reusejp_5415_:
{
lean_object* v___x_5417_; lean_object* v___x_5418_; lean_object* v___x_5420_; 
v___x_5417_ = lean_st_ref_set(v___y_5378_, v___x_5416_);
v___x_5418_ = lean_box(0);
if (v_isShared_5385_ == 0)
{
lean_ctor_set(v___x_5384_, 0, v___x_5418_);
v___x_5420_ = v___x_5384_;
goto v_reusejp_5419_;
}
else
{
lean_object* v_reuseFailAlloc_5421_; 
v_reuseFailAlloc_5421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5421_, 0, v___x_5418_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg___boxed(lean_object* v_cls_5427_, lean_object* v_msg_5428_, lean_object* v___y_5429_, lean_object* v___y_5430_, lean_object* v___y_5431_, lean_object* v___y_5432_, lean_object* v___y_5433_){
_start:
{
lean_object* v_res_5434_; 
v_res_5434_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(v_cls_5427_, v_msg_5428_, v___y_5429_, v___y_5430_, v___y_5431_, v___y_5432_);
lean_dec(v___y_5432_);
lean_dec_ref(v___y_5431_);
lean_dec(v___y_5430_);
lean_dec_ref(v___y_5429_);
return v_res_5434_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(lean_object* v_msg_5435_, lean_object* v___y_5436_, lean_object* v___y_5437_, lean_object* v___y_5438_, lean_object* v___y_5439_){
_start:
{
lean_object* v_ref_5441_; lean_object* v___x_5442_; lean_object* v_a_5443_; lean_object* v___x_5445_; uint8_t v_isShared_5446_; uint8_t v_isSharedCheck_5451_; 
v_ref_5441_ = lean_ctor_get(v___y_5438_, 5);
v___x_5442_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1_spec__1(v_msg_5435_, v___y_5436_, v___y_5437_, v___y_5438_, v___y_5439_);
v_a_5443_ = lean_ctor_get(v___x_5442_, 0);
v_isSharedCheck_5451_ = !lean_is_exclusive(v___x_5442_);
if (v_isSharedCheck_5451_ == 0)
{
v___x_5445_ = v___x_5442_;
v_isShared_5446_ = v_isSharedCheck_5451_;
goto v_resetjp_5444_;
}
else
{
lean_inc(v_a_5443_);
lean_dec(v___x_5442_);
v___x_5445_ = lean_box(0);
v_isShared_5446_ = v_isSharedCheck_5451_;
goto v_resetjp_5444_;
}
v_resetjp_5444_:
{
lean_object* v___x_5447_; lean_object* v___x_5449_; 
lean_inc(v_ref_5441_);
v___x_5447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5447_, 0, v_ref_5441_);
lean_ctor_set(v___x_5447_, 1, v_a_5443_);
if (v_isShared_5446_ == 0)
{
lean_ctor_set_tag(v___x_5445_, 1);
lean_ctor_set(v___x_5445_, 0, v___x_5447_);
v___x_5449_ = v___x_5445_;
goto v_reusejp_5448_;
}
else
{
lean_object* v_reuseFailAlloc_5450_; 
v_reuseFailAlloc_5450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5450_, 0, v___x_5447_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg___boxed(lean_object* v_msg_5452_, lean_object* v___y_5453_, lean_object* v___y_5454_, lean_object* v___y_5455_, lean_object* v___y_5456_, lean_object* v___y_5457_){
_start:
{
lean_object* v_res_5458_; 
v_res_5458_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v_msg_5452_, v___y_5453_, v___y_5454_, v___y_5455_, v___y_5456_);
lean_dec(v___y_5456_);
lean_dec_ref(v___y_5455_);
lean_dec(v___y_5454_);
lean_dec_ref(v___y_5453_);
return v_res_5458_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1(void){
_start:
{
lean_object* v___x_5460_; lean_object* v___x_5461_; 
v___x_5460_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__0));
v___x_5461_ = l_Lean_stringToMessageData(v___x_5460_);
return v___x_5461_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3(void){
_start:
{
lean_object* v___x_5463_; lean_object* v___x_5464_; 
v___x_5463_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__2));
v___x_5464_ = l_Lean_stringToMessageData(v___x_5463_);
return v___x_5464_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6(void){
_start:
{
lean_object* v___x_5468_; lean_object* v___x_5469_; 
v___x_5468_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__5));
v___x_5469_ = l_Lean_stringToMessageData(v___x_5468_);
return v___x_5469_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8(void){
_start:
{
lean_object* v___x_5471_; lean_object* v___x_5472_; 
v___x_5471_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__7));
v___x_5472_ = l_Lean_stringToMessageData(v___x_5471_);
return v___x_5472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1(lean_object* v_m_5473_, lean_object* v___x_5474_, lean_object* v_cls_5475_, lean_object* v___y_5476_, lean_object* v___y_5477_, lean_object* v___y_5478_, lean_object* v___y_5479_, lean_object* v___y_5480_, lean_object* v___y_5481_){
_start:
{
lean_object* v_e_5484_; lean_object* v_onTrue_5485_; lean_object* v___y_5486_; lean_object* v___y_5487_; lean_object* v___y_5488_; lean_object* v___y_5489_; lean_object* v___y_5490_; lean_object* v___y_5491_; lean_object* v___x_5521_; 
lean_inc(v___y_5481_);
lean_inc_ref(v___y_5480_);
lean_inc(v___y_5479_);
lean_inc_ref(v___y_5478_);
v___x_5521_ = l_Lean_Meta_Sym_preprocessMVar(v_m_5473_, v___y_5476_, v___y_5477_, v___y_5478_, v___y_5479_, v___y_5480_, v___y_5481_);
if (lean_obj_tag(v___x_5521_) == 0)
{
lean_object* v_a_5522_; lean_object* v___x_5523_; 
v_a_5522_ = lean_ctor_get(v___x_5521_, 0);
lean_inc(v_a_5522_);
lean_dec_ref(v___x_5521_);
lean_inc(v_a_5522_);
v___x_5523_ = l_Lean_MVarId_getType(v_a_5522_, v___y_5478_, v___y_5479_, v___y_5480_, v___y_5481_);
if (lean_obj_tag(v___x_5523_) == 0)
{
lean_object* v_a_5524_; lean_object* v___x_5525_; lean_object* v___x_5526_; uint8_t v___x_5527_; 
v_a_5524_ = lean_ctor_get(v___x_5523_, 0);
lean_inc(v_a_5524_);
lean_dec_ref(v___x_5523_);
v___x_5525_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__4));
v___x_5526_ = lean_unsigned_to_nat(3u);
v___x_5527_ = l_Lean_Expr_isAppOfArity(v_a_5524_, v___x_5525_, v___x_5526_);
if (v___x_5527_ == 0)
{
lean_object* v___x_5528_; lean_object* v___x_5529_; lean_object* v___x_5530_; lean_object* v___x_5531_; 
lean_dec(v_a_5522_);
lean_dec(v___y_5477_);
lean_dec_ref(v___y_5476_);
lean_dec(v_cls_5475_);
lean_dec_ref(v___x_5474_);
v___x_5528_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6);
v___x_5529_ = l_Lean_indentExpr(v_a_5524_);
v___x_5530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5530_, 0, v___x_5528_);
lean_ctor_set(v___x_5530_, 1, v___x_5529_);
v___x_5531_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_5530_, v___y_5478_, v___y_5479_, v___y_5480_, v___y_5481_);
lean_dec(v___y_5481_);
lean_dec_ref(v___y_5480_);
lean_dec(v___y_5479_);
lean_dec_ref(v___y_5478_);
return v___x_5531_;
}
else
{
lean_object* v___x_5532_; lean_object* v___x_5533_; lean_object* v___x_5534_; 
v___x_5532_ = l_Lean_Expr_appFn_x21(v_a_5524_);
lean_dec(v_a_5524_);
v___x_5533_ = l_Lean_Expr_appArg_x21(v___x_5532_);
lean_dec_ref(v___x_5532_);
lean_inc(v___y_5481_);
lean_inc_ref(v___y_5480_);
lean_inc(v___y_5479_);
lean_inc_ref(v___y_5478_);
lean_inc(v___y_5477_);
lean_inc_ref(v___y_5476_);
lean_inc_ref(v___x_5533_);
v___x_5534_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_5533_, v___x_5474_, v___y_5476_, v___y_5477_, v___y_5478_, v___y_5479_, v___y_5480_, v___y_5481_);
if (lean_obj_tag(v___x_5534_) == 0)
{
lean_object* v_a_5535_; lean_object* v___x_5536_; lean_object* v_a_5537_; lean_object* v___x_5538_; lean_object* v___f_5539_; lean_object* v___y_5541_; lean_object* v___y_5542_; lean_object* v___y_5543_; lean_object* v___y_5544_; lean_object* v___y_5545_; lean_object* v___y_5546_; uint8_t v___x_5550_; 
v_a_5535_ = lean_ctor_get(v___x_5534_, 0);
lean_inc(v_a_5535_);
lean_dec_ref(v___x_5534_);
lean_inc(v_cls_5475_);
v___x_5536_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__1___redArg(v_cls_5475_, v___y_5480_);
v_a_5537_ = lean_ctor_get(v___x_5536_, 0);
lean_inc(v_a_5537_);
lean_dec_ref(v___x_5536_);
v___x_5538_ = lean_box(v___x_5527_);
lean_inc(v_a_5522_);
v___f_5539_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5539_, 0, v_a_5522_);
lean_closure_set(v___f_5539_, 1, v___x_5538_);
v___x_5550_ = lean_unbox(v_a_5537_);
lean_dec(v_a_5537_);
if (v___x_5550_ == 0)
{
lean_dec(v_cls_5475_);
v___y_5541_ = v___y_5476_;
v___y_5542_ = v___y_5477_;
v___y_5543_ = v___y_5478_;
v___y_5544_ = v___y_5479_;
v___y_5545_ = v___y_5480_;
v___y_5546_ = v___y_5481_;
goto v___jp_5540_;
}
else
{
lean_object* v___x_5551_; lean_object* v___x_5552_; lean_object* v___x_5553_; lean_object* v___x_5554_; lean_object* v___x_5555_; lean_object* v___x_5556_; lean_object* v___x_5557_; lean_object* v___x_5558_; lean_object* v___x_5559_; 
v___x_5551_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8);
lean_inc_ref(v___x_5533_);
v___x_5552_ = l_Lean_indentExpr(v___x_5533_);
v___x_5553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5553_, 0, v___x_5551_);
lean_ctor_set(v___x_5553_, 1, v___x_5552_);
v___x_5554_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7);
v___x_5555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5555_, 0, v___x_5553_);
lean_ctor_set(v___x_5555_, 1, v___x_5554_);
v___x_5556_ = l_Lean_Meta_Sym_Simp_Result_getResultExpr(v___x_5533_, v_a_5535_);
v___x_5557_ = l_Lean_indentExpr(v___x_5556_);
v___x_5558_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5558_, 0, v___x_5555_);
lean_ctor_set(v___x_5558_, 1, v___x_5557_);
v___x_5559_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(v_cls_5475_, v___x_5558_, v___y_5478_, v___y_5479_, v___y_5480_, v___y_5481_);
if (lean_obj_tag(v___x_5559_) == 0)
{
lean_dec_ref(v___x_5559_);
v___y_5541_ = v___y_5476_;
v___y_5542_ = v___y_5477_;
v___y_5543_ = v___y_5478_;
v___y_5544_ = v___y_5479_;
v___y_5545_ = v___y_5480_;
v___y_5546_ = v___y_5481_;
goto v___jp_5540_;
}
else
{
lean_dec_ref(v___f_5539_);
lean_dec(v_a_5535_);
lean_dec_ref(v___x_5533_);
lean_dec(v_a_5522_);
lean_dec(v___y_5481_);
lean_dec_ref(v___y_5480_);
lean_dec(v___y_5479_);
lean_dec_ref(v___y_5478_);
lean_dec(v___y_5477_);
lean_dec_ref(v___y_5476_);
return v___x_5559_;
}
}
v___jp_5540_:
{
if (lean_obj_tag(v_a_5535_) == 0)
{
lean_dec_ref(v_a_5535_);
lean_dec(v_a_5522_);
v_e_5484_ = v___x_5533_;
v_onTrue_5485_ = v___f_5539_;
v___y_5486_ = v___y_5541_;
v___y_5487_ = v___y_5542_;
v___y_5488_ = v___y_5543_;
v___y_5489_ = v___y_5544_;
v___y_5490_ = v___y_5545_;
v___y_5491_ = v___y_5546_;
goto v___jp_5483_;
}
else
{
lean_object* v_e_x27_5547_; lean_object* v_proof_5548_; lean_object* v___x_5549_; 
lean_dec_ref(v___f_5539_);
lean_dec_ref(v___x_5533_);
v_e_x27_5547_ = lean_ctor_get(v_a_5535_, 0);
lean_inc_ref(v_e_x27_5547_);
v_proof_5548_ = lean_ctor_get(v_a_5535_, 1);
lean_inc_ref(v_proof_5548_);
lean_dec_ref(v_a_5535_);
v___x_5549_ = lean_alloc_closure((void*)(l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0___boxed), 9, 2);
lean_closure_set(v___x_5549_, 0, v_a_5522_);
lean_closure_set(v___x_5549_, 1, v_proof_5548_);
v_e_5484_ = v_e_x27_5547_;
v_onTrue_5485_ = v___x_5549_;
v___y_5486_ = v___y_5541_;
v___y_5487_ = v___y_5542_;
v___y_5488_ = v___y_5543_;
v___y_5489_ = v___y_5544_;
v___y_5490_ = v___y_5545_;
v___y_5491_ = v___y_5546_;
goto v___jp_5483_;
}
}
}
else
{
lean_object* v_a_5560_; lean_object* v___x_5562_; uint8_t v_isShared_5563_; uint8_t v_isSharedCheck_5567_; 
lean_dec_ref(v___x_5533_);
lean_dec(v_a_5522_);
lean_dec(v___y_5481_);
lean_dec_ref(v___y_5480_);
lean_dec(v___y_5479_);
lean_dec_ref(v___y_5478_);
lean_dec(v___y_5477_);
lean_dec_ref(v___y_5476_);
lean_dec(v_cls_5475_);
v_a_5560_ = lean_ctor_get(v___x_5534_, 0);
v_isSharedCheck_5567_ = !lean_is_exclusive(v___x_5534_);
if (v_isSharedCheck_5567_ == 0)
{
v___x_5562_ = v___x_5534_;
v_isShared_5563_ = v_isSharedCheck_5567_;
goto v_resetjp_5561_;
}
else
{
lean_inc(v_a_5560_);
lean_dec(v___x_5534_);
v___x_5562_ = lean_box(0);
v_isShared_5563_ = v_isSharedCheck_5567_;
goto v_resetjp_5561_;
}
v_resetjp_5561_:
{
lean_object* v___x_5565_; 
if (v_isShared_5563_ == 0)
{
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
return v___x_5565_;
}
}
}
}
}
else
{
lean_object* v_a_5568_; lean_object* v___x_5570_; uint8_t v_isShared_5571_; uint8_t v_isSharedCheck_5575_; 
lean_dec(v_a_5522_);
lean_dec(v___y_5481_);
lean_dec_ref(v___y_5480_);
lean_dec(v___y_5479_);
lean_dec_ref(v___y_5478_);
lean_dec(v___y_5477_);
lean_dec_ref(v___y_5476_);
lean_dec(v_cls_5475_);
lean_dec_ref(v___x_5474_);
v_a_5568_ = lean_ctor_get(v___x_5523_, 0);
v_isSharedCheck_5575_ = !lean_is_exclusive(v___x_5523_);
if (v_isSharedCheck_5575_ == 0)
{
v___x_5570_ = v___x_5523_;
v_isShared_5571_ = v_isSharedCheck_5575_;
goto v_resetjp_5569_;
}
else
{
lean_inc(v_a_5568_);
lean_dec(v___x_5523_);
v___x_5570_ = lean_box(0);
v_isShared_5571_ = v_isSharedCheck_5575_;
goto v_resetjp_5569_;
}
v_resetjp_5569_:
{
lean_object* v___x_5573_; 
if (v_isShared_5571_ == 0)
{
v___x_5573_ = v___x_5570_;
goto v_reusejp_5572_;
}
else
{
lean_object* v_reuseFailAlloc_5574_; 
v_reuseFailAlloc_5574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5574_, 0, v_a_5568_);
v___x_5573_ = v_reuseFailAlloc_5574_;
goto v_reusejp_5572_;
}
v_reusejp_5572_:
{
return v___x_5573_;
}
}
}
}
else
{
lean_object* v_a_5576_; lean_object* v___x_5578_; uint8_t v_isShared_5579_; uint8_t v_isSharedCheck_5583_; 
lean_dec(v___y_5481_);
lean_dec_ref(v___y_5480_);
lean_dec(v___y_5479_);
lean_dec_ref(v___y_5478_);
lean_dec(v___y_5477_);
lean_dec_ref(v___y_5476_);
lean_dec(v_cls_5475_);
lean_dec_ref(v___x_5474_);
v_a_5576_ = lean_ctor_get(v___x_5521_, 0);
v_isSharedCheck_5583_ = !lean_is_exclusive(v___x_5521_);
if (v_isSharedCheck_5583_ == 0)
{
v___x_5578_ = v___x_5521_;
v_isShared_5579_ = v_isSharedCheck_5583_;
goto v_resetjp_5577_;
}
else
{
lean_inc(v_a_5576_);
lean_dec(v___x_5521_);
v___x_5578_ = lean_box(0);
v_isShared_5579_ = v_isSharedCheck_5583_;
goto v_resetjp_5577_;
}
v_resetjp_5577_:
{
lean_object* v___x_5581_; 
if (v_isShared_5579_ == 0)
{
v___x_5581_ = v___x_5578_;
goto v_reusejp_5580_;
}
else
{
lean_object* v_reuseFailAlloc_5582_; 
v_reuseFailAlloc_5582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5582_, 0, v_a_5576_);
v___x_5581_ = v_reuseFailAlloc_5582_;
goto v_reusejp_5580_;
}
v_reusejp_5580_:
{
return v___x_5581_;
}
}
}
v___jp_5483_:
{
lean_object* v___x_5492_; 
v___x_5492_ = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(v_e_5484_, v___y_5486_);
if (lean_obj_tag(v___x_5492_) == 0)
{
lean_object* v_a_5493_; uint8_t v___x_5494_; 
v_a_5493_ = lean_ctor_get(v___x_5492_, 0);
lean_inc(v_a_5493_);
lean_dec_ref(v___x_5492_);
v___x_5494_ = lean_unbox(v_a_5493_);
lean_dec(v_a_5493_);
if (v___x_5494_ == 0)
{
lean_object* v___x_5495_; 
lean_dec(v___y_5487_);
lean_dec_ref(v_onTrue_5485_);
v___x_5495_ = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(v_e_5484_, v___y_5486_);
lean_dec_ref(v___y_5486_);
if (lean_obj_tag(v___x_5495_) == 0)
{
lean_object* v_a_5496_; uint8_t v___x_5497_; 
v_a_5496_ = lean_ctor_get(v___x_5495_, 0);
lean_inc(v_a_5496_);
lean_dec_ref(v___x_5495_);
v___x_5497_ = lean_unbox(v_a_5496_);
lean_dec(v_a_5496_);
if (v___x_5497_ == 0)
{
lean_object* v___x_5498_; lean_object* v___x_5499_; lean_object* v___x_5500_; lean_object* v___x_5501_; 
v___x_5498_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1);
v___x_5499_ = l_Lean_indentExpr(v_e_5484_);
v___x_5500_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5500_, 0, v___x_5498_);
lean_ctor_set(v___x_5500_, 1, v___x_5499_);
v___x_5501_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_5500_, v___y_5488_, v___y_5489_, v___y_5490_, v___y_5491_);
lean_dec(v___y_5491_);
lean_dec_ref(v___y_5490_);
lean_dec(v___y_5489_);
lean_dec_ref(v___y_5488_);
return v___x_5501_;
}
else
{
lean_object* v___x_5502_; lean_object* v___x_5503_; 
lean_dec_ref(v_e_5484_);
v___x_5502_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3);
v___x_5503_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_5502_, v___y_5488_, v___y_5489_, v___y_5490_, v___y_5491_);
lean_dec(v___y_5491_);
lean_dec_ref(v___y_5490_);
lean_dec(v___y_5489_);
lean_dec_ref(v___y_5488_);
return v___x_5503_;
}
}
else
{
lean_object* v_a_5504_; lean_object* v___x_5506_; uint8_t v_isShared_5507_; uint8_t v_isSharedCheck_5511_; 
lean_dec(v___y_5491_);
lean_dec_ref(v___y_5490_);
lean_dec(v___y_5489_);
lean_dec_ref(v___y_5488_);
lean_dec_ref(v_e_5484_);
v_a_5504_ = lean_ctor_get(v___x_5495_, 0);
v_isSharedCheck_5511_ = !lean_is_exclusive(v___x_5495_);
if (v_isSharedCheck_5511_ == 0)
{
v___x_5506_ = v___x_5495_;
v_isShared_5507_ = v_isSharedCheck_5511_;
goto v_resetjp_5505_;
}
else
{
lean_inc(v_a_5504_);
lean_dec(v___x_5495_);
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
else
{
lean_object* v___x_5512_; 
lean_dec_ref(v_e_5484_);
v___x_5512_ = lean_apply_7(v_onTrue_5485_, v___y_5486_, v___y_5487_, v___y_5488_, v___y_5489_, v___y_5490_, v___y_5491_, lean_box(0));
return v___x_5512_;
}
}
else
{
lean_object* v_a_5513_; lean_object* v___x_5515_; uint8_t v_isShared_5516_; uint8_t v_isSharedCheck_5520_; 
lean_dec(v___y_5491_);
lean_dec_ref(v___y_5490_);
lean_dec(v___y_5489_);
lean_dec_ref(v___y_5488_);
lean_dec(v___y_5487_);
lean_dec_ref(v___y_5486_);
lean_dec_ref(v_onTrue_5485_);
lean_dec_ref(v_e_5484_);
v_a_5513_ = lean_ctor_get(v___x_5492_, 0);
v_isSharedCheck_5520_ = !lean_is_exclusive(v___x_5492_);
if (v_isSharedCheck_5520_ == 0)
{
v___x_5515_ = v___x_5492_;
v_isShared_5516_ = v_isSharedCheck_5520_;
goto v_resetjp_5514_;
}
else
{
lean_inc(v_a_5513_);
lean_dec(v___x_5492_);
v___x_5515_ = lean_box(0);
v_isShared_5516_ = v_isSharedCheck_5520_;
goto v_resetjp_5514_;
}
v_resetjp_5514_:
{
lean_object* v___x_5518_; 
if (v_isShared_5516_ == 0)
{
v___x_5518_ = v___x_5515_;
goto v_reusejp_5517_;
}
else
{
lean_object* v_reuseFailAlloc_5519_; 
v_reuseFailAlloc_5519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5519_, 0, v_a_5513_);
v___x_5518_ = v_reuseFailAlloc_5519_;
goto v_reusejp_5517_;
}
v_reusejp_5517_:
{
return v___x_5518_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___boxed(lean_object* v_m_5584_, lean_object* v___x_5585_, lean_object* v_cls_5586_, lean_object* v___y_5587_, lean_object* v___y_5588_, lean_object* v___y_5589_, lean_object* v___y_5590_, lean_object* v___y_5591_, lean_object* v___y_5592_, lean_object* v___y_5593_){
_start:
{
lean_object* v_res_5594_; 
v_res_5594_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1(v_m_5584_, v___x_5585_, v_cls_5586_, v___y_5587_, v___y_5588_, v___y_5589_, v___y_5590_, v___y_5591_, v___y_5592_);
return v_res_5594_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__1(void){
_start:
{
lean_object* v___x_5596_; lean_object* v___x_5597_; 
v___x_5596_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__0));
v___x_5597_ = l_Lean_stringToMessageData(v___x_5596_);
return v___x_5597_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__3(void){
_start:
{
lean_object* v___x_5599_; lean_object* v___x_5600_; 
v___x_5599_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__2));
v___x_5600_ = l_Lean_stringToMessageData(v___x_5599_);
return v___x_5600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2(lean_object* v_x_5601_, lean_object* v___y_5602_, lean_object* v___y_5603_, lean_object* v___y_5604_, lean_object* v___y_5605_){
_start:
{
if (lean_obj_tag(v_x_5601_) == 0)
{
lean_object* v_a_5607_; lean_object* v___x_5609_; uint8_t v_isShared_5610_; uint8_t v_isSharedCheck_5617_; 
v_a_5607_ = lean_ctor_get(v_x_5601_, 0);
v_isSharedCheck_5617_ = !lean_is_exclusive(v_x_5601_);
if (v_isSharedCheck_5617_ == 0)
{
v___x_5609_ = v_x_5601_;
v_isShared_5610_ = v_isSharedCheck_5617_;
goto v_resetjp_5608_;
}
else
{
lean_inc(v_a_5607_);
lean_dec(v_x_5601_);
v___x_5609_ = lean_box(0);
v_isShared_5610_ = v_isSharedCheck_5617_;
goto v_resetjp_5608_;
}
v_resetjp_5608_:
{
lean_object* v___x_5611_; lean_object* v___x_5612_; lean_object* v___x_5613_; lean_object* v___x_5615_; 
v___x_5611_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__1);
v___x_5612_ = l_Lean_Exception_toMessageData(v_a_5607_);
v___x_5613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5613_, 0, v___x_5611_);
lean_ctor_set(v___x_5613_, 1, v___x_5612_);
if (v_isShared_5610_ == 0)
{
lean_ctor_set(v___x_5609_, 0, v___x_5613_);
v___x_5615_ = v___x_5609_;
goto v_reusejp_5614_;
}
else
{
lean_object* v_reuseFailAlloc_5616_; 
v_reuseFailAlloc_5616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5616_, 0, v___x_5613_);
v___x_5615_ = v_reuseFailAlloc_5616_;
goto v_reusejp_5614_;
}
v_reusejp_5614_:
{
return v___x_5615_;
}
}
}
else
{
lean_object* v___x_5619_; uint8_t v_isShared_5620_; uint8_t v_isSharedCheck_5625_; 
v_isSharedCheck_5625_ = !lean_is_exclusive(v_x_5601_);
if (v_isSharedCheck_5625_ == 0)
{
lean_object* v_unused_5626_; 
v_unused_5626_ = lean_ctor_get(v_x_5601_, 0);
lean_dec(v_unused_5626_);
v___x_5619_ = v_x_5601_;
v_isShared_5620_ = v_isSharedCheck_5625_;
goto v_resetjp_5618_;
}
else
{
lean_dec(v_x_5601_);
v___x_5619_ = lean_box(0);
v_isShared_5620_ = v_isSharedCheck_5625_;
goto v_resetjp_5618_;
}
v_resetjp_5618_:
{
lean_object* v___x_5621_; lean_object* v___x_5623_; 
v___x_5621_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__3, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__3);
if (v_isShared_5620_ == 0)
{
lean_ctor_set_tag(v___x_5619_, 0);
lean_ctor_set(v___x_5619_, 0, v___x_5621_);
v___x_5623_ = v___x_5619_;
goto v_reusejp_5622_;
}
else
{
lean_object* v_reuseFailAlloc_5624_; 
v_reuseFailAlloc_5624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5624_, 0, v___x_5621_);
v___x_5623_ = v_reuseFailAlloc_5624_;
goto v_reusejp_5622_;
}
v_reusejp_5622_:
{
return v___x_5623_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___boxed(lean_object* v_x_5627_, lean_object* v___y_5628_, lean_object* v___y_5629_, lean_object* v___y_5630_, lean_object* v___y_5631_, lean_object* v___y_5632_){
_start:
{
lean_object* v_res_5633_; 
v_res_5633_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2(v_x_5627_, v___y_5628_, v___y_5629_, v___y_5630_, v___y_5631_);
lean_dec(v___y_5631_);
lean_dec_ref(v___y_5630_);
lean_dec(v___y_5629_);
lean_dec_ref(v___y_5628_);
return v_res_5633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__3(lean_object* v_a_5634_, uint8_t v_hasTrace_5635_, lean_object* v___y_5636_, lean_object* v___y_5637_, lean_object* v___y_5638_, lean_object* v___y_5639_, lean_object* v___y_5640_, lean_object* v___y_5641_){
_start:
{
lean_object* v___x_5643_; 
v___x_5643_ = l_Lean_MVarId_refl(v_a_5634_, v_hasTrace_5635_, v___y_5638_, v___y_5639_, v___y_5640_, v___y_5641_);
return v___x_5643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__3___boxed(lean_object* v_a_5644_, lean_object* v_hasTrace_5645_, lean_object* v___y_5646_, lean_object* v___y_5647_, lean_object* v___y_5648_, lean_object* v___y_5649_, lean_object* v___y_5650_, lean_object* v___y_5651_, lean_object* v___y_5652_){
_start:
{
uint8_t v_hasTrace_boxed_5653_; lean_object* v_res_5654_; 
v_hasTrace_boxed_5653_ = lean_unbox(v_hasTrace_5645_);
v_res_5654_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__3(v_a_5644_, v_hasTrace_boxed_5653_, v___y_5646_, v___y_5647_, v___y_5648_, v___y_5649_, v___y_5650_, v___y_5651_);
lean_dec(v___y_5647_);
lean_dec_ref(v___y_5646_);
return v_res_5654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__4(lean_object* v_m_5655_, lean_object* v___x_5656_, lean_object* v_cls_5657_, uint8_t v_hasTrace_5658_, lean_object* v___y_5659_, lean_object* v___y_5660_, lean_object* v___y_5661_, lean_object* v___y_5662_, lean_object* v___y_5663_, lean_object* v___y_5664_){
_start:
{
lean_object* v_e_5667_; lean_object* v_onTrue_5668_; lean_object* v___y_5669_; lean_object* v___y_5670_; lean_object* v___y_5671_; lean_object* v___y_5672_; lean_object* v___y_5673_; lean_object* v___y_5674_; lean_object* v___x_5704_; 
lean_inc(v___y_5664_);
lean_inc_ref(v___y_5663_);
lean_inc(v___y_5662_);
lean_inc_ref(v___y_5661_);
v___x_5704_ = l_Lean_Meta_Sym_preprocessMVar(v_m_5655_, v___y_5659_, v___y_5660_, v___y_5661_, v___y_5662_, v___y_5663_, v___y_5664_);
if (lean_obj_tag(v___x_5704_) == 0)
{
lean_object* v_a_5705_; lean_object* v___x_5706_; 
v_a_5705_ = lean_ctor_get(v___x_5704_, 0);
lean_inc(v_a_5705_);
lean_dec_ref(v___x_5704_);
lean_inc(v_a_5705_);
v___x_5706_ = l_Lean_MVarId_getType(v_a_5705_, v___y_5661_, v___y_5662_, v___y_5663_, v___y_5664_);
if (lean_obj_tag(v___x_5706_) == 0)
{
lean_object* v_a_5707_; lean_object* v___x_5708_; lean_object* v___x_5709_; uint8_t v___x_5710_; 
v_a_5707_ = lean_ctor_get(v___x_5706_, 0);
lean_inc(v_a_5707_);
lean_dec_ref(v___x_5706_);
v___x_5708_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__4));
v___x_5709_ = lean_unsigned_to_nat(3u);
v___x_5710_ = l_Lean_Expr_isAppOfArity(v_a_5707_, v___x_5708_, v___x_5709_);
if (v___x_5710_ == 0)
{
lean_object* v___x_5711_; lean_object* v___x_5712_; lean_object* v___x_5713_; lean_object* v___x_5714_; 
lean_dec(v_a_5705_);
lean_dec(v___y_5660_);
lean_dec_ref(v___y_5659_);
lean_dec(v_cls_5657_);
lean_dec_ref(v___x_5656_);
v___x_5711_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6);
v___x_5712_ = l_Lean_indentExpr(v_a_5707_);
v___x_5713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5713_, 0, v___x_5711_);
lean_ctor_set(v___x_5713_, 1, v___x_5712_);
v___x_5714_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_5713_, v___y_5661_, v___y_5662_, v___y_5663_, v___y_5664_);
lean_dec(v___y_5664_);
lean_dec_ref(v___y_5663_);
lean_dec(v___y_5662_);
lean_dec_ref(v___y_5661_);
return v___x_5714_;
}
else
{
lean_object* v___x_5715_; lean_object* v___x_5716_; lean_object* v___x_5717_; 
v___x_5715_ = l_Lean_Expr_appFn_x21(v_a_5707_);
lean_dec(v_a_5707_);
v___x_5716_ = l_Lean_Expr_appArg_x21(v___x_5715_);
lean_dec_ref(v___x_5715_);
lean_inc(v___y_5664_);
lean_inc_ref(v___y_5663_);
lean_inc(v___y_5662_);
lean_inc_ref(v___y_5661_);
lean_inc(v___y_5660_);
lean_inc_ref(v___y_5659_);
lean_inc_ref(v___x_5716_);
v___x_5717_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_5716_, v___x_5656_, v___y_5659_, v___y_5660_, v___y_5661_, v___y_5662_, v___y_5663_, v___y_5664_);
if (lean_obj_tag(v___x_5717_) == 0)
{
lean_object* v_a_5718_; lean_object* v___x_5719_; lean_object* v_a_5720_; lean_object* v___x_5721_; lean_object* v___f_5722_; lean_object* v___y_5724_; lean_object* v___y_5725_; lean_object* v___y_5726_; lean_object* v___y_5727_; lean_object* v___y_5728_; lean_object* v___y_5729_; uint8_t v___x_5733_; 
v_a_5718_ = lean_ctor_get(v___x_5717_, 0);
lean_inc(v_a_5718_);
lean_dec_ref(v___x_5717_);
lean_inc(v_cls_5657_);
v___x_5719_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__1___redArg(v_cls_5657_, v___y_5663_);
v_a_5720_ = lean_ctor_get(v___x_5719_, 0);
lean_inc(v_a_5720_);
lean_dec_ref(v___x_5719_);
v___x_5721_ = lean_box(v_hasTrace_5658_);
lean_inc(v_a_5705_);
v___f_5722_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__3___boxed), 9, 2);
lean_closure_set(v___f_5722_, 0, v_a_5705_);
lean_closure_set(v___f_5722_, 1, v___x_5721_);
v___x_5733_ = lean_unbox(v_a_5720_);
lean_dec(v_a_5720_);
if (v___x_5733_ == 0)
{
lean_dec(v_cls_5657_);
v___y_5724_ = v___y_5659_;
v___y_5725_ = v___y_5660_;
v___y_5726_ = v___y_5661_;
v___y_5727_ = v___y_5662_;
v___y_5728_ = v___y_5663_;
v___y_5729_ = v___y_5664_;
goto v___jp_5723_;
}
else
{
lean_object* v___x_5734_; lean_object* v___x_5735_; lean_object* v___x_5736_; lean_object* v___x_5737_; lean_object* v___x_5738_; lean_object* v___x_5739_; lean_object* v___x_5740_; lean_object* v___x_5741_; lean_object* v___x_5742_; 
v___x_5734_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8);
lean_inc_ref(v___x_5716_);
v___x_5735_ = l_Lean_indentExpr(v___x_5716_);
v___x_5736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5736_, 0, v___x_5734_);
lean_ctor_set(v___x_5736_, 1, v___x_5735_);
v___x_5737_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7);
v___x_5738_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5738_, 0, v___x_5736_);
lean_ctor_set(v___x_5738_, 1, v___x_5737_);
v___x_5739_ = l_Lean_Meta_Sym_Simp_Result_getResultExpr(v___x_5716_, v_a_5718_);
v___x_5740_ = l_Lean_indentExpr(v___x_5739_);
v___x_5741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5741_, 0, v___x_5738_);
lean_ctor_set(v___x_5741_, 1, v___x_5740_);
v___x_5742_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(v_cls_5657_, v___x_5741_, v___y_5661_, v___y_5662_, v___y_5663_, v___y_5664_);
if (lean_obj_tag(v___x_5742_) == 0)
{
lean_dec_ref(v___x_5742_);
v___y_5724_ = v___y_5659_;
v___y_5725_ = v___y_5660_;
v___y_5726_ = v___y_5661_;
v___y_5727_ = v___y_5662_;
v___y_5728_ = v___y_5663_;
v___y_5729_ = v___y_5664_;
goto v___jp_5723_;
}
else
{
lean_dec_ref(v___f_5722_);
lean_dec(v_a_5718_);
lean_dec_ref(v___x_5716_);
lean_dec(v_a_5705_);
lean_dec(v___y_5664_);
lean_dec_ref(v___y_5663_);
lean_dec(v___y_5662_);
lean_dec_ref(v___y_5661_);
lean_dec(v___y_5660_);
lean_dec_ref(v___y_5659_);
return v___x_5742_;
}
}
v___jp_5723_:
{
if (lean_obj_tag(v_a_5718_) == 0)
{
lean_dec_ref(v_a_5718_);
lean_dec(v_a_5705_);
v_e_5667_ = v___x_5716_;
v_onTrue_5668_ = v___f_5722_;
v___y_5669_ = v___y_5724_;
v___y_5670_ = v___y_5725_;
v___y_5671_ = v___y_5726_;
v___y_5672_ = v___y_5727_;
v___y_5673_ = v___y_5728_;
v___y_5674_ = v___y_5729_;
goto v___jp_5666_;
}
else
{
lean_object* v_e_x27_5730_; lean_object* v_proof_5731_; lean_object* v___x_5732_; 
lean_dec_ref(v___f_5722_);
lean_dec_ref(v___x_5716_);
v_e_x27_5730_ = lean_ctor_get(v_a_5718_, 0);
lean_inc_ref(v_e_x27_5730_);
v_proof_5731_ = lean_ctor_get(v_a_5718_, 1);
lean_inc_ref(v_proof_5731_);
lean_dec_ref(v_a_5718_);
v___x_5732_ = lean_alloc_closure((void*)(l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0___boxed), 9, 2);
lean_closure_set(v___x_5732_, 0, v_a_5705_);
lean_closure_set(v___x_5732_, 1, v_proof_5731_);
v_e_5667_ = v_e_x27_5730_;
v_onTrue_5668_ = v___x_5732_;
v___y_5669_ = v___y_5724_;
v___y_5670_ = v___y_5725_;
v___y_5671_ = v___y_5726_;
v___y_5672_ = v___y_5727_;
v___y_5673_ = v___y_5728_;
v___y_5674_ = v___y_5729_;
goto v___jp_5666_;
}
}
}
else
{
lean_object* v_a_5743_; lean_object* v___x_5745_; uint8_t v_isShared_5746_; uint8_t v_isSharedCheck_5750_; 
lean_dec_ref(v___x_5716_);
lean_dec(v_a_5705_);
lean_dec(v___y_5664_);
lean_dec_ref(v___y_5663_);
lean_dec(v___y_5662_);
lean_dec_ref(v___y_5661_);
lean_dec(v___y_5660_);
lean_dec_ref(v___y_5659_);
lean_dec(v_cls_5657_);
v_a_5743_ = lean_ctor_get(v___x_5717_, 0);
v_isSharedCheck_5750_ = !lean_is_exclusive(v___x_5717_);
if (v_isSharedCheck_5750_ == 0)
{
v___x_5745_ = v___x_5717_;
v_isShared_5746_ = v_isSharedCheck_5750_;
goto v_resetjp_5744_;
}
else
{
lean_inc(v_a_5743_);
lean_dec(v___x_5717_);
v___x_5745_ = lean_box(0);
v_isShared_5746_ = v_isSharedCheck_5750_;
goto v_resetjp_5744_;
}
v_resetjp_5744_:
{
lean_object* v___x_5748_; 
if (v_isShared_5746_ == 0)
{
v___x_5748_ = v___x_5745_;
goto v_reusejp_5747_;
}
else
{
lean_object* v_reuseFailAlloc_5749_; 
v_reuseFailAlloc_5749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5749_, 0, v_a_5743_);
v___x_5748_ = v_reuseFailAlloc_5749_;
goto v_reusejp_5747_;
}
v_reusejp_5747_:
{
return v___x_5748_;
}
}
}
}
}
else
{
lean_object* v_a_5751_; lean_object* v___x_5753_; uint8_t v_isShared_5754_; uint8_t v_isSharedCheck_5758_; 
lean_dec(v_a_5705_);
lean_dec(v___y_5664_);
lean_dec_ref(v___y_5663_);
lean_dec(v___y_5662_);
lean_dec_ref(v___y_5661_);
lean_dec(v___y_5660_);
lean_dec_ref(v___y_5659_);
lean_dec(v_cls_5657_);
lean_dec_ref(v___x_5656_);
v_a_5751_ = lean_ctor_get(v___x_5706_, 0);
v_isSharedCheck_5758_ = !lean_is_exclusive(v___x_5706_);
if (v_isSharedCheck_5758_ == 0)
{
v___x_5753_ = v___x_5706_;
v_isShared_5754_ = v_isSharedCheck_5758_;
goto v_resetjp_5752_;
}
else
{
lean_inc(v_a_5751_);
lean_dec(v___x_5706_);
v___x_5753_ = lean_box(0);
v_isShared_5754_ = v_isSharedCheck_5758_;
goto v_resetjp_5752_;
}
v_resetjp_5752_:
{
lean_object* v___x_5756_; 
if (v_isShared_5754_ == 0)
{
v___x_5756_ = v___x_5753_;
goto v_reusejp_5755_;
}
else
{
lean_object* v_reuseFailAlloc_5757_; 
v_reuseFailAlloc_5757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5757_, 0, v_a_5751_);
v___x_5756_ = v_reuseFailAlloc_5757_;
goto v_reusejp_5755_;
}
v_reusejp_5755_:
{
return v___x_5756_;
}
}
}
}
else
{
lean_object* v_a_5759_; lean_object* v___x_5761_; uint8_t v_isShared_5762_; uint8_t v_isSharedCheck_5766_; 
lean_dec(v___y_5664_);
lean_dec_ref(v___y_5663_);
lean_dec(v___y_5662_);
lean_dec_ref(v___y_5661_);
lean_dec(v___y_5660_);
lean_dec_ref(v___y_5659_);
lean_dec(v_cls_5657_);
lean_dec_ref(v___x_5656_);
v_a_5759_ = lean_ctor_get(v___x_5704_, 0);
v_isSharedCheck_5766_ = !lean_is_exclusive(v___x_5704_);
if (v_isSharedCheck_5766_ == 0)
{
v___x_5761_ = v___x_5704_;
v_isShared_5762_ = v_isSharedCheck_5766_;
goto v_resetjp_5760_;
}
else
{
lean_inc(v_a_5759_);
lean_dec(v___x_5704_);
v___x_5761_ = lean_box(0);
v_isShared_5762_ = v_isSharedCheck_5766_;
goto v_resetjp_5760_;
}
v_resetjp_5760_:
{
lean_object* v___x_5764_; 
if (v_isShared_5762_ == 0)
{
v___x_5764_ = v___x_5761_;
goto v_reusejp_5763_;
}
else
{
lean_object* v_reuseFailAlloc_5765_; 
v_reuseFailAlloc_5765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5765_, 0, v_a_5759_);
v___x_5764_ = v_reuseFailAlloc_5765_;
goto v_reusejp_5763_;
}
v_reusejp_5763_:
{
return v___x_5764_;
}
}
}
v___jp_5666_:
{
lean_object* v___x_5675_; 
v___x_5675_ = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(v_e_5667_, v___y_5669_);
if (lean_obj_tag(v___x_5675_) == 0)
{
lean_object* v_a_5676_; uint8_t v___x_5677_; 
v_a_5676_ = lean_ctor_get(v___x_5675_, 0);
lean_inc(v_a_5676_);
lean_dec_ref(v___x_5675_);
v___x_5677_ = lean_unbox(v_a_5676_);
lean_dec(v_a_5676_);
if (v___x_5677_ == 0)
{
lean_object* v___x_5678_; 
lean_dec(v___y_5670_);
lean_dec_ref(v_onTrue_5668_);
v___x_5678_ = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(v_e_5667_, v___y_5669_);
lean_dec_ref(v___y_5669_);
if (lean_obj_tag(v___x_5678_) == 0)
{
lean_object* v_a_5679_; uint8_t v___x_5680_; 
v_a_5679_ = lean_ctor_get(v___x_5678_, 0);
lean_inc(v_a_5679_);
lean_dec_ref(v___x_5678_);
v___x_5680_ = lean_unbox(v_a_5679_);
lean_dec(v_a_5679_);
if (v___x_5680_ == 0)
{
lean_object* v___x_5681_; lean_object* v___x_5682_; lean_object* v___x_5683_; lean_object* v___x_5684_; 
v___x_5681_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1);
v___x_5682_ = l_Lean_indentExpr(v_e_5667_);
v___x_5683_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5683_, 0, v___x_5681_);
lean_ctor_set(v___x_5683_, 1, v___x_5682_);
v___x_5684_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_5683_, v___y_5671_, v___y_5672_, v___y_5673_, v___y_5674_);
lean_dec(v___y_5674_);
lean_dec_ref(v___y_5673_);
lean_dec(v___y_5672_);
lean_dec_ref(v___y_5671_);
return v___x_5684_;
}
else
{
lean_object* v___x_5685_; lean_object* v___x_5686_; 
lean_dec_ref(v_e_5667_);
v___x_5685_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3);
v___x_5686_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_5685_, v___y_5671_, v___y_5672_, v___y_5673_, v___y_5674_);
lean_dec(v___y_5674_);
lean_dec_ref(v___y_5673_);
lean_dec(v___y_5672_);
lean_dec_ref(v___y_5671_);
return v___x_5686_;
}
}
else
{
lean_object* v_a_5687_; lean_object* v___x_5689_; uint8_t v_isShared_5690_; uint8_t v_isSharedCheck_5694_; 
lean_dec(v___y_5674_);
lean_dec_ref(v___y_5673_);
lean_dec(v___y_5672_);
lean_dec_ref(v___y_5671_);
lean_dec_ref(v_e_5667_);
v_a_5687_ = lean_ctor_get(v___x_5678_, 0);
v_isSharedCheck_5694_ = !lean_is_exclusive(v___x_5678_);
if (v_isSharedCheck_5694_ == 0)
{
v___x_5689_ = v___x_5678_;
v_isShared_5690_ = v_isSharedCheck_5694_;
goto v_resetjp_5688_;
}
else
{
lean_inc(v_a_5687_);
lean_dec(v___x_5678_);
v___x_5689_ = lean_box(0);
v_isShared_5690_ = v_isSharedCheck_5694_;
goto v_resetjp_5688_;
}
v_resetjp_5688_:
{
lean_object* v___x_5692_; 
if (v_isShared_5690_ == 0)
{
v___x_5692_ = v___x_5689_;
goto v_reusejp_5691_;
}
else
{
lean_object* v_reuseFailAlloc_5693_; 
v_reuseFailAlloc_5693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5693_, 0, v_a_5687_);
v___x_5692_ = v_reuseFailAlloc_5693_;
goto v_reusejp_5691_;
}
v_reusejp_5691_:
{
return v___x_5692_;
}
}
}
}
else
{
lean_object* v___x_5695_; 
lean_dec_ref(v_e_5667_);
v___x_5695_ = lean_apply_7(v_onTrue_5668_, v___y_5669_, v___y_5670_, v___y_5671_, v___y_5672_, v___y_5673_, v___y_5674_, lean_box(0));
return v___x_5695_;
}
}
else
{
lean_object* v_a_5696_; lean_object* v___x_5698_; uint8_t v_isShared_5699_; uint8_t v_isSharedCheck_5703_; 
lean_dec(v___y_5674_);
lean_dec_ref(v___y_5673_);
lean_dec(v___y_5672_);
lean_dec_ref(v___y_5671_);
lean_dec(v___y_5670_);
lean_dec_ref(v___y_5669_);
lean_dec_ref(v_onTrue_5668_);
lean_dec_ref(v_e_5667_);
v_a_5696_ = lean_ctor_get(v___x_5675_, 0);
v_isSharedCheck_5703_ = !lean_is_exclusive(v___x_5675_);
if (v_isSharedCheck_5703_ == 0)
{
v___x_5698_ = v___x_5675_;
v_isShared_5699_ = v_isSharedCheck_5703_;
goto v_resetjp_5697_;
}
else
{
lean_inc(v_a_5696_);
lean_dec(v___x_5675_);
v___x_5698_ = lean_box(0);
v_isShared_5699_ = v_isSharedCheck_5703_;
goto v_resetjp_5697_;
}
v_resetjp_5697_:
{
lean_object* v___x_5701_; 
if (v_isShared_5699_ == 0)
{
v___x_5701_ = v___x_5698_;
goto v_reusejp_5700_;
}
else
{
lean_object* v_reuseFailAlloc_5702_; 
v_reuseFailAlloc_5702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5702_, 0, v_a_5696_);
v___x_5701_ = v_reuseFailAlloc_5702_;
goto v_reusejp_5700_;
}
v_reusejp_5700_:
{
return v___x_5701_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__4___boxed(lean_object* v_m_5767_, lean_object* v___x_5768_, lean_object* v_cls_5769_, lean_object* v_hasTrace_5770_, lean_object* v___y_5771_, lean_object* v___y_5772_, lean_object* v___y_5773_, lean_object* v___y_5774_, lean_object* v___y_5775_, lean_object* v___y_5776_, lean_object* v___y_5777_){
_start:
{
uint8_t v_hasTrace_boxed_5778_; lean_object* v_res_5779_; 
v_hasTrace_boxed_5778_ = lean_unbox(v_hasTrace_5770_);
v_res_5779_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__4(v_m_5767_, v___x_5768_, v_cls_5769_, v_hasTrace_boxed_5778_, v___y_5771_, v___y_5772_, v___y_5773_, v___y_5774_, v___y_5775_, v___y_5776_);
return v_res_5779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__6(lean_object* v_m_5780_, lean_object* v___x_5781_, lean_object* v_cls_5782_, uint8_t v___x_5783_, lean_object* v___y_5784_, lean_object* v___y_5785_, lean_object* v___y_5786_, lean_object* v___y_5787_, lean_object* v___y_5788_, lean_object* v___y_5789_){
_start:
{
lean_object* v_e_5792_; lean_object* v_onTrue_5793_; lean_object* v___y_5794_; lean_object* v___y_5795_; lean_object* v___y_5796_; lean_object* v___y_5797_; lean_object* v___y_5798_; lean_object* v___y_5799_; lean_object* v___x_5829_; 
lean_inc(v___y_5789_);
lean_inc_ref(v___y_5788_);
lean_inc(v___y_5787_);
lean_inc_ref(v___y_5786_);
v___x_5829_ = l_Lean_Meta_Sym_preprocessMVar(v_m_5780_, v___y_5784_, v___y_5785_, v___y_5786_, v___y_5787_, v___y_5788_, v___y_5789_);
if (lean_obj_tag(v___x_5829_) == 0)
{
lean_object* v_a_5830_; lean_object* v___x_5831_; 
v_a_5830_ = lean_ctor_get(v___x_5829_, 0);
lean_inc(v_a_5830_);
lean_dec_ref(v___x_5829_);
lean_inc(v_a_5830_);
v___x_5831_ = l_Lean_MVarId_getType(v_a_5830_, v___y_5786_, v___y_5787_, v___y_5788_, v___y_5789_);
if (lean_obj_tag(v___x_5831_) == 0)
{
lean_object* v_a_5832_; lean_object* v___x_5833_; lean_object* v___x_5834_; uint8_t v___x_5835_; 
v_a_5832_ = lean_ctor_get(v___x_5831_, 0);
lean_inc(v_a_5832_);
lean_dec_ref(v___x_5831_);
v___x_5833_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__4));
v___x_5834_ = lean_unsigned_to_nat(3u);
v___x_5835_ = l_Lean_Expr_isAppOfArity(v_a_5832_, v___x_5833_, v___x_5834_);
if (v___x_5835_ == 0)
{
lean_object* v___x_5836_; lean_object* v___x_5837_; lean_object* v___x_5838_; lean_object* v___x_5839_; 
lean_dec(v_a_5830_);
lean_dec(v___y_5785_);
lean_dec_ref(v___y_5784_);
lean_dec(v_cls_5782_);
lean_dec_ref(v___x_5781_);
v___x_5836_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6);
v___x_5837_ = l_Lean_indentExpr(v_a_5832_);
v___x_5838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5838_, 0, v___x_5836_);
lean_ctor_set(v___x_5838_, 1, v___x_5837_);
v___x_5839_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_5838_, v___y_5786_, v___y_5787_, v___y_5788_, v___y_5789_);
lean_dec(v___y_5789_);
lean_dec_ref(v___y_5788_);
lean_dec(v___y_5787_);
lean_dec_ref(v___y_5786_);
return v___x_5839_;
}
else
{
lean_object* v___x_5840_; lean_object* v___x_5841_; lean_object* v___x_5842_; 
v___x_5840_ = l_Lean_Expr_appFn_x21(v_a_5832_);
lean_dec(v_a_5832_);
v___x_5841_ = l_Lean_Expr_appArg_x21(v___x_5840_);
lean_dec_ref(v___x_5840_);
lean_inc(v___y_5789_);
lean_inc_ref(v___y_5788_);
lean_inc(v___y_5787_);
lean_inc_ref(v___y_5786_);
lean_inc(v___y_5785_);
lean_inc_ref(v___y_5784_);
lean_inc_ref(v___x_5841_);
v___x_5842_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_5841_, v___x_5781_, v___y_5784_, v___y_5785_, v___y_5786_, v___y_5787_, v___y_5788_, v___y_5789_);
if (lean_obj_tag(v___x_5842_) == 0)
{
lean_object* v_a_5843_; lean_object* v___x_5844_; lean_object* v_a_5845_; lean_object* v___x_5846_; lean_object* v___f_5847_; lean_object* v___y_5849_; lean_object* v___y_5850_; lean_object* v___y_5851_; lean_object* v___y_5852_; lean_object* v___y_5853_; lean_object* v___y_5854_; uint8_t v___x_5858_; 
v_a_5843_ = lean_ctor_get(v___x_5842_, 0);
lean_inc(v_a_5843_);
lean_dec_ref(v___x_5842_);
lean_inc(v_cls_5782_);
v___x_5844_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__1___redArg(v_cls_5782_, v___y_5788_);
v_a_5845_ = lean_ctor_get(v___x_5844_, 0);
lean_inc(v_a_5845_);
lean_dec_ref(v___x_5844_);
v___x_5846_ = lean_box(v___x_5783_);
lean_inc(v_a_5830_);
v___f_5847_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5847_, 0, v_a_5830_);
lean_closure_set(v___f_5847_, 1, v___x_5846_);
v___x_5858_ = lean_unbox(v_a_5845_);
lean_dec(v_a_5845_);
if (v___x_5858_ == 0)
{
lean_dec(v_cls_5782_);
v___y_5849_ = v___y_5784_;
v___y_5850_ = v___y_5785_;
v___y_5851_ = v___y_5786_;
v___y_5852_ = v___y_5787_;
v___y_5853_ = v___y_5788_;
v___y_5854_ = v___y_5789_;
goto v___jp_5848_;
}
else
{
lean_object* v___x_5859_; lean_object* v___x_5860_; lean_object* v___x_5861_; lean_object* v___x_5862_; lean_object* v___x_5863_; lean_object* v___x_5864_; lean_object* v___x_5865_; lean_object* v___x_5866_; lean_object* v___x_5867_; 
v___x_5859_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8);
lean_inc_ref(v___x_5841_);
v___x_5860_ = l_Lean_indentExpr(v___x_5841_);
v___x_5861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5861_, 0, v___x_5859_);
lean_ctor_set(v___x_5861_, 1, v___x_5860_);
v___x_5862_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7);
v___x_5863_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5863_, 0, v___x_5861_);
lean_ctor_set(v___x_5863_, 1, v___x_5862_);
v___x_5864_ = l_Lean_Meta_Sym_Simp_Result_getResultExpr(v___x_5841_, v_a_5843_);
v___x_5865_ = l_Lean_indentExpr(v___x_5864_);
v___x_5866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5866_, 0, v___x_5863_);
lean_ctor_set(v___x_5866_, 1, v___x_5865_);
v___x_5867_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(v_cls_5782_, v___x_5866_, v___y_5786_, v___y_5787_, v___y_5788_, v___y_5789_);
if (lean_obj_tag(v___x_5867_) == 0)
{
lean_dec_ref(v___x_5867_);
v___y_5849_ = v___y_5784_;
v___y_5850_ = v___y_5785_;
v___y_5851_ = v___y_5786_;
v___y_5852_ = v___y_5787_;
v___y_5853_ = v___y_5788_;
v___y_5854_ = v___y_5789_;
goto v___jp_5848_;
}
else
{
lean_dec_ref(v___f_5847_);
lean_dec(v_a_5843_);
lean_dec_ref(v___x_5841_);
lean_dec(v_a_5830_);
lean_dec(v___y_5789_);
lean_dec_ref(v___y_5788_);
lean_dec(v___y_5787_);
lean_dec_ref(v___y_5786_);
lean_dec(v___y_5785_);
lean_dec_ref(v___y_5784_);
return v___x_5867_;
}
}
v___jp_5848_:
{
if (lean_obj_tag(v_a_5843_) == 0)
{
lean_dec_ref(v_a_5843_);
lean_dec(v_a_5830_);
v_e_5792_ = v___x_5841_;
v_onTrue_5793_ = v___f_5847_;
v___y_5794_ = v___y_5849_;
v___y_5795_ = v___y_5850_;
v___y_5796_ = v___y_5851_;
v___y_5797_ = v___y_5852_;
v___y_5798_ = v___y_5853_;
v___y_5799_ = v___y_5854_;
goto v___jp_5791_;
}
else
{
lean_object* v_e_x27_5855_; lean_object* v_proof_5856_; lean_object* v___x_5857_; 
lean_dec_ref(v___f_5847_);
lean_dec_ref(v___x_5841_);
v_e_x27_5855_ = lean_ctor_get(v_a_5843_, 0);
lean_inc_ref(v_e_x27_5855_);
v_proof_5856_ = lean_ctor_get(v_a_5843_, 1);
lean_inc_ref(v_proof_5856_);
lean_dec_ref(v_a_5843_);
v___x_5857_ = lean_alloc_closure((void*)(l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0___boxed), 9, 2);
lean_closure_set(v___x_5857_, 0, v_a_5830_);
lean_closure_set(v___x_5857_, 1, v_proof_5856_);
v_e_5792_ = v_e_x27_5855_;
v_onTrue_5793_ = v___x_5857_;
v___y_5794_ = v___y_5849_;
v___y_5795_ = v___y_5850_;
v___y_5796_ = v___y_5851_;
v___y_5797_ = v___y_5852_;
v___y_5798_ = v___y_5853_;
v___y_5799_ = v___y_5854_;
goto v___jp_5791_;
}
}
}
else
{
lean_object* v_a_5868_; lean_object* v___x_5870_; uint8_t v_isShared_5871_; uint8_t v_isSharedCheck_5875_; 
lean_dec_ref(v___x_5841_);
lean_dec(v_a_5830_);
lean_dec(v___y_5789_);
lean_dec_ref(v___y_5788_);
lean_dec(v___y_5787_);
lean_dec_ref(v___y_5786_);
lean_dec(v___y_5785_);
lean_dec_ref(v___y_5784_);
lean_dec(v_cls_5782_);
v_a_5868_ = lean_ctor_get(v___x_5842_, 0);
v_isSharedCheck_5875_ = !lean_is_exclusive(v___x_5842_);
if (v_isSharedCheck_5875_ == 0)
{
v___x_5870_ = v___x_5842_;
v_isShared_5871_ = v_isSharedCheck_5875_;
goto v_resetjp_5869_;
}
else
{
lean_inc(v_a_5868_);
lean_dec(v___x_5842_);
v___x_5870_ = lean_box(0);
v_isShared_5871_ = v_isSharedCheck_5875_;
goto v_resetjp_5869_;
}
v_resetjp_5869_:
{
lean_object* v___x_5873_; 
if (v_isShared_5871_ == 0)
{
v___x_5873_ = v___x_5870_;
goto v_reusejp_5872_;
}
else
{
lean_object* v_reuseFailAlloc_5874_; 
v_reuseFailAlloc_5874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5874_, 0, v_a_5868_);
v___x_5873_ = v_reuseFailAlloc_5874_;
goto v_reusejp_5872_;
}
v_reusejp_5872_:
{
return v___x_5873_;
}
}
}
}
}
else
{
lean_object* v_a_5876_; lean_object* v___x_5878_; uint8_t v_isShared_5879_; uint8_t v_isSharedCheck_5883_; 
lean_dec(v_a_5830_);
lean_dec(v___y_5789_);
lean_dec_ref(v___y_5788_);
lean_dec(v___y_5787_);
lean_dec_ref(v___y_5786_);
lean_dec(v___y_5785_);
lean_dec_ref(v___y_5784_);
lean_dec(v_cls_5782_);
lean_dec_ref(v___x_5781_);
v_a_5876_ = lean_ctor_get(v___x_5831_, 0);
v_isSharedCheck_5883_ = !lean_is_exclusive(v___x_5831_);
if (v_isSharedCheck_5883_ == 0)
{
v___x_5878_ = v___x_5831_;
v_isShared_5879_ = v_isSharedCheck_5883_;
goto v_resetjp_5877_;
}
else
{
lean_inc(v_a_5876_);
lean_dec(v___x_5831_);
v___x_5878_ = lean_box(0);
v_isShared_5879_ = v_isSharedCheck_5883_;
goto v_resetjp_5877_;
}
v_resetjp_5877_:
{
lean_object* v___x_5881_; 
if (v_isShared_5879_ == 0)
{
v___x_5881_ = v___x_5878_;
goto v_reusejp_5880_;
}
else
{
lean_object* v_reuseFailAlloc_5882_; 
v_reuseFailAlloc_5882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5882_, 0, v_a_5876_);
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
else
{
lean_object* v_a_5884_; lean_object* v___x_5886_; uint8_t v_isShared_5887_; uint8_t v_isSharedCheck_5891_; 
lean_dec(v___y_5789_);
lean_dec_ref(v___y_5788_);
lean_dec(v___y_5787_);
lean_dec_ref(v___y_5786_);
lean_dec(v___y_5785_);
lean_dec_ref(v___y_5784_);
lean_dec(v_cls_5782_);
lean_dec_ref(v___x_5781_);
v_a_5884_ = lean_ctor_get(v___x_5829_, 0);
v_isSharedCheck_5891_ = !lean_is_exclusive(v___x_5829_);
if (v_isSharedCheck_5891_ == 0)
{
v___x_5886_ = v___x_5829_;
v_isShared_5887_ = v_isSharedCheck_5891_;
goto v_resetjp_5885_;
}
else
{
lean_inc(v_a_5884_);
lean_dec(v___x_5829_);
v___x_5886_ = lean_box(0);
v_isShared_5887_ = v_isSharedCheck_5891_;
goto v_resetjp_5885_;
}
v_resetjp_5885_:
{
lean_object* v___x_5889_; 
if (v_isShared_5887_ == 0)
{
v___x_5889_ = v___x_5886_;
goto v_reusejp_5888_;
}
else
{
lean_object* v_reuseFailAlloc_5890_; 
v_reuseFailAlloc_5890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5890_, 0, v_a_5884_);
v___x_5889_ = v_reuseFailAlloc_5890_;
goto v_reusejp_5888_;
}
v_reusejp_5888_:
{
return v___x_5889_;
}
}
}
v___jp_5791_:
{
lean_object* v___x_5800_; 
v___x_5800_ = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(v_e_5792_, v___y_5794_);
if (lean_obj_tag(v___x_5800_) == 0)
{
lean_object* v_a_5801_; uint8_t v___x_5802_; 
v_a_5801_ = lean_ctor_get(v___x_5800_, 0);
lean_inc(v_a_5801_);
lean_dec_ref(v___x_5800_);
v___x_5802_ = lean_unbox(v_a_5801_);
lean_dec(v_a_5801_);
if (v___x_5802_ == 0)
{
lean_object* v___x_5803_; 
lean_dec(v___y_5795_);
lean_dec_ref(v_onTrue_5793_);
v___x_5803_ = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(v_e_5792_, v___y_5794_);
lean_dec_ref(v___y_5794_);
if (lean_obj_tag(v___x_5803_) == 0)
{
lean_object* v_a_5804_; uint8_t v___x_5805_; 
v_a_5804_ = lean_ctor_get(v___x_5803_, 0);
lean_inc(v_a_5804_);
lean_dec_ref(v___x_5803_);
v___x_5805_ = lean_unbox(v_a_5804_);
lean_dec(v_a_5804_);
if (v___x_5805_ == 0)
{
lean_object* v___x_5806_; lean_object* v___x_5807_; lean_object* v___x_5808_; lean_object* v___x_5809_; 
v___x_5806_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1);
v___x_5807_ = l_Lean_indentExpr(v_e_5792_);
v___x_5808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5808_, 0, v___x_5806_);
lean_ctor_set(v___x_5808_, 1, v___x_5807_);
v___x_5809_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_5808_, v___y_5796_, v___y_5797_, v___y_5798_, v___y_5799_);
lean_dec(v___y_5799_);
lean_dec_ref(v___y_5798_);
lean_dec(v___y_5797_);
lean_dec_ref(v___y_5796_);
return v___x_5809_;
}
else
{
lean_object* v___x_5810_; lean_object* v___x_5811_; 
lean_dec_ref(v_e_5792_);
v___x_5810_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3);
v___x_5811_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_5810_, v___y_5796_, v___y_5797_, v___y_5798_, v___y_5799_);
lean_dec(v___y_5799_);
lean_dec_ref(v___y_5798_);
lean_dec(v___y_5797_);
lean_dec_ref(v___y_5796_);
return v___x_5811_;
}
}
else
{
lean_object* v_a_5812_; lean_object* v___x_5814_; uint8_t v_isShared_5815_; uint8_t v_isSharedCheck_5819_; 
lean_dec(v___y_5799_);
lean_dec_ref(v___y_5798_);
lean_dec(v___y_5797_);
lean_dec_ref(v___y_5796_);
lean_dec_ref(v_e_5792_);
v_a_5812_ = lean_ctor_get(v___x_5803_, 0);
v_isSharedCheck_5819_ = !lean_is_exclusive(v___x_5803_);
if (v_isSharedCheck_5819_ == 0)
{
v___x_5814_ = v___x_5803_;
v_isShared_5815_ = v_isSharedCheck_5819_;
goto v_resetjp_5813_;
}
else
{
lean_inc(v_a_5812_);
lean_dec(v___x_5803_);
v___x_5814_ = lean_box(0);
v_isShared_5815_ = v_isSharedCheck_5819_;
goto v_resetjp_5813_;
}
v_resetjp_5813_:
{
lean_object* v___x_5817_; 
if (v_isShared_5815_ == 0)
{
v___x_5817_ = v___x_5814_;
goto v_reusejp_5816_;
}
else
{
lean_object* v_reuseFailAlloc_5818_; 
v_reuseFailAlloc_5818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5818_, 0, v_a_5812_);
v___x_5817_ = v_reuseFailAlloc_5818_;
goto v_reusejp_5816_;
}
v_reusejp_5816_:
{
return v___x_5817_;
}
}
}
}
else
{
lean_object* v___x_5820_; 
lean_dec_ref(v_e_5792_);
v___x_5820_ = lean_apply_7(v_onTrue_5793_, v___y_5794_, v___y_5795_, v___y_5796_, v___y_5797_, v___y_5798_, v___y_5799_, lean_box(0));
return v___x_5820_;
}
}
else
{
lean_object* v_a_5821_; lean_object* v___x_5823_; uint8_t v_isShared_5824_; uint8_t v_isSharedCheck_5828_; 
lean_dec(v___y_5799_);
lean_dec_ref(v___y_5798_);
lean_dec(v___y_5797_);
lean_dec_ref(v___y_5796_);
lean_dec(v___y_5795_);
lean_dec_ref(v___y_5794_);
lean_dec_ref(v_onTrue_5793_);
lean_dec_ref(v_e_5792_);
v_a_5821_ = lean_ctor_get(v___x_5800_, 0);
v_isSharedCheck_5828_ = !lean_is_exclusive(v___x_5800_);
if (v_isSharedCheck_5828_ == 0)
{
v___x_5823_ = v___x_5800_;
v_isShared_5824_ = v_isSharedCheck_5828_;
goto v_resetjp_5822_;
}
else
{
lean_inc(v_a_5821_);
lean_dec(v___x_5800_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__6___boxed(lean_object* v_m_5892_, lean_object* v___x_5893_, lean_object* v_cls_5894_, lean_object* v___x_5895_, lean_object* v___y_5896_, lean_object* v___y_5897_, lean_object* v___y_5898_, lean_object* v___y_5899_, lean_object* v___y_5900_, lean_object* v___y_5901_, lean_object* v___y_5902_){
_start:
{
uint8_t v___x_21946__boxed_5903_; lean_object* v_res_5904_; 
v___x_21946__boxed_5903_ = lean_unbox(v___x_5895_);
v_res_5904_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__6(v_m_5892_, v___x_5893_, v_cls_5894_, v___x_21946__boxed_5903_, v___y_5896_, v___y_5897_, v___y_5898_, v___y_5899_, v___y_5900_, v___y_5901_);
return v_res_5904_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2_spec__2(lean_object* v_e_5905_){
_start:
{
if (lean_obj_tag(v_e_5905_) == 0)
{
uint8_t v___x_5906_; 
v___x_5906_ = 2;
return v___x_5906_;
}
else
{
uint8_t v___x_5907_; 
v___x_5907_ = 0;
return v___x_5907_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2_spec__2___boxed(lean_object* v_e_5908_){
_start:
{
uint8_t v_res_5909_; lean_object* v_r_5910_; 
v_res_5909_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2_spec__2(v_e_5908_);
lean_dec_ref(v_e_5908_);
v_r_5910_ = lean_box(v_res_5909_);
return v_r_5910_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2(lean_object* v_cls_5911_, uint8_t v_collapsed_5912_, lean_object* v_tag_5913_, lean_object* v_opts_5914_, uint8_t v_clsEnabled_5915_, lean_object* v_oldTraces_5916_, lean_object* v_msg_5917_, lean_object* v_resStartStop_5918_, lean_object* v___y_5919_, lean_object* v___y_5920_, lean_object* v___y_5921_, lean_object* v___y_5922_){
_start:
{
lean_object* v_fst_5924_; lean_object* v_snd_5925_; lean_object* v___x_5927_; uint8_t v_isShared_5928_; uint8_t v_isSharedCheck_6015_; 
v_fst_5924_ = lean_ctor_get(v_resStartStop_5918_, 0);
v_snd_5925_ = lean_ctor_get(v_resStartStop_5918_, 1);
v_isSharedCheck_6015_ = !lean_is_exclusive(v_resStartStop_5918_);
if (v_isSharedCheck_6015_ == 0)
{
v___x_5927_ = v_resStartStop_5918_;
v_isShared_5928_ = v_isSharedCheck_6015_;
goto v_resetjp_5926_;
}
else
{
lean_inc(v_snd_5925_);
lean_inc(v_fst_5924_);
lean_dec(v_resStartStop_5918_);
v___x_5927_ = lean_box(0);
v_isShared_5928_ = v_isSharedCheck_6015_;
goto v_resetjp_5926_;
}
v_resetjp_5926_:
{
lean_object* v___y_5930_; lean_object* v___y_5931_; lean_object* v_data_5932_; lean_object* v_fst_5935_; lean_object* v_snd_5936_; lean_object* v___x_5938_; uint8_t v_isShared_5939_; uint8_t v_isSharedCheck_6014_; 
v_fst_5935_ = lean_ctor_get(v_snd_5925_, 0);
v_snd_5936_ = lean_ctor_get(v_snd_5925_, 1);
v_isSharedCheck_6014_ = !lean_is_exclusive(v_snd_5925_);
if (v_isSharedCheck_6014_ == 0)
{
v___x_5938_ = v_snd_5925_;
v_isShared_5939_ = v_isSharedCheck_6014_;
goto v_resetjp_5937_;
}
else
{
lean_inc(v_snd_5936_);
lean_inc(v_fst_5935_);
lean_dec(v_snd_5925_);
v___x_5938_ = lean_box(0);
v_isShared_5939_ = v_isSharedCheck_6014_;
goto v_resetjp_5937_;
}
v___jp_5929_:
{
lean_object* v___x_5933_; 
v___x_5933_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__2_spec__2(v_oldTraces_5916_, v_data_5932_, v___y_5931_, v___y_5930_, v___y_5919_, v___y_5920_, v___y_5921_, v___y_5922_);
lean_dec(v___y_5922_);
lean_dec(v___y_5920_);
lean_dec_ref(v___y_5919_);
if (lean_obj_tag(v___x_5933_) == 0)
{
lean_object* v___x_5934_; 
lean_dec_ref(v___x_5933_);
v___x_5934_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__2_spec__3___redArg(v_fst_5924_);
return v___x_5934_;
}
else
{
lean_dec(v_fst_5924_);
return v___x_5933_;
}
}
v_resetjp_5937_:
{
lean_object* v___x_5940_; uint8_t v___x_5941_; lean_object* v___y_5943_; lean_object* v_a_5944_; uint8_t v___y_5968_; double v___y_5999_; 
v___x_5940_ = l_Lean_trace_profiler;
v___x_5941_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2(v_opts_5914_, v___x_5940_);
if (v___x_5941_ == 0)
{
v___y_5968_ = v___x_5941_;
goto v___jp_5967_;
}
else
{
lean_object* v___x_6004_; uint8_t v___x_6005_; 
v___x_6004_ = l_Lean_trace_profiler_useHeartbeats;
v___x_6005_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2(v_opts_5914_, v___x_6004_);
if (v___x_6005_ == 0)
{
lean_object* v___x_6006_; lean_object* v___x_6007_; double v___x_6008_; double v___x_6009_; double v___x_6010_; 
v___x_6006_ = l_Lean_trace_profiler_threshold;
v___x_6007_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__6(v_opts_5914_, v___x_6006_);
v___x_6008_ = lean_float_of_nat(v___x_6007_);
v___x_6009_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__4);
v___x_6010_ = lean_float_div(v___x_6008_, v___x_6009_);
v___y_5999_ = v___x_6010_;
goto v___jp_5998_;
}
else
{
lean_object* v___x_6011_; lean_object* v___x_6012_; double v___x_6013_; 
v___x_6011_ = l_Lean_trace_profiler_threshold;
v___x_6012_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__6(v_opts_5914_, v___x_6011_);
v___x_6013_ = lean_float_of_nat(v___x_6012_);
v___y_5999_ = v___x_6013_;
goto v___jp_5998_;
}
}
v___jp_5942_:
{
uint8_t v_result_5945_; lean_object* v___x_5946_; lean_object* v___x_5947_; lean_object* v___x_5948_; lean_object* v___x_5950_; 
v_result_5945_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2_spec__2(v_fst_5924_);
v___x_5946_ = l_Lean_TraceResult_toEmoji(v_result_5945_);
v___x_5947_ = l_Lean_stringToMessageData(v___x_5946_);
v___x_5948_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__1);
if (v_isShared_5939_ == 0)
{
lean_ctor_set_tag(v___x_5938_, 7);
lean_ctor_set(v___x_5938_, 1, v___x_5948_);
lean_ctor_set(v___x_5938_, 0, v___x_5947_);
v___x_5950_ = v___x_5938_;
goto v_reusejp_5949_;
}
else
{
lean_object* v_reuseFailAlloc_5961_; 
v_reuseFailAlloc_5961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5961_, 0, v___x_5947_);
lean_ctor_set(v_reuseFailAlloc_5961_, 1, v___x_5948_);
v___x_5950_ = v_reuseFailAlloc_5961_;
goto v_reusejp_5949_;
}
v_reusejp_5949_:
{
lean_object* v_m_5952_; 
if (v_isShared_5928_ == 0)
{
lean_ctor_set_tag(v___x_5927_, 7);
lean_ctor_set(v___x_5927_, 1, v_a_5944_);
lean_ctor_set(v___x_5927_, 0, v___x_5950_);
v_m_5952_ = v___x_5927_;
goto v_reusejp_5951_;
}
else
{
lean_object* v_reuseFailAlloc_5960_; 
v_reuseFailAlloc_5960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5960_, 0, v___x_5950_);
lean_ctor_set(v_reuseFailAlloc_5960_, 1, v_a_5944_);
v_m_5952_ = v_reuseFailAlloc_5960_;
goto v_reusejp_5951_;
}
v_reusejp_5951_:
{
lean_object* v___x_5953_; lean_object* v___x_5954_; double v___x_5955_; lean_object* v_data_5956_; 
v___x_5953_ = lean_box(v_result_5945_);
v___x_5954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5954_, 0, v___x_5953_);
v___x_5955_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__0);
lean_inc_ref(v_tag_5913_);
lean_inc_ref(v___x_5954_);
lean_inc(v_cls_5911_);
v_data_5956_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_5956_, 0, v_cls_5911_);
lean_ctor_set(v_data_5956_, 1, v___x_5954_);
lean_ctor_set(v_data_5956_, 2, v_tag_5913_);
lean_ctor_set_float(v_data_5956_, sizeof(void*)*3, v___x_5955_);
lean_ctor_set_float(v_data_5956_, sizeof(void*)*3 + 8, v___x_5955_);
lean_ctor_set_uint8(v_data_5956_, sizeof(void*)*3 + 16, v_collapsed_5912_);
if (v___x_5941_ == 0)
{
lean_dec_ref(v___x_5954_);
lean_dec(v_snd_5936_);
lean_dec(v_fst_5935_);
lean_dec_ref(v_tag_5913_);
lean_dec(v_cls_5911_);
v___y_5930_ = v_m_5952_;
v___y_5931_ = v___y_5943_;
v_data_5932_ = v_data_5956_;
goto v___jp_5929_;
}
else
{
lean_object* v_data_5957_; double v___x_5958_; double v___x_5959_; 
lean_dec_ref(v_data_5956_);
v_data_5957_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_5957_, 0, v_cls_5911_);
lean_ctor_set(v_data_5957_, 1, v___x_5954_);
lean_ctor_set(v_data_5957_, 2, v_tag_5913_);
v___x_5958_ = lean_unbox_float(v_fst_5935_);
lean_dec(v_fst_5935_);
lean_ctor_set_float(v_data_5957_, sizeof(void*)*3, v___x_5958_);
v___x_5959_ = lean_unbox_float(v_snd_5936_);
lean_dec(v_snd_5936_);
lean_ctor_set_float(v_data_5957_, sizeof(void*)*3 + 8, v___x_5959_);
lean_ctor_set_uint8(v_data_5957_, sizeof(void*)*3 + 16, v_collapsed_5912_);
v___y_5930_ = v_m_5952_;
v___y_5931_ = v___y_5943_;
v_data_5932_ = v_data_5957_;
goto v___jp_5929_;
}
}
}
}
v___jp_5962_:
{
lean_object* v_ref_5963_; lean_object* v___x_5964_; 
v_ref_5963_ = lean_ctor_get(v___y_5921_, 5);
lean_inc(v___y_5922_);
lean_inc_ref(v___y_5921_);
lean_inc(v___y_5920_);
lean_inc_ref(v___y_5919_);
lean_inc(v_fst_5924_);
v___x_5964_ = lean_apply_6(v_msg_5917_, v_fst_5924_, v___y_5919_, v___y_5920_, v___y_5921_, v___y_5922_, lean_box(0));
if (lean_obj_tag(v___x_5964_) == 0)
{
lean_object* v_a_5965_; 
v_a_5965_ = lean_ctor_get(v___x_5964_, 0);
lean_inc(v_a_5965_);
lean_dec_ref(v___x_5964_);
lean_inc(v_ref_5963_);
v___y_5943_ = v_ref_5963_;
v_a_5944_ = v_a_5965_;
goto v___jp_5942_;
}
else
{
lean_object* v___x_5966_; 
lean_dec_ref(v___x_5964_);
v___x_5966_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__3);
lean_inc(v_ref_5963_);
v___y_5943_ = v_ref_5963_;
v_a_5944_ = v___x_5966_;
goto v___jp_5942_;
}
}
v___jp_5967_:
{
if (v_clsEnabled_5915_ == 0)
{
if (v___y_5968_ == 0)
{
lean_object* v___x_5969_; lean_object* v_traceState_5970_; lean_object* v_env_5971_; lean_object* v_nextMacroScope_5972_; lean_object* v_ngen_5973_; lean_object* v_auxDeclNGen_5974_; lean_object* v_cache_5975_; lean_object* v_messages_5976_; lean_object* v_infoState_5977_; lean_object* v_snapshotTasks_5978_; lean_object* v___x_5980_; uint8_t v_isShared_5981_; uint8_t v_isSharedCheck_5997_; 
lean_del_object(v___x_5938_);
lean_dec(v_snd_5936_);
lean_dec(v_fst_5935_);
lean_del_object(v___x_5927_);
lean_dec_ref(v___y_5921_);
lean_dec(v___y_5920_);
lean_dec_ref(v___y_5919_);
lean_dec_ref(v_msg_5917_);
lean_dec_ref(v_tag_5913_);
lean_dec(v_cls_5911_);
v___x_5969_ = lean_st_ref_take(v___y_5922_);
v_traceState_5970_ = lean_ctor_get(v___x_5969_, 4);
v_env_5971_ = lean_ctor_get(v___x_5969_, 0);
v_nextMacroScope_5972_ = lean_ctor_get(v___x_5969_, 1);
v_ngen_5973_ = lean_ctor_get(v___x_5969_, 2);
v_auxDeclNGen_5974_ = lean_ctor_get(v___x_5969_, 3);
v_cache_5975_ = lean_ctor_get(v___x_5969_, 5);
v_messages_5976_ = lean_ctor_get(v___x_5969_, 6);
v_infoState_5977_ = lean_ctor_get(v___x_5969_, 7);
v_snapshotTasks_5978_ = lean_ctor_get(v___x_5969_, 8);
v_isSharedCheck_5997_ = !lean_is_exclusive(v___x_5969_);
if (v_isSharedCheck_5997_ == 0)
{
v___x_5980_ = v___x_5969_;
v_isShared_5981_ = v_isSharedCheck_5997_;
goto v_resetjp_5979_;
}
else
{
lean_inc(v_snapshotTasks_5978_);
lean_inc(v_infoState_5977_);
lean_inc(v_messages_5976_);
lean_inc(v_cache_5975_);
lean_inc(v_traceState_5970_);
lean_inc(v_auxDeclNGen_5974_);
lean_inc(v_ngen_5973_);
lean_inc(v_nextMacroScope_5972_);
lean_inc(v_env_5971_);
lean_dec(v___x_5969_);
v___x_5980_ = lean_box(0);
v_isShared_5981_ = v_isSharedCheck_5997_;
goto v_resetjp_5979_;
}
v_resetjp_5979_:
{
uint64_t v_tid_5982_; lean_object* v_traces_5983_; lean_object* v___x_5985_; uint8_t v_isShared_5986_; uint8_t v_isSharedCheck_5996_; 
v_tid_5982_ = lean_ctor_get_uint64(v_traceState_5970_, sizeof(void*)*1);
v_traces_5983_ = lean_ctor_get(v_traceState_5970_, 0);
v_isSharedCheck_5996_ = !lean_is_exclusive(v_traceState_5970_);
if (v_isSharedCheck_5996_ == 0)
{
v___x_5985_ = v_traceState_5970_;
v_isShared_5986_ = v_isSharedCheck_5996_;
goto v_resetjp_5984_;
}
else
{
lean_inc(v_traces_5983_);
lean_dec(v_traceState_5970_);
v___x_5985_ = lean_box(0);
v_isShared_5986_ = v_isSharedCheck_5996_;
goto v_resetjp_5984_;
}
v_resetjp_5984_:
{
lean_object* v___x_5987_; lean_object* v___x_5989_; 
v___x_5987_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_5916_, v_traces_5983_);
lean_dec_ref(v_traces_5983_);
if (v_isShared_5986_ == 0)
{
lean_ctor_set(v___x_5985_, 0, v___x_5987_);
v___x_5989_ = v___x_5985_;
goto v_reusejp_5988_;
}
else
{
lean_object* v_reuseFailAlloc_5995_; 
v_reuseFailAlloc_5995_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5995_, 0, v___x_5987_);
lean_ctor_set_uint64(v_reuseFailAlloc_5995_, sizeof(void*)*1, v_tid_5982_);
v___x_5989_ = v_reuseFailAlloc_5995_;
goto v_reusejp_5988_;
}
v_reusejp_5988_:
{
lean_object* v___x_5991_; 
if (v_isShared_5981_ == 0)
{
lean_ctor_set(v___x_5980_, 4, v___x_5989_);
v___x_5991_ = v___x_5980_;
goto v_reusejp_5990_;
}
else
{
lean_object* v_reuseFailAlloc_5994_; 
v_reuseFailAlloc_5994_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5994_, 0, v_env_5971_);
lean_ctor_set(v_reuseFailAlloc_5994_, 1, v_nextMacroScope_5972_);
lean_ctor_set(v_reuseFailAlloc_5994_, 2, v_ngen_5973_);
lean_ctor_set(v_reuseFailAlloc_5994_, 3, v_auxDeclNGen_5974_);
lean_ctor_set(v_reuseFailAlloc_5994_, 4, v___x_5989_);
lean_ctor_set(v_reuseFailAlloc_5994_, 5, v_cache_5975_);
lean_ctor_set(v_reuseFailAlloc_5994_, 6, v_messages_5976_);
lean_ctor_set(v_reuseFailAlloc_5994_, 7, v_infoState_5977_);
lean_ctor_set(v_reuseFailAlloc_5994_, 8, v_snapshotTasks_5978_);
v___x_5991_ = v_reuseFailAlloc_5994_;
goto v_reusejp_5990_;
}
v_reusejp_5990_:
{
lean_object* v___x_5992_; lean_object* v___x_5993_; 
v___x_5992_ = lean_st_ref_set(v___y_5922_, v___x_5991_);
lean_dec(v___y_5922_);
v___x_5993_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__2_spec__3___redArg(v_fst_5924_);
return v___x_5993_;
}
}
}
}
}
else
{
goto v___jp_5962_;
}
}
else
{
goto v___jp_5962_;
}
}
v___jp_5998_:
{
double v___x_6000_; double v___x_6001_; double v___x_6002_; uint8_t v___x_6003_; 
v___x_6000_ = lean_unbox_float(v_snd_5936_);
v___x_6001_ = lean_unbox_float(v_fst_5935_);
v___x_6002_ = lean_float_sub(v___x_6000_, v___x_6001_);
v___x_6003_ = lean_float_decLt(v___y_5999_, v___x_6002_);
v___y_5968_ = v___x_6003_;
goto v___jp_5967_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2___boxed(lean_object* v_cls_6016_, lean_object* v_collapsed_6017_, lean_object* v_tag_6018_, lean_object* v_opts_6019_, lean_object* v_clsEnabled_6020_, lean_object* v_oldTraces_6021_, lean_object* v_msg_6022_, lean_object* v_resStartStop_6023_, lean_object* v___y_6024_, lean_object* v___y_6025_, lean_object* v___y_6026_, lean_object* v___y_6027_, lean_object* v___y_6028_){
_start:
{
uint8_t v_collapsed_boxed_6029_; uint8_t v_clsEnabled_boxed_6030_; lean_object* v_res_6031_; 
v_collapsed_boxed_6029_ = lean_unbox(v_collapsed_6017_);
v_clsEnabled_boxed_6030_ = lean_unbox(v_clsEnabled_6020_);
v_res_6031_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2(v_cls_6016_, v_collapsed_boxed_6029_, v_tag_6018_, v_opts_6019_, v_clsEnabled_boxed_6030_, v_oldTraces_6021_, v_msg_6022_, v_resStartStop_6023_, v___y_6024_, v___y_6025_, v___y_6026_, v___y_6027_);
lean_dec_ref(v_opts_6019_);
return v_res_6031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal(lean_object* v_m_6033_, lean_object* v_a_6034_, lean_object* v_a_6035_, lean_object* v_a_6036_, lean_object* v_a_6037_){
_start:
{
lean_object* v_options_6039_; uint8_t v_hasTrace_6040_; lean_object* v_cls_6041_; 
v_options_6039_ = lean_ctor_get(v_a_6036_, 2);
v_hasTrace_6040_ = lean_ctor_get_uint8(v_options_6039_, sizeof(void*)*1);
v_cls_6041_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0));
if (v_hasTrace_6040_ == 0)
{
lean_object* v___x_6042_; lean_object* v___x_6043_; lean_object* v___x_6044_; lean_object* v___x_6045_; lean_object* v___f_6046_; lean_object* v___x_6047_; 
v___x_6042_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_6043_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__6(v_options_6039_, v___x_6042_);
v___x_6044_ = lean_unsigned_to_nat(2u);
v___x_6045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6045_, 0, v___x_6043_);
lean_ctor_set(v___x_6045_, 1, v___x_6044_);
v___f_6046_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___boxed), 10, 3);
lean_closure_set(v___f_6046_, 0, v_m_6033_);
lean_closure_set(v___f_6046_, 1, v___x_6045_);
lean_closure_set(v___f_6046_, 2, v_cls_6041_);
v___x_6047_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_6046_, v_a_6034_, v_a_6035_, v_a_6036_, v_a_6037_);
return v___x_6047_;
}
else
{
lean_object* v___x_6048_; lean_object* v_a_6049_; lean_object* v___f_6050_; lean_object* v___x_6051_; lean_object* v___y_6053_; lean_object* v___y_6054_; lean_object* v_a_6055_; lean_object* v___y_6069_; lean_object* v___y_6070_; lean_object* v_a_6071_; uint8_t v___x_6134_; 
v___x_6048_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg(v_cls_6041_, v_a_6036_);
v_a_6049_ = lean_ctor_get(v___x_6048_, 0);
lean_inc(v_a_6049_);
lean_dec_ref(v___x_6048_);
v___f_6050_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___closed__0));
v___x_6051_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__1));
v___x_6134_ = lean_unbox(v_a_6049_);
if (v___x_6134_ == 0)
{
lean_object* v___x_6135_; uint8_t v___x_6136_; 
v___x_6135_ = l_Lean_trace_profiler;
v___x_6136_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2(v_options_6039_, v___x_6135_);
if (v___x_6136_ == 0)
{
lean_object* v___x_6137_; lean_object* v___x_6138_; lean_object* v___x_6139_; lean_object* v___x_6140_; lean_object* v___x_6141_; lean_object* v___f_6142_; lean_object* v___x_6143_; 
lean_dec(v_a_6049_);
v___x_6137_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_6138_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__6(v_options_6039_, v___x_6137_);
v___x_6139_ = lean_unsigned_to_nat(2u);
v___x_6140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6140_, 0, v___x_6138_);
lean_ctor_set(v___x_6140_, 1, v___x_6139_);
v___x_6141_ = lean_box(v_hasTrace_6040_);
v___f_6142_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__4___boxed), 11, 4);
lean_closure_set(v___f_6142_, 0, v_m_6033_);
lean_closure_set(v___f_6142_, 1, v___x_6140_);
lean_closure_set(v___f_6142_, 2, v_cls_6041_);
lean_closure_set(v___f_6142_, 3, v___x_6141_);
v___x_6143_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_6142_, v_a_6034_, v_a_6035_, v_a_6036_, v_a_6037_);
return v___x_6143_;
}
else
{
lean_inc_ref(v_options_6039_);
goto v___jp_6081_;
}
}
else
{
lean_inc_ref(v_options_6039_);
goto v___jp_6081_;
}
v___jp_6052_:
{
lean_object* v___x_6056_; double v___x_6057_; double v___x_6058_; double v___x_6059_; double v___x_6060_; double v___x_6061_; lean_object* v___x_6062_; lean_object* v___x_6063_; lean_object* v___x_6064_; lean_object* v___x_6065_; uint8_t v___x_6066_; lean_object* v___x_6067_; 
v___x_6056_ = lean_io_mono_nanos_now();
v___x_6057_ = lean_float_of_nat(v___y_6053_);
v___x_6058_ = lean_float_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4);
v___x_6059_ = lean_float_div(v___x_6057_, v___x_6058_);
v___x_6060_ = lean_float_of_nat(v___x_6056_);
v___x_6061_ = lean_float_div(v___x_6060_, v___x_6058_);
v___x_6062_ = lean_box_float(v___x_6059_);
v___x_6063_ = lean_box_float(v___x_6061_);
v___x_6064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6064_, 0, v___x_6062_);
lean_ctor_set(v___x_6064_, 1, v___x_6063_);
v___x_6065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6065_, 0, v_a_6055_);
lean_ctor_set(v___x_6065_, 1, v___x_6064_);
v___x_6066_ = lean_unbox(v_a_6049_);
lean_dec(v_a_6049_);
v___x_6067_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2(v_cls_6041_, v_hasTrace_6040_, v___x_6051_, v_options_6039_, v___x_6066_, v___y_6054_, v___f_6050_, v___x_6065_, v_a_6034_, v_a_6035_, v_a_6036_, v_a_6037_);
lean_dec_ref(v_options_6039_);
return v___x_6067_;
}
v___jp_6068_:
{
lean_object* v___x_6072_; double v___x_6073_; double v___x_6074_; lean_object* v___x_6075_; lean_object* v___x_6076_; lean_object* v___x_6077_; lean_object* v___x_6078_; uint8_t v___x_6079_; lean_object* v___x_6080_; 
v___x_6072_ = lean_io_get_num_heartbeats();
v___x_6073_ = lean_float_of_nat(v___y_6069_);
v___x_6074_ = lean_float_of_nat(v___x_6072_);
v___x_6075_ = lean_box_float(v___x_6073_);
v___x_6076_ = lean_box_float(v___x_6074_);
v___x_6077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6077_, 0, v___x_6075_);
lean_ctor_set(v___x_6077_, 1, v___x_6076_);
v___x_6078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6078_, 0, v_a_6071_);
lean_ctor_set(v___x_6078_, 1, v___x_6077_);
v___x_6079_ = lean_unbox(v_a_6049_);
lean_dec(v_a_6049_);
v___x_6080_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2(v_cls_6041_, v_hasTrace_6040_, v___x_6051_, v_options_6039_, v___x_6079_, v___y_6070_, v___f_6050_, v___x_6078_, v_a_6034_, v_a_6035_, v_a_6036_, v_a_6037_);
lean_dec_ref(v_options_6039_);
return v___x_6080_;
}
v___jp_6081_:
{
lean_object* v___x_6082_; lean_object* v_a_6083_; lean_object* v___x_6084_; uint8_t v___x_6085_; 
v___x_6082_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1___redArg(v_a_6037_);
v_a_6083_ = lean_ctor_get(v___x_6082_, 0);
lean_inc(v_a_6083_);
lean_dec_ref(v___x_6082_);
v___x_6084_ = l_Lean_trace_profiler_useHeartbeats;
v___x_6085_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2(v_options_6039_, v___x_6084_);
if (v___x_6085_ == 0)
{
lean_object* v___x_6086_; lean_object* v___x_6087_; lean_object* v___x_6088_; lean_object* v___x_6089_; lean_object* v___x_6090_; lean_object* v___x_6091_; lean_object* v___f_6092_; lean_object* v___x_6093_; 
v___x_6086_ = lean_io_mono_nanos_now();
v___x_6087_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_6088_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__6(v_options_6039_, v___x_6087_);
v___x_6089_ = lean_unsigned_to_nat(2u);
v___x_6090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6090_, 0, v___x_6088_);
lean_ctor_set(v___x_6090_, 1, v___x_6089_);
v___x_6091_ = lean_box(v_hasTrace_6040_);
v___f_6092_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__4___boxed), 11, 4);
lean_closure_set(v___f_6092_, 0, v_m_6033_);
lean_closure_set(v___f_6092_, 1, v___x_6090_);
lean_closure_set(v___f_6092_, 2, v_cls_6041_);
lean_closure_set(v___f_6092_, 3, v___x_6091_);
lean_inc(v_a_6037_);
lean_inc_ref(v_a_6036_);
lean_inc(v_a_6035_);
lean_inc_ref(v_a_6034_);
v___x_6093_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_6092_, v_a_6034_, v_a_6035_, v_a_6036_, v_a_6037_);
if (lean_obj_tag(v___x_6093_) == 0)
{
lean_object* v_a_6094_; lean_object* v___x_6096_; uint8_t v_isShared_6097_; uint8_t v_isSharedCheck_6101_; 
v_a_6094_ = lean_ctor_get(v___x_6093_, 0);
v_isSharedCheck_6101_ = !lean_is_exclusive(v___x_6093_);
if (v_isSharedCheck_6101_ == 0)
{
v___x_6096_ = v___x_6093_;
v_isShared_6097_ = v_isSharedCheck_6101_;
goto v_resetjp_6095_;
}
else
{
lean_inc(v_a_6094_);
lean_dec(v___x_6093_);
v___x_6096_ = lean_box(0);
v_isShared_6097_ = v_isSharedCheck_6101_;
goto v_resetjp_6095_;
}
v_resetjp_6095_:
{
lean_object* v___x_6099_; 
if (v_isShared_6097_ == 0)
{
lean_ctor_set_tag(v___x_6096_, 1);
v___x_6099_ = v___x_6096_;
goto v_reusejp_6098_;
}
else
{
lean_object* v_reuseFailAlloc_6100_; 
v_reuseFailAlloc_6100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6100_, 0, v_a_6094_);
v___x_6099_ = v_reuseFailAlloc_6100_;
goto v_reusejp_6098_;
}
v_reusejp_6098_:
{
v___y_6053_ = v___x_6086_;
v___y_6054_ = v_a_6083_;
v_a_6055_ = v___x_6099_;
goto v___jp_6052_;
}
}
}
else
{
lean_object* v_a_6102_; lean_object* v___x_6104_; uint8_t v_isShared_6105_; uint8_t v_isSharedCheck_6109_; 
v_a_6102_ = lean_ctor_get(v___x_6093_, 0);
v_isSharedCheck_6109_ = !lean_is_exclusive(v___x_6093_);
if (v_isSharedCheck_6109_ == 0)
{
v___x_6104_ = v___x_6093_;
v_isShared_6105_ = v_isSharedCheck_6109_;
goto v_resetjp_6103_;
}
else
{
lean_inc(v_a_6102_);
lean_dec(v___x_6093_);
v___x_6104_ = lean_box(0);
v_isShared_6105_ = v_isSharedCheck_6109_;
goto v_resetjp_6103_;
}
v_resetjp_6103_:
{
lean_object* v___x_6107_; 
if (v_isShared_6105_ == 0)
{
lean_ctor_set_tag(v___x_6104_, 0);
v___x_6107_ = v___x_6104_;
goto v_reusejp_6106_;
}
else
{
lean_object* v_reuseFailAlloc_6108_; 
v_reuseFailAlloc_6108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6108_, 0, v_a_6102_);
v___x_6107_ = v_reuseFailAlloc_6108_;
goto v_reusejp_6106_;
}
v_reusejp_6106_:
{
v___y_6053_ = v___x_6086_;
v___y_6054_ = v_a_6083_;
v_a_6055_ = v___x_6107_;
goto v___jp_6052_;
}
}
}
}
else
{
lean_object* v___x_6110_; lean_object* v___x_6111_; lean_object* v___x_6112_; lean_object* v___x_6113_; lean_object* v___x_6114_; lean_object* v___x_6115_; lean_object* v___f_6116_; lean_object* v___x_6117_; 
v___x_6110_ = lean_io_get_num_heartbeats();
v___x_6111_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_6112_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__6(v_options_6039_, v___x_6111_);
v___x_6113_ = lean_unsigned_to_nat(2u);
v___x_6114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6114_, 0, v___x_6112_);
lean_ctor_set(v___x_6114_, 1, v___x_6113_);
v___x_6115_ = lean_box(v___x_6085_);
v___f_6116_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__6___boxed), 11, 4);
lean_closure_set(v___f_6116_, 0, v_m_6033_);
lean_closure_set(v___f_6116_, 1, v___x_6114_);
lean_closure_set(v___f_6116_, 2, v_cls_6041_);
lean_closure_set(v___f_6116_, 3, v___x_6115_);
lean_inc(v_a_6037_);
lean_inc_ref(v_a_6036_);
lean_inc(v_a_6035_);
lean_inc_ref(v_a_6034_);
v___x_6117_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_6116_, v_a_6034_, v_a_6035_, v_a_6036_, v_a_6037_);
if (lean_obj_tag(v___x_6117_) == 0)
{
lean_object* v_a_6118_; lean_object* v___x_6120_; uint8_t v_isShared_6121_; uint8_t v_isSharedCheck_6125_; 
v_a_6118_ = lean_ctor_get(v___x_6117_, 0);
v_isSharedCheck_6125_ = !lean_is_exclusive(v___x_6117_);
if (v_isSharedCheck_6125_ == 0)
{
v___x_6120_ = v___x_6117_;
v_isShared_6121_ = v_isSharedCheck_6125_;
goto v_resetjp_6119_;
}
else
{
lean_inc(v_a_6118_);
lean_dec(v___x_6117_);
v___x_6120_ = lean_box(0);
v_isShared_6121_ = v_isSharedCheck_6125_;
goto v_resetjp_6119_;
}
v_resetjp_6119_:
{
lean_object* v___x_6123_; 
if (v_isShared_6121_ == 0)
{
lean_ctor_set_tag(v___x_6120_, 1);
v___x_6123_ = v___x_6120_;
goto v_reusejp_6122_;
}
else
{
lean_object* v_reuseFailAlloc_6124_; 
v_reuseFailAlloc_6124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6124_, 0, v_a_6118_);
v___x_6123_ = v_reuseFailAlloc_6124_;
goto v_reusejp_6122_;
}
v_reusejp_6122_:
{
v___y_6069_ = v___x_6110_;
v___y_6070_ = v_a_6083_;
v_a_6071_ = v___x_6123_;
goto v___jp_6068_;
}
}
}
else
{
lean_object* v_a_6126_; lean_object* v___x_6128_; uint8_t v_isShared_6129_; uint8_t v_isSharedCheck_6133_; 
v_a_6126_ = lean_ctor_get(v___x_6117_, 0);
v_isSharedCheck_6133_ = !lean_is_exclusive(v___x_6117_);
if (v_isSharedCheck_6133_ == 0)
{
v___x_6128_ = v___x_6117_;
v_isShared_6129_ = v_isSharedCheck_6133_;
goto v_resetjp_6127_;
}
else
{
lean_inc(v_a_6126_);
lean_dec(v___x_6117_);
v___x_6128_ = lean_box(0);
v_isShared_6129_ = v_isSharedCheck_6133_;
goto v_resetjp_6127_;
}
v_resetjp_6127_:
{
lean_object* v___x_6131_; 
if (v_isShared_6129_ == 0)
{
lean_ctor_set_tag(v___x_6128_, 0);
v___x_6131_ = v___x_6128_;
goto v_reusejp_6130_;
}
else
{
lean_object* v_reuseFailAlloc_6132_; 
v_reuseFailAlloc_6132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6132_, 0, v_a_6126_);
v___x_6131_ = v_reuseFailAlloc_6132_;
goto v_reusejp_6130_;
}
v_reusejp_6130_:
{
v___y_6069_ = v___x_6110_;
v___y_6070_ = v_a_6083_;
v_a_6071_ = v___x_6131_;
goto v___jp_6068_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___boxed(lean_object* v_m_6144_, lean_object* v_a_6145_, lean_object* v_a_6146_, lean_object* v_a_6147_, lean_object* v_a_6148_, lean_object* v_a_6149_){
_start:
{
lean_object* v_res_6150_; 
v_res_6150_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal(v_m_6144_, v_a_6145_, v_a_6146_, v_a_6147_, v_a_6148_);
return v_res_6150_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0(lean_object* v_00_u03b1_6151_, lean_object* v_msg_6152_, lean_object* v___y_6153_, lean_object* v___y_6154_, lean_object* v___y_6155_, lean_object* v___y_6156_, lean_object* v___y_6157_, lean_object* v___y_6158_){
_start:
{
lean_object* v___x_6160_; 
v___x_6160_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v_msg_6152_, v___y_6155_, v___y_6156_, v___y_6157_, v___y_6158_);
return v___x_6160_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___boxed(lean_object* v_00_u03b1_6161_, lean_object* v_msg_6162_, lean_object* v___y_6163_, lean_object* v___y_6164_, lean_object* v___y_6165_, lean_object* v___y_6166_, lean_object* v___y_6167_, lean_object* v___y_6168_, lean_object* v___y_6169_){
_start:
{
lean_object* v_res_6170_; 
v_res_6170_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0(v_00_u03b1_6161_, v_msg_6162_, v___y_6163_, v___y_6164_, v___y_6165_, v___y_6166_, v___y_6167_, v___y_6168_);
lean_dec(v___y_6168_);
lean_dec_ref(v___y_6167_);
lean_dec(v___y_6166_);
lean_dec_ref(v___y_6165_);
lean_dec(v___y_6164_);
lean_dec_ref(v___y_6163_);
return v_res_6170_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1(lean_object* v_cls_6171_, lean_object* v_msg_6172_, lean_object* v___y_6173_, lean_object* v___y_6174_, lean_object* v___y_6175_, lean_object* v___y_6176_, lean_object* v___y_6177_, lean_object* v___y_6178_){
_start:
{
lean_object* v___x_6180_; 
v___x_6180_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(v_cls_6171_, v_msg_6172_, v___y_6175_, v___y_6176_, v___y_6177_, v___y_6178_);
return v___x_6180_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___boxed(lean_object* v_cls_6181_, lean_object* v_msg_6182_, lean_object* v___y_6183_, lean_object* v___y_6184_, lean_object* v___y_6185_, lean_object* v___y_6186_, lean_object* v___y_6187_, lean_object* v___y_6188_, lean_object* v___y_6189_){
_start:
{
lean_object* v_res_6190_; 
v_res_6190_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1(v_cls_6181_, v_msg_6182_, v___y_6183_, v___y_6184_, v___y_6185_, v___y_6186_, v___y_6187_, v___y_6188_);
lean_dec(v___y_6188_);
lean_dec_ref(v___y_6187_);
lean_dec(v___y_6186_);
lean_dec_ref(v___y_6185_);
lean_dec(v___y_6184_);
lean_dec_ref(v___y_6183_);
return v_res_6190_;
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
res = l_Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Main_1281344741____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Tactic_Cbv_cbv_warning = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Tactic_Cbv_cbv_warning);
lean_dec_ref(res);
res = l_Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Main_3491633865____hygCtx___hyg_4_();
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

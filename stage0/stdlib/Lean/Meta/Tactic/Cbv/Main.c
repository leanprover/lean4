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
lean_object* l_Lean_Expr_constName_x21(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConstApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConstApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_isOpaqueConst___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_isOpaqueConst___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_isOpaqueConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_isOpaqueConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConstApp(lean_object* v_e_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_532_ = l_Lean_Expr_getAppFn(v_e_521_);
v___x_533_ = l_Lean_Expr_constName_x21(v___x_532_);
lean_dec_ref(v___x_532_);
v___x_534_ = l_Lean_Meta_Tactic_Cbv_isCbvOpaque___redArg(v___x_533_, v_a_530_);
lean_dec(v___x_533_);
if (lean_obj_tag(v___x_534_) == 0)
{
lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_549_; 
v_a_535_ = lean_ctor_get(v___x_534_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_549_ == 0)
{
v___x_537_ = v___x_534_;
v_isShared_538_ = v_isSharedCheck_549_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_dec(v___x_534_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_549_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
uint8_t v___x_539_; 
v___x_539_ = lean_unbox(v_a_535_);
if (v___x_539_ == 0)
{
lean_object* v___x_540_; 
lean_del_object(v___x_537_);
lean_dec(v_a_535_);
lean_inc(v_a_530_);
lean_inc_ref(v_a_529_);
lean_inc(v_a_528_);
lean_inc_ref(v_a_527_);
lean_inc(v_a_526_);
lean_inc_ref(v_a_525_);
lean_inc(v_a_524_);
lean_inc_ref(v_a_523_);
lean_inc(v_a_522_);
lean_inc_ref(v_e_521_);
v___x_540_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations(v_e_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_);
if (lean_obj_tag(v___x_540_) == 0)
{
lean_object* v_a_541_; 
v_a_541_ = lean_ctor_get(v___x_540_, 0);
lean_inc(v_a_541_);
if (lean_obj_tag(v_a_541_) == 0)
{
uint8_t v_done_542_; 
v_done_542_ = lean_ctor_get_uint8(v_a_541_, 0);
lean_dec_ref(v_a_541_);
if (v_done_542_ == 0)
{
lean_object* v___x_543_; 
lean_dec_ref(v___x_540_);
v___x_543_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold(v_e_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_);
return v___x_543_;
}
else
{
lean_dec(v_a_530_);
lean_dec_ref(v_a_529_);
lean_dec(v_a_528_);
lean_dec_ref(v_a_527_);
lean_dec(v_a_526_);
lean_dec_ref(v_a_525_);
lean_dec(v_a_524_);
lean_dec_ref(v_a_523_);
lean_dec(v_a_522_);
lean_dec_ref(v_e_521_);
return v___x_540_;
}
}
else
{
lean_dec_ref(v_a_541_);
lean_dec(v_a_530_);
lean_dec_ref(v_a_529_);
lean_dec(v_a_528_);
lean_dec_ref(v_a_527_);
lean_dec(v_a_526_);
lean_dec_ref(v_a_525_);
lean_dec(v_a_524_);
lean_dec_ref(v_a_523_);
lean_dec(v_a_522_);
lean_dec_ref(v_e_521_);
return v___x_540_;
}
}
else
{
lean_dec(v_a_530_);
lean_dec_ref(v_a_529_);
lean_dec(v_a_528_);
lean_dec_ref(v_a_527_);
lean_dec(v_a_526_);
lean_dec_ref(v_a_525_);
lean_dec(v_a_524_);
lean_dec_ref(v_a_523_);
lean_dec(v_a_522_);
lean_dec_ref(v_e_521_);
return v___x_540_;
}
}
else
{
lean_object* v___x_544_; uint8_t v___x_545_; lean_object* v___x_547_; 
lean_dec(v_a_530_);
lean_dec_ref(v_a_529_);
lean_dec(v_a_528_);
lean_dec_ref(v_a_527_);
lean_dec(v_a_526_);
lean_dec_ref(v_a_525_);
lean_dec(v_a_524_);
lean_dec_ref(v_a_523_);
lean_dec(v_a_522_);
lean_dec_ref(v_e_521_);
v___x_544_ = lean_alloc_ctor(0, 0, 1);
v___x_545_ = lean_unbox(v_a_535_);
lean_dec(v_a_535_);
lean_ctor_set_uint8(v___x_544_, 0, v___x_545_);
if (v_isShared_538_ == 0)
{
lean_ctor_set(v___x_537_, 0, v___x_544_);
v___x_547_ = v___x_537_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v___x_544_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
}
else
{
lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_557_; 
lean_dec(v_a_530_);
lean_dec_ref(v_a_529_);
lean_dec(v_a_528_);
lean_dec_ref(v_a_527_);
lean_dec(v_a_526_);
lean_dec_ref(v_a_525_);
lean_dec(v_a_524_);
lean_dec_ref(v_a_523_);
lean_dec(v_a_522_);
lean_dec_ref(v_e_521_);
v_a_550_ = lean_ctor_get(v___x_534_, 0);
v_isSharedCheck_557_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_557_ == 0)
{
v___x_552_ = v___x_534_;
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___x_534_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_555_; 
if (v_isShared_553_ == 0)
{
v___x_555_ = v___x_552_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_a_550_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConstApp___boxed(lean_object* v_e_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConstApp(v_e_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_);
return v_res_569_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__4(void){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_579_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3));
v___x_580_ = l_Lean_stringToMessageData(v___x_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg(lean_object* v_e_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_){
_start:
{
lean_object* v_new_588_; lean_object* v___x_589_; 
lean_inc_ref(v_e_581_);
v_new_588_ = l_Lean_Expr_headBeta(v_e_581_);
v___x_589_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_new_588_, v_a_582_);
if (lean_obj_tag(v___x_589_) == 0)
{
lean_object* v_a_590_; lean_object* v___y_592_; lean_object* v___y_593_; lean_object* v___y_594_; lean_object* v___y_595_; lean_object* v___y_596_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v_a_618_; uint8_t v___x_619_; 
v_a_590_ = lean_ctor_get(v___x_589_, 0);
lean_inc(v_a_590_);
lean_dec_ref(v___x_589_);
v___x_616_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2));
v___x_617_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(v___x_616_, v_a_585_);
v_a_618_ = lean_ctor_get(v___x_617_, 0);
lean_inc(v_a_618_);
lean_dec_ref(v___x_617_);
v___x_619_ = lean_unbox(v_a_618_);
lean_dec(v_a_618_);
if (v___x_619_ == 0)
{
lean_dec_ref(v_e_581_);
v___y_592_ = v_a_582_;
v___y_593_ = v_a_583_;
v___y_594_ = v_a_584_;
v___y_595_ = v_a_585_;
v___y_596_ = v_a_586_;
goto v___jp_591_;
}
else
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_620_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__4, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__4_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__4);
v___x_621_ = l_Lean_indentExpr(v_e_581_);
v___x_622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_622_, 0, v___x_620_);
lean_ctor_set(v___x_622_, 1, v___x_621_);
v___x_623_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7);
v___x_624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_624_, 0, v___x_622_);
lean_ctor_set(v___x_624_, 1, v___x_623_);
lean_inc(v_a_590_);
v___x_625_ = l_Lean_indentExpr(v_a_590_);
v___x_626_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_626_, 0, v___x_624_);
lean_ctor_set(v___x_626_, 1, v___x_625_);
v___x_627_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg(v___x_616_, v___x_626_, v_a_583_, v_a_584_, v_a_585_, v_a_586_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_dec_ref(v___x_627_);
v___y_592_ = v_a_582_;
v___y_593_ = v_a_583_;
v___y_594_ = v_a_584_;
v___y_595_ = v_a_585_;
v___y_596_ = v_a_586_;
goto v___jp_591_;
}
else
{
lean_object* v_a_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_635_; 
lean_dec(v_a_590_);
lean_dec(v_a_586_);
lean_dec_ref(v_a_585_);
lean_dec(v_a_584_);
lean_dec_ref(v_a_583_);
v_a_628_ = lean_ctor_get(v___x_627_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_635_ == 0)
{
v___x_630_ = v___x_627_;
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_a_628_);
lean_dec(v___x_627_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_633_; 
if (v_isShared_631_ == 0)
{
v___x_633_ = v___x_630_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_a_628_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
}
v___jp_591_:
{
lean_object* v___x_597_; 
lean_inc(v_a_590_);
v___x_597_ = l_Lean_Meta_Sym_mkEqRefl___redArg(v_a_590_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_607_; 
v_a_598_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_607_ == 0)
{
v___x_600_ = v___x_597_;
v_isShared_601_ = v_isSharedCheck_607_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_597_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_607_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
uint8_t v___x_602_; lean_object* v___x_603_; lean_object* v___x_605_; 
v___x_602_ = 0;
v___x_603_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_603_, 0, v_a_590_);
lean_ctor_set(v___x_603_, 1, v_a_598_);
lean_ctor_set_uint8(v___x_603_, sizeof(void*)*2, v___x_602_);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 0, v___x_603_);
v___x_605_ = v___x_600_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v___x_603_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
else
{
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_615_; 
lean_dec(v_a_590_);
v_a_608_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_615_ == 0)
{
v___x_610_ = v___x_597_;
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v___x_597_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_613_; 
if (v_isShared_611_ == 0)
{
v___x_613_ = v___x_610_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_a_608_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
}
else
{
lean_object* v_a_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_643_; 
lean_dec(v_a_586_);
lean_dec_ref(v_a_585_);
lean_dec(v_a_584_);
lean_dec_ref(v_a_583_);
lean_dec_ref(v_e_581_);
v_a_636_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_643_ == 0)
{
v___x_638_ = v___x_589_;
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_a_636_);
lean_dec(v___x_589_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_641_; 
if (v_isShared_639_ == 0)
{
v___x_641_ = v___x_638_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_a_636_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___boxed(lean_object* v_e_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg(v_e_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
lean_dec(v_a_645_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce(lean_object* v_e_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg(v_e_652_, v_a_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___boxed(lean_object* v_e_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce(v_e_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_);
lean_dec(v_a_669_);
lean_dec_ref(v_a_668_);
lean_dec(v_a_667_);
lean_dec_ref(v_a_666_);
lean_dec(v_a_665_);
return v_res_675_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems___closed__1(void){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_677_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems___closed__0));
v___x_678_ = l_Lean_stringToMessageData(v___x_677_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems(lean_object* v_e_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = l_Lean_Expr_getAppFn(v_e_679_);
v___x_691_ = l_Lean_Expr_constName_x3f(v___x_690_);
lean_dec_ref(v___x_690_);
if (lean_obj_tag(v___x_691_) == 1)
{
lean_object* v_val_692_; lean_object* v___y_694_; lean_object* v___x_736_; 
v_val_692_ = lean_ctor_get(v___x_691_, 0);
lean_inc(v_val_692_);
lean_dec_ref(v___x_691_);
v___x_736_ = l_Lean_Meta_Tactic_Cbv_getCbvEvalLemmas___redArg(v_val_692_, v_a_688_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_object* v_a_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_762_; 
v_a_737_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_762_ == 0)
{
v___x_739_ = v___x_736_;
v_isShared_740_ = v_isSharedCheck_762_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_a_737_);
lean_dec(v___x_736_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_762_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
if (lean_obj_tag(v_a_737_) == 1)
{
lean_object* v_val_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
lean_del_object(v___x_739_);
v_val_741_ = lean_ctor_get(v_a_737_, 0);
lean_inc(v_val_741_);
lean_dec_ref(v_a_737_);
v___x_742_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8));
lean_inc(v_a_688_);
lean_inc_ref(v_a_687_);
lean_inc(v_a_686_);
lean_inc_ref(v_a_685_);
lean_inc_ref(v_e_679_);
v___x_743_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_val_741_, v___x_742_, v_e_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_);
if (lean_obj_tag(v___x_743_) == 0)
{
v___y_694_ = v___x_743_;
goto v___jp_693_;
}
else
{
lean_object* v_a_744_; uint8_t v___y_746_; uint8_t v___x_756_; 
v_a_744_ = lean_ctor_get(v___x_743_, 0);
lean_inc(v_a_744_);
v___x_756_ = l_Lean_Exception_isInterrupt(v_a_744_);
if (v___x_756_ == 0)
{
uint8_t v___x_757_; 
v___x_757_ = l_Lean_Exception_isRuntime(v_a_744_);
v___y_746_ = v___x_757_;
goto v___jp_745_;
}
else
{
lean_dec(v_a_744_);
v___y_746_ = v___x_756_;
goto v___jp_745_;
}
v___jp_745_:
{
if (v___y_746_ == 0)
{
lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_754_; 
lean_dec(v_val_692_);
lean_dec(v_a_688_);
lean_dec_ref(v_a_687_);
lean_dec(v_a_686_);
lean_dec_ref(v_a_685_);
lean_dec_ref(v_e_679_);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_754_ == 0)
{
lean_object* v_unused_755_; 
v_unused_755_ = lean_ctor_get(v___x_743_, 0);
lean_dec(v_unused_755_);
v___x_748_ = v___x_743_;
v_isShared_749_ = v_isSharedCheck_754_;
goto v_resetjp_747_;
}
else
{
lean_dec(v___x_743_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_754_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_750_; lean_object* v___x_752_; 
v___x_750_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_750_, 0, v___y_746_);
if (v_isShared_749_ == 0)
{
lean_ctor_set_tag(v___x_748_, 0);
lean_ctor_set(v___x_748_, 0, v___x_750_);
v___x_752_ = v___x_748_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_750_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
else
{
v___y_694_ = v___x_743_;
goto v___jp_693_;
}
}
}
}
else
{
lean_object* v___x_758_; lean_object* v___x_760_; 
lean_dec(v_a_737_);
lean_dec(v_val_692_);
lean_dec(v_a_688_);
lean_dec_ref(v_a_687_);
lean_dec(v_a_686_);
lean_dec_ref(v_a_685_);
lean_dec(v_a_684_);
lean_dec_ref(v_a_683_);
lean_dec(v_a_682_);
lean_dec_ref(v_a_681_);
lean_dec(v_a_680_);
lean_dec_ref(v_e_679_);
v___x_758_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__9));
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 0, v___x_758_);
v___x_760_ = v___x_739_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_758_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
}
else
{
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_770_; 
lean_dec(v_val_692_);
lean_dec(v_a_688_);
lean_dec_ref(v_a_687_);
lean_dec(v_a_686_);
lean_dec_ref(v_a_685_);
lean_dec(v_a_684_);
lean_dec_ref(v_a_683_);
lean_dec(v_a_682_);
lean_dec_ref(v_a_681_);
lean_dec(v_a_680_);
lean_dec_ref(v_e_679_);
v_a_763_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_770_ == 0)
{
v___x_765_ = v___x_736_;
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_736_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_768_; 
if (v_isShared_766_ == 0)
{
v___x_768_ = v___x_765_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_a_763_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
v___jp_693_:
{
if (lean_obj_tag(v___y_694_) == 0)
{
lean_object* v_a_695_; 
v_a_695_ = lean_ctor_get(v___y_694_, 0);
if (lean_obj_tag(v_a_695_) == 1)
{
lean_object* v_e_x27_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v_a_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_735_; 
lean_inc_ref(v_a_695_);
lean_dec_ref(v___y_694_);
v_e_x27_696_ = lean_ctor_get(v_a_695_, 0);
v___x_697_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__1));
v___x_698_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(v___x_697_, v_a_687_);
v_a_699_ = lean_ctor_get(v___x_698_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_735_ == 0)
{
v___x_701_ = v___x_698_;
v_isShared_702_ = v_isSharedCheck_735_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_a_699_);
lean_dec(v___x_698_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_735_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
uint8_t v___x_703_; 
v___x_703_ = lean_unbox(v_a_699_);
lean_dec(v_a_699_);
if (v___x_703_ == 0)
{
lean_object* v___x_705_; 
lean_dec(v_val_692_);
lean_dec(v_a_688_);
lean_dec_ref(v_a_687_);
lean_dec(v_a_686_);
lean_dec_ref(v_a_685_);
lean_dec_ref(v_e_679_);
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 0, v_a_695_);
v___x_705_ = v___x_701_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_a_695_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
else
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
lean_del_object(v___x_701_);
v___x_707_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems___closed__1, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems___closed__1);
v___x_708_ = l_Lean_MessageData_ofName(v_val_692_);
v___x_709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_709_, 0, v___x_707_);
lean_ctor_set(v___x_709_, 1, v___x_708_);
v___x_710_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__5, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__5_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__5);
v___x_711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_711_, 0, v___x_709_);
lean_ctor_set(v___x_711_, 1, v___x_710_);
v___x_712_ = l_Lean_indentExpr(v_e_679_);
v___x_713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_713_, 0, v___x_711_);
lean_ctor_set(v___x_713_, 1, v___x_712_);
v___x_714_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7);
v___x_715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_715_, 0, v___x_713_);
lean_ctor_set(v___x_715_, 1, v___x_714_);
lean_inc_ref(v_e_x27_696_);
v___x_716_ = l_Lean_indentExpr(v_e_x27_696_);
v___x_717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_717_, 0, v___x_715_);
lean_ctor_set(v___x_717_, 1, v___x_716_);
v___x_718_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg(v___x_697_, v___x_717_, v_a_685_, v_a_686_, v_a_687_, v_a_688_);
lean_dec(v_a_688_);
lean_dec_ref(v_a_687_);
lean_dec(v_a_686_);
lean_dec_ref(v_a_685_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_725_; 
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_725_ == 0)
{
lean_object* v_unused_726_; 
v_unused_726_ = lean_ctor_get(v___x_718_, 0);
lean_dec(v_unused_726_);
v___x_720_ = v___x_718_;
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
else
{
lean_dec(v___x_718_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_723_; 
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 0, v_a_695_);
v___x_723_ = v___x_720_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_a_695_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
else
{
lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_734_; 
lean_dec_ref(v_a_695_);
v_a_727_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_734_ == 0)
{
v___x_729_ = v___x_718_;
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v___x_718_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_732_; 
if (v_isShared_730_ == 0)
{
v___x_732_ = v___x_729_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_a_727_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
}
}
}
else
{
lean_dec(v_val_692_);
lean_dec(v_a_688_);
lean_dec_ref(v_a_687_);
lean_dec(v_a_686_);
lean_dec_ref(v_a_685_);
lean_dec_ref(v_e_679_);
return v___y_694_;
}
}
else
{
lean_dec(v_val_692_);
lean_dec(v_a_688_);
lean_dec_ref(v_a_687_);
lean_dec(v_a_686_);
lean_dec_ref(v_a_685_);
lean_dec_ref(v_e_679_);
return v___y_694_;
}
}
}
else
{
lean_object* v___x_771_; lean_object* v___x_772_; 
lean_dec(v___x_691_);
lean_dec(v_a_688_);
lean_dec_ref(v_a_687_);
lean_dec(v_a_686_);
lean_dec_ref(v_a_685_);
lean_dec(v_a_684_);
lean_dec_ref(v_a_683_);
lean_dec(v_a_682_);
lean_dec_ref(v_a_681_);
lean_dec(v_a_680_);
lean_dec_ref(v_e_679_);
v___x_771_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__9));
v___x_772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_772_, 0, v___x_771_);
return v___x_772_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems___boxed(lean_object* v_e_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems(v_e_773_, v_a_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_, v_a_781_, v_a_782_);
return v_res_784_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp___lam__0(lean_object* v_a_785_, uint8_t v_done_786_, lean_object* v_x_787_){
_start:
{
uint8_t v___x_788_; 
v___x_788_ = l_Lean_ConstantInfo_hasValue(v_a_785_, v_done_786_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp___lam__0___boxed(lean_object* v_a_789_, lean_object* v_done_790_, lean_object* v_x_791_){
_start:
{
uint8_t v_done_15678__boxed_792_; uint8_t v_res_793_; lean_object* v_r_794_; 
v_done_15678__boxed_792_ = lean_unbox(v_done_790_);
v_res_793_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp___lam__0(v_a_789_, v_done_15678__boxed_792_, v_x_791_);
lean_dec_ref(v_x_791_);
lean_dec_ref(v_a_789_);
v_r_794_ = lean_box(v_res_793_);
return v_r_794_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_795_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_796_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_797_, 0, v___x_796_);
return v___x_797_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_798_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_799_ = lean_unsigned_to_nat(0u);
v___x_800_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_800_, 0, v___x_799_);
lean_ctor_set(v___x_800_, 1, v___x_799_);
lean_ctor_set(v___x_800_, 2, v___x_799_);
lean_ctor_set(v___x_800_, 3, v___x_798_);
lean_ctor_set(v___x_800_, 4, v___x_798_);
lean_ctor_set(v___x_800_, 5, v___x_798_);
lean_ctor_set(v___x_800_, 6, v___x_798_);
lean_ctor_set(v___x_800_, 7, v___x_798_);
lean_ctor_set(v___x_800_, 8, v___x_798_);
return v___x_800_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_801_ = lean_unsigned_to_nat(32u);
v___x_802_ = lean_mk_empty_array_with_capacity(v___x_801_);
v___x_803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_803_, 0, v___x_802_);
return v___x_803_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_804_ = ((size_t)5ULL);
v___x_805_ = lean_unsigned_to_nat(0u);
v___x_806_ = lean_unsigned_to_nat(32u);
v___x_807_ = lean_mk_empty_array_with_capacity(v___x_806_);
v___x_808_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_809_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_809_, 0, v___x_808_);
lean_ctor_set(v___x_809_, 1, v___x_807_);
lean_ctor_set(v___x_809_, 2, v___x_805_);
lean_ctor_set(v___x_809_, 3, v___x_805_);
lean_ctor_set_usize(v___x_809_, 4, v___x_804_);
return v___x_809_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_810_ = lean_box(1);
v___x_811_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_812_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_813_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_813_, 0, v___x_812_);
lean_ctor_set(v___x_813_, 1, v___x_811_);
lean_ctor_set(v___x_813_, 2, v___x_810_);
return v___x_813_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_815_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6));
v___x_816_ = l_Lean_stringToMessageData(v___x_815_);
return v___x_816_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_818_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8));
v___x_819_ = l_Lean_stringToMessageData(v___x_818_);
return v___x_819_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_821_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10));
v___x_822_ = l_Lean_stringToMessageData(v___x_821_);
return v___x_822_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_824_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12));
v___x_825_ = l_Lean_stringToMessageData(v___x_824_);
return v___x_825_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15(void){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_827_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14));
v___x_828_ = l_Lean_stringToMessageData(v___x_827_);
return v___x_828_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17(void){
_start:
{
lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_830_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16));
v___x_831_ = l_Lean_stringToMessageData(v___x_830_);
return v___x_831_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19(void){
_start:
{
lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_833_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18));
v___x_834_ = l_Lean_stringToMessageData(v___x_833_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_msg_835_, lean_object* v_declHint_836_, lean_object* v___y_837_){
_start:
{
lean_object* v___x_839_; lean_object* v_env_840_; uint8_t v___x_841_; 
v___x_839_ = lean_st_ref_get(v___y_837_);
v_env_840_ = lean_ctor_get(v___x_839_, 0);
lean_inc_ref(v_env_840_);
lean_dec(v___x_839_);
v___x_841_ = l_Lean_Name_isAnonymous(v_declHint_836_);
if (v___x_841_ == 0)
{
uint8_t v_isExporting_842_; 
v_isExporting_842_ = lean_ctor_get_uint8(v_env_840_, sizeof(void*)*8);
if (v_isExporting_842_ == 0)
{
lean_object* v___x_843_; 
lean_dec_ref(v_env_840_);
lean_dec(v_declHint_836_);
v___x_843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_843_, 0, v_msg_835_);
return v___x_843_;
}
else
{
lean_object* v___x_844_; uint8_t v___x_845_; 
lean_inc_ref(v_env_840_);
v___x_844_ = l_Lean_Environment_setExporting(v_env_840_, v___x_841_);
lean_inc(v_declHint_836_);
lean_inc_ref(v___x_844_);
v___x_845_ = l_Lean_Environment_contains(v___x_844_, v_declHint_836_, v_isExporting_842_);
if (v___x_845_ == 0)
{
lean_object* v___x_846_; 
lean_dec_ref(v___x_844_);
lean_dec_ref(v_env_840_);
lean_dec(v_declHint_836_);
v___x_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_846_, 0, v_msg_835_);
return v___x_846_;
}
else
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v_c_852_; lean_object* v___x_853_; 
v___x_847_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_848_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_849_ = l_Lean_Options_empty;
v___x_850_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_850_, 0, v___x_844_);
lean_ctor_set(v___x_850_, 1, v___x_847_);
lean_ctor_set(v___x_850_, 2, v___x_848_);
lean_ctor_set(v___x_850_, 3, v___x_849_);
lean_inc(v_declHint_836_);
v___x_851_ = l_Lean_MessageData_ofConstName(v_declHint_836_, v___x_841_);
v_c_852_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_852_, 0, v___x_850_);
lean_ctor_set(v_c_852_, 1, v___x_851_);
v___x_853_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_840_, v_declHint_836_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
lean_dec_ref(v_env_840_);
lean_dec(v_declHint_836_);
v___x_854_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_855_, 0, v___x_854_);
lean_ctor_set(v___x_855_, 1, v_c_852_);
v___x_856_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_857_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_857_, 0, v___x_855_);
lean_ctor_set(v___x_857_, 1, v___x_856_);
v___x_858_ = l_Lean_MessageData_note(v___x_857_);
v___x_859_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_859_, 0, v_msg_835_);
lean_ctor_set(v___x_859_, 1, v___x_858_);
v___x_860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_860_, 0, v___x_859_);
return v___x_860_;
}
else
{
lean_object* v_val_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_896_; 
v_val_861_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_896_ == 0)
{
v___x_863_ = v___x_853_;
v_isShared_864_ = v_isSharedCheck_896_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_val_861_);
lean_dec(v___x_853_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_896_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v_mod_868_; uint8_t v___x_869_; 
v___x_865_ = lean_box(0);
v___x_866_ = l_Lean_Environment_header(v_env_840_);
lean_dec_ref(v_env_840_);
v___x_867_ = l_Lean_EnvironmentHeader_moduleNames(v___x_866_);
v_mod_868_ = lean_array_get(v___x_865_, v___x_867_, v_val_861_);
lean_dec(v_val_861_);
lean_dec_ref(v___x_867_);
v___x_869_ = l_Lean_isPrivateName(v_declHint_836_);
lean_dec(v_declHint_836_);
if (v___x_869_ == 0)
{
lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_881_; 
v___x_870_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_871_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_871_, 0, v___x_870_);
lean_ctor_set(v___x_871_, 1, v_c_852_);
v___x_872_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_871_);
lean_ctor_set(v___x_873_, 1, v___x_872_);
v___x_874_ = l_Lean_MessageData_ofName(v_mod_868_);
v___x_875_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_875_, 0, v___x_873_);
lean_ctor_set(v___x_875_, 1, v___x_874_);
v___x_876_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_877_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_877_, 0, v___x_875_);
lean_ctor_set(v___x_877_, 1, v___x_876_);
v___x_878_ = l_Lean_MessageData_note(v___x_877_);
v___x_879_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_879_, 0, v_msg_835_);
lean_ctor_set(v___x_879_, 1, v___x_878_);
if (v_isShared_864_ == 0)
{
lean_ctor_set_tag(v___x_863_, 0);
lean_ctor_set(v___x_863_, 0, v___x_879_);
v___x_881_ = v___x_863_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v___x_879_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
else
{
lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_894_; 
v___x_883_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_884_, 0, v___x_883_);
lean_ctor_set(v___x_884_, 1, v_c_852_);
v___x_885_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_886_, 0, v___x_884_);
lean_ctor_set(v___x_886_, 1, v___x_885_);
v___x_887_ = l_Lean_MessageData_ofName(v_mod_868_);
v___x_888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_886_);
lean_ctor_set(v___x_888_, 1, v___x_887_);
v___x_889_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
v___x_890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_890_, 0, v___x_888_);
lean_ctor_set(v___x_890_, 1, v___x_889_);
v___x_891_ = l_Lean_MessageData_note(v___x_890_);
v___x_892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_892_, 0, v_msg_835_);
lean_ctor_set(v___x_892_, 1, v___x_891_);
if (v_isShared_864_ == 0)
{
lean_ctor_set_tag(v___x_863_, 0);
lean_ctor_set(v___x_863_, 0, v___x_892_);
v___x_894_ = v___x_863_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 1, 0);
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
}
}
}
else
{
lean_object* v___x_897_; 
lean_dec_ref(v_env_840_);
lean_dec(v_declHint_836_);
v___x_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_897_, 0, v_msg_835_);
return v___x_897_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msg_898_, lean_object* v_declHint_899_, lean_object* v___y_900_, lean_object* v___y_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_898_, v_declHint_899_, v___y_900_);
lean_dec(v___y_900_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_msg_903_, lean_object* v_declHint_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_){
_start:
{
lean_object* v___x_915_; lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_925_; 
v___x_915_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_903_, v_declHint_904_, v___y_913_);
v_a_916_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_925_ == 0)
{
v___x_918_ = v___x_915_;
v_isShared_919_ = v_isSharedCheck_925_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_915_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_925_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_923_; 
v___x_920_ = l_Lean_unknownIdentifierMessageTag;
v___x_921_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_921_, 0, v___x_920_);
lean_ctor_set(v___x_921_, 1, v_a_916_);
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 0, v___x_921_);
v___x_923_ = v___x_918_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_921_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_msg_926_, lean_object* v_declHint_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_926_, v_declHint_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
lean_dec(v___y_928_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_msg_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
lean_object* v_ref_945_; lean_object* v___x_946_; lean_object* v_a_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_955_; 
v_ref_945_ = lean_ctor_get(v___y_942_, 5);
v___x_946_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1_spec__1(v_msg_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_);
v_a_947_ = lean_ctor_get(v___x_946_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_955_ == 0)
{
v___x_949_ = v___x_946_;
v_isShared_950_ = v_isSharedCheck_955_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_a_947_);
lean_dec(v___x_946_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_955_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_951_; lean_object* v___x_953_; 
lean_inc(v_ref_945_);
v___x_951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_951_, 0, v_ref_945_);
lean_ctor_set(v___x_951_, 1, v_a_947_);
if (v_isShared_950_ == 0)
{
lean_ctor_set_tag(v___x_949_, 1);
lean_ctor_set(v___x_949_, 0, v___x_951_);
v___x_953_ = v___x_949_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v___x_951_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_msg_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_963_, lean_object* v_msg_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
lean_object* v_fileName_975_; lean_object* v_fileMap_976_; lean_object* v_options_977_; lean_object* v_currRecDepth_978_; lean_object* v_maxRecDepth_979_; lean_object* v_ref_980_; lean_object* v_currNamespace_981_; lean_object* v_openDecls_982_; lean_object* v_initHeartbeats_983_; lean_object* v_maxHeartbeats_984_; lean_object* v_quotContext_985_; lean_object* v_currMacroScope_986_; uint8_t v_diag_987_; lean_object* v_cancelTk_x3f_988_; uint8_t v_suppressElabErrors_989_; lean_object* v_inheritedTraceOptions_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_999_; 
v_fileName_975_ = lean_ctor_get(v___y_972_, 0);
v_fileMap_976_ = lean_ctor_get(v___y_972_, 1);
v_options_977_ = lean_ctor_get(v___y_972_, 2);
v_currRecDepth_978_ = lean_ctor_get(v___y_972_, 3);
v_maxRecDepth_979_ = lean_ctor_get(v___y_972_, 4);
v_ref_980_ = lean_ctor_get(v___y_972_, 5);
v_currNamespace_981_ = lean_ctor_get(v___y_972_, 6);
v_openDecls_982_ = lean_ctor_get(v___y_972_, 7);
v_initHeartbeats_983_ = lean_ctor_get(v___y_972_, 8);
v_maxHeartbeats_984_ = lean_ctor_get(v___y_972_, 9);
v_quotContext_985_ = lean_ctor_get(v___y_972_, 10);
v_currMacroScope_986_ = lean_ctor_get(v___y_972_, 11);
v_diag_987_ = lean_ctor_get_uint8(v___y_972_, sizeof(void*)*14);
v_cancelTk_x3f_988_ = lean_ctor_get(v___y_972_, 12);
v_suppressElabErrors_989_ = lean_ctor_get_uint8(v___y_972_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_990_ = lean_ctor_get(v___y_972_, 13);
v_isSharedCheck_999_ = !lean_is_exclusive(v___y_972_);
if (v_isSharedCheck_999_ == 0)
{
v___x_992_ = v___y_972_;
v_isShared_993_ = v_isSharedCheck_999_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_inheritedTraceOptions_990_);
lean_inc(v_cancelTk_x3f_988_);
lean_inc(v_currMacroScope_986_);
lean_inc(v_quotContext_985_);
lean_inc(v_maxHeartbeats_984_);
lean_inc(v_initHeartbeats_983_);
lean_inc(v_openDecls_982_);
lean_inc(v_currNamespace_981_);
lean_inc(v_ref_980_);
lean_inc(v_maxRecDepth_979_);
lean_inc(v_currRecDepth_978_);
lean_inc(v_options_977_);
lean_inc(v_fileMap_976_);
lean_inc(v_fileName_975_);
lean_dec(v___y_972_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_999_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v_ref_994_; lean_object* v___x_996_; 
v_ref_994_ = l_Lean_replaceRef(v_ref_963_, v_ref_980_);
lean_dec(v_ref_980_);
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 5, v_ref_994_);
v___x_996_ = v___x_992_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_fileName_975_);
lean_ctor_set(v_reuseFailAlloc_998_, 1, v_fileMap_976_);
lean_ctor_set(v_reuseFailAlloc_998_, 2, v_options_977_);
lean_ctor_set(v_reuseFailAlloc_998_, 3, v_currRecDepth_978_);
lean_ctor_set(v_reuseFailAlloc_998_, 4, v_maxRecDepth_979_);
lean_ctor_set(v_reuseFailAlloc_998_, 5, v_ref_994_);
lean_ctor_set(v_reuseFailAlloc_998_, 6, v_currNamespace_981_);
lean_ctor_set(v_reuseFailAlloc_998_, 7, v_openDecls_982_);
lean_ctor_set(v_reuseFailAlloc_998_, 8, v_initHeartbeats_983_);
lean_ctor_set(v_reuseFailAlloc_998_, 9, v_maxHeartbeats_984_);
lean_ctor_set(v_reuseFailAlloc_998_, 10, v_quotContext_985_);
lean_ctor_set(v_reuseFailAlloc_998_, 11, v_currMacroScope_986_);
lean_ctor_set(v_reuseFailAlloc_998_, 12, v_cancelTk_x3f_988_);
lean_ctor_set(v_reuseFailAlloc_998_, 13, v_inheritedTraceOptions_990_);
lean_ctor_set_uint8(v_reuseFailAlloc_998_, sizeof(void*)*14, v_diag_987_);
lean_ctor_set_uint8(v_reuseFailAlloc_998_, sizeof(void*)*14 + 1, v_suppressElabErrors_989_);
v___x_996_ = v_reuseFailAlloc_998_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
lean_object* v___x_997_; 
v___x_997_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_964_, v___y_970_, v___y_971_, v___x_996_, v___y_973_);
lean_dec_ref(v___x_996_);
return v___x_997_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_1000_, lean_object* v_msg_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1000_, v_msg_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
lean_dec(v___y_1010_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
lean_dec(v___y_1004_);
lean_dec_ref(v___y_1003_);
lean_dec(v___y_1002_);
lean_dec(v_ref_1000_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_1013_, lean_object* v_msg_1014_, lean_object* v_declHint_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v___x_1026_; lean_object* v_a_1027_; lean_object* v___x_1028_; 
v___x_1026_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1014_, v_declHint_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_);
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
lean_inc(v_a_1027_);
lean_dec_ref(v___x_1026_);
v___x_1028_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1013_, v_a_1027_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_1029_, lean_object* v_msg_1030_, lean_object* v_declHint_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1029_, v_msg_1030_, v_declHint_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_);
lean_dec(v___y_1040_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec(v_ref_1029_);
return v_res_1042_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1044_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_1045_ = l_Lean_stringToMessageData(v___x_1044_);
return v___x_1045_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_1048_ = l_Lean_stringToMessageData(v___x_1047_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_1049_, lean_object* v_constName_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_){
_start:
{
lean_object* v___x_1061_; uint8_t v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1061_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_1062_ = 0;
lean_inc(v_constName_1050_);
v___x_1063_ = l_Lean_MessageData_ofConstName(v_constName_1050_, v___x_1062_);
v___x_1064_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1061_);
lean_ctor_set(v___x_1064_, 1, v___x_1063_);
v___x_1065_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_1066_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1064_);
lean_ctor_set(v___x_1066_, 1, v___x_1065_);
v___x_1067_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1049_, v___x_1066_, v_constName_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1068_, lean_object* v_constName_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg(v_ref_1068_, v_constName_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
lean_dec(v___y_1078_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v___y_1070_);
lean_dec(v_ref_1068_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0___redArg(lean_object* v_constName_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
lean_object* v_ref_1092_; lean_object* v___x_1093_; 
v_ref_1092_ = lean_ctor_get(v___y_1089_, 5);
lean_inc(v_ref_1092_);
v___x_1093_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg(v_ref_1092_, v_constName_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
lean_dec(v_ref_1092_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0___redArg(v_constName_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_);
lean_dec(v___y_1103_);
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1100_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0(lean_object* v_constName_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_){
_start:
{
lean_object* v___x_1117_; lean_object* v_env_1118_; uint8_t v___x_1119_; lean_object* v___x_1120_; 
v___x_1117_ = lean_st_ref_get(v___y_1115_);
v_env_1118_ = lean_ctor_get(v___x_1117_, 0);
lean_inc_ref(v_env_1118_);
lean_dec(v___x_1117_);
v___x_1119_ = 0;
lean_inc(v_constName_1106_);
v___x_1120_ = l_Lean_Environment_find_x3f(v_env_1118_, v_constName_1106_, v___x_1119_);
if (lean_obj_tag(v___x_1120_) == 0)
{
lean_object* v___x_1121_; 
v___x_1121_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0___redArg(v_constName_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
return v___x_1121_;
}
else
{
lean_object* v_val_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1129_; 
lean_dec_ref(v___y_1114_);
lean_dec(v_constName_1106_);
v_val_1122_ = lean_ctor_get(v___x_1120_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1120_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1124_ = v___x_1120_;
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_val_1122_);
lean_dec(v___x_1120_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1127_; 
if (v_isShared_1125_ == 0)
{
lean_ctor_set_tag(v___x_1124_, 0);
v___x_1127_ = v___x_1124_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_val_1122_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0___boxed(lean_object* v_constName_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0(v_constName_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
lean_dec(v___y_1139_);
lean_dec(v___y_1137_);
lean_dec_ref(v___y_1136_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v___y_1131_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp(lean_object* v_e_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_){
_start:
{
uint8_t v___x_1153_; 
v___x_1153_ = l_Lean_Expr_isApp(v_e_1142_);
if (v___x_1153_ == 0)
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
lean_dec(v_a_1151_);
lean_dec_ref(v_a_1150_);
lean_dec(v_a_1149_);
lean_dec_ref(v_a_1148_);
lean_dec(v_a_1147_);
lean_dec_ref(v_a_1146_);
lean_dec(v_a_1145_);
lean_dec_ref(v_a_1144_);
lean_dec(v_a_1143_);
lean_dec_ref(v_e_1142_);
v___x_1154_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_1154_, 0, v___x_1153_);
v___x_1155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1154_);
return v___x_1155_;
}
else
{
lean_object* v_fn_1156_; 
v_fn_1156_ = l_Lean_Expr_getAppFn(v_e_1142_);
switch(lean_obj_tag(v_fn_1156_))
{
case 4:
{
lean_object* v_declName_1157_; lean_object* v___x_1158_; 
v_declName_1157_ = lean_ctor_get(v_fn_1156_, 0);
lean_inc(v_declName_1157_);
lean_dec_ref(v_fn_1156_);
v___x_1158_ = l_Lean_Meta_Tactic_Cbv_isCbvOpaque___redArg(v_declName_1157_, v_a_1151_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1189_; 
v_a_1159_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1161_ = v___x_1158_;
v_isShared_1162_ = v_isSharedCheck_1189_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_dec(v___x_1158_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1189_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
uint8_t v___x_1163_; 
v___x_1163_ = lean_unbox(v_a_1159_);
if (v___x_1163_ == 0)
{
lean_object* v___x_1164_; 
lean_del_object(v___x_1161_);
lean_dec(v_a_1159_);
lean_inc_ref(v_a_1150_);
v___x_1164_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0(v_declName_1157_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_);
if (lean_obj_tag(v___x_1164_) == 0)
{
lean_object* v_a_1165_; lean_object* v___x_1166_; 
v_a_1165_ = lean_ctor_get(v___x_1164_, 0);
lean_inc(v_a_1165_);
lean_dec_ref(v___x_1164_);
lean_inc(v_a_1151_);
lean_inc_ref(v_a_1150_);
lean_inc(v_a_1149_);
lean_inc_ref(v_a_1148_);
lean_inc(v_a_1147_);
lean_inc_ref(v_a_1146_);
lean_inc(v_a_1145_);
lean_inc_ref(v_a_1144_);
lean_inc(v_a_1143_);
lean_inc_ref(v_e_1142_);
v___x_1166_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems(v_e_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_);
if (lean_obj_tag(v___x_1166_) == 0)
{
lean_object* v_a_1167_; 
v_a_1167_ = lean_ctor_get(v___x_1166_, 0);
lean_inc(v_a_1167_);
if (lean_obj_tag(v_a_1167_) == 0)
{
uint8_t v_done_1168_; 
v_done_1168_ = lean_ctor_get_uint8(v_a_1167_, 0);
lean_dec_ref(v_a_1167_);
if (v_done_1168_ == 0)
{
lean_object* v___x_1169_; lean_object* v___f_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
lean_dec_ref(v___x_1166_);
v___x_1169_ = lean_box(v_done_1168_);
v___f_1170_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1170_, 0, v_a_1165_);
lean_closure_set(v___f_1170_, 1, v___x_1169_);
v___x_1171_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConstApp___boxed), 11, 0);
lean_inc(v_a_1151_);
lean_inc_ref(v_a_1150_);
lean_inc(v_a_1149_);
lean_inc_ref(v_a_1148_);
lean_inc(v_a_1147_);
lean_inc_ref(v_a_1146_);
lean_inc(v_a_1145_);
lean_inc_ref(v_a_1144_);
lean_inc(v_a_1143_);
lean_inc_ref(v_e_1142_);
v___x_1172_ = l_Lean_Meta_Tactic_Cbv_guardSimproc(v___f_1170_, v___x_1171_, v_e_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_);
if (lean_obj_tag(v___x_1172_) == 0)
{
lean_object* v_a_1173_; 
v_a_1173_ = lean_ctor_get(v___x_1172_, 0);
lean_inc(v_a_1173_);
if (lean_obj_tag(v_a_1173_) == 0)
{
uint8_t v_done_1174_; 
v_done_1174_ = lean_ctor_get_uint8(v_a_1173_, 0);
lean_dec_ref(v_a_1173_);
if (v_done_1174_ == 0)
{
lean_object* v___x_1175_; 
lean_dec_ref(v___x_1172_);
v___x_1175_ = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher(v_e_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_);
lean_dec(v_a_1147_);
lean_dec_ref(v_a_1146_);
lean_dec(v_a_1145_);
lean_dec_ref(v_a_1144_);
lean_dec(v_a_1143_);
return v___x_1175_;
}
else
{
lean_dec(v_a_1151_);
lean_dec_ref(v_a_1150_);
lean_dec(v_a_1149_);
lean_dec_ref(v_a_1148_);
lean_dec(v_a_1147_);
lean_dec_ref(v_a_1146_);
lean_dec(v_a_1145_);
lean_dec_ref(v_a_1144_);
lean_dec(v_a_1143_);
lean_dec_ref(v_e_1142_);
return v___x_1172_;
}
}
else
{
lean_dec_ref(v_a_1173_);
lean_dec(v_a_1151_);
lean_dec_ref(v_a_1150_);
lean_dec(v_a_1149_);
lean_dec_ref(v_a_1148_);
lean_dec(v_a_1147_);
lean_dec_ref(v_a_1146_);
lean_dec(v_a_1145_);
lean_dec_ref(v_a_1144_);
lean_dec(v_a_1143_);
lean_dec_ref(v_e_1142_);
return v___x_1172_;
}
}
else
{
lean_dec(v_a_1151_);
lean_dec_ref(v_a_1150_);
lean_dec(v_a_1149_);
lean_dec_ref(v_a_1148_);
lean_dec(v_a_1147_);
lean_dec_ref(v_a_1146_);
lean_dec(v_a_1145_);
lean_dec_ref(v_a_1144_);
lean_dec(v_a_1143_);
lean_dec_ref(v_e_1142_);
return v___x_1172_;
}
}
else
{
lean_dec(v_a_1165_);
lean_dec(v_a_1151_);
lean_dec_ref(v_a_1150_);
lean_dec(v_a_1149_);
lean_dec_ref(v_a_1148_);
lean_dec(v_a_1147_);
lean_dec_ref(v_a_1146_);
lean_dec(v_a_1145_);
lean_dec_ref(v_a_1144_);
lean_dec(v_a_1143_);
lean_dec_ref(v_e_1142_);
return v___x_1166_;
}
}
else
{
lean_dec_ref(v_a_1167_);
lean_dec(v_a_1165_);
lean_dec(v_a_1151_);
lean_dec_ref(v_a_1150_);
lean_dec(v_a_1149_);
lean_dec_ref(v_a_1148_);
lean_dec(v_a_1147_);
lean_dec_ref(v_a_1146_);
lean_dec(v_a_1145_);
lean_dec_ref(v_a_1144_);
lean_dec(v_a_1143_);
lean_dec_ref(v_e_1142_);
return v___x_1166_;
}
}
else
{
lean_dec(v_a_1165_);
lean_dec(v_a_1151_);
lean_dec_ref(v_a_1150_);
lean_dec(v_a_1149_);
lean_dec_ref(v_a_1148_);
lean_dec(v_a_1147_);
lean_dec_ref(v_a_1146_);
lean_dec(v_a_1145_);
lean_dec_ref(v_a_1144_);
lean_dec(v_a_1143_);
lean_dec_ref(v_e_1142_);
return v___x_1166_;
}
}
else
{
lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1183_; 
lean_dec(v_a_1151_);
lean_dec_ref(v_a_1150_);
lean_dec(v_a_1149_);
lean_dec_ref(v_a_1148_);
lean_dec(v_a_1147_);
lean_dec_ref(v_a_1146_);
lean_dec(v_a_1145_);
lean_dec_ref(v_a_1144_);
lean_dec(v_a_1143_);
lean_dec_ref(v_e_1142_);
v_a_1176_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1178_ = v___x_1164_;
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___x_1164_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1181_; 
if (v_isShared_1179_ == 0)
{
v___x_1181_ = v___x_1178_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_a_1176_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
}
else
{
lean_object* v___x_1184_; uint8_t v___x_1185_; lean_object* v___x_1187_; 
lean_dec(v_declName_1157_);
lean_dec(v_a_1151_);
lean_dec_ref(v_a_1150_);
lean_dec(v_a_1149_);
lean_dec_ref(v_a_1148_);
lean_dec(v_a_1147_);
lean_dec_ref(v_a_1146_);
lean_dec(v_a_1145_);
lean_dec_ref(v_a_1144_);
lean_dec(v_a_1143_);
lean_dec_ref(v_e_1142_);
v___x_1184_ = lean_alloc_ctor(0, 0, 1);
v___x_1185_ = lean_unbox(v_a_1159_);
lean_dec(v_a_1159_);
lean_ctor_set_uint8(v___x_1184_, 0, v___x_1185_);
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 0, v___x_1184_);
v___x_1187_ = v___x_1161_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v___x_1184_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
}
}
else
{
lean_object* v_a_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1197_; 
lean_dec(v_declName_1157_);
lean_dec(v_a_1151_);
lean_dec_ref(v_a_1150_);
lean_dec(v_a_1149_);
lean_dec_ref(v_a_1148_);
lean_dec(v_a_1147_);
lean_dec_ref(v_a_1146_);
lean_dec(v_a_1145_);
lean_dec_ref(v_a_1144_);
lean_dec(v_a_1143_);
lean_dec_ref(v_e_1142_);
v_a_1190_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1197_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1192_ = v___x_1158_;
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_a_1190_);
lean_dec(v___x_1158_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1195_; 
if (v_isShared_1193_ == 0)
{
v___x_1195_ = v___x_1192_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_a_1190_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
}
}
case 6:
{
lean_object* v___x_1198_; 
lean_dec_ref(v_fn_1156_);
lean_dec_ref(v_a_1146_);
lean_dec(v_a_1145_);
lean_dec_ref(v_a_1144_);
lean_dec(v_a_1143_);
v___x_1198_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg(v_e_1142_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_);
lean_dec(v_a_1147_);
return v___x_1198_;
}
default: 
{
lean_object* v___x_1199_; lean_object* v___x_1200_; 
lean_dec_ref(v_fn_1156_);
lean_dec(v_a_1151_);
lean_dec_ref(v_a_1150_);
lean_dec(v_a_1149_);
lean_dec_ref(v_a_1148_);
lean_dec(v_a_1147_);
lean_dec_ref(v_a_1146_);
lean_dec(v_a_1145_);
lean_dec_ref(v_a_1144_);
lean_dec(v_a_1143_);
lean_dec_ref(v_e_1142_);
v___x_1199_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__9));
v___x_1200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1199_);
return v___x_1200_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp___boxed(lean_object* v_e_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp(v_e_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0(lean_object* v_00_u03b1_1213_, lean_object* v_constName_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_){
_start:
{
lean_object* v___x_1225_; 
v___x_1225_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0___redArg(v_constName_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1226_, lean_object* v_constName_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0(v_00_u03b1_1226_, v_constName_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
lean_dec(v___y_1236_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec(v___y_1228_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1239_, lean_object* v_ref_1240_, lean_object* v_constName_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_){
_start:
{
lean_object* v___x_1252_; 
v___x_1252_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg(v_ref_1240_, v_constName_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1253_, lean_object* v_ref_1254_, lean_object* v_constName_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
lean_object* v_res_1266_; 
v_res_1266_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1(v_00_u03b1_1253_, v_ref_1254_, v_constName_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
lean_dec(v___y_1264_);
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v___y_1256_);
lean_dec(v_ref_1254_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1267_, lean_object* v_ref_1268_, lean_object* v_msg_1269_, lean_object* v_declHint_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
lean_object* v___x_1281_; 
v___x_1281_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1268_, v_msg_1269_, v_declHint_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1282_, lean_object* v_ref_1283_, lean_object* v_msg_1284_, lean_object* v_declHint_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v_res_1296_; 
v_res_1296_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1282_, v_ref_1283_, v_msg_1284_, v_declHint_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_);
lean_dec(v___y_1294_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
lean_dec(v___y_1286_);
lean_dec(v_ref_1283_);
return v_res_1296_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_1297_, lean_object* v_declHint_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_){
_start:
{
lean_object* v___x_1309_; 
v___x_1309_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1297_, v_declHint_1298_, v___y_1307_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_1310_, lean_object* v_declHint_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_){
_start:
{
lean_object* v_res_1322_; 
v_res_1322_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_1310_, v_declHint_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
lean_dec(v___y_1320_);
lean_dec_ref(v___y_1319_);
lean_dec(v___y_1318_);
lean_dec_ref(v___y_1317_);
lean_dec(v___y_1316_);
lean_dec_ref(v___y_1315_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v___y_1312_);
return v_res_1322_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_1323_, lean_object* v_ref_1324_, lean_object* v_msg_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_){
_start:
{
lean_object* v___x_1336_; 
v___x_1336_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1324_, v_msg_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_);
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_1337_, lean_object* v_ref_1338_, lean_object* v_msg_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_1337_, v_ref_1338_, v_msg_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
lean_dec(v___y_1348_);
lean_dec(v___y_1346_);
lean_dec_ref(v___y_1345_);
lean_dec(v___y_1344_);
lean_dec_ref(v___y_1343_);
lean_dec(v___y_1342_);
lean_dec_ref(v___y_1341_);
lean_dec(v___y_1340_);
lean_dec(v_ref_1338_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_1351_, lean_object* v_msg_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_){
_start:
{
lean_object* v___x_1363_; 
v___x_1363_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_1352_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1364_, lean_object* v_msg_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_){
_start:
{
lean_object* v_res_1376_; 
v_res_1376_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(v_00_u03b1_1364_, v_msg_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
lean_dec(v___y_1374_);
lean_dec_ref(v___y_1373_);
lean_dec(v___y_1372_);
lean_dec_ref(v___y_1371_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
lean_dec(v___y_1366_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_isOpaqueConst___redArg(lean_object* v_e_1377_, lean_object* v_a_1378_){
_start:
{
if (lean_obj_tag(v_e_1377_) == 4)
{
lean_object* v_declName_1380_; lean_object* v___x_1381_; 
v_declName_1380_ = lean_ctor_get(v_e_1377_, 0);
v___x_1381_ = l_Lean_Meta_Tactic_Cbv_isCbvOpaque___redArg(v_declName_1380_, v_a_1378_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v_a_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1391_; 
v_a_1382_ = lean_ctor_get(v___x_1381_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1384_ = v___x_1381_;
v_isShared_1385_ = v_isSharedCheck_1391_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_a_1382_);
lean_dec(v___x_1381_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1391_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1386_; uint8_t v___x_1387_; lean_object* v___x_1389_; 
v___x_1386_ = lean_alloc_ctor(0, 0, 1);
v___x_1387_ = lean_unbox(v_a_1382_);
lean_dec(v_a_1382_);
lean_ctor_set_uint8(v___x_1386_, 0, v___x_1387_);
if (v_isShared_1385_ == 0)
{
lean_ctor_set(v___x_1384_, 0, v___x_1386_);
v___x_1389_ = v___x_1384_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v___x_1386_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
else
{
lean_object* v_a_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1399_; 
v_a_1392_ = lean_ctor_get(v___x_1381_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1394_ = v___x_1381_;
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_a_1392_);
lean_dec(v___x_1381_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1397_; 
if (v_isShared_1395_ == 0)
{
v___x_1397_ = v___x_1394_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v_a_1392_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
return v___x_1397_;
}
}
}
}
else
{
lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1400_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__9));
v___x_1401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1401_, 0, v___x_1400_);
return v___x_1401_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_isOpaqueConst___redArg___boxed(lean_object* v_e_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_){
_start:
{
lean_object* v_res_1405_; 
v_res_1405_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_isOpaqueConst___redArg(v_e_1402_, v_a_1403_);
lean_dec(v_a_1403_);
lean_dec_ref(v_e_1402_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_isOpaqueConst(lean_object* v_e_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_){
_start:
{
lean_object* v___x_1417_; 
v___x_1417_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_isOpaqueConst___redArg(v_e_1406_, v_a_1415_);
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_isOpaqueConst___boxed(lean_object* v_e_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_){
_start:
{
lean_object* v_res_1429_; 
v_res_1429_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_isOpaqueConst(v_e_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_);
lean_dec(v_a_1427_);
lean_dec_ref(v_a_1426_);
lean_dec(v_a_1425_);
lean_dec_ref(v_a_1424_);
lean_dec(v_a_1423_);
lean_dec_ref(v_a_1422_);
lean_dec(v_a_1421_);
lean_dec_ref(v_a_1420_);
lean_dec(v_a_1419_);
lean_dec_ref(v_e_1418_);
return v_res_1429_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__1(void){
_start:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1431_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__0));
v___x_1432_ = l_Lean_stringToMessageData(v___x_1431_);
return v___x_1432_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__3(void){
_start:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1434_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__2));
v___x_1435_ = l_Lean_stringToMessageData(v___x_1434_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg(lean_object* v_e_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_){
_start:
{
lean_object* v___x_1443_; 
lean_inc_ref(v_e_1436_);
v___x_1443_ = l_Lean_Expr_rawNatLit_x3f(v_e_1436_);
if (lean_obj_tag(v___x_1443_) == 1)
{
lean_object* v_val_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; 
v_val_1444_ = lean_ctor_get(v___x_1443_, 0);
lean_inc(v_val_1444_);
lean_dec_ref(v___x_1443_);
v___x_1445_ = l_Lean_mkNatLit(v_val_1444_);
v___x_1446_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_1445_, v_a_1437_);
if (lean_obj_tag(v___x_1446_) == 0)
{
lean_object* v_a_1447_; lean_object* v___y_1449_; lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v___y_1452_; lean_object* v___y_1453_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v_a_1475_; uint8_t v___x_1476_; 
v_a_1447_ = lean_ctor_get(v___x_1446_, 0);
lean_inc(v_a_1447_);
lean_dec_ref(v___x_1446_);
v___x_1473_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2));
v___x_1474_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(v___x_1473_, v_a_1440_);
v_a_1475_ = lean_ctor_get(v___x_1474_, 0);
lean_inc(v_a_1475_);
lean_dec_ref(v___x_1474_);
v___x_1476_ = lean_unbox(v_a_1475_);
lean_dec(v_a_1475_);
if (v___x_1476_ == 0)
{
v___y_1449_ = v_a_1437_;
v___y_1450_ = v_a_1438_;
v___y_1451_ = v_a_1439_;
v___y_1452_ = v_a_1440_;
v___y_1453_ = v_a_1441_;
goto v___jp_1448_;
}
else
{
lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1477_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__1, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__1);
lean_inc_ref(v_e_1436_);
v___x_1478_ = l_Lean_MessageData_ofExpr(v_e_1436_);
v___x_1479_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1477_);
lean_ctor_set(v___x_1479_, 1, v___x_1478_);
v___x_1480_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__3, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__3);
v___x_1481_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1481_, 0, v___x_1479_);
lean_ctor_set(v___x_1481_, 1, v___x_1480_);
lean_inc(v_a_1447_);
v___x_1482_ = l_Lean_MessageData_ofExpr(v_a_1447_);
v___x_1483_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1483_, 0, v___x_1481_);
lean_ctor_set(v___x_1483_, 1, v___x_1482_);
v___x_1484_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg(v___x_1473_, v___x_1483_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_);
if (lean_obj_tag(v___x_1484_) == 0)
{
lean_dec_ref(v___x_1484_);
v___y_1449_ = v_a_1437_;
v___y_1450_ = v_a_1438_;
v___y_1451_ = v_a_1439_;
v___y_1452_ = v_a_1440_;
v___y_1453_ = v_a_1441_;
goto v___jp_1448_;
}
else
{
lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1492_; 
lean_dec(v_a_1447_);
lean_dec(v_a_1441_);
lean_dec_ref(v_a_1440_);
lean_dec(v_a_1439_);
lean_dec_ref(v_a_1438_);
lean_dec_ref(v_e_1436_);
v_a_1485_ = lean_ctor_get(v___x_1484_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1487_ = v___x_1484_;
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_a_1485_);
lean_dec(v___x_1484_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1490_; 
if (v_isShared_1488_ == 0)
{
v___x_1490_ = v___x_1487_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_a_1485_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
}
v___jp_1448_:
{
lean_object* v___x_1454_; 
v___x_1454_ = l_Lean_Meta_Sym_mkEqRefl___redArg(v_e_1436_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_object* v_a_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1464_; 
v_a_1455_ = lean_ctor_get(v___x_1454_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1457_ = v___x_1454_;
v_isShared_1458_ = v_isSharedCheck_1464_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_a_1455_);
lean_dec(v___x_1454_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1464_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
uint8_t v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1462_; 
v___x_1459_ = 0;
v___x_1460_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_1460_, 0, v_a_1447_);
lean_ctor_set(v___x_1460_, 1, v_a_1455_);
lean_ctor_set_uint8(v___x_1460_, sizeof(void*)*2, v___x_1459_);
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 0, v___x_1460_);
v___x_1462_ = v___x_1457_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v___x_1460_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
else
{
lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1472_; 
lean_dec(v_a_1447_);
v_a_1465_ = lean_ctor_get(v___x_1454_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1467_ = v___x_1454_;
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v___x_1454_);
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
}
else
{
lean_object* v_a_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1500_; 
lean_dec(v_a_1441_);
lean_dec_ref(v_a_1440_);
lean_dec(v_a_1439_);
lean_dec_ref(v_a_1438_);
lean_dec_ref(v_e_1436_);
v_a_1493_ = lean_ctor_get(v___x_1446_, 0);
v_isSharedCheck_1500_ = !lean_is_exclusive(v___x_1446_);
if (v_isSharedCheck_1500_ == 0)
{
v___x_1495_ = v___x_1446_;
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_a_1493_);
lean_dec(v___x_1446_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1498_; 
if (v_isShared_1496_ == 0)
{
v___x_1498_ = v___x_1495_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v_a_1493_);
v___x_1498_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
return v___x_1498_;
}
}
}
}
else
{
lean_object* v___x_1501_; lean_object* v___x_1502_; 
lean_dec(v___x_1443_);
lean_dec(v_a_1441_);
lean_dec_ref(v_a_1440_);
lean_dec(v_a_1439_);
lean_dec_ref(v_a_1438_);
lean_dec_ref(v_e_1436_);
v___x_1501_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__9));
v___x_1502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1502_, 0, v___x_1501_);
return v___x_1502_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___boxed(lean_object* v_e_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg(v_e_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_);
lean_dec(v_a_1504_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit(lean_object* v_e_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_){
_start:
{
lean_object* v___x_1522_; 
v___x_1522_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg(v_e_1511_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___boxed(lean_object* v_e_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_){
_start:
{
lean_object* v_res_1534_; 
v_res_1534_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit(v_e_1523_, v_a_1524_, v_a_1525_, v_a_1526_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_);
lean_dec(v_a_1528_);
lean_dec_ref(v_a_1527_);
lean_dec(v_a_1526_);
lean_dec_ref(v_a_1525_);
lean_dec(v_a_1524_);
return v_res_1534_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg___closed__1(void){
_start:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1536_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg___closed__0));
v___x_1537_ = l_Lean_stringToMessageData(v___x_1536_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg(lean_object* v_e_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_){
_start:
{
if (lean_obj_tag(v_e_1538_) == 8)
{
lean_object* v_value_1545_; lean_object* v_body_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; uint8_t v___x_1550_; lean_object* v_new_1551_; lean_object* v___x_1552_; 
v_value_1545_ = lean_ctor_get(v_e_1538_, 2);
v_body_1546_ = lean_ctor_get(v_e_1538_, 3);
v___x_1547_ = lean_unsigned_to_nat(1u);
v___x_1548_ = lean_mk_empty_array_with_capacity(v___x_1547_);
lean_inc_ref(v_value_1545_);
v___x_1549_ = lean_array_push(v___x_1548_, v_value_1545_);
v___x_1550_ = 1;
v_new_1551_ = l_Lean_Meta_expandLet(v_body_1546_, v___x_1549_, v___x_1550_);
v___x_1552_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_new_1551_, v_a_1539_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v_a_1553_; lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v___y_1557_; lean_object* v___y_1558_; lean_object* v___y_1559_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v_a_1581_; uint8_t v___x_1582_; 
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
lean_inc(v_a_1553_);
lean_dec_ref(v___x_1552_);
v___x_1579_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2));
v___x_1580_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(v___x_1579_, v_a_1542_);
v_a_1581_ = lean_ctor_get(v___x_1580_, 0);
lean_inc(v_a_1581_);
lean_dec_ref(v___x_1580_);
v___x_1582_ = lean_unbox(v_a_1581_);
lean_dec(v_a_1581_);
if (v___x_1582_ == 0)
{
lean_dec_ref(v_e_1538_);
v___y_1555_ = v_a_1539_;
v___y_1556_ = v_a_1540_;
v___y_1557_ = v_a_1541_;
v___y_1558_ = v_a_1542_;
v___y_1559_ = v_a_1543_;
goto v___jp_1554_;
}
else
{
lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1583_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg___closed__1, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg___closed__1);
v___x_1584_ = l_Lean_indentExpr(v_e_1538_);
v___x_1585_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1583_);
lean_ctor_set(v___x_1585_, 1, v___x_1584_);
v___x_1586_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7);
v___x_1587_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1585_);
lean_ctor_set(v___x_1587_, 1, v___x_1586_);
lean_inc(v_a_1553_);
v___x_1588_ = l_Lean_indentExpr(v_a_1553_);
v___x_1589_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1587_);
lean_ctor_set(v___x_1589_, 1, v___x_1588_);
v___x_1590_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg(v___x_1579_, v___x_1589_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_dec_ref(v___x_1590_);
v___y_1555_ = v_a_1539_;
v___y_1556_ = v_a_1540_;
v___y_1557_ = v_a_1541_;
v___y_1558_ = v_a_1542_;
v___y_1559_ = v_a_1543_;
goto v___jp_1554_;
}
else
{
lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1598_; 
lean_dec(v_a_1553_);
lean_dec(v_a_1543_);
lean_dec_ref(v_a_1542_);
lean_dec(v_a_1541_);
lean_dec_ref(v_a_1540_);
v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1593_ = v___x_1590_;
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_dec(v___x_1590_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1596_; 
if (v_isShared_1594_ == 0)
{
v___x_1596_ = v___x_1593_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_a_1591_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
}
}
}
}
v___jp_1554_:
{
lean_object* v___x_1560_; 
lean_inc(v_a_1553_);
v___x_1560_ = l_Lean_Meta_Sym_mkEqRefl___redArg(v_a_1553_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_object* v_a_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1570_; 
v_a_1561_ = lean_ctor_get(v___x_1560_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1563_ = v___x_1560_;
v_isShared_1564_ = v_isSharedCheck_1570_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_a_1561_);
lean_dec(v___x_1560_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1570_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
uint8_t v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1568_; 
v___x_1565_ = 0;
v___x_1566_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_1566_, 0, v_a_1553_);
lean_ctor_set(v___x_1566_, 1, v_a_1561_);
lean_ctor_set_uint8(v___x_1566_, sizeof(void*)*2, v___x_1565_);
if (v_isShared_1564_ == 0)
{
lean_ctor_set(v___x_1563_, 0, v___x_1566_);
v___x_1568_ = v___x_1563_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v___x_1566_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
else
{
lean_object* v_a_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1578_; 
lean_dec(v_a_1553_);
v_a_1571_ = lean_ctor_get(v___x_1560_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1573_ = v___x_1560_;
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_a_1571_);
lean_dec(v___x_1560_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1576_; 
if (v_isShared_1574_ == 0)
{
v___x_1576_ = v___x_1573_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_a_1571_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
}
}
else
{
lean_object* v_a_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1606_; 
lean_dec_ref(v_e_1538_);
lean_dec(v_a_1543_);
lean_dec_ref(v_a_1542_);
lean_dec(v_a_1541_);
lean_dec_ref(v_a_1540_);
v_a_1599_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1601_ = v___x_1552_;
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_dec(v___x_1552_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1604_; 
if (v_isShared_1602_ == 0)
{
v___x_1604_ = v___x_1601_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_a_1599_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
}
else
{
lean_object* v___x_1607_; lean_object* v___x_1608_; 
lean_dec(v_a_1543_);
lean_dec_ref(v_a_1542_);
lean_dec(v_a_1541_);
lean_dec_ref(v_a_1540_);
lean_dec_ref(v_e_1538_);
v___x_1607_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__9));
v___x_1608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1607_);
return v___x_1608_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg___boxed(lean_object* v_e_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_){
_start:
{
lean_object* v_res_1616_; 
v_res_1616_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg(v_e_1609_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_, v_a_1614_);
lean_dec(v_a_1610_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce(lean_object* v_e_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_){
_start:
{
lean_object* v___x_1628_; 
v___x_1628_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg(v_e_1617_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___boxed(lean_object* v_e_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_){
_start:
{
lean_object* v_res_1640_; 
v_res_1640_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce(v_e_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_, v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_);
lean_dec(v_a_1634_);
lean_dec_ref(v_a_1633_);
lean_dec(v_a_1632_);
lean_dec_ref(v_a_1631_);
lean_dec(v_a_1630_);
return v_res_1640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(lean_object* v_structName_1641_, lean_object* v_idx_1642_, lean_object* v_struct_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
lean_object* v___y_1652_; lean_object* v___x_1655_; uint8_t v_debug_1656_; 
v___x_1655_ = lean_st_ref_get(v___y_1645_);
v_debug_1656_ = lean_ctor_get_uint8(v___x_1655_, sizeof(void*)*7);
lean_dec(v___x_1655_);
if (v_debug_1656_ == 0)
{
lean_dec(v___y_1649_);
lean_dec_ref(v___y_1648_);
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec_ref(v___y_1644_);
v___y_1652_ = v___y_1645_;
goto v___jp_1651_;
}
else
{
lean_object* v___x_1657_; 
lean_inc(v___y_1645_);
lean_inc_ref(v_struct_1643_);
v___x_1657_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_struct_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_);
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_dec_ref(v___x_1657_);
v___y_1652_ = v___y_1645_;
goto v___jp_1651_;
}
else
{
lean_object* v_a_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1665_; 
lean_dec(v___y_1645_);
lean_dec_ref(v_struct_1643_);
lean_dec(v_idx_1642_);
lean_dec(v_structName_1641_);
v_a_1658_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1660_ = v___x_1657_;
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_a_1658_);
lean_dec(v___x_1657_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1663_; 
if (v_isShared_1661_ == 0)
{
v___x_1663_ = v___x_1660_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_a_1658_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
}
v___jp_1651_:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___x_1653_ = l_Lean_Expr_proj___override(v_structName_1641_, v_idx_1642_, v_struct_1643_);
v___x_1654_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1653_, v___y_1652_);
lean_dec(v___y_1652_);
return v___x_1654_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg___boxed(lean_object* v_structName_1666_, lean_object* v_idx_1667_, lean_object* v_struct_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_structName_1666_, v_idx_1667_, v_struct_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0(lean_object* v_structName_1677_, lean_object* v_idx_1678_, lean_object* v_struct_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_){
_start:
{
lean_object* v___x_1690_; 
v___x_1690_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_structName_1677_, v_idx_1678_, v_struct_1679_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___boxed(lean_object* v_structName_1691_, lean_object* v_idx_1692_, lean_object* v_struct_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_){
_start:
{
lean_object* v_res_1704_; 
v_res_1704_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0(v_structName_1691_, v_idx_1692_, v_struct_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_);
lean_dec(v___y_1696_);
lean_dec_ref(v___y_1695_);
lean_dec(v___y_1694_);
return v_res_1704_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___redArg___closed__0(void){
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
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___x_1708_ = ((size_t)5ULL);
v___x_1709_ = lean_unsigned_to_nat(0u);
v___x_1710_ = lean_unsigned_to_nat(32u);
v___x_1711_ = lean_mk_empty_array_with_capacity(v___x_1710_);
v___x_1712_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___redArg___closed__0);
v___x_1713_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1713_, 0, v___x_1712_);
lean_ctor_set(v___x_1713_, 1, v___x_1711_);
lean_ctor_set(v___x_1713_, 2, v___x_1709_);
lean_ctor_set(v___x_1713_, 3, v___x_1709_);
lean_ctor_set_usize(v___x_1713_, 4, v___x_1708_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___redArg(lean_object* v___y_1714_){
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
v___x_1736_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___redArg___closed__1);
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___redArg___boxed(lean_object* v___y_1748_, lean_object* v___y_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___redArg(v___y_1748_);
lean_dec(v___y_1748_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1(lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_){
_start:
{
lean_object* v___x_1761_; 
v___x_1761_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___redArg(v___y_1759_);
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___boxed(lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1(v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_);
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
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2(lean_object* v_opts_1773_, lean_object* v_opt_1774_){
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
lean_dec_ref(v___x_1778_);
if (lean_obj_tag(v_val_1780_) == 1)
{
uint8_t v_v_1781_; 
v_v_1781_ = lean_ctor_get_uint8(v_val_1780_, 0);
lean_dec_ref(v_val_1780_);
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___boxed(lean_object* v_opts_1783_, lean_object* v_opt_1784_){
_start:
{
uint8_t v_res_1785_; lean_object* v_r_1786_; 
v_res_1785_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2(v_opts_1783_, v_opt_1784_);
lean_dec_ref(v_opt_1784_);
lean_dec_ref(v_opts_1783_);
v_r_1786_ = lean_box(v_res_1785_);
return v_r_1786_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1788_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__0));
v___x_1789_ = l_Lean_stringToMessageData(v___x_1788_);
return v___x_1789_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1791_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__2));
v___x_1792_ = l_Lean_stringToMessageData(v___x_1791_);
return v___x_1792_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__5(void){
_start:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1794_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__4));
v___x_1795_ = l_Lean_stringToMessageData(v___x_1794_);
return v___x_1795_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__7(void){
_start:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1797_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__6));
v___x_1798_ = l_Lean_stringToMessageData(v___x_1797_);
return v___x_1798_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__9(void){
_start:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1800_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__8));
v___x_1801_ = l_Lean_stringToMessageData(v___x_1800_);
return v___x_1801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0(lean_object* v_typeName_1802_, lean_object* v_idx_1803_, lean_object* v_e_1804_, lean_object* v_x_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_){
_start:
{
if (lean_obj_tag(v_x_1805_) == 0)
{
lean_object* v_a_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1836_; 
lean_dec_ref(v_e_1804_);
v_a_1816_ = lean_ctor_get(v_x_1805_, 0);
v_isSharedCheck_1836_ = !lean_is_exclusive(v_x_1805_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1818_ = v_x_1805_;
v_isShared_1819_ = v_isSharedCheck_1836_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_a_1816_);
lean_dec(v_x_1805_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1836_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1827_; 
v___x_1820_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__1);
v___x_1821_ = l_Lean_MessageData_ofName(v_typeName_1802_);
v___x_1822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1820_);
lean_ctor_set(v___x_1822_, 1, v___x_1821_);
v___x_1823_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_1824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1822_);
lean_ctor_set(v___x_1824_, 1, v___x_1823_);
v___x_1825_ = l_Nat_reprFast(v_idx_1803_);
if (v_isShared_1819_ == 0)
{
lean_ctor_set_tag(v___x_1818_, 3);
lean_ctor_set(v___x_1818_, 0, v___x_1825_);
v___x_1827_ = v___x_1818_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v___x_1825_);
v___x_1827_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1828_ = l_Lean_MessageData_ofFormat(v___x_1827_);
v___x_1829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1824_);
lean_ctor_set(v___x_1829_, 1, v___x_1828_);
v___x_1830_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__3, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__3_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__3);
v___x_1831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1829_);
lean_ctor_set(v___x_1831_, 1, v___x_1830_);
v___x_1832_ = l_Lean_Exception_toMessageData(v_a_1816_);
v___x_1833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1831_);
lean_ctor_set(v___x_1833_, 1, v___x_1832_);
v___x_1834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1833_);
return v___x_1834_;
}
}
}
else
{
lean_object* v_a_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1893_; 
v_a_1837_ = lean_ctor_get(v_x_1805_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v_x_1805_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1839_ = v_x_1805_;
v_isShared_1840_ = v_isSharedCheck_1893_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_a_1837_);
lean_dec(v_x_1805_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1893_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
if (lean_obj_tag(v_a_1837_) == 0)
{
uint8_t v_done_1841_; 
v_done_1841_ = lean_ctor_get_uint8(v_a_1837_, 0);
lean_dec_ref(v_a_1837_);
if (v_done_1841_ == 1)
{
lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1849_; 
v___x_1842_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__1);
v___x_1843_ = l_Lean_MessageData_ofName(v_typeName_1802_);
v___x_1844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1842_);
lean_ctor_set(v___x_1844_, 1, v___x_1843_);
v___x_1845_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_1846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1844_);
lean_ctor_set(v___x_1846_, 1, v___x_1845_);
v___x_1847_ = l_Nat_reprFast(v_idx_1803_);
if (v_isShared_1840_ == 0)
{
lean_ctor_set_tag(v___x_1839_, 3);
lean_ctor_set(v___x_1839_, 0, v___x_1847_);
v___x_1849_ = v___x_1839_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1847_);
v___x_1849_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1850_ = l_Lean_MessageData_ofFormat(v___x_1849_);
v___x_1851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1846_);
lean_ctor_set(v___x_1851_, 1, v___x_1850_);
v___x_1852_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__5, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__5_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__5);
v___x_1853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1851_);
lean_ctor_set(v___x_1853_, 1, v___x_1852_);
v___x_1854_ = l_Lean_indentExpr(v_e_1804_);
v___x_1855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1853_);
lean_ctor_set(v___x_1855_, 1, v___x_1854_);
v___x_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1855_);
return v___x_1856_;
}
}
else
{
lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1865_; 
lean_dec_ref(v_e_1804_);
v___x_1858_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__1);
v___x_1859_ = l_Lean_MessageData_ofName(v_typeName_1802_);
v___x_1860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1858_);
lean_ctor_set(v___x_1860_, 1, v___x_1859_);
v___x_1861_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_1862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1860_);
lean_ctor_set(v___x_1862_, 1, v___x_1861_);
v___x_1863_ = l_Nat_reprFast(v_idx_1803_);
if (v_isShared_1840_ == 0)
{
lean_ctor_set_tag(v___x_1839_, 3);
lean_ctor_set(v___x_1839_, 0, v___x_1863_);
v___x_1865_ = v___x_1839_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v___x_1863_);
v___x_1865_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
v___x_1866_ = l_Lean_MessageData_ofFormat(v___x_1865_);
v___x_1867_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1867_, 0, v___x_1862_);
lean_ctor_set(v___x_1867_, 1, v___x_1866_);
v___x_1868_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__7, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__7_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__7);
v___x_1869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1867_);
lean_ctor_set(v___x_1869_, 1, v___x_1868_);
v___x_1870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1869_);
return v___x_1870_;
}
}
}
else
{
lean_object* v_e_x27_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1880_; 
v_e_x27_1872_ = lean_ctor_get(v_a_1837_, 0);
lean_inc_ref(v_e_x27_1872_);
lean_dec_ref(v_a_1837_);
v___x_1873_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__1, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__1);
v___x_1874_ = l_Lean_MessageData_ofName(v_typeName_1802_);
v___x_1875_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1873_);
lean_ctor_set(v___x_1875_, 1, v___x_1874_);
v___x_1876_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_1877_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1875_);
lean_ctor_set(v___x_1877_, 1, v___x_1876_);
v___x_1878_ = l_Nat_reprFast(v_idx_1803_);
if (v_isShared_1840_ == 0)
{
lean_ctor_set_tag(v___x_1839_, 3);
lean_ctor_set(v___x_1839_, 0, v___x_1878_);
v___x_1880_ = v___x_1839_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v___x_1878_);
v___x_1880_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; 
v___x_1881_ = l_Lean_MessageData_ofFormat(v___x_1880_);
v___x_1882_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1877_);
lean_ctor_set(v___x_1882_, 1, v___x_1881_);
v___x_1883_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__9, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__9_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___closed__9);
v___x_1884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1882_);
lean_ctor_set(v___x_1884_, 1, v___x_1883_);
v___x_1885_ = l_Lean_indentExpr(v_e_1804_);
v___x_1886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1884_);
lean_ctor_set(v___x_1886_, 1, v___x_1885_);
v___x_1887_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7);
v___x_1888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1886_);
lean_ctor_set(v___x_1888_, 1, v___x_1887_);
v___x_1889_ = l_Lean_indentExpr(v_e_x27_1872_);
v___x_1890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1888_);
lean_ctor_set(v___x_1890_, 1, v___x_1889_);
v___x_1891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1890_);
return v___x_1891_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___boxed(lean_object* v_typeName_1894_, lean_object* v_idx_1895_, lean_object* v_e_1896_, lean_object* v_x_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0(v_typeName_1894_, v_idx_1895_, v_e_1896_, v_x_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
lean_dec(v___y_1898_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__4_spec__5(size_t v_sz_1909_, size_t v_i_1910_, lean_object* v_bs_1911_){
_start:
{
uint8_t v___x_1912_; 
v___x_1912_ = lean_usize_dec_lt(v_i_1910_, v_sz_1909_);
if (v___x_1912_ == 0)
{
return v_bs_1911_;
}
else
{
lean_object* v_v_1913_; lean_object* v_msg_1914_; lean_object* v___x_1915_; lean_object* v_bs_x27_1916_; size_t v___x_1917_; size_t v___x_1918_; lean_object* v___x_1919_; 
v_v_1913_ = lean_array_uget_borrowed(v_bs_1911_, v_i_1910_);
v_msg_1914_ = lean_ctor_get(v_v_1913_, 1);
lean_inc_ref(v_msg_1914_);
v___x_1915_ = lean_unsigned_to_nat(0u);
v_bs_x27_1916_ = lean_array_uset(v_bs_1911_, v_i_1910_, v___x_1915_);
v___x_1917_ = ((size_t)1ULL);
v___x_1918_ = lean_usize_add(v_i_1910_, v___x_1917_);
v___x_1919_ = lean_array_uset(v_bs_x27_1916_, v_i_1910_, v_msg_1914_);
v_i_1910_ = v___x_1918_;
v_bs_1911_ = v___x_1919_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__4_spec__5___boxed(lean_object* v_sz_1921_, lean_object* v_i_1922_, lean_object* v_bs_1923_){
_start:
{
size_t v_sz_boxed_1924_; size_t v_i_boxed_1925_; lean_object* v_res_1926_; 
v_sz_boxed_1924_ = lean_unbox_usize(v_sz_1921_);
lean_dec(v_sz_1921_);
v_i_boxed_1925_ = lean_unbox_usize(v_i_1922_);
lean_dec(v_i_1922_);
v_res_1926_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__4_spec__5(v_sz_boxed_1924_, v_i_boxed_1925_, v_bs_1923_);
return v_res_1926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__4___redArg(lean_object* v_oldTraces_1927_, lean_object* v_data_1928_, lean_object* v_ref_1929_, lean_object* v_msg_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_){
_start:
{
lean_object* v_fileName_1936_; lean_object* v_fileMap_1937_; lean_object* v_options_1938_; lean_object* v_currRecDepth_1939_; lean_object* v_maxRecDepth_1940_; lean_object* v_ref_1941_; lean_object* v_currNamespace_1942_; lean_object* v_openDecls_1943_; lean_object* v_initHeartbeats_1944_; lean_object* v_maxHeartbeats_1945_; lean_object* v_quotContext_1946_; lean_object* v_currMacroScope_1947_; uint8_t v_diag_1948_; lean_object* v_cancelTk_x3f_1949_; uint8_t v_suppressElabErrors_1950_; lean_object* v_inheritedTraceOptions_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_2006_; 
v_fileName_1936_ = lean_ctor_get(v___y_1933_, 0);
v_fileMap_1937_ = lean_ctor_get(v___y_1933_, 1);
v_options_1938_ = lean_ctor_get(v___y_1933_, 2);
v_currRecDepth_1939_ = lean_ctor_get(v___y_1933_, 3);
v_maxRecDepth_1940_ = lean_ctor_get(v___y_1933_, 4);
v_ref_1941_ = lean_ctor_get(v___y_1933_, 5);
v_currNamespace_1942_ = lean_ctor_get(v___y_1933_, 6);
v_openDecls_1943_ = lean_ctor_get(v___y_1933_, 7);
v_initHeartbeats_1944_ = lean_ctor_get(v___y_1933_, 8);
v_maxHeartbeats_1945_ = lean_ctor_get(v___y_1933_, 9);
v_quotContext_1946_ = lean_ctor_get(v___y_1933_, 10);
v_currMacroScope_1947_ = lean_ctor_get(v___y_1933_, 11);
v_diag_1948_ = lean_ctor_get_uint8(v___y_1933_, sizeof(void*)*14);
v_cancelTk_x3f_1949_ = lean_ctor_get(v___y_1933_, 12);
v_suppressElabErrors_1950_ = lean_ctor_get_uint8(v___y_1933_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1951_ = lean_ctor_get(v___y_1933_, 13);
v_isSharedCheck_2006_ = !lean_is_exclusive(v___y_1933_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_1953_ = v___y_1933_;
v_isShared_1954_ = v_isSharedCheck_2006_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_inheritedTraceOptions_1951_);
lean_inc(v_cancelTk_x3f_1949_);
lean_inc(v_currMacroScope_1947_);
lean_inc(v_quotContext_1946_);
lean_inc(v_maxHeartbeats_1945_);
lean_inc(v_initHeartbeats_1944_);
lean_inc(v_openDecls_1943_);
lean_inc(v_currNamespace_1942_);
lean_inc(v_ref_1941_);
lean_inc(v_maxRecDepth_1940_);
lean_inc(v_currRecDepth_1939_);
lean_inc(v_options_1938_);
lean_inc(v_fileMap_1937_);
lean_inc(v_fileName_1936_);
lean_dec(v___y_1933_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_2006_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1955_; lean_object* v_traceState_1956_; lean_object* v_traces_1957_; lean_object* v_ref_1958_; lean_object* v___x_1960_; 
v___x_1955_ = lean_st_ref_get(v___y_1934_);
v_traceState_1956_ = lean_ctor_get(v___x_1955_, 4);
lean_inc_ref(v_traceState_1956_);
lean_dec(v___x_1955_);
v_traces_1957_ = lean_ctor_get(v_traceState_1956_, 0);
lean_inc_ref(v_traces_1957_);
lean_dec_ref(v_traceState_1956_);
v_ref_1958_ = l_Lean_replaceRef(v_ref_1929_, v_ref_1941_);
lean_dec(v_ref_1941_);
if (v_isShared_1954_ == 0)
{
lean_ctor_set(v___x_1953_, 5, v_ref_1958_);
v___x_1960_ = v___x_1953_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_fileName_1936_);
lean_ctor_set(v_reuseFailAlloc_2005_, 1, v_fileMap_1937_);
lean_ctor_set(v_reuseFailAlloc_2005_, 2, v_options_1938_);
lean_ctor_set(v_reuseFailAlloc_2005_, 3, v_currRecDepth_1939_);
lean_ctor_set(v_reuseFailAlloc_2005_, 4, v_maxRecDepth_1940_);
lean_ctor_set(v_reuseFailAlloc_2005_, 5, v_ref_1958_);
lean_ctor_set(v_reuseFailAlloc_2005_, 6, v_currNamespace_1942_);
lean_ctor_set(v_reuseFailAlloc_2005_, 7, v_openDecls_1943_);
lean_ctor_set(v_reuseFailAlloc_2005_, 8, v_initHeartbeats_1944_);
lean_ctor_set(v_reuseFailAlloc_2005_, 9, v_maxHeartbeats_1945_);
lean_ctor_set(v_reuseFailAlloc_2005_, 10, v_quotContext_1946_);
lean_ctor_set(v_reuseFailAlloc_2005_, 11, v_currMacroScope_1947_);
lean_ctor_set(v_reuseFailAlloc_2005_, 12, v_cancelTk_x3f_1949_);
lean_ctor_set(v_reuseFailAlloc_2005_, 13, v_inheritedTraceOptions_1951_);
lean_ctor_set_uint8(v_reuseFailAlloc_2005_, sizeof(void*)*14, v_diag_1948_);
lean_ctor_set_uint8(v_reuseFailAlloc_2005_, sizeof(void*)*14 + 1, v_suppressElabErrors_1950_);
v___x_1960_ = v_reuseFailAlloc_2005_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
lean_object* v___x_1961_; size_t v_sz_1962_; size_t v___x_1963_; lean_object* v___x_1964_; lean_object* v_msg_1965_; lean_object* v___x_1966_; lean_object* v_a_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_2004_; 
v___x_1961_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1957_);
lean_dec_ref(v_traces_1957_);
v_sz_1962_ = lean_array_size(v___x_1961_);
v___x_1963_ = ((size_t)0ULL);
v___x_1964_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__4_spec__5(v_sz_1962_, v___x_1963_, v___x_1961_);
v_msg_1965_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1965_, 0, v_data_1928_);
lean_ctor_set(v_msg_1965_, 1, v_msg_1930_);
lean_ctor_set(v_msg_1965_, 2, v___x_1964_);
v___x_1966_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1_spec__1(v_msg_1965_, v___y_1931_, v___y_1932_, v___x_1960_, v___y_1934_);
lean_dec_ref(v___x_1960_);
v_a_1967_ = lean_ctor_get(v___x_1966_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1969_ = v___x_1966_;
v_isShared_1970_ = v_isSharedCheck_2004_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_a_1967_);
lean_dec(v___x_1966_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_2004_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___x_1971_; lean_object* v_traceState_1972_; lean_object* v_env_1973_; lean_object* v_nextMacroScope_1974_; lean_object* v_ngen_1975_; lean_object* v_auxDeclNGen_1976_; lean_object* v_cache_1977_; lean_object* v_messages_1978_; lean_object* v_infoState_1979_; lean_object* v_snapshotTasks_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_2003_; 
v___x_1971_ = lean_st_ref_take(v___y_1934_);
v_traceState_1972_ = lean_ctor_get(v___x_1971_, 4);
v_env_1973_ = lean_ctor_get(v___x_1971_, 0);
v_nextMacroScope_1974_ = lean_ctor_get(v___x_1971_, 1);
v_ngen_1975_ = lean_ctor_get(v___x_1971_, 2);
v_auxDeclNGen_1976_ = lean_ctor_get(v___x_1971_, 3);
v_cache_1977_ = lean_ctor_get(v___x_1971_, 5);
v_messages_1978_ = lean_ctor_get(v___x_1971_, 6);
v_infoState_1979_ = lean_ctor_get(v___x_1971_, 7);
v_snapshotTasks_1980_ = lean_ctor_get(v___x_1971_, 8);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1971_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1982_ = v___x_1971_;
v_isShared_1983_ = v_isSharedCheck_2003_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_snapshotTasks_1980_);
lean_inc(v_infoState_1979_);
lean_inc(v_messages_1978_);
lean_inc(v_cache_1977_);
lean_inc(v_traceState_1972_);
lean_inc(v_auxDeclNGen_1976_);
lean_inc(v_ngen_1975_);
lean_inc(v_nextMacroScope_1974_);
lean_inc(v_env_1973_);
lean_dec(v___x_1971_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_2003_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
uint64_t v_tid_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_2001_; 
v_tid_1984_ = lean_ctor_get_uint64(v_traceState_1972_, sizeof(void*)*1);
v_isSharedCheck_2001_ = !lean_is_exclusive(v_traceState_1972_);
if (v_isSharedCheck_2001_ == 0)
{
lean_object* v_unused_2002_; 
v_unused_2002_ = lean_ctor_get(v_traceState_1972_, 0);
lean_dec(v_unused_2002_);
v___x_1986_ = v_traceState_1972_;
v_isShared_1987_ = v_isSharedCheck_2001_;
goto v_resetjp_1985_;
}
else
{
lean_dec(v_traceState_1972_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_2001_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1991_; 
v___x_1988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1988_, 0, v_ref_1929_);
lean_ctor_set(v___x_1988_, 1, v_a_1967_);
v___x_1989_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1927_, v___x_1988_);
if (v_isShared_1987_ == 0)
{
lean_ctor_set(v___x_1986_, 0, v___x_1989_);
v___x_1991_ = v___x_1986_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v___x_1989_);
lean_ctor_set_uint64(v_reuseFailAlloc_2000_, sizeof(void*)*1, v_tid_1984_);
v___x_1991_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
lean_object* v___x_1993_; 
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 4, v___x_1991_);
v___x_1993_ = v___x_1982_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_env_1973_);
lean_ctor_set(v_reuseFailAlloc_1999_, 1, v_nextMacroScope_1974_);
lean_ctor_set(v_reuseFailAlloc_1999_, 2, v_ngen_1975_);
lean_ctor_set(v_reuseFailAlloc_1999_, 3, v_auxDeclNGen_1976_);
lean_ctor_set(v_reuseFailAlloc_1999_, 4, v___x_1991_);
lean_ctor_set(v_reuseFailAlloc_1999_, 5, v_cache_1977_);
lean_ctor_set(v_reuseFailAlloc_1999_, 6, v_messages_1978_);
lean_ctor_set(v_reuseFailAlloc_1999_, 7, v_infoState_1979_);
lean_ctor_set(v_reuseFailAlloc_1999_, 8, v_snapshotTasks_1980_);
v___x_1993_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1997_; 
v___x_1994_ = lean_st_ref_set(v___y_1934_, v___x_1993_);
v___x_1995_ = lean_box(0);
if (v_isShared_1970_ == 0)
{
lean_ctor_set(v___x_1969_, 0, v___x_1995_);
v___x_1997_ = v___x_1969_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v___x_1995_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__4___redArg___boxed(lean_object* v_oldTraces_2007_, lean_object* v_data_2008_, lean_object* v_ref_2009_, lean_object* v_msg_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_){
_start:
{
lean_object* v_res_2016_; 
v_res_2016_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__4___redArg(v_oldTraces_2007_, v_data_2008_, v_ref_2009_, v_msg_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_);
lean_dec(v___y_2014_);
lean_dec(v___y_2012_);
lean_dec_ref(v___y_2011_);
return v_res_2016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__6(lean_object* v_opts_2017_, lean_object* v_opt_2018_){
_start:
{
lean_object* v_name_2019_; lean_object* v_defValue_2020_; lean_object* v_map_2021_; lean_object* v___x_2022_; 
v_name_2019_ = lean_ctor_get(v_opt_2018_, 0);
v_defValue_2020_ = lean_ctor_get(v_opt_2018_, 1);
v_map_2021_ = lean_ctor_get(v_opts_2017_, 0);
v___x_2022_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2021_, v_name_2019_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_inc(v_defValue_2020_);
return v_defValue_2020_;
}
else
{
lean_object* v_val_2023_; 
v_val_2023_ = lean_ctor_get(v___x_2022_, 0);
lean_inc(v_val_2023_);
lean_dec_ref(v___x_2022_);
if (lean_obj_tag(v_val_2023_) == 3)
{
lean_object* v_v_2024_; 
v_v_2024_ = lean_ctor_get(v_val_2023_, 0);
lean_inc(v_v_2024_);
lean_dec_ref(v_val_2023_);
return v_v_2024_;
}
else
{
lean_dec(v_val_2023_);
lean_inc(v_defValue_2020_);
return v_defValue_2020_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__6___boxed(lean_object* v_opts_2025_, lean_object* v_opt_2026_){
_start:
{
lean_object* v_res_2027_; 
v_res_2027_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__6(v_opts_2025_, v_opt_2026_);
lean_dec_ref(v_opt_2026_);
lean_dec_ref(v_opts_2025_);
return v_res_2027_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__5___redArg(lean_object* v_x_2028_){
_start:
{
if (lean_obj_tag(v_x_2028_) == 0)
{
lean_object* v_a_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2037_; 
v_a_2030_ = lean_ctor_get(v_x_2028_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v_x_2028_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2032_ = v_x_2028_;
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_a_2030_);
lean_dec(v_x_2028_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___x_2035_; 
if (v_isShared_2033_ == 0)
{
lean_ctor_set_tag(v___x_2032_, 1);
v___x_2035_ = v___x_2032_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_a_2030_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
return v___x_2035_;
}
}
}
else
{
lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2045_; 
v_a_2038_ = lean_ctor_get(v_x_2028_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v_x_2028_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2040_ = v_x_2028_;
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v_x_2028_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2043_; 
if (v_isShared_2041_ == 0)
{
lean_ctor_set_tag(v___x_2040_, 0);
v___x_2043_ = v___x_2040_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_a_2038_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__5___redArg___boxed(lean_object* v_x_2046_, lean_object* v___y_2047_){
_start:
{
lean_object* v_res_2048_; 
v_res_2048_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__5___redArg(v_x_2046_);
return v_res_2048_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__3(lean_object* v_e_2049_){
_start:
{
if (lean_obj_tag(v_e_2049_) == 0)
{
uint8_t v___x_2050_; 
v___x_2050_ = 2;
return v___x_2050_;
}
else
{
uint8_t v___x_2051_; 
v___x_2051_ = 0;
return v___x_2051_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__3___boxed(lean_object* v_e_2052_){
_start:
{
uint8_t v_res_2053_; lean_object* v_r_2054_; 
v_res_2053_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__3(v_e_2052_);
lean_dec_ref(v_e_2052_);
v_r_2054_ = lean_box(v_res_2053_);
return v_r_2054_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__1(void){
_start:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2056_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__0));
v___x_2057_ = l_Lean_stringToMessageData(v___x_2056_);
return v___x_2057_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__3(void){
_start:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2059_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__2));
v___x_2060_ = l_Lean_stringToMessageData(v___x_2059_);
return v___x_2060_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__4(void){
_start:
{
lean_object* v___x_2061_; double v___x_2062_; 
v___x_2061_ = lean_unsigned_to_nat(1000u);
v___x_2062_ = lean_float_of_nat(v___x_2061_);
return v___x_2062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(lean_object* v_cls_2063_, uint8_t v_collapsed_2064_, lean_object* v_tag_2065_, lean_object* v_opts_2066_, uint8_t v_clsEnabled_2067_, lean_object* v_oldTraces_2068_, lean_object* v_msg_2069_, lean_object* v_resStartStop_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_){
_start:
{
lean_object* v_fst_2081_; lean_object* v_snd_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2180_; 
v_fst_2081_ = lean_ctor_get(v_resStartStop_2070_, 0);
v_snd_2082_ = lean_ctor_get(v_resStartStop_2070_, 1);
v_isSharedCheck_2180_ = !lean_is_exclusive(v_resStartStop_2070_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2084_ = v_resStartStop_2070_;
v_isShared_2085_ = v_isSharedCheck_2180_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_snd_2082_);
lean_inc(v_fst_2081_);
lean_dec(v_resStartStop_2070_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2180_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___y_2087_; lean_object* v___y_2088_; lean_object* v_data_2089_; lean_object* v_fst_2100_; lean_object* v_snd_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2179_; 
v_fst_2100_ = lean_ctor_get(v_snd_2082_, 0);
v_snd_2101_ = lean_ctor_get(v_snd_2082_, 1);
v_isSharedCheck_2179_ = !lean_is_exclusive(v_snd_2082_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2103_ = v_snd_2082_;
v_isShared_2104_ = v_isSharedCheck_2179_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_snd_2101_);
lean_inc(v_fst_2100_);
lean_dec(v_snd_2082_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2179_;
goto v_resetjp_2102_;
}
v___jp_2086_:
{
lean_object* v___x_2090_; 
v___x_2090_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__4___redArg(v_oldTraces_2068_, v_data_2089_, v___y_2087_, v___y_2088_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_);
lean_dec(v___y_2079_);
lean_dec(v___y_2077_);
lean_dec_ref(v___y_2076_);
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_object* v___x_2091_; 
lean_dec_ref(v___x_2090_);
v___x_2091_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__5___redArg(v_fst_2081_);
return v___x_2091_;
}
else
{
lean_object* v_a_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2099_; 
lean_dec(v_fst_2081_);
v_a_2092_ = lean_ctor_get(v___x_2090_, 0);
v_isSharedCheck_2099_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2094_ = v___x_2090_;
v_isShared_2095_ = v_isSharedCheck_2099_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_a_2092_);
lean_dec(v___x_2090_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2099_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v___x_2097_; 
if (v_isShared_2095_ == 0)
{
v___x_2097_ = v___x_2094_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v_a_2092_);
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
v_resetjp_2102_:
{
lean_object* v___x_2105_; uint8_t v___x_2106_; lean_object* v___y_2108_; lean_object* v_a_2109_; uint8_t v___y_2133_; double v___y_2164_; 
v___x_2105_ = l_Lean_trace_profiler;
v___x_2106_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2(v_opts_2066_, v___x_2105_);
if (v___x_2106_ == 0)
{
v___y_2133_ = v___x_2106_;
goto v___jp_2132_;
}
else
{
lean_object* v___x_2169_; uint8_t v___x_2170_; 
v___x_2169_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2170_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2(v_opts_2066_, v___x_2169_);
if (v___x_2170_ == 0)
{
lean_object* v___x_2171_; lean_object* v___x_2172_; double v___x_2173_; double v___x_2174_; double v___x_2175_; 
v___x_2171_ = l_Lean_trace_profiler_threshold;
v___x_2172_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__6(v_opts_2066_, v___x_2171_);
v___x_2173_ = lean_float_of_nat(v___x_2172_);
v___x_2174_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__4);
v___x_2175_ = lean_float_div(v___x_2173_, v___x_2174_);
v___y_2164_ = v___x_2175_;
goto v___jp_2163_;
}
else
{
lean_object* v___x_2176_; lean_object* v___x_2177_; double v___x_2178_; 
v___x_2176_ = l_Lean_trace_profiler_threshold;
v___x_2177_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__6(v_opts_2066_, v___x_2176_);
v___x_2178_ = lean_float_of_nat(v___x_2177_);
v___y_2164_ = v___x_2178_;
goto v___jp_2163_;
}
}
v___jp_2107_:
{
uint8_t v_result_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2115_; 
v_result_2110_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__3(v_fst_2081_);
v___x_2111_ = l_Lean_TraceResult_toEmoji(v_result_2110_);
v___x_2112_ = l_Lean_stringToMessageData(v___x_2111_);
v___x_2113_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__1);
if (v_isShared_2104_ == 0)
{
lean_ctor_set_tag(v___x_2103_, 7);
lean_ctor_set(v___x_2103_, 1, v___x_2113_);
lean_ctor_set(v___x_2103_, 0, v___x_2112_);
v___x_2115_ = v___x_2103_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v___x_2112_);
lean_ctor_set(v_reuseFailAlloc_2126_, 1, v___x_2113_);
v___x_2115_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
lean_object* v_m_2117_; 
if (v_isShared_2085_ == 0)
{
lean_ctor_set_tag(v___x_2084_, 7);
lean_ctor_set(v___x_2084_, 1, v_a_2109_);
lean_ctor_set(v___x_2084_, 0, v___x_2115_);
v_m_2117_ = v___x_2084_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v___x_2115_);
lean_ctor_set(v_reuseFailAlloc_2125_, 1, v_a_2109_);
v_m_2117_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; double v___x_2120_; lean_object* v_data_2121_; 
v___x_2118_ = lean_box(v_result_2110_);
v___x_2119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2118_);
v___x_2120_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__0);
lean_inc_ref(v_tag_2065_);
lean_inc_ref(v___x_2119_);
lean_inc(v_cls_2063_);
v_data_2121_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2121_, 0, v_cls_2063_);
lean_ctor_set(v_data_2121_, 1, v___x_2119_);
lean_ctor_set(v_data_2121_, 2, v_tag_2065_);
lean_ctor_set_float(v_data_2121_, sizeof(void*)*3, v___x_2120_);
lean_ctor_set_float(v_data_2121_, sizeof(void*)*3 + 8, v___x_2120_);
lean_ctor_set_uint8(v_data_2121_, sizeof(void*)*3 + 16, v_collapsed_2064_);
if (v___x_2106_ == 0)
{
lean_dec_ref(v___x_2119_);
lean_dec(v_snd_2101_);
lean_dec(v_fst_2100_);
lean_dec_ref(v_tag_2065_);
lean_dec(v_cls_2063_);
v___y_2087_ = v___y_2108_;
v___y_2088_ = v_m_2117_;
v_data_2089_ = v_data_2121_;
goto v___jp_2086_;
}
else
{
lean_object* v_data_2122_; double v___x_2123_; double v___x_2124_; 
lean_dec_ref(v_data_2121_);
v_data_2122_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2122_, 0, v_cls_2063_);
lean_ctor_set(v_data_2122_, 1, v___x_2119_);
lean_ctor_set(v_data_2122_, 2, v_tag_2065_);
v___x_2123_ = lean_unbox_float(v_fst_2100_);
lean_dec(v_fst_2100_);
lean_ctor_set_float(v_data_2122_, sizeof(void*)*3, v___x_2123_);
v___x_2124_ = lean_unbox_float(v_snd_2101_);
lean_dec(v_snd_2101_);
lean_ctor_set_float(v_data_2122_, sizeof(void*)*3 + 8, v___x_2124_);
lean_ctor_set_uint8(v_data_2122_, sizeof(void*)*3 + 16, v_collapsed_2064_);
v___y_2087_ = v___y_2108_;
v___y_2088_ = v_m_2117_;
v_data_2089_ = v_data_2122_;
goto v___jp_2086_;
}
}
}
}
v___jp_2127_:
{
lean_object* v_ref_2128_; lean_object* v___x_2129_; 
v_ref_2128_ = lean_ctor_get(v___y_2078_, 5);
lean_inc(v___y_2079_);
lean_inc_ref(v___y_2078_);
lean_inc(v___y_2077_);
lean_inc_ref(v___y_2076_);
lean_inc(v_fst_2081_);
v___x_2129_ = lean_apply_11(v_msg_2069_, v_fst_2081_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, lean_box(0));
if (lean_obj_tag(v___x_2129_) == 0)
{
lean_object* v_a_2130_; 
v_a_2130_ = lean_ctor_get(v___x_2129_, 0);
lean_inc(v_a_2130_);
lean_dec_ref(v___x_2129_);
lean_inc(v_ref_2128_);
v___y_2108_ = v_ref_2128_;
v_a_2109_ = v_a_2130_;
goto v___jp_2107_;
}
else
{
lean_object* v___x_2131_; 
lean_dec_ref(v___x_2129_);
v___x_2131_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__3);
lean_inc(v_ref_2128_);
v___y_2108_ = v_ref_2128_;
v_a_2109_ = v___x_2131_;
goto v___jp_2107_;
}
}
v___jp_2132_:
{
if (v_clsEnabled_2067_ == 0)
{
if (v___y_2133_ == 0)
{
lean_object* v___x_2134_; lean_object* v_traceState_2135_; lean_object* v_env_2136_; lean_object* v_nextMacroScope_2137_; lean_object* v_ngen_2138_; lean_object* v_auxDeclNGen_2139_; lean_object* v_cache_2140_; lean_object* v_messages_2141_; lean_object* v_infoState_2142_; lean_object* v_snapshotTasks_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2162_; 
lean_del_object(v___x_2103_);
lean_dec(v_snd_2101_);
lean_dec(v_fst_2100_);
lean_del_object(v___x_2084_);
lean_dec_ref(v___y_2078_);
lean_dec(v___y_2077_);
lean_dec_ref(v___y_2076_);
lean_dec(v___y_2075_);
lean_dec_ref(v___y_2074_);
lean_dec(v___y_2073_);
lean_dec_ref(v___y_2072_);
lean_dec(v___y_2071_);
lean_dec_ref(v_msg_2069_);
lean_dec_ref(v_tag_2065_);
lean_dec(v_cls_2063_);
v___x_2134_ = lean_st_ref_take(v___y_2079_);
v_traceState_2135_ = lean_ctor_get(v___x_2134_, 4);
v_env_2136_ = lean_ctor_get(v___x_2134_, 0);
v_nextMacroScope_2137_ = lean_ctor_get(v___x_2134_, 1);
v_ngen_2138_ = lean_ctor_get(v___x_2134_, 2);
v_auxDeclNGen_2139_ = lean_ctor_get(v___x_2134_, 3);
v_cache_2140_ = lean_ctor_get(v___x_2134_, 5);
v_messages_2141_ = lean_ctor_get(v___x_2134_, 6);
v_infoState_2142_ = lean_ctor_get(v___x_2134_, 7);
v_snapshotTasks_2143_ = lean_ctor_get(v___x_2134_, 8);
v_isSharedCheck_2162_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2145_ = v___x_2134_;
v_isShared_2146_ = v_isSharedCheck_2162_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_snapshotTasks_2143_);
lean_inc(v_infoState_2142_);
lean_inc(v_messages_2141_);
lean_inc(v_cache_2140_);
lean_inc(v_traceState_2135_);
lean_inc(v_auxDeclNGen_2139_);
lean_inc(v_ngen_2138_);
lean_inc(v_nextMacroScope_2137_);
lean_inc(v_env_2136_);
lean_dec(v___x_2134_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2162_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
uint64_t v_tid_2147_; lean_object* v_traces_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2161_; 
v_tid_2147_ = lean_ctor_get_uint64(v_traceState_2135_, sizeof(void*)*1);
v_traces_2148_ = lean_ctor_get(v_traceState_2135_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v_traceState_2135_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2150_ = v_traceState_2135_;
v_isShared_2151_ = v_isSharedCheck_2161_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_traces_2148_);
lean_dec(v_traceState_2135_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2161_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2152_; lean_object* v___x_2154_; 
v___x_2152_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2068_, v_traces_2148_);
lean_dec_ref(v_traces_2148_);
if (v_isShared_2151_ == 0)
{
lean_ctor_set(v___x_2150_, 0, v___x_2152_);
v___x_2154_ = v___x_2150_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v___x_2152_);
lean_ctor_set_uint64(v_reuseFailAlloc_2160_, sizeof(void*)*1, v_tid_2147_);
v___x_2154_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
lean_object* v___x_2156_; 
if (v_isShared_2146_ == 0)
{
lean_ctor_set(v___x_2145_, 4, v___x_2154_);
v___x_2156_ = v___x_2145_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_env_2136_);
lean_ctor_set(v_reuseFailAlloc_2159_, 1, v_nextMacroScope_2137_);
lean_ctor_set(v_reuseFailAlloc_2159_, 2, v_ngen_2138_);
lean_ctor_set(v_reuseFailAlloc_2159_, 3, v_auxDeclNGen_2139_);
lean_ctor_set(v_reuseFailAlloc_2159_, 4, v___x_2154_);
lean_ctor_set(v_reuseFailAlloc_2159_, 5, v_cache_2140_);
lean_ctor_set(v_reuseFailAlloc_2159_, 6, v_messages_2141_);
lean_ctor_set(v_reuseFailAlloc_2159_, 7, v_infoState_2142_);
lean_ctor_set(v_reuseFailAlloc_2159_, 8, v_snapshotTasks_2143_);
v___x_2156_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2157_ = lean_st_ref_set(v___y_2079_, v___x_2156_);
lean_dec(v___y_2079_);
v___x_2158_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__5___redArg(v_fst_2081_);
return v___x_2158_;
}
}
}
}
}
else
{
goto v___jp_2127_;
}
}
else
{
goto v___jp_2127_;
}
}
v___jp_2163_:
{
double v___x_2165_; double v___x_2166_; double v___x_2167_; uint8_t v___x_2168_; 
v___x_2165_ = lean_unbox_float(v_snd_2101_);
v___x_2166_ = lean_unbox_float(v_fst_2100_);
v___x_2167_ = lean_float_sub(v___x_2165_, v___x_2166_);
v___x_2168_ = lean_float_decLt(v___y_2164_, v___x_2167_);
v___y_2133_ = v___x_2168_;
goto v___jp_2132_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___boxed(lean_object** _args){
lean_object* v_cls_2181_ = _args[0];
lean_object* v_collapsed_2182_ = _args[1];
lean_object* v_tag_2183_ = _args[2];
lean_object* v_opts_2184_ = _args[3];
lean_object* v_clsEnabled_2185_ = _args[4];
lean_object* v_oldTraces_2186_ = _args[5];
lean_object* v_msg_2187_ = _args[6];
lean_object* v_resStartStop_2188_ = _args[7];
lean_object* v___y_2189_ = _args[8];
lean_object* v___y_2190_ = _args[9];
lean_object* v___y_2191_ = _args[10];
lean_object* v___y_2192_ = _args[11];
lean_object* v___y_2193_ = _args[12];
lean_object* v___y_2194_ = _args[13];
lean_object* v___y_2195_ = _args[14];
lean_object* v___y_2196_ = _args[15];
lean_object* v___y_2197_ = _args[16];
lean_object* v___y_2198_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_2199_; uint8_t v_clsEnabled_boxed_2200_; lean_object* v_res_2201_; 
v_collapsed_boxed_2199_ = lean_unbox(v_collapsed_2182_);
v_clsEnabled_boxed_2200_ = lean_unbox(v_clsEnabled_2185_);
v_res_2201_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_cls_2181_, v_collapsed_boxed_2199_, v_tag_2183_, v_opts_2184_, v_clsEnabled_boxed_2200_, v_oldTraces_2186_, v_msg_2187_, v_resStartStop_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_);
lean_dec_ref(v_opts_2184_);
return v_res_2201_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__3(void){
_start:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2207_ = lean_unsigned_to_nat(0u);
v___x_2208_ = l_Lean_Expr_bvar___override(v___x_2207_);
return v___x_2208_;
}
}
static double _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4(void){
_start:
{
lean_object* v___x_2209_; double v___x_2210_; 
v___x_2209_ = lean_unsigned_to_nat(1000000000u);
v___x_2210_ = lean_float_of_nat(v___x_2209_);
return v___x_2210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj(lean_object* v_e_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_){
_start:
{
uint8_t v___y_2223_; lean_object* v___y_2224_; lean_object* v_a_2225_; lean_object* v___y_2229_; lean_object* v_a_2230_; 
if (lean_obj_tag(v_e_2211_) == 11)
{
lean_object* v_typeName_2234_; lean_object* v_idx_2235_; lean_object* v_struct_2236_; lean_object* v_res_2238_; lean_object* v___y_2239_; lean_object* v___y_2240_; lean_object* v___y_2241_; lean_object* v___y_2242_; lean_object* v___y_2243_; lean_object* v___y_2244_; lean_object* v___y_2245_; lean_object* v___y_2246_; lean_object* v___y_2247_; lean_object* v_options_2444_; uint8_t v_hasTrace_2445_; 
v_typeName_2234_ = lean_ctor_get(v_e_2211_, 0);
v_idx_2235_ = lean_ctor_get(v_e_2211_, 1);
v_struct_2236_ = lean_ctor_get(v_e_2211_, 2);
v_options_2444_ = lean_ctor_get(v_a_2219_, 2);
v_hasTrace_2445_ = lean_ctor_get_uint8(v_options_2444_, sizeof(void*)*1);
if (v_hasTrace_2445_ == 0)
{
lean_object* v___x_2446_; 
lean_inc(v_a_2220_);
lean_inc_ref(v_a_2219_);
lean_inc(v_a_2218_);
lean_inc_ref(v_a_2217_);
lean_inc(v_a_2216_);
lean_inc_ref(v_a_2215_);
lean_inc(v_a_2214_);
lean_inc_ref(v_a_2213_);
lean_inc(v_a_2212_);
lean_inc_ref(v_struct_2236_);
v___x_2446_ = lean_sym_simp(v_struct_2236_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_);
if (lean_obj_tag(v___x_2446_) == 0)
{
lean_object* v_a_2447_; 
v_a_2447_ = lean_ctor_get(v___x_2446_, 0);
lean_inc(v_a_2447_);
lean_dec_ref(v___x_2446_);
v_res_2238_ = v_a_2447_;
v___y_2239_ = v_a_2212_;
v___y_2240_ = v_a_2213_;
v___y_2241_ = v_a_2214_;
v___y_2242_ = v_a_2215_;
v___y_2243_ = v_a_2216_;
v___y_2244_ = v_a_2217_;
v___y_2245_ = v_a_2218_;
v___y_2246_ = v_a_2219_;
v___y_2247_ = v_a_2220_;
goto v___jp_2237_;
}
else
{
lean_dec_ref(v_e_2211_);
lean_dec(v_a_2220_);
lean_dec_ref(v_a_2219_);
lean_dec(v_a_2218_);
lean_dec_ref(v_a_2217_);
lean_dec(v_a_2216_);
lean_dec_ref(v_a_2215_);
lean_dec(v_a_2214_);
lean_dec_ref(v_a_2213_);
lean_dec(v_a_2212_);
return v___x_2446_;
}
}
else
{
lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v_a_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2706_; 
v___x_2448_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2));
v___x_2449_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(v___x_2448_, v_a_2219_);
v_a_2450_ = lean_ctor_get(v___x_2449_, 0);
v_isSharedCheck_2706_ = !lean_is_exclusive(v___x_2449_);
if (v_isSharedCheck_2706_ == 0)
{
v___x_2452_ = v___x_2449_;
v_isShared_2453_ = v_isSharedCheck_2706_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_a_2450_);
lean_dec(v___x_2449_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2706_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v___f_2454_; lean_object* v___x_2455_; lean_object* v___y_2457_; lean_object* v___y_2458_; lean_object* v_a_2459_; lean_object* v___y_2473_; lean_object* v___y_2474_; lean_object* v_a_2475_; lean_object* v___y_2480_; lean_object* v___y_2481_; lean_object* v_a_2482_; lean_object* v___y_2485_; lean_object* v___y_2486_; uint8_t v___y_2487_; lean_object* v___y_2488_; lean_object* v_a_2489_; lean_object* v___y_2492_; uint8_t v___y_2493_; lean_object* v___y_2494_; lean_object* v___y_2495_; lean_object* v_a_2496_; lean_object* v___y_2499_; lean_object* v___y_2500_; lean_object* v_a_2501_; lean_object* v___y_2512_; lean_object* v___y_2513_; lean_object* v_a_2514_; lean_object* v___y_2517_; lean_object* v___y_2518_; lean_object* v_a_2519_; lean_object* v___y_2522_; lean_object* v___y_2523_; uint8_t v___y_2524_; lean_object* v___y_2525_; lean_object* v_a_2526_; lean_object* v___y_2529_; lean_object* v___y_2530_; lean_object* v___y_2531_; lean_object* v_a_2532_; uint8_t v___x_2701_; 
lean_inc_ref(v_e_2211_);
lean_inc(v_idx_2235_);
lean_inc(v_typeName_2234_);
v___f_2454_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___boxed), 14, 3);
lean_closure_set(v___f_2454_, 0, v_typeName_2234_);
lean_closure_set(v___f_2454_, 1, v_idx_2235_);
lean_closure_set(v___f_2454_, 2, v_e_2211_);
v___x_2455_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__1));
v___x_2701_ = lean_unbox(v_a_2450_);
if (v___x_2701_ == 0)
{
lean_object* v___x_2702_; uint8_t v___x_2703_; 
v___x_2702_ = l_Lean_trace_profiler;
v___x_2703_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2(v_options_2444_, v___x_2702_);
if (v___x_2703_ == 0)
{
lean_object* v___x_2704_; 
lean_dec_ref(v___f_2454_);
lean_del_object(v___x_2452_);
lean_dec(v_a_2450_);
lean_inc(v_a_2220_);
lean_inc_ref(v_a_2219_);
lean_inc(v_a_2218_);
lean_inc_ref(v_a_2217_);
lean_inc(v_a_2216_);
lean_inc_ref(v_a_2215_);
lean_inc(v_a_2214_);
lean_inc_ref(v_a_2213_);
lean_inc(v_a_2212_);
lean_inc_ref(v_struct_2236_);
v___x_2704_ = lean_sym_simp(v_struct_2236_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_);
if (lean_obj_tag(v___x_2704_) == 0)
{
lean_object* v_a_2705_; 
v_a_2705_ = lean_ctor_get(v___x_2704_, 0);
lean_inc(v_a_2705_);
lean_dec_ref(v___x_2704_);
v_res_2238_ = v_a_2705_;
v___y_2239_ = v_a_2212_;
v___y_2240_ = v_a_2213_;
v___y_2241_ = v_a_2214_;
v___y_2242_ = v_a_2215_;
v___y_2243_ = v_a_2216_;
v___y_2244_ = v_a_2217_;
v___y_2245_ = v_a_2218_;
v___y_2246_ = v_a_2219_;
v___y_2247_ = v_a_2220_;
goto v___jp_2237_;
}
else
{
lean_dec_ref(v_e_2211_);
lean_dec(v_a_2220_);
lean_dec_ref(v_a_2219_);
lean_dec(v_a_2218_);
lean_dec_ref(v_a_2217_);
lean_dec(v_a_2216_);
lean_dec_ref(v_a_2215_);
lean_dec(v_a_2214_);
lean_dec_ref(v_a_2213_);
lean_dec(v_a_2212_);
return v___x_2704_;
}
}
else
{
lean_inc_ref(v_options_2444_);
goto v___jp_2535_;
}
}
else
{
lean_inc_ref(v_options_2444_);
goto v___jp_2535_;
}
v___jp_2456_:
{
lean_object* v___x_2460_; double v___x_2461_; double v___x_2462_; double v___x_2463_; double v___x_2464_; double v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; uint8_t v___x_2470_; lean_object* v___x_2471_; 
v___x_2460_ = lean_io_mono_nanos_now();
v___x_2461_ = lean_float_of_nat(v___y_2458_);
v___x_2462_ = lean_float_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4);
v___x_2463_ = lean_float_div(v___x_2461_, v___x_2462_);
v___x_2464_ = lean_float_of_nat(v___x_2460_);
v___x_2465_ = lean_float_div(v___x_2464_, v___x_2462_);
v___x_2466_ = lean_box_float(v___x_2463_);
v___x_2467_ = lean_box_float(v___x_2465_);
v___x_2468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2468_, 0, v___x_2466_);
lean_ctor_set(v___x_2468_, 1, v___x_2467_);
v___x_2469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2469_, 0, v_a_2459_);
lean_ctor_set(v___x_2469_, 1, v___x_2468_);
v___x_2470_ = lean_unbox(v_a_2450_);
lean_dec(v_a_2450_);
v___x_2471_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v___x_2448_, v_hasTrace_2445_, v___x_2455_, v_options_2444_, v___x_2470_, v___y_2457_, v___f_2454_, v___x_2469_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_);
lean_dec_ref(v_options_2444_);
return v___x_2471_;
}
v___jp_2472_:
{
lean_object* v___x_2477_; 
if (v_isShared_2453_ == 0)
{
lean_ctor_set(v___x_2452_, 0, v_a_2475_);
v___x_2477_ = v___x_2452_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v_a_2475_);
v___x_2477_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
v___y_2457_ = v___y_2473_;
v___y_2458_ = v___y_2474_;
v_a_2459_ = v___x_2477_;
goto v___jp_2456_;
}
}
v___jp_2479_:
{
lean_object* v___x_2483_; 
v___x_2483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2483_, 0, v_a_2482_);
v___y_2457_ = v___y_2480_;
v___y_2458_ = v___y_2481_;
v_a_2459_ = v___x_2483_;
goto v___jp_2456_;
}
v___jp_2484_:
{
lean_object* v___x_2490_; 
v___x_2490_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_2490_, 0, v_a_2489_);
lean_ctor_set(v___x_2490_, 1, v___y_2486_);
lean_ctor_set_uint8(v___x_2490_, sizeof(void*)*2, v___y_2487_);
v___y_2480_ = v___y_2485_;
v___y_2481_ = v___y_2488_;
v_a_2482_ = v___x_2490_;
goto v___jp_2479_;
}
v___jp_2491_:
{
lean_object* v___x_2497_; 
v___x_2497_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_2497_, 0, v_a_2496_);
lean_ctor_set(v___x_2497_, 1, v___y_2494_);
lean_ctor_set_uint8(v___x_2497_, sizeof(void*)*2, v___y_2493_);
v___y_2480_ = v___y_2492_;
v___y_2481_ = v___y_2495_;
v_a_2482_ = v___x_2497_;
goto v___jp_2479_;
}
v___jp_2498_:
{
lean_object* v___x_2502_; double v___x_2503_; double v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; uint8_t v___x_2509_; lean_object* v___x_2510_; 
v___x_2502_ = lean_io_get_num_heartbeats();
v___x_2503_ = lean_float_of_nat(v___y_2500_);
v___x_2504_ = lean_float_of_nat(v___x_2502_);
v___x_2505_ = lean_box_float(v___x_2503_);
v___x_2506_ = lean_box_float(v___x_2504_);
v___x_2507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2507_, 0, v___x_2505_);
lean_ctor_set(v___x_2507_, 1, v___x_2506_);
v___x_2508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2508_, 0, v_a_2501_);
lean_ctor_set(v___x_2508_, 1, v___x_2507_);
v___x_2509_ = lean_unbox(v_a_2450_);
lean_dec(v_a_2450_);
v___x_2510_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v___x_2448_, v_hasTrace_2445_, v___x_2455_, v_options_2444_, v___x_2509_, v___y_2499_, v___f_2454_, v___x_2508_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_);
lean_dec_ref(v_options_2444_);
return v___x_2510_;
}
v___jp_2511_:
{
lean_object* v___x_2515_; 
v___x_2515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2515_, 0, v_a_2514_);
v___y_2499_ = v___y_2512_;
v___y_2500_ = v___y_2513_;
v_a_2501_ = v___x_2515_;
goto v___jp_2498_;
}
v___jp_2516_:
{
lean_object* v___x_2520_; 
v___x_2520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2520_, 0, v_a_2519_);
v___y_2499_ = v___y_2517_;
v___y_2500_ = v___y_2518_;
v_a_2501_ = v___x_2520_;
goto v___jp_2498_;
}
v___jp_2521_:
{
lean_object* v___x_2527_; 
v___x_2527_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_2527_, 0, v_a_2526_);
lean_ctor_set(v___x_2527_, 1, v___y_2523_);
lean_ctor_set_uint8(v___x_2527_, sizeof(void*)*2, v___y_2524_);
v___y_2517_ = v___y_2522_;
v___y_2518_ = v___y_2525_;
v_a_2519_ = v___x_2527_;
goto v___jp_2516_;
}
v___jp_2528_:
{
uint8_t v___x_2533_; lean_object* v___x_2534_; 
v___x_2533_ = 0;
v___x_2534_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_2534_, 0, v_a_2532_);
lean_ctor_set(v___x_2534_, 1, v___y_2530_);
lean_ctor_set_uint8(v___x_2534_, sizeof(void*)*2, v___x_2533_);
v___y_2517_ = v___y_2529_;
v___y_2518_ = v___y_2531_;
v_a_2519_ = v___x_2534_;
goto v___jp_2516_;
}
v___jp_2535_:
{
lean_object* v___x_2536_; lean_object* v_a_2537_; lean_object* v___x_2538_; uint8_t v___x_2539_; 
v___x_2536_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___redArg(v_a_2220_);
v_a_2537_ = lean_ctor_get(v___x_2536_, 0);
lean_inc(v_a_2537_);
lean_dec_ref(v___x_2536_);
v___x_2538_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2539_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2(v_options_2444_, v___x_2538_);
if (v___x_2539_ == 0)
{
lean_object* v___x_2540_; lean_object* v___x_2541_; 
v___x_2540_ = lean_io_mono_nanos_now();
lean_inc(v_a_2220_);
lean_inc_ref(v_a_2219_);
lean_inc(v_a_2218_);
lean_inc_ref(v_a_2217_);
lean_inc(v_a_2216_);
lean_inc_ref(v_a_2215_);
lean_inc(v_a_2214_);
lean_inc_ref(v_a_2213_);
lean_inc(v_a_2212_);
lean_inc_ref(v_struct_2236_);
v___x_2541_ = lean_sym_simp(v_struct_2236_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_);
if (lean_obj_tag(v___x_2541_) == 0)
{
lean_object* v_a_2542_; 
v_a_2542_ = lean_ctor_get(v___x_2541_, 0);
lean_inc(v_a_2542_);
lean_dec_ref(v___x_2541_);
if (lean_obj_tag(v_a_2542_) == 0)
{
lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2561_; 
v_isSharedCheck_2561_ = !lean_is_exclusive(v_a_2542_);
if (v_isSharedCheck_2561_ == 0)
{
v___x_2544_ = v_a_2542_;
v_isShared_2545_ = v_isSharedCheck_2561_;
goto v_resetjp_2543_;
}
else
{
lean_dec(v_a_2542_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2561_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v___x_2546_; lean_object* v___x_2547_; 
v___x_2546_ = lean_alloc_closure((void*)(l_Lean_Meta_reduceProj_x3f___boxed), 6, 1);
lean_closure_set(v___x_2546_, 0, v_e_2211_);
lean_inc(v_a_2220_);
lean_inc_ref(v_a_2219_);
lean_inc(v_a_2218_);
lean_inc_ref(v_a_2217_);
v___x_2547_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___x_2546_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_);
if (lean_obj_tag(v___x_2547_) == 0)
{
lean_object* v_a_2548_; 
v_a_2548_ = lean_ctor_get(v___x_2547_, 0);
lean_inc(v_a_2548_);
lean_dec_ref(v___x_2547_);
if (lean_obj_tag(v_a_2548_) == 1)
{
lean_object* v_val_2549_; lean_object* v___x_2550_; 
lean_del_object(v___x_2544_);
v_val_2549_ = lean_ctor_get(v_a_2548_, 0);
lean_inc(v_val_2549_);
lean_dec_ref(v_a_2548_);
v___x_2550_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_val_2549_, v_a_2216_);
if (lean_obj_tag(v___x_2550_) == 0)
{
lean_object* v_a_2551_; lean_object* v___x_2552_; 
v_a_2551_ = lean_ctor_get(v___x_2550_, 0);
lean_inc(v_a_2551_);
lean_dec_ref(v___x_2550_);
lean_inc(v_a_2220_);
lean_inc_ref(v_a_2219_);
lean_inc(v_a_2218_);
lean_inc_ref(v_a_2217_);
lean_inc(v_a_2551_);
v___x_2552_ = l_Lean_Meta_Sym_mkEqRefl___redArg(v_a_2551_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_);
if (lean_obj_tag(v___x_2552_) == 0)
{
lean_object* v_a_2553_; lean_object* v___x_2554_; 
lean_del_object(v___x_2452_);
v_a_2553_ = lean_ctor_get(v___x_2552_, 0);
lean_inc(v_a_2553_);
lean_dec_ref(v___x_2552_);
v___x_2554_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_2554_, 0, v_a_2551_);
lean_ctor_set(v___x_2554_, 1, v_a_2553_);
lean_ctor_set_uint8(v___x_2554_, sizeof(void*)*2, v___x_2539_);
v___y_2480_ = v_a_2537_;
v___y_2481_ = v___x_2540_;
v_a_2482_ = v___x_2554_;
goto v___jp_2479_;
}
else
{
lean_object* v_a_2555_; 
lean_dec(v_a_2551_);
v_a_2555_ = lean_ctor_get(v___x_2552_, 0);
lean_inc(v_a_2555_);
lean_dec_ref(v___x_2552_);
v___y_2473_ = v_a_2537_;
v___y_2474_ = v___x_2540_;
v_a_2475_ = v_a_2555_;
goto v___jp_2472_;
}
}
else
{
lean_object* v_a_2556_; 
v_a_2556_ = lean_ctor_get(v___x_2550_, 0);
lean_inc(v_a_2556_);
lean_dec_ref(v___x_2550_);
v___y_2473_ = v_a_2537_;
v___y_2474_ = v___x_2540_;
v_a_2475_ = v_a_2556_;
goto v___jp_2472_;
}
}
else
{
lean_object* v___x_2558_; 
lean_dec(v_a_2548_);
lean_del_object(v___x_2452_);
if (v_isShared_2545_ == 0)
{
v___x_2558_ = v___x_2544_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(0, 0, 1);
v___x_2558_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
lean_ctor_set_uint8(v___x_2558_, 0, v_hasTrace_2445_);
v___y_2480_ = v_a_2537_;
v___y_2481_ = v___x_2540_;
v_a_2482_ = v___x_2558_;
goto v___jp_2479_;
}
}
}
else
{
lean_object* v_a_2560_; 
lean_del_object(v___x_2544_);
v_a_2560_ = lean_ctor_get(v___x_2547_, 0);
lean_inc(v_a_2560_);
lean_dec_ref(v___x_2547_);
v___y_2473_ = v_a_2537_;
v___y_2474_ = v___x_2540_;
v_a_2475_ = v_a_2560_;
goto v___jp_2472_;
}
}
}
else
{
lean_object* v_e_x27_2562_; lean_object* v_proof_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2617_; 
v_e_x27_2562_ = lean_ctor_get(v_a_2542_, 0);
v_proof_2563_ = lean_ctor_get(v_a_2542_, 1);
v_isSharedCheck_2617_ = !lean_is_exclusive(v_a_2542_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2565_ = v_a_2542_;
v_isShared_2566_ = v_isSharedCheck_2617_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_proof_2563_);
lean_inc(v_e_x27_2562_);
lean_dec(v_a_2542_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2617_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2567_; 
lean_inc(v_a_2220_);
lean_inc_ref(v_a_2219_);
lean_inc(v_a_2218_);
lean_inc_ref(v_a_2217_);
lean_inc_ref(v_e_x27_2562_);
v___x_2567_ = l_Lean_Meta_Sym_inferType___redArg(v_e_x27_2562_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_);
if (lean_obj_tag(v___x_2567_) == 0)
{
lean_object* v_a_2568_; lean_object* v___x_2569_; uint8_t v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
v_a_2568_ = lean_ctor_get(v___x_2567_, 0);
lean_inc(v_a_2568_);
lean_dec_ref(v___x_2567_);
v___x_2569_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2));
v___x_2570_ = 0;
v___x_2571_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__3, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__3_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__3);
lean_inc(v_idx_2235_);
lean_inc(v_typeName_2234_);
v___x_2572_ = l_Lean_Expr_proj___override(v_typeName_2234_, v_idx_2235_, v___x_2571_);
v___x_2573_ = l_Lean_mkLambda(v___x_2569_, v___x_2570_, v_a_2568_, v___x_2572_);
lean_inc(v_a_2220_);
lean_inc_ref(v_a_2219_);
lean_inc(v_a_2218_);
lean_inc_ref(v_a_2217_);
lean_inc_ref(v___x_2573_);
v___x_2574_ = lean_infer_type(v___x_2573_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_);
if (lean_obj_tag(v___x_2574_) == 0)
{
lean_object* v_a_2575_; uint8_t v___x_2576_; 
v_a_2575_ = lean_ctor_get(v___x_2574_, 0);
lean_inc(v_a_2575_);
lean_dec_ref(v___x_2574_);
v___x_2576_ = l_Lean_Expr_isArrow(v_a_2575_);
lean_dec(v_a_2575_);
if (v___x_2576_ == 0)
{
lean_object* v___x_2577_; lean_object* v___x_2578_; 
lean_inc_ref(v_e_2211_);
v___x_2577_ = lean_alloc_closure((void*)(l_Lean_Meta_reduceProj_x3f___boxed), 6, 1);
lean_closure_set(v___x_2577_, 0, v_e_2211_);
lean_inc(v_a_2220_);
lean_inc_ref(v_a_2219_);
lean_inc(v_a_2218_);
lean_inc_ref(v_a_2217_);
v___x_2578_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___x_2577_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_);
if (lean_obj_tag(v___x_2578_) == 0)
{
lean_object* v_a_2579_; 
v_a_2579_ = lean_ctor_get(v___x_2578_, 0);
lean_inc(v_a_2579_);
lean_dec_ref(v___x_2578_);
if (lean_obj_tag(v_a_2579_) == 0)
{
lean_object* v___x_2580_; 
lean_del_object(v___x_2565_);
lean_inc(v_a_2220_);
lean_inc_ref(v_a_2219_);
lean_inc(v_a_2218_);
lean_inc_ref(v_a_2217_);
lean_inc_ref(v_e_x27_2562_);
lean_inc_ref(v_struct_2236_);
v___x_2580_ = l_Lean_Meta_isExprDefEq(v_struct_2236_, v_e_x27_2562_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_);
if (lean_obj_tag(v___x_2580_) == 0)
{
lean_object* v_a_2581_; uint8_t v___x_2582_; 
v_a_2581_ = lean_ctor_get(v___x_2580_, 0);
lean_inc(v_a_2581_);
lean_dec_ref(v___x_2580_);
v___x_2582_ = lean_unbox(v_a_2581_);
lean_dec(v_a_2581_);
if (v___x_2582_ == 0)
{
lean_object* v___x_2583_; 
lean_dec_ref(v___x_2573_);
lean_dec_ref(v_proof_2563_);
lean_dec_ref(v_e_x27_2562_);
lean_del_object(v___x_2452_);
lean_dec_ref(v_e_2211_);
v___x_2583_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_2583_, 0, v_hasTrace_2445_);
v___y_2480_ = v_a_2537_;
v___y_2481_ = v___x_2540_;
v_a_2482_ = v___x_2583_;
goto v___jp_2479_;
}
else
{
lean_object* v___x_2584_; 
lean_inc(v_a_2220_);
lean_inc_ref(v_a_2219_);
lean_inc(v_a_2218_);
lean_inc_ref(v_a_2217_);
v___x_2584_ = l_Lean_Meta_mkHCongr(v___x_2573_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_);
if (lean_obj_tag(v___x_2584_) == 0)
{
lean_object* v_a_2585_; lean_object* v_proof_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; 
v_a_2585_ = lean_ctor_get(v___x_2584_, 0);
lean_inc(v_a_2585_);
lean_dec_ref(v___x_2584_);
v_proof_2586_ = lean_ctor_get(v_a_2585_, 1);
lean_inc_ref(v_proof_2586_);
lean_dec(v_a_2585_);
lean_inc_ref(v_e_x27_2562_);
lean_inc_ref(v_struct_2236_);
v___x_2587_ = l_Lean_mkApp3(v_proof_2586_, v_struct_2236_, v_e_x27_2562_, v_proof_2563_);
lean_inc(v_a_2220_);
lean_inc_ref(v_a_2219_);
lean_inc(v_a_2218_);
lean_inc_ref(v_a_2217_);
v___x_2588_ = l_Lean_Meta_mkEqOfHEq(v___x_2587_, v___x_2539_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_);
if (lean_obj_tag(v___x_2588_) == 0)
{
lean_object* v_a_2589_; uint8_t v___x_2590_; 
v_a_2589_ = lean_ctor_get(v___x_2588_, 0);
lean_inc(v_a_2589_);
lean_dec_ref(v___x_2588_);
v___x_2590_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_2236_, v_e_x27_2562_);
if (v___x_2590_ == 0)
{
lean_object* v___x_2591_; 
lean_inc(v_idx_2235_);
lean_inc(v_typeName_2234_);
lean_dec_ref(v_e_2211_);
lean_inc(v_a_2220_);
lean_inc_ref(v_a_2219_);
lean_inc(v_a_2218_);
lean_inc_ref(v_a_2217_);
lean_inc(v_a_2216_);
lean_inc_ref(v_a_2215_);
v___x_2591_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_typeName_2234_, v_idx_2235_, v_e_x27_2562_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_object* v_a_2592_; 
lean_del_object(v___x_2452_);
v_a_2592_ = lean_ctor_get(v___x_2591_, 0);
lean_inc(v_a_2592_);
lean_dec_ref(v___x_2591_);
v___y_2485_ = v_a_2537_;
v___y_2486_ = v_a_2589_;
v___y_2487_ = v___x_2539_;
v___y_2488_ = v___x_2540_;
v_a_2489_ = v_a_2592_;
goto v___jp_2484_;
}
else
{
lean_object* v_a_2593_; 
lean_dec(v_a_2589_);
v_a_2593_ = lean_ctor_get(v___x_2591_, 0);
lean_inc(v_a_2593_);
lean_dec_ref(v___x_2591_);
v___y_2473_ = v_a_2537_;
v___y_2474_ = v___x_2540_;
v_a_2475_ = v_a_2593_;
goto v___jp_2472_;
}
}
else
{
lean_dec_ref(v_e_x27_2562_);
lean_del_object(v___x_2452_);
v___y_2485_ = v_a_2537_;
v___y_2486_ = v_a_2589_;
v___y_2487_ = v___x_2539_;
v___y_2488_ = v___x_2540_;
v_a_2489_ = v_e_2211_;
goto v___jp_2484_;
}
}
else
{
lean_object* v_a_2594_; 
lean_dec_ref(v_e_x27_2562_);
lean_dec_ref(v_e_2211_);
v_a_2594_ = lean_ctor_get(v___x_2588_, 0);
lean_inc(v_a_2594_);
lean_dec_ref(v___x_2588_);
v___y_2473_ = v_a_2537_;
v___y_2474_ = v___x_2540_;
v_a_2475_ = v_a_2594_;
goto v___jp_2472_;
}
}
else
{
lean_object* v_a_2595_; 
lean_dec_ref(v_proof_2563_);
lean_dec_ref(v_e_x27_2562_);
lean_dec_ref(v_e_2211_);
v_a_2595_ = lean_ctor_get(v___x_2584_, 0);
lean_inc(v_a_2595_);
lean_dec_ref(v___x_2584_);
v___y_2473_ = v_a_2537_;
v___y_2474_ = v___x_2540_;
v_a_2475_ = v_a_2595_;
goto v___jp_2472_;
}
}
}
else
{
lean_object* v_a_2596_; 
lean_dec_ref(v___x_2573_);
lean_dec_ref(v_proof_2563_);
lean_dec_ref(v_e_x27_2562_);
lean_dec_ref(v_e_2211_);
v_a_2596_ = lean_ctor_get(v___x_2580_, 0);
lean_inc(v_a_2596_);
lean_dec_ref(v___x_2580_);
v___y_2473_ = v_a_2537_;
v___y_2474_ = v___x_2540_;
v_a_2475_ = v_a_2596_;
goto v___jp_2472_;
}
}
else
{
lean_object* v_val_2597_; lean_object* v___x_2598_; 
lean_dec_ref(v___x_2573_);
lean_dec_ref(v_proof_2563_);
lean_dec_ref(v_e_x27_2562_);
lean_dec_ref(v_e_2211_);
v_val_2597_ = lean_ctor_get(v_a_2579_, 0);
lean_inc(v_val_2597_);
lean_dec_ref(v_a_2579_);
v___x_2598_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_val_2597_, v_a_2216_);
if (lean_obj_tag(v___x_2598_) == 0)
{
lean_object* v_a_2599_; lean_object* v___x_2600_; 
v_a_2599_ = lean_ctor_get(v___x_2598_, 0);
lean_inc(v_a_2599_);
lean_dec_ref(v___x_2598_);
lean_inc(v_a_2220_);
lean_inc_ref(v_a_2219_);
lean_inc(v_a_2218_);
lean_inc_ref(v_a_2217_);
lean_inc(v_a_2599_);
v___x_2600_ = l_Lean_Meta_Sym_mkEqRefl___redArg(v_a_2599_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_);
if (lean_obj_tag(v___x_2600_) == 0)
{
lean_object* v_a_2601_; lean_object* v___x_2603_; 
lean_del_object(v___x_2452_);
v_a_2601_ = lean_ctor_get(v___x_2600_, 0);
lean_inc(v_a_2601_);
lean_dec_ref(v___x_2600_);
if (v_isShared_2566_ == 0)
{
lean_ctor_set(v___x_2565_, 1, v_a_2601_);
lean_ctor_set(v___x_2565_, 0, v_a_2599_);
v___x_2603_ = v___x_2565_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_a_2599_);
lean_ctor_set(v_reuseFailAlloc_2604_, 1, v_a_2601_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
lean_ctor_set_uint8(v___x_2603_, sizeof(void*)*2, v___x_2539_);
v___y_2480_ = v_a_2537_;
v___y_2481_ = v___x_2540_;
v_a_2482_ = v___x_2603_;
goto v___jp_2479_;
}
}
else
{
lean_object* v_a_2605_; 
lean_dec(v_a_2599_);
lean_del_object(v___x_2565_);
v_a_2605_ = lean_ctor_get(v___x_2600_, 0);
lean_inc(v_a_2605_);
lean_dec_ref(v___x_2600_);
v___y_2473_ = v_a_2537_;
v___y_2474_ = v___x_2540_;
v_a_2475_ = v_a_2605_;
goto v___jp_2472_;
}
}
else
{
lean_object* v_a_2606_; 
lean_del_object(v___x_2565_);
v_a_2606_ = lean_ctor_get(v___x_2598_, 0);
lean_inc(v_a_2606_);
lean_dec_ref(v___x_2598_);
v___y_2473_ = v_a_2537_;
v___y_2474_ = v___x_2540_;
v_a_2475_ = v_a_2606_;
goto v___jp_2472_;
}
}
}
else
{
lean_object* v_a_2607_; 
lean_dec_ref(v___x_2573_);
lean_del_object(v___x_2565_);
lean_dec_ref(v_proof_2563_);
lean_dec_ref(v_e_x27_2562_);
lean_dec_ref(v_e_2211_);
v_a_2607_ = lean_ctor_get(v___x_2578_, 0);
lean_inc(v_a_2607_);
lean_dec_ref(v___x_2578_);
v___y_2473_ = v_a_2537_;
v___y_2474_ = v___x_2540_;
v_a_2475_ = v_a_2607_;
goto v___jp_2472_;
}
}
else
{
lean_object* v___x_2608_; 
lean_del_object(v___x_2565_);
lean_inc(v_a_2220_);
lean_inc_ref(v_a_2219_);
lean_inc(v_a_2218_);
lean_inc_ref(v_a_2217_);
v___x_2608_ = l_Lean_Meta_mkCongrArg(v___x_2573_, v_proof_2563_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_);
if (lean_obj_tag(v___x_2608_) == 0)
{
lean_object* v_a_2609_; uint8_t v___x_2610_; 
v_a_2609_ = lean_ctor_get(v___x_2608_, 0);
lean_inc(v_a_2609_);
lean_dec_ref(v___x_2608_);
v___x_2610_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_2236_, v_e_x27_2562_);
if (v___x_2610_ == 0)
{
lean_object* v___x_2611_; 
lean_inc(v_idx_2235_);
lean_inc(v_typeName_2234_);
lean_dec_ref(v_e_2211_);
lean_inc(v_a_2220_);
lean_inc_ref(v_a_2219_);
lean_inc(v_a_2218_);
lean_inc_ref(v_a_2217_);
lean_inc(v_a_2216_);
lean_inc_ref(v_a_2215_);
v___x_2611_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_typeName_2234_, v_idx_2235_, v_e_x27_2562_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_);
if (lean_obj_tag(v___x_2611_) == 0)
{
lean_object* v_a_2612_; 
lean_del_object(v___x_2452_);
v_a_2612_ = lean_ctor_get(v___x_2611_, 0);
lean_inc(v_a_2612_);
lean_dec_ref(v___x_2611_);
v___y_2492_ = v_a_2537_;
v___y_2493_ = v___x_2539_;
v___y_2494_ = v_a_2609_;
v___y_2495_ = v___x_2540_;
v_a_2496_ = v_a_2612_;
goto v___jp_2491_;
}
else
{
lean_object* v_a_2613_; 
lean_dec(v_a_2609_);
v_a_2613_ = lean_ctor_get(v___x_2611_, 0);
lean_inc(v_a_2613_);
lean_dec_ref(v___x_2611_);
v___y_2473_ = v_a_2537_;
v___y_2474_ = v___x_2540_;
v_a_2475_ = v_a_2613_;
goto v___jp_2472_;
}
}
else
{
lean_dec_ref(v_e_x27_2562_);
lean_del_object(v___x_2452_);
v___y_2492_ = v_a_2537_;
v___y_2493_ = v___x_2539_;
v___y_2494_ = v_a_2609_;
v___y_2495_ = v___x_2540_;
v_a_2496_ = v_e_2211_;
goto v___jp_2491_;
}
}
else
{
lean_object* v_a_2614_; 
lean_dec_ref(v_e_x27_2562_);
lean_dec_ref(v_e_2211_);
v_a_2614_ = lean_ctor_get(v___x_2608_, 0);
lean_inc(v_a_2614_);
lean_dec_ref(v___x_2608_);
v___y_2473_ = v_a_2537_;
v___y_2474_ = v___x_2540_;
v_a_2475_ = v_a_2614_;
goto v___jp_2472_;
}
}
}
else
{
lean_object* v_a_2615_; 
lean_dec_ref(v___x_2573_);
lean_del_object(v___x_2565_);
lean_dec_ref(v_proof_2563_);
lean_dec_ref(v_e_x27_2562_);
lean_dec_ref(v_e_2211_);
v_a_2615_ = lean_ctor_get(v___x_2574_, 0);
lean_inc(v_a_2615_);
lean_dec_ref(v___x_2574_);
v___y_2473_ = v_a_2537_;
v___y_2474_ = v___x_2540_;
v_a_2475_ = v_a_2615_;
goto v___jp_2472_;
}
}
else
{
lean_object* v_a_2616_; 
lean_del_object(v___x_2565_);
lean_dec_ref(v_proof_2563_);
lean_dec_ref(v_e_x27_2562_);
lean_dec_ref(v_e_2211_);
v_a_2616_ = lean_ctor_get(v___x_2567_, 0);
lean_inc(v_a_2616_);
lean_dec_ref(v___x_2567_);
v___y_2473_ = v_a_2537_;
v___y_2474_ = v___x_2540_;
v_a_2475_ = v_a_2616_;
goto v___jp_2472_;
}
}
}
}
else
{
lean_dec_ref(v_e_2211_);
if (lean_obj_tag(v___x_2541_) == 0)
{
lean_object* v_a_2618_; 
lean_del_object(v___x_2452_);
v_a_2618_ = lean_ctor_get(v___x_2541_, 0);
lean_inc(v_a_2618_);
lean_dec_ref(v___x_2541_);
v___y_2480_ = v_a_2537_;
v___y_2481_ = v___x_2540_;
v_a_2482_ = v_a_2618_;
goto v___jp_2479_;
}
else
{
lean_object* v_a_2619_; 
v_a_2619_ = lean_ctor_get(v___x_2541_, 0);
lean_inc(v_a_2619_);
lean_dec_ref(v___x_2541_);
v___y_2473_ = v_a_2537_;
v___y_2474_ = v___x_2540_;
v_a_2475_ = v_a_2619_;
goto v___jp_2472_;
}
}
}
else
{
lean_object* v___x_2620_; lean_object* v___x_2621_; 
lean_del_object(v___x_2452_);
v___x_2620_ = lean_io_get_num_heartbeats();
lean_inc(v_a_2220_);
lean_inc_ref(v_a_2219_);
lean_inc(v_a_2218_);
lean_inc_ref(v_a_2217_);
lean_inc(v_a_2216_);
lean_inc_ref(v_a_2215_);
lean_inc(v_a_2214_);
lean_inc_ref(v_a_2213_);
lean_inc(v_a_2212_);
lean_inc_ref(v_struct_2236_);
v___x_2621_ = lean_sym_simp(v_struct_2236_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_);
if (lean_obj_tag(v___x_2621_) == 0)
{
lean_object* v_a_2622_; 
v_a_2622_ = lean_ctor_get(v___x_2621_, 0);
lean_inc(v_a_2622_);
lean_dec_ref(v___x_2621_);
if (lean_obj_tag(v_a_2622_) == 0)
{
lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2642_; 
v_isSharedCheck_2642_ = !lean_is_exclusive(v_a_2622_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2624_ = v_a_2622_;
v_isShared_2625_ = v_isSharedCheck_2642_;
goto v_resetjp_2623_;
}
else
{
lean_dec(v_a_2622_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2642_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v___x_2626_; lean_object* v___x_2627_; 
v___x_2626_ = lean_alloc_closure((void*)(l_Lean_Meta_reduceProj_x3f___boxed), 6, 1);
lean_closure_set(v___x_2626_, 0, v_e_2211_);
lean_inc(v_a_2220_);
lean_inc_ref(v_a_2219_);
lean_inc(v_a_2218_);
lean_inc_ref(v_a_2217_);
v___x_2627_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___x_2626_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_);
if (lean_obj_tag(v___x_2627_) == 0)
{
lean_object* v_a_2628_; 
v_a_2628_ = lean_ctor_get(v___x_2627_, 0);
lean_inc(v_a_2628_);
lean_dec_ref(v___x_2627_);
if (lean_obj_tag(v_a_2628_) == 1)
{
lean_object* v_val_2629_; lean_object* v___x_2630_; 
lean_del_object(v___x_2624_);
v_val_2629_ = lean_ctor_get(v_a_2628_, 0);
lean_inc(v_val_2629_);
lean_dec_ref(v_a_2628_);
v___x_2630_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_val_2629_, v_a_2216_);
if (lean_obj_tag(v___x_2630_) == 0)
{
lean_object* v_a_2631_; lean_object* v___x_2632_; 
v_a_2631_ = lean_ctor_get(v___x_2630_, 0);
lean_inc(v_a_2631_);
lean_dec_ref(v___x_2630_);
lean_inc(v_a_2220_);
lean_inc_ref(v_a_2219_);
lean_inc(v_a_2218_);
lean_inc_ref(v_a_2217_);
lean_inc(v_a_2631_);
v___x_2632_ = l_Lean_Meta_Sym_mkEqRefl___redArg(v_a_2631_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_);
if (lean_obj_tag(v___x_2632_) == 0)
{
lean_object* v_a_2633_; uint8_t v___x_2634_; lean_object* v___x_2635_; 
v_a_2633_ = lean_ctor_get(v___x_2632_, 0);
lean_inc(v_a_2633_);
lean_dec_ref(v___x_2632_);
v___x_2634_ = 0;
v___x_2635_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_2635_, 0, v_a_2631_);
lean_ctor_set(v___x_2635_, 1, v_a_2633_);
lean_ctor_set_uint8(v___x_2635_, sizeof(void*)*2, v___x_2634_);
v___y_2517_ = v_a_2537_;
v___y_2518_ = v___x_2620_;
v_a_2519_ = v___x_2635_;
goto v___jp_2516_;
}
else
{
lean_object* v_a_2636_; 
lean_dec(v_a_2631_);
v_a_2636_ = lean_ctor_get(v___x_2632_, 0);
lean_inc(v_a_2636_);
lean_dec_ref(v___x_2632_);
v___y_2512_ = v_a_2537_;
v___y_2513_ = v___x_2620_;
v_a_2514_ = v_a_2636_;
goto v___jp_2511_;
}
}
else
{
lean_object* v_a_2637_; 
v_a_2637_ = lean_ctor_get(v___x_2630_, 0);
lean_inc(v_a_2637_);
lean_dec_ref(v___x_2630_);
v___y_2512_ = v_a_2537_;
v___y_2513_ = v___x_2620_;
v_a_2514_ = v_a_2637_;
goto v___jp_2511_;
}
}
else
{
lean_object* v___x_2639_; 
lean_dec(v_a_2628_);
if (v_isShared_2625_ == 0)
{
v___x_2639_ = v___x_2624_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(0, 0, 1);
v___x_2639_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
lean_ctor_set_uint8(v___x_2639_, 0, v___x_2539_);
v___y_2517_ = v_a_2537_;
v___y_2518_ = v___x_2620_;
v_a_2519_ = v___x_2639_;
goto v___jp_2516_;
}
}
}
else
{
lean_object* v_a_2641_; 
lean_del_object(v___x_2624_);
v_a_2641_ = lean_ctor_get(v___x_2627_, 0);
lean_inc(v_a_2641_);
lean_dec_ref(v___x_2627_);
v___y_2512_ = v_a_2537_;
v___y_2513_ = v___x_2620_;
v_a_2514_ = v_a_2641_;
goto v___jp_2511_;
}
}
}
else
{
lean_object* v_e_x27_2643_; lean_object* v_proof_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2698_; 
v_e_x27_2643_ = lean_ctor_get(v_a_2622_, 0);
v_proof_2644_ = lean_ctor_get(v_a_2622_, 1);
v_isSharedCheck_2698_ = !lean_is_exclusive(v_a_2622_);
if (v_isSharedCheck_2698_ == 0)
{
v___x_2646_ = v_a_2622_;
v_isShared_2647_ = v_isSharedCheck_2698_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_proof_2644_);
lean_inc(v_e_x27_2643_);
lean_dec(v_a_2622_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2698_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2648_; 
lean_inc(v_a_2220_);
lean_inc_ref(v_a_2219_);
lean_inc(v_a_2218_);
lean_inc_ref(v_a_2217_);
lean_inc_ref(v_e_x27_2643_);
v___x_2648_ = l_Lean_Meta_Sym_inferType___redArg(v_e_x27_2643_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_);
if (lean_obj_tag(v___x_2648_) == 0)
{
lean_object* v_a_2649_; lean_object* v___x_2650_; uint8_t v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; 
v_a_2649_ = lean_ctor_get(v___x_2648_, 0);
lean_inc(v_a_2649_);
lean_dec_ref(v___x_2648_);
v___x_2650_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2));
v___x_2651_ = 0;
v___x_2652_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__3, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__3_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__3);
lean_inc(v_idx_2235_);
lean_inc(v_typeName_2234_);
v___x_2653_ = l_Lean_Expr_proj___override(v_typeName_2234_, v_idx_2235_, v___x_2652_);
v___x_2654_ = l_Lean_mkLambda(v___x_2650_, v___x_2651_, v_a_2649_, v___x_2653_);
lean_inc(v_a_2220_);
lean_inc_ref(v_a_2219_);
lean_inc(v_a_2218_);
lean_inc_ref(v_a_2217_);
lean_inc_ref(v___x_2654_);
v___x_2655_ = lean_infer_type(v___x_2654_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_);
if (lean_obj_tag(v___x_2655_) == 0)
{
lean_object* v_a_2656_; uint8_t v___x_2657_; 
v_a_2656_ = lean_ctor_get(v___x_2655_, 0);
lean_inc(v_a_2656_);
lean_dec_ref(v___x_2655_);
v___x_2657_ = l_Lean_Expr_isArrow(v_a_2656_);
lean_dec(v_a_2656_);
if (v___x_2657_ == 0)
{
lean_object* v___x_2658_; lean_object* v___x_2659_; 
lean_inc_ref(v_e_2211_);
v___x_2658_ = lean_alloc_closure((void*)(l_Lean_Meta_reduceProj_x3f___boxed), 6, 1);
lean_closure_set(v___x_2658_, 0, v_e_2211_);
lean_inc(v_a_2220_);
lean_inc_ref(v_a_2219_);
lean_inc(v_a_2218_);
lean_inc_ref(v_a_2217_);
v___x_2659_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___x_2658_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_);
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_object* v_a_2660_; 
v_a_2660_ = lean_ctor_get(v___x_2659_, 0);
lean_inc(v_a_2660_);
lean_dec_ref(v___x_2659_);
if (lean_obj_tag(v_a_2660_) == 0)
{
lean_object* v___x_2661_; 
lean_del_object(v___x_2646_);
lean_inc(v_a_2220_);
lean_inc_ref(v_a_2219_);
lean_inc(v_a_2218_);
lean_inc_ref(v_a_2217_);
lean_inc_ref(v_e_x27_2643_);
lean_inc_ref(v_struct_2236_);
v___x_2661_ = l_Lean_Meta_isExprDefEq(v_struct_2236_, v_e_x27_2643_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_);
if (lean_obj_tag(v___x_2661_) == 0)
{
lean_object* v_a_2662_; uint8_t v___x_2663_; 
v_a_2662_ = lean_ctor_get(v___x_2661_, 0);
lean_inc(v_a_2662_);
lean_dec_ref(v___x_2661_);
v___x_2663_ = lean_unbox(v_a_2662_);
lean_dec(v_a_2662_);
if (v___x_2663_ == 0)
{
lean_object* v___x_2664_; 
lean_dec_ref(v___x_2654_);
lean_dec_ref(v_proof_2644_);
lean_dec_ref(v_e_x27_2643_);
lean_dec_ref(v_e_2211_);
v___x_2664_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_2664_, 0, v___x_2539_);
v___y_2517_ = v_a_2537_;
v___y_2518_ = v___x_2620_;
v_a_2519_ = v___x_2664_;
goto v___jp_2516_;
}
else
{
lean_object* v___x_2665_; 
lean_inc(v_a_2220_);
lean_inc_ref(v_a_2219_);
lean_inc(v_a_2218_);
lean_inc_ref(v_a_2217_);
v___x_2665_ = l_Lean_Meta_mkHCongr(v___x_2654_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_);
if (lean_obj_tag(v___x_2665_) == 0)
{
lean_object* v_a_2666_; lean_object* v_proof_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; 
v_a_2666_ = lean_ctor_get(v___x_2665_, 0);
lean_inc(v_a_2666_);
lean_dec_ref(v___x_2665_);
v_proof_2667_ = lean_ctor_get(v_a_2666_, 1);
lean_inc_ref(v_proof_2667_);
lean_dec(v_a_2666_);
lean_inc_ref(v_e_x27_2643_);
lean_inc_ref(v_struct_2236_);
v___x_2668_ = l_Lean_mkApp3(v_proof_2667_, v_struct_2236_, v_e_x27_2643_, v_proof_2644_);
lean_inc(v_a_2220_);
lean_inc_ref(v_a_2219_);
lean_inc(v_a_2218_);
lean_inc_ref(v_a_2217_);
v___x_2669_ = l_Lean_Meta_mkEqOfHEq(v___x_2668_, v___x_2657_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_);
if (lean_obj_tag(v___x_2669_) == 0)
{
lean_object* v_a_2670_; uint8_t v___x_2671_; 
v_a_2670_ = lean_ctor_get(v___x_2669_, 0);
lean_inc(v_a_2670_);
lean_dec_ref(v___x_2669_);
v___x_2671_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_2236_, v_e_x27_2643_);
if (v___x_2671_ == 0)
{
lean_object* v___x_2672_; 
lean_inc(v_idx_2235_);
lean_inc(v_typeName_2234_);
lean_dec_ref(v_e_2211_);
lean_inc(v_a_2220_);
lean_inc_ref(v_a_2219_);
lean_inc(v_a_2218_);
lean_inc_ref(v_a_2217_);
lean_inc(v_a_2216_);
lean_inc_ref(v_a_2215_);
v___x_2672_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_typeName_2234_, v_idx_2235_, v_e_x27_2643_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_);
if (lean_obj_tag(v___x_2672_) == 0)
{
lean_object* v_a_2673_; 
v_a_2673_ = lean_ctor_get(v___x_2672_, 0);
lean_inc(v_a_2673_);
lean_dec_ref(v___x_2672_);
v___y_2522_ = v_a_2537_;
v___y_2523_ = v_a_2670_;
v___y_2524_ = v___x_2657_;
v___y_2525_ = v___x_2620_;
v_a_2526_ = v_a_2673_;
goto v___jp_2521_;
}
else
{
lean_object* v_a_2674_; 
lean_dec(v_a_2670_);
v_a_2674_ = lean_ctor_get(v___x_2672_, 0);
lean_inc(v_a_2674_);
lean_dec_ref(v___x_2672_);
v___y_2512_ = v_a_2537_;
v___y_2513_ = v___x_2620_;
v_a_2514_ = v_a_2674_;
goto v___jp_2511_;
}
}
else
{
lean_dec_ref(v_e_x27_2643_);
v___y_2522_ = v_a_2537_;
v___y_2523_ = v_a_2670_;
v___y_2524_ = v___x_2657_;
v___y_2525_ = v___x_2620_;
v_a_2526_ = v_e_2211_;
goto v___jp_2521_;
}
}
else
{
lean_object* v_a_2675_; 
lean_dec_ref(v_e_x27_2643_);
lean_dec_ref(v_e_2211_);
v_a_2675_ = lean_ctor_get(v___x_2669_, 0);
lean_inc(v_a_2675_);
lean_dec_ref(v___x_2669_);
v___y_2512_ = v_a_2537_;
v___y_2513_ = v___x_2620_;
v_a_2514_ = v_a_2675_;
goto v___jp_2511_;
}
}
else
{
lean_object* v_a_2676_; 
lean_dec_ref(v_proof_2644_);
lean_dec_ref(v_e_x27_2643_);
lean_dec_ref(v_e_2211_);
v_a_2676_ = lean_ctor_get(v___x_2665_, 0);
lean_inc(v_a_2676_);
lean_dec_ref(v___x_2665_);
v___y_2512_ = v_a_2537_;
v___y_2513_ = v___x_2620_;
v_a_2514_ = v_a_2676_;
goto v___jp_2511_;
}
}
}
else
{
lean_object* v_a_2677_; 
lean_dec_ref(v___x_2654_);
lean_dec_ref(v_proof_2644_);
lean_dec_ref(v_e_x27_2643_);
lean_dec_ref(v_e_2211_);
v_a_2677_ = lean_ctor_get(v___x_2661_, 0);
lean_inc(v_a_2677_);
lean_dec_ref(v___x_2661_);
v___y_2512_ = v_a_2537_;
v___y_2513_ = v___x_2620_;
v_a_2514_ = v_a_2677_;
goto v___jp_2511_;
}
}
else
{
lean_object* v_val_2678_; lean_object* v___x_2679_; 
lean_dec_ref(v___x_2654_);
lean_dec_ref(v_proof_2644_);
lean_dec_ref(v_e_x27_2643_);
lean_dec_ref(v_e_2211_);
v_val_2678_ = lean_ctor_get(v_a_2660_, 0);
lean_inc(v_val_2678_);
lean_dec_ref(v_a_2660_);
v___x_2679_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_val_2678_, v_a_2216_);
if (lean_obj_tag(v___x_2679_) == 0)
{
lean_object* v_a_2680_; lean_object* v___x_2681_; 
v_a_2680_ = lean_ctor_get(v___x_2679_, 0);
lean_inc(v_a_2680_);
lean_dec_ref(v___x_2679_);
lean_inc(v_a_2220_);
lean_inc_ref(v_a_2219_);
lean_inc(v_a_2218_);
lean_inc_ref(v_a_2217_);
lean_inc(v_a_2680_);
v___x_2681_ = l_Lean_Meta_Sym_mkEqRefl___redArg(v_a_2680_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_);
if (lean_obj_tag(v___x_2681_) == 0)
{
lean_object* v_a_2682_; lean_object* v___x_2684_; 
v_a_2682_ = lean_ctor_get(v___x_2681_, 0);
lean_inc(v_a_2682_);
lean_dec_ref(v___x_2681_);
if (v_isShared_2647_ == 0)
{
lean_ctor_set(v___x_2646_, 1, v_a_2682_);
lean_ctor_set(v___x_2646_, 0, v_a_2680_);
v___x_2684_ = v___x_2646_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v_a_2680_);
lean_ctor_set(v_reuseFailAlloc_2685_, 1, v_a_2682_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
lean_ctor_set_uint8(v___x_2684_, sizeof(void*)*2, v___x_2657_);
v___y_2517_ = v_a_2537_;
v___y_2518_ = v___x_2620_;
v_a_2519_ = v___x_2684_;
goto v___jp_2516_;
}
}
else
{
lean_object* v_a_2686_; 
lean_dec(v_a_2680_);
lean_del_object(v___x_2646_);
v_a_2686_ = lean_ctor_get(v___x_2681_, 0);
lean_inc(v_a_2686_);
lean_dec_ref(v___x_2681_);
v___y_2512_ = v_a_2537_;
v___y_2513_ = v___x_2620_;
v_a_2514_ = v_a_2686_;
goto v___jp_2511_;
}
}
else
{
lean_object* v_a_2687_; 
lean_del_object(v___x_2646_);
v_a_2687_ = lean_ctor_get(v___x_2679_, 0);
lean_inc(v_a_2687_);
lean_dec_ref(v___x_2679_);
v___y_2512_ = v_a_2537_;
v___y_2513_ = v___x_2620_;
v_a_2514_ = v_a_2687_;
goto v___jp_2511_;
}
}
}
else
{
lean_object* v_a_2688_; 
lean_dec_ref(v___x_2654_);
lean_del_object(v___x_2646_);
lean_dec_ref(v_proof_2644_);
lean_dec_ref(v_e_x27_2643_);
lean_dec_ref(v_e_2211_);
v_a_2688_ = lean_ctor_get(v___x_2659_, 0);
lean_inc(v_a_2688_);
lean_dec_ref(v___x_2659_);
v___y_2512_ = v_a_2537_;
v___y_2513_ = v___x_2620_;
v_a_2514_ = v_a_2688_;
goto v___jp_2511_;
}
}
else
{
lean_object* v___x_2689_; 
lean_del_object(v___x_2646_);
lean_inc(v_a_2220_);
lean_inc_ref(v_a_2219_);
lean_inc(v_a_2218_);
lean_inc_ref(v_a_2217_);
v___x_2689_ = l_Lean_Meta_mkCongrArg(v___x_2654_, v_proof_2644_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_);
if (lean_obj_tag(v___x_2689_) == 0)
{
lean_object* v_a_2690_; uint8_t v___x_2691_; 
v_a_2690_ = lean_ctor_get(v___x_2689_, 0);
lean_inc(v_a_2690_);
lean_dec_ref(v___x_2689_);
v___x_2691_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_2236_, v_e_x27_2643_);
if (v___x_2691_ == 0)
{
lean_object* v___x_2692_; 
lean_inc(v_idx_2235_);
lean_inc(v_typeName_2234_);
lean_dec_ref(v_e_2211_);
lean_inc(v_a_2220_);
lean_inc_ref(v_a_2219_);
lean_inc(v_a_2218_);
lean_inc_ref(v_a_2217_);
lean_inc(v_a_2216_);
lean_inc_ref(v_a_2215_);
v___x_2692_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_typeName_2234_, v_idx_2235_, v_e_x27_2643_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_);
if (lean_obj_tag(v___x_2692_) == 0)
{
lean_object* v_a_2693_; 
v_a_2693_ = lean_ctor_get(v___x_2692_, 0);
lean_inc(v_a_2693_);
lean_dec_ref(v___x_2692_);
v___y_2529_ = v_a_2537_;
v___y_2530_ = v_a_2690_;
v___y_2531_ = v___x_2620_;
v_a_2532_ = v_a_2693_;
goto v___jp_2528_;
}
else
{
lean_object* v_a_2694_; 
lean_dec(v_a_2690_);
v_a_2694_ = lean_ctor_get(v___x_2692_, 0);
lean_inc(v_a_2694_);
lean_dec_ref(v___x_2692_);
v___y_2512_ = v_a_2537_;
v___y_2513_ = v___x_2620_;
v_a_2514_ = v_a_2694_;
goto v___jp_2511_;
}
}
else
{
lean_dec_ref(v_e_x27_2643_);
v___y_2529_ = v_a_2537_;
v___y_2530_ = v_a_2690_;
v___y_2531_ = v___x_2620_;
v_a_2532_ = v_e_2211_;
goto v___jp_2528_;
}
}
else
{
lean_object* v_a_2695_; 
lean_dec_ref(v_e_x27_2643_);
lean_dec_ref(v_e_2211_);
v_a_2695_ = lean_ctor_get(v___x_2689_, 0);
lean_inc(v_a_2695_);
lean_dec_ref(v___x_2689_);
v___y_2512_ = v_a_2537_;
v___y_2513_ = v___x_2620_;
v_a_2514_ = v_a_2695_;
goto v___jp_2511_;
}
}
}
else
{
lean_object* v_a_2696_; 
lean_dec_ref(v___x_2654_);
lean_del_object(v___x_2646_);
lean_dec_ref(v_proof_2644_);
lean_dec_ref(v_e_x27_2643_);
lean_dec_ref(v_e_2211_);
v_a_2696_ = lean_ctor_get(v___x_2655_, 0);
lean_inc(v_a_2696_);
lean_dec_ref(v___x_2655_);
v___y_2512_ = v_a_2537_;
v___y_2513_ = v___x_2620_;
v_a_2514_ = v_a_2696_;
goto v___jp_2511_;
}
}
else
{
lean_object* v_a_2697_; 
lean_del_object(v___x_2646_);
lean_dec_ref(v_proof_2644_);
lean_dec_ref(v_e_x27_2643_);
lean_dec_ref(v_e_2211_);
v_a_2697_ = lean_ctor_get(v___x_2648_, 0);
lean_inc(v_a_2697_);
lean_dec_ref(v___x_2648_);
v___y_2512_ = v_a_2537_;
v___y_2513_ = v___x_2620_;
v_a_2514_ = v_a_2697_;
goto v___jp_2511_;
}
}
}
}
else
{
lean_dec_ref(v_e_2211_);
if (lean_obj_tag(v___x_2621_) == 0)
{
lean_object* v_a_2699_; 
v_a_2699_ = lean_ctor_get(v___x_2621_, 0);
lean_inc(v_a_2699_);
lean_dec_ref(v___x_2621_);
v___y_2517_ = v_a_2537_;
v___y_2518_ = v___x_2620_;
v_a_2519_ = v_a_2699_;
goto v___jp_2516_;
}
else
{
lean_object* v_a_2700_; 
v_a_2700_ = lean_ctor_get(v___x_2621_, 0);
lean_inc(v_a_2700_);
lean_dec_ref(v___x_2621_);
v___y_2512_ = v_a_2537_;
v___y_2513_ = v___x_2620_;
v_a_2514_ = v_a_2700_;
goto v___jp_2511_;
}
}
}
}
}
}
v___jp_2237_:
{
lean_dec(v___y_2241_);
lean_dec_ref(v___y_2240_);
lean_dec(v___y_2239_);
if (lean_obj_tag(v_res_2238_) == 0)
{
lean_object* v___x_2248_; lean_object* v___x_2249_; 
lean_dec_ref(v_res_2238_);
lean_dec_ref(v___y_2242_);
v___x_2248_ = lean_alloc_closure((void*)(l_Lean_Meta_reduceProj_x3f___boxed), 6, 1);
lean_closure_set(v___x_2248_, 0, v_e_2211_);
lean_inc(v___y_2247_);
lean_inc_ref(v___y_2246_);
lean_inc(v___y_2245_);
lean_inc_ref(v___y_2244_);
v___x_2249_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___x_2248_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
if (lean_obj_tag(v___x_2249_) == 0)
{
lean_object* v_a_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2288_; 
v_a_2250_ = lean_ctor_get(v___x_2249_, 0);
v_isSharedCheck_2288_ = !lean_is_exclusive(v___x_2249_);
if (v_isSharedCheck_2288_ == 0)
{
v___x_2252_ = v___x_2249_;
v_isShared_2253_ = v_isSharedCheck_2288_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_a_2250_);
lean_dec(v___x_2249_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2288_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
if (lean_obj_tag(v_a_2250_) == 1)
{
lean_object* v_val_2254_; lean_object* v___x_2255_; 
lean_del_object(v___x_2252_);
v_val_2254_ = lean_ctor_get(v_a_2250_, 0);
lean_inc(v_val_2254_);
lean_dec_ref(v_a_2250_);
v___x_2255_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_val_2254_, v___y_2243_);
if (lean_obj_tag(v___x_2255_) == 0)
{
lean_object* v_a_2256_; lean_object* v___x_2257_; 
v_a_2256_ = lean_ctor_get(v___x_2255_, 0);
lean_inc(v_a_2256_);
lean_dec_ref(v___x_2255_);
lean_inc(v_a_2256_);
v___x_2257_ = l_Lean_Meta_Sym_mkEqRefl___redArg(v_a_2256_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
lean_dec(v___y_2243_);
if (lean_obj_tag(v___x_2257_) == 0)
{
lean_object* v_a_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2267_; 
v_a_2258_ = lean_ctor_get(v___x_2257_, 0);
v_isSharedCheck_2267_ = !lean_is_exclusive(v___x_2257_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_2260_ = v___x_2257_;
v_isShared_2261_ = v_isSharedCheck_2267_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_a_2258_);
lean_dec(v___x_2257_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2267_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
uint8_t v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2265_; 
v___x_2262_ = 0;
v___x_2263_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_2263_, 0, v_a_2256_);
lean_ctor_set(v___x_2263_, 1, v_a_2258_);
lean_ctor_set_uint8(v___x_2263_, sizeof(void*)*2, v___x_2262_);
if (v_isShared_2261_ == 0)
{
lean_ctor_set(v___x_2260_, 0, v___x_2263_);
v___x_2265_ = v___x_2260_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v___x_2263_);
v___x_2265_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
return v___x_2265_;
}
}
}
else
{
lean_object* v_a_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2275_; 
lean_dec(v_a_2256_);
v_a_2268_ = lean_ctor_get(v___x_2257_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v___x_2257_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2270_ = v___x_2257_;
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_a_2268_);
lean_dec(v___x_2257_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v___x_2273_; 
if (v_isShared_2271_ == 0)
{
v___x_2273_ = v___x_2270_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_a_2268_);
v___x_2273_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
return v___x_2273_;
}
}
}
}
else
{
lean_object* v_a_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2283_; 
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v___y_2243_);
v_a_2276_ = lean_ctor_get(v___x_2255_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2255_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2278_ = v___x_2255_;
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_a_2276_);
lean_dec(v___x_2255_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v___x_2281_; 
if (v_isShared_2279_ == 0)
{
v___x_2281_ = v___x_2278_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_a_2276_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
}
}
else
{
lean_object* v___x_2284_; lean_object* v___x_2286_; 
lean_dec(v_a_2250_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v___y_2243_);
v___x_2284_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__0));
if (v_isShared_2253_ == 0)
{
lean_ctor_set(v___x_2252_, 0, v___x_2284_);
v___x_2286_ = v___x_2252_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v___x_2284_);
v___x_2286_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
return v___x_2286_;
}
}
}
}
else
{
lean_object* v_a_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2296_; 
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v___y_2243_);
v_a_2289_ = lean_ctor_get(v___x_2249_, 0);
v_isSharedCheck_2296_ = !lean_is_exclusive(v___x_2249_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2291_ = v___x_2249_;
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_a_2289_);
lean_dec(v___x_2249_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2294_; 
if (v_isShared_2292_ == 0)
{
v___x_2294_ = v___x_2291_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v_a_2289_);
v___x_2294_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
return v___x_2294_;
}
}
}
}
else
{
lean_object* v_e_x27_2297_; lean_object* v_proof_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2443_; 
v_e_x27_2297_ = lean_ctor_get(v_res_2238_, 0);
v_proof_2298_ = lean_ctor_get(v_res_2238_, 1);
v_isSharedCheck_2443_ = !lean_is_exclusive(v_res_2238_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2300_ = v_res_2238_;
v_isShared_2301_ = v_isSharedCheck_2443_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_proof_2298_);
lean_inc(v_e_x27_2297_);
lean_dec(v_res_2238_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2443_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2302_; 
lean_inc(v___y_2247_);
lean_inc_ref(v___y_2246_);
lean_inc(v___y_2245_);
lean_inc_ref(v___y_2244_);
lean_inc_ref(v_e_x27_2297_);
v___x_2302_ = l_Lean_Meta_Sym_inferType___redArg(v_e_x27_2297_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v_a_2303_; lean_object* v___x_2304_; uint8_t v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; 
v_a_2303_ = lean_ctor_get(v___x_2302_, 0);
lean_inc(v_a_2303_);
lean_dec_ref(v___x_2302_);
v___x_2304_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2));
v___x_2305_ = 0;
v___x_2306_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__3, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__3_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__3);
lean_inc(v_idx_2235_);
lean_inc(v_typeName_2234_);
v___x_2307_ = l_Lean_Expr_proj___override(v_typeName_2234_, v_idx_2235_, v___x_2306_);
v___x_2308_ = l_Lean_mkLambda(v___x_2304_, v___x_2305_, v_a_2303_, v___x_2307_);
lean_inc(v___y_2247_);
lean_inc_ref(v___y_2246_);
lean_inc(v___y_2245_);
lean_inc_ref(v___y_2244_);
lean_inc_ref(v___x_2308_);
v___x_2309_ = lean_infer_type(v___x_2308_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
if (lean_obj_tag(v___x_2309_) == 0)
{
lean_object* v_a_2310_; uint8_t v___x_2311_; 
v_a_2310_ = lean_ctor_get(v___x_2309_, 0);
lean_inc(v_a_2310_);
lean_dec_ref(v___x_2309_);
v___x_2311_ = l_Lean_Expr_isArrow(v_a_2310_);
lean_dec(v_a_2310_);
if (v___x_2311_ == 0)
{
lean_object* v___x_2312_; lean_object* v___x_2313_; 
lean_inc_ref(v_e_2211_);
v___x_2312_ = lean_alloc_closure((void*)(l_Lean_Meta_reduceProj_x3f___boxed), 6, 1);
lean_closure_set(v___x_2312_, 0, v_e_2211_);
lean_inc(v___y_2247_);
lean_inc_ref(v___y_2246_);
lean_inc(v___y_2245_);
lean_inc_ref(v___y_2244_);
v___x_2313_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___x_2312_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
if (lean_obj_tag(v___x_2313_) == 0)
{
lean_object* v_a_2314_; 
v_a_2314_ = lean_ctor_get(v___x_2313_, 0);
lean_inc(v_a_2314_);
lean_dec_ref(v___x_2313_);
if (lean_obj_tag(v_a_2314_) == 0)
{
lean_object* v___x_2315_; 
lean_del_object(v___x_2300_);
lean_inc(v___y_2247_);
lean_inc_ref(v___y_2246_);
lean_inc(v___y_2245_);
lean_inc_ref(v___y_2244_);
lean_inc_ref(v_e_x27_2297_);
lean_inc_ref(v_struct_2236_);
v___x_2315_ = l_Lean_Meta_isExprDefEq(v_struct_2236_, v_e_x27_2297_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2358_; 
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2358_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2358_ == 0)
{
v___x_2318_ = v___x_2315_;
v_isShared_2319_ = v_isSharedCheck_2358_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v___x_2315_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2358_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
uint8_t v___x_2320_; 
v___x_2320_ = lean_unbox(v_a_2316_);
lean_dec(v_a_2316_);
if (v___x_2320_ == 0)
{
lean_object* v___x_2321_; lean_object* v___x_2323_; 
lean_dec_ref(v___x_2308_);
lean_dec_ref(v_proof_2298_);
lean_dec_ref(v_e_x27_2297_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
lean_dec_ref(v_e_2211_);
v___x_2321_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__0));
if (v_isShared_2319_ == 0)
{
lean_ctor_set(v___x_2318_, 0, v___x_2321_);
v___x_2323_ = v___x_2318_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v___x_2321_);
v___x_2323_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
return v___x_2323_;
}
}
else
{
lean_object* v___x_2325_; 
lean_del_object(v___x_2318_);
lean_inc(v___y_2247_);
lean_inc_ref(v___y_2246_);
lean_inc(v___y_2245_);
lean_inc_ref(v___y_2244_);
v___x_2325_ = l_Lean_Meta_mkHCongr(v___x_2308_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_object* v_a_2326_; lean_object* v_proof_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; 
v_a_2326_ = lean_ctor_get(v___x_2325_, 0);
lean_inc(v_a_2326_);
lean_dec_ref(v___x_2325_);
v_proof_2327_ = lean_ctor_get(v_a_2326_, 1);
lean_inc_ref(v_proof_2327_);
lean_dec(v_a_2326_);
lean_inc_ref(v_e_x27_2297_);
lean_inc_ref(v_struct_2236_);
v___x_2328_ = l_Lean_mkApp3(v_proof_2327_, v_struct_2236_, v_e_x27_2297_, v_proof_2298_);
lean_inc(v___y_2247_);
lean_inc_ref(v___y_2246_);
lean_inc(v___y_2245_);
lean_inc_ref(v___y_2244_);
v___x_2329_ = l_Lean_Meta_mkEqOfHEq(v___x_2328_, v___x_2311_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
if (lean_obj_tag(v___x_2329_) == 0)
{
lean_object* v_a_2330_; uint8_t v___x_2331_; 
v_a_2330_ = lean_ctor_get(v___x_2329_, 0);
lean_inc(v_a_2330_);
lean_dec_ref(v___x_2329_);
v___x_2331_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_2236_, v_e_x27_2297_);
if (v___x_2331_ == 0)
{
lean_object* v___x_2332_; 
lean_inc(v_idx_2235_);
lean_inc(v_typeName_2234_);
lean_dec_ref(v_e_2211_);
v___x_2332_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_typeName_2234_, v_idx_2235_, v_e_x27_2297_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
if (lean_obj_tag(v___x_2332_) == 0)
{
lean_object* v_a_2333_; 
v_a_2333_ = lean_ctor_get(v___x_2332_, 0);
lean_inc(v_a_2333_);
lean_dec_ref(v___x_2332_);
v___y_2223_ = v___x_2311_;
v___y_2224_ = v_a_2330_;
v_a_2225_ = v_a_2333_;
goto v___jp_2222_;
}
else
{
lean_object* v_a_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2341_; 
lean_dec(v_a_2330_);
v_a_2334_ = lean_ctor_get(v___x_2332_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2336_ = v___x_2332_;
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_a_2334_);
lean_dec(v___x_2332_);
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
lean_dec_ref(v_e_x27_2297_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
v___y_2223_ = v___x_2311_;
v___y_2224_ = v_a_2330_;
v_a_2225_ = v_e_2211_;
goto v___jp_2222_;
}
}
else
{
lean_object* v_a_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2349_; 
lean_dec_ref(v_e_x27_2297_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
lean_dec_ref(v_e_2211_);
v_a_2342_ = lean_ctor_get(v___x_2329_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2344_ = v___x_2329_;
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_a_2342_);
lean_dec(v___x_2329_);
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
lean_object* v_a_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2357_; 
lean_dec_ref(v_proof_2298_);
lean_dec_ref(v_e_x27_2297_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
lean_dec_ref(v_e_2211_);
v_a_2350_ = lean_ctor_get(v___x_2325_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2352_ = v___x_2325_;
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_a_2350_);
lean_dec(v___x_2325_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2355_; 
if (v_isShared_2353_ == 0)
{
v___x_2355_ = v___x_2352_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v_a_2350_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
return v___x_2355_;
}
}
}
}
}
}
else
{
lean_object* v_a_2359_; lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2366_; 
lean_dec_ref(v___x_2308_);
lean_dec_ref(v_proof_2298_);
lean_dec_ref(v_e_x27_2297_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
lean_dec_ref(v_e_2211_);
v_a_2359_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2366_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2366_ == 0)
{
v___x_2361_ = v___x_2315_;
v_isShared_2362_ = v_isSharedCheck_2366_;
goto v_resetjp_2360_;
}
else
{
lean_inc(v_a_2359_);
lean_dec(v___x_2315_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2366_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v___x_2364_; 
if (v_isShared_2362_ == 0)
{
v___x_2364_ = v___x_2361_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v_a_2359_);
v___x_2364_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
return v___x_2364_;
}
}
}
}
else
{
lean_object* v_val_2367_; lean_object* v___x_2368_; 
lean_dec_ref(v___x_2308_);
lean_dec_ref(v_proof_2298_);
lean_dec_ref(v_e_x27_2297_);
lean_dec_ref(v___y_2242_);
lean_dec_ref(v_e_2211_);
v_val_2367_ = lean_ctor_get(v_a_2314_, 0);
lean_inc(v_val_2367_);
lean_dec_ref(v_a_2314_);
v___x_2368_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_val_2367_, v___y_2243_);
if (lean_obj_tag(v___x_2368_) == 0)
{
lean_object* v_a_2369_; lean_object* v___x_2370_; 
v_a_2369_ = lean_ctor_get(v___x_2368_, 0);
lean_inc(v_a_2369_);
lean_dec_ref(v___x_2368_);
lean_inc(v_a_2369_);
v___x_2370_ = l_Lean_Meta_Sym_mkEqRefl___redArg(v_a_2369_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
lean_dec(v___y_2243_);
if (lean_obj_tag(v___x_2370_) == 0)
{
lean_object* v_a_2371_; lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2381_; 
v_a_2371_ = lean_ctor_get(v___x_2370_, 0);
v_isSharedCheck_2381_ = !lean_is_exclusive(v___x_2370_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2373_ = v___x_2370_;
v_isShared_2374_ = v_isSharedCheck_2381_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_a_2371_);
lean_dec(v___x_2370_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2381_;
goto v_resetjp_2372_;
}
v_resetjp_2372_:
{
lean_object* v___x_2376_; 
if (v_isShared_2301_ == 0)
{
lean_ctor_set(v___x_2300_, 1, v_a_2371_);
lean_ctor_set(v___x_2300_, 0, v_a_2369_);
v___x_2376_ = v___x_2300_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v_a_2369_);
lean_ctor_set(v_reuseFailAlloc_2380_, 1, v_a_2371_);
v___x_2376_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
lean_object* v___x_2378_; 
lean_ctor_set_uint8(v___x_2376_, sizeof(void*)*2, v___x_2311_);
if (v_isShared_2374_ == 0)
{
lean_ctor_set(v___x_2373_, 0, v___x_2376_);
v___x_2378_ = v___x_2373_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v___x_2376_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
return v___x_2378_;
}
}
}
}
else
{
lean_object* v_a_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2389_; 
lean_dec(v_a_2369_);
lean_del_object(v___x_2300_);
v_a_2382_ = lean_ctor_get(v___x_2370_, 0);
v_isSharedCheck_2389_ = !lean_is_exclusive(v___x_2370_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2384_ = v___x_2370_;
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_a_2382_);
lean_dec(v___x_2370_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v___x_2387_; 
if (v_isShared_2385_ == 0)
{
v___x_2387_ = v___x_2384_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v_a_2382_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
}
}
}
}
else
{
lean_object* v_a_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2397_; 
lean_del_object(v___x_2300_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v___y_2243_);
v_a_2390_ = lean_ctor_get(v___x_2368_, 0);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2368_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2392_ = v___x_2368_;
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_a_2390_);
lean_dec(v___x_2368_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v___x_2395_; 
if (v_isShared_2393_ == 0)
{
v___x_2395_ = v___x_2392_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v_a_2390_);
v___x_2395_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
return v___x_2395_;
}
}
}
}
}
else
{
lean_object* v_a_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2405_; 
lean_dec_ref(v___x_2308_);
lean_del_object(v___x_2300_);
lean_dec_ref(v_proof_2298_);
lean_dec_ref(v_e_x27_2297_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
lean_dec_ref(v_e_2211_);
v_a_2398_ = lean_ctor_get(v___x_2313_, 0);
v_isSharedCheck_2405_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2405_ == 0)
{
v___x_2400_ = v___x_2313_;
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_a_2398_);
lean_dec(v___x_2313_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2403_; 
if (v_isShared_2401_ == 0)
{
v___x_2403_ = v___x_2400_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v_a_2398_);
v___x_2403_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
return v___x_2403_;
}
}
}
}
else
{
lean_object* v___x_2406_; 
lean_del_object(v___x_2300_);
lean_inc(v___y_2247_);
lean_inc_ref(v___y_2246_);
lean_inc(v___y_2245_);
lean_inc_ref(v___y_2244_);
v___x_2406_ = l_Lean_Meta_mkCongrArg(v___x_2308_, v_proof_2298_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
if (lean_obj_tag(v___x_2406_) == 0)
{
lean_object* v_a_2407_; uint8_t v___x_2408_; 
v_a_2407_ = lean_ctor_get(v___x_2406_, 0);
lean_inc(v_a_2407_);
lean_dec_ref(v___x_2406_);
v___x_2408_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_2236_, v_e_x27_2297_);
if (v___x_2408_ == 0)
{
lean_object* v___x_2409_; 
lean_inc(v_idx_2235_);
lean_inc(v_typeName_2234_);
lean_dec_ref(v_e_2211_);
v___x_2409_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_typeName_2234_, v_idx_2235_, v_e_x27_2297_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
if (lean_obj_tag(v___x_2409_) == 0)
{
lean_object* v_a_2410_; 
v_a_2410_ = lean_ctor_get(v___x_2409_, 0);
lean_inc(v_a_2410_);
lean_dec_ref(v___x_2409_);
v___y_2229_ = v_a_2407_;
v_a_2230_ = v_a_2410_;
goto v___jp_2228_;
}
else
{
lean_object* v_a_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2418_; 
lean_dec(v_a_2407_);
v_a_2411_ = lean_ctor_get(v___x_2409_, 0);
v_isSharedCheck_2418_ = !lean_is_exclusive(v___x_2409_);
if (v_isSharedCheck_2418_ == 0)
{
v___x_2413_ = v___x_2409_;
v_isShared_2414_ = v_isSharedCheck_2418_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_a_2411_);
lean_dec(v___x_2409_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2418_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v___x_2416_; 
if (v_isShared_2414_ == 0)
{
v___x_2416_ = v___x_2413_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v_a_2411_);
v___x_2416_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
return v___x_2416_;
}
}
}
}
else
{
lean_dec_ref(v_e_x27_2297_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
v___y_2229_ = v_a_2407_;
v_a_2230_ = v_e_2211_;
goto v___jp_2228_;
}
}
else
{
lean_object* v_a_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2426_; 
lean_dec_ref(v_e_x27_2297_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
lean_dec_ref(v_e_2211_);
v_a_2419_ = lean_ctor_get(v___x_2406_, 0);
v_isSharedCheck_2426_ = !lean_is_exclusive(v___x_2406_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2421_ = v___x_2406_;
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_a_2419_);
lean_dec(v___x_2406_);
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
}
else
{
lean_object* v_a_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2434_; 
lean_dec_ref(v___x_2308_);
lean_del_object(v___x_2300_);
lean_dec_ref(v_proof_2298_);
lean_dec_ref(v_e_x27_2297_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
lean_dec_ref(v_e_2211_);
v_a_2427_ = lean_ctor_get(v___x_2309_, 0);
v_isSharedCheck_2434_ = !lean_is_exclusive(v___x_2309_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2429_ = v___x_2309_;
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_a_2427_);
lean_dec(v___x_2309_);
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
lean_del_object(v___x_2300_);
lean_dec_ref(v_proof_2298_);
lean_dec_ref(v_e_x27_2297_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
lean_dec_ref(v_e_2211_);
v_a_2435_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2442_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2437_ = v___x_2302_;
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_a_2435_);
lean_dec(v___x_2302_);
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
}
else
{
lean_object* v___x_2707_; lean_object* v___x_2708_; 
lean_dec(v_a_2220_);
lean_dec_ref(v_a_2219_);
lean_dec(v_a_2218_);
lean_dec_ref(v_a_2217_);
lean_dec(v_a_2216_);
lean_dec_ref(v_a_2215_);
lean_dec(v_a_2214_);
lean_dec_ref(v_a_2213_);
lean_dec(v_a_2212_);
lean_dec_ref(v_e_2211_);
v___x_2707_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__9));
v___x_2708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2707_);
return v___x_2708_;
}
v___jp_2222_:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___x_2226_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_2226_, 0, v_a_2225_);
lean_ctor_set(v___x_2226_, 1, v___y_2224_);
lean_ctor_set_uint8(v___x_2226_, sizeof(void*)*2, v___y_2223_);
v___x_2227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2227_, 0, v___x_2226_);
return v___x_2227_;
}
v___jp_2228_:
{
uint8_t v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___x_2231_ = 0;
v___x_2232_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_2232_, 0, v_a_2230_);
lean_ctor_set(v___x_2232_, 1, v___y_2229_);
lean_ctor_set_uint8(v___x_2232_, sizeof(void*)*2, v___x_2231_);
v___x_2233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2233_, 0, v___x_2232_);
return v___x_2233_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___boxed(lean_object* v_e_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_){
_start:
{
lean_object* v_res_2720_; 
v_res_2720_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj(v_e_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_);
return v_res_2720_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__5(lean_object* v_00_u03b1_2721_, lean_object* v_x_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_){
_start:
{
lean_object* v___x_2733_; 
v___x_2733_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__5___redArg(v_x_2722_);
return v___x_2733_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2734_, lean_object* v_x_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_){
_start:
{
lean_object* v_res_2746_; 
v_res_2746_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__5(v_00_u03b1_2734_, v_x_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_);
lean_dec(v___y_2744_);
lean_dec_ref(v___y_2743_);
lean_dec(v___y_2742_);
lean_dec_ref(v___y_2741_);
lean_dec(v___y_2740_);
lean_dec_ref(v___y_2739_);
lean_dec(v___y_2738_);
lean_dec_ref(v___y_2737_);
lean_dec(v___y_2736_);
return v_res_2746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__4(lean_object* v_oldTraces_2747_, lean_object* v_data_2748_, lean_object* v_ref_2749_, lean_object* v_msg_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_){
_start:
{
lean_object* v___x_2761_; 
v___x_2761_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__4___redArg(v_oldTraces_2747_, v_data_2748_, v_ref_2749_, v_msg_2750_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
return v___x_2761_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__4___boxed(lean_object* v_oldTraces_2762_, lean_object* v_data_2763_, lean_object* v_ref_2764_, lean_object* v_msg_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_){
_start:
{
lean_object* v_res_2776_; 
v_res_2776_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__4(v_oldTraces_2762_, v_data_2763_, v_ref_2764_, v_msg_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_);
lean_dec(v___y_2774_);
lean_dec(v___y_2772_);
lean_dec_ref(v___y_2771_);
lean_dec(v___y_2770_);
lean_dec_ref(v___y_2769_);
lean_dec(v___y_2768_);
lean_dec_ref(v___y_2767_);
lean_dec(v___y_2766_);
return v_res_2776_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__0(void){
_start:
{
lean_object* v___x_2777_; lean_object* v_dummy_2778_; 
v___x_2777_ = lean_box(0);
v_dummy_2778_ = l_Lean_Expr_sort___override(v___x_2777_);
return v_dummy_2778_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__2(void){
_start:
{
lean_object* v___x_2780_; lean_object* v___x_2781_; 
v___x_2780_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__1));
v___x_2781_ = l_Lean_stringToMessageData(v___x_2780_);
return v___x_2781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn(lean_object* v_e_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_){
_start:
{
uint8_t v___x_2796_; 
v___x_2796_ = l_Lean_Expr_isApp(v_e_2782_);
if (v___x_2796_ == 0)
{
lean_object* v___x_2797_; lean_object* v___x_2798_; 
lean_dec(v_a_2791_);
lean_dec_ref(v_a_2790_);
lean_dec(v_a_2789_);
lean_dec_ref(v_a_2788_);
lean_dec(v_a_2787_);
lean_dec_ref(v_a_2786_);
lean_dec(v_a_2785_);
lean_dec_ref(v_a_2784_);
lean_dec(v_a_2783_);
lean_dec_ref(v_e_2782_);
v___x_2797_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_2797_, 0, v___x_2796_);
v___x_2798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2798_, 0, v___x_2797_);
return v___x_2798_;
}
else
{
lean_object* v_fn_2799_; uint8_t v___x_2800_; 
v_fn_2799_ = l_Lean_Expr_getAppFn(v_e_2782_);
v___x_2800_ = l_Lean_Expr_isLambda(v_fn_2799_);
if (v___x_2800_ == 0)
{
uint8_t v___x_2801_; 
v___x_2801_ = l_Lean_Expr_isConst(v_fn_2799_);
if (v___x_2801_ == 0)
{
lean_object* v___x_2802_; 
lean_inc(v_a_2791_);
lean_inc_ref(v_a_2790_);
lean_inc(v_a_2789_);
lean_inc_ref(v_a_2788_);
lean_inc(v_a_2787_);
lean_inc_ref(v_a_2786_);
v___x_2802_ = lean_sym_simp(v_fn_2799_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_, v_a_2787_, v_a_2788_, v_a_2789_, v_a_2790_, v_a_2791_);
if (lean_obj_tag(v___x_2802_) == 0)
{
lean_object* v_a_2803_; 
v_a_2803_ = lean_ctor_get(v___x_2802_, 0);
lean_inc(v_a_2803_);
if (lean_obj_tag(v_a_2803_) == 0)
{
lean_dec_ref(v_a_2803_);
lean_dec(v_a_2791_);
lean_dec_ref(v_a_2790_);
lean_dec(v_a_2789_);
lean_dec_ref(v_a_2788_);
lean_dec(v_a_2787_);
lean_dec_ref(v_a_2786_);
lean_dec_ref(v_e_2782_);
return v___x_2802_;
}
else
{
lean_object* v_e_x27_2804_; lean_object* v_proof_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2881_; 
lean_dec_ref(v___x_2802_);
v_e_x27_2804_ = lean_ctor_get(v_a_2803_, 0);
v_proof_2805_ = lean_ctor_get(v_a_2803_, 1);
v_isSharedCheck_2881_ = !lean_is_exclusive(v_a_2803_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2807_ = v_a_2803_;
v_isShared_2808_ = v_isSharedCheck_2881_;
goto v_resetjp_2806_;
}
else
{
lean_inc(v_proof_2805_);
lean_inc(v_e_x27_2804_);
lean_dec(v_a_2803_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2881_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
lean_object* v___x_2809_; 
lean_inc(v_a_2791_);
lean_inc_ref(v_a_2790_);
lean_inc(v_a_2789_);
lean_inc_ref(v_a_2788_);
lean_inc_ref(v_e_x27_2804_);
v___x_2809_ = l_Lean_Meta_Sym_inferType___redArg(v_e_x27_2804_, v_a_2787_, v_a_2788_, v_a_2789_, v_a_2790_, v_a_2791_);
if (lean_obj_tag(v___x_2809_) == 0)
{
lean_object* v_a_2810_; lean_object* v_dummy_2811_; lean_object* v_nargs_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; 
v_a_2810_ = lean_ctor_get(v___x_2809_, 0);
lean_inc(v_a_2810_);
lean_dec_ref(v___x_2809_);
v_dummy_2811_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__0, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__0_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__0);
v_nargs_2812_ = l_Lean_Expr_getAppNumArgs(v_e_2782_);
lean_inc(v_nargs_2812_);
v___x_2813_ = lean_mk_array(v_nargs_2812_, v_dummy_2811_);
v___x_2814_ = lean_unsigned_to_nat(1u);
v___x_2815_ = lean_nat_sub(v_nargs_2812_, v___x_2814_);
lean_dec(v_nargs_2812_);
lean_inc_ref(v_e_2782_);
v___x_2816_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2782_, v___x_2813_, v___x_2815_);
lean_inc(v_a_2791_);
lean_inc_ref(v_a_2790_);
lean_inc(v_a_2789_);
lean_inc_ref(v_a_2788_);
v___x_2817_ = l_Lean_Meta_Tactic_Cbv_mkAppNS(v_e_x27_2804_, v___x_2816_, v_a_2786_, v_a_2787_, v_a_2788_, v_a_2789_, v_a_2790_, v_a_2791_);
if (lean_obj_tag(v___x_2817_) == 0)
{
lean_object* v_a_2818_; lean_object* v___x_2819_; uint8_t v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; 
v_a_2818_ = lean_ctor_get(v___x_2817_, 0);
lean_inc(v_a_2818_);
lean_dec_ref(v___x_2817_);
v___x_2819_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2));
v___x_2820_ = 0;
v___x_2821_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__3, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__3_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__3);
v___x_2822_ = l_Lean_mkAppN(v___x_2821_, v___x_2816_);
lean_dec_ref(v___x_2816_);
v___x_2823_ = l_Lean_mkLambda(v___x_2819_, v___x_2820_, v_a_2810_, v___x_2822_);
lean_inc(v_a_2791_);
lean_inc_ref(v_a_2790_);
lean_inc(v_a_2789_);
lean_inc_ref(v_a_2788_);
v___x_2824_ = l_Lean_Meta_mkCongrArg(v___x_2823_, v_proof_2805_, v_a_2788_, v_a_2789_, v_a_2790_, v_a_2791_);
if (lean_obj_tag(v___x_2824_) == 0)
{
lean_object* v_a_2825_; lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2856_; 
v_a_2825_ = lean_ctor_get(v___x_2824_, 0);
v_isSharedCheck_2856_ = !lean_is_exclusive(v___x_2824_);
if (v_isSharedCheck_2856_ == 0)
{
v___x_2827_ = v___x_2824_;
v_isShared_2828_ = v_isSharedCheck_2856_;
goto v_resetjp_2826_;
}
else
{
lean_inc(v_a_2825_);
lean_dec(v___x_2824_);
v___x_2827_ = lean_box(0);
v_isShared_2828_ = v_isSharedCheck_2856_;
goto v_resetjp_2826_;
}
v_resetjp_2826_:
{
lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v_a_2838_; uint8_t v___x_2839_; 
v___x_2836_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2));
v___x_2837_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(v___x_2836_, v_a_2790_);
v_a_2838_ = lean_ctor_get(v___x_2837_, 0);
lean_inc(v_a_2838_);
lean_dec_ref(v___x_2837_);
v___x_2839_ = lean_unbox(v_a_2838_);
lean_dec(v_a_2838_);
if (v___x_2839_ == 0)
{
lean_dec(v_a_2791_);
lean_dec_ref(v_a_2790_);
lean_dec(v_a_2789_);
lean_dec_ref(v_a_2788_);
lean_dec_ref(v_e_2782_);
goto v___jp_2829_;
}
else
{
lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; 
v___x_2840_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__2, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__2);
v___x_2841_ = l_Lean_indentExpr(v_e_2782_);
v___x_2842_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2842_, 0, v___x_2840_);
lean_ctor_set(v___x_2842_, 1, v___x_2841_);
v___x_2843_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7);
v___x_2844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2844_, 0, v___x_2842_);
lean_ctor_set(v___x_2844_, 1, v___x_2843_);
lean_inc(v_a_2818_);
v___x_2845_ = l_Lean_indentExpr(v_a_2818_);
v___x_2846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2846_, 0, v___x_2844_);
lean_ctor_set(v___x_2846_, 1, v___x_2845_);
v___x_2847_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg(v___x_2836_, v___x_2846_, v_a_2788_, v_a_2789_, v_a_2790_, v_a_2791_);
lean_dec(v_a_2791_);
lean_dec_ref(v_a_2790_);
lean_dec(v_a_2789_);
lean_dec_ref(v_a_2788_);
if (lean_obj_tag(v___x_2847_) == 0)
{
lean_dec_ref(v___x_2847_);
goto v___jp_2829_;
}
else
{
lean_object* v_a_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2855_; 
lean_del_object(v___x_2827_);
lean_dec(v_a_2825_);
lean_dec(v_a_2818_);
lean_del_object(v___x_2807_);
v_a_2848_ = lean_ctor_get(v___x_2847_, 0);
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2847_);
if (v_isSharedCheck_2855_ == 0)
{
v___x_2850_ = v___x_2847_;
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_a_2848_);
lean_dec(v___x_2847_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v___x_2853_; 
if (v_isShared_2851_ == 0)
{
v___x_2853_ = v___x_2850_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_a_2848_);
v___x_2853_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
return v___x_2853_;
}
}
}
}
v___jp_2829_:
{
lean_object* v___x_2831_; 
if (v_isShared_2808_ == 0)
{
lean_ctor_set(v___x_2807_, 1, v_a_2825_);
lean_ctor_set(v___x_2807_, 0, v_a_2818_);
v___x_2831_ = v___x_2807_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_a_2818_);
lean_ctor_set(v_reuseFailAlloc_2835_, 1, v_a_2825_);
v___x_2831_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
lean_object* v___x_2833_; 
lean_ctor_set_uint8(v___x_2831_, sizeof(void*)*2, v___x_2801_);
if (v_isShared_2828_ == 0)
{
lean_ctor_set(v___x_2827_, 0, v___x_2831_);
v___x_2833_ = v___x_2827_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v___x_2831_);
v___x_2833_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
return v___x_2833_;
}
}
}
}
}
else
{
lean_object* v_a_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2864_; 
lean_dec(v_a_2818_);
lean_del_object(v___x_2807_);
lean_dec(v_a_2791_);
lean_dec_ref(v_a_2790_);
lean_dec(v_a_2789_);
lean_dec_ref(v_a_2788_);
lean_dec_ref(v_e_2782_);
v_a_2857_ = lean_ctor_get(v___x_2824_, 0);
v_isSharedCheck_2864_ = !lean_is_exclusive(v___x_2824_);
if (v_isSharedCheck_2864_ == 0)
{
v___x_2859_ = v___x_2824_;
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_a_2857_);
lean_dec(v___x_2824_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v___x_2862_; 
if (v_isShared_2860_ == 0)
{
v___x_2862_ = v___x_2859_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v_a_2857_);
v___x_2862_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
return v___x_2862_;
}
}
}
}
else
{
lean_object* v_a_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2872_; 
lean_dec_ref(v___x_2816_);
lean_dec(v_a_2810_);
lean_del_object(v___x_2807_);
lean_dec_ref(v_proof_2805_);
lean_dec(v_a_2791_);
lean_dec_ref(v_a_2790_);
lean_dec(v_a_2789_);
lean_dec_ref(v_a_2788_);
lean_dec_ref(v_e_2782_);
v_a_2865_ = lean_ctor_get(v___x_2817_, 0);
v_isSharedCheck_2872_ = !lean_is_exclusive(v___x_2817_);
if (v_isSharedCheck_2872_ == 0)
{
v___x_2867_ = v___x_2817_;
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_a_2865_);
lean_dec(v___x_2817_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
lean_object* v___x_2870_; 
if (v_isShared_2868_ == 0)
{
v___x_2870_ = v___x_2867_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v_a_2865_);
v___x_2870_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
return v___x_2870_;
}
}
}
}
else
{
lean_object* v_a_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2880_; 
lean_del_object(v___x_2807_);
lean_dec_ref(v_proof_2805_);
lean_dec_ref(v_e_x27_2804_);
lean_dec(v_a_2791_);
lean_dec_ref(v_a_2790_);
lean_dec(v_a_2789_);
lean_dec_ref(v_a_2788_);
lean_dec(v_a_2787_);
lean_dec_ref(v_a_2786_);
lean_dec_ref(v_e_2782_);
v_a_2873_ = lean_ctor_get(v___x_2809_, 0);
v_isSharedCheck_2880_ = !lean_is_exclusive(v___x_2809_);
if (v_isSharedCheck_2880_ == 0)
{
v___x_2875_ = v___x_2809_;
v_isShared_2876_ = v_isSharedCheck_2880_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_a_2873_);
lean_dec(v___x_2809_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2880_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
lean_object* v___x_2878_; 
if (v_isShared_2876_ == 0)
{
v___x_2878_ = v___x_2875_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v_a_2873_);
v___x_2878_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
return v___x_2878_;
}
}
}
}
}
}
else
{
lean_dec(v_a_2791_);
lean_dec_ref(v_a_2790_);
lean_dec(v_a_2789_);
lean_dec_ref(v_a_2788_);
lean_dec(v_a_2787_);
lean_dec_ref(v_a_2786_);
lean_dec_ref(v_e_2782_);
return v___x_2802_;
}
}
else
{
lean_dec_ref(v_fn_2799_);
lean_dec(v_a_2791_);
lean_dec_ref(v_a_2790_);
lean_dec(v_a_2789_);
lean_dec_ref(v_a_2788_);
lean_dec(v_a_2787_);
lean_dec_ref(v_a_2786_);
lean_dec(v_a_2785_);
lean_dec_ref(v_a_2784_);
lean_dec(v_a_2783_);
lean_dec_ref(v_e_2782_);
goto v___jp_2793_;
}
}
else
{
lean_dec_ref(v_fn_2799_);
lean_dec(v_a_2791_);
lean_dec_ref(v_a_2790_);
lean_dec(v_a_2789_);
lean_dec_ref(v_a_2788_);
lean_dec(v_a_2787_);
lean_dec_ref(v_a_2786_);
lean_dec(v_a_2785_);
lean_dec_ref(v_a_2784_);
lean_dec(v_a_2783_);
lean_dec_ref(v_e_2782_);
goto v___jp_2793_;
}
}
v___jp_2793_:
{
lean_object* v___x_2794_; lean_object* v___x_2795_; 
v___x_2794_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__9));
v___x_2795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2795_, 0, v___x_2794_);
return v___x_2795_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___boxed(lean_object* v_e_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_){
_start:
{
lean_object* v_res_2893_; 
v_res_2893_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn(v_e_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_);
return v_res_2893_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___closed__1(void){
_start:
{
lean_object* v___x_2895_; lean_object* v___x_2896_; 
v___x_2895_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___closed__0));
v___x_2896_ = l_Lean_stringToMessageData(v___x_2895_);
return v___x_2896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst(lean_object* v_e_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_){
_start:
{
if (lean_obj_tag(v_e_2897_) == 4)
{
lean_object* v_declName_2908_; lean_object* v_us_2909_; lean_object* v___x_2910_; 
v_declName_2908_ = lean_ctor_get(v_e_2897_, 0);
v_us_2909_ = lean_ctor_get(v_e_2897_, 1);
lean_inc_ref(v_a_2905_);
lean_inc(v_declName_2908_);
v___x_2910_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0(v_declName_2908_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_);
if (lean_obj_tag(v___x_2910_) == 0)
{
lean_object* v_a_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_3029_; 
v_a_2911_ = lean_ctor_get(v___x_2910_, 0);
v_isSharedCheck_3029_ = !lean_is_exclusive(v___x_2910_);
if (v_isSharedCheck_3029_ == 0)
{
v___x_2913_ = v___x_2910_;
v_isShared_2914_ = v_isSharedCheck_3029_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_a_2911_);
lean_dec(v___x_2910_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_3029_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
uint8_t v___x_2915_; 
v___x_2915_ = l_Lean_ConstantInfo_isDefinition(v_a_2911_);
if (v___x_2915_ == 0)
{
lean_object* v___x_2916_; lean_object* v___x_2918_; 
lean_dec(v_a_2911_);
lean_dec_ref(v_e_2897_);
lean_dec(v_a_2906_);
lean_dec_ref(v_a_2905_);
lean_dec(v_a_2904_);
lean_dec_ref(v_a_2903_);
v___x_2916_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_2916_, 0, v___x_2915_);
if (v_isShared_2914_ == 0)
{
lean_ctor_set(v___x_2913_, 0, v___x_2916_);
v___x_2918_ = v___x_2913_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v___x_2916_);
v___x_2918_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
return v___x_2918_;
}
}
else
{
lean_object* v___x_2920_; 
lean_del_object(v___x_2913_);
lean_inc(v_a_2906_);
lean_inc_ref(v_a_2905_);
lean_inc(v_a_2904_);
lean_inc_ref(v_a_2903_);
lean_inc_ref(v_e_2897_);
v___x_2920_ = l_Lean_Meta_Sym_inferType___redArg(v_e_2897_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_);
if (lean_obj_tag(v___x_2920_) == 0)
{
lean_object* v_a_2921_; lean_object* v___x_2922_; 
v_a_2921_ = lean_ctor_get(v___x_2920_, 0);
lean_inc(v_a_2921_);
lean_dec_ref(v___x_2920_);
lean_inc(v_a_2906_);
lean_inc_ref(v_a_2905_);
lean_inc(v_a_2904_);
lean_inc_ref(v_a_2903_);
v___x_2922_ = l_Lean_Meta_whnfD(v_a_2921_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_);
if (lean_obj_tag(v___x_2922_) == 0)
{
lean_object* v_a_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_3012_; 
v_a_2923_ = lean_ctor_get(v___x_2922_, 0);
v_isSharedCheck_3012_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_3012_ == 0)
{
v___x_2925_ = v___x_2922_;
v_isShared_2926_ = v_isSharedCheck_3012_;
goto v_resetjp_2924_;
}
else
{
lean_inc(v_a_2923_);
lean_dec(v___x_2922_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_3012_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
if (lean_obj_tag(v_a_2923_) == 7)
{
lean_object* v___x_2927_; lean_object* v___x_2929_; 
lean_dec_ref(v_a_2923_);
lean_dec(v_a_2911_);
lean_dec_ref(v_e_2897_);
lean_dec(v_a_2906_);
lean_dec_ref(v_a_2905_);
lean_dec(v_a_2904_);
lean_dec_ref(v_a_2903_);
v___x_2927_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__9));
if (v_isShared_2926_ == 0)
{
lean_ctor_set(v___x_2925_, 0, v___x_2927_);
v___x_2929_ = v___x_2925_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v___x_2927_);
v___x_2929_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
return v___x_2929_;
}
}
else
{
uint8_t v___x_2931_; lean_object* v___y_2933_; lean_object* v___y_2934_; lean_object* v___y_2935_; lean_object* v___y_2936_; lean_object* v___y_2937_; lean_object* v___y_2938_; uint8_t v___y_2958_; uint8_t v___x_3007_; 
lean_dec(v_a_2923_);
v___x_2931_ = 0;
v___x_3007_ = l_Lean_ConstantInfo_hasValue(v_a_2911_, v___x_2931_);
if (v___x_3007_ == 0)
{
v___y_2958_ = v___x_3007_;
goto v___jp_2957_;
}
else
{
lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; uint8_t v___x_3011_; 
v___x_3008_ = l_Lean_ConstantInfo_levelParams(v_a_2911_);
v___x_3009_ = l_List_lengthTR___redArg(v___x_3008_);
lean_dec(v___x_3008_);
v___x_3010_ = l_List_lengthTR___redArg(v_us_2909_);
v___x_3011_ = lean_nat_dec_eq(v___x_3009_, v___x_3010_);
lean_dec(v___x_3010_);
lean_dec(v___x_3009_);
v___y_2958_ = v___x_3011_;
goto v___jp_2957_;
}
v___jp_2932_:
{
lean_object* v___x_2939_; 
lean_inc_ref(v___y_2933_);
v___x_2939_ = l_Lean_Meta_Sym_mkEqRefl___redArg(v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_);
if (lean_obj_tag(v___x_2939_) == 0)
{
lean_object* v_a_2940_; lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_2948_; 
v_a_2940_ = lean_ctor_get(v___x_2939_, 0);
v_isSharedCheck_2948_ = !lean_is_exclusive(v___x_2939_);
if (v_isSharedCheck_2948_ == 0)
{
v___x_2942_ = v___x_2939_;
v_isShared_2943_ = v_isSharedCheck_2948_;
goto v_resetjp_2941_;
}
else
{
lean_inc(v_a_2940_);
lean_dec(v___x_2939_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_2948_;
goto v_resetjp_2941_;
}
v_resetjp_2941_:
{
lean_object* v___x_2944_; lean_object* v___x_2946_; 
v___x_2944_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_2944_, 0, v___y_2933_);
lean_ctor_set(v___x_2944_, 1, v_a_2940_);
lean_ctor_set_uint8(v___x_2944_, sizeof(void*)*2, v___x_2931_);
if (v_isShared_2943_ == 0)
{
lean_ctor_set(v___x_2942_, 0, v___x_2944_);
v___x_2946_ = v___x_2942_;
goto v_reusejp_2945_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v___x_2944_);
v___x_2946_ = v_reuseFailAlloc_2947_;
goto v_reusejp_2945_;
}
v_reusejp_2945_:
{
return v___x_2946_;
}
}
}
else
{
lean_object* v_a_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2956_; 
lean_dec_ref(v___y_2933_);
v_a_2949_ = lean_ctor_get(v___x_2939_, 0);
v_isSharedCheck_2956_ = !lean_is_exclusive(v___x_2939_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2951_ = v___x_2939_;
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_a_2949_);
lean_dec(v___x_2939_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2954_; 
if (v_isShared_2952_ == 0)
{
v___x_2954_ = v___x_2951_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v_a_2949_);
v___x_2954_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
return v___x_2954_;
}
}
}
}
v___jp_2957_:
{
if (v___y_2958_ == 0)
{
lean_object* v___x_2959_; lean_object* v___x_2961_; 
lean_dec(v_a_2911_);
lean_dec_ref(v_e_2897_);
lean_dec(v_a_2906_);
lean_dec_ref(v_a_2905_);
lean_dec(v_a_2904_);
lean_dec_ref(v_a_2903_);
v___x_2959_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__9));
if (v_isShared_2926_ == 0)
{
lean_ctor_set(v___x_2925_, 0, v___x_2959_);
v___x_2961_ = v___x_2925_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2962_; 
v_reuseFailAlloc_2962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2962_, 0, v___x_2959_);
v___x_2961_ = v_reuseFailAlloc_2962_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
return v___x_2961_;
}
}
else
{
lean_object* v___x_2963_; 
lean_del_object(v___x_2925_);
lean_inc(v_us_2909_);
v___x_2963_ = l_Lean_Core_instantiateValueLevelParams(v_a_2911_, v_us_2909_, v_a_2905_, v_a_2906_);
lean_dec(v_a_2911_);
if (lean_obj_tag(v___x_2963_) == 0)
{
lean_object* v_a_2964_; lean_object* v___x_2965_; 
v_a_2964_ = lean_ctor_get(v___x_2963_, 0);
lean_inc(v_a_2964_);
lean_dec_ref(v___x_2963_);
v___x_2965_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_a_2964_, v_a_2902_);
if (lean_obj_tag(v___x_2965_) == 0)
{
lean_object* v_a_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v_a_2969_; uint8_t v___x_2970_; 
v_a_2966_ = lean_ctor_get(v___x_2965_, 0);
lean_inc(v_a_2966_);
lean_dec_ref(v___x_2965_);
v___x_2967_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__1));
v___x_2968_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(v___x_2967_, v_a_2905_);
v_a_2969_ = lean_ctor_get(v___x_2968_, 0);
lean_inc(v_a_2969_);
lean_dec_ref(v___x_2968_);
v___x_2970_ = lean_unbox(v_a_2969_);
lean_dec(v_a_2969_);
if (v___x_2970_ == 0)
{
lean_dec_ref(v_e_2897_);
v___y_2933_ = v_a_2966_;
v___y_2934_ = v_a_2902_;
v___y_2935_ = v_a_2903_;
v___y_2936_ = v_a_2904_;
v___y_2937_ = v_a_2905_;
v___y_2938_ = v_a_2906_;
goto v___jp_2932_;
}
else
{
lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; 
v___x_2971_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___closed__1, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___closed__1);
lean_inc(v_declName_2908_);
v___x_2972_ = l_Lean_MessageData_ofName(v_declName_2908_);
v___x_2973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2973_, 0, v___x_2971_);
lean_ctor_set(v___x_2973_, 1, v___x_2972_);
v___x_2974_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__5, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__5_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__5);
v___x_2975_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2975_, 0, v___x_2973_);
lean_ctor_set(v___x_2975_, 1, v___x_2974_);
v___x_2976_ = l_Lean_indentExpr(v_e_2897_);
v___x_2977_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2977_, 0, v___x_2975_);
lean_ctor_set(v___x_2977_, 1, v___x_2976_);
v___x_2978_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7);
v___x_2979_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2979_, 0, v___x_2977_);
lean_ctor_set(v___x_2979_, 1, v___x_2978_);
lean_inc(v_a_2966_);
v___x_2980_ = l_Lean_indentExpr(v_a_2966_);
v___x_2981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2981_, 0, v___x_2979_);
lean_ctor_set(v___x_2981_, 1, v___x_2980_);
v___x_2982_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg(v___x_2967_, v___x_2981_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_);
if (lean_obj_tag(v___x_2982_) == 0)
{
lean_dec_ref(v___x_2982_);
v___y_2933_ = v_a_2966_;
v___y_2934_ = v_a_2902_;
v___y_2935_ = v_a_2903_;
v___y_2936_ = v_a_2904_;
v___y_2937_ = v_a_2905_;
v___y_2938_ = v_a_2906_;
goto v___jp_2932_;
}
else
{
lean_object* v_a_2983_; lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_2990_; 
lean_dec(v_a_2966_);
lean_dec(v_a_2906_);
lean_dec_ref(v_a_2905_);
lean_dec(v_a_2904_);
lean_dec_ref(v_a_2903_);
v_a_2983_ = lean_ctor_get(v___x_2982_, 0);
v_isSharedCheck_2990_ = !lean_is_exclusive(v___x_2982_);
if (v_isSharedCheck_2990_ == 0)
{
v___x_2985_ = v___x_2982_;
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
else
{
lean_inc(v_a_2983_);
lean_dec(v___x_2982_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
lean_object* v___x_2988_; 
if (v_isShared_2986_ == 0)
{
v___x_2988_ = v___x_2985_;
goto v_reusejp_2987_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v_a_2983_);
v___x_2988_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2987_;
}
v_reusejp_2987_:
{
return v___x_2988_;
}
}
}
}
}
else
{
lean_object* v_a_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_2998_; 
lean_dec_ref(v_e_2897_);
lean_dec(v_a_2906_);
lean_dec_ref(v_a_2905_);
lean_dec(v_a_2904_);
lean_dec_ref(v_a_2903_);
v_a_2991_ = lean_ctor_get(v___x_2965_, 0);
v_isSharedCheck_2998_ = !lean_is_exclusive(v___x_2965_);
if (v_isSharedCheck_2998_ == 0)
{
v___x_2993_ = v___x_2965_;
v_isShared_2994_ = v_isSharedCheck_2998_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_a_2991_);
lean_dec(v___x_2965_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_2998_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v___x_2996_; 
if (v_isShared_2994_ == 0)
{
v___x_2996_ = v___x_2993_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v_a_2991_);
v___x_2996_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
return v___x_2996_;
}
}
}
}
else
{
lean_object* v_a_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3006_; 
lean_dec_ref(v_e_2897_);
lean_dec(v_a_2906_);
lean_dec_ref(v_a_2905_);
lean_dec(v_a_2904_);
lean_dec_ref(v_a_2903_);
v_a_2999_ = lean_ctor_get(v___x_2963_, 0);
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2963_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_3001_ = v___x_2963_;
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_a_2999_);
lean_dec(v___x_2963_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___x_3004_; 
if (v_isShared_3002_ == 0)
{
v___x_3004_ = v___x_3001_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v_a_2999_);
v___x_3004_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
return v___x_3004_;
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
lean_object* v_a_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3020_; 
lean_dec(v_a_2911_);
lean_dec_ref(v_e_2897_);
lean_dec(v_a_2906_);
lean_dec_ref(v_a_2905_);
lean_dec(v_a_2904_);
lean_dec_ref(v_a_2903_);
v_a_3013_ = lean_ctor_get(v___x_2922_, 0);
v_isSharedCheck_3020_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_3020_ == 0)
{
v___x_3015_ = v___x_2922_;
v_isShared_3016_ = v_isSharedCheck_3020_;
goto v_resetjp_3014_;
}
else
{
lean_inc(v_a_3013_);
lean_dec(v___x_2922_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3020_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v___x_3018_; 
if (v_isShared_3016_ == 0)
{
v___x_3018_ = v___x_3015_;
goto v_reusejp_3017_;
}
else
{
lean_object* v_reuseFailAlloc_3019_; 
v_reuseFailAlloc_3019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3019_, 0, v_a_3013_);
v___x_3018_ = v_reuseFailAlloc_3019_;
goto v_reusejp_3017_;
}
v_reusejp_3017_:
{
return v___x_3018_;
}
}
}
}
else
{
lean_object* v_a_3021_; lean_object* v___x_3023_; uint8_t v_isShared_3024_; uint8_t v_isSharedCheck_3028_; 
lean_dec(v_a_2911_);
lean_dec_ref(v_e_2897_);
lean_dec(v_a_2906_);
lean_dec_ref(v_a_2905_);
lean_dec(v_a_2904_);
lean_dec_ref(v_a_2903_);
v_a_3021_ = lean_ctor_get(v___x_2920_, 0);
v_isSharedCheck_3028_ = !lean_is_exclusive(v___x_2920_);
if (v_isSharedCheck_3028_ == 0)
{
v___x_3023_ = v___x_2920_;
v_isShared_3024_ = v_isSharedCheck_3028_;
goto v_resetjp_3022_;
}
else
{
lean_inc(v_a_3021_);
lean_dec(v___x_2920_);
v___x_3023_ = lean_box(0);
v_isShared_3024_ = v_isSharedCheck_3028_;
goto v_resetjp_3022_;
}
v_resetjp_3022_:
{
lean_object* v___x_3026_; 
if (v_isShared_3024_ == 0)
{
v___x_3026_ = v___x_3023_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v_a_3021_);
v___x_3026_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
return v___x_3026_;
}
}
}
}
}
}
else
{
lean_object* v_a_3030_; lean_object* v___x_3032_; uint8_t v_isShared_3033_; uint8_t v_isSharedCheck_3037_; 
lean_dec_ref(v_e_2897_);
lean_dec(v_a_2906_);
lean_dec_ref(v_a_2905_);
lean_dec(v_a_2904_);
lean_dec_ref(v_a_2903_);
v_a_3030_ = lean_ctor_get(v___x_2910_, 0);
v_isSharedCheck_3037_ = !lean_is_exclusive(v___x_2910_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_3032_ = v___x_2910_;
v_isShared_3033_ = v_isSharedCheck_3037_;
goto v_resetjp_3031_;
}
else
{
lean_inc(v_a_3030_);
lean_dec(v___x_2910_);
v___x_3032_ = lean_box(0);
v_isShared_3033_ = v_isSharedCheck_3037_;
goto v_resetjp_3031_;
}
v_resetjp_3031_:
{
lean_object* v___x_3035_; 
if (v_isShared_3033_ == 0)
{
v___x_3035_ = v___x_3032_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v_a_3030_);
v___x_3035_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
return v___x_3035_;
}
}
}
}
else
{
lean_object* v___x_3038_; lean_object* v___x_3039_; 
lean_dec(v_a_2906_);
lean_dec_ref(v_a_2905_);
lean_dec(v_a_2904_);
lean_dec_ref(v_a_2903_);
lean_dec_ref(v_e_2897_);
v___x_3038_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__9));
v___x_3039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3039_, 0, v___x_3038_);
return v___x_3039_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___boxed(lean_object* v_e_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_){
_start:
{
lean_object* v_res_3051_; 
v_res_3051_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst(v_e_3040_, v_a_3041_, v_a_3042_, v_a_3043_, v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_, v_a_3048_, v_a_3049_);
lean_dec(v_a_3045_);
lean_dec_ref(v_a_3044_);
lean_dec(v_a_3043_);
lean_dec_ref(v_a_3042_);
lean_dec(v_a_3041_);
return v_res_3051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___lam__0(lean_object* v_x_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_){
_start:
{
lean_object* v___x_3064_; 
lean_inc(v___y_3062_);
lean_inc_ref(v___y_3061_);
lean_inc(v___y_3060_);
lean_inc_ref(v___y_3059_);
lean_inc(v___y_3058_);
lean_inc_ref(v___y_3057_);
lean_inc(v___y_3056_);
lean_inc_ref(v___y_3055_);
lean_inc(v___y_3054_);
lean_inc_ref(v___y_3053_);
v___x_3064_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems(v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_);
if (lean_obj_tag(v___x_3064_) == 0)
{
lean_object* v_a_3065_; 
v_a_3065_ = lean_ctor_get(v___x_3064_, 0);
lean_inc(v_a_3065_);
if (lean_obj_tag(v_a_3065_) == 0)
{
uint8_t v_done_3066_; 
v_done_3066_ = lean_ctor_get_uint8(v_a_3065_, 0);
lean_dec_ref(v_a_3065_);
if (v_done_3066_ == 0)
{
lean_object* v___x_3067_; 
lean_dec_ref(v___x_3064_);
v___x_3067_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst(v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_);
lean_dec(v___y_3058_);
lean_dec_ref(v___y_3057_);
lean_dec(v___y_3056_);
lean_dec_ref(v___y_3055_);
lean_dec(v___y_3054_);
return v___x_3067_;
}
else
{
lean_dec(v___y_3062_);
lean_dec_ref(v___y_3061_);
lean_dec(v___y_3060_);
lean_dec_ref(v___y_3059_);
lean_dec(v___y_3058_);
lean_dec_ref(v___y_3057_);
lean_dec(v___y_3056_);
lean_dec_ref(v___y_3055_);
lean_dec(v___y_3054_);
lean_dec_ref(v___y_3053_);
return v___x_3064_;
}
}
else
{
lean_dec_ref(v_a_3065_);
lean_dec(v___y_3062_);
lean_dec_ref(v___y_3061_);
lean_dec(v___y_3060_);
lean_dec_ref(v___y_3059_);
lean_dec(v___y_3058_);
lean_dec_ref(v___y_3057_);
lean_dec(v___y_3056_);
lean_dec_ref(v___y_3055_);
lean_dec(v___y_3054_);
lean_dec_ref(v___y_3053_);
return v___x_3064_;
}
}
else
{
lean_dec(v___y_3062_);
lean_dec_ref(v___y_3061_);
lean_dec(v___y_3060_);
lean_dec_ref(v___y_3059_);
lean_dec(v___y_3058_);
lean_dec_ref(v___y_3057_);
lean_dec(v___y_3056_);
lean_dec_ref(v___y_3055_);
lean_dec(v___y_3054_);
lean_dec_ref(v___y_3053_);
return v___x_3064_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___lam__0___boxed(lean_object* v_x_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_){
_start:
{
lean_object* v_res_3080_; 
v_res_3080_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___lam__0(v_x_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_);
return v_res_3080_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep(lean_object* v_e_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_){
_start:
{
switch(lean_obj_tag(v_e_3081_))
{
case 9:
{
lean_object* v___x_3095_; 
lean_dec_ref(v_a_3085_);
lean_dec(v_a_3084_);
lean_dec_ref(v_a_3083_);
lean_dec(v_a_3082_);
v___x_3095_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg(v_e_3081_, v_a_3086_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_);
lean_dec(v_a_3086_);
return v___x_3095_;
}
case 11:
{
lean_object* v___x_3096_; 
v___x_3096_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj(v_e_3081_, v_a_3082_, v_a_3083_, v_a_3084_, v_a_3085_, v_a_3086_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_);
return v___x_3096_;
}
case 4:
{
lean_object* v___x_3097_; 
v___x_3097_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_isOpaqueConst___redArg(v_e_3081_, v_a_3090_);
if (lean_obj_tag(v___x_3097_) == 0)
{
lean_object* v_a_3098_; lean_object* v___x_3099_; uint8_t v_done_3100_; 
v_a_3098_ = lean_ctor_get(v___x_3097_, 0);
lean_inc(v_a_3098_);
v___x_3099_ = lean_box(0);
v_done_3100_ = lean_ctor_get_uint8(v_a_3098_, 0);
lean_dec(v_a_3098_);
if (v_done_3100_ == 0)
{
lean_object* v___x_3101_; 
lean_dec_ref(v___x_3097_);
v___x_3101_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___lam__0(v___x_3099_, v_e_3081_, v_a_3082_, v_a_3083_, v_a_3084_, v_a_3085_, v_a_3086_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_);
return v___x_3101_;
}
else
{
lean_dec_ref(v_e_3081_);
lean_dec(v_a_3090_);
lean_dec_ref(v_a_3089_);
lean_dec(v_a_3088_);
lean_dec_ref(v_a_3087_);
lean_dec(v_a_3086_);
lean_dec_ref(v_a_3085_);
lean_dec(v_a_3084_);
lean_dec_ref(v_a_3083_);
lean_dec(v_a_3082_);
return v___x_3097_;
}
}
else
{
lean_dec_ref(v_e_3081_);
lean_dec(v_a_3090_);
lean_dec_ref(v_a_3089_);
lean_dec(v_a_3088_);
lean_dec_ref(v_a_3087_);
lean_dec(v_a_3086_);
lean_dec_ref(v_a_3085_);
lean_dec(v_a_3084_);
lean_dec_ref(v_a_3083_);
lean_dec(v_a_3082_);
return v___x_3097_;
}
}
case 5:
{
lean_object* v___x_3102_; 
lean_inc(v_a_3090_);
lean_inc_ref(v_a_3089_);
lean_inc(v_a_3088_);
lean_inc_ref(v_a_3087_);
lean_inc(v_a_3086_);
lean_inc_ref(v_a_3085_);
lean_inc(v_a_3084_);
lean_inc_ref(v_a_3083_);
lean_inc(v_a_3082_);
lean_inc_ref(v_e_3081_);
v___x_3102_ = l_Lean_Meta_Tactic_Cbv_tryMatcher(v_e_3081_, v_a_3082_, v_a_3083_, v_a_3084_, v_a_3085_, v_a_3086_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_);
if (lean_obj_tag(v___x_3102_) == 0)
{
lean_object* v_a_3103_; 
v_a_3103_ = lean_ctor_get(v___x_3102_, 0);
lean_inc(v_a_3103_);
if (lean_obj_tag(v_a_3103_) == 0)
{
uint8_t v_done_3104_; 
v_done_3104_ = lean_ctor_get_uint8(v_a_3103_, 0);
lean_dec_ref(v_a_3103_);
if (v_done_3104_ == 0)
{
lean_object* v___x_3105_; 
lean_dec_ref(v___x_3102_);
v___x_3105_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn(v_e_3081_, v_a_3082_, v_a_3083_, v_a_3084_, v_a_3085_, v_a_3086_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_);
return v___x_3105_;
}
else
{
lean_dec_ref(v_e_3081_);
lean_dec(v_a_3090_);
lean_dec_ref(v_a_3089_);
lean_dec(v_a_3088_);
lean_dec_ref(v_a_3087_);
lean_dec(v_a_3086_);
lean_dec_ref(v_a_3085_);
lean_dec(v_a_3084_);
lean_dec_ref(v_a_3083_);
lean_dec(v_a_3082_);
return v___x_3102_;
}
}
else
{
lean_dec_ref(v_a_3103_);
lean_dec_ref(v_e_3081_);
lean_dec(v_a_3090_);
lean_dec_ref(v_a_3089_);
lean_dec(v_a_3088_);
lean_dec_ref(v_a_3087_);
lean_dec(v_a_3086_);
lean_dec_ref(v_a_3085_);
lean_dec(v_a_3084_);
lean_dec_ref(v_a_3083_);
lean_dec(v_a_3082_);
return v___x_3102_;
}
}
else
{
lean_dec_ref(v_e_3081_);
lean_dec(v_a_3090_);
lean_dec_ref(v_a_3089_);
lean_dec(v_a_3088_);
lean_dec_ref(v_a_3087_);
lean_dec(v_a_3086_);
lean_dec_ref(v_a_3085_);
lean_dec(v_a_3084_);
lean_dec_ref(v_a_3083_);
lean_dec(v_a_3082_);
return v___x_3102_;
}
}
case 8:
{
uint8_t v___x_3106_; 
lean_dec(v_a_3084_);
lean_dec_ref(v_a_3083_);
lean_dec(v_a_3082_);
v___x_3106_ = l_Lean_Expr_letNondep_x21(v_e_3081_);
if (v___x_3106_ == 0)
{
lean_object* v___x_3107_; 
lean_dec_ref(v_a_3085_);
v___x_3107_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg(v_e_3081_, v_a_3086_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_);
lean_dec(v_a_3086_);
return v___x_3107_;
}
else
{
lean_object* v___x_3108_; 
v___x_3108_ = l_Lean_Meta_Sym_Simp_toBetaApp(v_e_3081_, v_a_3085_, v_a_3086_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_);
if (lean_obj_tag(v___x_3108_) == 0)
{
lean_object* v_a_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3120_; 
v_a_3109_ = lean_ctor_get(v___x_3108_, 0);
v_isSharedCheck_3120_ = !lean_is_exclusive(v___x_3108_);
if (v_isSharedCheck_3120_ == 0)
{
v___x_3111_ = v___x_3108_;
v_isShared_3112_ = v_isSharedCheck_3120_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_a_3109_);
lean_dec(v___x_3108_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3120_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
lean_object* v_e_3113_; lean_object* v_h_3114_; uint8_t v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3118_; 
v_e_3113_ = lean_ctor_get(v_a_3109_, 2);
lean_inc_ref(v_e_3113_);
v_h_3114_ = lean_ctor_get(v_a_3109_, 3);
lean_inc_ref(v_h_3114_);
lean_dec(v_a_3109_);
v___x_3115_ = 0;
v___x_3116_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_3116_, 0, v_e_3113_);
lean_ctor_set(v___x_3116_, 1, v_h_3114_);
lean_ctor_set_uint8(v___x_3116_, sizeof(void*)*2, v___x_3115_);
if (v_isShared_3112_ == 0)
{
lean_ctor_set(v___x_3111_, 0, v___x_3116_);
v___x_3118_ = v___x_3111_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v___x_3116_);
v___x_3118_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
return v___x_3118_;
}
}
}
else
{
lean_object* v_a_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3128_; 
v_a_3121_ = lean_ctor_get(v___x_3108_, 0);
v_isSharedCheck_3128_ = !lean_is_exclusive(v___x_3108_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3123_ = v___x_3108_;
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_a_3121_);
lean_dec(v___x_3108_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v___x_3126_; 
if (v_isShared_3124_ == 0)
{
v___x_3126_ = v___x_3123_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v_a_3121_);
v___x_3126_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
return v___x_3126_;
}
}
}
}
}
case 7:
{
lean_dec_ref(v_e_3081_);
lean_dec(v_a_3090_);
lean_dec_ref(v_a_3089_);
lean_dec(v_a_3088_);
lean_dec_ref(v_a_3087_);
lean_dec(v_a_3086_);
lean_dec_ref(v_a_3085_);
lean_dec(v_a_3084_);
lean_dec_ref(v_a_3083_);
lean_dec(v_a_3082_);
goto v___jp_3092_;
}
case 6:
{
lean_dec_ref(v_e_3081_);
lean_dec(v_a_3090_);
lean_dec_ref(v_a_3089_);
lean_dec(v_a_3088_);
lean_dec_ref(v_a_3087_);
lean_dec(v_a_3086_);
lean_dec_ref(v_a_3085_);
lean_dec(v_a_3084_);
lean_dec_ref(v_a_3083_);
lean_dec(v_a_3082_);
goto v___jp_3092_;
}
case 1:
{
lean_object* v___x_3129_; lean_object* v___x_3130_; 
lean_dec_ref(v_e_3081_);
lean_dec(v_a_3090_);
lean_dec_ref(v_a_3089_);
lean_dec(v_a_3088_);
lean_dec_ref(v_a_3087_);
lean_dec(v_a_3086_);
lean_dec_ref(v_a_3085_);
lean_dec(v_a_3084_);
lean_dec_ref(v_a_3083_);
lean_dec(v_a_3082_);
v___x_3129_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__0));
v___x_3130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3130_, 0, v___x_3129_);
return v___x_3130_;
}
case 2:
{
lean_object* v___x_3131_; lean_object* v___x_3132_; 
lean_dec_ref(v_e_3081_);
lean_dec(v_a_3090_);
lean_dec_ref(v_a_3089_);
lean_dec(v_a_3088_);
lean_dec_ref(v_a_3087_);
lean_dec(v_a_3086_);
lean_dec_ref(v_a_3085_);
lean_dec(v_a_3084_);
lean_dec_ref(v_a_3083_);
lean_dec(v_a_3082_);
v___x_3131_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__0));
v___x_3132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3132_, 0, v___x_3131_);
return v___x_3132_;
}
case 0:
{
lean_object* v___x_3133_; lean_object* v___x_3134_; 
lean_dec_ref(v_e_3081_);
lean_dec(v_a_3090_);
lean_dec_ref(v_a_3089_);
lean_dec(v_a_3088_);
lean_dec_ref(v_a_3087_);
lean_dec(v_a_3086_);
lean_dec_ref(v_a_3085_);
lean_dec(v_a_3084_);
lean_dec_ref(v_a_3083_);
lean_dec(v_a_3082_);
v___x_3133_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__0));
v___x_3134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3134_, 0, v___x_3133_);
return v___x_3134_;
}
case 3:
{
lean_object* v___x_3135_; lean_object* v___x_3136_; 
lean_dec_ref(v_e_3081_);
lean_dec(v_a_3090_);
lean_dec_ref(v_a_3089_);
lean_dec(v_a_3088_);
lean_dec_ref(v_a_3087_);
lean_dec(v_a_3086_);
lean_dec_ref(v_a_3085_);
lean_dec(v_a_3084_);
lean_dec_ref(v_a_3083_);
lean_dec(v_a_3082_);
v___x_3135_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__0));
v___x_3136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3136_, 0, v___x_3135_);
return v___x_3136_;
}
default: 
{
lean_object* v___x_3137_; lean_object* v___x_3138_; 
lean_dec(v_a_3090_);
lean_dec_ref(v_a_3089_);
lean_dec(v_a_3088_);
lean_dec_ref(v_a_3087_);
lean_dec(v_a_3086_);
lean_dec_ref(v_a_3085_);
lean_dec(v_a_3084_);
lean_dec_ref(v_a_3083_);
lean_dec(v_a_3082_);
lean_dec_ref(v_e_3081_);
v___x_3137_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__9));
v___x_3138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3138_, 0, v___x_3137_);
return v___x_3138_;
}
}
v___jp_3092_:
{
lean_object* v___x_3093_; lean_object* v___x_3094_; 
v___x_3093_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__0));
v___x_3094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3094_, 0, v___x_3093_);
return v___x_3094_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___boxed(lean_object* v_e_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_, lean_object* v_a_3146_, lean_object* v_a_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_){
_start:
{
lean_object* v_res_3150_; 
v_res_3150_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep(v_e_3139_, v_a_3140_, v_a_3141_, v_a_3142_, v_a_3143_, v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_, v_a_3148_);
return v_res_3150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPre(lean_object* v_simprocs_3151_, lean_object* v_a_3152_, lean_object* v_a_3153_, lean_object* v_a_3154_, lean_object* v_a_3155_, lean_object* v_a_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_, lean_object* v_a_3159_, lean_object* v_a_3160_, lean_object* v_a_3161_){
_start:
{
lean_object* v___x_3163_; 
lean_inc_ref(v_a_3152_);
v___x_3163_ = l_Lean_Meta_Tactic_Cbv_isBuiltinValue___redArg(v_a_3152_);
if (lean_obj_tag(v___x_3163_) == 0)
{
lean_object* v_a_3164_; 
v_a_3164_ = lean_ctor_get(v___x_3163_, 0);
lean_inc(v_a_3164_);
if (lean_obj_tag(v_a_3164_) == 0)
{
uint8_t v_done_3165_; 
v_done_3165_ = lean_ctor_get_uint8(v_a_3164_, 0);
lean_dec_ref(v_a_3164_);
if (v_done_3165_ == 0)
{
lean_object* v___x_3166_; 
lean_dec_ref(v___x_3163_);
lean_inc(v_a_3161_);
lean_inc_ref(v_a_3160_);
lean_inc(v_a_3159_);
lean_inc_ref(v_a_3158_);
lean_inc_ref(v_a_3152_);
v___x_3166_ = l_Lean_Meta_Tactic_Cbv_isProofTerm___redArg(v_a_3152_, v_a_3156_, v_a_3157_, v_a_3158_, v_a_3159_, v_a_3160_, v_a_3161_);
if (lean_obj_tag(v___x_3166_) == 0)
{
lean_object* v_a_3167_; 
v_a_3167_ = lean_ctor_get(v___x_3166_, 0);
lean_inc(v_a_3167_);
if (lean_obj_tag(v_a_3167_) == 0)
{
uint8_t v_done_3168_; 
v_done_3168_ = lean_ctor_get_uint8(v_a_3167_, 0);
lean_dec_ref(v_a_3167_);
if (v_done_3168_ == 0)
{
lean_object* v_pre_3169_; lean_object* v_erased_3170_; lean_object* v___x_3171_; 
lean_dec_ref(v___x_3166_);
v_pre_3169_ = lean_ctor_get(v_simprocs_3151_, 0);
lean_inc_ref(v_pre_3169_);
v_erased_3170_ = lean_ctor_get(v_simprocs_3151_, 4);
lean_inc_ref(v_erased_3170_);
lean_dec_ref(v_simprocs_3151_);
lean_inc(v_a_3161_);
lean_inc_ref(v_a_3160_);
lean_inc(v_a_3159_);
lean_inc_ref(v_a_3158_);
lean_inc(v_a_3157_);
lean_inc_ref(v_a_3156_);
lean_inc(v_a_3155_);
lean_inc_ref(v_a_3154_);
lean_inc(v_a_3153_);
lean_inc_ref(v_a_3152_);
v___x_3171_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch(v_pre_3169_, v_erased_3170_, v_a_3152_, v_a_3153_, v_a_3154_, v_a_3155_, v_a_3156_, v_a_3157_, v_a_3158_, v_a_3159_, v_a_3160_, v_a_3161_);
if (lean_obj_tag(v___x_3171_) == 0)
{
lean_object* v_a_3172_; 
v_a_3172_ = lean_ctor_get(v___x_3171_, 0);
lean_inc(v_a_3172_);
if (lean_obj_tag(v_a_3172_) == 0)
{
uint8_t v_done_3173_; 
v_done_3173_ = lean_ctor_get_uint8(v_a_3172_, 0);
lean_dec_ref(v_a_3172_);
if (v_done_3173_ == 0)
{
lean_object* v___x_3174_; 
lean_dec_ref(v___x_3171_);
v___x_3174_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep(v_a_3152_, v_a_3153_, v_a_3154_, v_a_3155_, v_a_3156_, v_a_3157_, v_a_3158_, v_a_3159_, v_a_3160_, v_a_3161_);
return v___x_3174_;
}
else
{
lean_dec(v_a_3161_);
lean_dec_ref(v_a_3160_);
lean_dec(v_a_3159_);
lean_dec_ref(v_a_3158_);
lean_dec(v_a_3157_);
lean_dec_ref(v_a_3156_);
lean_dec(v_a_3155_);
lean_dec_ref(v_a_3154_);
lean_dec(v_a_3153_);
lean_dec_ref(v_a_3152_);
return v___x_3171_;
}
}
else
{
lean_dec_ref(v_a_3172_);
lean_dec(v_a_3161_);
lean_dec_ref(v_a_3160_);
lean_dec(v_a_3159_);
lean_dec_ref(v_a_3158_);
lean_dec(v_a_3157_);
lean_dec_ref(v_a_3156_);
lean_dec(v_a_3155_);
lean_dec_ref(v_a_3154_);
lean_dec(v_a_3153_);
lean_dec_ref(v_a_3152_);
return v___x_3171_;
}
}
else
{
lean_dec(v_a_3161_);
lean_dec_ref(v_a_3160_);
lean_dec(v_a_3159_);
lean_dec_ref(v_a_3158_);
lean_dec(v_a_3157_);
lean_dec_ref(v_a_3156_);
lean_dec(v_a_3155_);
lean_dec_ref(v_a_3154_);
lean_dec(v_a_3153_);
lean_dec_ref(v_a_3152_);
return v___x_3171_;
}
}
else
{
lean_dec(v_a_3161_);
lean_dec_ref(v_a_3160_);
lean_dec(v_a_3159_);
lean_dec_ref(v_a_3158_);
lean_dec(v_a_3157_);
lean_dec_ref(v_a_3156_);
lean_dec(v_a_3155_);
lean_dec_ref(v_a_3154_);
lean_dec(v_a_3153_);
lean_dec_ref(v_a_3152_);
lean_dec_ref(v_simprocs_3151_);
return v___x_3166_;
}
}
else
{
lean_dec_ref(v_a_3167_);
lean_dec(v_a_3161_);
lean_dec_ref(v_a_3160_);
lean_dec(v_a_3159_);
lean_dec_ref(v_a_3158_);
lean_dec(v_a_3157_);
lean_dec_ref(v_a_3156_);
lean_dec(v_a_3155_);
lean_dec_ref(v_a_3154_);
lean_dec(v_a_3153_);
lean_dec_ref(v_a_3152_);
lean_dec_ref(v_simprocs_3151_);
return v___x_3166_;
}
}
else
{
lean_dec(v_a_3161_);
lean_dec_ref(v_a_3160_);
lean_dec(v_a_3159_);
lean_dec_ref(v_a_3158_);
lean_dec(v_a_3157_);
lean_dec_ref(v_a_3156_);
lean_dec(v_a_3155_);
lean_dec_ref(v_a_3154_);
lean_dec(v_a_3153_);
lean_dec_ref(v_a_3152_);
lean_dec_ref(v_simprocs_3151_);
return v___x_3166_;
}
}
else
{
lean_dec(v_a_3161_);
lean_dec_ref(v_a_3160_);
lean_dec(v_a_3159_);
lean_dec_ref(v_a_3158_);
lean_dec(v_a_3157_);
lean_dec_ref(v_a_3156_);
lean_dec(v_a_3155_);
lean_dec_ref(v_a_3154_);
lean_dec(v_a_3153_);
lean_dec_ref(v_a_3152_);
lean_dec_ref(v_simprocs_3151_);
return v___x_3163_;
}
}
else
{
lean_dec_ref(v_a_3164_);
lean_dec(v_a_3161_);
lean_dec_ref(v_a_3160_);
lean_dec(v_a_3159_);
lean_dec_ref(v_a_3158_);
lean_dec(v_a_3157_);
lean_dec_ref(v_a_3156_);
lean_dec(v_a_3155_);
lean_dec_ref(v_a_3154_);
lean_dec(v_a_3153_);
lean_dec_ref(v_a_3152_);
lean_dec_ref(v_simprocs_3151_);
return v___x_3163_;
}
}
else
{
lean_dec(v_a_3161_);
lean_dec_ref(v_a_3160_);
lean_dec(v_a_3159_);
lean_dec_ref(v_a_3158_);
lean_dec(v_a_3157_);
lean_dec_ref(v_a_3156_);
lean_dec(v_a_3155_);
lean_dec_ref(v_a_3154_);
lean_dec(v_a_3153_);
lean_dec_ref(v_a_3152_);
lean_dec_ref(v_simprocs_3151_);
return v___x_3163_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPre___boxed(lean_object* v_simprocs_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_, lean_object* v_a_3178_, lean_object* v_a_3179_, lean_object* v_a_3180_, lean_object* v_a_3181_, lean_object* v_a_3182_, lean_object* v_a_3183_, lean_object* v_a_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_){
_start:
{
lean_object* v_res_3187_; 
v_res_3187_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPre(v_simprocs_3175_, v_a_3176_, v_a_3177_, v_a_3178_, v_a_3179_, v_a_3180_, v_a_3181_, v_a_3182_, v_a_3183_, v_a_3184_, v_a_3185_);
return v_res_3187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPost(lean_object* v_simprocs_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_, lean_object* v_a_3193_, lean_object* v_a_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_){
_start:
{
lean_object* v___x_3200_; lean_object* v___x_3201_; 
v___x_3200_ = lean_unsigned_to_nat(255u);
lean_inc(v_a_3198_);
lean_inc_ref(v_a_3197_);
lean_inc(v_a_3196_);
lean_inc_ref(v_a_3195_);
lean_inc_ref(v_a_3189_);
v___x_3201_ = l_Lean_Meta_Sym_Simp_evalGround___redArg(v___x_3200_, v_a_3189_, v_a_3193_, v_a_3194_, v_a_3195_, v_a_3196_, v_a_3197_, v_a_3198_);
if (lean_obj_tag(v___x_3201_) == 0)
{
lean_object* v_a_3202_; 
v_a_3202_ = lean_ctor_get(v___x_3201_, 0);
lean_inc(v_a_3202_);
if (lean_obj_tag(v_a_3202_) == 0)
{
uint8_t v_done_3203_; 
v_done_3203_ = lean_ctor_get_uint8(v_a_3202_, 0);
lean_dec_ref(v_a_3202_);
if (v_done_3203_ == 0)
{
lean_object* v_eval_3204_; lean_object* v_post_3205_; lean_object* v_erased_3206_; lean_object* v___x_3207_; 
lean_dec_ref(v___x_3201_);
v_eval_3204_ = lean_ctor_get(v_simprocs_3188_, 1);
lean_inc_ref(v_eval_3204_);
v_post_3205_ = lean_ctor_get(v_simprocs_3188_, 2);
lean_inc_ref(v_post_3205_);
v_erased_3206_ = lean_ctor_get(v_simprocs_3188_, 4);
lean_inc_ref(v_erased_3206_);
lean_dec_ref(v_simprocs_3188_);
lean_inc(v_a_3198_);
lean_inc_ref(v_a_3197_);
lean_inc(v_a_3196_);
lean_inc_ref(v_a_3195_);
lean_inc(v_a_3194_);
lean_inc_ref(v_a_3193_);
lean_inc(v_a_3192_);
lean_inc_ref(v_a_3191_);
lean_inc(v_a_3190_);
lean_inc_ref(v_a_3189_);
lean_inc_ref(v_erased_3206_);
v___x_3207_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch(v_eval_3204_, v_erased_3206_, v_a_3189_, v_a_3190_, v_a_3191_, v_a_3192_, v_a_3193_, v_a_3194_, v_a_3195_, v_a_3196_, v_a_3197_, v_a_3198_);
if (lean_obj_tag(v___x_3207_) == 0)
{
lean_object* v_a_3208_; 
v_a_3208_ = lean_ctor_get(v___x_3207_, 0);
lean_inc(v_a_3208_);
if (lean_obj_tag(v_a_3208_) == 0)
{
uint8_t v_done_3209_; 
v_done_3209_ = lean_ctor_get_uint8(v_a_3208_, 0);
lean_dec_ref(v_a_3208_);
if (v_done_3209_ == 0)
{
lean_object* v___x_3210_; 
lean_dec_ref(v___x_3207_);
lean_inc(v_a_3198_);
lean_inc_ref(v_a_3197_);
lean_inc(v_a_3196_);
lean_inc_ref(v_a_3195_);
lean_inc(v_a_3194_);
lean_inc_ref(v_a_3193_);
lean_inc(v_a_3192_);
lean_inc_ref(v_a_3191_);
lean_inc(v_a_3190_);
lean_inc_ref(v_a_3189_);
v___x_3210_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp(v_a_3189_, v_a_3190_, v_a_3191_, v_a_3192_, v_a_3193_, v_a_3194_, v_a_3195_, v_a_3196_, v_a_3197_, v_a_3198_);
if (lean_obj_tag(v___x_3210_) == 0)
{
lean_object* v_a_3211_; 
v_a_3211_ = lean_ctor_get(v___x_3210_, 0);
lean_inc(v_a_3211_);
if (lean_obj_tag(v_a_3211_) == 0)
{
uint8_t v_done_3212_; 
v_done_3212_ = lean_ctor_get_uint8(v_a_3211_, 0);
lean_dec_ref(v_a_3211_);
if (v_done_3212_ == 0)
{
lean_object* v___x_3213_; 
lean_dec_ref(v___x_3210_);
v___x_3213_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch(v_post_3205_, v_erased_3206_, v_a_3189_, v_a_3190_, v_a_3191_, v_a_3192_, v_a_3193_, v_a_3194_, v_a_3195_, v_a_3196_, v_a_3197_, v_a_3198_);
return v___x_3213_;
}
else
{
lean_dec_ref(v_erased_3206_);
lean_dec_ref(v_post_3205_);
lean_dec(v_a_3198_);
lean_dec_ref(v_a_3197_);
lean_dec(v_a_3196_);
lean_dec_ref(v_a_3195_);
lean_dec(v_a_3194_);
lean_dec_ref(v_a_3193_);
lean_dec(v_a_3192_);
lean_dec_ref(v_a_3191_);
lean_dec(v_a_3190_);
lean_dec_ref(v_a_3189_);
return v___x_3210_;
}
}
else
{
lean_dec_ref(v_a_3211_);
lean_dec_ref(v_erased_3206_);
lean_dec_ref(v_post_3205_);
lean_dec(v_a_3198_);
lean_dec_ref(v_a_3197_);
lean_dec(v_a_3196_);
lean_dec_ref(v_a_3195_);
lean_dec(v_a_3194_);
lean_dec_ref(v_a_3193_);
lean_dec(v_a_3192_);
lean_dec_ref(v_a_3191_);
lean_dec(v_a_3190_);
lean_dec_ref(v_a_3189_);
return v___x_3210_;
}
}
else
{
lean_dec_ref(v_erased_3206_);
lean_dec_ref(v_post_3205_);
lean_dec(v_a_3198_);
lean_dec_ref(v_a_3197_);
lean_dec(v_a_3196_);
lean_dec_ref(v_a_3195_);
lean_dec(v_a_3194_);
lean_dec_ref(v_a_3193_);
lean_dec(v_a_3192_);
lean_dec_ref(v_a_3191_);
lean_dec(v_a_3190_);
lean_dec_ref(v_a_3189_);
return v___x_3210_;
}
}
else
{
lean_dec_ref(v_erased_3206_);
lean_dec_ref(v_post_3205_);
lean_dec(v_a_3198_);
lean_dec_ref(v_a_3197_);
lean_dec(v_a_3196_);
lean_dec_ref(v_a_3195_);
lean_dec(v_a_3194_);
lean_dec_ref(v_a_3193_);
lean_dec(v_a_3192_);
lean_dec_ref(v_a_3191_);
lean_dec(v_a_3190_);
lean_dec_ref(v_a_3189_);
return v___x_3207_;
}
}
else
{
lean_dec_ref(v_a_3208_);
lean_dec_ref(v_erased_3206_);
lean_dec_ref(v_post_3205_);
lean_dec(v_a_3198_);
lean_dec_ref(v_a_3197_);
lean_dec(v_a_3196_);
lean_dec_ref(v_a_3195_);
lean_dec(v_a_3194_);
lean_dec_ref(v_a_3193_);
lean_dec(v_a_3192_);
lean_dec_ref(v_a_3191_);
lean_dec(v_a_3190_);
lean_dec_ref(v_a_3189_);
return v___x_3207_;
}
}
else
{
lean_dec_ref(v_erased_3206_);
lean_dec_ref(v_post_3205_);
lean_dec(v_a_3198_);
lean_dec_ref(v_a_3197_);
lean_dec(v_a_3196_);
lean_dec_ref(v_a_3195_);
lean_dec(v_a_3194_);
lean_dec_ref(v_a_3193_);
lean_dec(v_a_3192_);
lean_dec_ref(v_a_3191_);
lean_dec(v_a_3190_);
lean_dec_ref(v_a_3189_);
return v___x_3207_;
}
}
else
{
lean_dec(v_a_3198_);
lean_dec_ref(v_a_3197_);
lean_dec(v_a_3196_);
lean_dec_ref(v_a_3195_);
lean_dec(v_a_3194_);
lean_dec_ref(v_a_3193_);
lean_dec(v_a_3192_);
lean_dec_ref(v_a_3191_);
lean_dec(v_a_3190_);
lean_dec_ref(v_a_3189_);
lean_dec_ref(v_simprocs_3188_);
return v___x_3201_;
}
}
else
{
lean_dec_ref(v_a_3202_);
lean_dec(v_a_3198_);
lean_dec_ref(v_a_3197_);
lean_dec(v_a_3196_);
lean_dec_ref(v_a_3195_);
lean_dec(v_a_3194_);
lean_dec_ref(v_a_3193_);
lean_dec(v_a_3192_);
lean_dec_ref(v_a_3191_);
lean_dec(v_a_3190_);
lean_dec_ref(v_a_3189_);
lean_dec_ref(v_simprocs_3188_);
return v___x_3201_;
}
}
else
{
lean_dec(v_a_3198_);
lean_dec_ref(v_a_3197_);
lean_dec(v_a_3196_);
lean_dec_ref(v_a_3195_);
lean_dec(v_a_3194_);
lean_dec_ref(v_a_3193_);
lean_dec(v_a_3192_);
lean_dec_ref(v_a_3191_);
lean_dec(v_a_3190_);
lean_dec_ref(v_a_3189_);
lean_dec_ref(v_simprocs_3188_);
return v___x_3201_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPost___boxed(lean_object* v_simprocs_3214_, lean_object* v_a_3215_, lean_object* v_a_3216_, lean_object* v_a_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_){
_start:
{
lean_object* v_res_3226_; 
v_res_3226_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPost(v_simprocs_3214_, v_a_3215_, v_a_3216_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_);
return v_res_3226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(lean_object* v_simprocs_3227_){
_start:
{
lean_object* v___x_3228_; lean_object* v___x_3229_; uint8_t v___x_3230_; lean_object* v___x_3231_; 
lean_inc_ref(v_simprocs_3227_);
v___x_3228_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPre___boxed), 12, 1);
lean_closure_set(v___x_3228_, 0, v_simprocs_3227_);
v___x_3229_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPost___boxed), 12, 1);
lean_closure_set(v___x_3229_, 0, v_simprocs_3227_);
v___x_3230_ = 1;
v___x_3231_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3231_, 0, v___x_3228_);
lean_ctor_set(v___x_3231_, 1, v___x_3229_);
lean_ctor_set_uint8(v___x_3231_, sizeof(void*)*2, v___x_3230_);
return v___x_3231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(lean_object* v_e_3232_, lean_object* v_config_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_){
_start:
{
lean_object* v___x_3241_; 
v___x_3241_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_3239_);
if (lean_obj_tag(v___x_3241_) == 0)
{
lean_object* v_a_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; 
v_a_3242_ = lean_ctor_get(v___x_3241_, 0);
lean_inc(v_a_3242_);
lean_dec_ref(v___x_3241_);
v___x_3243_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(v_a_3242_);
v___x_3244_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_3244_, 0, v_e_3232_);
v___x_3245_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v___x_3244_, v___x_3243_, v_config_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_);
return v___x_3245_;
}
else
{
lean_object* v_a_3246_; lean_object* v___x_3248_; uint8_t v_isShared_3249_; uint8_t v_isSharedCheck_3253_; 
lean_dec(v_a_3239_);
lean_dec_ref(v_a_3238_);
lean_dec(v_a_3237_);
lean_dec_ref(v_a_3236_);
lean_dec(v_a_3235_);
lean_dec_ref(v_a_3234_);
lean_dec_ref(v_config_3233_);
lean_dec_ref(v_e_3232_);
v_a_3246_ = lean_ctor_get(v___x_3241_, 0);
v_isSharedCheck_3253_ = !lean_is_exclusive(v___x_3241_);
if (v_isSharedCheck_3253_ == 0)
{
v___x_3248_ = v___x_3241_;
v_isShared_3249_ = v_isSharedCheck_3253_;
goto v_resetjp_3247_;
}
else
{
lean_inc(v_a_3246_);
lean_dec(v___x_3241_);
v___x_3248_ = lean_box(0);
v_isShared_3249_ = v_isSharedCheck_3253_;
goto v_resetjp_3247_;
}
v_resetjp_3247_:
{
lean_object* v___x_3251_; 
if (v_isShared_3249_ == 0)
{
v___x_3251_ = v___x_3248_;
goto v_reusejp_3250_;
}
else
{
lean_object* v_reuseFailAlloc_3252_; 
v_reuseFailAlloc_3252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3252_, 0, v_a_3246_);
v___x_3251_ = v_reuseFailAlloc_3252_;
goto v_reusejp_3250_;
}
v_reusejp_3250_:
{
return v___x_3251_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore___boxed(lean_object* v_e_3254_, lean_object* v_config_3255_, lean_object* v_a_3256_, lean_object* v_a_3257_, lean_object* v_a_3258_, lean_object* v_a_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_){
_start:
{
lean_object* v_res_3263_; 
v_res_3263_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v_e_3254_, v_config_3255_, v_a_3256_, v_a_3257_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_);
return v_res_3263_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg(lean_object* v_cls_3264_, lean_object* v___y_3265_){
_start:
{
lean_object* v_options_3267_; uint8_t v_hasTrace_3268_; 
v_options_3267_ = lean_ctor_get(v___y_3265_, 2);
v_hasTrace_3268_ = lean_ctor_get_uint8(v_options_3267_, sizeof(void*)*1);
if (v_hasTrace_3268_ == 0)
{
lean_object* v___x_3269_; lean_object* v___x_3270_; 
lean_dec(v_cls_3264_);
v___x_3269_ = lean_box(v_hasTrace_3268_);
v___x_3270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3270_, 0, v___x_3269_);
return v___x_3270_;
}
else
{
lean_object* v_inheritedTraceOptions_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; uint8_t v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; 
v_inheritedTraceOptions_3271_ = lean_ctor_get(v___y_3265_, 13);
v___x_3272_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__1));
v___x_3273_ = l_Lean_Name_append(v___x_3272_, v_cls_3264_);
v___x_3274_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3271_, v_options_3267_, v___x_3273_);
lean_dec(v___x_3273_);
v___x_3275_ = lean_box(v___x_3274_);
v___x_3276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3276_, 0, v___x_3275_);
return v___x_3276_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg___boxed(lean_object* v_cls_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_){
_start:
{
lean_object* v_res_3280_; 
v_res_3280_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg(v_cls_3277_, v___y_3278_);
lean_dec_ref(v___y_3278_);
return v_res_3280_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0(lean_object* v_cls_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_){
_start:
{
lean_object* v___x_3287_; 
v___x_3287_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg(v_cls_3281_, v___y_3284_);
return v___x_3287_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___boxed(lean_object* v_cls_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_){
_start:
{
lean_object* v_res_3294_; 
v_res_3294_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0(v_cls_3288_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_);
lean_dec(v___y_3292_);
lean_dec_ref(v___y_3291_);
lean_dec(v___y_3290_);
lean_dec_ref(v___y_3289_);
return v_res_3294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1___redArg(lean_object* v___y_3295_){
_start:
{
lean_object* v___x_3297_; lean_object* v_traceState_3298_; lean_object* v_traces_3299_; lean_object* v___x_3300_; lean_object* v_traceState_3301_; lean_object* v_env_3302_; lean_object* v_nextMacroScope_3303_; lean_object* v_ngen_3304_; lean_object* v_auxDeclNGen_3305_; lean_object* v_cache_3306_; lean_object* v_messages_3307_; lean_object* v_infoState_3308_; lean_object* v_snapshotTasks_3309_; lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3330_; 
v___x_3297_ = lean_st_ref_get(v___y_3295_);
v_traceState_3298_ = lean_ctor_get(v___x_3297_, 4);
lean_inc_ref(v_traceState_3298_);
lean_dec(v___x_3297_);
v_traces_3299_ = lean_ctor_get(v_traceState_3298_, 0);
lean_inc_ref(v_traces_3299_);
lean_dec_ref(v_traceState_3298_);
v___x_3300_ = lean_st_ref_take(v___y_3295_);
v_traceState_3301_ = lean_ctor_get(v___x_3300_, 4);
v_env_3302_ = lean_ctor_get(v___x_3300_, 0);
v_nextMacroScope_3303_ = lean_ctor_get(v___x_3300_, 1);
v_ngen_3304_ = lean_ctor_get(v___x_3300_, 2);
v_auxDeclNGen_3305_ = lean_ctor_get(v___x_3300_, 3);
v_cache_3306_ = lean_ctor_get(v___x_3300_, 5);
v_messages_3307_ = lean_ctor_get(v___x_3300_, 6);
v_infoState_3308_ = lean_ctor_get(v___x_3300_, 7);
v_snapshotTasks_3309_ = lean_ctor_get(v___x_3300_, 8);
v_isSharedCheck_3330_ = !lean_is_exclusive(v___x_3300_);
if (v_isSharedCheck_3330_ == 0)
{
v___x_3311_ = v___x_3300_;
v_isShared_3312_ = v_isSharedCheck_3330_;
goto v_resetjp_3310_;
}
else
{
lean_inc(v_snapshotTasks_3309_);
lean_inc(v_infoState_3308_);
lean_inc(v_messages_3307_);
lean_inc(v_cache_3306_);
lean_inc(v_traceState_3301_);
lean_inc(v_auxDeclNGen_3305_);
lean_inc(v_ngen_3304_);
lean_inc(v_nextMacroScope_3303_);
lean_inc(v_env_3302_);
lean_dec(v___x_3300_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3330_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
uint64_t v_tid_3313_; lean_object* v___x_3315_; uint8_t v_isShared_3316_; uint8_t v_isSharedCheck_3328_; 
v_tid_3313_ = lean_ctor_get_uint64(v_traceState_3301_, sizeof(void*)*1);
v_isSharedCheck_3328_ = !lean_is_exclusive(v_traceState_3301_);
if (v_isSharedCheck_3328_ == 0)
{
lean_object* v_unused_3329_; 
v_unused_3329_ = lean_ctor_get(v_traceState_3301_, 0);
lean_dec(v_unused_3329_);
v___x_3315_ = v_traceState_3301_;
v_isShared_3316_ = v_isSharedCheck_3328_;
goto v_resetjp_3314_;
}
else
{
lean_dec(v_traceState_3301_);
v___x_3315_ = lean_box(0);
v_isShared_3316_ = v_isSharedCheck_3328_;
goto v_resetjp_3314_;
}
v_resetjp_3314_:
{
lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3321_; 
v___x_3317_ = lean_unsigned_to_nat(32u);
v___x_3318_ = lean_mk_empty_array_with_capacity(v___x_3317_);
lean_dec_ref(v___x_3318_);
v___x_3319_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___redArg___closed__1);
if (v_isShared_3316_ == 0)
{
lean_ctor_set(v___x_3315_, 0, v___x_3319_);
v___x_3321_ = v___x_3315_;
goto v_reusejp_3320_;
}
else
{
lean_object* v_reuseFailAlloc_3327_; 
v_reuseFailAlloc_3327_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3327_, 0, v___x_3319_);
lean_ctor_set_uint64(v_reuseFailAlloc_3327_, sizeof(void*)*1, v_tid_3313_);
v___x_3321_ = v_reuseFailAlloc_3327_;
goto v_reusejp_3320_;
}
v_reusejp_3320_:
{
lean_object* v___x_3323_; 
if (v_isShared_3312_ == 0)
{
lean_ctor_set(v___x_3311_, 4, v___x_3321_);
v___x_3323_ = v___x_3311_;
goto v_reusejp_3322_;
}
else
{
lean_object* v_reuseFailAlloc_3326_; 
v_reuseFailAlloc_3326_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3326_, 0, v_env_3302_);
lean_ctor_set(v_reuseFailAlloc_3326_, 1, v_nextMacroScope_3303_);
lean_ctor_set(v_reuseFailAlloc_3326_, 2, v_ngen_3304_);
lean_ctor_set(v_reuseFailAlloc_3326_, 3, v_auxDeclNGen_3305_);
lean_ctor_set(v_reuseFailAlloc_3326_, 4, v___x_3321_);
lean_ctor_set(v_reuseFailAlloc_3326_, 5, v_cache_3306_);
lean_ctor_set(v_reuseFailAlloc_3326_, 6, v_messages_3307_);
lean_ctor_set(v_reuseFailAlloc_3326_, 7, v_infoState_3308_);
lean_ctor_set(v_reuseFailAlloc_3326_, 8, v_snapshotTasks_3309_);
v___x_3323_ = v_reuseFailAlloc_3326_;
goto v_reusejp_3322_;
}
v_reusejp_3322_:
{
lean_object* v___x_3324_; lean_object* v___x_3325_; 
v___x_3324_ = lean_st_ref_set(v___y_3295_, v___x_3323_);
v___x_3325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3325_, 0, v_traces_3299_);
return v___x_3325_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1___redArg___boxed(lean_object* v___y_3331_, lean_object* v___y_3332_){
_start:
{
lean_object* v_res_3333_; 
v_res_3333_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1___redArg(v___y_3331_);
lean_dec(v___y_3331_);
return v_res_3333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1(lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_){
_start:
{
lean_object* v___x_3339_; 
v___x_3339_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1___redArg(v___y_3337_);
return v___x_3339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1___boxed(lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_){
_start:
{
lean_object* v_res_3345_; 
v_res_3345_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1(v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_);
lean_dec(v___y_3343_);
lean_dec_ref(v___y_3342_);
lean_dec(v___y_3341_);
lean_dec_ref(v___y_3340_);
return v_res_3345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0(lean_object* v_a_3346_, lean_object* v___x_3347_, lean_object* v___x_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_){
_start:
{
lean_object* v___x_3356_; 
v___x_3356_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_3346_, v___y_3350_);
if (lean_obj_tag(v___x_3356_) == 0)
{
lean_object* v_a_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; 
v_a_3357_ = lean_ctor_get(v___x_3356_, 0);
lean_inc(v_a_3357_);
lean_dec_ref(v___x_3356_);
v___x_3358_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_3358_, 0, v_a_3357_);
v___x_3359_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v___x_3358_, v___x_3347_, v___x_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_);
return v___x_3359_;
}
else
{
lean_object* v_a_3360_; lean_object* v___x_3362_; uint8_t v_isShared_3363_; uint8_t v_isSharedCheck_3367_; 
lean_dec(v___y_3354_);
lean_dec_ref(v___y_3353_);
lean_dec(v___y_3352_);
lean_dec_ref(v___y_3351_);
lean_dec(v___y_3350_);
lean_dec_ref(v___y_3349_);
lean_dec_ref(v___x_3348_);
lean_dec_ref(v___x_3347_);
v_a_3360_ = lean_ctor_get(v___x_3356_, 0);
v_isSharedCheck_3367_ = !lean_is_exclusive(v___x_3356_);
if (v_isSharedCheck_3367_ == 0)
{
v___x_3362_ = v___x_3356_;
v_isShared_3363_ = v_isSharedCheck_3367_;
goto v_resetjp_3361_;
}
else
{
lean_inc(v_a_3360_);
lean_dec(v___x_3356_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___boxed(lean_object* v_a_3368_, lean_object* v___x_3369_, lean_object* v___x_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_){
_start:
{
lean_object* v_res_3378_; 
v_res_3378_ = l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0(v_a_3368_, v___x_3369_, v___x_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_);
return v_res_3378_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3380_; lean_object* v___x_3381_; 
v___x_3380_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__0));
v___x_3381_ = l_Lean_stringToMessageData(v___x_3380_);
return v___x_3381_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3383_; lean_object* v___x_3384_; 
v___x_3383_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__2));
v___x_3384_ = l_Lean_stringToMessageData(v___x_3383_);
return v___x_3384_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__5(void){
_start:
{
lean_object* v___x_3386_; lean_object* v___x_3387_; 
v___x_3386_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__4));
v___x_3387_ = l_Lean_stringToMessageData(v___x_3386_);
return v___x_3387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1(lean_object* v_e_3388_, lean_object* v_x_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_){
_start:
{
if (lean_obj_tag(v_x_3389_) == 0)
{
lean_object* v_a_3395_; lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3405_; 
lean_dec_ref(v_e_3388_);
v_a_3395_ = lean_ctor_get(v_x_3389_, 0);
v_isSharedCheck_3405_ = !lean_is_exclusive(v_x_3389_);
if (v_isSharedCheck_3405_ == 0)
{
v___x_3397_ = v_x_3389_;
v_isShared_3398_ = v_isSharedCheck_3405_;
goto v_resetjp_3396_;
}
else
{
lean_inc(v_a_3395_);
lean_dec(v_x_3389_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3405_;
goto v_resetjp_3396_;
}
v_resetjp_3396_:
{
lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3403_; 
v___x_3399_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__1);
v___x_3400_ = l_Lean_Exception_toMessageData(v_a_3395_);
v___x_3401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3401_, 0, v___x_3399_);
lean_ctor_set(v___x_3401_, 1, v___x_3400_);
if (v_isShared_3398_ == 0)
{
lean_ctor_set(v___x_3397_, 0, v___x_3401_);
v___x_3403_ = v___x_3397_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v___x_3401_);
v___x_3403_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
return v___x_3403_;
}
}
}
else
{
lean_object* v_a_3406_; lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3427_; 
v_a_3406_ = lean_ctor_get(v_x_3389_, 0);
v_isSharedCheck_3427_ = !lean_is_exclusive(v_x_3389_);
if (v_isSharedCheck_3427_ == 0)
{
v___x_3408_ = v_x_3389_;
v_isShared_3409_ = v_isSharedCheck_3427_;
goto v_resetjp_3407_;
}
else
{
lean_inc(v_a_3406_);
lean_dec(v_x_3389_);
v___x_3408_ = lean_box(0);
v_isShared_3409_ = v_isSharedCheck_3427_;
goto v_resetjp_3407_;
}
v_resetjp_3407_:
{
if (lean_obj_tag(v_a_3406_) == 0)
{
lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3414_; 
lean_dec_ref(v_a_3406_);
v___x_3410_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__3, &l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__3);
v___x_3411_ = l_Lean_indentExpr(v_e_3388_);
v___x_3412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3412_, 0, v___x_3410_);
lean_ctor_set(v___x_3412_, 1, v___x_3411_);
if (v_isShared_3409_ == 0)
{
lean_ctor_set_tag(v___x_3408_, 0);
lean_ctor_set(v___x_3408_, 0, v___x_3412_);
v___x_3414_ = v___x_3408_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3415_; 
v_reuseFailAlloc_3415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3415_, 0, v___x_3412_);
v___x_3414_ = v_reuseFailAlloc_3415_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
return v___x_3414_;
}
}
else
{
lean_object* v_e_x27_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3425_; 
v_e_x27_3416_ = lean_ctor_get(v_a_3406_, 0);
lean_inc_ref(v_e_x27_3416_);
lean_dec_ref(v_a_3406_);
v___x_3417_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__5, &l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__5_once, _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__5);
v___x_3418_ = l_Lean_indentExpr(v_e_3388_);
v___x_3419_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3419_, 0, v___x_3417_);
lean_ctor_set(v___x_3419_, 1, v___x_3418_);
v___x_3420_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7);
v___x_3421_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3421_, 0, v___x_3419_);
lean_ctor_set(v___x_3421_, 1, v___x_3420_);
v___x_3422_ = l_Lean_indentExpr(v_e_x27_3416_);
v___x_3423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3423_, 0, v___x_3421_);
lean_ctor_set(v___x_3423_, 1, v___x_3422_);
if (v_isShared_3409_ == 0)
{
lean_ctor_set_tag(v___x_3408_, 0);
lean_ctor_set(v___x_3408_, 0, v___x_3423_);
v___x_3425_ = v___x_3408_;
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___boxed(lean_object* v_e_3428_, lean_object* v_x_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_){
_start:
{
lean_object* v_res_3435_; 
v_res_3435_ = l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1(v_e_3428_, v_x_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_);
lean_dec(v___y_3433_);
lean_dec_ref(v___y_3432_);
lean_dec(v___y_3431_);
lean_dec_ref(v___y_3430_);
return v_res_3435_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__2_spec__3___redArg(lean_object* v_x_3436_){
_start:
{
if (lean_obj_tag(v_x_3436_) == 0)
{
lean_object* v_a_3438_; lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3445_; 
v_a_3438_ = lean_ctor_get(v_x_3436_, 0);
v_isSharedCheck_3445_ = !lean_is_exclusive(v_x_3436_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3440_ = v_x_3436_;
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
else
{
lean_inc(v_a_3438_);
lean_dec(v_x_3436_);
v___x_3440_ = lean_box(0);
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
v_resetjp_3439_:
{
lean_object* v___x_3443_; 
if (v_isShared_3441_ == 0)
{
lean_ctor_set_tag(v___x_3440_, 1);
v___x_3443_ = v___x_3440_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v_a_3438_);
v___x_3443_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
return v___x_3443_;
}
}
}
else
{
lean_object* v_a_3446_; lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3453_; 
v_a_3446_ = lean_ctor_get(v_x_3436_, 0);
v_isSharedCheck_3453_ = !lean_is_exclusive(v_x_3436_);
if (v_isSharedCheck_3453_ == 0)
{
v___x_3448_ = v_x_3436_;
v_isShared_3449_ = v_isSharedCheck_3453_;
goto v_resetjp_3447_;
}
else
{
lean_inc(v_a_3446_);
lean_dec(v_x_3436_);
v___x_3448_ = lean_box(0);
v_isShared_3449_ = v_isSharedCheck_3453_;
goto v_resetjp_3447_;
}
v_resetjp_3447_:
{
lean_object* v___x_3451_; 
if (v_isShared_3449_ == 0)
{
lean_ctor_set_tag(v___x_3448_, 0);
v___x_3451_ = v___x_3448_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v_a_3446_);
v___x_3451_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
return v___x_3451_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__2_spec__3___redArg___boxed(lean_object* v_x_3454_, lean_object* v___y_3455_){
_start:
{
lean_object* v_res_3456_; 
v_res_3456_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__2_spec__3___redArg(v_x_3454_);
return v_res_3456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__2_spec__2(lean_object* v_oldTraces_3457_, lean_object* v_data_3458_, lean_object* v_ref_3459_, lean_object* v_msg_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_){
_start:
{
lean_object* v_fileName_3466_; lean_object* v_fileMap_3467_; lean_object* v_options_3468_; lean_object* v_currRecDepth_3469_; lean_object* v_maxRecDepth_3470_; lean_object* v_ref_3471_; lean_object* v_currNamespace_3472_; lean_object* v_openDecls_3473_; lean_object* v_initHeartbeats_3474_; lean_object* v_maxHeartbeats_3475_; lean_object* v_quotContext_3476_; lean_object* v_currMacroScope_3477_; uint8_t v_diag_3478_; lean_object* v_cancelTk_x3f_3479_; uint8_t v_suppressElabErrors_3480_; lean_object* v_inheritedTraceOptions_3481_; lean_object* v___x_3483_; uint8_t v_isShared_3484_; uint8_t v_isSharedCheck_3536_; 
v_fileName_3466_ = lean_ctor_get(v___y_3463_, 0);
v_fileMap_3467_ = lean_ctor_get(v___y_3463_, 1);
v_options_3468_ = lean_ctor_get(v___y_3463_, 2);
v_currRecDepth_3469_ = lean_ctor_get(v___y_3463_, 3);
v_maxRecDepth_3470_ = lean_ctor_get(v___y_3463_, 4);
v_ref_3471_ = lean_ctor_get(v___y_3463_, 5);
v_currNamespace_3472_ = lean_ctor_get(v___y_3463_, 6);
v_openDecls_3473_ = lean_ctor_get(v___y_3463_, 7);
v_initHeartbeats_3474_ = lean_ctor_get(v___y_3463_, 8);
v_maxHeartbeats_3475_ = lean_ctor_get(v___y_3463_, 9);
v_quotContext_3476_ = lean_ctor_get(v___y_3463_, 10);
v_currMacroScope_3477_ = lean_ctor_get(v___y_3463_, 11);
v_diag_3478_ = lean_ctor_get_uint8(v___y_3463_, sizeof(void*)*14);
v_cancelTk_x3f_3479_ = lean_ctor_get(v___y_3463_, 12);
v_suppressElabErrors_3480_ = lean_ctor_get_uint8(v___y_3463_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3481_ = lean_ctor_get(v___y_3463_, 13);
v_isSharedCheck_3536_ = !lean_is_exclusive(v___y_3463_);
if (v_isSharedCheck_3536_ == 0)
{
v___x_3483_ = v___y_3463_;
v_isShared_3484_ = v_isSharedCheck_3536_;
goto v_resetjp_3482_;
}
else
{
lean_inc(v_inheritedTraceOptions_3481_);
lean_inc(v_cancelTk_x3f_3479_);
lean_inc(v_currMacroScope_3477_);
lean_inc(v_quotContext_3476_);
lean_inc(v_maxHeartbeats_3475_);
lean_inc(v_initHeartbeats_3474_);
lean_inc(v_openDecls_3473_);
lean_inc(v_currNamespace_3472_);
lean_inc(v_ref_3471_);
lean_inc(v_maxRecDepth_3470_);
lean_inc(v_currRecDepth_3469_);
lean_inc(v_options_3468_);
lean_inc(v_fileMap_3467_);
lean_inc(v_fileName_3466_);
lean_dec(v___y_3463_);
v___x_3483_ = lean_box(0);
v_isShared_3484_ = v_isSharedCheck_3536_;
goto v_resetjp_3482_;
}
v_resetjp_3482_:
{
lean_object* v___x_3485_; lean_object* v_traceState_3486_; lean_object* v_traces_3487_; lean_object* v_ref_3488_; lean_object* v___x_3490_; 
v___x_3485_ = lean_st_ref_get(v___y_3464_);
v_traceState_3486_ = lean_ctor_get(v___x_3485_, 4);
lean_inc_ref(v_traceState_3486_);
lean_dec(v___x_3485_);
v_traces_3487_ = lean_ctor_get(v_traceState_3486_, 0);
lean_inc_ref(v_traces_3487_);
lean_dec_ref(v_traceState_3486_);
v_ref_3488_ = l_Lean_replaceRef(v_ref_3459_, v_ref_3471_);
lean_dec(v_ref_3471_);
if (v_isShared_3484_ == 0)
{
lean_ctor_set(v___x_3483_, 5, v_ref_3488_);
v___x_3490_ = v___x_3483_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v_fileName_3466_);
lean_ctor_set(v_reuseFailAlloc_3535_, 1, v_fileMap_3467_);
lean_ctor_set(v_reuseFailAlloc_3535_, 2, v_options_3468_);
lean_ctor_set(v_reuseFailAlloc_3535_, 3, v_currRecDepth_3469_);
lean_ctor_set(v_reuseFailAlloc_3535_, 4, v_maxRecDepth_3470_);
lean_ctor_set(v_reuseFailAlloc_3535_, 5, v_ref_3488_);
lean_ctor_set(v_reuseFailAlloc_3535_, 6, v_currNamespace_3472_);
lean_ctor_set(v_reuseFailAlloc_3535_, 7, v_openDecls_3473_);
lean_ctor_set(v_reuseFailAlloc_3535_, 8, v_initHeartbeats_3474_);
lean_ctor_set(v_reuseFailAlloc_3535_, 9, v_maxHeartbeats_3475_);
lean_ctor_set(v_reuseFailAlloc_3535_, 10, v_quotContext_3476_);
lean_ctor_set(v_reuseFailAlloc_3535_, 11, v_currMacroScope_3477_);
lean_ctor_set(v_reuseFailAlloc_3535_, 12, v_cancelTk_x3f_3479_);
lean_ctor_set(v_reuseFailAlloc_3535_, 13, v_inheritedTraceOptions_3481_);
lean_ctor_set_uint8(v_reuseFailAlloc_3535_, sizeof(void*)*14, v_diag_3478_);
lean_ctor_set_uint8(v_reuseFailAlloc_3535_, sizeof(void*)*14 + 1, v_suppressElabErrors_3480_);
v___x_3490_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
lean_object* v___x_3491_; size_t v_sz_3492_; size_t v___x_3493_; lean_object* v___x_3494_; lean_object* v_msg_3495_; lean_object* v___x_3496_; lean_object* v_a_3497_; lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3534_; 
v___x_3491_ = l_Lean_PersistentArray_toArray___redArg(v_traces_3487_);
lean_dec_ref(v_traces_3487_);
v_sz_3492_ = lean_array_size(v___x_3491_);
v___x_3493_ = ((size_t)0ULL);
v___x_3494_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__4_spec__5(v_sz_3492_, v___x_3493_, v___x_3491_);
v_msg_3495_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_3495_, 0, v_data_3458_);
lean_ctor_set(v_msg_3495_, 1, v_msg_3460_);
lean_ctor_set(v_msg_3495_, 2, v___x_3494_);
v___x_3496_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1_spec__1(v_msg_3495_, v___y_3461_, v___y_3462_, v___x_3490_, v___y_3464_);
lean_dec_ref(v___x_3490_);
v_a_3497_ = lean_ctor_get(v___x_3496_, 0);
v_isSharedCheck_3534_ = !lean_is_exclusive(v___x_3496_);
if (v_isSharedCheck_3534_ == 0)
{
v___x_3499_ = v___x_3496_;
v_isShared_3500_ = v_isSharedCheck_3534_;
goto v_resetjp_3498_;
}
else
{
lean_inc(v_a_3497_);
lean_dec(v___x_3496_);
v___x_3499_ = lean_box(0);
v_isShared_3500_ = v_isSharedCheck_3534_;
goto v_resetjp_3498_;
}
v_resetjp_3498_:
{
lean_object* v___x_3501_; lean_object* v_traceState_3502_; lean_object* v_env_3503_; lean_object* v_nextMacroScope_3504_; lean_object* v_ngen_3505_; lean_object* v_auxDeclNGen_3506_; lean_object* v_cache_3507_; lean_object* v_messages_3508_; lean_object* v_infoState_3509_; lean_object* v_snapshotTasks_3510_; lean_object* v___x_3512_; uint8_t v_isShared_3513_; uint8_t v_isSharedCheck_3533_; 
v___x_3501_ = lean_st_ref_take(v___y_3464_);
v_traceState_3502_ = lean_ctor_get(v___x_3501_, 4);
v_env_3503_ = lean_ctor_get(v___x_3501_, 0);
v_nextMacroScope_3504_ = lean_ctor_get(v___x_3501_, 1);
v_ngen_3505_ = lean_ctor_get(v___x_3501_, 2);
v_auxDeclNGen_3506_ = lean_ctor_get(v___x_3501_, 3);
v_cache_3507_ = lean_ctor_get(v___x_3501_, 5);
v_messages_3508_ = lean_ctor_get(v___x_3501_, 6);
v_infoState_3509_ = lean_ctor_get(v___x_3501_, 7);
v_snapshotTasks_3510_ = lean_ctor_get(v___x_3501_, 8);
v_isSharedCheck_3533_ = !lean_is_exclusive(v___x_3501_);
if (v_isSharedCheck_3533_ == 0)
{
v___x_3512_ = v___x_3501_;
v_isShared_3513_ = v_isSharedCheck_3533_;
goto v_resetjp_3511_;
}
else
{
lean_inc(v_snapshotTasks_3510_);
lean_inc(v_infoState_3509_);
lean_inc(v_messages_3508_);
lean_inc(v_cache_3507_);
lean_inc(v_traceState_3502_);
lean_inc(v_auxDeclNGen_3506_);
lean_inc(v_ngen_3505_);
lean_inc(v_nextMacroScope_3504_);
lean_inc(v_env_3503_);
lean_dec(v___x_3501_);
v___x_3512_ = lean_box(0);
v_isShared_3513_ = v_isSharedCheck_3533_;
goto v_resetjp_3511_;
}
v_resetjp_3511_:
{
uint64_t v_tid_3514_; lean_object* v___x_3516_; uint8_t v_isShared_3517_; uint8_t v_isSharedCheck_3531_; 
v_tid_3514_ = lean_ctor_get_uint64(v_traceState_3502_, sizeof(void*)*1);
v_isSharedCheck_3531_ = !lean_is_exclusive(v_traceState_3502_);
if (v_isSharedCheck_3531_ == 0)
{
lean_object* v_unused_3532_; 
v_unused_3532_ = lean_ctor_get(v_traceState_3502_, 0);
lean_dec(v_unused_3532_);
v___x_3516_ = v_traceState_3502_;
v_isShared_3517_ = v_isSharedCheck_3531_;
goto v_resetjp_3515_;
}
else
{
lean_dec(v_traceState_3502_);
v___x_3516_ = lean_box(0);
v_isShared_3517_ = v_isSharedCheck_3531_;
goto v_resetjp_3515_;
}
v_resetjp_3515_:
{
lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3521_; 
v___x_3518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3518_, 0, v_ref_3459_);
lean_ctor_set(v___x_3518_, 1, v_a_3497_);
v___x_3519_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_3457_, v___x_3518_);
if (v_isShared_3517_ == 0)
{
lean_ctor_set(v___x_3516_, 0, v___x_3519_);
v___x_3521_ = v___x_3516_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3530_; 
v_reuseFailAlloc_3530_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3530_, 0, v___x_3519_);
lean_ctor_set_uint64(v_reuseFailAlloc_3530_, sizeof(void*)*1, v_tid_3514_);
v___x_3521_ = v_reuseFailAlloc_3530_;
goto v_reusejp_3520_;
}
v_reusejp_3520_:
{
lean_object* v___x_3523_; 
if (v_isShared_3513_ == 0)
{
lean_ctor_set(v___x_3512_, 4, v___x_3521_);
v___x_3523_ = v___x_3512_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v_env_3503_);
lean_ctor_set(v_reuseFailAlloc_3529_, 1, v_nextMacroScope_3504_);
lean_ctor_set(v_reuseFailAlloc_3529_, 2, v_ngen_3505_);
lean_ctor_set(v_reuseFailAlloc_3529_, 3, v_auxDeclNGen_3506_);
lean_ctor_set(v_reuseFailAlloc_3529_, 4, v___x_3521_);
lean_ctor_set(v_reuseFailAlloc_3529_, 5, v_cache_3507_);
lean_ctor_set(v_reuseFailAlloc_3529_, 6, v_messages_3508_);
lean_ctor_set(v_reuseFailAlloc_3529_, 7, v_infoState_3509_);
lean_ctor_set(v_reuseFailAlloc_3529_, 8, v_snapshotTasks_3510_);
v___x_3523_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3527_; 
v___x_3524_ = lean_st_ref_set(v___y_3464_, v___x_3523_);
v___x_3525_ = lean_box(0);
if (v_isShared_3500_ == 0)
{
lean_ctor_set(v___x_3499_, 0, v___x_3525_);
v___x_3527_ = v___x_3499_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v___x_3525_);
v___x_3527_ = v_reuseFailAlloc_3528_;
goto v_reusejp_3526_;
}
v_reusejp_3526_:
{
return v___x_3527_;
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__2_spec__2___boxed(lean_object* v_oldTraces_3537_, lean_object* v_data_3538_, lean_object* v_ref_3539_, lean_object* v_msg_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_){
_start:
{
lean_object* v_res_3546_; 
v_res_3546_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__2_spec__2(v_oldTraces_3537_, v_data_3538_, v_ref_3539_, v_msg_3540_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_);
lean_dec(v___y_3544_);
lean_dec(v___y_3542_);
lean_dec_ref(v___y_3541_);
return v_res_3546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__2(lean_object* v_cls_3547_, uint8_t v_collapsed_3548_, lean_object* v_tag_3549_, lean_object* v_opts_3550_, uint8_t v_clsEnabled_3551_, lean_object* v_oldTraces_3552_, lean_object* v_msg_3553_, lean_object* v_resStartStop_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_){
_start:
{
lean_object* v_fst_3560_; lean_object* v_snd_3561_; lean_object* v___x_3563_; uint8_t v_isShared_3564_; uint8_t v_isSharedCheck_3659_; 
v_fst_3560_ = lean_ctor_get(v_resStartStop_3554_, 0);
v_snd_3561_ = lean_ctor_get(v_resStartStop_3554_, 1);
v_isSharedCheck_3659_ = !lean_is_exclusive(v_resStartStop_3554_);
if (v_isSharedCheck_3659_ == 0)
{
v___x_3563_ = v_resStartStop_3554_;
v_isShared_3564_ = v_isSharedCheck_3659_;
goto v_resetjp_3562_;
}
else
{
lean_inc(v_snd_3561_);
lean_inc(v_fst_3560_);
lean_dec(v_resStartStop_3554_);
v___x_3563_ = lean_box(0);
v_isShared_3564_ = v_isSharedCheck_3659_;
goto v_resetjp_3562_;
}
v_resetjp_3562_:
{
lean_object* v___y_3566_; lean_object* v___y_3567_; lean_object* v_data_3568_; lean_object* v_fst_3579_; lean_object* v_snd_3580_; lean_object* v___x_3582_; uint8_t v_isShared_3583_; uint8_t v_isSharedCheck_3658_; 
v_fst_3579_ = lean_ctor_get(v_snd_3561_, 0);
v_snd_3580_ = lean_ctor_get(v_snd_3561_, 1);
v_isSharedCheck_3658_ = !lean_is_exclusive(v_snd_3561_);
if (v_isSharedCheck_3658_ == 0)
{
v___x_3582_ = v_snd_3561_;
v_isShared_3583_ = v_isSharedCheck_3658_;
goto v_resetjp_3581_;
}
else
{
lean_inc(v_snd_3580_);
lean_inc(v_fst_3579_);
lean_dec(v_snd_3561_);
v___x_3582_ = lean_box(0);
v_isShared_3583_ = v_isSharedCheck_3658_;
goto v_resetjp_3581_;
}
v___jp_3565_:
{
lean_object* v___x_3569_; 
v___x_3569_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__2_spec__2(v_oldTraces_3552_, v_data_3568_, v___y_3566_, v___y_3567_, v___y_3555_, v___y_3556_, v___y_3557_, v___y_3558_);
lean_dec(v___y_3558_);
lean_dec(v___y_3556_);
lean_dec_ref(v___y_3555_);
if (lean_obj_tag(v___x_3569_) == 0)
{
lean_object* v___x_3570_; 
lean_dec_ref(v___x_3569_);
v___x_3570_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__2_spec__3___redArg(v_fst_3560_);
return v___x_3570_;
}
else
{
lean_object* v_a_3571_; lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3578_; 
lean_dec(v_fst_3560_);
v_a_3571_ = lean_ctor_get(v___x_3569_, 0);
v_isSharedCheck_3578_ = !lean_is_exclusive(v___x_3569_);
if (v_isSharedCheck_3578_ == 0)
{
v___x_3573_ = v___x_3569_;
v_isShared_3574_ = v_isSharedCheck_3578_;
goto v_resetjp_3572_;
}
else
{
lean_inc(v_a_3571_);
lean_dec(v___x_3569_);
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
v_resetjp_3581_:
{
lean_object* v___x_3584_; uint8_t v___x_3585_; lean_object* v___y_3587_; lean_object* v_a_3588_; uint8_t v___y_3612_; double v___y_3643_; 
v___x_3584_ = l_Lean_trace_profiler;
v___x_3585_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2(v_opts_3550_, v___x_3584_);
if (v___x_3585_ == 0)
{
v___y_3612_ = v___x_3585_;
goto v___jp_3611_;
}
else
{
lean_object* v___x_3648_; uint8_t v___x_3649_; 
v___x_3648_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3649_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2(v_opts_3550_, v___x_3648_);
if (v___x_3649_ == 0)
{
lean_object* v___x_3650_; lean_object* v___x_3651_; double v___x_3652_; double v___x_3653_; double v___x_3654_; 
v___x_3650_ = l_Lean_trace_profiler_threshold;
v___x_3651_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__6(v_opts_3550_, v___x_3650_);
v___x_3652_ = lean_float_of_nat(v___x_3651_);
v___x_3653_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__4);
v___x_3654_ = lean_float_div(v___x_3652_, v___x_3653_);
v___y_3643_ = v___x_3654_;
goto v___jp_3642_;
}
else
{
lean_object* v___x_3655_; lean_object* v___x_3656_; double v___x_3657_; 
v___x_3655_ = l_Lean_trace_profiler_threshold;
v___x_3656_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__6(v_opts_3550_, v___x_3655_);
v___x_3657_ = lean_float_of_nat(v___x_3656_);
v___y_3643_ = v___x_3657_;
goto v___jp_3642_;
}
}
v___jp_3586_:
{
uint8_t v_result_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3594_; 
v_result_3589_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__3(v_fst_3560_);
v___x_3590_ = l_Lean_TraceResult_toEmoji(v_result_3589_);
v___x_3591_ = l_Lean_stringToMessageData(v___x_3590_);
v___x_3592_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__1);
if (v_isShared_3583_ == 0)
{
lean_ctor_set_tag(v___x_3582_, 7);
lean_ctor_set(v___x_3582_, 1, v___x_3592_);
lean_ctor_set(v___x_3582_, 0, v___x_3591_);
v___x_3594_ = v___x_3582_;
goto v_reusejp_3593_;
}
else
{
lean_object* v_reuseFailAlloc_3605_; 
v_reuseFailAlloc_3605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3605_, 0, v___x_3591_);
lean_ctor_set(v_reuseFailAlloc_3605_, 1, v___x_3592_);
v___x_3594_ = v_reuseFailAlloc_3605_;
goto v_reusejp_3593_;
}
v_reusejp_3593_:
{
lean_object* v_m_3596_; 
if (v_isShared_3564_ == 0)
{
lean_ctor_set_tag(v___x_3563_, 7);
lean_ctor_set(v___x_3563_, 1, v_a_3588_);
lean_ctor_set(v___x_3563_, 0, v___x_3594_);
v_m_3596_ = v___x_3563_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3604_; 
v_reuseFailAlloc_3604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3604_, 0, v___x_3594_);
lean_ctor_set(v_reuseFailAlloc_3604_, 1, v_a_3588_);
v_m_3596_ = v_reuseFailAlloc_3604_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
lean_object* v___x_3597_; lean_object* v___x_3598_; double v___x_3599_; lean_object* v_data_3600_; 
v___x_3597_ = lean_box(v_result_3589_);
v___x_3598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3598_, 0, v___x_3597_);
v___x_3599_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__0);
lean_inc_ref(v_tag_3549_);
lean_inc_ref(v___x_3598_);
lean_inc(v_cls_3547_);
v_data_3600_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3600_, 0, v_cls_3547_);
lean_ctor_set(v_data_3600_, 1, v___x_3598_);
lean_ctor_set(v_data_3600_, 2, v_tag_3549_);
lean_ctor_set_float(v_data_3600_, sizeof(void*)*3, v___x_3599_);
lean_ctor_set_float(v_data_3600_, sizeof(void*)*3 + 8, v___x_3599_);
lean_ctor_set_uint8(v_data_3600_, sizeof(void*)*3 + 16, v_collapsed_3548_);
if (v___x_3585_ == 0)
{
lean_dec_ref(v___x_3598_);
lean_dec(v_snd_3580_);
lean_dec(v_fst_3579_);
lean_dec_ref(v_tag_3549_);
lean_dec(v_cls_3547_);
v___y_3566_ = v___y_3587_;
v___y_3567_ = v_m_3596_;
v_data_3568_ = v_data_3600_;
goto v___jp_3565_;
}
else
{
lean_object* v_data_3601_; double v___x_3602_; double v___x_3603_; 
lean_dec_ref(v_data_3600_);
v_data_3601_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3601_, 0, v_cls_3547_);
lean_ctor_set(v_data_3601_, 1, v___x_3598_);
lean_ctor_set(v_data_3601_, 2, v_tag_3549_);
v___x_3602_ = lean_unbox_float(v_fst_3579_);
lean_dec(v_fst_3579_);
lean_ctor_set_float(v_data_3601_, sizeof(void*)*3, v___x_3602_);
v___x_3603_ = lean_unbox_float(v_snd_3580_);
lean_dec(v_snd_3580_);
lean_ctor_set_float(v_data_3601_, sizeof(void*)*3 + 8, v___x_3603_);
lean_ctor_set_uint8(v_data_3601_, sizeof(void*)*3 + 16, v_collapsed_3548_);
v___y_3566_ = v___y_3587_;
v___y_3567_ = v_m_3596_;
v_data_3568_ = v_data_3601_;
goto v___jp_3565_;
}
}
}
}
v___jp_3606_:
{
lean_object* v_ref_3607_; lean_object* v___x_3608_; 
v_ref_3607_ = lean_ctor_get(v___y_3557_, 5);
lean_inc(v___y_3558_);
lean_inc_ref(v___y_3557_);
lean_inc(v___y_3556_);
lean_inc_ref(v___y_3555_);
lean_inc(v_fst_3560_);
v___x_3608_ = lean_apply_6(v_msg_3553_, v_fst_3560_, v___y_3555_, v___y_3556_, v___y_3557_, v___y_3558_, lean_box(0));
if (lean_obj_tag(v___x_3608_) == 0)
{
lean_object* v_a_3609_; 
v_a_3609_ = lean_ctor_get(v___x_3608_, 0);
lean_inc(v_a_3609_);
lean_dec_ref(v___x_3608_);
lean_inc(v_ref_3607_);
v___y_3587_ = v_ref_3607_;
v_a_3588_ = v_a_3609_;
goto v___jp_3586_;
}
else
{
lean_object* v___x_3610_; 
lean_dec_ref(v___x_3608_);
v___x_3610_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__3);
lean_inc(v_ref_3607_);
v___y_3587_ = v_ref_3607_;
v_a_3588_ = v___x_3610_;
goto v___jp_3586_;
}
}
v___jp_3611_:
{
if (v_clsEnabled_3551_ == 0)
{
if (v___y_3612_ == 0)
{
lean_object* v___x_3613_; lean_object* v_traceState_3614_; lean_object* v_env_3615_; lean_object* v_nextMacroScope_3616_; lean_object* v_ngen_3617_; lean_object* v_auxDeclNGen_3618_; lean_object* v_cache_3619_; lean_object* v_messages_3620_; lean_object* v_infoState_3621_; lean_object* v_snapshotTasks_3622_; lean_object* v___x_3624_; uint8_t v_isShared_3625_; uint8_t v_isSharedCheck_3641_; 
lean_del_object(v___x_3582_);
lean_dec(v_snd_3580_);
lean_dec(v_fst_3579_);
lean_del_object(v___x_3563_);
lean_dec_ref(v___y_3557_);
lean_dec(v___y_3556_);
lean_dec_ref(v___y_3555_);
lean_dec_ref(v_msg_3553_);
lean_dec_ref(v_tag_3549_);
lean_dec(v_cls_3547_);
v___x_3613_ = lean_st_ref_take(v___y_3558_);
v_traceState_3614_ = lean_ctor_get(v___x_3613_, 4);
v_env_3615_ = lean_ctor_get(v___x_3613_, 0);
v_nextMacroScope_3616_ = lean_ctor_get(v___x_3613_, 1);
v_ngen_3617_ = lean_ctor_get(v___x_3613_, 2);
v_auxDeclNGen_3618_ = lean_ctor_get(v___x_3613_, 3);
v_cache_3619_ = lean_ctor_get(v___x_3613_, 5);
v_messages_3620_ = lean_ctor_get(v___x_3613_, 6);
v_infoState_3621_ = lean_ctor_get(v___x_3613_, 7);
v_snapshotTasks_3622_ = lean_ctor_get(v___x_3613_, 8);
v_isSharedCheck_3641_ = !lean_is_exclusive(v___x_3613_);
if (v_isSharedCheck_3641_ == 0)
{
v___x_3624_ = v___x_3613_;
v_isShared_3625_ = v_isSharedCheck_3641_;
goto v_resetjp_3623_;
}
else
{
lean_inc(v_snapshotTasks_3622_);
lean_inc(v_infoState_3621_);
lean_inc(v_messages_3620_);
lean_inc(v_cache_3619_);
lean_inc(v_traceState_3614_);
lean_inc(v_auxDeclNGen_3618_);
lean_inc(v_ngen_3617_);
lean_inc(v_nextMacroScope_3616_);
lean_inc(v_env_3615_);
lean_dec(v___x_3613_);
v___x_3624_ = lean_box(0);
v_isShared_3625_ = v_isSharedCheck_3641_;
goto v_resetjp_3623_;
}
v_resetjp_3623_:
{
uint64_t v_tid_3626_; lean_object* v_traces_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3640_; 
v_tid_3626_ = lean_ctor_get_uint64(v_traceState_3614_, sizeof(void*)*1);
v_traces_3627_ = lean_ctor_get(v_traceState_3614_, 0);
v_isSharedCheck_3640_ = !lean_is_exclusive(v_traceState_3614_);
if (v_isSharedCheck_3640_ == 0)
{
v___x_3629_ = v_traceState_3614_;
v_isShared_3630_ = v_isSharedCheck_3640_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_traces_3627_);
lean_dec(v_traceState_3614_);
v___x_3629_ = lean_box(0);
v_isShared_3630_ = v_isSharedCheck_3640_;
goto v_resetjp_3628_;
}
v_resetjp_3628_:
{
lean_object* v___x_3631_; lean_object* v___x_3633_; 
v___x_3631_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3552_, v_traces_3627_);
lean_dec_ref(v_traces_3627_);
if (v_isShared_3630_ == 0)
{
lean_ctor_set(v___x_3629_, 0, v___x_3631_);
v___x_3633_ = v___x_3629_;
goto v_reusejp_3632_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v___x_3631_);
lean_ctor_set_uint64(v_reuseFailAlloc_3639_, sizeof(void*)*1, v_tid_3626_);
v___x_3633_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3632_;
}
v_reusejp_3632_:
{
lean_object* v___x_3635_; 
if (v_isShared_3625_ == 0)
{
lean_ctor_set(v___x_3624_, 4, v___x_3633_);
v___x_3635_ = v___x_3624_;
goto v_reusejp_3634_;
}
else
{
lean_object* v_reuseFailAlloc_3638_; 
v_reuseFailAlloc_3638_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3638_, 0, v_env_3615_);
lean_ctor_set(v_reuseFailAlloc_3638_, 1, v_nextMacroScope_3616_);
lean_ctor_set(v_reuseFailAlloc_3638_, 2, v_ngen_3617_);
lean_ctor_set(v_reuseFailAlloc_3638_, 3, v_auxDeclNGen_3618_);
lean_ctor_set(v_reuseFailAlloc_3638_, 4, v___x_3633_);
lean_ctor_set(v_reuseFailAlloc_3638_, 5, v_cache_3619_);
lean_ctor_set(v_reuseFailAlloc_3638_, 6, v_messages_3620_);
lean_ctor_set(v_reuseFailAlloc_3638_, 7, v_infoState_3621_);
lean_ctor_set(v_reuseFailAlloc_3638_, 8, v_snapshotTasks_3622_);
v___x_3635_ = v_reuseFailAlloc_3638_;
goto v_reusejp_3634_;
}
v_reusejp_3634_:
{
lean_object* v___x_3636_; lean_object* v___x_3637_; 
v___x_3636_ = lean_st_ref_set(v___y_3558_, v___x_3635_);
lean_dec(v___y_3558_);
v___x_3637_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__2_spec__3___redArg(v_fst_3560_);
return v___x_3637_;
}
}
}
}
}
else
{
goto v___jp_3606_;
}
}
else
{
goto v___jp_3606_;
}
}
v___jp_3642_:
{
double v___x_3644_; double v___x_3645_; double v___x_3646_; uint8_t v___x_3647_; 
v___x_3644_ = lean_unbox_float(v_snd_3580_);
v___x_3645_ = lean_unbox_float(v_fst_3579_);
v___x_3646_ = lean_float_sub(v___x_3644_, v___x_3645_);
v___x_3647_ = lean_float_decLt(v___y_3643_, v___x_3646_);
v___y_3612_ = v___x_3647_;
goto v___jp_3611_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__2___boxed(lean_object* v_cls_3660_, lean_object* v_collapsed_3661_, lean_object* v_tag_3662_, lean_object* v_opts_3663_, lean_object* v_clsEnabled_3664_, lean_object* v_oldTraces_3665_, lean_object* v_msg_3666_, lean_object* v_resStartStop_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_){
_start:
{
uint8_t v_collapsed_boxed_3673_; uint8_t v_clsEnabled_boxed_3674_; lean_object* v_res_3675_; 
v_collapsed_boxed_3673_ = lean_unbox(v_collapsed_3661_);
v_clsEnabled_boxed_3674_ = lean_unbox(v_clsEnabled_3664_);
v_res_3675_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__2(v_cls_3660_, v_collapsed_boxed_3673_, v_tag_3662_, v_opts_3663_, v_clsEnabled_boxed_3674_, v_oldTraces_3665_, v_msg_3666_, v_resStartStop_3667_, v___y_3668_, v___y_3669_, v___y_3670_, v___y_3671_);
lean_dec_ref(v_opts_3663_);
return v_res_3675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry(lean_object* v_e_3680_, lean_object* v_a_3681_, lean_object* v_a_3682_, lean_object* v_a_3683_, lean_object* v_a_3684_){
_start:
{
lean_object* v_options_3686_; uint8_t v_hasTrace_3687_; 
v_options_3686_ = lean_ctor_get(v_a_3683_, 2);
v_hasTrace_3687_ = lean_ctor_get_uint8(v_options_3686_, sizeof(void*)*1);
if (v_hasTrace_3687_ == 0)
{
lean_object* v___x_3688_; 
v___x_3688_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_3684_);
if (lean_obj_tag(v___x_3688_) == 0)
{
lean_object* v_a_3689_; lean_object* v___x_3690_; 
v_a_3689_ = lean_ctor_get(v___x_3688_, 0);
lean_inc(v_a_3689_);
lean_dec_ref(v___x_3688_);
lean_inc(v_a_3684_);
lean_inc_ref(v_a_3683_);
lean_inc(v_a_3682_);
lean_inc_ref(v_a_3681_);
v___x_3690_ = l_Lean_Meta_Sym_unfoldReducible(v_e_3680_, v_a_3681_, v_a_3682_, v_a_3683_, v_a_3684_);
if (lean_obj_tag(v___x_3690_) == 0)
{
lean_object* v_a_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___f_3697_; lean_object* v___x_3698_; 
v_a_3691_ = lean_ctor_get(v___x_3690_, 0);
lean_inc(v_a_3691_);
lean_dec_ref(v___x_3690_);
v___x_3692_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_3693_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__6(v_options_3686_, v___x_3692_);
v___x_3694_ = lean_unsigned_to_nat(2u);
v___x_3695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3695_, 0, v___x_3693_);
lean_ctor_set(v___x_3695_, 1, v___x_3694_);
v___x_3696_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(v_a_3689_);
v___f_3697_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3697_, 0, v_a_3691_);
lean_closure_set(v___f_3697_, 1, v___x_3696_);
lean_closure_set(v___f_3697_, 2, v___x_3695_);
v___x_3698_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_3697_, v_a_3681_, v_a_3682_, v_a_3683_, v_a_3684_);
return v___x_3698_;
}
else
{
lean_object* v_a_3699_; lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3706_; 
lean_dec(v_a_3689_);
lean_dec(v_a_3684_);
lean_dec_ref(v_a_3683_);
lean_dec(v_a_3682_);
lean_dec_ref(v_a_3681_);
v_a_3699_ = lean_ctor_get(v___x_3690_, 0);
v_isSharedCheck_3706_ = !lean_is_exclusive(v___x_3690_);
if (v_isSharedCheck_3706_ == 0)
{
v___x_3701_ = v___x_3690_;
v_isShared_3702_ = v_isSharedCheck_3706_;
goto v_resetjp_3700_;
}
else
{
lean_inc(v_a_3699_);
lean_dec(v___x_3690_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3706_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
lean_object* v___x_3704_; 
if (v_isShared_3702_ == 0)
{
v___x_3704_ = v___x_3701_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v_a_3699_);
v___x_3704_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
return v___x_3704_;
}
}
}
}
else
{
lean_object* v_a_3707_; lean_object* v___x_3709_; uint8_t v_isShared_3710_; uint8_t v_isSharedCheck_3714_; 
lean_dec(v_a_3684_);
lean_dec_ref(v_a_3683_);
lean_dec(v_a_3682_);
lean_dec_ref(v_a_3681_);
lean_dec_ref(v_e_3680_);
v_a_3707_ = lean_ctor_get(v___x_3688_, 0);
v_isSharedCheck_3714_ = !lean_is_exclusive(v___x_3688_);
if (v_isSharedCheck_3714_ == 0)
{
v___x_3709_ = v___x_3688_;
v_isShared_3710_ = v_isSharedCheck_3714_;
goto v_resetjp_3708_;
}
else
{
lean_inc(v_a_3707_);
lean_dec(v___x_3688_);
v___x_3709_ = lean_box(0);
v_isShared_3710_ = v_isSharedCheck_3714_;
goto v_resetjp_3708_;
}
v_resetjp_3708_:
{
lean_object* v___x_3712_; 
if (v_isShared_3710_ == 0)
{
v___x_3712_ = v___x_3709_;
goto v_reusejp_3711_;
}
else
{
lean_object* v_reuseFailAlloc_3713_; 
v_reuseFailAlloc_3713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3713_, 0, v_a_3707_);
v___x_3712_ = v_reuseFailAlloc_3713_;
goto v_reusejp_3711_;
}
v_reusejp_3711_:
{
return v___x_3712_;
}
}
}
}
else
{
lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v_a_3717_; lean_object* v___x_3719_; uint8_t v_isShared_3720_; uint8_t v_isSharedCheck_3845_; 
v___x_3715_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0));
v___x_3716_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg(v___x_3715_, v_a_3683_);
v_a_3717_ = lean_ctor_get(v___x_3716_, 0);
v_isSharedCheck_3845_ = !lean_is_exclusive(v___x_3716_);
if (v_isSharedCheck_3845_ == 0)
{
v___x_3719_ = v___x_3716_;
v_isShared_3720_ = v_isSharedCheck_3845_;
goto v_resetjp_3718_;
}
else
{
lean_inc(v_a_3717_);
lean_dec(v___x_3716_);
v___x_3719_ = lean_box(0);
v_isShared_3720_ = v_isSharedCheck_3845_;
goto v_resetjp_3718_;
}
v_resetjp_3718_:
{
lean_object* v___f_3721_; lean_object* v___x_3722_; lean_object* v___y_3724_; lean_object* v___y_3725_; lean_object* v_a_3726_; lean_object* v___y_3740_; lean_object* v___y_3741_; lean_object* v_a_3742_; lean_object* v___y_3747_; lean_object* v___y_3748_; lean_object* v_a_3749_; lean_object* v___y_3760_; lean_object* v___y_3761_; lean_object* v_a_3762_; uint8_t v___x_3815_; 
lean_inc_ref(v_e_3680_);
v___f_3721_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___boxed), 7, 1);
lean_closure_set(v___f_3721_, 0, v_e_3680_);
v___x_3722_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__1));
v___x_3815_ = lean_unbox(v_a_3717_);
if (v___x_3815_ == 0)
{
lean_object* v___x_3816_; uint8_t v___x_3817_; 
v___x_3816_ = l_Lean_trace_profiler;
v___x_3817_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2(v_options_3686_, v___x_3816_);
if (v___x_3817_ == 0)
{
lean_object* v___x_3818_; 
lean_dec_ref(v___f_3721_);
lean_del_object(v___x_3719_);
lean_dec(v_a_3717_);
v___x_3818_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_3684_);
if (lean_obj_tag(v___x_3818_) == 0)
{
lean_object* v_a_3819_; lean_object* v___x_3820_; 
v_a_3819_ = lean_ctor_get(v___x_3818_, 0);
lean_inc(v_a_3819_);
lean_dec_ref(v___x_3818_);
lean_inc(v_a_3684_);
lean_inc_ref(v_a_3683_);
lean_inc(v_a_3682_);
lean_inc_ref(v_a_3681_);
v___x_3820_ = l_Lean_Meta_Sym_unfoldReducible(v_e_3680_, v_a_3681_, v_a_3682_, v_a_3683_, v_a_3684_);
if (lean_obj_tag(v___x_3820_) == 0)
{
lean_object* v_a_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___f_3827_; lean_object* v___x_3828_; 
v_a_3821_ = lean_ctor_get(v___x_3820_, 0);
lean_inc(v_a_3821_);
lean_dec_ref(v___x_3820_);
v___x_3822_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_3823_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__6(v_options_3686_, v___x_3822_);
v___x_3824_ = lean_unsigned_to_nat(2u);
v___x_3825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3825_, 0, v___x_3823_);
lean_ctor_set(v___x_3825_, 1, v___x_3824_);
v___x_3826_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(v_a_3819_);
v___f_3827_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3827_, 0, v_a_3821_);
lean_closure_set(v___f_3827_, 1, v___x_3826_);
lean_closure_set(v___f_3827_, 2, v___x_3825_);
v___x_3828_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_3827_, v_a_3681_, v_a_3682_, v_a_3683_, v_a_3684_);
return v___x_3828_;
}
else
{
lean_object* v_a_3829_; lean_object* v___x_3831_; uint8_t v_isShared_3832_; uint8_t v_isSharedCheck_3836_; 
lean_dec(v_a_3819_);
lean_dec(v_a_3684_);
lean_dec_ref(v_a_3683_);
lean_dec(v_a_3682_);
lean_dec_ref(v_a_3681_);
v_a_3829_ = lean_ctor_get(v___x_3820_, 0);
v_isSharedCheck_3836_ = !lean_is_exclusive(v___x_3820_);
if (v_isSharedCheck_3836_ == 0)
{
v___x_3831_ = v___x_3820_;
v_isShared_3832_ = v_isSharedCheck_3836_;
goto v_resetjp_3830_;
}
else
{
lean_inc(v_a_3829_);
lean_dec(v___x_3820_);
v___x_3831_ = lean_box(0);
v_isShared_3832_ = v_isSharedCheck_3836_;
goto v_resetjp_3830_;
}
v_resetjp_3830_:
{
lean_object* v___x_3834_; 
if (v_isShared_3832_ == 0)
{
v___x_3834_ = v___x_3831_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v_a_3829_);
v___x_3834_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
return v___x_3834_;
}
}
}
}
else
{
lean_object* v_a_3837_; lean_object* v___x_3839_; uint8_t v_isShared_3840_; uint8_t v_isSharedCheck_3844_; 
lean_dec(v_a_3684_);
lean_dec_ref(v_a_3683_);
lean_dec(v_a_3682_);
lean_dec_ref(v_a_3681_);
lean_dec_ref(v_e_3680_);
v_a_3837_ = lean_ctor_get(v___x_3818_, 0);
v_isSharedCheck_3844_ = !lean_is_exclusive(v___x_3818_);
if (v_isSharedCheck_3844_ == 0)
{
v___x_3839_ = v___x_3818_;
v_isShared_3840_ = v_isSharedCheck_3844_;
goto v_resetjp_3838_;
}
else
{
lean_inc(v_a_3837_);
lean_dec(v___x_3818_);
v___x_3839_ = lean_box(0);
v_isShared_3840_ = v_isSharedCheck_3844_;
goto v_resetjp_3838_;
}
v_resetjp_3838_:
{
lean_object* v___x_3842_; 
if (v_isShared_3840_ == 0)
{
v___x_3842_ = v___x_3839_;
goto v_reusejp_3841_;
}
else
{
lean_object* v_reuseFailAlloc_3843_; 
v_reuseFailAlloc_3843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3843_, 0, v_a_3837_);
v___x_3842_ = v_reuseFailAlloc_3843_;
goto v_reusejp_3841_;
}
v_reusejp_3841_:
{
return v___x_3842_;
}
}
}
}
else
{
lean_inc_ref(v_options_3686_);
goto v___jp_3764_;
}
}
else
{
lean_inc_ref(v_options_3686_);
goto v___jp_3764_;
}
v___jp_3723_:
{
lean_object* v___x_3727_; double v___x_3728_; double v___x_3729_; double v___x_3730_; double v___x_3731_; double v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; uint8_t v___x_3737_; lean_object* v___x_3738_; 
v___x_3727_ = lean_io_mono_nanos_now();
v___x_3728_ = lean_float_of_nat(v___y_3725_);
v___x_3729_ = lean_float_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4);
v___x_3730_ = lean_float_div(v___x_3728_, v___x_3729_);
v___x_3731_ = lean_float_of_nat(v___x_3727_);
v___x_3732_ = lean_float_div(v___x_3731_, v___x_3729_);
v___x_3733_ = lean_box_float(v___x_3730_);
v___x_3734_ = lean_box_float(v___x_3732_);
v___x_3735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3735_, 0, v___x_3733_);
lean_ctor_set(v___x_3735_, 1, v___x_3734_);
v___x_3736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3736_, 0, v_a_3726_);
lean_ctor_set(v___x_3736_, 1, v___x_3735_);
v___x_3737_ = lean_unbox(v_a_3717_);
lean_dec(v_a_3717_);
v___x_3738_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__2(v___x_3715_, v_hasTrace_3687_, v___x_3722_, v_options_3686_, v___x_3737_, v___y_3724_, v___f_3721_, v___x_3736_, v_a_3681_, v_a_3682_, v_a_3683_, v_a_3684_);
lean_dec_ref(v_options_3686_);
return v___x_3738_;
}
v___jp_3739_:
{
lean_object* v___x_3744_; 
if (v_isShared_3720_ == 0)
{
lean_ctor_set(v___x_3719_, 0, v_a_3742_);
v___x_3744_ = v___x_3719_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v_a_3742_);
v___x_3744_ = v_reuseFailAlloc_3745_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
v___y_3724_ = v___y_3740_;
v___y_3725_ = v___y_3741_;
v_a_3726_ = v___x_3744_;
goto v___jp_3723_;
}
}
v___jp_3746_:
{
lean_object* v___x_3750_; double v___x_3751_; double v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; uint8_t v___x_3757_; lean_object* v___x_3758_; 
v___x_3750_ = lean_io_get_num_heartbeats();
v___x_3751_ = lean_float_of_nat(v___y_3747_);
v___x_3752_ = lean_float_of_nat(v___x_3750_);
v___x_3753_ = lean_box_float(v___x_3751_);
v___x_3754_ = lean_box_float(v___x_3752_);
v___x_3755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3755_, 0, v___x_3753_);
lean_ctor_set(v___x_3755_, 1, v___x_3754_);
v___x_3756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3756_, 0, v_a_3749_);
lean_ctor_set(v___x_3756_, 1, v___x_3755_);
v___x_3757_ = lean_unbox(v_a_3717_);
lean_dec(v_a_3717_);
v___x_3758_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__2(v___x_3715_, v_hasTrace_3687_, v___x_3722_, v_options_3686_, v___x_3757_, v___y_3748_, v___f_3721_, v___x_3756_, v_a_3681_, v_a_3682_, v_a_3683_, v_a_3684_);
lean_dec_ref(v_options_3686_);
return v___x_3758_;
}
v___jp_3759_:
{
lean_object* v___x_3763_; 
v___x_3763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3763_, 0, v_a_3762_);
v___y_3747_ = v___y_3760_;
v___y_3748_ = v___y_3761_;
v_a_3749_ = v___x_3763_;
goto v___jp_3746_;
}
v___jp_3764_:
{
lean_object* v___x_3765_; lean_object* v_a_3766_; lean_object* v___x_3767_; uint8_t v___x_3768_; 
v___x_3765_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1___redArg(v_a_3684_);
v_a_3766_ = lean_ctor_get(v___x_3765_, 0);
lean_inc(v_a_3766_);
lean_dec_ref(v___x_3765_);
v___x_3767_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3768_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2(v_options_3686_, v___x_3767_);
if (v___x_3768_ == 0)
{
lean_object* v___x_3769_; lean_object* v___x_3770_; 
v___x_3769_ = lean_io_mono_nanos_now();
v___x_3770_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_3684_);
if (lean_obj_tag(v___x_3770_) == 0)
{
lean_object* v_a_3771_; lean_object* v___x_3772_; 
v_a_3771_ = lean_ctor_get(v___x_3770_, 0);
lean_inc(v_a_3771_);
lean_dec_ref(v___x_3770_);
lean_inc(v_a_3684_);
lean_inc_ref(v_a_3683_);
lean_inc(v_a_3682_);
lean_inc_ref(v_a_3681_);
v___x_3772_ = l_Lean_Meta_Sym_unfoldReducible(v_e_3680_, v_a_3681_, v_a_3682_, v_a_3683_, v_a_3684_);
if (lean_obj_tag(v___x_3772_) == 0)
{
lean_object* v_a_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___f_3779_; lean_object* v___x_3780_; 
v_a_3773_ = lean_ctor_get(v___x_3772_, 0);
lean_inc(v_a_3773_);
lean_dec_ref(v___x_3772_);
v___x_3774_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_3775_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__6(v_options_3686_, v___x_3774_);
v___x_3776_ = lean_unsigned_to_nat(2u);
v___x_3777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3777_, 0, v___x_3775_);
lean_ctor_set(v___x_3777_, 1, v___x_3776_);
v___x_3778_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(v_a_3771_);
v___f_3779_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3779_, 0, v_a_3773_);
lean_closure_set(v___f_3779_, 1, v___x_3778_);
lean_closure_set(v___f_3779_, 2, v___x_3777_);
lean_inc(v_a_3684_);
lean_inc_ref(v_a_3683_);
lean_inc(v_a_3682_);
lean_inc_ref(v_a_3681_);
v___x_3780_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_3779_, v_a_3681_, v_a_3682_, v_a_3683_, v_a_3684_);
if (lean_obj_tag(v___x_3780_) == 0)
{
lean_object* v_a_3781_; lean_object* v___x_3783_; uint8_t v_isShared_3784_; uint8_t v_isSharedCheck_3788_; 
lean_del_object(v___x_3719_);
v_a_3781_ = lean_ctor_get(v___x_3780_, 0);
v_isSharedCheck_3788_ = !lean_is_exclusive(v___x_3780_);
if (v_isSharedCheck_3788_ == 0)
{
v___x_3783_ = v___x_3780_;
v_isShared_3784_ = v_isSharedCheck_3788_;
goto v_resetjp_3782_;
}
else
{
lean_inc(v_a_3781_);
lean_dec(v___x_3780_);
v___x_3783_ = lean_box(0);
v_isShared_3784_ = v_isSharedCheck_3788_;
goto v_resetjp_3782_;
}
v_resetjp_3782_:
{
lean_object* v___x_3786_; 
if (v_isShared_3784_ == 0)
{
lean_ctor_set_tag(v___x_3783_, 1);
v___x_3786_ = v___x_3783_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3787_; 
v_reuseFailAlloc_3787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3787_, 0, v_a_3781_);
v___x_3786_ = v_reuseFailAlloc_3787_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
v___y_3724_ = v_a_3766_;
v___y_3725_ = v___x_3769_;
v_a_3726_ = v___x_3786_;
goto v___jp_3723_;
}
}
}
else
{
lean_object* v_a_3789_; 
v_a_3789_ = lean_ctor_get(v___x_3780_, 0);
lean_inc(v_a_3789_);
lean_dec_ref(v___x_3780_);
v___y_3740_ = v_a_3766_;
v___y_3741_ = v___x_3769_;
v_a_3742_ = v_a_3789_;
goto v___jp_3739_;
}
}
else
{
lean_object* v_a_3790_; 
lean_dec(v_a_3771_);
v_a_3790_ = lean_ctor_get(v___x_3772_, 0);
lean_inc(v_a_3790_);
lean_dec_ref(v___x_3772_);
v___y_3740_ = v_a_3766_;
v___y_3741_ = v___x_3769_;
v_a_3742_ = v_a_3790_;
goto v___jp_3739_;
}
}
else
{
lean_object* v_a_3791_; 
lean_dec_ref(v_e_3680_);
v_a_3791_ = lean_ctor_get(v___x_3770_, 0);
lean_inc(v_a_3791_);
lean_dec_ref(v___x_3770_);
v___y_3740_ = v_a_3766_;
v___y_3741_ = v___x_3769_;
v_a_3742_ = v_a_3791_;
goto v___jp_3739_;
}
}
else
{
lean_object* v___x_3792_; lean_object* v___x_3793_; 
lean_del_object(v___x_3719_);
v___x_3792_ = lean_io_get_num_heartbeats();
v___x_3793_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_3684_);
if (lean_obj_tag(v___x_3793_) == 0)
{
lean_object* v_a_3794_; lean_object* v___x_3795_; 
v_a_3794_ = lean_ctor_get(v___x_3793_, 0);
lean_inc(v_a_3794_);
lean_dec_ref(v___x_3793_);
lean_inc(v_a_3684_);
lean_inc_ref(v_a_3683_);
lean_inc(v_a_3682_);
lean_inc_ref(v_a_3681_);
v___x_3795_ = l_Lean_Meta_Sym_unfoldReducible(v_e_3680_, v_a_3681_, v_a_3682_, v_a_3683_, v_a_3684_);
if (lean_obj_tag(v___x_3795_) == 0)
{
lean_object* v_a_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___f_3802_; lean_object* v___x_3803_; 
v_a_3796_ = lean_ctor_get(v___x_3795_, 0);
lean_inc(v_a_3796_);
lean_dec_ref(v___x_3795_);
v___x_3797_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_3798_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__6(v_options_3686_, v___x_3797_);
v___x_3799_ = lean_unsigned_to_nat(2u);
v___x_3800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3800_, 0, v___x_3798_);
lean_ctor_set(v___x_3800_, 1, v___x_3799_);
v___x_3801_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(v_a_3794_);
v___f_3802_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3802_, 0, v_a_3796_);
lean_closure_set(v___f_3802_, 1, v___x_3801_);
lean_closure_set(v___f_3802_, 2, v___x_3800_);
lean_inc(v_a_3684_);
lean_inc_ref(v_a_3683_);
lean_inc(v_a_3682_);
lean_inc_ref(v_a_3681_);
v___x_3803_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_3802_, v_a_3681_, v_a_3682_, v_a_3683_, v_a_3684_);
if (lean_obj_tag(v___x_3803_) == 0)
{
lean_object* v_a_3804_; lean_object* v___x_3806_; uint8_t v_isShared_3807_; uint8_t v_isSharedCheck_3811_; 
v_a_3804_ = lean_ctor_get(v___x_3803_, 0);
v_isSharedCheck_3811_ = !lean_is_exclusive(v___x_3803_);
if (v_isSharedCheck_3811_ == 0)
{
v___x_3806_ = v___x_3803_;
v_isShared_3807_ = v_isSharedCheck_3811_;
goto v_resetjp_3805_;
}
else
{
lean_inc(v_a_3804_);
lean_dec(v___x_3803_);
v___x_3806_ = lean_box(0);
v_isShared_3807_ = v_isSharedCheck_3811_;
goto v_resetjp_3805_;
}
v_resetjp_3805_:
{
lean_object* v___x_3809_; 
if (v_isShared_3807_ == 0)
{
lean_ctor_set_tag(v___x_3806_, 1);
v___x_3809_ = v___x_3806_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3810_; 
v_reuseFailAlloc_3810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3810_, 0, v_a_3804_);
v___x_3809_ = v_reuseFailAlloc_3810_;
goto v_reusejp_3808_;
}
v_reusejp_3808_:
{
v___y_3747_ = v___x_3792_;
v___y_3748_ = v_a_3766_;
v_a_3749_ = v___x_3809_;
goto v___jp_3746_;
}
}
}
else
{
lean_object* v_a_3812_; 
v_a_3812_ = lean_ctor_get(v___x_3803_, 0);
lean_inc(v_a_3812_);
lean_dec_ref(v___x_3803_);
v___y_3760_ = v___x_3792_;
v___y_3761_ = v_a_3766_;
v_a_3762_ = v_a_3812_;
goto v___jp_3759_;
}
}
else
{
lean_object* v_a_3813_; 
lean_dec(v_a_3794_);
v_a_3813_ = lean_ctor_get(v___x_3795_, 0);
lean_inc(v_a_3813_);
lean_dec_ref(v___x_3795_);
v___y_3760_ = v___x_3792_;
v___y_3761_ = v_a_3766_;
v_a_3762_ = v_a_3813_;
goto v___jp_3759_;
}
}
else
{
lean_object* v_a_3814_; 
lean_dec_ref(v_e_3680_);
v_a_3814_ = lean_ctor_get(v___x_3793_, 0);
lean_inc(v_a_3814_);
lean_dec_ref(v___x_3793_);
v___y_3760_ = v___x_3792_;
v___y_3761_ = v_a_3766_;
v_a_3762_ = v_a_3814_;
goto v___jp_3759_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___boxed(lean_object* v_e_3846_, lean_object* v_a_3847_, lean_object* v_a_3848_, lean_object* v_a_3849_, lean_object* v_a_3850_, lean_object* v_a_3851_){
_start:
{
lean_object* v_res_3852_; 
v_res_3852_ = l_Lean_Meta_Tactic_Cbv_cbvEntry(v_e_3846_, v_a_3847_, v_a_3848_, v_a_3849_, v_a_3850_);
return v_res_3852_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__2_spec__3(lean_object* v_00_u03b1_3853_, lean_object* v_x_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_){
_start:
{
lean_object* v___x_3860_; 
v___x_3860_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__2_spec__3___redArg(v_x_3854_);
return v___x_3860_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__2_spec__3___boxed(lean_object* v_00_u03b1_3861_, lean_object* v_x_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_){
_start:
{
lean_object* v_res_3868_; 
v_res_3868_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__2_spec__3(v_00_u03b1_3861_, v_x_3862_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_);
lean_dec(v___y_3866_);
lean_dec_ref(v___y_3865_);
lean_dec(v___y_3864_);
lean_dec_ref(v___y_3863_);
return v_res_3868_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__1___redArg(lean_object* v_cls_3869_, lean_object* v___y_3870_){
_start:
{
lean_object* v_options_3872_; uint8_t v_hasTrace_3873_; 
v_options_3872_ = lean_ctor_get(v___y_3870_, 2);
v_hasTrace_3873_ = lean_ctor_get_uint8(v_options_3872_, sizeof(void*)*1);
if (v_hasTrace_3873_ == 0)
{
lean_object* v___x_3874_; lean_object* v___x_3875_; 
lean_dec(v_cls_3869_);
v___x_3874_ = lean_box(v_hasTrace_3873_);
v___x_3875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3875_, 0, v___x_3874_);
return v___x_3875_;
}
else
{
lean_object* v_inheritedTraceOptions_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; uint8_t v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; 
v_inheritedTraceOptions_3876_ = lean_ctor_get(v___y_3870_, 13);
v___x_3877_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__1));
v___x_3878_ = l_Lean_Name_append(v___x_3877_, v_cls_3869_);
v___x_3879_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3876_, v_options_3872_, v___x_3878_);
lean_dec(v___x_3878_);
v___x_3880_ = lean_box(v___x_3879_);
v___x_3881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3881_, 0, v___x_3880_);
return v___x_3881_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__1___redArg___boxed(lean_object* v_cls_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_){
_start:
{
lean_object* v_res_3885_; 
v_res_3885_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__1___redArg(v_cls_3882_, v___y_3883_);
lean_dec_ref(v___y_3883_);
return v_res_3885_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__1(lean_object* v_cls_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_){
_start:
{
lean_object* v___x_3894_; 
v___x_3894_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__1___redArg(v_cls_3886_, v___y_3891_);
return v___x_3894_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__1___boxed(lean_object* v_cls_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_){
_start:
{
lean_object* v_res_3903_; 
v_res_3903_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__1(v_cls_3895_, v___y_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_);
lean_dec(v___y_3901_);
lean_dec_ref(v___y_3900_);
lean_dec(v___y_3899_);
lean_dec_ref(v___y_3898_);
lean_dec(v___y_3897_);
lean_dec_ref(v___y_3896_);
return v_res_3903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2___redArg(lean_object* v___y_3904_){
_start:
{
lean_object* v___x_3906_; lean_object* v_traceState_3907_; lean_object* v_traces_3908_; lean_object* v___x_3909_; lean_object* v_traceState_3910_; lean_object* v_env_3911_; lean_object* v_nextMacroScope_3912_; lean_object* v_ngen_3913_; lean_object* v_auxDeclNGen_3914_; lean_object* v_cache_3915_; lean_object* v_messages_3916_; lean_object* v_infoState_3917_; lean_object* v_snapshotTasks_3918_; lean_object* v___x_3920_; uint8_t v_isShared_3921_; uint8_t v_isSharedCheck_3939_; 
v___x_3906_ = lean_st_ref_get(v___y_3904_);
v_traceState_3907_ = lean_ctor_get(v___x_3906_, 4);
lean_inc_ref(v_traceState_3907_);
lean_dec(v___x_3906_);
v_traces_3908_ = lean_ctor_get(v_traceState_3907_, 0);
lean_inc_ref(v_traces_3908_);
lean_dec_ref(v_traceState_3907_);
v___x_3909_ = lean_st_ref_take(v___y_3904_);
v_traceState_3910_ = lean_ctor_get(v___x_3909_, 4);
v_env_3911_ = lean_ctor_get(v___x_3909_, 0);
v_nextMacroScope_3912_ = lean_ctor_get(v___x_3909_, 1);
v_ngen_3913_ = lean_ctor_get(v___x_3909_, 2);
v_auxDeclNGen_3914_ = lean_ctor_get(v___x_3909_, 3);
v_cache_3915_ = lean_ctor_get(v___x_3909_, 5);
v_messages_3916_ = lean_ctor_get(v___x_3909_, 6);
v_infoState_3917_ = lean_ctor_get(v___x_3909_, 7);
v_snapshotTasks_3918_ = lean_ctor_get(v___x_3909_, 8);
v_isSharedCheck_3939_ = !lean_is_exclusive(v___x_3909_);
if (v_isSharedCheck_3939_ == 0)
{
v___x_3920_ = v___x_3909_;
v_isShared_3921_ = v_isSharedCheck_3939_;
goto v_resetjp_3919_;
}
else
{
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
v___x_3920_ = lean_box(0);
v_isShared_3921_ = v_isSharedCheck_3939_;
goto v_resetjp_3919_;
}
v_resetjp_3919_:
{
uint64_t v_tid_3922_; lean_object* v___x_3924_; uint8_t v_isShared_3925_; uint8_t v_isSharedCheck_3937_; 
v_tid_3922_ = lean_ctor_get_uint64(v_traceState_3910_, sizeof(void*)*1);
v_isSharedCheck_3937_ = !lean_is_exclusive(v_traceState_3910_);
if (v_isSharedCheck_3937_ == 0)
{
lean_object* v_unused_3938_; 
v_unused_3938_ = lean_ctor_get(v_traceState_3910_, 0);
lean_dec(v_unused_3938_);
v___x_3924_ = v_traceState_3910_;
v_isShared_3925_ = v_isSharedCheck_3937_;
goto v_resetjp_3923_;
}
else
{
lean_dec(v_traceState_3910_);
v___x_3924_ = lean_box(0);
v_isShared_3925_ = v_isSharedCheck_3937_;
goto v_resetjp_3923_;
}
v_resetjp_3923_:
{
lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3930_; 
v___x_3926_ = lean_unsigned_to_nat(32u);
v___x_3927_ = lean_mk_empty_array_with_capacity(v___x_3926_);
lean_dec_ref(v___x_3927_);
v___x_3928_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___redArg___closed__1);
if (v_isShared_3925_ == 0)
{
lean_ctor_set(v___x_3924_, 0, v___x_3928_);
v___x_3930_ = v___x_3924_;
goto v_reusejp_3929_;
}
else
{
lean_object* v_reuseFailAlloc_3936_; 
v_reuseFailAlloc_3936_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3936_, 0, v___x_3928_);
lean_ctor_set_uint64(v_reuseFailAlloc_3936_, sizeof(void*)*1, v_tid_3922_);
v___x_3930_ = v_reuseFailAlloc_3936_;
goto v_reusejp_3929_;
}
v_reusejp_3929_:
{
lean_object* v___x_3932_; 
if (v_isShared_3921_ == 0)
{
lean_ctor_set(v___x_3920_, 4, v___x_3930_);
v___x_3932_ = v___x_3920_;
goto v_reusejp_3931_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v_env_3911_);
lean_ctor_set(v_reuseFailAlloc_3935_, 1, v_nextMacroScope_3912_);
lean_ctor_set(v_reuseFailAlloc_3935_, 2, v_ngen_3913_);
lean_ctor_set(v_reuseFailAlloc_3935_, 3, v_auxDeclNGen_3914_);
lean_ctor_set(v_reuseFailAlloc_3935_, 4, v___x_3930_);
lean_ctor_set(v_reuseFailAlloc_3935_, 5, v_cache_3915_);
lean_ctor_set(v_reuseFailAlloc_3935_, 6, v_messages_3916_);
lean_ctor_set(v_reuseFailAlloc_3935_, 7, v_infoState_3917_);
lean_ctor_set(v_reuseFailAlloc_3935_, 8, v_snapshotTasks_3918_);
v___x_3932_ = v_reuseFailAlloc_3935_;
goto v_reusejp_3931_;
}
v_reusejp_3931_:
{
lean_object* v___x_3933_; lean_object* v___x_3934_; 
v___x_3933_ = lean_st_ref_set(v___y_3904_, v___x_3932_);
v___x_3934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3934_, 0, v_traces_3908_);
return v___x_3934_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2___redArg___boxed(lean_object* v___y_3940_, lean_object* v___y_3941_){
_start:
{
lean_object* v_res_3942_; 
v_res_3942_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2___redArg(v___y_3940_);
lean_dec(v___y_3940_);
return v_res_3942_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2(lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_){
_start:
{
lean_object* v___x_3950_; 
v___x_3950_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2___redArg(v___y_3948_);
return v___x_3950_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2___boxed(lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_){
_start:
{
lean_object* v_res_3958_; 
v_res_3958_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2(v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_);
lean_dec(v___y_3956_);
lean_dec_ref(v___y_3955_);
lean_dec(v___y_3954_);
lean_dec_ref(v___y_3953_);
lean_dec(v___y_3952_);
lean_dec_ref(v___y_3951_);
return v_res_3958_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__5___redArg___lam__0(lean_object* v_x_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_){
_start:
{
lean_object* v___x_3967_; 
v___x_3967_ = lean_apply_7(v_x_3959_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_, lean_box(0));
return v___x_3967_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__5___redArg___lam__0___boxed(lean_object* v_x_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_){
_start:
{
lean_object* v_res_3976_; 
v_res_3976_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__5___redArg___lam__0(v_x_3968_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_);
return v_res_3976_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__5___redArg(lean_object* v_mvarId_3977_, lean_object* v_x_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_){
_start:
{
lean_object* v___f_3986_; lean_object* v___x_3987_; 
v___f_3986_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__5___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_3986_, 0, v_x_3978_);
lean_closure_set(v___f_3986_, 1, v___y_3979_);
lean_closure_set(v___f_3986_, 2, v___y_3980_);
v___x_3987_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3977_, v___f_3986_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_);
if (lean_obj_tag(v___x_3987_) == 0)
{
return v___x_3987_;
}
else
{
lean_object* v_a_3988_; lean_object* v___x_3990_; uint8_t v_isShared_3991_; uint8_t v_isSharedCheck_3995_; 
v_a_3988_ = lean_ctor_get(v___x_3987_, 0);
v_isSharedCheck_3995_ = !lean_is_exclusive(v___x_3987_);
if (v_isSharedCheck_3995_ == 0)
{
v___x_3990_ = v___x_3987_;
v_isShared_3991_ = v_isSharedCheck_3995_;
goto v_resetjp_3989_;
}
else
{
lean_inc(v_a_3988_);
lean_dec(v___x_3987_);
v___x_3990_ = lean_box(0);
v_isShared_3991_ = v_isSharedCheck_3995_;
goto v_resetjp_3989_;
}
v_resetjp_3989_:
{
lean_object* v___x_3993_; 
if (v_isShared_3991_ == 0)
{
v___x_3993_ = v___x_3990_;
goto v_reusejp_3992_;
}
else
{
lean_object* v_reuseFailAlloc_3994_; 
v_reuseFailAlloc_3994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3994_, 0, v_a_3988_);
v___x_3993_ = v_reuseFailAlloc_3994_;
goto v_reusejp_3992_;
}
v_reusejp_3992_:
{
return v___x_3993_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__5___redArg___boxed(lean_object* v_mvarId_3996_, lean_object* v_x_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_){
_start:
{
lean_object* v_res_4005_; 
v_res_4005_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__5___redArg(v_mvarId_3996_, v_x_3997_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_);
return v_res_4005_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__5(lean_object* v_00_u03b1_4006_, lean_object* v_mvarId_4007_, lean_object* v_x_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_){
_start:
{
lean_object* v___x_4016_; 
v___x_4016_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__5___redArg(v_mvarId_4007_, v_x_4008_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_);
return v___x_4016_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__5___boxed(lean_object* v_00_u03b1_4017_, lean_object* v_mvarId_4018_, lean_object* v_x_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_){
_start:
{
lean_object* v_res_4027_; 
v_res_4027_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__5(v_00_u03b1_4017_, v_mvarId_4018_, v_x_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_);
return v_res_4027_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4029_; lean_object* v___x_4030_; 
v___x_4029_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__0));
v___x_4030_ = l_Lean_stringToMessageData(v___x_4029_);
return v___x_4030_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4032_; lean_object* v___x_4033_; 
v___x_4032_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__2));
v___x_4033_ = l_Lean_stringToMessageData(v___x_4032_);
return v___x_4033_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4035_; lean_object* v___x_4036_; 
v___x_4035_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__4));
v___x_4036_ = l_Lean_stringToMessageData(v___x_4035_);
return v___x_4036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0(lean_object* v_a_4037_, lean_object* v_x_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_){
_start:
{
if (lean_obj_tag(v_x_4038_) == 0)
{
lean_object* v_a_4046_; lean_object* v___x_4048_; uint8_t v_isShared_4049_; uint8_t v_isSharedCheck_4056_; 
lean_dec_ref(v_a_4037_);
v_a_4046_ = lean_ctor_get(v_x_4038_, 0);
v_isSharedCheck_4056_ = !lean_is_exclusive(v_x_4038_);
if (v_isSharedCheck_4056_ == 0)
{
v___x_4048_ = v_x_4038_;
v_isShared_4049_ = v_isSharedCheck_4056_;
goto v_resetjp_4047_;
}
else
{
lean_inc(v_a_4046_);
lean_dec(v_x_4038_);
v___x_4048_ = lean_box(0);
v_isShared_4049_ = v_isSharedCheck_4056_;
goto v_resetjp_4047_;
}
v_resetjp_4047_:
{
lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4054_; 
v___x_4050_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__1);
v___x_4051_ = l_Lean_Exception_toMessageData(v_a_4046_);
v___x_4052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4052_, 0, v___x_4050_);
lean_ctor_set(v___x_4052_, 1, v___x_4051_);
if (v_isShared_4049_ == 0)
{
lean_ctor_set(v___x_4048_, 0, v___x_4052_);
v___x_4054_ = v___x_4048_;
goto v_reusejp_4053_;
}
else
{
lean_object* v_reuseFailAlloc_4055_; 
v_reuseFailAlloc_4055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4055_, 0, v___x_4052_);
v___x_4054_ = v_reuseFailAlloc_4055_;
goto v_reusejp_4053_;
}
v_reusejp_4053_:
{
return v___x_4054_;
}
}
}
else
{
lean_object* v_a_4057_; lean_object* v___x_4059_; uint8_t v_isShared_4060_; uint8_t v_isSharedCheck_4076_; 
v_a_4057_ = lean_ctor_get(v_x_4038_, 0);
v_isSharedCheck_4076_ = !lean_is_exclusive(v_x_4038_);
if (v_isSharedCheck_4076_ == 0)
{
v___x_4059_ = v_x_4038_;
v_isShared_4060_ = v_isSharedCheck_4076_;
goto v_resetjp_4058_;
}
else
{
lean_inc(v_a_4057_);
lean_dec(v_x_4038_);
v___x_4059_ = lean_box(0);
v_isShared_4060_ = v_isSharedCheck_4076_;
goto v_resetjp_4058_;
}
v_resetjp_4058_:
{
if (lean_obj_tag(v_a_4057_) == 0)
{
lean_object* v___x_4061_; lean_object* v___x_4063_; 
lean_dec_ref(v_a_4057_);
lean_dec_ref(v_a_4037_);
v___x_4061_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__3, &l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__3);
if (v_isShared_4060_ == 0)
{
lean_ctor_set_tag(v___x_4059_, 0);
lean_ctor_set(v___x_4059_, 0, v___x_4061_);
v___x_4063_ = v___x_4059_;
goto v_reusejp_4062_;
}
else
{
lean_object* v_reuseFailAlloc_4064_; 
v_reuseFailAlloc_4064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4064_, 0, v___x_4061_);
v___x_4063_ = v_reuseFailAlloc_4064_;
goto v_reusejp_4062_;
}
v_reusejp_4062_:
{
return v___x_4063_;
}
}
else
{
lean_object* v_e_x27_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4074_; 
v_e_x27_4065_ = lean_ctor_get(v_a_4057_, 0);
lean_inc_ref(v_e_x27_4065_);
lean_dec_ref(v_a_4057_);
v___x_4066_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__5, &l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__5_once, _init_l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___closed__5);
v___x_4067_ = l_Lean_indentExpr(v_a_4037_);
v___x_4068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4068_, 0, v___x_4066_);
lean_ctor_set(v___x_4068_, 1, v___x_4067_);
v___x_4069_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7);
v___x_4070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4070_, 0, v___x_4068_);
lean_ctor_set(v___x_4070_, 1, v___x_4069_);
v___x_4071_ = l_Lean_indentExpr(v_e_x27_4065_);
v___x_4072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4072_, 0, v___x_4070_);
lean_ctor_set(v___x_4072_, 1, v___x_4071_);
if (v_isShared_4060_ == 0)
{
lean_ctor_set_tag(v___x_4059_, 0);
lean_ctor_set(v___x_4059_, 0, v___x_4072_);
v___x_4074_ = v___x_4059_;
goto v_reusejp_4073_;
}
else
{
lean_object* v_reuseFailAlloc_4075_; 
v_reuseFailAlloc_4075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4075_, 0, v___x_4072_);
v___x_4074_ = v_reuseFailAlloc_4075_;
goto v_reusejp_4073_;
}
v_reusejp_4073_:
{
return v___x_4074_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___boxed(lean_object* v_a_4077_, lean_object* v_x_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_){
_start:
{
lean_object* v_res_4086_; 
v_res_4086_ = l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0(v_a_4077_, v_x_4078_, v___y_4079_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_);
lean_dec(v___y_4084_);
lean_dec_ref(v___y_4083_);
lean_dec(v___y_4082_);
lean_dec_ref(v___y_4081_);
lean_dec(v___y_4080_);
lean_dec_ref(v___y_4079_);
return v_res_4086_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3_spec__5___redArg(lean_object* v_x_4087_){
_start:
{
if (lean_obj_tag(v_x_4087_) == 0)
{
lean_object* v_a_4089_; lean_object* v___x_4091_; uint8_t v_isShared_4092_; uint8_t v_isSharedCheck_4096_; 
v_a_4089_ = lean_ctor_get(v_x_4087_, 0);
v_isSharedCheck_4096_ = !lean_is_exclusive(v_x_4087_);
if (v_isSharedCheck_4096_ == 0)
{
v___x_4091_ = v_x_4087_;
v_isShared_4092_ = v_isSharedCheck_4096_;
goto v_resetjp_4090_;
}
else
{
lean_inc(v_a_4089_);
lean_dec(v_x_4087_);
v___x_4091_ = lean_box(0);
v_isShared_4092_ = v_isSharedCheck_4096_;
goto v_resetjp_4090_;
}
v_resetjp_4090_:
{
lean_object* v___x_4094_; 
if (v_isShared_4092_ == 0)
{
lean_ctor_set_tag(v___x_4091_, 1);
v___x_4094_ = v___x_4091_;
goto v_reusejp_4093_;
}
else
{
lean_object* v_reuseFailAlloc_4095_; 
v_reuseFailAlloc_4095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4095_, 0, v_a_4089_);
v___x_4094_ = v_reuseFailAlloc_4095_;
goto v_reusejp_4093_;
}
v_reusejp_4093_:
{
return v___x_4094_;
}
}
}
else
{
lean_object* v_a_4097_; lean_object* v___x_4099_; uint8_t v_isShared_4100_; uint8_t v_isSharedCheck_4104_; 
v_a_4097_ = lean_ctor_get(v_x_4087_, 0);
v_isSharedCheck_4104_ = !lean_is_exclusive(v_x_4087_);
if (v_isSharedCheck_4104_ == 0)
{
v___x_4099_ = v_x_4087_;
v_isShared_4100_ = v_isSharedCheck_4104_;
goto v_resetjp_4098_;
}
else
{
lean_inc(v_a_4097_);
lean_dec(v_x_4087_);
v___x_4099_ = lean_box(0);
v_isShared_4100_ = v_isSharedCheck_4104_;
goto v_resetjp_4098_;
}
v_resetjp_4098_:
{
lean_object* v___x_4102_; 
if (v_isShared_4100_ == 0)
{
lean_ctor_set_tag(v___x_4099_, 0);
v___x_4102_ = v___x_4099_;
goto v_reusejp_4101_;
}
else
{
lean_object* v_reuseFailAlloc_4103_; 
v_reuseFailAlloc_4103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4103_, 0, v_a_4097_);
v___x_4102_ = v_reuseFailAlloc_4103_;
goto v_reusejp_4101_;
}
v_reusejp_4101_:
{
return v___x_4102_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3_spec__5___redArg___boxed(lean_object* v_x_4105_, lean_object* v___y_4106_){
_start:
{
lean_object* v_res_4107_; 
v_res_4107_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3_spec__5___redArg(v_x_4105_);
return v_res_4107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3_spec__4___redArg(lean_object* v_oldTraces_4108_, lean_object* v_data_4109_, lean_object* v_ref_4110_, lean_object* v_msg_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_){
_start:
{
lean_object* v_fileName_4117_; lean_object* v_fileMap_4118_; lean_object* v_options_4119_; lean_object* v_currRecDepth_4120_; lean_object* v_maxRecDepth_4121_; lean_object* v_ref_4122_; lean_object* v_currNamespace_4123_; lean_object* v_openDecls_4124_; lean_object* v_initHeartbeats_4125_; lean_object* v_maxHeartbeats_4126_; lean_object* v_quotContext_4127_; lean_object* v_currMacroScope_4128_; uint8_t v_diag_4129_; lean_object* v_cancelTk_x3f_4130_; uint8_t v_suppressElabErrors_4131_; lean_object* v_inheritedTraceOptions_4132_; lean_object* v___x_4134_; uint8_t v_isShared_4135_; uint8_t v_isSharedCheck_4187_; 
v_fileName_4117_ = lean_ctor_get(v___y_4114_, 0);
v_fileMap_4118_ = lean_ctor_get(v___y_4114_, 1);
v_options_4119_ = lean_ctor_get(v___y_4114_, 2);
v_currRecDepth_4120_ = lean_ctor_get(v___y_4114_, 3);
v_maxRecDepth_4121_ = lean_ctor_get(v___y_4114_, 4);
v_ref_4122_ = lean_ctor_get(v___y_4114_, 5);
v_currNamespace_4123_ = lean_ctor_get(v___y_4114_, 6);
v_openDecls_4124_ = lean_ctor_get(v___y_4114_, 7);
v_initHeartbeats_4125_ = lean_ctor_get(v___y_4114_, 8);
v_maxHeartbeats_4126_ = lean_ctor_get(v___y_4114_, 9);
v_quotContext_4127_ = lean_ctor_get(v___y_4114_, 10);
v_currMacroScope_4128_ = lean_ctor_get(v___y_4114_, 11);
v_diag_4129_ = lean_ctor_get_uint8(v___y_4114_, sizeof(void*)*14);
v_cancelTk_x3f_4130_ = lean_ctor_get(v___y_4114_, 12);
v_suppressElabErrors_4131_ = lean_ctor_get_uint8(v___y_4114_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_4132_ = lean_ctor_get(v___y_4114_, 13);
v_isSharedCheck_4187_ = !lean_is_exclusive(v___y_4114_);
if (v_isSharedCheck_4187_ == 0)
{
v___x_4134_ = v___y_4114_;
v_isShared_4135_ = v_isSharedCheck_4187_;
goto v_resetjp_4133_;
}
else
{
lean_inc(v_inheritedTraceOptions_4132_);
lean_inc(v_cancelTk_x3f_4130_);
lean_inc(v_currMacroScope_4128_);
lean_inc(v_quotContext_4127_);
lean_inc(v_maxHeartbeats_4126_);
lean_inc(v_initHeartbeats_4125_);
lean_inc(v_openDecls_4124_);
lean_inc(v_currNamespace_4123_);
lean_inc(v_ref_4122_);
lean_inc(v_maxRecDepth_4121_);
lean_inc(v_currRecDepth_4120_);
lean_inc(v_options_4119_);
lean_inc(v_fileMap_4118_);
lean_inc(v_fileName_4117_);
lean_dec(v___y_4114_);
v___x_4134_ = lean_box(0);
v_isShared_4135_ = v_isSharedCheck_4187_;
goto v_resetjp_4133_;
}
v_resetjp_4133_:
{
lean_object* v___x_4136_; lean_object* v_traceState_4137_; lean_object* v_traces_4138_; lean_object* v_ref_4139_; lean_object* v___x_4141_; 
v___x_4136_ = lean_st_ref_get(v___y_4115_);
v_traceState_4137_ = lean_ctor_get(v___x_4136_, 4);
lean_inc_ref(v_traceState_4137_);
lean_dec(v___x_4136_);
v_traces_4138_ = lean_ctor_get(v_traceState_4137_, 0);
lean_inc_ref(v_traces_4138_);
lean_dec_ref(v_traceState_4137_);
v_ref_4139_ = l_Lean_replaceRef(v_ref_4110_, v_ref_4122_);
lean_dec(v_ref_4122_);
if (v_isShared_4135_ == 0)
{
lean_ctor_set(v___x_4134_, 5, v_ref_4139_);
v___x_4141_ = v___x_4134_;
goto v_reusejp_4140_;
}
else
{
lean_object* v_reuseFailAlloc_4186_; 
v_reuseFailAlloc_4186_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_4186_, 0, v_fileName_4117_);
lean_ctor_set(v_reuseFailAlloc_4186_, 1, v_fileMap_4118_);
lean_ctor_set(v_reuseFailAlloc_4186_, 2, v_options_4119_);
lean_ctor_set(v_reuseFailAlloc_4186_, 3, v_currRecDepth_4120_);
lean_ctor_set(v_reuseFailAlloc_4186_, 4, v_maxRecDepth_4121_);
lean_ctor_set(v_reuseFailAlloc_4186_, 5, v_ref_4139_);
lean_ctor_set(v_reuseFailAlloc_4186_, 6, v_currNamespace_4123_);
lean_ctor_set(v_reuseFailAlloc_4186_, 7, v_openDecls_4124_);
lean_ctor_set(v_reuseFailAlloc_4186_, 8, v_initHeartbeats_4125_);
lean_ctor_set(v_reuseFailAlloc_4186_, 9, v_maxHeartbeats_4126_);
lean_ctor_set(v_reuseFailAlloc_4186_, 10, v_quotContext_4127_);
lean_ctor_set(v_reuseFailAlloc_4186_, 11, v_currMacroScope_4128_);
lean_ctor_set(v_reuseFailAlloc_4186_, 12, v_cancelTk_x3f_4130_);
lean_ctor_set(v_reuseFailAlloc_4186_, 13, v_inheritedTraceOptions_4132_);
lean_ctor_set_uint8(v_reuseFailAlloc_4186_, sizeof(void*)*14, v_diag_4129_);
lean_ctor_set_uint8(v_reuseFailAlloc_4186_, sizeof(void*)*14 + 1, v_suppressElabErrors_4131_);
v___x_4141_ = v_reuseFailAlloc_4186_;
goto v_reusejp_4140_;
}
v_reusejp_4140_:
{
lean_object* v___x_4142_; size_t v_sz_4143_; size_t v___x_4144_; lean_object* v___x_4145_; lean_object* v_msg_4146_; lean_object* v___x_4147_; lean_object* v_a_4148_; lean_object* v___x_4150_; uint8_t v_isShared_4151_; uint8_t v_isSharedCheck_4185_; 
v___x_4142_ = l_Lean_PersistentArray_toArray___redArg(v_traces_4138_);
lean_dec_ref(v_traces_4138_);
v_sz_4143_ = lean_array_size(v___x_4142_);
v___x_4144_ = ((size_t)0ULL);
v___x_4145_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__4_spec__5(v_sz_4143_, v___x_4144_, v___x_4142_);
v_msg_4146_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_4146_, 0, v_data_4109_);
lean_ctor_set(v_msg_4146_, 1, v_msg_4111_);
lean_ctor_set(v_msg_4146_, 2, v___x_4145_);
v___x_4147_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1_spec__1(v_msg_4146_, v___y_4112_, v___y_4113_, v___x_4141_, v___y_4115_);
lean_dec_ref(v___x_4141_);
v_a_4148_ = lean_ctor_get(v___x_4147_, 0);
v_isSharedCheck_4185_ = !lean_is_exclusive(v___x_4147_);
if (v_isSharedCheck_4185_ == 0)
{
v___x_4150_ = v___x_4147_;
v_isShared_4151_ = v_isSharedCheck_4185_;
goto v_resetjp_4149_;
}
else
{
lean_inc(v_a_4148_);
lean_dec(v___x_4147_);
v___x_4150_ = lean_box(0);
v_isShared_4151_ = v_isSharedCheck_4185_;
goto v_resetjp_4149_;
}
v_resetjp_4149_:
{
lean_object* v___x_4152_; lean_object* v_traceState_4153_; lean_object* v_env_4154_; lean_object* v_nextMacroScope_4155_; lean_object* v_ngen_4156_; lean_object* v_auxDeclNGen_4157_; lean_object* v_cache_4158_; lean_object* v_messages_4159_; lean_object* v_infoState_4160_; lean_object* v_snapshotTasks_4161_; lean_object* v___x_4163_; uint8_t v_isShared_4164_; uint8_t v_isSharedCheck_4184_; 
v___x_4152_ = lean_st_ref_take(v___y_4115_);
v_traceState_4153_ = lean_ctor_get(v___x_4152_, 4);
v_env_4154_ = lean_ctor_get(v___x_4152_, 0);
v_nextMacroScope_4155_ = lean_ctor_get(v___x_4152_, 1);
v_ngen_4156_ = lean_ctor_get(v___x_4152_, 2);
v_auxDeclNGen_4157_ = lean_ctor_get(v___x_4152_, 3);
v_cache_4158_ = lean_ctor_get(v___x_4152_, 5);
v_messages_4159_ = lean_ctor_get(v___x_4152_, 6);
v_infoState_4160_ = lean_ctor_get(v___x_4152_, 7);
v_snapshotTasks_4161_ = lean_ctor_get(v___x_4152_, 8);
v_isSharedCheck_4184_ = !lean_is_exclusive(v___x_4152_);
if (v_isSharedCheck_4184_ == 0)
{
v___x_4163_ = v___x_4152_;
v_isShared_4164_ = v_isSharedCheck_4184_;
goto v_resetjp_4162_;
}
else
{
lean_inc(v_snapshotTasks_4161_);
lean_inc(v_infoState_4160_);
lean_inc(v_messages_4159_);
lean_inc(v_cache_4158_);
lean_inc(v_traceState_4153_);
lean_inc(v_auxDeclNGen_4157_);
lean_inc(v_ngen_4156_);
lean_inc(v_nextMacroScope_4155_);
lean_inc(v_env_4154_);
lean_dec(v___x_4152_);
v___x_4163_ = lean_box(0);
v_isShared_4164_ = v_isSharedCheck_4184_;
goto v_resetjp_4162_;
}
v_resetjp_4162_:
{
uint64_t v_tid_4165_; lean_object* v___x_4167_; uint8_t v_isShared_4168_; uint8_t v_isSharedCheck_4182_; 
v_tid_4165_ = lean_ctor_get_uint64(v_traceState_4153_, sizeof(void*)*1);
v_isSharedCheck_4182_ = !lean_is_exclusive(v_traceState_4153_);
if (v_isSharedCheck_4182_ == 0)
{
lean_object* v_unused_4183_; 
v_unused_4183_ = lean_ctor_get(v_traceState_4153_, 0);
lean_dec(v_unused_4183_);
v___x_4167_ = v_traceState_4153_;
v_isShared_4168_ = v_isSharedCheck_4182_;
goto v_resetjp_4166_;
}
else
{
lean_dec(v_traceState_4153_);
v___x_4167_ = lean_box(0);
v_isShared_4168_ = v_isSharedCheck_4182_;
goto v_resetjp_4166_;
}
v_resetjp_4166_:
{
lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4172_; 
v___x_4169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4169_, 0, v_ref_4110_);
lean_ctor_set(v___x_4169_, 1, v_a_4148_);
v___x_4170_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_4108_, v___x_4169_);
if (v_isShared_4168_ == 0)
{
lean_ctor_set(v___x_4167_, 0, v___x_4170_);
v___x_4172_ = v___x_4167_;
goto v_reusejp_4171_;
}
else
{
lean_object* v_reuseFailAlloc_4181_; 
v_reuseFailAlloc_4181_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4181_, 0, v___x_4170_);
lean_ctor_set_uint64(v_reuseFailAlloc_4181_, sizeof(void*)*1, v_tid_4165_);
v___x_4172_ = v_reuseFailAlloc_4181_;
goto v_reusejp_4171_;
}
v_reusejp_4171_:
{
lean_object* v___x_4174_; 
if (v_isShared_4164_ == 0)
{
lean_ctor_set(v___x_4163_, 4, v___x_4172_);
v___x_4174_ = v___x_4163_;
goto v_reusejp_4173_;
}
else
{
lean_object* v_reuseFailAlloc_4180_; 
v_reuseFailAlloc_4180_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4180_, 0, v_env_4154_);
lean_ctor_set(v_reuseFailAlloc_4180_, 1, v_nextMacroScope_4155_);
lean_ctor_set(v_reuseFailAlloc_4180_, 2, v_ngen_4156_);
lean_ctor_set(v_reuseFailAlloc_4180_, 3, v_auxDeclNGen_4157_);
lean_ctor_set(v_reuseFailAlloc_4180_, 4, v___x_4172_);
lean_ctor_set(v_reuseFailAlloc_4180_, 5, v_cache_4158_);
lean_ctor_set(v_reuseFailAlloc_4180_, 6, v_messages_4159_);
lean_ctor_set(v_reuseFailAlloc_4180_, 7, v_infoState_4160_);
lean_ctor_set(v_reuseFailAlloc_4180_, 8, v_snapshotTasks_4161_);
v___x_4174_ = v_reuseFailAlloc_4180_;
goto v_reusejp_4173_;
}
v_reusejp_4173_:
{
lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4178_; 
v___x_4175_ = lean_st_ref_set(v___y_4115_, v___x_4174_);
v___x_4176_ = lean_box(0);
if (v_isShared_4151_ == 0)
{
lean_ctor_set(v___x_4150_, 0, v___x_4176_);
v___x_4178_ = v___x_4150_;
goto v_reusejp_4177_;
}
else
{
lean_object* v_reuseFailAlloc_4179_; 
v_reuseFailAlloc_4179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4179_, 0, v___x_4176_);
v___x_4178_ = v_reuseFailAlloc_4179_;
goto v_reusejp_4177_;
}
v_reusejp_4177_:
{
return v___x_4178_;
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3_spec__4___redArg___boxed(lean_object* v_oldTraces_4188_, lean_object* v_data_4189_, lean_object* v_ref_4190_, lean_object* v_msg_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_){
_start:
{
lean_object* v_res_4197_; 
v_res_4197_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3_spec__4___redArg(v_oldTraces_4188_, v_data_4189_, v_ref_4190_, v_msg_4191_, v___y_4192_, v___y_4193_, v___y_4194_, v___y_4195_);
lean_dec(v___y_4195_);
lean_dec(v___y_4193_);
lean_dec_ref(v___y_4192_);
return v_res_4197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3(lean_object* v_cls_4198_, uint8_t v_collapsed_4199_, lean_object* v_tag_4200_, lean_object* v_opts_4201_, uint8_t v_clsEnabled_4202_, lean_object* v_oldTraces_4203_, lean_object* v_msg_4204_, lean_object* v_resStartStop_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_){
_start:
{
lean_object* v_fst_4213_; lean_object* v_snd_4214_; lean_object* v___x_4216_; uint8_t v_isShared_4217_; uint8_t v_isSharedCheck_4312_; 
v_fst_4213_ = lean_ctor_get(v_resStartStop_4205_, 0);
v_snd_4214_ = lean_ctor_get(v_resStartStop_4205_, 1);
v_isSharedCheck_4312_ = !lean_is_exclusive(v_resStartStop_4205_);
if (v_isSharedCheck_4312_ == 0)
{
v___x_4216_ = v_resStartStop_4205_;
v_isShared_4217_ = v_isSharedCheck_4312_;
goto v_resetjp_4215_;
}
else
{
lean_inc(v_snd_4214_);
lean_inc(v_fst_4213_);
lean_dec(v_resStartStop_4205_);
v___x_4216_ = lean_box(0);
v_isShared_4217_ = v_isSharedCheck_4312_;
goto v_resetjp_4215_;
}
v_resetjp_4215_:
{
lean_object* v___y_4219_; lean_object* v___y_4220_; lean_object* v_data_4221_; lean_object* v_fst_4232_; lean_object* v_snd_4233_; lean_object* v___x_4235_; uint8_t v_isShared_4236_; uint8_t v_isSharedCheck_4311_; 
v_fst_4232_ = lean_ctor_get(v_snd_4214_, 0);
v_snd_4233_ = lean_ctor_get(v_snd_4214_, 1);
v_isSharedCheck_4311_ = !lean_is_exclusive(v_snd_4214_);
if (v_isSharedCheck_4311_ == 0)
{
v___x_4235_ = v_snd_4214_;
v_isShared_4236_ = v_isSharedCheck_4311_;
goto v_resetjp_4234_;
}
else
{
lean_inc(v_snd_4233_);
lean_inc(v_fst_4232_);
lean_dec(v_snd_4214_);
v___x_4235_ = lean_box(0);
v_isShared_4236_ = v_isSharedCheck_4311_;
goto v_resetjp_4234_;
}
v___jp_4218_:
{
lean_object* v___x_4222_; 
v___x_4222_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3_spec__4___redArg(v_oldTraces_4203_, v_data_4221_, v___y_4219_, v___y_4220_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_);
lean_dec(v___y_4211_);
lean_dec(v___y_4209_);
lean_dec_ref(v___y_4208_);
if (lean_obj_tag(v___x_4222_) == 0)
{
lean_object* v___x_4223_; 
lean_dec_ref(v___x_4222_);
v___x_4223_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3_spec__5___redArg(v_fst_4213_);
return v___x_4223_;
}
else
{
lean_object* v_a_4224_; lean_object* v___x_4226_; uint8_t v_isShared_4227_; uint8_t v_isSharedCheck_4231_; 
lean_dec(v_fst_4213_);
v_a_4224_ = lean_ctor_get(v___x_4222_, 0);
v_isSharedCheck_4231_ = !lean_is_exclusive(v___x_4222_);
if (v_isSharedCheck_4231_ == 0)
{
v___x_4226_ = v___x_4222_;
v_isShared_4227_ = v_isSharedCheck_4231_;
goto v_resetjp_4225_;
}
else
{
lean_inc(v_a_4224_);
lean_dec(v___x_4222_);
v___x_4226_ = lean_box(0);
v_isShared_4227_ = v_isSharedCheck_4231_;
goto v_resetjp_4225_;
}
v_resetjp_4225_:
{
lean_object* v___x_4229_; 
if (v_isShared_4227_ == 0)
{
v___x_4229_ = v___x_4226_;
goto v_reusejp_4228_;
}
else
{
lean_object* v_reuseFailAlloc_4230_; 
v_reuseFailAlloc_4230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4230_, 0, v_a_4224_);
v___x_4229_ = v_reuseFailAlloc_4230_;
goto v_reusejp_4228_;
}
v_reusejp_4228_:
{
return v___x_4229_;
}
}
}
}
v_resetjp_4234_:
{
lean_object* v___x_4237_; uint8_t v___x_4238_; lean_object* v___y_4240_; lean_object* v_a_4241_; uint8_t v___y_4265_; double v___y_4296_; 
v___x_4237_ = l_Lean_trace_profiler;
v___x_4238_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2(v_opts_4201_, v___x_4237_);
if (v___x_4238_ == 0)
{
v___y_4265_ = v___x_4238_;
goto v___jp_4264_;
}
else
{
lean_object* v___x_4301_; uint8_t v___x_4302_; 
v___x_4301_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4302_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2(v_opts_4201_, v___x_4301_);
if (v___x_4302_ == 0)
{
lean_object* v___x_4303_; lean_object* v___x_4304_; double v___x_4305_; double v___x_4306_; double v___x_4307_; 
v___x_4303_ = l_Lean_trace_profiler_threshold;
v___x_4304_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__6(v_opts_4201_, v___x_4303_);
v___x_4305_ = lean_float_of_nat(v___x_4304_);
v___x_4306_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__4);
v___x_4307_ = lean_float_div(v___x_4305_, v___x_4306_);
v___y_4296_ = v___x_4307_;
goto v___jp_4295_;
}
else
{
lean_object* v___x_4308_; lean_object* v___x_4309_; double v___x_4310_; 
v___x_4308_ = l_Lean_trace_profiler_threshold;
v___x_4309_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__6(v_opts_4201_, v___x_4308_);
v___x_4310_ = lean_float_of_nat(v___x_4309_);
v___y_4296_ = v___x_4310_;
goto v___jp_4295_;
}
}
v___jp_4239_:
{
uint8_t v_result_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4247_; 
v_result_4242_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__3(v_fst_4213_);
v___x_4243_ = l_Lean_TraceResult_toEmoji(v_result_4242_);
v___x_4244_ = l_Lean_stringToMessageData(v___x_4243_);
v___x_4245_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__1);
if (v_isShared_4236_ == 0)
{
lean_ctor_set_tag(v___x_4235_, 7);
lean_ctor_set(v___x_4235_, 1, v___x_4245_);
lean_ctor_set(v___x_4235_, 0, v___x_4244_);
v___x_4247_ = v___x_4235_;
goto v_reusejp_4246_;
}
else
{
lean_object* v_reuseFailAlloc_4258_; 
v_reuseFailAlloc_4258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4258_, 0, v___x_4244_);
lean_ctor_set(v_reuseFailAlloc_4258_, 1, v___x_4245_);
v___x_4247_ = v_reuseFailAlloc_4258_;
goto v_reusejp_4246_;
}
v_reusejp_4246_:
{
lean_object* v_m_4249_; 
if (v_isShared_4217_ == 0)
{
lean_ctor_set_tag(v___x_4216_, 7);
lean_ctor_set(v___x_4216_, 1, v_a_4241_);
lean_ctor_set(v___x_4216_, 0, v___x_4247_);
v_m_4249_ = v___x_4216_;
goto v_reusejp_4248_;
}
else
{
lean_object* v_reuseFailAlloc_4257_; 
v_reuseFailAlloc_4257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4257_, 0, v___x_4247_);
lean_ctor_set(v_reuseFailAlloc_4257_, 1, v_a_4241_);
v_m_4249_ = v_reuseFailAlloc_4257_;
goto v_reusejp_4248_;
}
v_reusejp_4248_:
{
lean_object* v___x_4250_; lean_object* v___x_4251_; double v___x_4252_; lean_object* v_data_4253_; 
v___x_4250_ = lean_box(v_result_4242_);
v___x_4251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4251_, 0, v___x_4250_);
v___x_4252_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__0);
lean_inc_ref(v_tag_4200_);
lean_inc_ref(v___x_4251_);
lean_inc(v_cls_4198_);
v_data_4253_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4253_, 0, v_cls_4198_);
lean_ctor_set(v_data_4253_, 1, v___x_4251_);
lean_ctor_set(v_data_4253_, 2, v_tag_4200_);
lean_ctor_set_float(v_data_4253_, sizeof(void*)*3, v___x_4252_);
lean_ctor_set_float(v_data_4253_, sizeof(void*)*3 + 8, v___x_4252_);
lean_ctor_set_uint8(v_data_4253_, sizeof(void*)*3 + 16, v_collapsed_4199_);
if (v___x_4238_ == 0)
{
lean_dec_ref(v___x_4251_);
lean_dec(v_snd_4233_);
lean_dec(v_fst_4232_);
lean_dec_ref(v_tag_4200_);
lean_dec(v_cls_4198_);
v___y_4219_ = v___y_4240_;
v___y_4220_ = v_m_4249_;
v_data_4221_ = v_data_4253_;
goto v___jp_4218_;
}
else
{
lean_object* v_data_4254_; double v___x_4255_; double v___x_4256_; 
lean_dec_ref(v_data_4253_);
v_data_4254_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4254_, 0, v_cls_4198_);
lean_ctor_set(v_data_4254_, 1, v___x_4251_);
lean_ctor_set(v_data_4254_, 2, v_tag_4200_);
v___x_4255_ = lean_unbox_float(v_fst_4232_);
lean_dec(v_fst_4232_);
lean_ctor_set_float(v_data_4254_, sizeof(void*)*3, v___x_4255_);
v___x_4256_ = lean_unbox_float(v_snd_4233_);
lean_dec(v_snd_4233_);
lean_ctor_set_float(v_data_4254_, sizeof(void*)*3 + 8, v___x_4256_);
lean_ctor_set_uint8(v_data_4254_, sizeof(void*)*3 + 16, v_collapsed_4199_);
v___y_4219_ = v___y_4240_;
v___y_4220_ = v_m_4249_;
v_data_4221_ = v_data_4254_;
goto v___jp_4218_;
}
}
}
}
v___jp_4259_:
{
lean_object* v_ref_4260_; lean_object* v___x_4261_; 
v_ref_4260_ = lean_ctor_get(v___y_4210_, 5);
lean_inc(v___y_4211_);
lean_inc_ref(v___y_4210_);
lean_inc(v___y_4209_);
lean_inc_ref(v___y_4208_);
lean_inc(v_fst_4213_);
v___x_4261_ = lean_apply_8(v_msg_4204_, v_fst_4213_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_, lean_box(0));
if (lean_obj_tag(v___x_4261_) == 0)
{
lean_object* v_a_4262_; 
v_a_4262_ = lean_ctor_get(v___x_4261_, 0);
lean_inc(v_a_4262_);
lean_dec_ref(v___x_4261_);
lean_inc(v_ref_4260_);
v___y_4240_ = v_ref_4260_;
v_a_4241_ = v_a_4262_;
goto v___jp_4239_;
}
else
{
lean_object* v___x_4263_; 
lean_dec_ref(v___x_4261_);
v___x_4263_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__3);
lean_inc(v_ref_4260_);
v___y_4240_ = v_ref_4260_;
v_a_4241_ = v___x_4263_;
goto v___jp_4239_;
}
}
v___jp_4264_:
{
if (v_clsEnabled_4202_ == 0)
{
if (v___y_4265_ == 0)
{
lean_object* v___x_4266_; lean_object* v_traceState_4267_; lean_object* v_env_4268_; lean_object* v_nextMacroScope_4269_; lean_object* v_ngen_4270_; lean_object* v_auxDeclNGen_4271_; lean_object* v_cache_4272_; lean_object* v_messages_4273_; lean_object* v_infoState_4274_; lean_object* v_snapshotTasks_4275_; lean_object* v___x_4277_; uint8_t v_isShared_4278_; uint8_t v_isSharedCheck_4294_; 
lean_del_object(v___x_4235_);
lean_dec(v_snd_4233_);
lean_dec(v_fst_4232_);
lean_del_object(v___x_4216_);
lean_dec_ref(v___y_4210_);
lean_dec(v___y_4209_);
lean_dec_ref(v___y_4208_);
lean_dec(v___y_4207_);
lean_dec_ref(v___y_4206_);
lean_dec_ref(v_msg_4204_);
lean_dec_ref(v_tag_4200_);
lean_dec(v_cls_4198_);
v___x_4266_ = lean_st_ref_take(v___y_4211_);
v_traceState_4267_ = lean_ctor_get(v___x_4266_, 4);
v_env_4268_ = lean_ctor_get(v___x_4266_, 0);
v_nextMacroScope_4269_ = lean_ctor_get(v___x_4266_, 1);
v_ngen_4270_ = lean_ctor_get(v___x_4266_, 2);
v_auxDeclNGen_4271_ = lean_ctor_get(v___x_4266_, 3);
v_cache_4272_ = lean_ctor_get(v___x_4266_, 5);
v_messages_4273_ = lean_ctor_get(v___x_4266_, 6);
v_infoState_4274_ = lean_ctor_get(v___x_4266_, 7);
v_snapshotTasks_4275_ = lean_ctor_get(v___x_4266_, 8);
v_isSharedCheck_4294_ = !lean_is_exclusive(v___x_4266_);
if (v_isSharedCheck_4294_ == 0)
{
v___x_4277_ = v___x_4266_;
v_isShared_4278_ = v_isSharedCheck_4294_;
goto v_resetjp_4276_;
}
else
{
lean_inc(v_snapshotTasks_4275_);
lean_inc(v_infoState_4274_);
lean_inc(v_messages_4273_);
lean_inc(v_cache_4272_);
lean_inc(v_traceState_4267_);
lean_inc(v_auxDeclNGen_4271_);
lean_inc(v_ngen_4270_);
lean_inc(v_nextMacroScope_4269_);
lean_inc(v_env_4268_);
lean_dec(v___x_4266_);
v___x_4277_ = lean_box(0);
v_isShared_4278_ = v_isSharedCheck_4294_;
goto v_resetjp_4276_;
}
v_resetjp_4276_:
{
uint64_t v_tid_4279_; lean_object* v_traces_4280_; lean_object* v___x_4282_; uint8_t v_isShared_4283_; uint8_t v_isSharedCheck_4293_; 
v_tid_4279_ = lean_ctor_get_uint64(v_traceState_4267_, sizeof(void*)*1);
v_traces_4280_ = lean_ctor_get(v_traceState_4267_, 0);
v_isSharedCheck_4293_ = !lean_is_exclusive(v_traceState_4267_);
if (v_isSharedCheck_4293_ == 0)
{
v___x_4282_ = v_traceState_4267_;
v_isShared_4283_ = v_isSharedCheck_4293_;
goto v_resetjp_4281_;
}
else
{
lean_inc(v_traces_4280_);
lean_dec(v_traceState_4267_);
v___x_4282_ = lean_box(0);
v_isShared_4283_ = v_isSharedCheck_4293_;
goto v_resetjp_4281_;
}
v_resetjp_4281_:
{
lean_object* v___x_4284_; lean_object* v___x_4286_; 
v___x_4284_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_4203_, v_traces_4280_);
lean_dec_ref(v_traces_4280_);
if (v_isShared_4283_ == 0)
{
lean_ctor_set(v___x_4282_, 0, v___x_4284_);
v___x_4286_ = v___x_4282_;
goto v_reusejp_4285_;
}
else
{
lean_object* v_reuseFailAlloc_4292_; 
v_reuseFailAlloc_4292_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4292_, 0, v___x_4284_);
lean_ctor_set_uint64(v_reuseFailAlloc_4292_, sizeof(void*)*1, v_tid_4279_);
v___x_4286_ = v_reuseFailAlloc_4292_;
goto v_reusejp_4285_;
}
v_reusejp_4285_:
{
lean_object* v___x_4288_; 
if (v_isShared_4278_ == 0)
{
lean_ctor_set(v___x_4277_, 4, v___x_4286_);
v___x_4288_ = v___x_4277_;
goto v_reusejp_4287_;
}
else
{
lean_object* v_reuseFailAlloc_4291_; 
v_reuseFailAlloc_4291_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4291_, 0, v_env_4268_);
lean_ctor_set(v_reuseFailAlloc_4291_, 1, v_nextMacroScope_4269_);
lean_ctor_set(v_reuseFailAlloc_4291_, 2, v_ngen_4270_);
lean_ctor_set(v_reuseFailAlloc_4291_, 3, v_auxDeclNGen_4271_);
lean_ctor_set(v_reuseFailAlloc_4291_, 4, v___x_4286_);
lean_ctor_set(v_reuseFailAlloc_4291_, 5, v_cache_4272_);
lean_ctor_set(v_reuseFailAlloc_4291_, 6, v_messages_4273_);
lean_ctor_set(v_reuseFailAlloc_4291_, 7, v_infoState_4274_);
lean_ctor_set(v_reuseFailAlloc_4291_, 8, v_snapshotTasks_4275_);
v___x_4288_ = v_reuseFailAlloc_4291_;
goto v_reusejp_4287_;
}
v_reusejp_4287_:
{
lean_object* v___x_4289_; lean_object* v___x_4290_; 
v___x_4289_ = lean_st_ref_set(v___y_4211_, v___x_4288_);
lean_dec(v___y_4211_);
v___x_4290_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3_spec__5___redArg(v_fst_4213_);
return v___x_4290_;
}
}
}
}
}
else
{
goto v___jp_4259_;
}
}
else
{
goto v___jp_4259_;
}
}
v___jp_4295_:
{
double v___x_4297_; double v___x_4298_; double v___x_4299_; uint8_t v___x_4300_; 
v___x_4297_ = lean_unbox_float(v_snd_4233_);
v___x_4298_ = lean_unbox_float(v_fst_4232_);
v___x_4299_ = lean_float_sub(v___x_4297_, v___x_4298_);
v___x_4300_ = lean_float_decLt(v___y_4296_, v___x_4299_);
v___y_4265_ = v___x_4300_;
goto v___jp_4264_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3___boxed(lean_object* v_cls_4313_, lean_object* v_collapsed_4314_, lean_object* v_tag_4315_, lean_object* v_opts_4316_, lean_object* v_clsEnabled_4317_, lean_object* v_oldTraces_4318_, lean_object* v_msg_4319_, lean_object* v_resStartStop_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_){
_start:
{
uint8_t v_collapsed_boxed_4328_; uint8_t v_clsEnabled_boxed_4329_; lean_object* v_res_4330_; 
v_collapsed_boxed_4328_ = lean_unbox(v_collapsed_4314_);
v_clsEnabled_boxed_4329_ = lean_unbox(v_clsEnabled_4317_);
v_res_4330_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3(v_cls_4313_, v_collapsed_boxed_4328_, v_tag_4315_, v_opts_4316_, v_clsEnabled_boxed_4329_, v_oldTraces_4318_, v_msg_4319_, v_resStartStop_4320_, v___y_4321_, v___y_4322_, v___y_4323_, v___y_4324_, v___y_4325_, v___y_4326_);
lean_dec_ref(v_opts_4316_);
return v_res_4330_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4332_; lean_object* v___x_4333_; 
v___x_4332_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__0));
v___x_4333_ = l_Lean_stringToMessageData(v___x_4332_);
return v___x_4333_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4335_; lean_object* v___x_4336_; 
v___x_4335_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__2));
v___x_4336_ = l_Lean_stringToMessageData(v___x_4335_);
return v___x_4336_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4338_; lean_object* v___x_4339_; 
v___x_4338_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__4));
v___x_4339_ = l_Lean_stringToMessageData(v___x_4338_);
return v___x_4339_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0(lean_object* v_a_4340_, lean_object* v___x_4341_, lean_object* v_x_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_){
_start:
{
if (lean_obj_tag(v_x_4342_) == 0)
{
lean_object* v_a_4350_; lean_object* v___x_4352_; uint8_t v_isShared_4353_; uint8_t v_isSharedCheck_4365_; 
lean_dec_ref(v___x_4341_);
v_a_4350_ = lean_ctor_get(v_x_4342_, 0);
v_isSharedCheck_4365_ = !lean_is_exclusive(v_x_4342_);
if (v_isSharedCheck_4365_ == 0)
{
v___x_4352_ = v_x_4342_;
v_isShared_4353_ = v_isSharedCheck_4365_;
goto v_resetjp_4351_;
}
else
{
lean_inc(v_a_4350_);
lean_dec(v_x_4342_);
v___x_4352_ = lean_box(0);
v_isShared_4353_ = v_isSharedCheck_4365_;
goto v_resetjp_4351_;
}
v_resetjp_4351_:
{
lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4363_; 
v___x_4354_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__1);
v___x_4355_ = l_Lean_LocalDecl_userName(v_a_4340_);
v___x_4356_ = l_Lean_MessageData_ofName(v___x_4355_);
v___x_4357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4357_, 0, v___x_4354_);
lean_ctor_set(v___x_4357_, 1, v___x_4356_);
v___x_4358_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__3);
v___x_4359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4359_, 0, v___x_4357_);
lean_ctor_set(v___x_4359_, 1, v___x_4358_);
v___x_4360_ = l_Lean_Exception_toMessageData(v_a_4350_);
v___x_4361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4361_, 0, v___x_4359_);
lean_ctor_set(v___x_4361_, 1, v___x_4360_);
if (v_isShared_4353_ == 0)
{
lean_ctor_set(v___x_4352_, 0, v___x_4361_);
v___x_4363_ = v___x_4352_;
goto v_reusejp_4362_;
}
else
{
lean_object* v_reuseFailAlloc_4364_; 
v_reuseFailAlloc_4364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4364_, 0, v___x_4361_);
v___x_4363_ = v_reuseFailAlloc_4364_;
goto v_reusejp_4362_;
}
v_reusejp_4362_:
{
return v___x_4363_;
}
}
}
else
{
lean_object* v_a_4366_; lean_object* v___x_4368_; uint8_t v_isShared_4369_; uint8_t v_isSharedCheck_4395_; 
v_a_4366_ = lean_ctor_get(v_x_4342_, 0);
v_isSharedCheck_4395_ = !lean_is_exclusive(v_x_4342_);
if (v_isSharedCheck_4395_ == 0)
{
v___x_4368_ = v_x_4342_;
v_isShared_4369_ = v_isSharedCheck_4395_;
goto v_resetjp_4367_;
}
else
{
lean_inc(v_a_4366_);
lean_dec(v_x_4342_);
v___x_4368_ = lean_box(0);
v_isShared_4369_ = v_isSharedCheck_4395_;
goto v_resetjp_4367_;
}
v_resetjp_4367_:
{
if (lean_obj_tag(v_a_4366_) == 0)
{
lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4377_; 
lean_dec_ref(v_a_4366_);
lean_dec_ref(v___x_4341_);
v___x_4370_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__1);
v___x_4371_ = l_Lean_LocalDecl_userName(v_a_4340_);
v___x_4372_ = l_Lean_MessageData_ofName(v___x_4371_);
v___x_4373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4373_, 0, v___x_4370_);
lean_ctor_set(v___x_4373_, 1, v___x_4372_);
v___x_4374_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__5);
v___x_4375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4375_, 0, v___x_4373_);
lean_ctor_set(v___x_4375_, 1, v___x_4374_);
if (v_isShared_4369_ == 0)
{
lean_ctor_set_tag(v___x_4368_, 0);
lean_ctor_set(v___x_4368_, 0, v___x_4375_);
v___x_4377_ = v___x_4368_;
goto v_reusejp_4376_;
}
else
{
lean_object* v_reuseFailAlloc_4378_; 
v_reuseFailAlloc_4378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4378_, 0, v___x_4375_);
v___x_4377_ = v_reuseFailAlloc_4378_;
goto v_reusejp_4376_;
}
v_reusejp_4376_:
{
return v___x_4377_;
}
}
else
{
lean_object* v_e_x27_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4393_; 
v_e_x27_4379_ = lean_ctor_get(v_a_4366_, 0);
lean_inc_ref(v_e_x27_4379_);
lean_dec_ref(v_a_4366_);
v___x_4380_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___closed__1);
v___x_4381_ = l_Lean_LocalDecl_userName(v_a_4340_);
v___x_4382_ = l_Lean_MessageData_ofName(v___x_4381_);
v___x_4383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4383_, 0, v___x_4380_);
lean_ctor_set(v___x_4383_, 1, v___x_4382_);
v___x_4384_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__5, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__5_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__5);
v___x_4385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4385_, 0, v___x_4383_);
lean_ctor_set(v___x_4385_, 1, v___x_4384_);
v___x_4386_ = l_Lean_indentExpr(v___x_4341_);
v___x_4387_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4387_, 0, v___x_4385_);
lean_ctor_set(v___x_4387_, 1, v___x_4386_);
v___x_4388_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7);
v___x_4389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4389_, 0, v___x_4387_);
lean_ctor_set(v___x_4389_, 1, v___x_4388_);
v___x_4390_ = l_Lean_indentExpr(v_e_x27_4379_);
v___x_4391_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4391_, 0, v___x_4389_);
lean_ctor_set(v___x_4391_, 1, v___x_4390_);
if (v_isShared_4369_ == 0)
{
lean_ctor_set_tag(v___x_4368_, 0);
lean_ctor_set(v___x_4368_, 0, v___x_4391_);
v___x_4393_ = v___x_4368_;
goto v_reusejp_4392_;
}
else
{
lean_object* v_reuseFailAlloc_4394_; 
v_reuseFailAlloc_4394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4394_, 0, v___x_4391_);
v___x_4393_ = v_reuseFailAlloc_4394_;
goto v_reusejp_4392_;
}
v_reusejp_4392_:
{
return v___x_4393_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___boxed(lean_object* v_a_4396_, lean_object* v___x_4397_, lean_object* v_x_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_){
_start:
{
lean_object* v_res_4406_; 
v_res_4406_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0(v_a_4396_, v___x_4397_, v_x_4398_, v___y_4399_, v___y_4400_, v___y_4401_, v___y_4402_, v___y_4403_, v___y_4404_);
lean_dec(v___y_4404_);
lean_dec_ref(v___y_4403_);
lean_dec(v___y_4402_);
lean_dec_ref(v___y_4401_);
lean_dec(v___y_4400_);
lean_dec_ref(v___y_4399_);
lean_dec_ref(v_a_4396_);
return v_res_4406_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4_spec__8_spec__10___redArg(lean_object* v_x_4407_, lean_object* v_x_4408_, lean_object* v_x_4409_, lean_object* v_x_4410_){
_start:
{
lean_object* v_ks_4411_; lean_object* v_vs_4412_; lean_object* v___x_4414_; uint8_t v_isShared_4415_; uint8_t v_isSharedCheck_4436_; 
v_ks_4411_ = lean_ctor_get(v_x_4407_, 0);
v_vs_4412_ = lean_ctor_get(v_x_4407_, 1);
v_isSharedCheck_4436_ = !lean_is_exclusive(v_x_4407_);
if (v_isSharedCheck_4436_ == 0)
{
v___x_4414_ = v_x_4407_;
v_isShared_4415_ = v_isSharedCheck_4436_;
goto v_resetjp_4413_;
}
else
{
lean_inc(v_vs_4412_);
lean_inc(v_ks_4411_);
lean_dec(v_x_4407_);
v___x_4414_ = lean_box(0);
v_isShared_4415_ = v_isSharedCheck_4436_;
goto v_resetjp_4413_;
}
v_resetjp_4413_:
{
lean_object* v___x_4416_; uint8_t v___x_4417_; 
v___x_4416_ = lean_array_get_size(v_ks_4411_);
v___x_4417_ = lean_nat_dec_lt(v_x_4408_, v___x_4416_);
if (v___x_4417_ == 0)
{
lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4421_; 
lean_dec(v_x_4408_);
v___x_4418_ = lean_array_push(v_ks_4411_, v_x_4409_);
v___x_4419_ = lean_array_push(v_vs_4412_, v_x_4410_);
if (v_isShared_4415_ == 0)
{
lean_ctor_set(v___x_4414_, 1, v___x_4419_);
lean_ctor_set(v___x_4414_, 0, v___x_4418_);
v___x_4421_ = v___x_4414_;
goto v_reusejp_4420_;
}
else
{
lean_object* v_reuseFailAlloc_4422_; 
v_reuseFailAlloc_4422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4422_, 0, v___x_4418_);
lean_ctor_set(v_reuseFailAlloc_4422_, 1, v___x_4419_);
v___x_4421_ = v_reuseFailAlloc_4422_;
goto v_reusejp_4420_;
}
v_reusejp_4420_:
{
return v___x_4421_;
}
}
else
{
lean_object* v_k_x27_4423_; uint8_t v___x_4424_; 
v_k_x27_4423_ = lean_array_fget_borrowed(v_ks_4411_, v_x_4408_);
v___x_4424_ = l_Lean_instBEqMVarId_beq(v_x_4409_, v_k_x27_4423_);
if (v___x_4424_ == 0)
{
lean_object* v___x_4426_; 
if (v_isShared_4415_ == 0)
{
v___x_4426_ = v___x_4414_;
goto v_reusejp_4425_;
}
else
{
lean_object* v_reuseFailAlloc_4430_; 
v_reuseFailAlloc_4430_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4430_, 0, v_ks_4411_);
lean_ctor_set(v_reuseFailAlloc_4430_, 1, v_vs_4412_);
v___x_4426_ = v_reuseFailAlloc_4430_;
goto v_reusejp_4425_;
}
v_reusejp_4425_:
{
lean_object* v___x_4427_; lean_object* v___x_4428_; 
v___x_4427_ = lean_unsigned_to_nat(1u);
v___x_4428_ = lean_nat_add(v_x_4408_, v___x_4427_);
lean_dec(v_x_4408_);
v_x_4407_ = v___x_4426_;
v_x_4408_ = v___x_4428_;
goto _start;
}
}
else
{
lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4434_; 
v___x_4431_ = lean_array_fset(v_ks_4411_, v_x_4408_, v_x_4409_);
v___x_4432_ = lean_array_fset(v_vs_4412_, v_x_4408_, v_x_4410_);
lean_dec(v_x_4408_);
if (v_isShared_4415_ == 0)
{
lean_ctor_set(v___x_4414_, 1, v___x_4432_);
lean_ctor_set(v___x_4414_, 0, v___x_4431_);
v___x_4434_ = v___x_4414_;
goto v_reusejp_4433_;
}
else
{
lean_object* v_reuseFailAlloc_4435_; 
v_reuseFailAlloc_4435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4435_, 0, v___x_4431_);
lean_ctor_set(v_reuseFailAlloc_4435_, 1, v___x_4432_);
v___x_4434_ = v_reuseFailAlloc_4435_;
goto v_reusejp_4433_;
}
v_reusejp_4433_:
{
return v___x_4434_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4_spec__8___redArg(lean_object* v_n_4437_, lean_object* v_k_4438_, lean_object* v_v_4439_){
_start:
{
lean_object* v___x_4440_; lean_object* v___x_4441_; 
v___x_4440_ = lean_unsigned_to_nat(0u);
v___x_4441_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4_spec__8_spec__10___redArg(v_n_4437_, v___x_4440_, v_k_4438_, v_v_4439_);
return v___x_4441_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4___redArg___closed__0(void){
_start:
{
size_t v___x_4442_; size_t v___x_4443_; size_t v___x_4444_; 
v___x_4442_ = ((size_t)5ULL);
v___x_4443_ = ((size_t)1ULL);
v___x_4444_ = lean_usize_shift_left(v___x_4443_, v___x_4442_);
return v___x_4444_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_4445_; size_t v___x_4446_; size_t v___x_4447_; 
v___x_4445_ = ((size_t)1ULL);
v___x_4446_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4___redArg___closed__0);
v___x_4447_ = lean_usize_sub(v___x_4446_, v___x_4445_);
return v___x_4447_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_4448_; 
v___x_4448_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_4448_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4___redArg(lean_object* v_x_4449_, size_t v_x_4450_, size_t v_x_4451_, lean_object* v_x_4452_, lean_object* v_x_4453_){
_start:
{
if (lean_obj_tag(v_x_4449_) == 0)
{
lean_object* v_es_4454_; size_t v___x_4455_; size_t v___x_4456_; size_t v___x_4457_; size_t v___x_4458_; lean_object* v_j_4459_; lean_object* v___x_4460_; uint8_t v___x_4461_; 
v_es_4454_ = lean_ctor_get(v_x_4449_, 0);
v___x_4455_ = ((size_t)5ULL);
v___x_4456_ = ((size_t)1ULL);
v___x_4457_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4___redArg___closed__1);
v___x_4458_ = lean_usize_land(v_x_4450_, v___x_4457_);
v_j_4459_ = lean_usize_to_nat(v___x_4458_);
v___x_4460_ = lean_array_get_size(v_es_4454_);
v___x_4461_ = lean_nat_dec_lt(v_j_4459_, v___x_4460_);
if (v___x_4461_ == 0)
{
lean_dec(v_j_4459_);
lean_dec(v_x_4453_);
lean_dec(v_x_4452_);
return v_x_4449_;
}
else
{
lean_object* v___x_4463_; uint8_t v_isShared_4464_; uint8_t v_isSharedCheck_4498_; 
lean_inc_ref(v_es_4454_);
v_isSharedCheck_4498_ = !lean_is_exclusive(v_x_4449_);
if (v_isSharedCheck_4498_ == 0)
{
lean_object* v_unused_4499_; 
v_unused_4499_ = lean_ctor_get(v_x_4449_, 0);
lean_dec(v_unused_4499_);
v___x_4463_ = v_x_4449_;
v_isShared_4464_ = v_isSharedCheck_4498_;
goto v_resetjp_4462_;
}
else
{
lean_dec(v_x_4449_);
v___x_4463_ = lean_box(0);
v_isShared_4464_ = v_isSharedCheck_4498_;
goto v_resetjp_4462_;
}
v_resetjp_4462_:
{
lean_object* v_v_4465_; lean_object* v___x_4466_; lean_object* v_xs_x27_4467_; lean_object* v___y_4469_; 
v_v_4465_ = lean_array_fget(v_es_4454_, v_j_4459_);
v___x_4466_ = lean_box(0);
v_xs_x27_4467_ = lean_array_fset(v_es_4454_, v_j_4459_, v___x_4466_);
switch(lean_obj_tag(v_v_4465_))
{
case 0:
{
lean_object* v_key_4474_; lean_object* v_val_4475_; lean_object* v___x_4477_; uint8_t v_isShared_4478_; uint8_t v_isSharedCheck_4485_; 
v_key_4474_ = lean_ctor_get(v_v_4465_, 0);
v_val_4475_ = lean_ctor_get(v_v_4465_, 1);
v_isSharedCheck_4485_ = !lean_is_exclusive(v_v_4465_);
if (v_isSharedCheck_4485_ == 0)
{
v___x_4477_ = v_v_4465_;
v_isShared_4478_ = v_isSharedCheck_4485_;
goto v_resetjp_4476_;
}
else
{
lean_inc(v_val_4475_);
lean_inc(v_key_4474_);
lean_dec(v_v_4465_);
v___x_4477_ = lean_box(0);
v_isShared_4478_ = v_isSharedCheck_4485_;
goto v_resetjp_4476_;
}
v_resetjp_4476_:
{
uint8_t v___x_4479_; 
v___x_4479_ = l_Lean_instBEqMVarId_beq(v_x_4452_, v_key_4474_);
if (v___x_4479_ == 0)
{
lean_object* v___x_4480_; lean_object* v___x_4481_; 
lean_del_object(v___x_4477_);
v___x_4480_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_4474_, v_val_4475_, v_x_4452_, v_x_4453_);
v___x_4481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4481_, 0, v___x_4480_);
v___y_4469_ = v___x_4481_;
goto v___jp_4468_;
}
else
{
lean_object* v___x_4483_; 
lean_dec(v_val_4475_);
lean_dec(v_key_4474_);
if (v_isShared_4478_ == 0)
{
lean_ctor_set(v___x_4477_, 1, v_x_4453_);
lean_ctor_set(v___x_4477_, 0, v_x_4452_);
v___x_4483_ = v___x_4477_;
goto v_reusejp_4482_;
}
else
{
lean_object* v_reuseFailAlloc_4484_; 
v_reuseFailAlloc_4484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4484_, 0, v_x_4452_);
lean_ctor_set(v_reuseFailAlloc_4484_, 1, v_x_4453_);
v___x_4483_ = v_reuseFailAlloc_4484_;
goto v_reusejp_4482_;
}
v_reusejp_4482_:
{
v___y_4469_ = v___x_4483_;
goto v___jp_4468_;
}
}
}
}
case 1:
{
lean_object* v_node_4486_; lean_object* v___x_4488_; uint8_t v_isShared_4489_; uint8_t v_isSharedCheck_4496_; 
v_node_4486_ = lean_ctor_get(v_v_4465_, 0);
v_isSharedCheck_4496_ = !lean_is_exclusive(v_v_4465_);
if (v_isSharedCheck_4496_ == 0)
{
v___x_4488_ = v_v_4465_;
v_isShared_4489_ = v_isSharedCheck_4496_;
goto v_resetjp_4487_;
}
else
{
lean_inc(v_node_4486_);
lean_dec(v_v_4465_);
v___x_4488_ = lean_box(0);
v_isShared_4489_ = v_isSharedCheck_4496_;
goto v_resetjp_4487_;
}
v_resetjp_4487_:
{
size_t v___x_4490_; size_t v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4494_; 
v___x_4490_ = lean_usize_shift_right(v_x_4450_, v___x_4455_);
v___x_4491_ = lean_usize_add(v_x_4451_, v___x_4456_);
v___x_4492_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4___redArg(v_node_4486_, v___x_4490_, v___x_4491_, v_x_4452_, v_x_4453_);
if (v_isShared_4489_ == 0)
{
lean_ctor_set(v___x_4488_, 0, v___x_4492_);
v___x_4494_ = v___x_4488_;
goto v_reusejp_4493_;
}
else
{
lean_object* v_reuseFailAlloc_4495_; 
v_reuseFailAlloc_4495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4495_, 0, v___x_4492_);
v___x_4494_ = v_reuseFailAlloc_4495_;
goto v_reusejp_4493_;
}
v_reusejp_4493_:
{
v___y_4469_ = v___x_4494_;
goto v___jp_4468_;
}
}
}
default: 
{
lean_object* v___x_4497_; 
v___x_4497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4497_, 0, v_x_4452_);
lean_ctor_set(v___x_4497_, 1, v_x_4453_);
v___y_4469_ = v___x_4497_;
goto v___jp_4468_;
}
}
v___jp_4468_:
{
lean_object* v___x_4470_; lean_object* v___x_4472_; 
v___x_4470_ = lean_array_fset(v_xs_x27_4467_, v_j_4459_, v___y_4469_);
lean_dec(v_j_4459_);
if (v_isShared_4464_ == 0)
{
lean_ctor_set(v___x_4463_, 0, v___x_4470_);
v___x_4472_ = v___x_4463_;
goto v_reusejp_4471_;
}
else
{
lean_object* v_reuseFailAlloc_4473_; 
v_reuseFailAlloc_4473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4473_, 0, v___x_4470_);
v___x_4472_ = v_reuseFailAlloc_4473_;
goto v_reusejp_4471_;
}
v_reusejp_4471_:
{
return v___x_4472_;
}
}
}
}
}
else
{
lean_object* v_ks_4500_; lean_object* v_vs_4501_; lean_object* v___x_4503_; uint8_t v_isShared_4504_; uint8_t v_isSharedCheck_4521_; 
v_ks_4500_ = lean_ctor_get(v_x_4449_, 0);
v_vs_4501_ = lean_ctor_get(v_x_4449_, 1);
v_isSharedCheck_4521_ = !lean_is_exclusive(v_x_4449_);
if (v_isSharedCheck_4521_ == 0)
{
v___x_4503_ = v_x_4449_;
v_isShared_4504_ = v_isSharedCheck_4521_;
goto v_resetjp_4502_;
}
else
{
lean_inc(v_vs_4501_);
lean_inc(v_ks_4500_);
lean_dec(v_x_4449_);
v___x_4503_ = lean_box(0);
v_isShared_4504_ = v_isSharedCheck_4521_;
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
lean_object* v_reuseFailAlloc_4520_; 
v_reuseFailAlloc_4520_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4520_, 0, v_ks_4500_);
lean_ctor_set(v_reuseFailAlloc_4520_, 1, v_vs_4501_);
v___x_4506_ = v_reuseFailAlloc_4520_;
goto v_reusejp_4505_;
}
v_reusejp_4505_:
{
lean_object* v_newNode_4507_; uint8_t v___y_4509_; size_t v___x_4515_; uint8_t v___x_4516_; 
v_newNode_4507_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4_spec__8___redArg(v___x_4506_, v_x_4452_, v_x_4453_);
v___x_4515_ = ((size_t)7ULL);
v___x_4516_ = lean_usize_dec_le(v___x_4515_, v_x_4451_);
if (v___x_4516_ == 0)
{
lean_object* v___x_4517_; lean_object* v___x_4518_; uint8_t v___x_4519_; 
v___x_4517_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4507_);
v___x_4518_ = lean_unsigned_to_nat(4u);
v___x_4519_ = lean_nat_dec_lt(v___x_4517_, v___x_4518_);
lean_dec(v___x_4517_);
v___y_4509_ = v___x_4519_;
goto v___jp_4508_;
}
else
{
v___y_4509_ = v___x_4516_;
goto v___jp_4508_;
}
v___jp_4508_:
{
if (v___y_4509_ == 0)
{
lean_object* v_ks_4510_; lean_object* v_vs_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; 
v_ks_4510_ = lean_ctor_get(v_newNode_4507_, 0);
lean_inc_ref(v_ks_4510_);
v_vs_4511_ = lean_ctor_get(v_newNode_4507_, 1);
lean_inc_ref(v_vs_4511_);
lean_dec_ref(v_newNode_4507_);
v___x_4512_ = lean_unsigned_to_nat(0u);
v___x_4513_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4___redArg___closed__2);
v___x_4514_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4_spec__9___redArg(v_x_4451_, v_ks_4510_, v_vs_4511_, v___x_4512_, v___x_4513_);
lean_dec_ref(v_vs_4511_);
lean_dec_ref(v_ks_4510_);
return v___x_4514_;
}
else
{
return v_newNode_4507_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4_spec__9___redArg(size_t v_depth_4522_, lean_object* v_keys_4523_, lean_object* v_vals_4524_, lean_object* v_i_4525_, lean_object* v_entries_4526_){
_start:
{
lean_object* v___x_4527_; uint8_t v___x_4528_; 
v___x_4527_ = lean_array_get_size(v_keys_4523_);
v___x_4528_ = lean_nat_dec_lt(v_i_4525_, v___x_4527_);
if (v___x_4528_ == 0)
{
lean_dec(v_i_4525_);
return v_entries_4526_;
}
else
{
lean_object* v_k_4529_; lean_object* v_v_4530_; uint64_t v___x_4531_; size_t v_h_4532_; size_t v___x_4533_; lean_object* v___x_4534_; size_t v___x_4535_; size_t v___x_4536_; size_t v___x_4537_; size_t v_h_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; 
v_k_4529_ = lean_array_fget_borrowed(v_keys_4523_, v_i_4525_);
v_v_4530_ = lean_array_fget_borrowed(v_vals_4524_, v_i_4525_);
v___x_4531_ = l_Lean_instHashableMVarId_hash(v_k_4529_);
v_h_4532_ = lean_uint64_to_usize(v___x_4531_);
v___x_4533_ = ((size_t)5ULL);
v___x_4534_ = lean_unsigned_to_nat(1u);
v___x_4535_ = ((size_t)1ULL);
v___x_4536_ = lean_usize_sub(v_depth_4522_, v___x_4535_);
v___x_4537_ = lean_usize_mul(v___x_4533_, v___x_4536_);
v_h_4538_ = lean_usize_shift_right(v_h_4532_, v___x_4537_);
v___x_4539_ = lean_nat_add(v_i_4525_, v___x_4534_);
lean_dec(v_i_4525_);
lean_inc(v_v_4530_);
lean_inc(v_k_4529_);
v___x_4540_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4___redArg(v_entries_4526_, v_h_4538_, v_depth_4522_, v_k_4529_, v_v_4530_);
v_i_4525_ = v___x_4539_;
v_entries_4526_ = v___x_4540_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4_spec__9___redArg___boxed(lean_object* v_depth_4542_, lean_object* v_keys_4543_, lean_object* v_vals_4544_, lean_object* v_i_4545_, lean_object* v_entries_4546_){
_start:
{
size_t v_depth_boxed_4547_; lean_object* v_res_4548_; 
v_depth_boxed_4547_ = lean_unbox_usize(v_depth_4542_);
lean_dec(v_depth_4542_);
v_res_4548_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4_spec__9___redArg(v_depth_boxed_4547_, v_keys_4543_, v_vals_4544_, v_i_4545_, v_entries_4546_);
lean_dec_ref(v_vals_4544_);
lean_dec_ref(v_keys_4543_);
return v_res_4548_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_x_4549_, lean_object* v_x_4550_, lean_object* v_x_4551_, lean_object* v_x_4552_, lean_object* v_x_4553_){
_start:
{
size_t v_x_46709__boxed_4554_; size_t v_x_46710__boxed_4555_; lean_object* v_res_4556_; 
v_x_46709__boxed_4554_ = lean_unbox_usize(v_x_4550_);
lean_dec(v_x_4550_);
v_x_46710__boxed_4555_ = lean_unbox_usize(v_x_4551_);
lean_dec(v_x_4551_);
v_res_4556_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4___redArg(v_x_4549_, v_x_46709__boxed_4554_, v_x_46710__boxed_4555_, v_x_4552_, v_x_4553_);
return v_res_4556_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0___redArg(lean_object* v_x_4557_, lean_object* v_x_4558_, lean_object* v_x_4559_){
_start:
{
uint64_t v___x_4560_; size_t v___x_4561_; size_t v___x_4562_; lean_object* v___x_4563_; 
v___x_4560_ = l_Lean_instHashableMVarId_hash(v_x_4558_);
v___x_4561_ = lean_uint64_to_usize(v___x_4560_);
v___x_4562_ = ((size_t)1ULL);
v___x_4563_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4___redArg(v_x_4557_, v___x_4561_, v___x_4562_, v_x_4558_, v_x_4559_);
return v___x_4563_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0___redArg(lean_object* v_mvarId_4564_, lean_object* v_val_4565_, lean_object* v___y_4566_){
_start:
{
lean_object* v___x_4568_; lean_object* v_mctx_4569_; lean_object* v_cache_4570_; lean_object* v_zetaDeltaFVarIds_4571_; lean_object* v_postponed_4572_; lean_object* v_diag_4573_; lean_object* v___x_4575_; uint8_t v_isShared_4576_; uint8_t v_isSharedCheck_4600_; 
v___x_4568_ = lean_st_ref_take(v___y_4566_);
v_mctx_4569_ = lean_ctor_get(v___x_4568_, 0);
v_cache_4570_ = lean_ctor_get(v___x_4568_, 1);
v_zetaDeltaFVarIds_4571_ = lean_ctor_get(v___x_4568_, 2);
v_postponed_4572_ = lean_ctor_get(v___x_4568_, 3);
v_diag_4573_ = lean_ctor_get(v___x_4568_, 4);
v_isSharedCheck_4600_ = !lean_is_exclusive(v___x_4568_);
if (v_isSharedCheck_4600_ == 0)
{
v___x_4575_ = v___x_4568_;
v_isShared_4576_ = v_isSharedCheck_4600_;
goto v_resetjp_4574_;
}
else
{
lean_inc(v_diag_4573_);
lean_inc(v_postponed_4572_);
lean_inc(v_zetaDeltaFVarIds_4571_);
lean_inc(v_cache_4570_);
lean_inc(v_mctx_4569_);
lean_dec(v___x_4568_);
v___x_4575_ = lean_box(0);
v_isShared_4576_ = v_isSharedCheck_4600_;
goto v_resetjp_4574_;
}
v_resetjp_4574_:
{
lean_object* v_depth_4577_; lean_object* v_levelAssignDepth_4578_; lean_object* v_mvarCounter_4579_; lean_object* v_lDepth_4580_; lean_object* v_decls_4581_; lean_object* v_userNames_4582_; lean_object* v_lAssignment_4583_; lean_object* v_eAssignment_4584_; lean_object* v_dAssignment_4585_; lean_object* v___x_4587_; uint8_t v_isShared_4588_; uint8_t v_isSharedCheck_4599_; 
v_depth_4577_ = lean_ctor_get(v_mctx_4569_, 0);
v_levelAssignDepth_4578_ = lean_ctor_get(v_mctx_4569_, 1);
v_mvarCounter_4579_ = lean_ctor_get(v_mctx_4569_, 2);
v_lDepth_4580_ = lean_ctor_get(v_mctx_4569_, 3);
v_decls_4581_ = lean_ctor_get(v_mctx_4569_, 4);
v_userNames_4582_ = lean_ctor_get(v_mctx_4569_, 5);
v_lAssignment_4583_ = lean_ctor_get(v_mctx_4569_, 6);
v_eAssignment_4584_ = lean_ctor_get(v_mctx_4569_, 7);
v_dAssignment_4585_ = lean_ctor_get(v_mctx_4569_, 8);
v_isSharedCheck_4599_ = !lean_is_exclusive(v_mctx_4569_);
if (v_isSharedCheck_4599_ == 0)
{
v___x_4587_ = v_mctx_4569_;
v_isShared_4588_ = v_isSharedCheck_4599_;
goto v_resetjp_4586_;
}
else
{
lean_inc(v_dAssignment_4585_);
lean_inc(v_eAssignment_4584_);
lean_inc(v_lAssignment_4583_);
lean_inc(v_userNames_4582_);
lean_inc(v_decls_4581_);
lean_inc(v_lDepth_4580_);
lean_inc(v_mvarCounter_4579_);
lean_inc(v_levelAssignDepth_4578_);
lean_inc(v_depth_4577_);
lean_dec(v_mctx_4569_);
v___x_4587_ = lean_box(0);
v_isShared_4588_ = v_isSharedCheck_4599_;
goto v_resetjp_4586_;
}
v_resetjp_4586_:
{
lean_object* v___x_4589_; lean_object* v___x_4591_; 
v___x_4589_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0___redArg(v_eAssignment_4584_, v_mvarId_4564_, v_val_4565_);
if (v_isShared_4588_ == 0)
{
lean_ctor_set(v___x_4587_, 7, v___x_4589_);
v___x_4591_ = v___x_4587_;
goto v_reusejp_4590_;
}
else
{
lean_object* v_reuseFailAlloc_4598_; 
v_reuseFailAlloc_4598_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4598_, 0, v_depth_4577_);
lean_ctor_set(v_reuseFailAlloc_4598_, 1, v_levelAssignDepth_4578_);
lean_ctor_set(v_reuseFailAlloc_4598_, 2, v_mvarCounter_4579_);
lean_ctor_set(v_reuseFailAlloc_4598_, 3, v_lDepth_4580_);
lean_ctor_set(v_reuseFailAlloc_4598_, 4, v_decls_4581_);
lean_ctor_set(v_reuseFailAlloc_4598_, 5, v_userNames_4582_);
lean_ctor_set(v_reuseFailAlloc_4598_, 6, v_lAssignment_4583_);
lean_ctor_set(v_reuseFailAlloc_4598_, 7, v___x_4589_);
lean_ctor_set(v_reuseFailAlloc_4598_, 8, v_dAssignment_4585_);
v___x_4591_ = v_reuseFailAlloc_4598_;
goto v_reusejp_4590_;
}
v_reusejp_4590_:
{
lean_object* v___x_4593_; 
if (v_isShared_4576_ == 0)
{
lean_ctor_set(v___x_4575_, 0, v___x_4591_);
v___x_4593_ = v___x_4575_;
goto v_reusejp_4592_;
}
else
{
lean_object* v_reuseFailAlloc_4597_; 
v_reuseFailAlloc_4597_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4597_, 0, v___x_4591_);
lean_ctor_set(v_reuseFailAlloc_4597_, 1, v_cache_4570_);
lean_ctor_set(v_reuseFailAlloc_4597_, 2, v_zetaDeltaFVarIds_4571_);
lean_ctor_set(v_reuseFailAlloc_4597_, 3, v_postponed_4572_);
lean_ctor_set(v_reuseFailAlloc_4597_, 4, v_diag_4573_);
v___x_4593_ = v_reuseFailAlloc_4597_;
goto v_reusejp_4592_;
}
v_reusejp_4592_:
{
lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; 
v___x_4594_ = lean_st_ref_set(v___y_4566_, v___x_4593_);
v___x_4595_ = lean_box(0);
v___x_4596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4596_, 0, v___x_4595_);
return v___x_4596_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0___redArg___boxed(lean_object* v_mvarId_4601_, lean_object* v_val_4602_, lean_object* v___y_4603_, lean_object* v___y_4604_){
_start:
{
lean_object* v_res_4605_; 
v_res_4605_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0___redArg(v_mvarId_4601_, v_val_4602_, v___y_4603_);
lean_dec(v___y_4603_);
return v_res_4605_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4(lean_object* v_a_4613_, lean_object* v___x_4614_, lean_object* v_as_4615_, size_t v_sz_4616_, size_t v_i_4617_, lean_object* v_b_4618_, lean_object* v___y_4619_, lean_object* v___y_4620_, lean_object* v___y_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_, lean_object* v___y_4624_){
_start:
{
lean_object* v_a_4627_; uint8_t v___x_4631_; 
v___x_4631_ = lean_usize_dec_lt(v_i_4617_, v_sz_4616_);
if (v___x_4631_ == 0)
{
lean_object* v___x_4632_; 
lean_dec(v___y_4624_);
lean_dec_ref(v___y_4623_);
lean_dec(v___y_4622_);
lean_dec_ref(v___y_4621_);
lean_dec(v___y_4620_);
lean_dec_ref(v___y_4619_);
lean_dec_ref(v___x_4614_);
lean_dec(v_a_4613_);
v___x_4632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4632_, 0, v_b_4618_);
return v___x_4632_;
}
else
{
lean_object* v_a_4633_; lean_object* v___x_4634_; 
v_a_4633_ = lean_array_uget_borrowed(v_as_4615_, v_i_4617_);
lean_inc_ref(v___y_4621_);
lean_inc(v_a_4633_);
v___x_4634_ = l_Lean_FVarId_getDecl___redArg(v_a_4633_, v___y_4621_, v___y_4623_, v___y_4624_);
if (lean_obj_tag(v___x_4634_) == 0)
{
lean_object* v_options_4635_; lean_object* v_a_4636_; lean_object* v_snd_4637_; lean_object* v___x_4639_; uint8_t v_isShared_4640_; uint8_t v_isSharedCheck_4838_; 
v_options_4635_ = lean_ctor_get(v___y_4623_, 2);
v_a_4636_ = lean_ctor_get(v___x_4634_, 0);
lean_inc(v_a_4636_);
lean_dec_ref(v___x_4634_);
v_snd_4637_ = lean_ctor_get(v_b_4618_, 1);
v_isSharedCheck_4838_ = !lean_is_exclusive(v_b_4618_);
if (v_isSharedCheck_4838_ == 0)
{
lean_object* v_unused_4839_; 
v_unused_4839_ = lean_ctor_get(v_b_4618_, 0);
lean_dec(v_unused_4839_);
v___x_4639_ = v_b_4618_;
v_isShared_4640_ = v_isSharedCheck_4838_;
goto v_resetjp_4638_;
}
else
{
lean_inc(v_snd_4637_);
lean_dec(v_b_4618_);
v___x_4639_ = lean_box(0);
v_isShared_4640_ = v_isSharedCheck_4838_;
goto v_resetjp_4638_;
}
v_resetjp_4638_:
{
uint8_t v_hasTrace_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; lean_object* v___y_4645_; 
v_hasTrace_4641_ = lean_ctor_get_uint8(v_options_4635_, sizeof(void*)*1);
v___x_4642_ = lean_box(0);
v___x_4643_ = l_Lean_LocalDecl_type(v_a_4636_);
if (v_hasTrace_4641_ == 0)
{
lean_object* v___x_4742_; 
lean_inc(v___y_4624_);
lean_inc_ref(v___y_4623_);
lean_inc(v___y_4622_);
lean_inc_ref(v___y_4621_);
lean_inc(v___y_4620_);
lean_inc_ref(v___y_4619_);
lean_inc_ref(v___x_4614_);
lean_inc_ref(v___x_4643_);
v___x_4742_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_4643_, v___x_4614_, v___y_4619_, v___y_4620_, v___y_4621_, v___y_4622_, v___y_4623_, v___y_4624_);
v___y_4645_ = v___x_4742_;
goto v___jp_4644_;
}
else
{
lean_object* v___x_4743_; lean_object* v___x_4744_; 
v___x_4743_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0));
v___x_4744_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__1___redArg(v___x_4743_, v___y_4623_);
if (lean_obj_tag(v___x_4744_) == 0)
{
lean_object* v_a_4745_; lean_object* v___f_4746_; lean_object* v___x_4747_; lean_object* v___y_4749_; lean_object* v___y_4750_; lean_object* v_a_4751_; lean_object* v___y_4765_; lean_object* v___y_4766_; lean_object* v_a_4767_; uint8_t v___x_4826_; 
v_a_4745_ = lean_ctor_get(v___x_4744_, 0);
lean_inc(v_a_4745_);
lean_dec_ref(v___x_4744_);
lean_inc_ref(v___x_4643_);
lean_inc(v_a_4636_);
v___f_4746_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___lam__0___boxed), 10, 2);
lean_closure_set(v___f_4746_, 0, v_a_4636_);
lean_closure_set(v___f_4746_, 1, v___x_4643_);
v___x_4747_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__1));
v___x_4826_ = lean_unbox(v_a_4745_);
if (v___x_4826_ == 0)
{
lean_object* v___x_4827_; uint8_t v___x_4828_; 
v___x_4827_ = l_Lean_trace_profiler;
v___x_4828_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2(v_options_4635_, v___x_4827_);
if (v___x_4828_ == 0)
{
lean_object* v___x_4829_; 
lean_dec_ref(v___f_4746_);
lean_dec(v_a_4745_);
lean_inc(v___y_4624_);
lean_inc_ref(v___y_4623_);
lean_inc(v___y_4622_);
lean_inc_ref(v___y_4621_);
lean_inc(v___y_4620_);
lean_inc_ref(v___y_4619_);
lean_inc_ref(v___x_4614_);
lean_inc_ref(v___x_4643_);
v___x_4829_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_4643_, v___x_4614_, v___y_4619_, v___y_4620_, v___y_4621_, v___y_4622_, v___y_4623_, v___y_4624_);
v___y_4645_ = v___x_4829_;
goto v___jp_4644_;
}
else
{
goto v___jp_4777_;
}
}
else
{
goto v___jp_4777_;
}
v___jp_4748_:
{
lean_object* v___x_4752_; double v___x_4753_; double v___x_4754_; double v___x_4755_; double v___x_4756_; double v___x_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; lean_object* v___x_4760_; lean_object* v___x_4761_; uint8_t v___x_4762_; lean_object* v___x_4763_; 
v___x_4752_ = lean_io_mono_nanos_now();
v___x_4753_ = lean_float_of_nat(v___y_4750_);
v___x_4754_ = lean_float_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4);
v___x_4755_ = lean_float_div(v___x_4753_, v___x_4754_);
v___x_4756_ = lean_float_of_nat(v___x_4752_);
v___x_4757_ = lean_float_div(v___x_4756_, v___x_4754_);
v___x_4758_ = lean_box_float(v___x_4755_);
v___x_4759_ = lean_box_float(v___x_4757_);
v___x_4760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4760_, 0, v___x_4758_);
lean_ctor_set(v___x_4760_, 1, v___x_4759_);
v___x_4761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4761_, 0, v_a_4751_);
lean_ctor_set(v___x_4761_, 1, v___x_4760_);
v___x_4762_ = lean_unbox(v_a_4745_);
lean_dec(v_a_4745_);
lean_inc(v___y_4624_);
lean_inc_ref(v___y_4623_);
lean_inc(v___y_4622_);
lean_inc_ref(v___y_4621_);
lean_inc(v___y_4620_);
lean_inc_ref(v___y_4619_);
v___x_4763_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3(v___x_4743_, v_hasTrace_4641_, v___x_4747_, v_options_4635_, v___x_4762_, v___y_4749_, v___f_4746_, v___x_4761_, v___y_4619_, v___y_4620_, v___y_4621_, v___y_4622_, v___y_4623_, v___y_4624_);
v___y_4645_ = v___x_4763_;
goto v___jp_4644_;
}
v___jp_4764_:
{
lean_object* v___x_4768_; double v___x_4769_; double v___x_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; uint8_t v___x_4775_; lean_object* v___x_4776_; 
v___x_4768_ = lean_io_get_num_heartbeats();
v___x_4769_ = lean_float_of_nat(v___y_4765_);
v___x_4770_ = lean_float_of_nat(v___x_4768_);
v___x_4771_ = lean_box_float(v___x_4769_);
v___x_4772_ = lean_box_float(v___x_4770_);
v___x_4773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4773_, 0, v___x_4771_);
lean_ctor_set(v___x_4773_, 1, v___x_4772_);
v___x_4774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4774_, 0, v_a_4767_);
lean_ctor_set(v___x_4774_, 1, v___x_4773_);
v___x_4775_ = lean_unbox(v_a_4745_);
lean_dec(v_a_4745_);
lean_inc(v___y_4624_);
lean_inc_ref(v___y_4623_);
lean_inc(v___y_4622_);
lean_inc_ref(v___y_4621_);
lean_inc(v___y_4620_);
lean_inc_ref(v___y_4619_);
v___x_4776_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3(v___x_4743_, v_hasTrace_4641_, v___x_4747_, v_options_4635_, v___x_4775_, v___y_4766_, v___f_4746_, v___x_4774_, v___y_4619_, v___y_4620_, v___y_4621_, v___y_4622_, v___y_4623_, v___y_4624_);
v___y_4645_ = v___x_4776_;
goto v___jp_4644_;
}
v___jp_4777_:
{
lean_object* v___x_4778_; 
v___x_4778_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2___redArg(v___y_4624_);
if (lean_obj_tag(v___x_4778_) == 0)
{
lean_object* v_a_4779_; lean_object* v___x_4780_; uint8_t v___x_4781_; 
v_a_4779_ = lean_ctor_get(v___x_4778_, 0);
lean_inc(v_a_4779_);
lean_dec_ref(v___x_4778_);
v___x_4780_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4781_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2(v_options_4635_, v___x_4780_);
if (v___x_4781_ == 0)
{
lean_object* v___x_4782_; lean_object* v___x_4783_; 
v___x_4782_ = lean_io_mono_nanos_now();
lean_inc(v___y_4624_);
lean_inc_ref(v___y_4623_);
lean_inc(v___y_4622_);
lean_inc_ref(v___y_4621_);
lean_inc(v___y_4620_);
lean_inc_ref(v___y_4619_);
lean_inc_ref(v___x_4614_);
lean_inc_ref(v___x_4643_);
v___x_4783_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_4643_, v___x_4614_, v___y_4619_, v___y_4620_, v___y_4621_, v___y_4622_, v___y_4623_, v___y_4624_);
if (lean_obj_tag(v___x_4783_) == 0)
{
lean_object* v_a_4784_; lean_object* v___x_4786_; uint8_t v_isShared_4787_; uint8_t v_isSharedCheck_4791_; 
v_a_4784_ = lean_ctor_get(v___x_4783_, 0);
v_isSharedCheck_4791_ = !lean_is_exclusive(v___x_4783_);
if (v_isSharedCheck_4791_ == 0)
{
v___x_4786_ = v___x_4783_;
v_isShared_4787_ = v_isSharedCheck_4791_;
goto v_resetjp_4785_;
}
else
{
lean_inc(v_a_4784_);
lean_dec(v___x_4783_);
v___x_4786_ = lean_box(0);
v_isShared_4787_ = v_isSharedCheck_4791_;
goto v_resetjp_4785_;
}
v_resetjp_4785_:
{
lean_object* v___x_4789_; 
if (v_isShared_4787_ == 0)
{
lean_ctor_set_tag(v___x_4786_, 1);
v___x_4789_ = v___x_4786_;
goto v_reusejp_4788_;
}
else
{
lean_object* v_reuseFailAlloc_4790_; 
v_reuseFailAlloc_4790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4790_, 0, v_a_4784_);
v___x_4789_ = v_reuseFailAlloc_4790_;
goto v_reusejp_4788_;
}
v_reusejp_4788_:
{
v___y_4749_ = v_a_4779_;
v___y_4750_ = v___x_4782_;
v_a_4751_ = v___x_4789_;
goto v___jp_4748_;
}
}
}
else
{
lean_object* v_a_4792_; lean_object* v___x_4794_; uint8_t v_isShared_4795_; uint8_t v_isSharedCheck_4799_; 
v_a_4792_ = lean_ctor_get(v___x_4783_, 0);
v_isSharedCheck_4799_ = !lean_is_exclusive(v___x_4783_);
if (v_isSharedCheck_4799_ == 0)
{
v___x_4794_ = v___x_4783_;
v_isShared_4795_ = v_isSharedCheck_4799_;
goto v_resetjp_4793_;
}
else
{
lean_inc(v_a_4792_);
lean_dec(v___x_4783_);
v___x_4794_ = lean_box(0);
v_isShared_4795_ = v_isSharedCheck_4799_;
goto v_resetjp_4793_;
}
v_resetjp_4793_:
{
lean_object* v___x_4797_; 
if (v_isShared_4795_ == 0)
{
lean_ctor_set_tag(v___x_4794_, 0);
v___x_4797_ = v___x_4794_;
goto v_reusejp_4796_;
}
else
{
lean_object* v_reuseFailAlloc_4798_; 
v_reuseFailAlloc_4798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4798_, 0, v_a_4792_);
v___x_4797_ = v_reuseFailAlloc_4798_;
goto v_reusejp_4796_;
}
v_reusejp_4796_:
{
v___y_4749_ = v_a_4779_;
v___y_4750_ = v___x_4782_;
v_a_4751_ = v___x_4797_;
goto v___jp_4748_;
}
}
}
}
else
{
lean_object* v___x_4800_; lean_object* v___x_4801_; 
v___x_4800_ = lean_io_get_num_heartbeats();
lean_inc(v___y_4624_);
lean_inc_ref(v___y_4623_);
lean_inc(v___y_4622_);
lean_inc_ref(v___y_4621_);
lean_inc(v___y_4620_);
lean_inc_ref(v___y_4619_);
lean_inc_ref(v___x_4614_);
lean_inc_ref(v___x_4643_);
v___x_4801_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_4643_, v___x_4614_, v___y_4619_, v___y_4620_, v___y_4621_, v___y_4622_, v___y_4623_, v___y_4624_);
if (lean_obj_tag(v___x_4801_) == 0)
{
lean_object* v_a_4802_; lean_object* v___x_4804_; uint8_t v_isShared_4805_; uint8_t v_isSharedCheck_4809_; 
v_a_4802_ = lean_ctor_get(v___x_4801_, 0);
v_isSharedCheck_4809_ = !lean_is_exclusive(v___x_4801_);
if (v_isSharedCheck_4809_ == 0)
{
v___x_4804_ = v___x_4801_;
v_isShared_4805_ = v_isSharedCheck_4809_;
goto v_resetjp_4803_;
}
else
{
lean_inc(v_a_4802_);
lean_dec(v___x_4801_);
v___x_4804_ = lean_box(0);
v_isShared_4805_ = v_isSharedCheck_4809_;
goto v_resetjp_4803_;
}
v_resetjp_4803_:
{
lean_object* v___x_4807_; 
if (v_isShared_4805_ == 0)
{
lean_ctor_set_tag(v___x_4804_, 1);
v___x_4807_ = v___x_4804_;
goto v_reusejp_4806_;
}
else
{
lean_object* v_reuseFailAlloc_4808_; 
v_reuseFailAlloc_4808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4808_, 0, v_a_4802_);
v___x_4807_ = v_reuseFailAlloc_4808_;
goto v_reusejp_4806_;
}
v_reusejp_4806_:
{
v___y_4765_ = v___x_4800_;
v___y_4766_ = v_a_4779_;
v_a_4767_ = v___x_4807_;
goto v___jp_4764_;
}
}
}
else
{
lean_object* v_a_4810_; lean_object* v___x_4812_; uint8_t v_isShared_4813_; uint8_t v_isSharedCheck_4817_; 
v_a_4810_ = lean_ctor_get(v___x_4801_, 0);
v_isSharedCheck_4817_ = !lean_is_exclusive(v___x_4801_);
if (v_isSharedCheck_4817_ == 0)
{
v___x_4812_ = v___x_4801_;
v_isShared_4813_ = v_isSharedCheck_4817_;
goto v_resetjp_4811_;
}
else
{
lean_inc(v_a_4810_);
lean_dec(v___x_4801_);
v___x_4812_ = lean_box(0);
v_isShared_4813_ = v_isSharedCheck_4817_;
goto v_resetjp_4811_;
}
v_resetjp_4811_:
{
lean_object* v___x_4815_; 
if (v_isShared_4813_ == 0)
{
lean_ctor_set_tag(v___x_4812_, 0);
v___x_4815_ = v___x_4812_;
goto v_reusejp_4814_;
}
else
{
lean_object* v_reuseFailAlloc_4816_; 
v_reuseFailAlloc_4816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4816_, 0, v_a_4810_);
v___x_4815_ = v_reuseFailAlloc_4816_;
goto v_reusejp_4814_;
}
v_reusejp_4814_:
{
v___y_4765_ = v___x_4800_;
v___y_4766_ = v_a_4779_;
v_a_4767_ = v___x_4815_;
goto v___jp_4764_;
}
}
}
}
}
else
{
lean_object* v_a_4818_; lean_object* v___x_4820_; uint8_t v_isShared_4821_; uint8_t v_isSharedCheck_4825_; 
lean_dec_ref(v___f_4746_);
lean_dec(v_a_4745_);
lean_dec_ref(v___x_4643_);
lean_del_object(v___x_4639_);
lean_dec(v_snd_4637_);
lean_dec(v_a_4636_);
lean_dec(v___y_4624_);
lean_dec_ref(v___y_4623_);
lean_dec(v___y_4622_);
lean_dec_ref(v___y_4621_);
lean_dec(v___y_4620_);
lean_dec_ref(v___y_4619_);
lean_dec_ref(v___x_4614_);
lean_dec(v_a_4613_);
v_a_4818_ = lean_ctor_get(v___x_4778_, 0);
v_isSharedCheck_4825_ = !lean_is_exclusive(v___x_4778_);
if (v_isSharedCheck_4825_ == 0)
{
v___x_4820_ = v___x_4778_;
v_isShared_4821_ = v_isSharedCheck_4825_;
goto v_resetjp_4819_;
}
else
{
lean_inc(v_a_4818_);
lean_dec(v___x_4778_);
v___x_4820_ = lean_box(0);
v_isShared_4821_ = v_isSharedCheck_4825_;
goto v_resetjp_4819_;
}
v_resetjp_4819_:
{
lean_object* v___x_4823_; 
if (v_isShared_4821_ == 0)
{
v___x_4823_ = v___x_4820_;
goto v_reusejp_4822_;
}
else
{
lean_object* v_reuseFailAlloc_4824_; 
v_reuseFailAlloc_4824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4824_, 0, v_a_4818_);
v___x_4823_ = v_reuseFailAlloc_4824_;
goto v_reusejp_4822_;
}
v_reusejp_4822_:
{
return v___x_4823_;
}
}
}
}
}
else
{
lean_object* v_a_4830_; lean_object* v___x_4832_; uint8_t v_isShared_4833_; uint8_t v_isSharedCheck_4837_; 
lean_dec_ref(v___x_4643_);
lean_del_object(v___x_4639_);
lean_dec(v_snd_4637_);
lean_dec(v_a_4636_);
lean_dec(v___y_4624_);
lean_dec_ref(v___y_4623_);
lean_dec(v___y_4622_);
lean_dec_ref(v___y_4621_);
lean_dec(v___y_4620_);
lean_dec_ref(v___y_4619_);
lean_dec_ref(v___x_4614_);
lean_dec(v_a_4613_);
v_a_4830_ = lean_ctor_get(v___x_4744_, 0);
v_isSharedCheck_4837_ = !lean_is_exclusive(v___x_4744_);
if (v_isSharedCheck_4837_ == 0)
{
v___x_4832_ = v___x_4744_;
v_isShared_4833_ = v_isSharedCheck_4837_;
goto v_resetjp_4831_;
}
else
{
lean_inc(v_a_4830_);
lean_dec(v___x_4744_);
v___x_4832_ = lean_box(0);
v_isShared_4833_ = v_isSharedCheck_4837_;
goto v_resetjp_4831_;
}
v_resetjp_4831_:
{
lean_object* v___x_4835_; 
if (v_isShared_4833_ == 0)
{
v___x_4835_ = v___x_4832_;
goto v_reusejp_4834_;
}
else
{
lean_object* v_reuseFailAlloc_4836_; 
v_reuseFailAlloc_4836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4836_, 0, v_a_4830_);
v___x_4835_ = v_reuseFailAlloc_4836_;
goto v_reusejp_4834_;
}
v_reusejp_4834_:
{
return v___x_4835_;
}
}
}
}
v___jp_4644_:
{
if (lean_obj_tag(v___y_4645_) == 0)
{
lean_object* v_a_4646_; 
v_a_4646_ = lean_ctor_get(v___y_4645_, 0);
lean_inc(v_a_4646_);
lean_dec_ref(v___y_4645_);
if (lean_obj_tag(v_a_4646_) == 0)
{
lean_object* v___x_4648_; 
lean_dec_ref(v_a_4646_);
lean_dec_ref(v___x_4643_);
lean_dec(v_a_4636_);
if (v_isShared_4640_ == 0)
{
lean_ctor_set(v___x_4639_, 0, v___x_4642_);
v___x_4648_ = v___x_4639_;
goto v_reusejp_4647_;
}
else
{
lean_object* v_reuseFailAlloc_4649_; 
v_reuseFailAlloc_4649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4649_, 0, v___x_4642_);
lean_ctor_set(v_reuseFailAlloc_4649_, 1, v_snd_4637_);
v___x_4648_ = v_reuseFailAlloc_4649_;
goto v_reusejp_4647_;
}
v_reusejp_4647_:
{
v_a_4627_ = v___x_4648_;
goto v___jp_4626_;
}
}
else
{
lean_object* v_e_x27_4650_; lean_object* v_proof_4651_; uint8_t v___x_4652_; 
v_e_x27_4650_ = lean_ctor_get(v_a_4646_, 0);
lean_inc_ref(v_e_x27_4650_);
v_proof_4651_ = lean_ctor_get(v_a_4646_, 1);
lean_inc_ref(v_proof_4651_);
lean_dec_ref(v_a_4646_);
lean_inc_ref(v_e_x27_4650_);
v___x_4652_ = l_Lean_Expr_isFalse(v_e_x27_4650_);
if (v___x_4652_ == 0)
{
lean_object* v___x_4653_; 
lean_inc(v___y_4624_);
lean_inc_ref(v___y_4623_);
lean_inc(v___y_4622_);
lean_inc_ref(v___y_4621_);
lean_inc_ref(v___x_4643_);
v___x_4653_ = l_Lean_Meta_getLevel(v___x_4643_, v___y_4621_, v___y_4622_, v___y_4623_, v___y_4624_);
if (lean_obj_tag(v___x_4653_) == 0)
{
lean_object* v_a_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; uint8_t v___x_4662_; uint8_t v___x_4663_; lean_object* v___x_4664_; lean_object* v___x_4665_; lean_object* v___x_4667_; 
v_a_4654_ = lean_ctor_get(v___x_4653_, 0);
lean_inc(v_a_4654_);
lean_dec_ref(v___x_4653_);
v___x_4655_ = l_Lean_LocalDecl_userName(v_a_4636_);
lean_dec(v_a_4636_);
v___x_4656_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___closed__2));
v___x_4657_ = lean_box(0);
v___x_4658_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4658_, 0, v_a_4654_);
lean_ctor_set(v___x_4658_, 1, v___x_4657_);
v___x_4659_ = l_Lean_mkConst(v___x_4656_, v___x_4658_);
lean_inc(v_a_4633_);
v___x_4660_ = l_Lean_mkFVar(v_a_4633_);
lean_inc_ref(v_e_x27_4650_);
v___x_4661_ = l_Lean_mkApp4(v___x_4659_, v___x_4643_, v_e_x27_4650_, v_proof_4651_, v___x_4660_);
v___x_4662_ = 0;
v___x_4663_ = 0;
v___x_4664_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_4664_, 0, v___x_4655_);
lean_ctor_set(v___x_4664_, 1, v_e_x27_4650_);
lean_ctor_set(v___x_4664_, 2, v___x_4661_);
lean_ctor_set_uint8(v___x_4664_, sizeof(void*)*3, v___x_4662_);
lean_ctor_set_uint8(v___x_4664_, sizeof(void*)*3 + 1, v___x_4663_);
v___x_4665_ = lean_array_push(v_snd_4637_, v___x_4664_);
if (v_isShared_4640_ == 0)
{
lean_ctor_set(v___x_4639_, 1, v___x_4665_);
lean_ctor_set(v___x_4639_, 0, v___x_4642_);
v___x_4667_ = v___x_4639_;
goto v_reusejp_4666_;
}
else
{
lean_object* v_reuseFailAlloc_4668_; 
v_reuseFailAlloc_4668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4668_, 0, v___x_4642_);
lean_ctor_set(v_reuseFailAlloc_4668_, 1, v___x_4665_);
v___x_4667_ = v_reuseFailAlloc_4668_;
goto v_reusejp_4666_;
}
v_reusejp_4666_:
{
v_a_4627_ = v___x_4667_;
goto v___jp_4626_;
}
}
else
{
lean_object* v_a_4669_; lean_object* v___x_4671_; uint8_t v_isShared_4672_; uint8_t v_isSharedCheck_4676_; 
lean_dec_ref(v_proof_4651_);
lean_dec_ref(v_e_x27_4650_);
lean_dec_ref(v___x_4643_);
lean_del_object(v___x_4639_);
lean_dec(v_snd_4637_);
lean_dec(v_a_4636_);
lean_dec(v___y_4624_);
lean_dec_ref(v___y_4623_);
lean_dec(v___y_4622_);
lean_dec_ref(v___y_4621_);
lean_dec(v___y_4620_);
lean_dec_ref(v___y_4619_);
lean_dec_ref(v___x_4614_);
lean_dec(v_a_4613_);
v_a_4669_ = lean_ctor_get(v___x_4653_, 0);
v_isSharedCheck_4676_ = !lean_is_exclusive(v___x_4653_);
if (v_isSharedCheck_4676_ == 0)
{
v___x_4671_ = v___x_4653_;
v_isShared_4672_ = v_isSharedCheck_4676_;
goto v_resetjp_4670_;
}
else
{
lean_inc(v_a_4669_);
lean_dec(v___x_4653_);
v___x_4671_ = lean_box(0);
v_isShared_4672_ = v_isSharedCheck_4676_;
goto v_resetjp_4670_;
}
v_resetjp_4670_:
{
lean_object* v___x_4674_; 
if (v_isShared_4672_ == 0)
{
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
}
else
{
lean_object* v___x_4677_; 
lean_dec(v_a_4636_);
lean_dec(v___y_4620_);
lean_dec_ref(v___y_4619_);
lean_dec_ref(v___x_4614_);
lean_inc(v___y_4624_);
lean_inc_ref(v___y_4623_);
lean_inc(v___y_4622_);
lean_inc_ref(v___y_4621_);
lean_inc_ref(v___x_4643_);
v___x_4677_ = l_Lean_Meta_getLevel(v___x_4643_, v___y_4621_, v___y_4622_, v___y_4623_, v___y_4624_);
if (lean_obj_tag(v___x_4677_) == 0)
{
lean_object* v_a_4678_; lean_object* v___x_4679_; 
v_a_4678_ = lean_ctor_get(v___x_4677_, 0);
lean_inc(v_a_4678_);
lean_dec_ref(v___x_4677_);
lean_inc(v_a_4613_);
v___x_4679_ = l_Lean_MVarId_getType(v_a_4613_, v___y_4621_, v___y_4622_, v___y_4623_, v___y_4624_);
if (lean_obj_tag(v___x_4679_) == 0)
{
lean_object* v_a_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; 
v_a_4680_ = lean_ctor_get(v___x_4679_, 0);
lean_inc(v_a_4680_);
lean_dec_ref(v___x_4679_);
v___x_4681_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___closed__2));
v___x_4682_ = lean_box(0);
v___x_4683_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4683_, 0, v_a_4678_);
lean_ctor_set(v___x_4683_, 1, v___x_4682_);
v___x_4684_ = l_Lean_mkConst(v___x_4681_, v___x_4683_);
lean_inc(v_a_4633_);
v___x_4685_ = l_Lean_mkFVar(v_a_4633_);
v___x_4686_ = l_Lean_mkApp4(v___x_4684_, v___x_4643_, v_e_x27_4650_, v_proof_4651_, v___x_4685_);
lean_inc(v___y_4622_);
v___x_4687_ = l_Lean_Meta_mkFalseElim(v_a_4680_, v___x_4686_, v___y_4621_, v___y_4622_, v___y_4623_, v___y_4624_);
if (lean_obj_tag(v___x_4687_) == 0)
{
lean_object* v_a_4688_; lean_object* v___x_4689_; 
v_a_4688_ = lean_ctor_get(v___x_4687_, 0);
lean_inc(v_a_4688_);
lean_dec_ref(v___x_4687_);
v___x_4689_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0___redArg(v_a_4613_, v_a_4688_, v___y_4622_);
lean_dec(v___y_4622_);
if (lean_obj_tag(v___x_4689_) == 0)
{
lean_object* v___x_4691_; uint8_t v_isShared_4692_; uint8_t v_isSharedCheck_4700_; 
v_isSharedCheck_4700_ = !lean_is_exclusive(v___x_4689_);
if (v_isSharedCheck_4700_ == 0)
{
lean_object* v_unused_4701_; 
v_unused_4701_ = lean_ctor_get(v___x_4689_, 0);
lean_dec(v_unused_4701_);
v___x_4691_ = v___x_4689_;
v_isShared_4692_ = v_isSharedCheck_4700_;
goto v_resetjp_4690_;
}
else
{
lean_dec(v___x_4689_);
v___x_4691_ = lean_box(0);
v_isShared_4692_ = v_isSharedCheck_4700_;
goto v_resetjp_4690_;
}
v_resetjp_4690_:
{
lean_object* v___x_4693_; lean_object* v___x_4695_; 
v___x_4693_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___closed__3));
if (v_isShared_4640_ == 0)
{
lean_ctor_set(v___x_4639_, 0, v___x_4693_);
v___x_4695_ = v___x_4639_;
goto v_reusejp_4694_;
}
else
{
lean_object* v_reuseFailAlloc_4699_; 
v_reuseFailAlloc_4699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4699_, 0, v___x_4693_);
lean_ctor_set(v_reuseFailAlloc_4699_, 1, v_snd_4637_);
v___x_4695_ = v_reuseFailAlloc_4699_;
goto v_reusejp_4694_;
}
v_reusejp_4694_:
{
lean_object* v___x_4697_; 
if (v_isShared_4692_ == 0)
{
lean_ctor_set(v___x_4691_, 0, v___x_4695_);
v___x_4697_ = v___x_4691_;
goto v_reusejp_4696_;
}
else
{
lean_object* v_reuseFailAlloc_4698_; 
v_reuseFailAlloc_4698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4698_, 0, v___x_4695_);
v___x_4697_ = v_reuseFailAlloc_4698_;
goto v_reusejp_4696_;
}
v_reusejp_4696_:
{
return v___x_4697_;
}
}
}
}
else
{
lean_object* v_a_4702_; lean_object* v___x_4704_; uint8_t v_isShared_4705_; uint8_t v_isSharedCheck_4709_; 
lean_del_object(v___x_4639_);
lean_dec(v_snd_4637_);
v_a_4702_ = lean_ctor_get(v___x_4689_, 0);
v_isSharedCheck_4709_ = !lean_is_exclusive(v___x_4689_);
if (v_isSharedCheck_4709_ == 0)
{
v___x_4704_ = v___x_4689_;
v_isShared_4705_ = v_isSharedCheck_4709_;
goto v_resetjp_4703_;
}
else
{
lean_inc(v_a_4702_);
lean_dec(v___x_4689_);
v___x_4704_ = lean_box(0);
v_isShared_4705_ = v_isSharedCheck_4709_;
goto v_resetjp_4703_;
}
v_resetjp_4703_:
{
lean_object* v___x_4707_; 
if (v_isShared_4705_ == 0)
{
v___x_4707_ = v___x_4704_;
goto v_reusejp_4706_;
}
else
{
lean_object* v_reuseFailAlloc_4708_; 
v_reuseFailAlloc_4708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4708_, 0, v_a_4702_);
v___x_4707_ = v_reuseFailAlloc_4708_;
goto v_reusejp_4706_;
}
v_reusejp_4706_:
{
return v___x_4707_;
}
}
}
}
else
{
lean_object* v_a_4710_; lean_object* v___x_4712_; uint8_t v_isShared_4713_; uint8_t v_isSharedCheck_4717_; 
lean_del_object(v___x_4639_);
lean_dec(v_snd_4637_);
lean_dec(v___y_4622_);
lean_dec(v_a_4613_);
v_a_4710_ = lean_ctor_get(v___x_4687_, 0);
v_isSharedCheck_4717_ = !lean_is_exclusive(v___x_4687_);
if (v_isSharedCheck_4717_ == 0)
{
v___x_4712_ = v___x_4687_;
v_isShared_4713_ = v_isSharedCheck_4717_;
goto v_resetjp_4711_;
}
else
{
lean_inc(v_a_4710_);
lean_dec(v___x_4687_);
v___x_4712_ = lean_box(0);
v_isShared_4713_ = v_isSharedCheck_4717_;
goto v_resetjp_4711_;
}
v_resetjp_4711_:
{
lean_object* v___x_4715_; 
if (v_isShared_4713_ == 0)
{
v___x_4715_ = v___x_4712_;
goto v_reusejp_4714_;
}
else
{
lean_object* v_reuseFailAlloc_4716_; 
v_reuseFailAlloc_4716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4716_, 0, v_a_4710_);
v___x_4715_ = v_reuseFailAlloc_4716_;
goto v_reusejp_4714_;
}
v_reusejp_4714_:
{
return v___x_4715_;
}
}
}
}
else
{
lean_object* v_a_4718_; lean_object* v___x_4720_; uint8_t v_isShared_4721_; uint8_t v_isSharedCheck_4725_; 
lean_dec(v_a_4678_);
lean_dec_ref(v_proof_4651_);
lean_dec_ref(v_e_x27_4650_);
lean_dec_ref(v___x_4643_);
lean_del_object(v___x_4639_);
lean_dec(v_snd_4637_);
lean_dec(v___y_4624_);
lean_dec_ref(v___y_4623_);
lean_dec(v___y_4622_);
lean_dec_ref(v___y_4621_);
lean_dec(v_a_4613_);
v_a_4718_ = lean_ctor_get(v___x_4679_, 0);
v_isSharedCheck_4725_ = !lean_is_exclusive(v___x_4679_);
if (v_isSharedCheck_4725_ == 0)
{
v___x_4720_ = v___x_4679_;
v_isShared_4721_ = v_isSharedCheck_4725_;
goto v_resetjp_4719_;
}
else
{
lean_inc(v_a_4718_);
lean_dec(v___x_4679_);
v___x_4720_ = lean_box(0);
v_isShared_4721_ = v_isSharedCheck_4725_;
goto v_resetjp_4719_;
}
v_resetjp_4719_:
{
lean_object* v___x_4723_; 
if (v_isShared_4721_ == 0)
{
v___x_4723_ = v___x_4720_;
goto v_reusejp_4722_;
}
else
{
lean_object* v_reuseFailAlloc_4724_; 
v_reuseFailAlloc_4724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4724_, 0, v_a_4718_);
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
else
{
lean_object* v_a_4726_; lean_object* v___x_4728_; uint8_t v_isShared_4729_; uint8_t v_isSharedCheck_4733_; 
lean_dec_ref(v_proof_4651_);
lean_dec_ref(v_e_x27_4650_);
lean_dec_ref(v___x_4643_);
lean_del_object(v___x_4639_);
lean_dec(v_snd_4637_);
lean_dec(v___y_4624_);
lean_dec_ref(v___y_4623_);
lean_dec(v___y_4622_);
lean_dec_ref(v___y_4621_);
lean_dec(v_a_4613_);
v_a_4726_ = lean_ctor_get(v___x_4677_, 0);
v_isSharedCheck_4733_ = !lean_is_exclusive(v___x_4677_);
if (v_isSharedCheck_4733_ == 0)
{
v___x_4728_ = v___x_4677_;
v_isShared_4729_ = v_isSharedCheck_4733_;
goto v_resetjp_4727_;
}
else
{
lean_inc(v_a_4726_);
lean_dec(v___x_4677_);
v___x_4728_ = lean_box(0);
v_isShared_4729_ = v_isSharedCheck_4733_;
goto v_resetjp_4727_;
}
v_resetjp_4727_:
{
lean_object* v___x_4731_; 
if (v_isShared_4729_ == 0)
{
v___x_4731_ = v___x_4728_;
goto v_reusejp_4730_;
}
else
{
lean_object* v_reuseFailAlloc_4732_; 
v_reuseFailAlloc_4732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4732_, 0, v_a_4726_);
v___x_4731_ = v_reuseFailAlloc_4732_;
goto v_reusejp_4730_;
}
v_reusejp_4730_:
{
return v___x_4731_;
}
}
}
}
}
}
else
{
lean_object* v_a_4734_; lean_object* v___x_4736_; uint8_t v_isShared_4737_; uint8_t v_isSharedCheck_4741_; 
lean_dec_ref(v___x_4643_);
lean_del_object(v___x_4639_);
lean_dec(v_snd_4637_);
lean_dec(v_a_4636_);
lean_dec(v___y_4624_);
lean_dec_ref(v___y_4623_);
lean_dec(v___y_4622_);
lean_dec_ref(v___y_4621_);
lean_dec(v___y_4620_);
lean_dec_ref(v___y_4619_);
lean_dec_ref(v___x_4614_);
lean_dec(v_a_4613_);
v_a_4734_ = lean_ctor_get(v___y_4645_, 0);
v_isSharedCheck_4741_ = !lean_is_exclusive(v___y_4645_);
if (v_isSharedCheck_4741_ == 0)
{
v___x_4736_ = v___y_4645_;
v_isShared_4737_ = v_isSharedCheck_4741_;
goto v_resetjp_4735_;
}
else
{
lean_inc(v_a_4734_);
lean_dec(v___y_4645_);
v___x_4736_ = lean_box(0);
v_isShared_4737_ = v_isSharedCheck_4741_;
goto v_resetjp_4735_;
}
v_resetjp_4735_:
{
lean_object* v___x_4739_; 
if (v_isShared_4737_ == 0)
{
v___x_4739_ = v___x_4736_;
goto v_reusejp_4738_;
}
else
{
lean_object* v_reuseFailAlloc_4740_; 
v_reuseFailAlloc_4740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4740_, 0, v_a_4734_);
v___x_4739_ = v_reuseFailAlloc_4740_;
goto v_reusejp_4738_;
}
v_reusejp_4738_:
{
return v___x_4739_;
}
}
}
}
}
}
else
{
lean_object* v_a_4840_; lean_object* v___x_4842_; uint8_t v_isShared_4843_; uint8_t v_isSharedCheck_4847_; 
lean_dec(v___y_4624_);
lean_dec_ref(v___y_4623_);
lean_dec(v___y_4622_);
lean_dec_ref(v___y_4621_);
lean_dec(v___y_4620_);
lean_dec_ref(v___y_4619_);
lean_dec_ref(v_b_4618_);
lean_dec_ref(v___x_4614_);
lean_dec(v_a_4613_);
v_a_4840_ = lean_ctor_get(v___x_4634_, 0);
v_isSharedCheck_4847_ = !lean_is_exclusive(v___x_4634_);
if (v_isSharedCheck_4847_ == 0)
{
v___x_4842_ = v___x_4634_;
v_isShared_4843_ = v_isSharedCheck_4847_;
goto v_resetjp_4841_;
}
else
{
lean_inc(v_a_4840_);
lean_dec(v___x_4634_);
v___x_4842_ = lean_box(0);
v_isShared_4843_ = v_isSharedCheck_4847_;
goto v_resetjp_4841_;
}
v_resetjp_4841_:
{
lean_object* v___x_4845_; 
if (v_isShared_4843_ == 0)
{
v___x_4845_ = v___x_4842_;
goto v_reusejp_4844_;
}
else
{
lean_object* v_reuseFailAlloc_4846_; 
v_reuseFailAlloc_4846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4846_, 0, v_a_4840_);
v___x_4845_ = v_reuseFailAlloc_4846_;
goto v_reusejp_4844_;
}
v_reusejp_4844_:
{
return v___x_4845_;
}
}
}
}
v___jp_4626_:
{
size_t v___x_4628_; size_t v___x_4629_; 
v___x_4628_ = ((size_t)1ULL);
v___x_4629_ = lean_usize_add(v_i_4617_, v___x_4628_);
v_i_4617_ = v___x_4629_;
v_b_4618_ = v_a_4627_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4___boxed(lean_object* v_a_4848_, lean_object* v___x_4849_, lean_object* v_as_4850_, lean_object* v_sz_4851_, lean_object* v_i_4852_, lean_object* v_b_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_){
_start:
{
size_t v_sz_boxed_4861_; size_t v_i_boxed_4862_; lean_object* v_res_4863_; 
v_sz_boxed_4861_ = lean_unbox_usize(v_sz_4851_);
lean_dec(v_sz_4851_);
v_i_boxed_4862_ = lean_unbox_usize(v_i_4852_);
lean_dec(v_i_4852_);
v_res_4863_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4(v_a_4848_, v___x_4849_, v_as_4850_, v_sz_boxed_4861_, v_i_boxed_4862_, v_b_4853_, v___y_4854_, v___y_4855_, v___y_4856_, v___y_4857_, v___y_4858_, v___y_4859_);
lean_dec_ref(v_as_4850_);
return v_res_4863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__1(lean_object* v_a_4864_, lean_object* v___x_4865_, lean_object* v_fvarIdsToSimp_4866_, size_t v_sz_4867_, size_t v___x_4868_, lean_object* v___x_4869_, uint8_t v_simplifyTarget_4870_, lean_object* v___y_4871_, lean_object* v___y_4872_, lean_object* v___y_4873_, lean_object* v___y_4874_, lean_object* v___y_4875_, lean_object* v___y_4876_){
_start:
{
lean_object* v___y_4879_; lean_object* v___y_4880_; lean_object* v___y_4881_; lean_object* v___y_4882_; lean_object* v___y_4883_; uint8_t v___y_4884_; lean_object* v___x_4904_; 
lean_inc(v___y_4876_);
lean_inc_ref(v___y_4875_);
lean_inc(v___y_4874_);
lean_inc_ref(v___y_4873_);
lean_inc(v___y_4872_);
lean_inc_ref(v___y_4871_);
lean_inc_ref(v___x_4865_);
lean_inc(v_a_4864_);
v___x_4904_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__4(v_a_4864_, v___x_4865_, v_fvarIdsToSimp_4866_, v_sz_4867_, v___x_4868_, v___x_4869_, v___y_4871_, v___y_4872_, v___y_4873_, v___y_4874_, v___y_4875_, v___y_4876_);
if (lean_obj_tag(v___x_4904_) == 0)
{
lean_object* v_a_4905_; lean_object* v___x_4907_; uint8_t v_isShared_4908_; uint8_t v_isSharedCheck_5109_; 
v_a_4905_ = lean_ctor_get(v___x_4904_, 0);
v_isSharedCheck_5109_ = !lean_is_exclusive(v___x_4904_);
if (v_isSharedCheck_5109_ == 0)
{
v___x_4907_ = v___x_4904_;
v_isShared_4908_ = v_isSharedCheck_5109_;
goto v_resetjp_4906_;
}
else
{
lean_inc(v_a_4905_);
lean_dec(v___x_4904_);
v___x_4907_ = lean_box(0);
v_isShared_4908_ = v_isSharedCheck_5109_;
goto v_resetjp_4906_;
}
v_resetjp_4906_:
{
lean_object* v_fst_4909_; lean_object* v_snd_4910_; lean_object* v___x_4912_; uint8_t v_isShared_4913_; uint8_t v_isSharedCheck_5108_; 
v_fst_4909_ = lean_ctor_get(v_a_4905_, 0);
v_snd_4910_ = lean_ctor_get(v_a_4905_, 1);
v_isSharedCheck_5108_ = !lean_is_exclusive(v_a_4905_);
if (v_isSharedCheck_5108_ == 0)
{
v___x_4912_ = v_a_4905_;
v_isShared_4913_ = v_isSharedCheck_5108_;
goto v_resetjp_4911_;
}
else
{
lean_inc(v_snd_4910_);
lean_inc(v_fst_4909_);
lean_dec(v_a_4905_);
v___x_4912_ = lean_box(0);
v_isShared_4913_ = v_isSharedCheck_5108_;
goto v_resetjp_4911_;
}
v_resetjp_4911_:
{
lean_object* v_mvarIdNew_4915_; lean_object* v___y_4916_; lean_object* v___y_4917_; lean_object* v___y_4918_; lean_object* v___y_4919_; lean_object* v___y_4966_; 
if (lean_obj_tag(v_fst_4909_) == 0)
{
lean_del_object(v___x_4907_);
if (v_simplifyTarget_4870_ == 0)
{
lean_del_object(v___x_4912_);
lean_dec(v___y_4872_);
lean_dec_ref(v___y_4871_);
lean_dec_ref(v___x_4865_);
v_mvarIdNew_4915_ = v_a_4864_;
v___y_4916_ = v___y_4873_;
v___y_4917_ = v___y_4874_;
v___y_4918_ = v___y_4875_;
v___y_4919_ = v___y_4876_;
goto v___jp_4914_;
}
else
{
lean_object* v___x_5009_; 
lean_inc(v_a_4864_);
v___x_5009_ = l_Lean_MVarId_getType(v_a_4864_, v___y_4873_, v___y_4874_, v___y_4875_, v___y_4876_);
if (lean_obj_tag(v___x_5009_) == 0)
{
lean_object* v_options_5010_; uint8_t v_hasTrace_5011_; 
v_options_5010_ = lean_ctor_get(v___y_4875_, 2);
v_hasTrace_5011_ = lean_ctor_get_uint8(v_options_5010_, sizeof(void*)*1);
if (v_hasTrace_5011_ == 0)
{
lean_object* v_a_5012_; lean_object* v___x_5013_; 
lean_del_object(v___x_4912_);
v_a_5012_ = lean_ctor_get(v___x_5009_, 0);
lean_inc(v_a_5012_);
lean_dec_ref(v___x_5009_);
lean_inc(v___y_4876_);
lean_inc_ref(v___y_4875_);
lean_inc(v___y_4874_);
lean_inc_ref(v___y_4873_);
v___x_5013_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v_a_5012_, v___x_4865_, v___y_4871_, v___y_4872_, v___y_4873_, v___y_4874_, v___y_4875_, v___y_4876_);
v___y_4966_ = v___x_5013_;
goto v___jp_4965_;
}
else
{
lean_object* v_a_5014_; lean_object* v___x_5015_; lean_object* v___x_5016_; lean_object* v_a_5017_; lean_object* v___f_5018_; lean_object* v___x_5019_; lean_object* v___y_5021_; lean_object* v___y_5022_; lean_object* v_a_5023_; lean_object* v___y_5039_; lean_object* v___y_5040_; lean_object* v_a_5041_; uint8_t v___x_5092_; 
v_a_5014_ = lean_ctor_get(v___x_5009_, 0);
lean_inc(v_a_5014_);
lean_dec_ref(v___x_5009_);
v___x_5015_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0));
v___x_5016_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__1___redArg(v___x_5015_, v___y_4875_);
v_a_5017_ = lean_ctor_get(v___x_5016_, 0);
lean_inc(v_a_5017_);
lean_dec_ref(v___x_5016_);
lean_inc(v_a_5014_);
v___f_5018_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___boxed), 9, 1);
lean_closure_set(v___f_5018_, 0, v_a_5014_);
v___x_5019_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__1));
v___x_5092_ = lean_unbox(v_a_5017_);
if (v___x_5092_ == 0)
{
lean_object* v___x_5093_; uint8_t v___x_5094_; 
v___x_5093_ = l_Lean_trace_profiler;
v___x_5094_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2(v_options_5010_, v___x_5093_);
if (v___x_5094_ == 0)
{
lean_object* v___x_5095_; 
lean_dec_ref(v___f_5018_);
lean_dec(v_a_5017_);
lean_del_object(v___x_4912_);
lean_inc(v___y_4876_);
lean_inc_ref(v___y_4875_);
lean_inc(v___y_4874_);
lean_inc_ref(v___y_4873_);
v___x_5095_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v_a_5014_, v___x_4865_, v___y_4871_, v___y_4872_, v___y_4873_, v___y_4874_, v___y_4875_, v___y_4876_);
v___y_4966_ = v___x_5095_;
goto v___jp_4965_;
}
else
{
goto v___jp_5051_;
}
}
else
{
goto v___jp_5051_;
}
v___jp_5020_:
{
lean_object* v___x_5024_; double v___x_5025_; double v___x_5026_; double v___x_5027_; double v___x_5028_; double v___x_5029_; lean_object* v___x_5030_; lean_object* v___x_5031_; lean_object* v___x_5033_; 
v___x_5024_ = lean_io_mono_nanos_now();
v___x_5025_ = lean_float_of_nat(v___y_5022_);
v___x_5026_ = lean_float_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4);
v___x_5027_ = lean_float_div(v___x_5025_, v___x_5026_);
v___x_5028_ = lean_float_of_nat(v___x_5024_);
v___x_5029_ = lean_float_div(v___x_5028_, v___x_5026_);
v___x_5030_ = lean_box_float(v___x_5027_);
v___x_5031_ = lean_box_float(v___x_5029_);
if (v_isShared_4913_ == 0)
{
lean_ctor_set(v___x_4912_, 1, v___x_5031_);
lean_ctor_set(v___x_4912_, 0, v___x_5030_);
v___x_5033_ = v___x_4912_;
goto v_reusejp_5032_;
}
else
{
lean_object* v_reuseFailAlloc_5037_; 
v_reuseFailAlloc_5037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5037_, 0, v___x_5030_);
lean_ctor_set(v_reuseFailAlloc_5037_, 1, v___x_5031_);
v___x_5033_ = v_reuseFailAlloc_5037_;
goto v_reusejp_5032_;
}
v_reusejp_5032_:
{
lean_object* v___x_5034_; uint8_t v___x_5035_; lean_object* v___x_5036_; 
v___x_5034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5034_, 0, v_a_5023_);
lean_ctor_set(v___x_5034_, 1, v___x_5033_);
v___x_5035_ = lean_unbox(v_a_5017_);
lean_dec(v_a_5017_);
lean_inc(v___y_4876_);
lean_inc_ref(v___y_4875_);
lean_inc(v___y_4874_);
lean_inc_ref(v___y_4873_);
v___x_5036_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3(v___x_5015_, v_hasTrace_5011_, v___x_5019_, v_options_5010_, v___x_5035_, v___y_5021_, v___f_5018_, v___x_5034_, v___y_4871_, v___y_4872_, v___y_4873_, v___y_4874_, v___y_4875_, v___y_4876_);
v___y_4966_ = v___x_5036_;
goto v___jp_4965_;
}
}
v___jp_5038_:
{
lean_object* v___x_5042_; double v___x_5043_; double v___x_5044_; lean_object* v___x_5045_; lean_object* v___x_5046_; lean_object* v___x_5047_; lean_object* v___x_5048_; uint8_t v___x_5049_; lean_object* v___x_5050_; 
v___x_5042_ = lean_io_get_num_heartbeats();
v___x_5043_ = lean_float_of_nat(v___y_5040_);
v___x_5044_ = lean_float_of_nat(v___x_5042_);
v___x_5045_ = lean_box_float(v___x_5043_);
v___x_5046_ = lean_box_float(v___x_5044_);
v___x_5047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5047_, 0, v___x_5045_);
lean_ctor_set(v___x_5047_, 1, v___x_5046_);
v___x_5048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5048_, 0, v_a_5041_);
lean_ctor_set(v___x_5048_, 1, v___x_5047_);
v___x_5049_ = lean_unbox(v_a_5017_);
lean_dec(v_a_5017_);
lean_inc(v___y_4876_);
lean_inc_ref(v___y_4875_);
lean_inc(v___y_4874_);
lean_inc_ref(v___y_4873_);
v___x_5050_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3(v___x_5015_, v_hasTrace_5011_, v___x_5019_, v_options_5010_, v___x_5049_, v___y_5039_, v___f_5018_, v___x_5048_, v___y_4871_, v___y_4872_, v___y_4873_, v___y_4874_, v___y_4875_, v___y_4876_);
v___y_4966_ = v___x_5050_;
goto v___jp_4965_;
}
v___jp_5051_:
{
lean_object* v___x_5052_; lean_object* v_a_5053_; lean_object* v___x_5054_; uint8_t v___x_5055_; 
v___x_5052_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__2___redArg(v___y_4876_);
v_a_5053_ = lean_ctor_get(v___x_5052_, 0);
lean_inc(v_a_5053_);
lean_dec_ref(v___x_5052_);
v___x_5054_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5055_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2(v_options_5010_, v___x_5054_);
if (v___x_5055_ == 0)
{
lean_object* v___x_5056_; lean_object* v___x_5057_; 
v___x_5056_ = lean_io_mono_nanos_now();
lean_inc(v___y_4876_);
lean_inc_ref(v___y_4875_);
lean_inc(v___y_4874_);
lean_inc_ref(v___y_4873_);
lean_inc(v___y_4872_);
lean_inc_ref(v___y_4871_);
v___x_5057_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v_a_5014_, v___x_4865_, v___y_4871_, v___y_4872_, v___y_4873_, v___y_4874_, v___y_4875_, v___y_4876_);
if (lean_obj_tag(v___x_5057_) == 0)
{
lean_object* v_a_5058_; lean_object* v___x_5060_; uint8_t v_isShared_5061_; uint8_t v_isSharedCheck_5065_; 
v_a_5058_ = lean_ctor_get(v___x_5057_, 0);
v_isSharedCheck_5065_ = !lean_is_exclusive(v___x_5057_);
if (v_isSharedCheck_5065_ == 0)
{
v___x_5060_ = v___x_5057_;
v_isShared_5061_ = v_isSharedCheck_5065_;
goto v_resetjp_5059_;
}
else
{
lean_inc(v_a_5058_);
lean_dec(v___x_5057_);
v___x_5060_ = lean_box(0);
v_isShared_5061_ = v_isSharedCheck_5065_;
goto v_resetjp_5059_;
}
v_resetjp_5059_:
{
lean_object* v___x_5063_; 
if (v_isShared_5061_ == 0)
{
lean_ctor_set_tag(v___x_5060_, 1);
v___x_5063_ = v___x_5060_;
goto v_reusejp_5062_;
}
else
{
lean_object* v_reuseFailAlloc_5064_; 
v_reuseFailAlloc_5064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5064_, 0, v_a_5058_);
v___x_5063_ = v_reuseFailAlloc_5064_;
goto v_reusejp_5062_;
}
v_reusejp_5062_:
{
v___y_5021_ = v_a_5053_;
v___y_5022_ = v___x_5056_;
v_a_5023_ = v___x_5063_;
goto v___jp_5020_;
}
}
}
else
{
lean_object* v_a_5066_; lean_object* v___x_5068_; uint8_t v_isShared_5069_; uint8_t v_isSharedCheck_5073_; 
v_a_5066_ = lean_ctor_get(v___x_5057_, 0);
v_isSharedCheck_5073_ = !lean_is_exclusive(v___x_5057_);
if (v_isSharedCheck_5073_ == 0)
{
v___x_5068_ = v___x_5057_;
v_isShared_5069_ = v_isSharedCheck_5073_;
goto v_resetjp_5067_;
}
else
{
lean_inc(v_a_5066_);
lean_dec(v___x_5057_);
v___x_5068_ = lean_box(0);
v_isShared_5069_ = v_isSharedCheck_5073_;
goto v_resetjp_5067_;
}
v_resetjp_5067_:
{
lean_object* v___x_5071_; 
if (v_isShared_5069_ == 0)
{
lean_ctor_set_tag(v___x_5068_, 0);
v___x_5071_ = v___x_5068_;
goto v_reusejp_5070_;
}
else
{
lean_object* v_reuseFailAlloc_5072_; 
v_reuseFailAlloc_5072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5072_, 0, v_a_5066_);
v___x_5071_ = v_reuseFailAlloc_5072_;
goto v_reusejp_5070_;
}
v_reusejp_5070_:
{
v___y_5021_ = v_a_5053_;
v___y_5022_ = v___x_5056_;
v_a_5023_ = v___x_5071_;
goto v___jp_5020_;
}
}
}
}
else
{
lean_object* v___x_5074_; lean_object* v___x_5075_; 
lean_del_object(v___x_4912_);
v___x_5074_ = lean_io_get_num_heartbeats();
lean_inc(v___y_4876_);
lean_inc_ref(v___y_4875_);
lean_inc(v___y_4874_);
lean_inc_ref(v___y_4873_);
lean_inc(v___y_4872_);
lean_inc_ref(v___y_4871_);
v___x_5075_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v_a_5014_, v___x_4865_, v___y_4871_, v___y_4872_, v___y_4873_, v___y_4874_, v___y_4875_, v___y_4876_);
if (lean_obj_tag(v___x_5075_) == 0)
{
lean_object* v_a_5076_; lean_object* v___x_5078_; uint8_t v_isShared_5079_; uint8_t v_isSharedCheck_5083_; 
v_a_5076_ = lean_ctor_get(v___x_5075_, 0);
v_isSharedCheck_5083_ = !lean_is_exclusive(v___x_5075_);
if (v_isSharedCheck_5083_ == 0)
{
v___x_5078_ = v___x_5075_;
v_isShared_5079_ = v_isSharedCheck_5083_;
goto v_resetjp_5077_;
}
else
{
lean_inc(v_a_5076_);
lean_dec(v___x_5075_);
v___x_5078_ = lean_box(0);
v_isShared_5079_ = v_isSharedCheck_5083_;
goto v_resetjp_5077_;
}
v_resetjp_5077_:
{
lean_object* v___x_5081_; 
if (v_isShared_5079_ == 0)
{
lean_ctor_set_tag(v___x_5078_, 1);
v___x_5081_ = v___x_5078_;
goto v_reusejp_5080_;
}
else
{
lean_object* v_reuseFailAlloc_5082_; 
v_reuseFailAlloc_5082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5082_, 0, v_a_5076_);
v___x_5081_ = v_reuseFailAlloc_5082_;
goto v_reusejp_5080_;
}
v_reusejp_5080_:
{
v___y_5039_ = v_a_5053_;
v___y_5040_ = v___x_5074_;
v_a_5041_ = v___x_5081_;
goto v___jp_5038_;
}
}
}
else
{
lean_object* v_a_5084_; lean_object* v___x_5086_; uint8_t v_isShared_5087_; uint8_t v_isSharedCheck_5091_; 
v_a_5084_ = lean_ctor_get(v___x_5075_, 0);
v_isSharedCheck_5091_ = !lean_is_exclusive(v___x_5075_);
if (v_isSharedCheck_5091_ == 0)
{
v___x_5086_ = v___x_5075_;
v_isShared_5087_ = v_isSharedCheck_5091_;
goto v_resetjp_5085_;
}
else
{
lean_inc(v_a_5084_);
lean_dec(v___x_5075_);
v___x_5086_ = lean_box(0);
v_isShared_5087_ = v_isSharedCheck_5091_;
goto v_resetjp_5085_;
}
v_resetjp_5085_:
{
lean_object* v___x_5089_; 
if (v_isShared_5087_ == 0)
{
lean_ctor_set_tag(v___x_5086_, 0);
v___x_5089_ = v___x_5086_;
goto v_reusejp_5088_;
}
else
{
lean_object* v_reuseFailAlloc_5090_; 
v_reuseFailAlloc_5090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5090_, 0, v_a_5084_);
v___x_5089_ = v_reuseFailAlloc_5090_;
goto v_reusejp_5088_;
}
v_reusejp_5088_:
{
v___y_5039_ = v_a_5053_;
v___y_5040_ = v___x_5074_;
v_a_5041_ = v___x_5089_;
goto v___jp_5038_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5096_; lean_object* v___x_5098_; uint8_t v_isShared_5099_; uint8_t v_isSharedCheck_5103_; 
lean_del_object(v___x_4912_);
lean_dec(v_snd_4910_);
lean_dec(v___y_4876_);
lean_dec_ref(v___y_4875_);
lean_dec(v___y_4874_);
lean_dec_ref(v___y_4873_);
lean_dec(v___y_4872_);
lean_dec_ref(v___y_4871_);
lean_dec_ref(v___x_4865_);
lean_dec(v_a_4864_);
v_a_5096_ = lean_ctor_get(v___x_5009_, 0);
v_isSharedCheck_5103_ = !lean_is_exclusive(v___x_5009_);
if (v_isSharedCheck_5103_ == 0)
{
v___x_5098_ = v___x_5009_;
v_isShared_5099_ = v_isSharedCheck_5103_;
goto v_resetjp_5097_;
}
else
{
lean_inc(v_a_5096_);
lean_dec(v___x_5009_);
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
}
else
{
lean_object* v_val_5104_; lean_object* v___x_5106_; 
lean_del_object(v___x_4912_);
lean_dec(v_snd_4910_);
lean_dec(v___y_4876_);
lean_dec_ref(v___y_4875_);
lean_dec(v___y_4874_);
lean_dec_ref(v___y_4873_);
lean_dec(v___y_4872_);
lean_dec_ref(v___y_4871_);
lean_dec_ref(v___x_4865_);
lean_dec(v_a_4864_);
v_val_5104_ = lean_ctor_get(v_fst_4909_, 0);
lean_inc(v_val_5104_);
lean_dec_ref(v_fst_4909_);
if (v_isShared_4908_ == 0)
{
lean_ctor_set(v___x_4907_, 0, v_val_5104_);
v___x_5106_ = v___x_4907_;
goto v_reusejp_5105_;
}
else
{
lean_object* v_reuseFailAlloc_5107_; 
v_reuseFailAlloc_5107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5107_, 0, v_val_5104_);
v___x_5106_ = v_reuseFailAlloc_5107_;
goto v_reusejp_5105_;
}
v_reusejp_5105_:
{
return v___x_5106_;
}
}
v___jp_4914_:
{
lean_object* v___x_4920_; 
lean_inc(v___y_4919_);
lean_inc_ref(v___y_4918_);
lean_inc(v___y_4917_);
lean_inc_ref(v___y_4916_);
v___x_4920_ = l_Lean_MVarId_assertHypotheses(v_mvarIdNew_4915_, v_snd_4910_, v___y_4916_, v___y_4917_, v___y_4918_, v___y_4919_);
if (lean_obj_tag(v___x_4920_) == 0)
{
lean_object* v_a_4921_; lean_object* v_snd_4922_; lean_object* v___x_4923_; 
v_a_4921_ = lean_ctor_get(v___x_4920_, 0);
lean_inc(v_a_4921_);
lean_dec_ref(v___x_4920_);
v_snd_4922_ = lean_ctor_get(v_a_4921_, 1);
lean_inc(v_snd_4922_);
lean_dec(v_a_4921_);
lean_inc(v___y_4919_);
lean_inc_ref(v___y_4918_);
lean_inc(v___y_4917_);
lean_inc_ref(v___y_4916_);
v___x_4923_ = l_Lean_MVarId_tryClearMany(v_snd_4922_, v_fvarIdsToSimp_4866_, v___y_4916_, v___y_4917_, v___y_4918_, v___y_4919_);
if (lean_obj_tag(v___x_4923_) == 0)
{
lean_object* v_a_4924_; lean_object* v___x_4925_; 
v_a_4924_ = lean_ctor_get(v___x_4923_, 0);
lean_inc(v_a_4924_);
lean_dec_ref(v___x_4923_);
v___x_4925_ = l_Lean_Meta_saveState___redArg(v___y_4917_, v___y_4919_);
if (lean_obj_tag(v___x_4925_) == 0)
{
lean_object* v_a_4926_; uint8_t v___x_4927_; lean_object* v___x_4928_; 
v_a_4926_ = lean_ctor_get(v___x_4925_, 0);
lean_inc(v_a_4926_);
lean_dec_ref(v___x_4925_);
v___x_4927_ = 1;
lean_inc(v___y_4919_);
lean_inc(v___y_4917_);
lean_inc(v_a_4924_);
v___x_4928_ = l_Lean_MVarId_refl(v_a_4924_, v___x_4927_, v___y_4916_, v___y_4917_, v___y_4918_, v___y_4919_);
if (lean_obj_tag(v___x_4928_) == 0)
{
lean_object* v___x_4930_; uint8_t v_isShared_4931_; uint8_t v_isSharedCheck_4936_; 
lean_dec(v_a_4926_);
lean_dec(v_a_4924_);
lean_dec(v___y_4919_);
lean_dec(v___y_4917_);
v_isSharedCheck_4936_ = !lean_is_exclusive(v___x_4928_);
if (v_isSharedCheck_4936_ == 0)
{
lean_object* v_unused_4937_; 
v_unused_4937_ = lean_ctor_get(v___x_4928_, 0);
lean_dec(v_unused_4937_);
v___x_4930_ = v___x_4928_;
v_isShared_4931_ = v_isSharedCheck_4936_;
goto v_resetjp_4929_;
}
else
{
lean_dec(v___x_4928_);
v___x_4930_ = lean_box(0);
v_isShared_4931_ = v_isSharedCheck_4936_;
goto v_resetjp_4929_;
}
v_resetjp_4929_:
{
lean_object* v___x_4932_; lean_object* v___x_4934_; 
v___x_4932_ = lean_box(0);
if (v_isShared_4931_ == 0)
{
lean_ctor_set(v___x_4930_, 0, v___x_4932_);
v___x_4934_ = v___x_4930_;
goto v_reusejp_4933_;
}
else
{
lean_object* v_reuseFailAlloc_4935_; 
v_reuseFailAlloc_4935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4935_, 0, v___x_4932_);
v___x_4934_ = v_reuseFailAlloc_4935_;
goto v_reusejp_4933_;
}
v_reusejp_4933_:
{
return v___x_4934_;
}
}
}
else
{
lean_object* v_a_4938_; uint8_t v___x_4939_; 
v_a_4938_ = lean_ctor_get(v___x_4928_, 0);
lean_inc(v_a_4938_);
lean_dec_ref(v___x_4928_);
v___x_4939_ = l_Lean_Exception_isInterrupt(v_a_4938_);
if (v___x_4939_ == 0)
{
uint8_t v___x_4940_; 
lean_inc(v_a_4938_);
v___x_4940_ = l_Lean_Exception_isRuntime(v_a_4938_);
v___y_4879_ = v_a_4924_;
v___y_4880_ = v___y_4917_;
v___y_4881_ = v___y_4919_;
v___y_4882_ = v_a_4938_;
v___y_4883_ = v_a_4926_;
v___y_4884_ = v___x_4940_;
goto v___jp_4878_;
}
else
{
v___y_4879_ = v_a_4924_;
v___y_4880_ = v___y_4917_;
v___y_4881_ = v___y_4919_;
v___y_4882_ = v_a_4938_;
v___y_4883_ = v_a_4926_;
v___y_4884_ = v___x_4939_;
goto v___jp_4878_;
}
}
}
else
{
lean_object* v_a_4941_; lean_object* v___x_4943_; uint8_t v_isShared_4944_; uint8_t v_isSharedCheck_4948_; 
lean_dec(v_a_4924_);
lean_dec(v___y_4919_);
lean_dec_ref(v___y_4918_);
lean_dec(v___y_4917_);
lean_dec_ref(v___y_4916_);
v_a_4941_ = lean_ctor_get(v___x_4925_, 0);
v_isSharedCheck_4948_ = !lean_is_exclusive(v___x_4925_);
if (v_isSharedCheck_4948_ == 0)
{
v___x_4943_ = v___x_4925_;
v_isShared_4944_ = v_isSharedCheck_4948_;
goto v_resetjp_4942_;
}
else
{
lean_inc(v_a_4941_);
lean_dec(v___x_4925_);
v___x_4943_ = lean_box(0);
v_isShared_4944_ = v_isSharedCheck_4948_;
goto v_resetjp_4942_;
}
v_resetjp_4942_:
{
lean_object* v___x_4946_; 
if (v_isShared_4944_ == 0)
{
v___x_4946_ = v___x_4943_;
goto v_reusejp_4945_;
}
else
{
lean_object* v_reuseFailAlloc_4947_; 
v_reuseFailAlloc_4947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4947_, 0, v_a_4941_);
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
else
{
lean_object* v_a_4949_; lean_object* v___x_4951_; uint8_t v_isShared_4952_; uint8_t v_isSharedCheck_4956_; 
lean_dec(v___y_4919_);
lean_dec_ref(v___y_4918_);
lean_dec(v___y_4917_);
lean_dec_ref(v___y_4916_);
v_a_4949_ = lean_ctor_get(v___x_4923_, 0);
v_isSharedCheck_4956_ = !lean_is_exclusive(v___x_4923_);
if (v_isSharedCheck_4956_ == 0)
{
v___x_4951_ = v___x_4923_;
v_isShared_4952_ = v_isSharedCheck_4956_;
goto v_resetjp_4950_;
}
else
{
lean_inc(v_a_4949_);
lean_dec(v___x_4923_);
v___x_4951_ = lean_box(0);
v_isShared_4952_ = v_isSharedCheck_4956_;
goto v_resetjp_4950_;
}
v_resetjp_4950_:
{
lean_object* v___x_4954_; 
if (v_isShared_4952_ == 0)
{
v___x_4954_ = v___x_4951_;
goto v_reusejp_4953_;
}
else
{
lean_object* v_reuseFailAlloc_4955_; 
v_reuseFailAlloc_4955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4955_, 0, v_a_4949_);
v___x_4954_ = v_reuseFailAlloc_4955_;
goto v_reusejp_4953_;
}
v_reusejp_4953_:
{
return v___x_4954_;
}
}
}
}
else
{
lean_object* v_a_4957_; lean_object* v___x_4959_; uint8_t v_isShared_4960_; uint8_t v_isSharedCheck_4964_; 
lean_dec(v___y_4919_);
lean_dec_ref(v___y_4918_);
lean_dec(v___y_4917_);
lean_dec_ref(v___y_4916_);
v_a_4957_ = lean_ctor_get(v___x_4920_, 0);
v_isSharedCheck_4964_ = !lean_is_exclusive(v___x_4920_);
if (v_isSharedCheck_4964_ == 0)
{
v___x_4959_ = v___x_4920_;
v_isShared_4960_ = v_isSharedCheck_4964_;
goto v_resetjp_4958_;
}
else
{
lean_inc(v_a_4957_);
lean_dec(v___x_4920_);
v___x_4959_ = lean_box(0);
v_isShared_4960_ = v_isSharedCheck_4964_;
goto v_resetjp_4958_;
}
v_resetjp_4958_:
{
lean_object* v___x_4962_; 
if (v_isShared_4960_ == 0)
{
v___x_4962_ = v___x_4959_;
goto v_reusejp_4961_;
}
else
{
lean_object* v_reuseFailAlloc_4963_; 
v_reuseFailAlloc_4963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4963_, 0, v_a_4957_);
v___x_4962_ = v_reuseFailAlloc_4963_;
goto v_reusejp_4961_;
}
v_reusejp_4961_:
{
return v___x_4962_;
}
}
}
}
v___jp_4965_:
{
if (lean_obj_tag(v___y_4966_) == 0)
{
lean_object* v_a_4967_; 
v_a_4967_ = lean_ctor_get(v___y_4966_, 0);
lean_inc(v_a_4967_);
lean_dec_ref(v___y_4966_);
if (lean_obj_tag(v_a_4967_) == 0)
{
lean_dec_ref(v_a_4967_);
v_mvarIdNew_4915_ = v_a_4864_;
v___y_4916_ = v___y_4873_;
v___y_4917_ = v___y_4874_;
v___y_4918_ = v___y_4875_;
v___y_4919_ = v___y_4876_;
goto v___jp_4914_;
}
else
{
lean_object* v_e_x27_4968_; lean_object* v_proof_4969_; uint8_t v___x_4970_; 
v_e_x27_4968_ = lean_ctor_get(v_a_4967_, 0);
lean_inc_ref(v_e_x27_4968_);
v_proof_4969_ = lean_ctor_get(v_a_4967_, 1);
lean_inc_ref(v_proof_4969_);
lean_dec_ref(v_a_4967_);
lean_inc_ref(v_e_x27_4968_);
v___x_4970_ = l_Lean_Expr_isTrue(v_e_x27_4968_);
if (v___x_4970_ == 0)
{
lean_object* v___x_4971_; 
lean_inc(v___y_4876_);
lean_inc_ref(v___y_4875_);
lean_inc(v___y_4874_);
lean_inc_ref(v___y_4873_);
v___x_4971_ = l_Lean_MVarId_replaceTargetEq(v_a_4864_, v_e_x27_4968_, v_proof_4969_, v___y_4873_, v___y_4874_, v___y_4875_, v___y_4876_);
if (lean_obj_tag(v___x_4971_) == 0)
{
lean_object* v_a_4972_; 
v_a_4972_ = lean_ctor_get(v___x_4971_, 0);
lean_inc(v_a_4972_);
lean_dec_ref(v___x_4971_);
v_mvarIdNew_4915_ = v_a_4972_;
v___y_4916_ = v___y_4873_;
v___y_4917_ = v___y_4874_;
v___y_4918_ = v___y_4875_;
v___y_4919_ = v___y_4876_;
goto v___jp_4914_;
}
else
{
lean_object* v_a_4973_; lean_object* v___x_4975_; uint8_t v_isShared_4976_; uint8_t v_isSharedCheck_4980_; 
lean_dec(v_snd_4910_);
lean_dec(v___y_4876_);
lean_dec_ref(v___y_4875_);
lean_dec(v___y_4874_);
lean_dec_ref(v___y_4873_);
v_a_4973_ = lean_ctor_get(v___x_4971_, 0);
v_isSharedCheck_4980_ = !lean_is_exclusive(v___x_4971_);
if (v_isSharedCheck_4980_ == 0)
{
v___x_4975_ = v___x_4971_;
v_isShared_4976_ = v_isSharedCheck_4980_;
goto v_resetjp_4974_;
}
else
{
lean_inc(v_a_4973_);
lean_dec(v___x_4971_);
v___x_4975_ = lean_box(0);
v_isShared_4976_ = v_isSharedCheck_4980_;
goto v_resetjp_4974_;
}
v_resetjp_4974_:
{
lean_object* v___x_4978_; 
if (v_isShared_4976_ == 0)
{
v___x_4978_ = v___x_4975_;
goto v_reusejp_4977_;
}
else
{
lean_object* v_reuseFailAlloc_4979_; 
v_reuseFailAlloc_4979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4979_, 0, v_a_4973_);
v___x_4978_ = v_reuseFailAlloc_4979_;
goto v_reusejp_4977_;
}
v_reusejp_4977_:
{
return v___x_4978_;
}
}
}
}
else
{
lean_object* v___x_4981_; 
lean_dec_ref(v_e_x27_4968_);
lean_dec(v_snd_4910_);
lean_inc(v___y_4874_);
v___x_4981_ = l_Lean_Meta_mkOfEqTrue(v_proof_4969_, v___y_4873_, v___y_4874_, v___y_4875_, v___y_4876_);
if (lean_obj_tag(v___x_4981_) == 0)
{
lean_object* v_a_4982_; lean_object* v___x_4983_; lean_object* v___x_4985_; uint8_t v_isShared_4986_; uint8_t v_isSharedCheck_4991_; 
v_a_4982_ = lean_ctor_get(v___x_4981_, 0);
lean_inc(v_a_4982_);
lean_dec_ref(v___x_4981_);
v___x_4983_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0___redArg(v_a_4864_, v_a_4982_, v___y_4874_);
lean_dec(v___y_4874_);
v_isSharedCheck_4991_ = !lean_is_exclusive(v___x_4983_);
if (v_isSharedCheck_4991_ == 0)
{
lean_object* v_unused_4992_; 
v_unused_4992_ = lean_ctor_get(v___x_4983_, 0);
lean_dec(v_unused_4992_);
v___x_4985_ = v___x_4983_;
v_isShared_4986_ = v_isSharedCheck_4991_;
goto v_resetjp_4984_;
}
else
{
lean_dec(v___x_4983_);
v___x_4985_ = lean_box(0);
v_isShared_4986_ = v_isSharedCheck_4991_;
goto v_resetjp_4984_;
}
v_resetjp_4984_:
{
lean_object* v___x_4987_; lean_object* v___x_4989_; 
v___x_4987_ = lean_box(0);
if (v_isShared_4986_ == 0)
{
lean_ctor_set(v___x_4985_, 0, v___x_4987_);
v___x_4989_ = v___x_4985_;
goto v_reusejp_4988_;
}
else
{
lean_object* v_reuseFailAlloc_4990_; 
v_reuseFailAlloc_4990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4990_, 0, v___x_4987_);
v___x_4989_ = v_reuseFailAlloc_4990_;
goto v_reusejp_4988_;
}
v_reusejp_4988_:
{
return v___x_4989_;
}
}
}
else
{
lean_object* v_a_4993_; lean_object* v___x_4995_; uint8_t v_isShared_4996_; uint8_t v_isSharedCheck_5000_; 
lean_dec(v___y_4874_);
lean_dec(v_a_4864_);
v_a_4993_ = lean_ctor_get(v___x_4981_, 0);
v_isSharedCheck_5000_ = !lean_is_exclusive(v___x_4981_);
if (v_isSharedCheck_5000_ == 0)
{
v___x_4995_ = v___x_4981_;
v_isShared_4996_ = v_isSharedCheck_5000_;
goto v_resetjp_4994_;
}
else
{
lean_inc(v_a_4993_);
lean_dec(v___x_4981_);
v___x_4995_ = lean_box(0);
v_isShared_4996_ = v_isSharedCheck_5000_;
goto v_resetjp_4994_;
}
v_resetjp_4994_:
{
lean_object* v___x_4998_; 
if (v_isShared_4996_ == 0)
{
v___x_4998_ = v___x_4995_;
goto v_reusejp_4997_;
}
else
{
lean_object* v_reuseFailAlloc_4999_; 
v_reuseFailAlloc_4999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4999_, 0, v_a_4993_);
v___x_4998_ = v_reuseFailAlloc_4999_;
goto v_reusejp_4997_;
}
v_reusejp_4997_:
{
return v___x_4998_;
}
}
}
}
}
}
else
{
lean_object* v_a_5001_; lean_object* v___x_5003_; uint8_t v_isShared_5004_; uint8_t v_isSharedCheck_5008_; 
lean_dec(v_snd_4910_);
lean_dec(v___y_4876_);
lean_dec_ref(v___y_4875_);
lean_dec(v___y_4874_);
lean_dec_ref(v___y_4873_);
lean_dec(v_a_4864_);
v_a_5001_ = lean_ctor_get(v___y_4966_, 0);
v_isSharedCheck_5008_ = !lean_is_exclusive(v___y_4966_);
if (v_isSharedCheck_5008_ == 0)
{
v___x_5003_ = v___y_4966_;
v_isShared_5004_ = v_isSharedCheck_5008_;
goto v_resetjp_5002_;
}
else
{
lean_inc(v_a_5001_);
lean_dec(v___y_4966_);
v___x_5003_ = lean_box(0);
v_isShared_5004_ = v_isSharedCheck_5008_;
goto v_resetjp_5002_;
}
v_resetjp_5002_:
{
lean_object* v___x_5006_; 
if (v_isShared_5004_ == 0)
{
v___x_5006_ = v___x_5003_;
goto v_reusejp_5005_;
}
else
{
lean_object* v_reuseFailAlloc_5007_; 
v_reuseFailAlloc_5007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5007_, 0, v_a_5001_);
v___x_5006_ = v_reuseFailAlloc_5007_;
goto v_reusejp_5005_;
}
v_reusejp_5005_:
{
return v___x_5006_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5110_; lean_object* v___x_5112_; uint8_t v_isShared_5113_; uint8_t v_isSharedCheck_5117_; 
lean_dec(v___y_4876_);
lean_dec_ref(v___y_4875_);
lean_dec(v___y_4874_);
lean_dec_ref(v___y_4873_);
lean_dec(v___y_4872_);
lean_dec_ref(v___y_4871_);
lean_dec_ref(v___x_4865_);
lean_dec(v_a_4864_);
v_a_5110_ = lean_ctor_get(v___x_4904_, 0);
v_isSharedCheck_5117_ = !lean_is_exclusive(v___x_4904_);
if (v_isSharedCheck_5117_ == 0)
{
v___x_5112_ = v___x_4904_;
v_isShared_5113_ = v_isSharedCheck_5117_;
goto v_resetjp_5111_;
}
else
{
lean_inc(v_a_5110_);
lean_dec(v___x_4904_);
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
v___jp_4878_:
{
if (v___y_4884_ == 0)
{
lean_object* v___x_4885_; 
lean_dec_ref(v___y_4882_);
v___x_4885_ = l_Lean_Meta_SavedState_restore___redArg(v___y_4883_, v___y_4880_, v___y_4881_);
lean_dec(v___y_4881_);
lean_dec(v___y_4880_);
lean_dec_ref(v___y_4883_);
if (lean_obj_tag(v___x_4885_) == 0)
{
lean_object* v___x_4887_; uint8_t v_isShared_4888_; uint8_t v_isSharedCheck_4893_; 
v_isSharedCheck_4893_ = !lean_is_exclusive(v___x_4885_);
if (v_isSharedCheck_4893_ == 0)
{
lean_object* v_unused_4894_; 
v_unused_4894_ = lean_ctor_get(v___x_4885_, 0);
lean_dec(v_unused_4894_);
v___x_4887_ = v___x_4885_;
v_isShared_4888_ = v_isSharedCheck_4893_;
goto v_resetjp_4886_;
}
else
{
lean_dec(v___x_4885_);
v___x_4887_ = lean_box(0);
v_isShared_4888_ = v_isSharedCheck_4893_;
goto v_resetjp_4886_;
}
v_resetjp_4886_:
{
lean_object* v___x_4889_; lean_object* v___x_4891_; 
v___x_4889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4889_, 0, v___y_4879_);
if (v_isShared_4888_ == 0)
{
lean_ctor_set(v___x_4887_, 0, v___x_4889_);
v___x_4891_ = v___x_4887_;
goto v_reusejp_4890_;
}
else
{
lean_object* v_reuseFailAlloc_4892_; 
v_reuseFailAlloc_4892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4892_, 0, v___x_4889_);
v___x_4891_ = v_reuseFailAlloc_4892_;
goto v_reusejp_4890_;
}
v_reusejp_4890_:
{
return v___x_4891_;
}
}
}
else
{
lean_object* v_a_4895_; lean_object* v___x_4897_; uint8_t v_isShared_4898_; uint8_t v_isSharedCheck_4902_; 
lean_dec(v___y_4879_);
v_a_4895_ = lean_ctor_get(v___x_4885_, 0);
v_isSharedCheck_4902_ = !lean_is_exclusive(v___x_4885_);
if (v_isSharedCheck_4902_ == 0)
{
v___x_4897_ = v___x_4885_;
v_isShared_4898_ = v_isSharedCheck_4902_;
goto v_resetjp_4896_;
}
else
{
lean_inc(v_a_4895_);
lean_dec(v___x_4885_);
v___x_4897_ = lean_box(0);
v_isShared_4898_ = v_isSharedCheck_4902_;
goto v_resetjp_4896_;
}
v_resetjp_4896_:
{
lean_object* v___x_4900_; 
if (v_isShared_4898_ == 0)
{
v___x_4900_ = v___x_4897_;
goto v_reusejp_4899_;
}
else
{
lean_object* v_reuseFailAlloc_4901_; 
v_reuseFailAlloc_4901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4901_, 0, v_a_4895_);
v___x_4900_ = v_reuseFailAlloc_4901_;
goto v_reusejp_4899_;
}
v_reusejp_4899_:
{
return v___x_4900_;
}
}
}
}
else
{
lean_object* v___x_4903_; 
lean_dec_ref(v___y_4883_);
lean_dec(v___y_4881_);
lean_dec(v___y_4880_);
lean_dec(v___y_4879_);
v___x_4903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4903_, 0, v___y_4882_);
return v___x_4903_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__1___boxed(lean_object* v_a_5118_, lean_object* v___x_5119_, lean_object* v_fvarIdsToSimp_5120_, lean_object* v_sz_5121_, lean_object* v___x_5122_, lean_object* v___x_5123_, lean_object* v_simplifyTarget_5124_, lean_object* v___y_5125_, lean_object* v___y_5126_, lean_object* v___y_5127_, lean_object* v___y_5128_, lean_object* v___y_5129_, lean_object* v___y_5130_, lean_object* v___y_5131_){
_start:
{
size_t v_sz_boxed_5132_; size_t v___x_47442__boxed_5133_; uint8_t v_simplifyTarget_boxed_5134_; lean_object* v_res_5135_; 
v_sz_boxed_5132_ = lean_unbox_usize(v_sz_5121_);
lean_dec(v_sz_5121_);
v___x_47442__boxed_5133_ = lean_unbox_usize(v___x_5122_);
lean_dec(v___x_5122_);
v_simplifyTarget_boxed_5134_ = lean_unbox(v_simplifyTarget_5124_);
v_res_5135_ = l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__1(v_a_5118_, v___x_5119_, v_fvarIdsToSimp_5120_, v_sz_boxed_5132_, v___x_47442__boxed_5133_, v___x_5123_, v_simplifyTarget_boxed_5134_, v___y_5125_, v___y_5126_, v___y_5127_, v___y_5128_, v___y_5129_, v___y_5130_);
lean_dec_ref(v_fvarIdsToSimp_5120_);
return v_res_5135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__2(lean_object* v_mvarId_5143_, lean_object* v_fvarIdsToSimp_5144_, lean_object* v___x_5145_, uint8_t v_simplifyTarget_5146_, lean_object* v___y_5147_, lean_object* v___y_5148_, lean_object* v___y_5149_, lean_object* v___y_5150_, lean_object* v___y_5151_, lean_object* v___y_5152_){
_start:
{
lean_object* v___x_5154_; 
lean_inc(v___y_5152_);
lean_inc_ref(v___y_5151_);
lean_inc(v___y_5150_);
lean_inc_ref(v___y_5149_);
v___x_5154_ = l_Lean_Meta_Sym_preprocessMVar(v_mvarId_5143_, v___y_5147_, v___y_5148_, v___y_5149_, v___y_5150_, v___y_5151_, v___y_5152_);
if (lean_obj_tag(v___x_5154_) == 0)
{
lean_object* v_a_5155_; lean_object* v___x_5156_; size_t v_sz_5157_; lean_object* v___x_5158_; lean_object* v___x_5159_; lean_object* v___x_5160_; lean_object* v___f_5161_; lean_object* v___x_5162_; 
v_a_5155_ = lean_ctor_get(v___x_5154_, 0);
lean_inc(v_a_5155_);
lean_dec_ref(v___x_5154_);
v___x_5156_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__2___closed__1));
v_sz_5157_ = lean_array_size(v_fvarIdsToSimp_5144_);
v___x_5158_ = lean_box_usize(v_sz_5157_);
v___x_5159_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__2___boxed__const__1));
v___x_5160_ = lean_box(v_simplifyTarget_5146_);
lean_inc(v_a_5155_);
v___f_5161_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__1___boxed), 14, 7);
lean_closure_set(v___f_5161_, 0, v_a_5155_);
lean_closure_set(v___f_5161_, 1, v___x_5145_);
lean_closure_set(v___f_5161_, 2, v_fvarIdsToSimp_5144_);
lean_closure_set(v___f_5161_, 3, v___x_5158_);
lean_closure_set(v___f_5161_, 4, v___x_5159_);
lean_closure_set(v___f_5161_, 5, v___x_5156_);
lean_closure_set(v___f_5161_, 6, v___x_5160_);
v___x_5162_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__5___redArg(v_a_5155_, v___f_5161_, v___y_5147_, v___y_5148_, v___y_5149_, v___y_5150_, v___y_5151_, v___y_5152_);
return v___x_5162_;
}
else
{
lean_object* v_a_5163_; lean_object* v___x_5165_; uint8_t v_isShared_5166_; uint8_t v_isSharedCheck_5170_; 
lean_dec(v___y_5152_);
lean_dec_ref(v___y_5151_);
lean_dec(v___y_5150_);
lean_dec_ref(v___y_5149_);
lean_dec(v___y_5148_);
lean_dec_ref(v___y_5147_);
lean_dec_ref(v___x_5145_);
lean_dec_ref(v_fvarIdsToSimp_5144_);
v_a_5163_ = lean_ctor_get(v___x_5154_, 0);
v_isSharedCheck_5170_ = !lean_is_exclusive(v___x_5154_);
if (v_isSharedCheck_5170_ == 0)
{
v___x_5165_ = v___x_5154_;
v_isShared_5166_ = v_isSharedCheck_5170_;
goto v_resetjp_5164_;
}
else
{
lean_inc(v_a_5163_);
lean_dec(v___x_5154_);
v___x_5165_ = lean_box(0);
v_isShared_5166_ = v_isSharedCheck_5170_;
goto v_resetjp_5164_;
}
v_resetjp_5164_:
{
lean_object* v___x_5168_; 
if (v_isShared_5166_ == 0)
{
v___x_5168_ = v___x_5165_;
goto v_reusejp_5167_;
}
else
{
lean_object* v_reuseFailAlloc_5169_; 
v_reuseFailAlloc_5169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5169_, 0, v_a_5163_);
v___x_5168_ = v_reuseFailAlloc_5169_;
goto v_reusejp_5167_;
}
v_reusejp_5167_:
{
return v___x_5168_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__2___boxed(lean_object* v_mvarId_5171_, lean_object* v_fvarIdsToSimp_5172_, lean_object* v___x_5173_, lean_object* v_simplifyTarget_5174_, lean_object* v___y_5175_, lean_object* v___y_5176_, lean_object* v___y_5177_, lean_object* v___y_5178_, lean_object* v___y_5179_, lean_object* v___y_5180_, lean_object* v___y_5181_){
_start:
{
uint8_t v_simplifyTarget_boxed_5182_; lean_object* v_res_5183_; 
v_simplifyTarget_boxed_5182_ = lean_unbox(v_simplifyTarget_5174_);
v_res_5183_ = l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__2(v_mvarId_5171_, v_fvarIdsToSimp_5172_, v___x_5173_, v_simplifyTarget_boxed_5182_, v___y_5175_, v___y_5176_, v___y_5177_, v___y_5178_, v___y_5179_, v___y_5180_);
return v_res_5183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal(lean_object* v_mvarId_5184_, uint8_t v_simplifyTarget_5185_, lean_object* v_fvarIdsToSimp_5186_, lean_object* v_a_5187_, lean_object* v_a_5188_, lean_object* v_a_5189_, lean_object* v_a_5190_){
_start:
{
lean_object* v_options_5192_; lean_object* v___x_5193_; lean_object* v___x_5194_; lean_object* v___x_5195_; lean_object* v___x_5196_; lean_object* v___x_5197_; lean_object* v___f_5198_; lean_object* v___x_5199_; 
v_options_5192_ = lean_ctor_get(v_a_5189_, 2);
v___x_5193_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_5194_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__6(v_options_5192_, v___x_5193_);
v___x_5195_ = lean_unsigned_to_nat(2u);
v___x_5196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5196_, 0, v___x_5194_);
lean_ctor_set(v___x_5196_, 1, v___x_5195_);
v___x_5197_ = lean_box(v_simplifyTarget_5185_);
v___f_5198_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__2___boxed), 11, 4);
lean_closure_set(v___f_5198_, 0, v_mvarId_5184_);
lean_closure_set(v___f_5198_, 1, v_fvarIdsToSimp_5186_);
lean_closure_set(v___f_5198_, 2, v___x_5196_);
lean_closure_set(v___f_5198_, 3, v___x_5197_);
v___x_5199_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_5198_, v_a_5187_, v_a_5188_, v_a_5189_, v_a_5190_);
return v___x_5199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___boxed(lean_object* v_mvarId_5200_, lean_object* v_simplifyTarget_5201_, lean_object* v_fvarIdsToSimp_5202_, lean_object* v_a_5203_, lean_object* v_a_5204_, lean_object* v_a_5205_, lean_object* v_a_5206_, lean_object* v_a_5207_){
_start:
{
uint8_t v_simplifyTarget_boxed_5208_; lean_object* v_res_5209_; 
v_simplifyTarget_boxed_5208_ = lean_unbox(v_simplifyTarget_5201_);
v_res_5209_ = l_Lean_Meta_Tactic_Cbv_cbvGoal(v_mvarId_5200_, v_simplifyTarget_boxed_5208_, v_fvarIdsToSimp_5202_, v_a_5203_, v_a_5204_, v_a_5205_, v_a_5206_);
return v_res_5209_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0(lean_object* v_mvarId_5210_, lean_object* v_val_5211_, lean_object* v___y_5212_, lean_object* v___y_5213_, lean_object* v___y_5214_, lean_object* v___y_5215_, lean_object* v___y_5216_, lean_object* v___y_5217_){
_start:
{
lean_object* v___x_5219_; 
v___x_5219_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0___redArg(v_mvarId_5210_, v_val_5211_, v___y_5215_);
return v___x_5219_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0___boxed(lean_object* v_mvarId_5220_, lean_object* v_val_5221_, lean_object* v___y_5222_, lean_object* v___y_5223_, lean_object* v___y_5224_, lean_object* v___y_5225_, lean_object* v___y_5226_, lean_object* v___y_5227_, lean_object* v___y_5228_){
_start:
{
lean_object* v_res_5229_; 
v_res_5229_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0(v_mvarId_5220_, v_val_5221_, v___y_5222_, v___y_5223_, v___y_5224_, v___y_5225_, v___y_5226_, v___y_5227_);
lean_dec(v___y_5227_);
lean_dec_ref(v___y_5226_);
lean_dec(v___y_5225_);
lean_dec_ref(v___y_5224_);
lean_dec(v___y_5223_);
lean_dec_ref(v___y_5222_);
return v_res_5229_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3_spec__5(lean_object* v_00_u03b1_5230_, lean_object* v_x_5231_, lean_object* v___y_5232_, lean_object* v___y_5233_, lean_object* v___y_5234_, lean_object* v___y_5235_, lean_object* v___y_5236_, lean_object* v___y_5237_){
_start:
{
lean_object* v___x_5239_; 
v___x_5239_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3_spec__5___redArg(v_x_5231_);
return v___x_5239_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3_spec__5___boxed(lean_object* v_00_u03b1_5240_, lean_object* v_x_5241_, lean_object* v___y_5242_, lean_object* v___y_5243_, lean_object* v___y_5244_, lean_object* v___y_5245_, lean_object* v___y_5246_, lean_object* v___y_5247_, lean_object* v___y_5248_){
_start:
{
lean_object* v_res_5249_; 
v_res_5249_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3_spec__5(v_00_u03b1_5240_, v_x_5241_, v___y_5242_, v___y_5243_, v___y_5244_, v___y_5245_, v___y_5246_, v___y_5247_);
lean_dec(v___y_5247_);
lean_dec_ref(v___y_5246_);
lean_dec(v___y_5245_);
lean_dec_ref(v___y_5244_);
lean_dec(v___y_5243_);
lean_dec_ref(v___y_5242_);
return v_res_5249_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0(lean_object* v_00_u03b2_5250_, lean_object* v_x_5251_, lean_object* v_x_5252_, lean_object* v_x_5253_){
_start:
{
lean_object* v___x_5254_; 
v___x_5254_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0___redArg(v_x_5251_, v_x_5252_, v_x_5253_);
return v___x_5254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3_spec__4(lean_object* v_oldTraces_5255_, lean_object* v_data_5256_, lean_object* v_ref_5257_, lean_object* v_msg_5258_, lean_object* v___y_5259_, lean_object* v___y_5260_, lean_object* v___y_5261_, lean_object* v___y_5262_, lean_object* v___y_5263_, lean_object* v___y_5264_){
_start:
{
lean_object* v___x_5266_; 
v___x_5266_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3_spec__4___redArg(v_oldTraces_5255_, v_data_5256_, v_ref_5257_, v_msg_5258_, v___y_5261_, v___y_5262_, v___y_5263_, v___y_5264_);
return v___x_5266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3_spec__4___boxed(lean_object* v_oldTraces_5267_, lean_object* v_data_5268_, lean_object* v_ref_5269_, lean_object* v_msg_5270_, lean_object* v___y_5271_, lean_object* v___y_5272_, lean_object* v___y_5273_, lean_object* v___y_5274_, lean_object* v___y_5275_, lean_object* v___y_5276_, lean_object* v___y_5277_){
_start:
{
lean_object* v_res_5278_; 
v_res_5278_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__3_spec__4(v_oldTraces_5267_, v_data_5268_, v_ref_5269_, v_msg_5270_, v___y_5271_, v___y_5272_, v___y_5273_, v___y_5274_, v___y_5275_, v___y_5276_);
lean_dec(v___y_5276_);
lean_dec(v___y_5274_);
lean_dec_ref(v___y_5273_);
lean_dec(v___y_5272_);
lean_dec_ref(v___y_5271_);
return v_res_5278_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4(lean_object* v_00_u03b2_5279_, lean_object* v_x_5280_, size_t v_x_5281_, size_t v_x_5282_, lean_object* v_x_5283_, lean_object* v_x_5284_){
_start:
{
lean_object* v___x_5285_; 
v___x_5285_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4___redArg(v_x_5280_, v_x_5281_, v_x_5282_, v_x_5283_, v_x_5284_);
return v___x_5285_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b2_5286_, lean_object* v_x_5287_, lean_object* v_x_5288_, lean_object* v_x_5289_, lean_object* v_x_5290_, lean_object* v_x_5291_){
_start:
{
size_t v_x_48142__boxed_5292_; size_t v_x_48143__boxed_5293_; lean_object* v_res_5294_; 
v_x_48142__boxed_5292_ = lean_unbox_usize(v_x_5288_);
lean_dec(v_x_5288_);
v_x_48143__boxed_5293_ = lean_unbox_usize(v_x_5289_);
lean_dec(v_x_5289_);
v_res_5294_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4(v_00_u03b2_5286_, v_x_5287_, v_x_48142__boxed_5292_, v_x_48143__boxed_5293_, v_x_5290_, v_x_5291_);
return v_res_5294_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4_spec__8(lean_object* v_00_u03b2_5295_, lean_object* v_n_5296_, lean_object* v_k_5297_, lean_object* v_v_5298_){
_start:
{
lean_object* v___x_5299_; 
v___x_5299_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4_spec__8___redArg(v_n_5296_, v_k_5297_, v_v_5298_);
return v___x_5299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4_spec__9(lean_object* v_00_u03b2_5300_, size_t v_depth_5301_, lean_object* v_keys_5302_, lean_object* v_vals_5303_, lean_object* v_heq_5304_, lean_object* v_i_5305_, lean_object* v_entries_5306_){
_start:
{
lean_object* v___x_5307_; 
v___x_5307_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4_spec__9___redArg(v_depth_5301_, v_keys_5302_, v_vals_5303_, v_i_5305_, v_entries_5306_);
return v___x_5307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4_spec__9___boxed(lean_object* v_00_u03b2_5308_, lean_object* v_depth_5309_, lean_object* v_keys_5310_, lean_object* v_vals_5311_, lean_object* v_heq_5312_, lean_object* v_i_5313_, lean_object* v_entries_5314_){
_start:
{
size_t v_depth_boxed_5315_; lean_object* v_res_5316_; 
v_depth_boxed_5315_ = lean_unbox_usize(v_depth_5309_);
lean_dec(v_depth_5309_);
v_res_5316_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4_spec__9(v_00_u03b2_5308_, v_depth_boxed_5315_, v_keys_5310_, v_vals_5311_, v_heq_5312_, v_i_5313_, v_entries_5314_);
lean_dec_ref(v_vals_5311_);
lean_dec_ref(v_keys_5310_);
return v_res_5316_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4_spec__8_spec__10(lean_object* v_00_u03b2_5317_, lean_object* v_x_5318_, lean_object* v_x_5319_, lean_object* v_x_5320_, lean_object* v_x_5321_){
_start:
{
lean_object* v___x_5322_; 
v___x_5322_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0_spec__0_spec__4_spec__8_spec__10___redArg(v_x_5318_, v_x_5319_, v_x_5320_, v_x_5321_);
return v___x_5322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0(lean_object* v_a_5323_, uint8_t v___x_5324_, lean_object* v___y_5325_, lean_object* v___y_5326_, lean_object* v___y_5327_, lean_object* v___y_5328_, lean_object* v___y_5329_, lean_object* v___y_5330_){
_start:
{
lean_object* v___x_5332_; 
v___x_5332_ = l_Lean_MVarId_refl(v_a_5323_, v___x_5324_, v___y_5327_, v___y_5328_, v___y_5329_, v___y_5330_);
return v___x_5332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0___boxed(lean_object* v_a_5333_, lean_object* v___x_5334_, lean_object* v___y_5335_, lean_object* v___y_5336_, lean_object* v___y_5337_, lean_object* v___y_5338_, lean_object* v___y_5339_, lean_object* v___y_5340_, lean_object* v___y_5341_){
_start:
{
uint8_t v___x_21137__boxed_5342_; lean_object* v_res_5343_; 
v___x_21137__boxed_5342_ = lean_unbox(v___x_5334_);
v_res_5343_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0(v_a_5333_, v___x_21137__boxed_5342_, v___y_5335_, v___y_5336_, v___y_5337_, v___y_5338_, v___y_5339_, v___y_5340_);
lean_dec(v___y_5336_);
lean_dec_ref(v___y_5335_);
return v_res_5343_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(lean_object* v_cls_5344_, lean_object* v_msg_5345_, lean_object* v___y_5346_, lean_object* v___y_5347_, lean_object* v___y_5348_, lean_object* v___y_5349_){
_start:
{
lean_object* v_ref_5351_; lean_object* v___x_5352_; lean_object* v_a_5353_; lean_object* v___x_5355_; uint8_t v_isShared_5356_; uint8_t v_isSharedCheck_5397_; 
v_ref_5351_ = lean_ctor_get(v___y_5348_, 5);
v___x_5352_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1_spec__1(v_msg_5345_, v___y_5346_, v___y_5347_, v___y_5348_, v___y_5349_);
v_a_5353_ = lean_ctor_get(v___x_5352_, 0);
v_isSharedCheck_5397_ = !lean_is_exclusive(v___x_5352_);
if (v_isSharedCheck_5397_ == 0)
{
v___x_5355_ = v___x_5352_;
v_isShared_5356_ = v_isSharedCheck_5397_;
goto v_resetjp_5354_;
}
else
{
lean_inc(v_a_5353_);
lean_dec(v___x_5352_);
v___x_5355_ = lean_box(0);
v_isShared_5356_ = v_isSharedCheck_5397_;
goto v_resetjp_5354_;
}
v_resetjp_5354_:
{
lean_object* v___x_5357_; lean_object* v_traceState_5358_; lean_object* v_env_5359_; lean_object* v_nextMacroScope_5360_; lean_object* v_ngen_5361_; lean_object* v_auxDeclNGen_5362_; lean_object* v_cache_5363_; lean_object* v_messages_5364_; lean_object* v_infoState_5365_; lean_object* v_snapshotTasks_5366_; lean_object* v___x_5368_; uint8_t v_isShared_5369_; uint8_t v_isSharedCheck_5396_; 
v___x_5357_ = lean_st_ref_take(v___y_5349_);
v_traceState_5358_ = lean_ctor_get(v___x_5357_, 4);
v_env_5359_ = lean_ctor_get(v___x_5357_, 0);
v_nextMacroScope_5360_ = lean_ctor_get(v___x_5357_, 1);
v_ngen_5361_ = lean_ctor_get(v___x_5357_, 2);
v_auxDeclNGen_5362_ = lean_ctor_get(v___x_5357_, 3);
v_cache_5363_ = lean_ctor_get(v___x_5357_, 5);
v_messages_5364_ = lean_ctor_get(v___x_5357_, 6);
v_infoState_5365_ = lean_ctor_get(v___x_5357_, 7);
v_snapshotTasks_5366_ = lean_ctor_get(v___x_5357_, 8);
v_isSharedCheck_5396_ = !lean_is_exclusive(v___x_5357_);
if (v_isSharedCheck_5396_ == 0)
{
v___x_5368_ = v___x_5357_;
v_isShared_5369_ = v_isSharedCheck_5396_;
goto v_resetjp_5367_;
}
else
{
lean_inc(v_snapshotTasks_5366_);
lean_inc(v_infoState_5365_);
lean_inc(v_messages_5364_);
lean_inc(v_cache_5363_);
lean_inc(v_traceState_5358_);
lean_inc(v_auxDeclNGen_5362_);
lean_inc(v_ngen_5361_);
lean_inc(v_nextMacroScope_5360_);
lean_inc(v_env_5359_);
lean_dec(v___x_5357_);
v___x_5368_ = lean_box(0);
v_isShared_5369_ = v_isSharedCheck_5396_;
goto v_resetjp_5367_;
}
v_resetjp_5367_:
{
uint64_t v_tid_5370_; lean_object* v_traces_5371_; lean_object* v___x_5373_; uint8_t v_isShared_5374_; uint8_t v_isSharedCheck_5395_; 
v_tid_5370_ = lean_ctor_get_uint64(v_traceState_5358_, sizeof(void*)*1);
v_traces_5371_ = lean_ctor_get(v_traceState_5358_, 0);
v_isSharedCheck_5395_ = !lean_is_exclusive(v_traceState_5358_);
if (v_isSharedCheck_5395_ == 0)
{
v___x_5373_ = v_traceState_5358_;
v_isShared_5374_ = v_isSharedCheck_5395_;
goto v_resetjp_5372_;
}
else
{
lean_inc(v_traces_5371_);
lean_dec(v_traceState_5358_);
v___x_5373_ = lean_box(0);
v_isShared_5374_ = v_isSharedCheck_5395_;
goto v_resetjp_5372_;
}
v_resetjp_5372_:
{
lean_object* v___x_5375_; double v___x_5376_; uint8_t v___x_5377_; lean_object* v___x_5378_; lean_object* v___x_5379_; lean_object* v___x_5380_; lean_object* v___x_5381_; lean_object* v___x_5382_; lean_object* v___x_5383_; lean_object* v___x_5385_; 
v___x_5375_ = lean_box(0);
v___x_5376_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__0);
v___x_5377_ = 0;
v___x_5378_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__1));
v___x_5379_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_5379_, 0, v_cls_5344_);
lean_ctor_set(v___x_5379_, 1, v___x_5375_);
lean_ctor_set(v___x_5379_, 2, v___x_5378_);
lean_ctor_set_float(v___x_5379_, sizeof(void*)*3, v___x_5376_);
lean_ctor_set_float(v___x_5379_, sizeof(void*)*3 + 8, v___x_5376_);
lean_ctor_set_uint8(v___x_5379_, sizeof(void*)*3 + 16, v___x_5377_);
v___x_5380_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__2));
v___x_5381_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_5381_, 0, v___x_5379_);
lean_ctor_set(v___x_5381_, 1, v_a_5353_);
lean_ctor_set(v___x_5381_, 2, v___x_5380_);
lean_inc(v_ref_5351_);
v___x_5382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5382_, 0, v_ref_5351_);
lean_ctor_set(v___x_5382_, 1, v___x_5381_);
v___x_5383_ = l_Lean_PersistentArray_push___redArg(v_traces_5371_, v___x_5382_);
if (v_isShared_5374_ == 0)
{
lean_ctor_set(v___x_5373_, 0, v___x_5383_);
v___x_5385_ = v___x_5373_;
goto v_reusejp_5384_;
}
else
{
lean_object* v_reuseFailAlloc_5394_; 
v_reuseFailAlloc_5394_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5394_, 0, v___x_5383_);
lean_ctor_set_uint64(v_reuseFailAlloc_5394_, sizeof(void*)*1, v_tid_5370_);
v___x_5385_ = v_reuseFailAlloc_5394_;
goto v_reusejp_5384_;
}
v_reusejp_5384_:
{
lean_object* v___x_5387_; 
if (v_isShared_5369_ == 0)
{
lean_ctor_set(v___x_5368_, 4, v___x_5385_);
v___x_5387_ = v___x_5368_;
goto v_reusejp_5386_;
}
else
{
lean_object* v_reuseFailAlloc_5393_; 
v_reuseFailAlloc_5393_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5393_, 0, v_env_5359_);
lean_ctor_set(v_reuseFailAlloc_5393_, 1, v_nextMacroScope_5360_);
lean_ctor_set(v_reuseFailAlloc_5393_, 2, v_ngen_5361_);
lean_ctor_set(v_reuseFailAlloc_5393_, 3, v_auxDeclNGen_5362_);
lean_ctor_set(v_reuseFailAlloc_5393_, 4, v___x_5385_);
lean_ctor_set(v_reuseFailAlloc_5393_, 5, v_cache_5363_);
lean_ctor_set(v_reuseFailAlloc_5393_, 6, v_messages_5364_);
lean_ctor_set(v_reuseFailAlloc_5393_, 7, v_infoState_5365_);
lean_ctor_set(v_reuseFailAlloc_5393_, 8, v_snapshotTasks_5366_);
v___x_5387_ = v_reuseFailAlloc_5393_;
goto v_reusejp_5386_;
}
v_reusejp_5386_:
{
lean_object* v___x_5388_; lean_object* v___x_5389_; lean_object* v___x_5391_; 
v___x_5388_ = lean_st_ref_set(v___y_5349_, v___x_5387_);
v___x_5389_ = lean_box(0);
if (v_isShared_5356_ == 0)
{
lean_ctor_set(v___x_5355_, 0, v___x_5389_);
v___x_5391_ = v___x_5355_;
goto v_reusejp_5390_;
}
else
{
lean_object* v_reuseFailAlloc_5392_; 
v_reuseFailAlloc_5392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5392_, 0, v___x_5389_);
v___x_5391_ = v_reuseFailAlloc_5392_;
goto v_reusejp_5390_;
}
v_reusejp_5390_:
{
return v___x_5391_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg___boxed(lean_object* v_cls_5398_, lean_object* v_msg_5399_, lean_object* v___y_5400_, lean_object* v___y_5401_, lean_object* v___y_5402_, lean_object* v___y_5403_, lean_object* v___y_5404_){
_start:
{
lean_object* v_res_5405_; 
v_res_5405_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(v_cls_5398_, v_msg_5399_, v___y_5400_, v___y_5401_, v___y_5402_, v___y_5403_);
lean_dec(v___y_5403_);
lean_dec_ref(v___y_5402_);
lean_dec(v___y_5401_);
lean_dec_ref(v___y_5400_);
return v_res_5405_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(lean_object* v_msg_5406_, lean_object* v___y_5407_, lean_object* v___y_5408_, lean_object* v___y_5409_, lean_object* v___y_5410_){
_start:
{
lean_object* v_ref_5412_; lean_object* v___x_5413_; lean_object* v_a_5414_; lean_object* v___x_5416_; uint8_t v_isShared_5417_; uint8_t v_isSharedCheck_5422_; 
v_ref_5412_ = lean_ctor_get(v___y_5409_, 5);
v___x_5413_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1_spec__1(v_msg_5406_, v___y_5407_, v___y_5408_, v___y_5409_, v___y_5410_);
v_a_5414_ = lean_ctor_get(v___x_5413_, 0);
v_isSharedCheck_5422_ = !lean_is_exclusive(v___x_5413_);
if (v_isSharedCheck_5422_ == 0)
{
v___x_5416_ = v___x_5413_;
v_isShared_5417_ = v_isSharedCheck_5422_;
goto v_resetjp_5415_;
}
else
{
lean_inc(v_a_5414_);
lean_dec(v___x_5413_);
v___x_5416_ = lean_box(0);
v_isShared_5417_ = v_isSharedCheck_5422_;
goto v_resetjp_5415_;
}
v_resetjp_5415_:
{
lean_object* v___x_5418_; lean_object* v___x_5420_; 
lean_inc(v_ref_5412_);
v___x_5418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5418_, 0, v_ref_5412_);
lean_ctor_set(v___x_5418_, 1, v_a_5414_);
if (v_isShared_5417_ == 0)
{
lean_ctor_set_tag(v___x_5416_, 1);
lean_ctor_set(v___x_5416_, 0, v___x_5418_);
v___x_5420_ = v___x_5416_;
goto v_reusejp_5419_;
}
else
{
lean_object* v_reuseFailAlloc_5421_; 
v_reuseFailAlloc_5421_ = lean_alloc_ctor(1, 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg___boxed(lean_object* v_msg_5423_, lean_object* v___y_5424_, lean_object* v___y_5425_, lean_object* v___y_5426_, lean_object* v___y_5427_, lean_object* v___y_5428_){
_start:
{
lean_object* v_res_5429_; 
v_res_5429_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v_msg_5423_, v___y_5424_, v___y_5425_, v___y_5426_, v___y_5427_);
lean_dec(v___y_5427_);
lean_dec_ref(v___y_5426_);
lean_dec(v___y_5425_);
lean_dec_ref(v___y_5424_);
return v_res_5429_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1(void){
_start:
{
lean_object* v___x_5431_; lean_object* v___x_5432_; 
v___x_5431_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__0));
v___x_5432_ = l_Lean_stringToMessageData(v___x_5431_);
return v___x_5432_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3(void){
_start:
{
lean_object* v___x_5434_; lean_object* v___x_5435_; 
v___x_5434_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__2));
v___x_5435_ = l_Lean_stringToMessageData(v___x_5434_);
return v___x_5435_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6(void){
_start:
{
lean_object* v___x_5439_; lean_object* v___x_5440_; 
v___x_5439_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__5));
v___x_5440_ = l_Lean_stringToMessageData(v___x_5439_);
return v___x_5440_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8(void){
_start:
{
lean_object* v___x_5442_; lean_object* v___x_5443_; 
v___x_5442_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__7));
v___x_5443_ = l_Lean_stringToMessageData(v___x_5442_);
return v___x_5443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1(lean_object* v_m_5444_, lean_object* v___x_5445_, lean_object* v_cls_5446_, lean_object* v___y_5447_, lean_object* v___y_5448_, lean_object* v___y_5449_, lean_object* v___y_5450_, lean_object* v___y_5451_, lean_object* v___y_5452_){
_start:
{
lean_object* v_e_5455_; lean_object* v_onTrue_5456_; lean_object* v___y_5457_; lean_object* v___y_5458_; lean_object* v___y_5459_; lean_object* v___y_5460_; lean_object* v___y_5461_; lean_object* v___y_5462_; lean_object* v___x_5492_; 
lean_inc(v___y_5452_);
lean_inc_ref(v___y_5451_);
lean_inc(v___y_5450_);
lean_inc_ref(v___y_5449_);
v___x_5492_ = l_Lean_Meta_Sym_preprocessMVar(v_m_5444_, v___y_5447_, v___y_5448_, v___y_5449_, v___y_5450_, v___y_5451_, v___y_5452_);
if (lean_obj_tag(v___x_5492_) == 0)
{
lean_object* v_a_5493_; lean_object* v___x_5494_; 
v_a_5493_ = lean_ctor_get(v___x_5492_, 0);
lean_inc(v_a_5493_);
lean_dec_ref(v___x_5492_);
lean_inc(v_a_5493_);
v___x_5494_ = l_Lean_MVarId_getType(v_a_5493_, v___y_5449_, v___y_5450_, v___y_5451_, v___y_5452_);
if (lean_obj_tag(v___x_5494_) == 0)
{
lean_object* v_a_5495_; lean_object* v___x_5496_; lean_object* v___x_5497_; uint8_t v___x_5498_; 
v_a_5495_ = lean_ctor_get(v___x_5494_, 0);
lean_inc(v_a_5495_);
lean_dec_ref(v___x_5494_);
v___x_5496_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__4));
v___x_5497_ = lean_unsigned_to_nat(3u);
v___x_5498_ = l_Lean_Expr_isAppOfArity(v_a_5495_, v___x_5496_, v___x_5497_);
if (v___x_5498_ == 0)
{
lean_object* v___x_5499_; lean_object* v___x_5500_; lean_object* v___x_5501_; lean_object* v___x_5502_; 
lean_dec(v_a_5493_);
lean_dec(v___y_5448_);
lean_dec_ref(v___y_5447_);
lean_dec(v_cls_5446_);
lean_dec_ref(v___x_5445_);
v___x_5499_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6);
v___x_5500_ = l_Lean_indentExpr(v_a_5495_);
v___x_5501_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5501_, 0, v___x_5499_);
lean_ctor_set(v___x_5501_, 1, v___x_5500_);
v___x_5502_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_5501_, v___y_5449_, v___y_5450_, v___y_5451_, v___y_5452_);
lean_dec(v___y_5452_);
lean_dec_ref(v___y_5451_);
lean_dec(v___y_5450_);
lean_dec_ref(v___y_5449_);
return v___x_5502_;
}
else
{
lean_object* v___x_5503_; lean_object* v___x_5504_; lean_object* v___x_5505_; 
v___x_5503_ = l_Lean_Expr_appFn_x21(v_a_5495_);
lean_dec(v_a_5495_);
v___x_5504_ = l_Lean_Expr_appArg_x21(v___x_5503_);
lean_dec_ref(v___x_5503_);
lean_inc(v___y_5452_);
lean_inc_ref(v___y_5451_);
lean_inc(v___y_5450_);
lean_inc_ref(v___y_5449_);
lean_inc(v___y_5448_);
lean_inc_ref(v___y_5447_);
lean_inc_ref(v___x_5504_);
v___x_5505_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_5504_, v___x_5445_, v___y_5447_, v___y_5448_, v___y_5449_, v___y_5450_, v___y_5451_, v___y_5452_);
if (lean_obj_tag(v___x_5505_) == 0)
{
lean_object* v_a_5506_; lean_object* v___x_5507_; lean_object* v_a_5508_; lean_object* v___x_5509_; lean_object* v___f_5510_; lean_object* v___y_5512_; lean_object* v___y_5513_; lean_object* v___y_5514_; lean_object* v___y_5515_; lean_object* v___y_5516_; lean_object* v___y_5517_; uint8_t v___x_5521_; 
v_a_5506_ = lean_ctor_get(v___x_5505_, 0);
lean_inc(v_a_5506_);
lean_dec_ref(v___x_5505_);
lean_inc(v_cls_5446_);
v___x_5507_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__1___redArg(v_cls_5446_, v___y_5451_);
v_a_5508_ = lean_ctor_get(v___x_5507_, 0);
lean_inc(v_a_5508_);
lean_dec_ref(v___x_5507_);
v___x_5509_ = lean_box(v___x_5498_);
lean_inc(v_a_5493_);
v___f_5510_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5510_, 0, v_a_5493_);
lean_closure_set(v___f_5510_, 1, v___x_5509_);
v___x_5521_ = lean_unbox(v_a_5508_);
lean_dec(v_a_5508_);
if (v___x_5521_ == 0)
{
lean_dec(v_cls_5446_);
v___y_5512_ = v___y_5447_;
v___y_5513_ = v___y_5448_;
v___y_5514_ = v___y_5449_;
v___y_5515_ = v___y_5450_;
v___y_5516_ = v___y_5451_;
v___y_5517_ = v___y_5452_;
goto v___jp_5511_;
}
else
{
lean_object* v___x_5522_; lean_object* v___x_5523_; lean_object* v___x_5524_; lean_object* v___x_5525_; lean_object* v___x_5526_; lean_object* v___x_5527_; lean_object* v___x_5528_; lean_object* v___x_5529_; lean_object* v___x_5530_; 
v___x_5522_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8);
lean_inc_ref(v___x_5504_);
v___x_5523_ = l_Lean_indentExpr(v___x_5504_);
v___x_5524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5524_, 0, v___x_5522_);
lean_ctor_set(v___x_5524_, 1, v___x_5523_);
v___x_5525_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7);
v___x_5526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5526_, 0, v___x_5524_);
lean_ctor_set(v___x_5526_, 1, v___x_5525_);
v___x_5527_ = l_Lean_Meta_Sym_Simp_Result_getResultExpr(v___x_5504_, v_a_5506_);
v___x_5528_ = l_Lean_indentExpr(v___x_5527_);
v___x_5529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5529_, 0, v___x_5526_);
lean_ctor_set(v___x_5529_, 1, v___x_5528_);
v___x_5530_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(v_cls_5446_, v___x_5529_, v___y_5449_, v___y_5450_, v___y_5451_, v___y_5452_);
if (lean_obj_tag(v___x_5530_) == 0)
{
lean_dec_ref(v___x_5530_);
v___y_5512_ = v___y_5447_;
v___y_5513_ = v___y_5448_;
v___y_5514_ = v___y_5449_;
v___y_5515_ = v___y_5450_;
v___y_5516_ = v___y_5451_;
v___y_5517_ = v___y_5452_;
goto v___jp_5511_;
}
else
{
lean_dec_ref(v___f_5510_);
lean_dec(v_a_5506_);
lean_dec_ref(v___x_5504_);
lean_dec(v_a_5493_);
lean_dec(v___y_5452_);
lean_dec_ref(v___y_5451_);
lean_dec(v___y_5450_);
lean_dec_ref(v___y_5449_);
lean_dec(v___y_5448_);
lean_dec_ref(v___y_5447_);
return v___x_5530_;
}
}
v___jp_5511_:
{
if (lean_obj_tag(v_a_5506_) == 0)
{
lean_dec_ref(v_a_5506_);
lean_dec(v_a_5493_);
v_e_5455_ = v___x_5504_;
v_onTrue_5456_ = v___f_5510_;
v___y_5457_ = v___y_5512_;
v___y_5458_ = v___y_5513_;
v___y_5459_ = v___y_5514_;
v___y_5460_ = v___y_5515_;
v___y_5461_ = v___y_5516_;
v___y_5462_ = v___y_5517_;
goto v___jp_5454_;
}
else
{
lean_object* v_e_x27_5518_; lean_object* v_proof_5519_; lean_object* v___x_5520_; 
lean_dec_ref(v___f_5510_);
lean_dec_ref(v___x_5504_);
v_e_x27_5518_ = lean_ctor_get(v_a_5506_, 0);
lean_inc_ref(v_e_x27_5518_);
v_proof_5519_ = lean_ctor_get(v_a_5506_, 1);
lean_inc_ref(v_proof_5519_);
lean_dec_ref(v_a_5506_);
v___x_5520_ = lean_alloc_closure((void*)(l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0___boxed), 9, 2);
lean_closure_set(v___x_5520_, 0, v_a_5493_);
lean_closure_set(v___x_5520_, 1, v_proof_5519_);
v_e_5455_ = v_e_x27_5518_;
v_onTrue_5456_ = v___x_5520_;
v___y_5457_ = v___y_5512_;
v___y_5458_ = v___y_5513_;
v___y_5459_ = v___y_5514_;
v___y_5460_ = v___y_5515_;
v___y_5461_ = v___y_5516_;
v___y_5462_ = v___y_5517_;
goto v___jp_5454_;
}
}
}
else
{
lean_object* v_a_5531_; lean_object* v___x_5533_; uint8_t v_isShared_5534_; uint8_t v_isSharedCheck_5538_; 
lean_dec_ref(v___x_5504_);
lean_dec(v_a_5493_);
lean_dec(v___y_5452_);
lean_dec_ref(v___y_5451_);
lean_dec(v___y_5450_);
lean_dec_ref(v___y_5449_);
lean_dec(v___y_5448_);
lean_dec_ref(v___y_5447_);
lean_dec(v_cls_5446_);
v_a_5531_ = lean_ctor_get(v___x_5505_, 0);
v_isSharedCheck_5538_ = !lean_is_exclusive(v___x_5505_);
if (v_isSharedCheck_5538_ == 0)
{
v___x_5533_ = v___x_5505_;
v_isShared_5534_ = v_isSharedCheck_5538_;
goto v_resetjp_5532_;
}
else
{
lean_inc(v_a_5531_);
lean_dec(v___x_5505_);
v___x_5533_ = lean_box(0);
v_isShared_5534_ = v_isSharedCheck_5538_;
goto v_resetjp_5532_;
}
v_resetjp_5532_:
{
lean_object* v___x_5536_; 
if (v_isShared_5534_ == 0)
{
v___x_5536_ = v___x_5533_;
goto v_reusejp_5535_;
}
else
{
lean_object* v_reuseFailAlloc_5537_; 
v_reuseFailAlloc_5537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5537_, 0, v_a_5531_);
v___x_5536_ = v_reuseFailAlloc_5537_;
goto v_reusejp_5535_;
}
v_reusejp_5535_:
{
return v___x_5536_;
}
}
}
}
}
else
{
lean_object* v_a_5539_; lean_object* v___x_5541_; uint8_t v_isShared_5542_; uint8_t v_isSharedCheck_5546_; 
lean_dec(v_a_5493_);
lean_dec(v___y_5452_);
lean_dec_ref(v___y_5451_);
lean_dec(v___y_5450_);
lean_dec_ref(v___y_5449_);
lean_dec(v___y_5448_);
lean_dec_ref(v___y_5447_);
lean_dec(v_cls_5446_);
lean_dec_ref(v___x_5445_);
v_a_5539_ = lean_ctor_get(v___x_5494_, 0);
v_isSharedCheck_5546_ = !lean_is_exclusive(v___x_5494_);
if (v_isSharedCheck_5546_ == 0)
{
v___x_5541_ = v___x_5494_;
v_isShared_5542_ = v_isSharedCheck_5546_;
goto v_resetjp_5540_;
}
else
{
lean_inc(v_a_5539_);
lean_dec(v___x_5494_);
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
else
{
lean_object* v_a_5547_; lean_object* v___x_5549_; uint8_t v_isShared_5550_; uint8_t v_isSharedCheck_5554_; 
lean_dec(v___y_5452_);
lean_dec_ref(v___y_5451_);
lean_dec(v___y_5450_);
lean_dec_ref(v___y_5449_);
lean_dec(v___y_5448_);
lean_dec_ref(v___y_5447_);
lean_dec(v_cls_5446_);
lean_dec_ref(v___x_5445_);
v_a_5547_ = lean_ctor_get(v___x_5492_, 0);
v_isSharedCheck_5554_ = !lean_is_exclusive(v___x_5492_);
if (v_isSharedCheck_5554_ == 0)
{
v___x_5549_ = v___x_5492_;
v_isShared_5550_ = v_isSharedCheck_5554_;
goto v_resetjp_5548_;
}
else
{
lean_inc(v_a_5547_);
lean_dec(v___x_5492_);
v___x_5549_ = lean_box(0);
v_isShared_5550_ = v_isSharedCheck_5554_;
goto v_resetjp_5548_;
}
v_resetjp_5548_:
{
lean_object* v___x_5552_; 
if (v_isShared_5550_ == 0)
{
v___x_5552_ = v___x_5549_;
goto v_reusejp_5551_;
}
else
{
lean_object* v_reuseFailAlloc_5553_; 
v_reuseFailAlloc_5553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5553_, 0, v_a_5547_);
v___x_5552_ = v_reuseFailAlloc_5553_;
goto v_reusejp_5551_;
}
v_reusejp_5551_:
{
return v___x_5552_;
}
}
}
v___jp_5454_:
{
lean_object* v___x_5463_; 
v___x_5463_ = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(v_e_5455_, v___y_5457_);
if (lean_obj_tag(v___x_5463_) == 0)
{
lean_object* v_a_5464_; uint8_t v___x_5465_; 
v_a_5464_ = lean_ctor_get(v___x_5463_, 0);
lean_inc(v_a_5464_);
lean_dec_ref(v___x_5463_);
v___x_5465_ = lean_unbox(v_a_5464_);
lean_dec(v_a_5464_);
if (v___x_5465_ == 0)
{
lean_object* v___x_5466_; 
lean_dec(v___y_5458_);
lean_dec_ref(v_onTrue_5456_);
v___x_5466_ = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(v_e_5455_, v___y_5457_);
lean_dec_ref(v___y_5457_);
if (lean_obj_tag(v___x_5466_) == 0)
{
lean_object* v_a_5467_; uint8_t v___x_5468_; 
v_a_5467_ = lean_ctor_get(v___x_5466_, 0);
lean_inc(v_a_5467_);
lean_dec_ref(v___x_5466_);
v___x_5468_ = lean_unbox(v_a_5467_);
lean_dec(v_a_5467_);
if (v___x_5468_ == 0)
{
lean_object* v___x_5469_; lean_object* v___x_5470_; lean_object* v___x_5471_; lean_object* v___x_5472_; 
v___x_5469_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1);
v___x_5470_ = l_Lean_indentExpr(v_e_5455_);
v___x_5471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5471_, 0, v___x_5469_);
lean_ctor_set(v___x_5471_, 1, v___x_5470_);
v___x_5472_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_5471_, v___y_5459_, v___y_5460_, v___y_5461_, v___y_5462_);
lean_dec(v___y_5462_);
lean_dec_ref(v___y_5461_);
lean_dec(v___y_5460_);
lean_dec_ref(v___y_5459_);
return v___x_5472_;
}
else
{
lean_object* v___x_5473_; lean_object* v___x_5474_; 
lean_dec_ref(v_e_5455_);
v___x_5473_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3);
v___x_5474_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_5473_, v___y_5459_, v___y_5460_, v___y_5461_, v___y_5462_);
lean_dec(v___y_5462_);
lean_dec_ref(v___y_5461_);
lean_dec(v___y_5460_);
lean_dec_ref(v___y_5459_);
return v___x_5474_;
}
}
else
{
lean_object* v_a_5475_; lean_object* v___x_5477_; uint8_t v_isShared_5478_; uint8_t v_isSharedCheck_5482_; 
lean_dec(v___y_5462_);
lean_dec_ref(v___y_5461_);
lean_dec(v___y_5460_);
lean_dec_ref(v___y_5459_);
lean_dec_ref(v_e_5455_);
v_a_5475_ = lean_ctor_get(v___x_5466_, 0);
v_isSharedCheck_5482_ = !lean_is_exclusive(v___x_5466_);
if (v_isSharedCheck_5482_ == 0)
{
v___x_5477_ = v___x_5466_;
v_isShared_5478_ = v_isSharedCheck_5482_;
goto v_resetjp_5476_;
}
else
{
lean_inc(v_a_5475_);
lean_dec(v___x_5466_);
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
}
else
{
lean_object* v___x_5483_; 
lean_dec_ref(v_e_5455_);
v___x_5483_ = lean_apply_7(v_onTrue_5456_, v___y_5457_, v___y_5458_, v___y_5459_, v___y_5460_, v___y_5461_, v___y_5462_, lean_box(0));
return v___x_5483_;
}
}
else
{
lean_object* v_a_5484_; lean_object* v___x_5486_; uint8_t v_isShared_5487_; uint8_t v_isSharedCheck_5491_; 
lean_dec(v___y_5462_);
lean_dec_ref(v___y_5461_);
lean_dec(v___y_5460_);
lean_dec_ref(v___y_5459_);
lean_dec(v___y_5458_);
lean_dec_ref(v___y_5457_);
lean_dec_ref(v_onTrue_5456_);
lean_dec_ref(v_e_5455_);
v_a_5484_ = lean_ctor_get(v___x_5463_, 0);
v_isSharedCheck_5491_ = !lean_is_exclusive(v___x_5463_);
if (v_isSharedCheck_5491_ == 0)
{
v___x_5486_ = v___x_5463_;
v_isShared_5487_ = v_isSharedCheck_5491_;
goto v_resetjp_5485_;
}
else
{
lean_inc(v_a_5484_);
lean_dec(v___x_5463_);
v___x_5486_ = lean_box(0);
v_isShared_5487_ = v_isSharedCheck_5491_;
goto v_resetjp_5485_;
}
v_resetjp_5485_:
{
lean_object* v___x_5489_; 
if (v_isShared_5487_ == 0)
{
v___x_5489_ = v___x_5486_;
goto v_reusejp_5488_;
}
else
{
lean_object* v_reuseFailAlloc_5490_; 
v_reuseFailAlloc_5490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5490_, 0, v_a_5484_);
v___x_5489_ = v_reuseFailAlloc_5490_;
goto v_reusejp_5488_;
}
v_reusejp_5488_:
{
return v___x_5489_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___boxed(lean_object* v_m_5555_, lean_object* v___x_5556_, lean_object* v_cls_5557_, lean_object* v___y_5558_, lean_object* v___y_5559_, lean_object* v___y_5560_, lean_object* v___y_5561_, lean_object* v___y_5562_, lean_object* v___y_5563_, lean_object* v___y_5564_){
_start:
{
lean_object* v_res_5565_; 
v_res_5565_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1(v_m_5555_, v___x_5556_, v_cls_5557_, v___y_5558_, v___y_5559_, v___y_5560_, v___y_5561_, v___y_5562_, v___y_5563_);
return v_res_5565_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__1(void){
_start:
{
lean_object* v___x_5567_; lean_object* v___x_5568_; 
v___x_5567_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__0));
v___x_5568_ = l_Lean_stringToMessageData(v___x_5567_);
return v___x_5568_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__3(void){
_start:
{
lean_object* v___x_5570_; lean_object* v___x_5571_; 
v___x_5570_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__2));
v___x_5571_ = l_Lean_stringToMessageData(v___x_5570_);
return v___x_5571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2(lean_object* v_x_5572_, lean_object* v___y_5573_, lean_object* v___y_5574_, lean_object* v___y_5575_, lean_object* v___y_5576_){
_start:
{
if (lean_obj_tag(v_x_5572_) == 0)
{
lean_object* v_a_5578_; lean_object* v___x_5580_; uint8_t v_isShared_5581_; uint8_t v_isSharedCheck_5588_; 
v_a_5578_ = lean_ctor_get(v_x_5572_, 0);
v_isSharedCheck_5588_ = !lean_is_exclusive(v_x_5572_);
if (v_isSharedCheck_5588_ == 0)
{
v___x_5580_ = v_x_5572_;
v_isShared_5581_ = v_isSharedCheck_5588_;
goto v_resetjp_5579_;
}
else
{
lean_inc(v_a_5578_);
lean_dec(v_x_5572_);
v___x_5580_ = lean_box(0);
v_isShared_5581_ = v_isSharedCheck_5588_;
goto v_resetjp_5579_;
}
v_resetjp_5579_:
{
lean_object* v___x_5582_; lean_object* v___x_5583_; lean_object* v___x_5584_; lean_object* v___x_5586_; 
v___x_5582_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__1);
v___x_5583_ = l_Lean_Exception_toMessageData(v_a_5578_);
v___x_5584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5584_, 0, v___x_5582_);
lean_ctor_set(v___x_5584_, 1, v___x_5583_);
if (v_isShared_5581_ == 0)
{
lean_ctor_set(v___x_5580_, 0, v___x_5584_);
v___x_5586_ = v___x_5580_;
goto v_reusejp_5585_;
}
else
{
lean_object* v_reuseFailAlloc_5587_; 
v_reuseFailAlloc_5587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5587_, 0, v___x_5584_);
v___x_5586_ = v_reuseFailAlloc_5587_;
goto v_reusejp_5585_;
}
v_reusejp_5585_:
{
return v___x_5586_;
}
}
}
else
{
lean_object* v___x_5590_; uint8_t v_isShared_5591_; uint8_t v_isSharedCheck_5596_; 
v_isSharedCheck_5596_ = !lean_is_exclusive(v_x_5572_);
if (v_isSharedCheck_5596_ == 0)
{
lean_object* v_unused_5597_; 
v_unused_5597_ = lean_ctor_get(v_x_5572_, 0);
lean_dec(v_unused_5597_);
v___x_5590_ = v_x_5572_;
v_isShared_5591_ = v_isSharedCheck_5596_;
goto v_resetjp_5589_;
}
else
{
lean_dec(v_x_5572_);
v___x_5590_ = lean_box(0);
v_isShared_5591_ = v_isSharedCheck_5596_;
goto v_resetjp_5589_;
}
v_resetjp_5589_:
{
lean_object* v___x_5592_; lean_object* v___x_5594_; 
v___x_5592_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__3, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__3);
if (v_isShared_5591_ == 0)
{
lean_ctor_set_tag(v___x_5590_, 0);
lean_ctor_set(v___x_5590_, 0, v___x_5592_);
v___x_5594_ = v___x_5590_;
goto v_reusejp_5593_;
}
else
{
lean_object* v_reuseFailAlloc_5595_; 
v_reuseFailAlloc_5595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5595_, 0, v___x_5592_);
v___x_5594_ = v_reuseFailAlloc_5595_;
goto v_reusejp_5593_;
}
v_reusejp_5593_:
{
return v___x_5594_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___boxed(lean_object* v_x_5598_, lean_object* v___y_5599_, lean_object* v___y_5600_, lean_object* v___y_5601_, lean_object* v___y_5602_, lean_object* v___y_5603_){
_start:
{
lean_object* v_res_5604_; 
v_res_5604_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2(v_x_5598_, v___y_5599_, v___y_5600_, v___y_5601_, v___y_5602_);
lean_dec(v___y_5602_);
lean_dec_ref(v___y_5601_);
lean_dec(v___y_5600_);
lean_dec_ref(v___y_5599_);
return v_res_5604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__3(lean_object* v_a_5605_, uint8_t v_hasTrace_5606_, lean_object* v___y_5607_, lean_object* v___y_5608_, lean_object* v___y_5609_, lean_object* v___y_5610_, lean_object* v___y_5611_, lean_object* v___y_5612_){
_start:
{
lean_object* v___x_5614_; 
v___x_5614_ = l_Lean_MVarId_refl(v_a_5605_, v_hasTrace_5606_, v___y_5609_, v___y_5610_, v___y_5611_, v___y_5612_);
return v___x_5614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__3___boxed(lean_object* v_a_5615_, lean_object* v_hasTrace_5616_, lean_object* v___y_5617_, lean_object* v___y_5618_, lean_object* v___y_5619_, lean_object* v___y_5620_, lean_object* v___y_5621_, lean_object* v___y_5622_, lean_object* v___y_5623_){
_start:
{
uint8_t v_hasTrace_boxed_5624_; lean_object* v_res_5625_; 
v_hasTrace_boxed_5624_ = lean_unbox(v_hasTrace_5616_);
v_res_5625_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__3(v_a_5615_, v_hasTrace_boxed_5624_, v___y_5617_, v___y_5618_, v___y_5619_, v___y_5620_, v___y_5621_, v___y_5622_);
lean_dec(v___y_5618_);
lean_dec_ref(v___y_5617_);
return v_res_5625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__4(lean_object* v_m_5626_, lean_object* v___x_5627_, lean_object* v_cls_5628_, uint8_t v_hasTrace_5629_, lean_object* v___y_5630_, lean_object* v___y_5631_, lean_object* v___y_5632_, lean_object* v___y_5633_, lean_object* v___y_5634_, lean_object* v___y_5635_){
_start:
{
lean_object* v_e_5638_; lean_object* v_onTrue_5639_; lean_object* v___y_5640_; lean_object* v___y_5641_; lean_object* v___y_5642_; lean_object* v___y_5643_; lean_object* v___y_5644_; lean_object* v___y_5645_; lean_object* v___x_5675_; 
lean_inc(v___y_5635_);
lean_inc_ref(v___y_5634_);
lean_inc(v___y_5633_);
lean_inc_ref(v___y_5632_);
v___x_5675_ = l_Lean_Meta_Sym_preprocessMVar(v_m_5626_, v___y_5630_, v___y_5631_, v___y_5632_, v___y_5633_, v___y_5634_, v___y_5635_);
if (lean_obj_tag(v___x_5675_) == 0)
{
lean_object* v_a_5676_; lean_object* v___x_5677_; 
v_a_5676_ = lean_ctor_get(v___x_5675_, 0);
lean_inc(v_a_5676_);
lean_dec_ref(v___x_5675_);
lean_inc(v_a_5676_);
v___x_5677_ = l_Lean_MVarId_getType(v_a_5676_, v___y_5632_, v___y_5633_, v___y_5634_, v___y_5635_);
if (lean_obj_tag(v___x_5677_) == 0)
{
lean_object* v_a_5678_; lean_object* v___x_5679_; lean_object* v___x_5680_; uint8_t v___x_5681_; 
v_a_5678_ = lean_ctor_get(v___x_5677_, 0);
lean_inc(v_a_5678_);
lean_dec_ref(v___x_5677_);
v___x_5679_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__4));
v___x_5680_ = lean_unsigned_to_nat(3u);
v___x_5681_ = l_Lean_Expr_isAppOfArity(v_a_5678_, v___x_5679_, v___x_5680_);
if (v___x_5681_ == 0)
{
lean_object* v___x_5682_; lean_object* v___x_5683_; lean_object* v___x_5684_; lean_object* v___x_5685_; 
lean_dec(v_a_5676_);
lean_dec(v___y_5631_);
lean_dec_ref(v___y_5630_);
lean_dec(v_cls_5628_);
lean_dec_ref(v___x_5627_);
v___x_5682_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6);
v___x_5683_ = l_Lean_indentExpr(v_a_5678_);
v___x_5684_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5684_, 0, v___x_5682_);
lean_ctor_set(v___x_5684_, 1, v___x_5683_);
v___x_5685_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_5684_, v___y_5632_, v___y_5633_, v___y_5634_, v___y_5635_);
lean_dec(v___y_5635_);
lean_dec_ref(v___y_5634_);
lean_dec(v___y_5633_);
lean_dec_ref(v___y_5632_);
return v___x_5685_;
}
else
{
lean_object* v___x_5686_; lean_object* v___x_5687_; lean_object* v___x_5688_; 
v___x_5686_ = l_Lean_Expr_appFn_x21(v_a_5678_);
lean_dec(v_a_5678_);
v___x_5687_ = l_Lean_Expr_appArg_x21(v___x_5686_);
lean_dec_ref(v___x_5686_);
lean_inc(v___y_5635_);
lean_inc_ref(v___y_5634_);
lean_inc(v___y_5633_);
lean_inc_ref(v___y_5632_);
lean_inc(v___y_5631_);
lean_inc_ref(v___y_5630_);
lean_inc_ref(v___x_5687_);
v___x_5688_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_5687_, v___x_5627_, v___y_5630_, v___y_5631_, v___y_5632_, v___y_5633_, v___y_5634_, v___y_5635_);
if (lean_obj_tag(v___x_5688_) == 0)
{
lean_object* v_a_5689_; lean_object* v___x_5690_; lean_object* v_a_5691_; lean_object* v___x_5692_; lean_object* v___f_5693_; lean_object* v___y_5695_; lean_object* v___y_5696_; lean_object* v___y_5697_; lean_object* v___y_5698_; lean_object* v___y_5699_; lean_object* v___y_5700_; uint8_t v___x_5704_; 
v_a_5689_ = lean_ctor_get(v___x_5688_, 0);
lean_inc(v_a_5689_);
lean_dec_ref(v___x_5688_);
lean_inc(v_cls_5628_);
v___x_5690_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__1___redArg(v_cls_5628_, v___y_5634_);
v_a_5691_ = lean_ctor_get(v___x_5690_, 0);
lean_inc(v_a_5691_);
lean_dec_ref(v___x_5690_);
v___x_5692_ = lean_box(v_hasTrace_5629_);
lean_inc(v_a_5676_);
v___f_5693_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__3___boxed), 9, 2);
lean_closure_set(v___f_5693_, 0, v_a_5676_);
lean_closure_set(v___f_5693_, 1, v___x_5692_);
v___x_5704_ = lean_unbox(v_a_5691_);
lean_dec(v_a_5691_);
if (v___x_5704_ == 0)
{
lean_dec(v_cls_5628_);
v___y_5695_ = v___y_5630_;
v___y_5696_ = v___y_5631_;
v___y_5697_ = v___y_5632_;
v___y_5698_ = v___y_5633_;
v___y_5699_ = v___y_5634_;
v___y_5700_ = v___y_5635_;
goto v___jp_5694_;
}
else
{
lean_object* v___x_5705_; lean_object* v___x_5706_; lean_object* v___x_5707_; lean_object* v___x_5708_; lean_object* v___x_5709_; lean_object* v___x_5710_; lean_object* v___x_5711_; lean_object* v___x_5712_; lean_object* v___x_5713_; 
v___x_5705_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8);
lean_inc_ref(v___x_5687_);
v___x_5706_ = l_Lean_indentExpr(v___x_5687_);
v___x_5707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5707_, 0, v___x_5705_);
lean_ctor_set(v___x_5707_, 1, v___x_5706_);
v___x_5708_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7);
v___x_5709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5709_, 0, v___x_5707_);
lean_ctor_set(v___x_5709_, 1, v___x_5708_);
v___x_5710_ = l_Lean_Meta_Sym_Simp_Result_getResultExpr(v___x_5687_, v_a_5689_);
v___x_5711_ = l_Lean_indentExpr(v___x_5710_);
v___x_5712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5712_, 0, v___x_5709_);
lean_ctor_set(v___x_5712_, 1, v___x_5711_);
v___x_5713_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(v_cls_5628_, v___x_5712_, v___y_5632_, v___y_5633_, v___y_5634_, v___y_5635_);
if (lean_obj_tag(v___x_5713_) == 0)
{
lean_dec_ref(v___x_5713_);
v___y_5695_ = v___y_5630_;
v___y_5696_ = v___y_5631_;
v___y_5697_ = v___y_5632_;
v___y_5698_ = v___y_5633_;
v___y_5699_ = v___y_5634_;
v___y_5700_ = v___y_5635_;
goto v___jp_5694_;
}
else
{
lean_dec_ref(v___f_5693_);
lean_dec(v_a_5689_);
lean_dec_ref(v___x_5687_);
lean_dec(v_a_5676_);
lean_dec(v___y_5635_);
lean_dec_ref(v___y_5634_);
lean_dec(v___y_5633_);
lean_dec_ref(v___y_5632_);
lean_dec(v___y_5631_);
lean_dec_ref(v___y_5630_);
return v___x_5713_;
}
}
v___jp_5694_:
{
if (lean_obj_tag(v_a_5689_) == 0)
{
lean_dec_ref(v_a_5689_);
lean_dec(v_a_5676_);
v_e_5638_ = v___x_5687_;
v_onTrue_5639_ = v___f_5693_;
v___y_5640_ = v___y_5695_;
v___y_5641_ = v___y_5696_;
v___y_5642_ = v___y_5697_;
v___y_5643_ = v___y_5698_;
v___y_5644_ = v___y_5699_;
v___y_5645_ = v___y_5700_;
goto v___jp_5637_;
}
else
{
lean_object* v_e_x27_5701_; lean_object* v_proof_5702_; lean_object* v___x_5703_; 
lean_dec_ref(v___f_5693_);
lean_dec_ref(v___x_5687_);
v_e_x27_5701_ = lean_ctor_get(v_a_5689_, 0);
lean_inc_ref(v_e_x27_5701_);
v_proof_5702_ = lean_ctor_get(v_a_5689_, 1);
lean_inc_ref(v_proof_5702_);
lean_dec_ref(v_a_5689_);
v___x_5703_ = lean_alloc_closure((void*)(l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0___boxed), 9, 2);
lean_closure_set(v___x_5703_, 0, v_a_5676_);
lean_closure_set(v___x_5703_, 1, v_proof_5702_);
v_e_5638_ = v_e_x27_5701_;
v_onTrue_5639_ = v___x_5703_;
v___y_5640_ = v___y_5695_;
v___y_5641_ = v___y_5696_;
v___y_5642_ = v___y_5697_;
v___y_5643_ = v___y_5698_;
v___y_5644_ = v___y_5699_;
v___y_5645_ = v___y_5700_;
goto v___jp_5637_;
}
}
}
else
{
lean_object* v_a_5714_; lean_object* v___x_5716_; uint8_t v_isShared_5717_; uint8_t v_isSharedCheck_5721_; 
lean_dec_ref(v___x_5687_);
lean_dec(v_a_5676_);
lean_dec(v___y_5635_);
lean_dec_ref(v___y_5634_);
lean_dec(v___y_5633_);
lean_dec_ref(v___y_5632_);
lean_dec(v___y_5631_);
lean_dec_ref(v___y_5630_);
lean_dec(v_cls_5628_);
v_a_5714_ = lean_ctor_get(v___x_5688_, 0);
v_isSharedCheck_5721_ = !lean_is_exclusive(v___x_5688_);
if (v_isSharedCheck_5721_ == 0)
{
v___x_5716_ = v___x_5688_;
v_isShared_5717_ = v_isSharedCheck_5721_;
goto v_resetjp_5715_;
}
else
{
lean_inc(v_a_5714_);
lean_dec(v___x_5688_);
v___x_5716_ = lean_box(0);
v_isShared_5717_ = v_isSharedCheck_5721_;
goto v_resetjp_5715_;
}
v_resetjp_5715_:
{
lean_object* v___x_5719_; 
if (v_isShared_5717_ == 0)
{
v___x_5719_ = v___x_5716_;
goto v_reusejp_5718_;
}
else
{
lean_object* v_reuseFailAlloc_5720_; 
v_reuseFailAlloc_5720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5720_, 0, v_a_5714_);
v___x_5719_ = v_reuseFailAlloc_5720_;
goto v_reusejp_5718_;
}
v_reusejp_5718_:
{
return v___x_5719_;
}
}
}
}
}
else
{
lean_object* v_a_5722_; lean_object* v___x_5724_; uint8_t v_isShared_5725_; uint8_t v_isSharedCheck_5729_; 
lean_dec(v_a_5676_);
lean_dec(v___y_5635_);
lean_dec_ref(v___y_5634_);
lean_dec(v___y_5633_);
lean_dec_ref(v___y_5632_);
lean_dec(v___y_5631_);
lean_dec_ref(v___y_5630_);
lean_dec(v_cls_5628_);
lean_dec_ref(v___x_5627_);
v_a_5722_ = lean_ctor_get(v___x_5677_, 0);
v_isSharedCheck_5729_ = !lean_is_exclusive(v___x_5677_);
if (v_isSharedCheck_5729_ == 0)
{
v___x_5724_ = v___x_5677_;
v_isShared_5725_ = v_isSharedCheck_5729_;
goto v_resetjp_5723_;
}
else
{
lean_inc(v_a_5722_);
lean_dec(v___x_5677_);
v___x_5724_ = lean_box(0);
v_isShared_5725_ = v_isSharedCheck_5729_;
goto v_resetjp_5723_;
}
v_resetjp_5723_:
{
lean_object* v___x_5727_; 
if (v_isShared_5725_ == 0)
{
v___x_5727_ = v___x_5724_;
goto v_reusejp_5726_;
}
else
{
lean_object* v_reuseFailAlloc_5728_; 
v_reuseFailAlloc_5728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5728_, 0, v_a_5722_);
v___x_5727_ = v_reuseFailAlloc_5728_;
goto v_reusejp_5726_;
}
v_reusejp_5726_:
{
return v___x_5727_;
}
}
}
}
else
{
lean_object* v_a_5730_; lean_object* v___x_5732_; uint8_t v_isShared_5733_; uint8_t v_isSharedCheck_5737_; 
lean_dec(v___y_5635_);
lean_dec_ref(v___y_5634_);
lean_dec(v___y_5633_);
lean_dec_ref(v___y_5632_);
lean_dec(v___y_5631_);
lean_dec_ref(v___y_5630_);
lean_dec(v_cls_5628_);
lean_dec_ref(v___x_5627_);
v_a_5730_ = lean_ctor_get(v___x_5675_, 0);
v_isSharedCheck_5737_ = !lean_is_exclusive(v___x_5675_);
if (v_isSharedCheck_5737_ == 0)
{
v___x_5732_ = v___x_5675_;
v_isShared_5733_ = v_isSharedCheck_5737_;
goto v_resetjp_5731_;
}
else
{
lean_inc(v_a_5730_);
lean_dec(v___x_5675_);
v___x_5732_ = lean_box(0);
v_isShared_5733_ = v_isSharedCheck_5737_;
goto v_resetjp_5731_;
}
v_resetjp_5731_:
{
lean_object* v___x_5735_; 
if (v_isShared_5733_ == 0)
{
v___x_5735_ = v___x_5732_;
goto v_reusejp_5734_;
}
else
{
lean_object* v_reuseFailAlloc_5736_; 
v_reuseFailAlloc_5736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5736_, 0, v_a_5730_);
v___x_5735_ = v_reuseFailAlloc_5736_;
goto v_reusejp_5734_;
}
v_reusejp_5734_:
{
return v___x_5735_;
}
}
}
v___jp_5637_:
{
lean_object* v___x_5646_; 
v___x_5646_ = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(v_e_5638_, v___y_5640_);
if (lean_obj_tag(v___x_5646_) == 0)
{
lean_object* v_a_5647_; uint8_t v___x_5648_; 
v_a_5647_ = lean_ctor_get(v___x_5646_, 0);
lean_inc(v_a_5647_);
lean_dec_ref(v___x_5646_);
v___x_5648_ = lean_unbox(v_a_5647_);
lean_dec(v_a_5647_);
if (v___x_5648_ == 0)
{
lean_object* v___x_5649_; 
lean_dec(v___y_5641_);
lean_dec_ref(v_onTrue_5639_);
v___x_5649_ = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(v_e_5638_, v___y_5640_);
lean_dec_ref(v___y_5640_);
if (lean_obj_tag(v___x_5649_) == 0)
{
lean_object* v_a_5650_; uint8_t v___x_5651_; 
v_a_5650_ = lean_ctor_get(v___x_5649_, 0);
lean_inc(v_a_5650_);
lean_dec_ref(v___x_5649_);
v___x_5651_ = lean_unbox(v_a_5650_);
lean_dec(v_a_5650_);
if (v___x_5651_ == 0)
{
lean_object* v___x_5652_; lean_object* v___x_5653_; lean_object* v___x_5654_; lean_object* v___x_5655_; 
v___x_5652_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1);
v___x_5653_ = l_Lean_indentExpr(v_e_5638_);
v___x_5654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5654_, 0, v___x_5652_);
lean_ctor_set(v___x_5654_, 1, v___x_5653_);
v___x_5655_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_5654_, v___y_5642_, v___y_5643_, v___y_5644_, v___y_5645_);
lean_dec(v___y_5645_);
lean_dec_ref(v___y_5644_);
lean_dec(v___y_5643_);
lean_dec_ref(v___y_5642_);
return v___x_5655_;
}
else
{
lean_object* v___x_5656_; lean_object* v___x_5657_; 
lean_dec_ref(v_e_5638_);
v___x_5656_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3);
v___x_5657_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_5656_, v___y_5642_, v___y_5643_, v___y_5644_, v___y_5645_);
lean_dec(v___y_5645_);
lean_dec_ref(v___y_5644_);
lean_dec(v___y_5643_);
lean_dec_ref(v___y_5642_);
return v___x_5657_;
}
}
else
{
lean_object* v_a_5658_; lean_object* v___x_5660_; uint8_t v_isShared_5661_; uint8_t v_isSharedCheck_5665_; 
lean_dec(v___y_5645_);
lean_dec_ref(v___y_5644_);
lean_dec(v___y_5643_);
lean_dec_ref(v___y_5642_);
lean_dec_ref(v_e_5638_);
v_a_5658_ = lean_ctor_get(v___x_5649_, 0);
v_isSharedCheck_5665_ = !lean_is_exclusive(v___x_5649_);
if (v_isSharedCheck_5665_ == 0)
{
v___x_5660_ = v___x_5649_;
v_isShared_5661_ = v_isSharedCheck_5665_;
goto v_resetjp_5659_;
}
else
{
lean_inc(v_a_5658_);
lean_dec(v___x_5649_);
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
lean_object* v___x_5666_; 
lean_dec_ref(v_e_5638_);
v___x_5666_ = lean_apply_7(v_onTrue_5639_, v___y_5640_, v___y_5641_, v___y_5642_, v___y_5643_, v___y_5644_, v___y_5645_, lean_box(0));
return v___x_5666_;
}
}
else
{
lean_object* v_a_5667_; lean_object* v___x_5669_; uint8_t v_isShared_5670_; uint8_t v_isSharedCheck_5674_; 
lean_dec(v___y_5645_);
lean_dec_ref(v___y_5644_);
lean_dec(v___y_5643_);
lean_dec_ref(v___y_5642_);
lean_dec(v___y_5641_);
lean_dec_ref(v___y_5640_);
lean_dec_ref(v_onTrue_5639_);
lean_dec_ref(v_e_5638_);
v_a_5667_ = lean_ctor_get(v___x_5646_, 0);
v_isSharedCheck_5674_ = !lean_is_exclusive(v___x_5646_);
if (v_isSharedCheck_5674_ == 0)
{
v___x_5669_ = v___x_5646_;
v_isShared_5670_ = v_isSharedCheck_5674_;
goto v_resetjp_5668_;
}
else
{
lean_inc(v_a_5667_);
lean_dec(v___x_5646_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__4___boxed(lean_object* v_m_5738_, lean_object* v___x_5739_, lean_object* v_cls_5740_, lean_object* v_hasTrace_5741_, lean_object* v___y_5742_, lean_object* v___y_5743_, lean_object* v___y_5744_, lean_object* v___y_5745_, lean_object* v___y_5746_, lean_object* v___y_5747_, lean_object* v___y_5748_){
_start:
{
uint8_t v_hasTrace_boxed_5749_; lean_object* v_res_5750_; 
v_hasTrace_boxed_5749_ = lean_unbox(v_hasTrace_5741_);
v_res_5750_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__4(v_m_5738_, v___x_5739_, v_cls_5740_, v_hasTrace_boxed_5749_, v___y_5742_, v___y_5743_, v___y_5744_, v___y_5745_, v___y_5746_, v___y_5747_);
return v_res_5750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__6(lean_object* v_m_5751_, lean_object* v___x_5752_, lean_object* v_cls_5753_, uint8_t v___x_5754_, lean_object* v___y_5755_, lean_object* v___y_5756_, lean_object* v___y_5757_, lean_object* v___y_5758_, lean_object* v___y_5759_, lean_object* v___y_5760_){
_start:
{
lean_object* v_e_5763_; lean_object* v_onTrue_5764_; lean_object* v___y_5765_; lean_object* v___y_5766_; lean_object* v___y_5767_; lean_object* v___y_5768_; lean_object* v___y_5769_; lean_object* v___y_5770_; lean_object* v___x_5800_; 
lean_inc(v___y_5760_);
lean_inc_ref(v___y_5759_);
lean_inc(v___y_5758_);
lean_inc_ref(v___y_5757_);
v___x_5800_ = l_Lean_Meta_Sym_preprocessMVar(v_m_5751_, v___y_5755_, v___y_5756_, v___y_5757_, v___y_5758_, v___y_5759_, v___y_5760_);
if (lean_obj_tag(v___x_5800_) == 0)
{
lean_object* v_a_5801_; lean_object* v___x_5802_; 
v_a_5801_ = lean_ctor_get(v___x_5800_, 0);
lean_inc(v_a_5801_);
lean_dec_ref(v___x_5800_);
lean_inc(v_a_5801_);
v___x_5802_ = l_Lean_MVarId_getType(v_a_5801_, v___y_5757_, v___y_5758_, v___y_5759_, v___y_5760_);
if (lean_obj_tag(v___x_5802_) == 0)
{
lean_object* v_a_5803_; lean_object* v___x_5804_; lean_object* v___x_5805_; uint8_t v___x_5806_; 
v_a_5803_ = lean_ctor_get(v___x_5802_, 0);
lean_inc(v_a_5803_);
lean_dec_ref(v___x_5802_);
v___x_5804_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__4));
v___x_5805_ = lean_unsigned_to_nat(3u);
v___x_5806_ = l_Lean_Expr_isAppOfArity(v_a_5803_, v___x_5804_, v___x_5805_);
if (v___x_5806_ == 0)
{
lean_object* v___x_5807_; lean_object* v___x_5808_; lean_object* v___x_5809_; lean_object* v___x_5810_; 
lean_dec(v_a_5801_);
lean_dec(v___y_5756_);
lean_dec_ref(v___y_5755_);
lean_dec(v_cls_5753_);
lean_dec_ref(v___x_5752_);
v___x_5807_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6);
v___x_5808_ = l_Lean_indentExpr(v_a_5803_);
v___x_5809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5809_, 0, v___x_5807_);
lean_ctor_set(v___x_5809_, 1, v___x_5808_);
v___x_5810_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_5809_, v___y_5757_, v___y_5758_, v___y_5759_, v___y_5760_);
lean_dec(v___y_5760_);
lean_dec_ref(v___y_5759_);
lean_dec(v___y_5758_);
lean_dec_ref(v___y_5757_);
return v___x_5810_;
}
else
{
lean_object* v___x_5811_; lean_object* v___x_5812_; lean_object* v___x_5813_; 
v___x_5811_ = l_Lean_Expr_appFn_x21(v_a_5803_);
lean_dec(v_a_5803_);
v___x_5812_ = l_Lean_Expr_appArg_x21(v___x_5811_);
lean_dec_ref(v___x_5811_);
lean_inc(v___y_5760_);
lean_inc_ref(v___y_5759_);
lean_inc(v___y_5758_);
lean_inc_ref(v___y_5757_);
lean_inc(v___y_5756_);
lean_inc_ref(v___y_5755_);
lean_inc_ref(v___x_5812_);
v___x_5813_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_5812_, v___x_5752_, v___y_5755_, v___y_5756_, v___y_5757_, v___y_5758_, v___y_5759_, v___y_5760_);
if (lean_obj_tag(v___x_5813_) == 0)
{
lean_object* v_a_5814_; lean_object* v___x_5815_; lean_object* v_a_5816_; lean_object* v___x_5817_; lean_object* v___f_5818_; lean_object* v___y_5820_; lean_object* v___y_5821_; lean_object* v___y_5822_; lean_object* v___y_5823_; lean_object* v___y_5824_; lean_object* v___y_5825_; uint8_t v___x_5829_; 
v_a_5814_ = lean_ctor_get(v___x_5813_, 0);
lean_inc(v_a_5814_);
lean_dec_ref(v___x_5813_);
lean_inc(v_cls_5753_);
v___x_5815_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__1___redArg(v_cls_5753_, v___y_5759_);
v_a_5816_ = lean_ctor_get(v___x_5815_, 0);
lean_inc(v_a_5816_);
lean_dec_ref(v___x_5815_);
v___x_5817_ = lean_box(v___x_5754_);
lean_inc(v_a_5801_);
v___f_5818_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5818_, 0, v_a_5801_);
lean_closure_set(v___f_5818_, 1, v___x_5817_);
v___x_5829_ = lean_unbox(v_a_5816_);
lean_dec(v_a_5816_);
if (v___x_5829_ == 0)
{
lean_dec(v_cls_5753_);
v___y_5820_ = v___y_5755_;
v___y_5821_ = v___y_5756_;
v___y_5822_ = v___y_5757_;
v___y_5823_ = v___y_5758_;
v___y_5824_ = v___y_5759_;
v___y_5825_ = v___y_5760_;
goto v___jp_5819_;
}
else
{
lean_object* v___x_5830_; lean_object* v___x_5831_; lean_object* v___x_5832_; lean_object* v___x_5833_; lean_object* v___x_5834_; lean_object* v___x_5835_; lean_object* v___x_5836_; lean_object* v___x_5837_; lean_object* v___x_5838_; 
v___x_5830_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8);
lean_inc_ref(v___x_5812_);
v___x_5831_ = l_Lean_indentExpr(v___x_5812_);
v___x_5832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5832_, 0, v___x_5830_);
lean_ctor_set(v___x_5832_, 1, v___x_5831_);
v___x_5833_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7);
v___x_5834_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5834_, 0, v___x_5832_);
lean_ctor_set(v___x_5834_, 1, v___x_5833_);
v___x_5835_ = l_Lean_Meta_Sym_Simp_Result_getResultExpr(v___x_5812_, v_a_5814_);
v___x_5836_ = l_Lean_indentExpr(v___x_5835_);
v___x_5837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5837_, 0, v___x_5834_);
lean_ctor_set(v___x_5837_, 1, v___x_5836_);
v___x_5838_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(v_cls_5753_, v___x_5837_, v___y_5757_, v___y_5758_, v___y_5759_, v___y_5760_);
if (lean_obj_tag(v___x_5838_) == 0)
{
lean_dec_ref(v___x_5838_);
v___y_5820_ = v___y_5755_;
v___y_5821_ = v___y_5756_;
v___y_5822_ = v___y_5757_;
v___y_5823_ = v___y_5758_;
v___y_5824_ = v___y_5759_;
v___y_5825_ = v___y_5760_;
goto v___jp_5819_;
}
else
{
lean_dec_ref(v___f_5818_);
lean_dec(v_a_5814_);
lean_dec_ref(v___x_5812_);
lean_dec(v_a_5801_);
lean_dec(v___y_5760_);
lean_dec_ref(v___y_5759_);
lean_dec(v___y_5758_);
lean_dec_ref(v___y_5757_);
lean_dec(v___y_5756_);
lean_dec_ref(v___y_5755_);
return v___x_5838_;
}
}
v___jp_5819_:
{
if (lean_obj_tag(v_a_5814_) == 0)
{
lean_dec_ref(v_a_5814_);
lean_dec(v_a_5801_);
v_e_5763_ = v___x_5812_;
v_onTrue_5764_ = v___f_5818_;
v___y_5765_ = v___y_5820_;
v___y_5766_ = v___y_5821_;
v___y_5767_ = v___y_5822_;
v___y_5768_ = v___y_5823_;
v___y_5769_ = v___y_5824_;
v___y_5770_ = v___y_5825_;
goto v___jp_5762_;
}
else
{
lean_object* v_e_x27_5826_; lean_object* v_proof_5827_; lean_object* v___x_5828_; 
lean_dec_ref(v___f_5818_);
lean_dec_ref(v___x_5812_);
v_e_x27_5826_ = lean_ctor_get(v_a_5814_, 0);
lean_inc_ref(v_e_x27_5826_);
v_proof_5827_ = lean_ctor_get(v_a_5814_, 1);
lean_inc_ref(v_proof_5827_);
lean_dec_ref(v_a_5814_);
v___x_5828_ = lean_alloc_closure((void*)(l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoal_spec__0___boxed), 9, 2);
lean_closure_set(v___x_5828_, 0, v_a_5801_);
lean_closure_set(v___x_5828_, 1, v_proof_5827_);
v_e_5763_ = v_e_x27_5826_;
v_onTrue_5764_ = v___x_5828_;
v___y_5765_ = v___y_5820_;
v___y_5766_ = v___y_5821_;
v___y_5767_ = v___y_5822_;
v___y_5768_ = v___y_5823_;
v___y_5769_ = v___y_5824_;
v___y_5770_ = v___y_5825_;
goto v___jp_5762_;
}
}
}
else
{
lean_object* v_a_5839_; lean_object* v___x_5841_; uint8_t v_isShared_5842_; uint8_t v_isSharedCheck_5846_; 
lean_dec_ref(v___x_5812_);
lean_dec(v_a_5801_);
lean_dec(v___y_5760_);
lean_dec_ref(v___y_5759_);
lean_dec(v___y_5758_);
lean_dec_ref(v___y_5757_);
lean_dec(v___y_5756_);
lean_dec_ref(v___y_5755_);
lean_dec(v_cls_5753_);
v_a_5839_ = lean_ctor_get(v___x_5813_, 0);
v_isSharedCheck_5846_ = !lean_is_exclusive(v___x_5813_);
if (v_isSharedCheck_5846_ == 0)
{
v___x_5841_ = v___x_5813_;
v_isShared_5842_ = v_isSharedCheck_5846_;
goto v_resetjp_5840_;
}
else
{
lean_inc(v_a_5839_);
lean_dec(v___x_5813_);
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
else
{
lean_object* v_a_5847_; lean_object* v___x_5849_; uint8_t v_isShared_5850_; uint8_t v_isSharedCheck_5854_; 
lean_dec(v_a_5801_);
lean_dec(v___y_5760_);
lean_dec_ref(v___y_5759_);
lean_dec(v___y_5758_);
lean_dec_ref(v___y_5757_);
lean_dec(v___y_5756_);
lean_dec_ref(v___y_5755_);
lean_dec(v_cls_5753_);
lean_dec_ref(v___x_5752_);
v_a_5847_ = lean_ctor_get(v___x_5802_, 0);
v_isSharedCheck_5854_ = !lean_is_exclusive(v___x_5802_);
if (v_isSharedCheck_5854_ == 0)
{
v___x_5849_ = v___x_5802_;
v_isShared_5850_ = v_isSharedCheck_5854_;
goto v_resetjp_5848_;
}
else
{
lean_inc(v_a_5847_);
lean_dec(v___x_5802_);
v___x_5849_ = lean_box(0);
v_isShared_5850_ = v_isSharedCheck_5854_;
goto v_resetjp_5848_;
}
v_resetjp_5848_:
{
lean_object* v___x_5852_; 
if (v_isShared_5850_ == 0)
{
v___x_5852_ = v___x_5849_;
goto v_reusejp_5851_;
}
else
{
lean_object* v_reuseFailAlloc_5853_; 
v_reuseFailAlloc_5853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5853_, 0, v_a_5847_);
v___x_5852_ = v_reuseFailAlloc_5853_;
goto v_reusejp_5851_;
}
v_reusejp_5851_:
{
return v___x_5852_;
}
}
}
}
else
{
lean_object* v_a_5855_; lean_object* v___x_5857_; uint8_t v_isShared_5858_; uint8_t v_isSharedCheck_5862_; 
lean_dec(v___y_5760_);
lean_dec_ref(v___y_5759_);
lean_dec(v___y_5758_);
lean_dec_ref(v___y_5757_);
lean_dec(v___y_5756_);
lean_dec_ref(v___y_5755_);
lean_dec(v_cls_5753_);
lean_dec_ref(v___x_5752_);
v_a_5855_ = lean_ctor_get(v___x_5800_, 0);
v_isSharedCheck_5862_ = !lean_is_exclusive(v___x_5800_);
if (v_isSharedCheck_5862_ == 0)
{
v___x_5857_ = v___x_5800_;
v_isShared_5858_ = v_isSharedCheck_5862_;
goto v_resetjp_5856_;
}
else
{
lean_inc(v_a_5855_);
lean_dec(v___x_5800_);
v___x_5857_ = lean_box(0);
v_isShared_5858_ = v_isSharedCheck_5862_;
goto v_resetjp_5856_;
}
v_resetjp_5856_:
{
lean_object* v___x_5860_; 
if (v_isShared_5858_ == 0)
{
v___x_5860_ = v___x_5857_;
goto v_reusejp_5859_;
}
else
{
lean_object* v_reuseFailAlloc_5861_; 
v_reuseFailAlloc_5861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5861_, 0, v_a_5855_);
v___x_5860_ = v_reuseFailAlloc_5861_;
goto v_reusejp_5859_;
}
v_reusejp_5859_:
{
return v___x_5860_;
}
}
}
v___jp_5762_:
{
lean_object* v___x_5771_; 
v___x_5771_ = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(v_e_5763_, v___y_5765_);
if (lean_obj_tag(v___x_5771_) == 0)
{
lean_object* v_a_5772_; uint8_t v___x_5773_; 
v_a_5772_ = lean_ctor_get(v___x_5771_, 0);
lean_inc(v_a_5772_);
lean_dec_ref(v___x_5771_);
v___x_5773_ = lean_unbox(v_a_5772_);
lean_dec(v_a_5772_);
if (v___x_5773_ == 0)
{
lean_object* v___x_5774_; 
lean_dec(v___y_5766_);
lean_dec_ref(v_onTrue_5764_);
v___x_5774_ = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(v_e_5763_, v___y_5765_);
lean_dec_ref(v___y_5765_);
if (lean_obj_tag(v___x_5774_) == 0)
{
lean_object* v_a_5775_; uint8_t v___x_5776_; 
v_a_5775_ = lean_ctor_get(v___x_5774_, 0);
lean_inc(v_a_5775_);
lean_dec_ref(v___x_5774_);
v___x_5776_ = lean_unbox(v_a_5775_);
lean_dec(v_a_5775_);
if (v___x_5776_ == 0)
{
lean_object* v___x_5777_; lean_object* v___x_5778_; lean_object* v___x_5779_; lean_object* v___x_5780_; 
v___x_5777_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1);
v___x_5778_ = l_Lean_indentExpr(v_e_5763_);
v___x_5779_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5779_, 0, v___x_5777_);
lean_ctor_set(v___x_5779_, 1, v___x_5778_);
v___x_5780_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_5779_, v___y_5767_, v___y_5768_, v___y_5769_, v___y_5770_);
lean_dec(v___y_5770_);
lean_dec_ref(v___y_5769_);
lean_dec(v___y_5768_);
lean_dec_ref(v___y_5767_);
return v___x_5780_;
}
else
{
lean_object* v___x_5781_; lean_object* v___x_5782_; 
lean_dec_ref(v_e_5763_);
v___x_5781_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3);
v___x_5782_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_5781_, v___y_5767_, v___y_5768_, v___y_5769_, v___y_5770_);
lean_dec(v___y_5770_);
lean_dec_ref(v___y_5769_);
lean_dec(v___y_5768_);
lean_dec_ref(v___y_5767_);
return v___x_5782_;
}
}
else
{
lean_object* v_a_5783_; lean_object* v___x_5785_; uint8_t v_isShared_5786_; uint8_t v_isSharedCheck_5790_; 
lean_dec(v___y_5770_);
lean_dec_ref(v___y_5769_);
lean_dec(v___y_5768_);
lean_dec_ref(v___y_5767_);
lean_dec_ref(v_e_5763_);
v_a_5783_ = lean_ctor_get(v___x_5774_, 0);
v_isSharedCheck_5790_ = !lean_is_exclusive(v___x_5774_);
if (v_isSharedCheck_5790_ == 0)
{
v___x_5785_ = v___x_5774_;
v_isShared_5786_ = v_isSharedCheck_5790_;
goto v_resetjp_5784_;
}
else
{
lean_inc(v_a_5783_);
lean_dec(v___x_5774_);
v___x_5785_ = lean_box(0);
v_isShared_5786_ = v_isSharedCheck_5790_;
goto v_resetjp_5784_;
}
v_resetjp_5784_:
{
lean_object* v___x_5788_; 
if (v_isShared_5786_ == 0)
{
v___x_5788_ = v___x_5785_;
goto v_reusejp_5787_;
}
else
{
lean_object* v_reuseFailAlloc_5789_; 
v_reuseFailAlloc_5789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5789_, 0, v_a_5783_);
v___x_5788_ = v_reuseFailAlloc_5789_;
goto v_reusejp_5787_;
}
v_reusejp_5787_:
{
return v___x_5788_;
}
}
}
}
else
{
lean_object* v___x_5791_; 
lean_dec_ref(v_e_5763_);
v___x_5791_ = lean_apply_7(v_onTrue_5764_, v___y_5765_, v___y_5766_, v___y_5767_, v___y_5768_, v___y_5769_, v___y_5770_, lean_box(0));
return v___x_5791_;
}
}
else
{
lean_object* v_a_5792_; lean_object* v___x_5794_; uint8_t v_isShared_5795_; uint8_t v_isSharedCheck_5799_; 
lean_dec(v___y_5770_);
lean_dec_ref(v___y_5769_);
lean_dec(v___y_5768_);
lean_dec_ref(v___y_5767_);
lean_dec(v___y_5766_);
lean_dec_ref(v___y_5765_);
lean_dec_ref(v_onTrue_5764_);
lean_dec_ref(v_e_5763_);
v_a_5792_ = lean_ctor_get(v___x_5771_, 0);
v_isSharedCheck_5799_ = !lean_is_exclusive(v___x_5771_);
if (v_isSharedCheck_5799_ == 0)
{
v___x_5794_ = v___x_5771_;
v_isShared_5795_ = v_isSharedCheck_5799_;
goto v_resetjp_5793_;
}
else
{
lean_inc(v_a_5792_);
lean_dec(v___x_5771_);
v___x_5794_ = lean_box(0);
v_isShared_5795_ = v_isSharedCheck_5799_;
goto v_resetjp_5793_;
}
v_resetjp_5793_:
{
lean_object* v___x_5797_; 
if (v_isShared_5795_ == 0)
{
v___x_5797_ = v___x_5794_;
goto v_reusejp_5796_;
}
else
{
lean_object* v_reuseFailAlloc_5798_; 
v_reuseFailAlloc_5798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5798_, 0, v_a_5792_);
v___x_5797_ = v_reuseFailAlloc_5798_;
goto v_reusejp_5796_;
}
v_reusejp_5796_:
{
return v___x_5797_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__6___boxed(lean_object* v_m_5863_, lean_object* v___x_5864_, lean_object* v_cls_5865_, lean_object* v___x_5866_, lean_object* v___y_5867_, lean_object* v___y_5868_, lean_object* v___y_5869_, lean_object* v___y_5870_, lean_object* v___y_5871_, lean_object* v___y_5872_, lean_object* v___y_5873_){
_start:
{
uint8_t v___x_21946__boxed_5874_; lean_object* v_res_5875_; 
v___x_21946__boxed_5874_ = lean_unbox(v___x_5866_);
v_res_5875_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__6(v_m_5863_, v___x_5864_, v_cls_5865_, v___x_21946__boxed_5874_, v___y_5867_, v___y_5868_, v___y_5869_, v___y_5870_, v___y_5871_, v___y_5872_);
return v_res_5875_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2_spec__2(lean_object* v_e_5876_){
_start:
{
if (lean_obj_tag(v_e_5876_) == 0)
{
uint8_t v___x_5877_; 
v___x_5877_ = 2;
return v___x_5877_;
}
else
{
uint8_t v___x_5878_; 
v___x_5878_ = 0;
return v___x_5878_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2_spec__2___boxed(lean_object* v_e_5879_){
_start:
{
uint8_t v_res_5880_; lean_object* v_r_5881_; 
v_res_5880_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2_spec__2(v_e_5879_);
lean_dec_ref(v_e_5879_);
v_r_5881_ = lean_box(v_res_5880_);
return v_r_5881_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2(lean_object* v_cls_5882_, uint8_t v_collapsed_5883_, lean_object* v_tag_5884_, lean_object* v_opts_5885_, uint8_t v_clsEnabled_5886_, lean_object* v_oldTraces_5887_, lean_object* v_msg_5888_, lean_object* v_resStartStop_5889_, lean_object* v___y_5890_, lean_object* v___y_5891_, lean_object* v___y_5892_, lean_object* v___y_5893_){
_start:
{
lean_object* v_fst_5895_; lean_object* v_snd_5896_; lean_object* v___x_5898_; uint8_t v_isShared_5899_; uint8_t v_isSharedCheck_5986_; 
v_fst_5895_ = lean_ctor_get(v_resStartStop_5889_, 0);
v_snd_5896_ = lean_ctor_get(v_resStartStop_5889_, 1);
v_isSharedCheck_5986_ = !lean_is_exclusive(v_resStartStop_5889_);
if (v_isSharedCheck_5986_ == 0)
{
v___x_5898_ = v_resStartStop_5889_;
v_isShared_5899_ = v_isSharedCheck_5986_;
goto v_resetjp_5897_;
}
else
{
lean_inc(v_snd_5896_);
lean_inc(v_fst_5895_);
lean_dec(v_resStartStop_5889_);
v___x_5898_ = lean_box(0);
v_isShared_5899_ = v_isSharedCheck_5986_;
goto v_resetjp_5897_;
}
v_resetjp_5897_:
{
lean_object* v___y_5901_; lean_object* v___y_5902_; lean_object* v_data_5903_; lean_object* v_fst_5906_; lean_object* v_snd_5907_; lean_object* v___x_5909_; uint8_t v_isShared_5910_; uint8_t v_isSharedCheck_5985_; 
v_fst_5906_ = lean_ctor_get(v_snd_5896_, 0);
v_snd_5907_ = lean_ctor_get(v_snd_5896_, 1);
v_isSharedCheck_5985_ = !lean_is_exclusive(v_snd_5896_);
if (v_isSharedCheck_5985_ == 0)
{
v___x_5909_ = v_snd_5896_;
v_isShared_5910_ = v_isSharedCheck_5985_;
goto v_resetjp_5908_;
}
else
{
lean_inc(v_snd_5907_);
lean_inc(v_fst_5906_);
lean_dec(v_snd_5896_);
v___x_5909_ = lean_box(0);
v_isShared_5910_ = v_isSharedCheck_5985_;
goto v_resetjp_5908_;
}
v___jp_5900_:
{
lean_object* v___x_5904_; 
v___x_5904_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__2_spec__2(v_oldTraces_5887_, v_data_5903_, v___y_5901_, v___y_5902_, v___y_5890_, v___y_5891_, v___y_5892_, v___y_5893_);
lean_dec(v___y_5893_);
lean_dec(v___y_5891_);
lean_dec_ref(v___y_5890_);
if (lean_obj_tag(v___x_5904_) == 0)
{
lean_object* v___x_5905_; 
lean_dec_ref(v___x_5904_);
v___x_5905_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__2_spec__3___redArg(v_fst_5895_);
return v___x_5905_;
}
else
{
lean_dec(v_fst_5895_);
return v___x_5904_;
}
}
v_resetjp_5908_:
{
lean_object* v___x_5911_; uint8_t v___x_5912_; lean_object* v___y_5914_; lean_object* v_a_5915_; uint8_t v___y_5939_; double v___y_5970_; 
v___x_5911_ = l_Lean_trace_profiler;
v___x_5912_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2(v_opts_5885_, v___x_5911_);
if (v___x_5912_ == 0)
{
v___y_5939_ = v___x_5912_;
goto v___jp_5938_;
}
else
{
lean_object* v___x_5975_; uint8_t v___x_5976_; 
v___x_5975_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5976_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2(v_opts_5885_, v___x_5975_);
if (v___x_5976_ == 0)
{
lean_object* v___x_5977_; lean_object* v___x_5978_; double v___x_5979_; double v___x_5980_; double v___x_5981_; 
v___x_5977_ = l_Lean_trace_profiler_threshold;
v___x_5978_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__6(v_opts_5885_, v___x_5977_);
v___x_5979_ = lean_float_of_nat(v___x_5978_);
v___x_5980_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__4);
v___x_5981_ = lean_float_div(v___x_5979_, v___x_5980_);
v___y_5970_ = v___x_5981_;
goto v___jp_5969_;
}
else
{
lean_object* v___x_5982_; lean_object* v___x_5983_; double v___x_5984_; 
v___x_5982_ = l_Lean_trace_profiler_threshold;
v___x_5983_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__6(v_opts_5885_, v___x_5982_);
v___x_5984_ = lean_float_of_nat(v___x_5983_);
v___y_5970_ = v___x_5984_;
goto v___jp_5969_;
}
}
v___jp_5913_:
{
uint8_t v_result_5916_; lean_object* v___x_5917_; lean_object* v___x_5918_; lean_object* v___x_5919_; lean_object* v___x_5921_; 
v_result_5916_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2_spec__2(v_fst_5895_);
v___x_5917_ = l_Lean_TraceResult_toEmoji(v_result_5916_);
v___x_5918_ = l_Lean_stringToMessageData(v___x_5917_);
v___x_5919_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__1);
if (v_isShared_5910_ == 0)
{
lean_ctor_set_tag(v___x_5909_, 7);
lean_ctor_set(v___x_5909_, 1, v___x_5919_);
lean_ctor_set(v___x_5909_, 0, v___x_5918_);
v___x_5921_ = v___x_5909_;
goto v_reusejp_5920_;
}
else
{
lean_object* v_reuseFailAlloc_5932_; 
v_reuseFailAlloc_5932_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5932_, 0, v___x_5918_);
lean_ctor_set(v_reuseFailAlloc_5932_, 1, v___x_5919_);
v___x_5921_ = v_reuseFailAlloc_5932_;
goto v_reusejp_5920_;
}
v_reusejp_5920_:
{
lean_object* v_m_5923_; 
if (v_isShared_5899_ == 0)
{
lean_ctor_set_tag(v___x_5898_, 7);
lean_ctor_set(v___x_5898_, 1, v_a_5915_);
lean_ctor_set(v___x_5898_, 0, v___x_5921_);
v_m_5923_ = v___x_5898_;
goto v_reusejp_5922_;
}
else
{
lean_object* v_reuseFailAlloc_5931_; 
v_reuseFailAlloc_5931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5931_, 0, v___x_5921_);
lean_ctor_set(v_reuseFailAlloc_5931_, 1, v_a_5915_);
v_m_5923_ = v_reuseFailAlloc_5931_;
goto v_reusejp_5922_;
}
v_reusejp_5922_:
{
lean_object* v___x_5924_; lean_object* v___x_5925_; double v___x_5926_; lean_object* v_data_5927_; 
v___x_5924_ = lean_box(v_result_5916_);
v___x_5925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5925_, 0, v___x_5924_);
v___x_5926_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__0);
lean_inc_ref(v_tag_5884_);
lean_inc_ref(v___x_5925_);
lean_inc(v_cls_5882_);
v_data_5927_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_5927_, 0, v_cls_5882_);
lean_ctor_set(v_data_5927_, 1, v___x_5925_);
lean_ctor_set(v_data_5927_, 2, v_tag_5884_);
lean_ctor_set_float(v_data_5927_, sizeof(void*)*3, v___x_5926_);
lean_ctor_set_float(v_data_5927_, sizeof(void*)*3 + 8, v___x_5926_);
lean_ctor_set_uint8(v_data_5927_, sizeof(void*)*3 + 16, v_collapsed_5883_);
if (v___x_5912_ == 0)
{
lean_dec_ref(v___x_5925_);
lean_dec(v_snd_5907_);
lean_dec(v_fst_5906_);
lean_dec_ref(v_tag_5884_);
lean_dec(v_cls_5882_);
v___y_5901_ = v___y_5914_;
v___y_5902_ = v_m_5923_;
v_data_5903_ = v_data_5927_;
goto v___jp_5900_;
}
else
{
lean_object* v_data_5928_; double v___x_5929_; double v___x_5930_; 
lean_dec_ref(v_data_5927_);
v_data_5928_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_5928_, 0, v_cls_5882_);
lean_ctor_set(v_data_5928_, 1, v___x_5925_);
lean_ctor_set(v_data_5928_, 2, v_tag_5884_);
v___x_5929_ = lean_unbox_float(v_fst_5906_);
lean_dec(v_fst_5906_);
lean_ctor_set_float(v_data_5928_, sizeof(void*)*3, v___x_5929_);
v___x_5930_ = lean_unbox_float(v_snd_5907_);
lean_dec(v_snd_5907_);
lean_ctor_set_float(v_data_5928_, sizeof(void*)*3 + 8, v___x_5930_);
lean_ctor_set_uint8(v_data_5928_, sizeof(void*)*3 + 16, v_collapsed_5883_);
v___y_5901_ = v___y_5914_;
v___y_5902_ = v_m_5923_;
v_data_5903_ = v_data_5928_;
goto v___jp_5900_;
}
}
}
}
v___jp_5933_:
{
lean_object* v_ref_5934_; lean_object* v___x_5935_; 
v_ref_5934_ = lean_ctor_get(v___y_5892_, 5);
lean_inc(v___y_5893_);
lean_inc_ref(v___y_5892_);
lean_inc(v___y_5891_);
lean_inc_ref(v___y_5890_);
lean_inc(v_fst_5895_);
v___x_5935_ = lean_apply_6(v_msg_5888_, v_fst_5895_, v___y_5890_, v___y_5891_, v___y_5892_, v___y_5893_, lean_box(0));
if (lean_obj_tag(v___x_5935_) == 0)
{
lean_object* v_a_5936_; 
v_a_5936_ = lean_ctor_get(v___x_5935_, 0);
lean_inc(v_a_5936_);
lean_dec_ref(v___x_5935_);
lean_inc(v_ref_5934_);
v___y_5914_ = v_ref_5934_;
v_a_5915_ = v_a_5936_;
goto v___jp_5913_;
}
else
{
lean_object* v___x_5937_; 
lean_dec_ref(v___x_5935_);
v___x_5937_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___closed__3);
lean_inc(v_ref_5934_);
v___y_5914_ = v_ref_5934_;
v_a_5915_ = v___x_5937_;
goto v___jp_5913_;
}
}
v___jp_5938_:
{
if (v_clsEnabled_5886_ == 0)
{
if (v___y_5939_ == 0)
{
lean_object* v___x_5940_; lean_object* v_traceState_5941_; lean_object* v_env_5942_; lean_object* v_nextMacroScope_5943_; lean_object* v_ngen_5944_; lean_object* v_auxDeclNGen_5945_; lean_object* v_cache_5946_; lean_object* v_messages_5947_; lean_object* v_infoState_5948_; lean_object* v_snapshotTasks_5949_; lean_object* v___x_5951_; uint8_t v_isShared_5952_; uint8_t v_isSharedCheck_5968_; 
lean_del_object(v___x_5909_);
lean_dec(v_snd_5907_);
lean_dec(v_fst_5906_);
lean_del_object(v___x_5898_);
lean_dec_ref(v___y_5892_);
lean_dec(v___y_5891_);
lean_dec_ref(v___y_5890_);
lean_dec_ref(v_msg_5888_);
lean_dec_ref(v_tag_5884_);
lean_dec(v_cls_5882_);
v___x_5940_ = lean_st_ref_take(v___y_5893_);
v_traceState_5941_ = lean_ctor_get(v___x_5940_, 4);
v_env_5942_ = lean_ctor_get(v___x_5940_, 0);
v_nextMacroScope_5943_ = lean_ctor_get(v___x_5940_, 1);
v_ngen_5944_ = lean_ctor_get(v___x_5940_, 2);
v_auxDeclNGen_5945_ = lean_ctor_get(v___x_5940_, 3);
v_cache_5946_ = lean_ctor_get(v___x_5940_, 5);
v_messages_5947_ = lean_ctor_get(v___x_5940_, 6);
v_infoState_5948_ = lean_ctor_get(v___x_5940_, 7);
v_snapshotTasks_5949_ = lean_ctor_get(v___x_5940_, 8);
v_isSharedCheck_5968_ = !lean_is_exclusive(v___x_5940_);
if (v_isSharedCheck_5968_ == 0)
{
v___x_5951_ = v___x_5940_;
v_isShared_5952_ = v_isSharedCheck_5968_;
goto v_resetjp_5950_;
}
else
{
lean_inc(v_snapshotTasks_5949_);
lean_inc(v_infoState_5948_);
lean_inc(v_messages_5947_);
lean_inc(v_cache_5946_);
lean_inc(v_traceState_5941_);
lean_inc(v_auxDeclNGen_5945_);
lean_inc(v_ngen_5944_);
lean_inc(v_nextMacroScope_5943_);
lean_inc(v_env_5942_);
lean_dec(v___x_5940_);
v___x_5951_ = lean_box(0);
v_isShared_5952_ = v_isSharedCheck_5968_;
goto v_resetjp_5950_;
}
v_resetjp_5950_:
{
uint64_t v_tid_5953_; lean_object* v_traces_5954_; lean_object* v___x_5956_; uint8_t v_isShared_5957_; uint8_t v_isSharedCheck_5967_; 
v_tid_5953_ = lean_ctor_get_uint64(v_traceState_5941_, sizeof(void*)*1);
v_traces_5954_ = lean_ctor_get(v_traceState_5941_, 0);
v_isSharedCheck_5967_ = !lean_is_exclusive(v_traceState_5941_);
if (v_isSharedCheck_5967_ == 0)
{
v___x_5956_ = v_traceState_5941_;
v_isShared_5957_ = v_isSharedCheck_5967_;
goto v_resetjp_5955_;
}
else
{
lean_inc(v_traces_5954_);
lean_dec(v_traceState_5941_);
v___x_5956_ = lean_box(0);
v_isShared_5957_ = v_isSharedCheck_5967_;
goto v_resetjp_5955_;
}
v_resetjp_5955_:
{
lean_object* v___x_5958_; lean_object* v___x_5960_; 
v___x_5958_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_5887_, v_traces_5954_);
lean_dec_ref(v_traces_5954_);
if (v_isShared_5957_ == 0)
{
lean_ctor_set(v___x_5956_, 0, v___x_5958_);
v___x_5960_ = v___x_5956_;
goto v_reusejp_5959_;
}
else
{
lean_object* v_reuseFailAlloc_5966_; 
v_reuseFailAlloc_5966_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5966_, 0, v___x_5958_);
lean_ctor_set_uint64(v_reuseFailAlloc_5966_, sizeof(void*)*1, v_tid_5953_);
v___x_5960_ = v_reuseFailAlloc_5966_;
goto v_reusejp_5959_;
}
v_reusejp_5959_:
{
lean_object* v___x_5962_; 
if (v_isShared_5952_ == 0)
{
lean_ctor_set(v___x_5951_, 4, v___x_5960_);
v___x_5962_ = v___x_5951_;
goto v_reusejp_5961_;
}
else
{
lean_object* v_reuseFailAlloc_5965_; 
v_reuseFailAlloc_5965_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5965_, 0, v_env_5942_);
lean_ctor_set(v_reuseFailAlloc_5965_, 1, v_nextMacroScope_5943_);
lean_ctor_set(v_reuseFailAlloc_5965_, 2, v_ngen_5944_);
lean_ctor_set(v_reuseFailAlloc_5965_, 3, v_auxDeclNGen_5945_);
lean_ctor_set(v_reuseFailAlloc_5965_, 4, v___x_5960_);
lean_ctor_set(v_reuseFailAlloc_5965_, 5, v_cache_5946_);
lean_ctor_set(v_reuseFailAlloc_5965_, 6, v_messages_5947_);
lean_ctor_set(v_reuseFailAlloc_5965_, 7, v_infoState_5948_);
lean_ctor_set(v_reuseFailAlloc_5965_, 8, v_snapshotTasks_5949_);
v___x_5962_ = v_reuseFailAlloc_5965_;
goto v_reusejp_5961_;
}
v_reusejp_5961_:
{
lean_object* v___x_5963_; lean_object* v___x_5964_; 
v___x_5963_ = lean_st_ref_set(v___y_5893_, v___x_5962_);
lean_dec(v___y_5893_);
v___x_5964_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__2_spec__3___redArg(v_fst_5895_);
return v___x_5964_;
}
}
}
}
}
else
{
goto v___jp_5933_;
}
}
else
{
goto v___jp_5933_;
}
}
v___jp_5969_:
{
double v___x_5971_; double v___x_5972_; double v___x_5973_; uint8_t v___x_5974_; 
v___x_5971_ = lean_unbox_float(v_snd_5907_);
v___x_5972_ = lean_unbox_float(v_fst_5906_);
v___x_5973_ = lean_float_sub(v___x_5971_, v___x_5972_);
v___x_5974_ = lean_float_decLt(v___y_5970_, v___x_5973_);
v___y_5939_ = v___x_5974_;
goto v___jp_5938_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2___boxed(lean_object* v_cls_5987_, lean_object* v_collapsed_5988_, lean_object* v_tag_5989_, lean_object* v_opts_5990_, lean_object* v_clsEnabled_5991_, lean_object* v_oldTraces_5992_, lean_object* v_msg_5993_, lean_object* v_resStartStop_5994_, lean_object* v___y_5995_, lean_object* v___y_5996_, lean_object* v___y_5997_, lean_object* v___y_5998_, lean_object* v___y_5999_){
_start:
{
uint8_t v_collapsed_boxed_6000_; uint8_t v_clsEnabled_boxed_6001_; lean_object* v_res_6002_; 
v_collapsed_boxed_6000_ = lean_unbox(v_collapsed_5988_);
v_clsEnabled_boxed_6001_ = lean_unbox(v_clsEnabled_5991_);
v_res_6002_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2(v_cls_5987_, v_collapsed_boxed_6000_, v_tag_5989_, v_opts_5990_, v_clsEnabled_boxed_6001_, v_oldTraces_5992_, v_msg_5993_, v_resStartStop_5994_, v___y_5995_, v___y_5996_, v___y_5997_, v___y_5998_);
lean_dec_ref(v_opts_5990_);
return v_res_6002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal(lean_object* v_m_6004_, lean_object* v_a_6005_, lean_object* v_a_6006_, lean_object* v_a_6007_, lean_object* v_a_6008_){
_start:
{
lean_object* v_options_6010_; uint8_t v_hasTrace_6011_; lean_object* v_cls_6012_; 
v_options_6010_ = lean_ctor_get(v_a_6007_, 2);
v_hasTrace_6011_ = lean_ctor_get_uint8(v_options_6010_, sizeof(void*)*1);
v_cls_6012_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0));
if (v_hasTrace_6011_ == 0)
{
lean_object* v___x_6013_; lean_object* v___x_6014_; lean_object* v___x_6015_; lean_object* v___x_6016_; lean_object* v___f_6017_; lean_object* v___x_6018_; 
v___x_6013_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_6014_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__6(v_options_6010_, v___x_6013_);
v___x_6015_ = lean_unsigned_to_nat(2u);
v___x_6016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6016_, 0, v___x_6014_);
lean_ctor_set(v___x_6016_, 1, v___x_6015_);
v___f_6017_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___boxed), 10, 3);
lean_closure_set(v___f_6017_, 0, v_m_6004_);
lean_closure_set(v___f_6017_, 1, v___x_6016_);
lean_closure_set(v___f_6017_, 2, v_cls_6012_);
v___x_6018_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_6017_, v_a_6005_, v_a_6006_, v_a_6007_, v_a_6008_);
return v___x_6018_;
}
else
{
lean_object* v___x_6019_; lean_object* v_a_6020_; lean_object* v___f_6021_; lean_object* v___x_6022_; lean_object* v___y_6024_; lean_object* v___y_6025_; lean_object* v_a_6026_; lean_object* v___y_6040_; lean_object* v___y_6041_; lean_object* v_a_6042_; uint8_t v___x_6105_; 
v___x_6019_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg(v_cls_6012_, v_a_6007_);
v_a_6020_ = lean_ctor_get(v___x_6019_, 0);
lean_inc(v_a_6020_);
lean_dec_ref(v___x_6019_);
v___f_6021_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___closed__0));
v___x_6022_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__1___redArg___closed__1));
v___x_6105_ = lean_unbox(v_a_6020_);
if (v___x_6105_ == 0)
{
lean_object* v___x_6106_; uint8_t v___x_6107_; 
v___x_6106_ = l_Lean_trace_profiler;
v___x_6107_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2(v_options_6010_, v___x_6106_);
if (v___x_6107_ == 0)
{
lean_object* v___x_6108_; lean_object* v___x_6109_; lean_object* v___x_6110_; lean_object* v___x_6111_; lean_object* v___x_6112_; lean_object* v___f_6113_; lean_object* v___x_6114_; 
lean_dec(v_a_6020_);
v___x_6108_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_6109_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__6(v_options_6010_, v___x_6108_);
v___x_6110_ = lean_unsigned_to_nat(2u);
v___x_6111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6111_, 0, v___x_6109_);
lean_ctor_set(v___x_6111_, 1, v___x_6110_);
v___x_6112_ = lean_box(v_hasTrace_6011_);
v___f_6113_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__4___boxed), 11, 4);
lean_closure_set(v___f_6113_, 0, v_m_6004_);
lean_closure_set(v___f_6113_, 1, v___x_6111_);
lean_closure_set(v___f_6113_, 2, v_cls_6012_);
lean_closure_set(v___f_6113_, 3, v___x_6112_);
v___x_6114_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_6113_, v_a_6005_, v_a_6006_, v_a_6007_, v_a_6008_);
return v___x_6114_;
}
else
{
lean_inc_ref(v_options_6010_);
goto v___jp_6052_;
}
}
else
{
lean_inc_ref(v_options_6010_);
goto v___jp_6052_;
}
v___jp_6023_:
{
lean_object* v___x_6027_; double v___x_6028_; double v___x_6029_; double v___x_6030_; double v___x_6031_; double v___x_6032_; lean_object* v___x_6033_; lean_object* v___x_6034_; lean_object* v___x_6035_; lean_object* v___x_6036_; uint8_t v___x_6037_; lean_object* v___x_6038_; 
v___x_6027_ = lean_io_mono_nanos_now();
v___x_6028_ = lean_float_of_nat(v___y_6024_);
v___x_6029_ = lean_float_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4);
v___x_6030_ = lean_float_div(v___x_6028_, v___x_6029_);
v___x_6031_ = lean_float_of_nat(v___x_6027_);
v___x_6032_ = lean_float_div(v___x_6031_, v___x_6029_);
v___x_6033_ = lean_box_float(v___x_6030_);
v___x_6034_ = lean_box_float(v___x_6032_);
v___x_6035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6035_, 0, v___x_6033_);
lean_ctor_set(v___x_6035_, 1, v___x_6034_);
v___x_6036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6036_, 0, v_a_6026_);
lean_ctor_set(v___x_6036_, 1, v___x_6035_);
v___x_6037_ = lean_unbox(v_a_6020_);
lean_dec(v_a_6020_);
v___x_6038_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2(v_cls_6012_, v_hasTrace_6011_, v___x_6022_, v_options_6010_, v___x_6037_, v___y_6025_, v___f_6021_, v___x_6036_, v_a_6005_, v_a_6006_, v_a_6007_, v_a_6008_);
lean_dec_ref(v_options_6010_);
return v___x_6038_;
}
v___jp_6039_:
{
lean_object* v___x_6043_; double v___x_6044_; double v___x_6045_; lean_object* v___x_6046_; lean_object* v___x_6047_; lean_object* v___x_6048_; lean_object* v___x_6049_; uint8_t v___x_6050_; lean_object* v___x_6051_; 
v___x_6043_ = lean_io_get_num_heartbeats();
v___x_6044_ = lean_float_of_nat(v___y_6041_);
v___x_6045_ = lean_float_of_nat(v___x_6043_);
v___x_6046_ = lean_box_float(v___x_6044_);
v___x_6047_ = lean_box_float(v___x_6045_);
v___x_6048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6048_, 0, v___x_6046_);
lean_ctor_set(v___x_6048_, 1, v___x_6047_);
v___x_6049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6049_, 0, v_a_6042_);
lean_ctor_set(v___x_6049_, 1, v___x_6048_);
v___x_6050_ = lean_unbox(v_a_6020_);
lean_dec(v_a_6020_);
v___x_6051_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2(v_cls_6012_, v_hasTrace_6011_, v___x_6022_, v_options_6010_, v___x_6050_, v___y_6040_, v___f_6021_, v___x_6049_, v_a_6005_, v_a_6006_, v_a_6007_, v_a_6008_);
lean_dec_ref(v_options_6010_);
return v___x_6051_;
}
v___jp_6052_:
{
lean_object* v___x_6053_; lean_object* v_a_6054_; lean_object* v___x_6055_; uint8_t v___x_6056_; 
v___x_6053_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1___redArg(v_a_6008_);
v_a_6054_ = lean_ctor_get(v___x_6053_, 0);
lean_inc(v_a_6054_);
lean_dec_ref(v___x_6053_);
v___x_6055_ = l_Lean_trace_profiler_useHeartbeats;
v___x_6056_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2(v_options_6010_, v___x_6055_);
if (v___x_6056_ == 0)
{
lean_object* v___x_6057_; lean_object* v___x_6058_; lean_object* v___x_6059_; lean_object* v___x_6060_; lean_object* v___x_6061_; lean_object* v___x_6062_; lean_object* v___f_6063_; lean_object* v___x_6064_; 
v___x_6057_ = lean_io_mono_nanos_now();
v___x_6058_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_6059_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__6(v_options_6010_, v___x_6058_);
v___x_6060_ = lean_unsigned_to_nat(2u);
v___x_6061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6061_, 0, v___x_6059_);
lean_ctor_set(v___x_6061_, 1, v___x_6060_);
v___x_6062_ = lean_box(v_hasTrace_6011_);
v___f_6063_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__4___boxed), 11, 4);
lean_closure_set(v___f_6063_, 0, v_m_6004_);
lean_closure_set(v___f_6063_, 1, v___x_6061_);
lean_closure_set(v___f_6063_, 2, v_cls_6012_);
lean_closure_set(v___f_6063_, 3, v___x_6062_);
lean_inc(v_a_6008_);
lean_inc_ref(v_a_6007_);
lean_inc(v_a_6006_);
lean_inc_ref(v_a_6005_);
v___x_6064_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_6063_, v_a_6005_, v_a_6006_, v_a_6007_, v_a_6008_);
if (lean_obj_tag(v___x_6064_) == 0)
{
lean_object* v_a_6065_; lean_object* v___x_6067_; uint8_t v_isShared_6068_; uint8_t v_isSharedCheck_6072_; 
v_a_6065_ = lean_ctor_get(v___x_6064_, 0);
v_isSharedCheck_6072_ = !lean_is_exclusive(v___x_6064_);
if (v_isSharedCheck_6072_ == 0)
{
v___x_6067_ = v___x_6064_;
v_isShared_6068_ = v_isSharedCheck_6072_;
goto v_resetjp_6066_;
}
else
{
lean_inc(v_a_6065_);
lean_dec(v___x_6064_);
v___x_6067_ = lean_box(0);
v_isShared_6068_ = v_isSharedCheck_6072_;
goto v_resetjp_6066_;
}
v_resetjp_6066_:
{
lean_object* v___x_6070_; 
if (v_isShared_6068_ == 0)
{
lean_ctor_set_tag(v___x_6067_, 1);
v___x_6070_ = v___x_6067_;
goto v_reusejp_6069_;
}
else
{
lean_object* v_reuseFailAlloc_6071_; 
v_reuseFailAlloc_6071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6071_, 0, v_a_6065_);
v___x_6070_ = v_reuseFailAlloc_6071_;
goto v_reusejp_6069_;
}
v_reusejp_6069_:
{
v___y_6024_ = v___x_6057_;
v___y_6025_ = v_a_6054_;
v_a_6026_ = v___x_6070_;
goto v___jp_6023_;
}
}
}
else
{
lean_object* v_a_6073_; lean_object* v___x_6075_; uint8_t v_isShared_6076_; uint8_t v_isSharedCheck_6080_; 
v_a_6073_ = lean_ctor_get(v___x_6064_, 0);
v_isSharedCheck_6080_ = !lean_is_exclusive(v___x_6064_);
if (v_isSharedCheck_6080_ == 0)
{
v___x_6075_ = v___x_6064_;
v_isShared_6076_ = v_isSharedCheck_6080_;
goto v_resetjp_6074_;
}
else
{
lean_inc(v_a_6073_);
lean_dec(v___x_6064_);
v___x_6075_ = lean_box(0);
v_isShared_6076_ = v_isSharedCheck_6080_;
goto v_resetjp_6074_;
}
v_resetjp_6074_:
{
lean_object* v___x_6078_; 
if (v_isShared_6076_ == 0)
{
lean_ctor_set_tag(v___x_6075_, 0);
v___x_6078_ = v___x_6075_;
goto v_reusejp_6077_;
}
else
{
lean_object* v_reuseFailAlloc_6079_; 
v_reuseFailAlloc_6079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6079_, 0, v_a_6073_);
v___x_6078_ = v_reuseFailAlloc_6079_;
goto v_reusejp_6077_;
}
v_reusejp_6077_:
{
v___y_6024_ = v___x_6057_;
v___y_6025_ = v_a_6054_;
v_a_6026_ = v___x_6078_;
goto v___jp_6023_;
}
}
}
}
else
{
lean_object* v___x_6081_; lean_object* v___x_6082_; lean_object* v___x_6083_; lean_object* v___x_6084_; lean_object* v___x_6085_; lean_object* v___x_6086_; lean_object* v___f_6087_; lean_object* v___x_6088_; 
v___x_6081_ = lean_io_get_num_heartbeats();
v___x_6082_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_6083_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3_spec__6(v_options_6010_, v___x_6082_);
v___x_6084_ = lean_unsigned_to_nat(2u);
v___x_6085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6085_, 0, v___x_6083_);
lean_ctor_set(v___x_6085_, 1, v___x_6084_);
v___x_6086_ = lean_box(v___x_6056_);
v___f_6087_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__6___boxed), 11, 4);
lean_closure_set(v___f_6087_, 0, v_m_6004_);
lean_closure_set(v___f_6087_, 1, v___x_6085_);
lean_closure_set(v___f_6087_, 2, v_cls_6012_);
lean_closure_set(v___f_6087_, 3, v___x_6086_);
lean_inc(v_a_6008_);
lean_inc_ref(v_a_6007_);
lean_inc(v_a_6006_);
lean_inc_ref(v_a_6005_);
v___x_6088_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_6087_, v_a_6005_, v_a_6006_, v_a_6007_, v_a_6008_);
if (lean_obj_tag(v___x_6088_) == 0)
{
lean_object* v_a_6089_; lean_object* v___x_6091_; uint8_t v_isShared_6092_; uint8_t v_isSharedCheck_6096_; 
v_a_6089_ = lean_ctor_get(v___x_6088_, 0);
v_isSharedCheck_6096_ = !lean_is_exclusive(v___x_6088_);
if (v_isSharedCheck_6096_ == 0)
{
v___x_6091_ = v___x_6088_;
v_isShared_6092_ = v_isSharedCheck_6096_;
goto v_resetjp_6090_;
}
else
{
lean_inc(v_a_6089_);
lean_dec(v___x_6088_);
v___x_6091_ = lean_box(0);
v_isShared_6092_ = v_isSharedCheck_6096_;
goto v_resetjp_6090_;
}
v_resetjp_6090_:
{
lean_object* v___x_6094_; 
if (v_isShared_6092_ == 0)
{
lean_ctor_set_tag(v___x_6091_, 1);
v___x_6094_ = v___x_6091_;
goto v_reusejp_6093_;
}
else
{
lean_object* v_reuseFailAlloc_6095_; 
v_reuseFailAlloc_6095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6095_, 0, v_a_6089_);
v___x_6094_ = v_reuseFailAlloc_6095_;
goto v_reusejp_6093_;
}
v_reusejp_6093_:
{
v___y_6040_ = v_a_6054_;
v___y_6041_ = v___x_6081_;
v_a_6042_ = v___x_6094_;
goto v___jp_6039_;
}
}
}
else
{
lean_object* v_a_6097_; lean_object* v___x_6099_; uint8_t v_isShared_6100_; uint8_t v_isSharedCheck_6104_; 
v_a_6097_ = lean_ctor_get(v___x_6088_, 0);
v_isSharedCheck_6104_ = !lean_is_exclusive(v___x_6088_);
if (v_isSharedCheck_6104_ == 0)
{
v___x_6099_ = v___x_6088_;
v_isShared_6100_ = v_isSharedCheck_6104_;
goto v_resetjp_6098_;
}
else
{
lean_inc(v_a_6097_);
lean_dec(v___x_6088_);
v___x_6099_ = lean_box(0);
v_isShared_6100_ = v_isSharedCheck_6104_;
goto v_resetjp_6098_;
}
v_resetjp_6098_:
{
lean_object* v___x_6102_; 
if (v_isShared_6100_ == 0)
{
lean_ctor_set_tag(v___x_6099_, 0);
v___x_6102_ = v___x_6099_;
goto v_reusejp_6101_;
}
else
{
lean_object* v_reuseFailAlloc_6103_; 
v_reuseFailAlloc_6103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6103_, 0, v_a_6097_);
v___x_6102_ = v_reuseFailAlloc_6103_;
goto v_reusejp_6101_;
}
v_reusejp_6101_:
{
v___y_6040_ = v_a_6054_;
v___y_6041_ = v___x_6081_;
v_a_6042_ = v___x_6102_;
goto v___jp_6039_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___boxed(lean_object* v_m_6115_, lean_object* v_a_6116_, lean_object* v_a_6117_, lean_object* v_a_6118_, lean_object* v_a_6119_, lean_object* v_a_6120_){
_start:
{
lean_object* v_res_6121_; 
v_res_6121_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal(v_m_6115_, v_a_6116_, v_a_6117_, v_a_6118_, v_a_6119_);
return v_res_6121_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0(lean_object* v_00_u03b1_6122_, lean_object* v_msg_6123_, lean_object* v___y_6124_, lean_object* v___y_6125_, lean_object* v___y_6126_, lean_object* v___y_6127_, lean_object* v___y_6128_, lean_object* v___y_6129_){
_start:
{
lean_object* v___x_6131_; 
v___x_6131_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v_msg_6123_, v___y_6126_, v___y_6127_, v___y_6128_, v___y_6129_);
return v___x_6131_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___boxed(lean_object* v_00_u03b1_6132_, lean_object* v_msg_6133_, lean_object* v___y_6134_, lean_object* v___y_6135_, lean_object* v___y_6136_, lean_object* v___y_6137_, lean_object* v___y_6138_, lean_object* v___y_6139_, lean_object* v___y_6140_){
_start:
{
lean_object* v_res_6141_; 
v_res_6141_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0(v_00_u03b1_6132_, v_msg_6133_, v___y_6134_, v___y_6135_, v___y_6136_, v___y_6137_, v___y_6138_, v___y_6139_);
lean_dec(v___y_6139_);
lean_dec_ref(v___y_6138_);
lean_dec(v___y_6137_);
lean_dec_ref(v___y_6136_);
lean_dec(v___y_6135_);
lean_dec_ref(v___y_6134_);
return v_res_6141_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1(lean_object* v_cls_6142_, lean_object* v_msg_6143_, lean_object* v___y_6144_, lean_object* v___y_6145_, lean_object* v___y_6146_, lean_object* v___y_6147_, lean_object* v___y_6148_, lean_object* v___y_6149_){
_start:
{
lean_object* v___x_6151_; 
v___x_6151_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(v_cls_6142_, v_msg_6143_, v___y_6146_, v___y_6147_, v___y_6148_, v___y_6149_);
return v___x_6151_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___boxed(lean_object* v_cls_6152_, lean_object* v_msg_6153_, lean_object* v___y_6154_, lean_object* v___y_6155_, lean_object* v___y_6156_, lean_object* v___y_6157_, lean_object* v___y_6158_, lean_object* v___y_6159_, lean_object* v___y_6160_){
_start:
{
lean_object* v_res_6161_; 
v_res_6161_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1(v_cls_6152_, v_msg_6153_, v___y_6154_, v___y_6155_, v___y_6156_, v___y_6157_, v___y_6158_, v___y_6159_);
lean_dec(v___y_6159_);
lean_dec_ref(v___y_6158_);
lean_dec(v___y_6157_);
lean_dec_ref(v___y_6156_);
lean_dec(v___y_6155_);
lean_dec_ref(v___y_6154_);
return v_res_6161_;
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

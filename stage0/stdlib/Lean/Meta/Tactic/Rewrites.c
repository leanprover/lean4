// Lean compiler output
// Module: Lean.Meta.Tactic.Rewrites
// Imports: public import Lean.Meta.LazyDiscrTree public import Lean.Meta.Tactic.Rewrite public import Lean.Meta.Tactic.Refl public import Lean.Meta.Tactic.SolveByElim public import Lean.Meta.Tactic.TryThis public import Lean.Util.Heartbeats
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
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* l_Lean_MVarId_refl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_rewrite(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MVarId_assumption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SolveByElim_solveByElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_toLOption___redArg(lean_object*);
lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescopeReducing(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFnArgs(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_paren(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
uint8_t l_Lean_AsyncConstantInfo_isUnsafe(lean_object*);
uint8_t l_Lean_Meta_allowCompletion(lean_object*, lean_object*);
uint8_t l_Lean_Linter_isDeprecated(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t l_Lean_Name_isMetaprogramming(lean_object*);
lean_object* l_Lean_AsyncConstantInfo_toConstantVal(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getRemainingHeartbeats___redArg(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_ppExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_getMaxHeartbeats___redArg(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__0_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__0_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__0_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "rewrites"};
static const lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__0_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(186, 205, 46, 93, 234, 75, 44, 75)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(168, 155, 40, 124, 249, 233, 147, 160)}};
static const lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__3_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__3_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__3_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__4_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__3_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__4_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__4_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__5_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__5_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__5_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__6_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__4_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__5_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__6_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__6_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__7_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__7_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__7_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__8_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__6_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__7_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__8_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__8_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__9_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__8_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__0_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__9_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__9_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__10_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Rewrites"};
static const lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__10_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__10_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__11_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__9_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__10_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(198, 206, 142, 20, 34, 4, 12, 32)}};
static const lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__11_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__11_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__12_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__11_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(79, 110, 239, 104, 195, 0, 147, 113)}};
static const lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__12_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__12_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__13_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__12_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__5_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(98, 164, 76, 120, 62, 172, 121, 119)}};
static const lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__13_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__13_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__14_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__13_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__7_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(118, 133, 176, 63, 107, 91, 224, 141)}};
static const lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__14_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__14_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__15_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__14_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__10_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(55, 24, 242, 217, 59, 67, 106, 68)}};
static const lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__15_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__15_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__16_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__16_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__16_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__17_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__15_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__16_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(6, 160, 145, 196, 123, 32, 65, 209)}};
static const lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__17_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__17_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__18_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__18_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__18_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__19_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__17_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__18_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(183, 63, 117, 171, 186, 172, 103, 190)}};
static const lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__19_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__19_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__20_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__19_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__5_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(74, 251, 37, 185, 55, 190, 134, 39)}};
static const lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__20_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__20_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__21_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__20_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__7_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(110, 106, 163, 183, 60, 46, 37, 40)}};
static const lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__21_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__21_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__22_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__21_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__0_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(147, 13, 170, 221, 32, 240, 96, 44)}};
static const lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__22_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__22_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__23_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__22_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__10_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(86, 122, 118, 181, 205, 247, 113, 18)}};
static const lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__23_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__23_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__24_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__24_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__25_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__25_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__25_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__26_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__26_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__27_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__27_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__27_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__28_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__28_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__29_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__29_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__0_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "lemmas"};
static const lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__0_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__0_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__0_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(186, 205, 46, 93, 234, 75, 44, 75)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(168, 155, 40, 124, 249, 233, 147, 160)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__0_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(18, 2, 242, 27, 177, 68, 56, 130)}};
static const lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__23_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value),((lean_object*)(((size_t)(414759425) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(128, 187, 177, 155, 100, 254, 232, 115)}};
static const lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__3_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__25_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(87, 206, 218, 196, 232, 32, 33, 156)}};
static const lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__3_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__3_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__4_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__3_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__27_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(191, 183, 33, 48, 151, 181, 196, 249)}};
static const lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__4_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__4_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__5_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__4_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(250, 25, 56, 12, 246, 113, 116, 47)}};
static const lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__5_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__5_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Rewrites_rewriteResultLemma___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "congrArg"};
static const lean_object* l_Lean_Meta_Rewrites_rewriteResultLemma___closed__0 = (const lean_object*)&l_Lean_Meta_Rewrites_rewriteResultLemma___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Rewrites_rewriteResultLemma___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Rewrites_rewriteResultLemma___closed__0_value),LEAN_SCALAR_PTR_LITERAL(188, 17, 22, 243, 206, 91, 171, 36)}};
static const lean_object* l_Lean_Meta_Rewrites_rewriteResultLemma___closed__1 = (const lean_object*)&l_Lean_Meta_Rewrites_rewriteResultLemma___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rewriteResultLemma(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rewriteResultLemma___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_forwardWeight;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_backwardWeight;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_forward_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_forward_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_forward_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_forward_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_backward_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_backward_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_backward_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_backward_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Iff"};
static const lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__1(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_inj'"};
static const lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "injEq"};
static const lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "sizeOf_spec"};
static const lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_inj"};
static const lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_Rewrites_localHypotheses_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_Rewrites_localHypotheses_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_localHypotheses_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_localHypotheses_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1___closed__0 = (const lean_object*)&l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Rewrites_localHypotheses___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Rewrites_localHypotheses___closed__0 = (const lean_object*)&l_Lean_Meta_Rewrites_localHypotheses___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_localHypotheses(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_localHypotheses___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Rewrites_droppedKeys___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Rewrites_droppedKeys___closed__0 = (const lean_object*)&l_Lean_Meta_Rewrites_droppedKeys___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Rewrites_droppedKeys___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_Rewrites_droppedKeys___closed__1 = (const lean_object*)&l_Lean_Meta_Rewrites_droppedKeys___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Rewrites_droppedKeys___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Rewrites_droppedKeys___closed__1_value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Rewrites_droppedKeys___closed__2 = (const lean_object*)&l_Lean_Meta_Rewrites_droppedKeys___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Rewrites_droppedKeys___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1)),((lean_object*)&l_Lean_Meta_Rewrites_droppedKeys___closed__0_value)}};
static const lean_object* l_Lean_Meta_Rewrites_droppedKeys___closed__3 = (const lean_object*)&l_Lean_Meta_Rewrites_droppedKeys___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Rewrites_droppedKeys___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1)),((lean_object*)&l_Lean_Meta_Rewrites_droppedKeys___closed__3_value)}};
static const lean_object* l_Lean_Meta_Rewrites_droppedKeys___closed__4 = (const lean_object*)&l_Lean_Meta_Rewrites_droppedKeys___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Rewrites_droppedKeys___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Rewrites_droppedKeys___closed__2_value),((lean_object*)&l_Lean_Meta_Rewrites_droppedKeys___closed__4_value)}};
static const lean_object* l_Lean_Meta_Rewrites_droppedKeys___closed__5 = (const lean_object*)&l_Lean_Meta_Rewrites_droppedKeys___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Rewrites_droppedKeys___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Rewrites_droppedKeys___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Rewrites_droppedKeys___closed__6 = (const lean_object*)&l_Lean_Meta_Rewrites_droppedKeys___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Rewrites_droppedKeys___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Rewrites_droppedKeys___closed__0_value),((lean_object*)&l_Lean_Meta_Rewrites_droppedKeys___closed__6_value)}};
static const lean_object* l_Lean_Meta_Rewrites_droppedKeys___closed__7 = (const lean_object*)&l_Lean_Meta_Rewrites_droppedKeys___closed__7_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Rewrites_droppedKeys = (const lean_object*)&l_Lean_Meta_Rewrites_droppedKeys___closed__7_value;
static const lean_closure_object l_Lean_Meta_Rewrites_createModuleTreeRef___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Rewrites_createModuleTreeRef___closed__0 = (const lean_object*)&l_Lean_Meta_Rewrites_createModuleTreeRef___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_createModuleTreeRef(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_createModuleTreeRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_1824551397____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_1824551397____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_ext;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_constantsPerImportTask;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_incPrio(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Rewrites_rwFindDecls___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Rewrites_incPrio, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Rewrites_rwFindDecls___closed__0 = (const lean_object*)&l_Lean_Meta_Rewrites_rwFindDecls___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwFindDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwFindDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_none_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_none_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_none_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_none_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_assumption_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_assumption_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_assumption_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_assumption_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "failed"};
static const lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__0 = (const lean_object*)&l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Rewrites_solveByElim___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Rewrites_solveByElim___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Rewrites_solveByElim___closed__0 = (const lean_object*)&l_Lean_Meta_Rewrites_solveByElim___closed__0_value;
static const lean_closure_object l_Lean_Meta_Rewrites_solveByElim___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Rewrites_solveByElim___lam__1___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Rewrites_solveByElim___closed__1 = (const lean_object*)&l_Lean_Meta_Rewrites_solveByElim___closed__1_value;
static const lean_closure_object l_Lean_Meta_Rewrites_solveByElim___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Rewrites_solveByElim___lam__2___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Rewrites_solveByElim___closed__2 = (const lean_object*)&l_Lean_Meta_Rewrites_solveByElim___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Rewrites_solveByElim___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 1, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Rewrites_solveByElim___closed__3 = (const lean_object*)&l_Lean_Meta_Rewrites_solveByElim___closed__3_value;
static const lean_array_object l_Lean_Meta_Rewrites_solveByElim___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Rewrites_solveByElim___closed__4 = (const lean_object*)&l_Lean_Meta_Rewrites_solveByElim___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Rewrites_rwLemma_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Rewrites_rwLemma_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "symm"};
static const lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(220, 149, 144, 59, 77, 93, 25, 217)}};
static const lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(2, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__2_value;
static const lean_string_object l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__3 = (const lean_object*)&l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__4 = (const lean_object*)&l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5;
static const lean_string_object l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "considering "};
static const lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__6 = (const lean_object*)&l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__7;
static const lean_string_object l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 2, .m_data = "← "};
static const lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__8 = (const lean_object*)&l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__0 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__0_value;
static const lean_ctor_object l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__0_value)}};
static const lean_object* l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__1 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__1_value;
static lean_once_cell_t l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__2;
static lean_once_cell_t l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__3;
static const lean_string_object l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__4 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__4_value;
static const lean_string_object l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__5 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__5_value;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4(lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Rewrites_rewriteCandidates___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Rewrites_rewriteCandidates___closed__0 = (const lean_object*)&l_Lean_Meta_Rewrites_rewriteCandidates___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Rewrites_rewriteCandidates___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Rewrites_rewriteCandidates___closed__1;
static lean_once_cell_t l_Lean_Meta_Rewrites_rewriteCandidates___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Rewrites_rewriteCandidates___closed__2;
static lean_once_cell_t l_Lean_Meta_Rewrites_rewriteCandidates___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Rewrites_rewriteCandidates___closed__3;
static const lean_string_object l_Lean_Meta_Rewrites_rewriteCandidates___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Candidate rewrite lemmas:\n"};
static const lean_object* l_Lean_Meta_Rewrites_rewriteCandidates___closed__4 = (const lean_object*)&l_Lean_Meta_Rewrites_rewriteCandidates___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Rewrites_rewriteCandidates___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Rewrites_rewriteCandidates___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rewriteCandidates(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rewriteCandidates___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_newGoal(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_newGoal___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_takeListAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_takeListAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Rewrites_findRewrites___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Rewrites_findRewrites___closed__0;
static lean_once_cell_t l_Lean_Meta_Rewrites_findRewrites___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Rewrites_findRewrites___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_findRewrites(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_findRewrites___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__24_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_57_ = lean_unsigned_to_nat(2316440083u);
v___x_58_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__23_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_));
v___x_59_ = l_Lean_Name_num___override(v___x_58_, v___x_57_);
return v___x_59_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__26_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_61_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__25_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_));
v___x_62_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__24_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__24_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__24_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_);
v___x_63_ = l_Lean_Name_str___override(v___x_62_, v___x_61_);
return v___x_63_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__28_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_65_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__27_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_));
v___x_66_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__26_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__26_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__26_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_);
v___x_67_ = l_Lean_Name_str___override(v___x_66_, v___x_65_);
return v___x_67_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__29_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_68_ = lean_unsigned_to_nat(2u);
v___x_69_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__28_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__28_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__28_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_);
v___x_70_ = l_Lean_Name_num___override(v___x_69_, v___x_68_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_72_; uint8_t v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_72_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_));
v___x_73_ = 0;
v___x_74_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__29_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__29_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__29_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_);
v___x_75_ = l_Lean_registerTraceClass(v___x_72_, v___x_73_, v___x_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2____boxed(lean_object* v_a_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_();
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_96_; uint8_t v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_96_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_));
v___x_97_ = 0;
v___x_98_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__5_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_));
v___x_99_ = l_Lean_registerTraceClass(v___x_96_, v___x_97_, v___x_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2____boxed(lean_object* v_a_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_();
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rewriteResultLemma(lean_object* v_r_105_){
_start:
{
lean_object* v_eqProof_106_; lean_object* v___x_107_; lean_object* v___x_108_; uint8_t v___x_109_; 
v_eqProof_106_ = lean_ctor_get(v_r_105_, 1);
v___x_107_ = ((lean_object*)(l_Lean_Meta_Rewrites_rewriteResultLemma___closed__1));
v___x_108_ = lean_unsigned_to_nat(6u);
v___x_109_ = l_Lean_Expr_isAppOfArity(v_eqProof_106_, v___x_107_, v___x_108_);
if (v___x_109_ == 0)
{
lean_object* v___x_110_; 
v___x_110_ = lean_box(0);
return v___x_110_;
}
else
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_111_ = lean_unsigned_to_nat(5u);
v___x_112_ = l_Lean_Expr_getAppNumArgs(v_eqProof_106_);
v___x_113_ = lean_nat_sub(v___x_112_, v___x_111_);
lean_dec(v___x_112_);
v___x_114_ = lean_unsigned_to_nat(1u);
v___x_115_ = lean_nat_sub(v___x_113_, v___x_114_);
lean_dec(v___x_113_);
v___x_116_ = l_Lean_Expr_getRevArg_x21(v_eqProof_106_, v___x_115_);
v___x_117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_117_, 0, v___x_116_);
return v___x_117_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rewriteResultLemma___boxed(lean_object* v_r_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Lean_Meta_Rewrites_rewriteResultLemma(v_r_118_);
lean_dec_ref(v_r_118_);
return v_res_119_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_forwardWeight(void){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = lean_unsigned_to_nat(2u);
return v___x_120_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_backwardWeight(void){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = lean_unsigned_to_nat(1u);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_ctorIdx(uint8_t v_x_122_){
_start:
{
if (v_x_122_ == 0)
{
lean_object* v___x_123_; 
v___x_123_ = lean_unsigned_to_nat(0u);
return v___x_123_;
}
else
{
lean_object* v___x_124_; 
v___x_124_ = lean_unsigned_to_nat(1u);
return v___x_124_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_ctorIdx___boxed(lean_object* v_x_125_){
_start:
{
uint8_t v_x_boxed_126_; lean_object* v_res_127_; 
v_x_boxed_126_ = lean_unbox(v_x_125_);
v_res_127_ = l_Lean_Meta_Rewrites_RwDirection_ctorIdx(v_x_boxed_126_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_toCtorIdx(uint8_t v_x_128_){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = l_Lean_Meta_Rewrites_RwDirection_ctorIdx(v_x_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_toCtorIdx___boxed(lean_object* v_x_130_){
_start:
{
uint8_t v_x_4__boxed_131_; lean_object* v_res_132_; 
v_x_4__boxed_131_ = lean_unbox(v_x_130_);
v_res_132_ = l_Lean_Meta_Rewrites_RwDirection_toCtorIdx(v_x_4__boxed_131_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_ctorElim___redArg(lean_object* v_k_133_){
_start:
{
lean_inc(v_k_133_);
return v_k_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_ctorElim___redArg___boxed(lean_object* v_k_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_Lean_Meta_Rewrites_RwDirection_ctorElim___redArg(v_k_134_);
lean_dec(v_k_134_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_ctorElim(lean_object* v_motive_136_, lean_object* v_ctorIdx_137_, uint8_t v_t_138_, lean_object* v_h_139_, lean_object* v_k_140_){
_start:
{
lean_inc(v_k_140_);
return v_k_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_ctorElim___boxed(lean_object* v_motive_141_, lean_object* v_ctorIdx_142_, lean_object* v_t_143_, lean_object* v_h_144_, lean_object* v_k_145_){
_start:
{
uint8_t v_t_boxed_146_; lean_object* v_res_147_; 
v_t_boxed_146_ = lean_unbox(v_t_143_);
v_res_147_ = l_Lean_Meta_Rewrites_RwDirection_ctorElim(v_motive_141_, v_ctorIdx_142_, v_t_boxed_146_, v_h_144_, v_k_145_);
lean_dec(v_k_145_);
lean_dec(v_ctorIdx_142_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_forward_elim___redArg(lean_object* v_forward_148_){
_start:
{
lean_inc(v_forward_148_);
return v_forward_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_forward_elim___redArg___boxed(lean_object* v_forward_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Lean_Meta_Rewrites_RwDirection_forward_elim___redArg(v_forward_149_);
lean_dec(v_forward_149_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_forward_elim(lean_object* v_motive_151_, uint8_t v_t_152_, lean_object* v_h_153_, lean_object* v_forward_154_){
_start:
{
lean_inc(v_forward_154_);
return v_forward_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_forward_elim___boxed(lean_object* v_motive_155_, lean_object* v_t_156_, lean_object* v_h_157_, lean_object* v_forward_158_){
_start:
{
uint8_t v_t_boxed_159_; lean_object* v_res_160_; 
v_t_boxed_159_ = lean_unbox(v_t_156_);
v_res_160_ = l_Lean_Meta_Rewrites_RwDirection_forward_elim(v_motive_155_, v_t_boxed_159_, v_h_157_, v_forward_158_);
lean_dec(v_forward_158_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_backward_elim___redArg(lean_object* v_backward_161_){
_start:
{
lean_inc(v_backward_161_);
return v_backward_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_backward_elim___redArg___boxed(lean_object* v_backward_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_Lean_Meta_Rewrites_RwDirection_backward_elim___redArg(v_backward_162_);
lean_dec(v_backward_162_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_backward_elim(lean_object* v_motive_164_, uint8_t v_t_165_, lean_object* v_h_166_, lean_object* v_backward_167_){
_start:
{
lean_inc(v_backward_167_);
return v_backward_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_backward_elim___boxed(lean_object* v_motive_168_, lean_object* v_t_169_, lean_object* v_h_170_, lean_object* v_backward_171_){
_start:
{
uint8_t v_t_boxed_172_; lean_object* v_res_173_; 
v_t_boxed_172_ = lean_unbox(v_t_169_);
v_res_173_ = l_Lean_Meta_Rewrites_RwDirection_backward_elim(v_motive_168_, v_t_boxed_172_, v_h_170_, v_backward_171_);
lean_dec(v_backward_171_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___lam__0(lean_object* v_k_174_, lean_object* v_b_175_, lean_object* v_c_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_){
_start:
{
lean_object* v___x_182_; 
lean_inc(v___y_180_);
lean_inc_ref(v___y_179_);
lean_inc(v___y_178_);
lean_inc_ref(v___y_177_);
v___x_182_ = lean_apply_7(v_k_174_, v_b_175_, v_c_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_, lean_box(0));
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___lam__0___boxed(lean_object* v_k_183_, lean_object* v_b_184_, lean_object* v_c_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___lam__0(v_k_183_, v_b_184_, v_c_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_);
lean_dec(v___y_189_);
lean_dec_ref(v___y_188_);
lean_dec(v___y_187_);
lean_dec_ref(v___y_186_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg(lean_object* v_type_192_, lean_object* v_k_193_, uint8_t v_cleanupAnnotations_194_, uint8_t v_whnfType_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
lean_object* v___f_201_; lean_object* v___x_202_; 
v___f_201_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_201_, 0, v_k_193_);
v___x_202_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_192_, v___f_201_, v_cleanupAnnotations_194_, v_whnfType_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_);
if (lean_obj_tag(v___x_202_) == 0)
{
lean_object* v_a_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_210_; 
v_a_203_ = lean_ctor_get(v___x_202_, 0);
v_isSharedCheck_210_ = !lean_is_exclusive(v___x_202_);
if (v_isSharedCheck_210_ == 0)
{
v___x_205_ = v___x_202_;
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_a_203_);
lean_dec(v___x_202_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_208_; 
if (v_isShared_206_ == 0)
{
v___x_208_ = v___x_205_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v_a_203_);
v___x_208_ = v_reuseFailAlloc_209_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
return v___x_208_;
}
}
}
else
{
lean_object* v_a_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_218_; 
v_a_211_ = lean_ctor_get(v___x_202_, 0);
v_isSharedCheck_218_ = !lean_is_exclusive(v___x_202_);
if (v_isSharedCheck_218_ == 0)
{
v___x_213_ = v___x_202_;
v_isShared_214_ = v_isSharedCheck_218_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_a_211_);
lean_dec(v___x_202_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_218_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v___x_216_; 
if (v_isShared_214_ == 0)
{
v___x_216_ = v___x_213_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_a_211_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
return v___x_216_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___boxed(lean_object* v_type_219_, lean_object* v_k_220_, lean_object* v_cleanupAnnotations_221_, lean_object* v_whnfType_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_228_; uint8_t v_whnfType_boxed_229_; lean_object* v_res_230_; 
v_cleanupAnnotations_boxed_228_ = lean_unbox(v_cleanupAnnotations_221_);
v_whnfType_boxed_229_ = lean_unbox(v_whnfType_222_);
v_res_230_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg(v_type_219_, v_k_220_, v_cleanupAnnotations_boxed_228_, v_whnfType_boxed_229_, v___y_223_, v___y_224_, v___y_225_, v___y_226_);
lean_dec(v___y_226_);
lean_dec_ref(v___y_225_);
lean_dec(v___y_224_);
lean_dec_ref(v___y_223_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0(lean_object* v_00_u03b1_231_, lean_object* v_type_232_, lean_object* v_k_233_, uint8_t v_cleanupAnnotations_234_, uint8_t v_whnfType_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg(v_type_232_, v_k_233_, v_cleanupAnnotations_234_, v_whnfType_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___boxed(lean_object* v_00_u03b1_242_, lean_object* v_type_243_, lean_object* v_k_244_, lean_object* v_cleanupAnnotations_245_, lean_object* v_whnfType_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_252_; uint8_t v_whnfType_boxed_253_; lean_object* v_res_254_; 
v_cleanupAnnotations_boxed_252_ = lean_unbox(v_cleanupAnnotations_245_);
v_whnfType_boxed_253_ = lean_unbox(v_whnfType_246_);
v_res_254_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0(v_00_u03b1_242_, v_type_243_, v_k_244_, v_cleanupAnnotations_boxed_252_, v_whnfType_boxed_253_, v___y_247_, v___y_248_, v___y_249_, v___y_250_);
lean_dec(v___y_250_);
lean_dec_ref(v___y_249_);
lean_dec(v___y_248_);
lean_dec_ref(v___y_247_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1___redArg(lean_object* v_k_255_, uint8_t v_allowLevelAssignments_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
lean_object* v___x_262_; 
v___x_262_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_256_, v_k_255_, v___y_257_, v___y_258_, v___y_259_, v___y_260_);
if (lean_obj_tag(v___x_262_) == 0)
{
lean_object* v_a_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_270_; 
v_a_263_ = lean_ctor_get(v___x_262_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_262_);
if (v_isSharedCheck_270_ == 0)
{
v___x_265_ = v___x_262_;
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_a_263_);
lean_dec(v___x_262_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_268_; 
if (v_isShared_266_ == 0)
{
v___x_268_ = v___x_265_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_a_263_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
else
{
lean_object* v_a_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_278_; 
v_a_271_ = lean_ctor_get(v___x_262_, 0);
v_isSharedCheck_278_ = !lean_is_exclusive(v___x_262_);
if (v_isSharedCheck_278_ == 0)
{
v___x_273_ = v___x_262_;
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_a_271_);
lean_dec(v___x_262_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_276_; 
if (v_isShared_274_ == 0)
{
v___x_276_ = v___x_273_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_a_271_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1___redArg___boxed(lean_object* v_k_279_, lean_object* v_allowLevelAssignments_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_286_; lean_object* v_res_287_; 
v_allowLevelAssignments_boxed_286_ = lean_unbox(v_allowLevelAssignments_280_);
v_res_287_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1___redArg(v_k_279_, v_allowLevelAssignments_boxed_286_, v___y_281_, v___y_282_, v___y_283_, v___y_284_);
lean_dec(v___y_284_);
lean_dec_ref(v___y_283_);
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1(lean_object* v_00_u03b1_288_, lean_object* v_k_289_, uint8_t v_allowLevelAssignments_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1___redArg(v_k_289_, v_allowLevelAssignments_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1___boxed(lean_object* v_00_u03b1_297_, lean_object* v_k_298_, lean_object* v_allowLevelAssignments_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_305_; lean_object* v_res_306_; 
v_allowLevelAssignments_boxed_305_ = lean_unbox(v_allowLevelAssignments_299_);
v_res_306_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1(v_00_u03b1_297_, v_k_298_, v_allowLevelAssignments_boxed_305_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0(lean_object* v_name_311_, lean_object* v_x_312_, lean_object* v_type_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_){
_start:
{
lean_object* v___x_322_; lean_object* v_fst_323_; 
v___x_322_ = l_Lean_Expr_getAppFnArgs(v_type_313_);
v_fst_323_ = lean_ctor_get(v___x_322_, 0);
lean_inc(v_fst_323_);
if (lean_obj_tag(v_fst_323_) == 1)
{
lean_object* v_pre_324_; 
v_pre_324_ = lean_ctor_get(v_fst_323_, 0);
if (lean_obj_tag(v_pre_324_) == 0)
{
lean_object* v_snd_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_424_; 
v_snd_325_ = lean_ctor_get(v___x_322_, 1);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_322_);
if (v_isSharedCheck_424_ == 0)
{
lean_object* v_unused_425_; 
v_unused_425_ = lean_ctor_get(v___x_322_, 0);
lean_dec(v_unused_425_);
v___x_327_ = v___x_322_;
v_isShared_328_ = v_isSharedCheck_424_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_snd_325_);
lean_dec(v___x_322_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_424_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v_str_329_; lean_object* v___x_330_; uint8_t v___x_331_; 
v_str_329_ = lean_ctor_get(v_fst_323_, 1);
lean_inc_ref(v_str_329_);
lean_dec_ref_known(v_fst_323_, 2);
v___x_330_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__1));
v___x_331_ = lean_string_dec_eq(v_str_329_, v___x_330_);
if (v___x_331_ == 0)
{
lean_object* v___x_332_; uint8_t v___x_333_; 
v___x_332_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__2));
v___x_333_ = lean_string_dec_eq(v_str_329_, v___x_332_);
lean_dec_ref(v_str_329_);
if (v___x_333_ == 0)
{
lean_del_object(v___x_327_);
lean_dec(v_snd_325_);
lean_dec(v_name_311_);
goto v___jp_319_;
}
else
{
lean_object* v___x_334_; lean_object* v___x_335_; uint8_t v___x_336_; 
v___x_334_ = lean_array_get_size(v_snd_325_);
v___x_335_ = lean_unsigned_to_nat(2u);
v___x_336_ = lean_nat_dec_eq(v___x_334_, v___x_335_);
if (v___x_336_ == 0)
{
lean_del_object(v___x_327_);
lean_dec(v_snd_325_);
lean_dec(v_name_311_);
goto v___jp_319_;
}
else
{
lean_object* v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; lean_object* v___x_340_; lean_object* v___x_342_; 
v___x_337_ = lean_unsigned_to_nat(0u);
v___x_338_ = lean_array_fget_borrowed(v_snd_325_, v___x_337_);
v___x_339_ = 0;
v___x_340_ = lean_box(v___x_339_);
lean_inc(v_name_311_);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 1, v___x_340_);
lean_ctor_set(v___x_327_, 0, v_name_311_);
v___x_342_ = v___x_327_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_name_311_);
lean_ctor_set(v_reuseFailAlloc_378_, 1, v___x_340_);
v___x_342_ = v_reuseFailAlloc_378_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
lean_object* v___x_343_; 
lean_inc(v___x_338_);
v___x_343_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(v___x_338_, v___x_342_, v___y_314_, v___y_315_, v___y_316_, v___y_317_);
if (lean_obj_tag(v___x_343_) == 0)
{
lean_object* v_a_344_; lean_object* v___x_345_; lean_object* v___x_346_; uint8_t v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v_a_344_ = lean_ctor_get(v___x_343_, 0);
lean_inc(v_a_344_);
lean_dec_ref_known(v___x_343_, 1);
v___x_345_ = lean_unsigned_to_nat(1u);
v___x_346_ = lean_array_fget(v_snd_325_, v___x_345_);
lean_dec(v_snd_325_);
v___x_347_ = 1;
v___x_348_ = lean_box(v___x_347_);
v___x_349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_349_, 0, v_name_311_);
lean_ctor_set(v___x_349_, 1, v___x_348_);
v___x_350_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(v___x_346_, v___x_349_, v___y_314_, v___y_315_, v___y_316_, v___y_317_);
if (lean_obj_tag(v___x_350_) == 0)
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_361_; 
v_a_351_ = lean_ctor_get(v___x_350_, 0);
v_isSharedCheck_361_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_361_ == 0)
{
v___x_353_ = v___x_350_;
v_isShared_354_ = v_isSharedCheck_361_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_350_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_361_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_359_; 
v___x_355_ = lean_mk_empty_array_with_capacity(v___x_335_);
v___x_356_ = lean_array_push(v___x_355_, v_a_344_);
v___x_357_ = lean_array_push(v___x_356_, v_a_351_);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 0, v___x_357_);
v___x_359_ = v___x_353_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v___x_357_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
}
else
{
lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_369_; 
lean_dec(v_a_344_);
v_a_362_ = lean_ctor_get(v___x_350_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_369_ == 0)
{
v___x_364_ = v___x_350_;
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_a_362_);
lean_dec(v___x_350_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_367_; 
if (v_isShared_365_ == 0)
{
v___x_367_ = v___x_364_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_a_362_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
}
else
{
lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_377_; 
lean_dec(v_snd_325_);
lean_dec(v_name_311_);
v_a_370_ = lean_ctor_get(v___x_343_, 0);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_377_ == 0)
{
v___x_372_ = v___x_343_;
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_dec(v___x_343_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_375_; 
if (v_isShared_373_ == 0)
{
v___x_375_ = v___x_372_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_a_370_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_379_; lean_object* v___x_380_; uint8_t v___x_381_; 
lean_dec_ref(v_str_329_);
v___x_379_ = lean_array_get_size(v_snd_325_);
v___x_380_ = lean_unsigned_to_nat(3u);
v___x_381_ = lean_nat_dec_eq(v___x_379_, v___x_380_);
if (v___x_381_ == 0)
{
lean_del_object(v___x_327_);
lean_dec(v_snd_325_);
lean_dec(v_name_311_);
goto v___jp_319_;
}
else
{
lean_object* v___x_382_; lean_object* v___x_383_; uint8_t v___x_384_; lean_object* v___x_385_; lean_object* v___x_387_; 
v___x_382_ = lean_unsigned_to_nat(1u);
v___x_383_ = lean_array_fget_borrowed(v_snd_325_, v___x_382_);
v___x_384_ = 0;
v___x_385_ = lean_box(v___x_384_);
lean_inc(v_name_311_);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 1, v___x_385_);
lean_ctor_set(v___x_327_, 0, v_name_311_);
v___x_387_ = v___x_327_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_name_311_);
lean_ctor_set(v_reuseFailAlloc_423_, 1, v___x_385_);
v___x_387_ = v_reuseFailAlloc_423_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
lean_object* v___x_388_; 
lean_inc(v___x_383_);
v___x_388_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(v___x_383_, v___x_387_, v___y_314_, v___y_315_, v___y_316_, v___y_317_);
if (lean_obj_tag(v___x_388_) == 0)
{
lean_object* v_a_389_; lean_object* v___x_390_; lean_object* v___x_391_; uint8_t v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v_a_389_ = lean_ctor_get(v___x_388_, 0);
lean_inc(v_a_389_);
lean_dec_ref_known(v___x_388_, 1);
v___x_390_ = lean_unsigned_to_nat(2u);
v___x_391_ = lean_array_fget(v_snd_325_, v___x_390_);
lean_dec(v_snd_325_);
v___x_392_ = 1;
v___x_393_ = lean_box(v___x_392_);
v___x_394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_394_, 0, v_name_311_);
lean_ctor_set(v___x_394_, 1, v___x_393_);
v___x_395_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(v___x_391_, v___x_394_, v___y_314_, v___y_315_, v___y_316_, v___y_317_);
if (lean_obj_tag(v___x_395_) == 0)
{
lean_object* v_a_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_406_; 
v_a_396_ = lean_ctor_get(v___x_395_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_406_ == 0)
{
v___x_398_ = v___x_395_;
v_isShared_399_ = v_isSharedCheck_406_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_a_396_);
lean_dec(v___x_395_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_406_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_404_; 
v___x_400_ = lean_mk_empty_array_with_capacity(v___x_390_);
v___x_401_ = lean_array_push(v___x_400_, v_a_389_);
v___x_402_ = lean_array_push(v___x_401_, v_a_396_);
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 0, v___x_402_);
v___x_404_ = v___x_398_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_402_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
else
{
lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_414_; 
lean_dec(v_a_389_);
v_a_407_ = lean_ctor_get(v___x_395_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_414_ == 0)
{
v___x_409_ = v___x_395_;
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v___x_395_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_412_; 
if (v_isShared_410_ == 0)
{
v___x_412_ = v___x_409_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_a_407_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
}
else
{
lean_object* v_a_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_422_; 
lean_dec(v_snd_325_);
lean_dec(v_name_311_);
v_a_415_ = lean_ctor_get(v___x_388_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_422_ == 0)
{
v___x_417_ = v___x_388_;
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_a_415_);
lean_dec(v___x_388_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_420_; 
if (v_isShared_418_ == 0)
{
v___x_420_ = v___x_417_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_a_415_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
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
lean_dec_ref_known(v_fst_323_, 2);
lean_dec_ref(v___x_322_);
lean_dec(v_name_311_);
goto v___jp_319_;
}
}
else
{
lean_dec(v_fst_323_);
lean_dec_ref(v___x_322_);
lean_dec(v_name_311_);
goto v___jp_319_;
}
v___jp_319_:
{
lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_320_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0));
v___x_321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_321_, 0, v___x_320_);
return v___x_321_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___boxed(lean_object* v_name_426_, lean_object* v_x_427_, lean_object* v_type_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0(v_name_426_, v_x_427_, v_type_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
lean_dec(v___y_430_);
lean_dec_ref(v___y_429_);
lean_dec_ref(v_x_427_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__1(uint8_t v___x_435_, lean_object* v_type_436_, lean_object* v___f_437_, uint8_t v___x_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
lean_object* v___x_444_; uint8_t v_foApprox_445_; uint8_t v_ctxApprox_446_; uint8_t v_quasiPatternApprox_447_; uint8_t v_constApprox_448_; uint8_t v_isDefEqStuckEx_449_; uint8_t v_unificationHints_450_; uint8_t v_proofIrrelevance_451_; uint8_t v_assignSyntheticOpaque_452_; uint8_t v_offsetCnstrs_453_; uint8_t v_etaStruct_454_; uint8_t v_univApprox_455_; uint8_t v_iota_456_; uint8_t v_beta_457_; uint8_t v_proj_458_; uint8_t v_zeta_459_; uint8_t v_zetaDelta_460_; uint8_t v_zetaUnused_461_; uint8_t v_zetaHave_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_501_; 
v___x_444_ = l_Lean_Meta_Context_config(v___y_439_);
v_foApprox_445_ = lean_ctor_get_uint8(v___x_444_, 0);
v_ctxApprox_446_ = lean_ctor_get_uint8(v___x_444_, 1);
v_quasiPatternApprox_447_ = lean_ctor_get_uint8(v___x_444_, 2);
v_constApprox_448_ = lean_ctor_get_uint8(v___x_444_, 3);
v_isDefEqStuckEx_449_ = lean_ctor_get_uint8(v___x_444_, 4);
v_unificationHints_450_ = lean_ctor_get_uint8(v___x_444_, 5);
v_proofIrrelevance_451_ = lean_ctor_get_uint8(v___x_444_, 6);
v_assignSyntheticOpaque_452_ = lean_ctor_get_uint8(v___x_444_, 7);
v_offsetCnstrs_453_ = lean_ctor_get_uint8(v___x_444_, 8);
v_etaStruct_454_ = lean_ctor_get_uint8(v___x_444_, 10);
v_univApprox_455_ = lean_ctor_get_uint8(v___x_444_, 11);
v_iota_456_ = lean_ctor_get_uint8(v___x_444_, 12);
v_beta_457_ = lean_ctor_get_uint8(v___x_444_, 13);
v_proj_458_ = lean_ctor_get_uint8(v___x_444_, 14);
v_zeta_459_ = lean_ctor_get_uint8(v___x_444_, 15);
v_zetaDelta_460_ = lean_ctor_get_uint8(v___x_444_, 16);
v_zetaUnused_461_ = lean_ctor_get_uint8(v___x_444_, 17);
v_zetaHave_462_ = lean_ctor_get_uint8(v___x_444_, 18);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_501_ == 0)
{
v___x_464_ = v___x_444_;
v_isShared_465_ = v_isSharedCheck_501_;
goto v_resetjp_463_;
}
else
{
lean_dec(v___x_444_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_501_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
uint8_t v_trackZetaDelta_466_; lean_object* v_zetaDeltaSet_467_; lean_object* v_lctx_468_; lean_object* v_localInstances_469_; lean_object* v_defEqCtx_x3f_470_; lean_object* v_synthPendingDepth_471_; lean_object* v_canUnfold_x3f_472_; uint8_t v_univApprox_473_; uint8_t v_inTypeClassResolution_474_; uint8_t v_cacheInferType_475_; lean_object* v_config_477_; 
v_trackZetaDelta_466_ = lean_ctor_get_uint8(v___y_439_, sizeof(void*)*7);
v_zetaDeltaSet_467_ = lean_ctor_get(v___y_439_, 1);
lean_inc(v_zetaDeltaSet_467_);
v_lctx_468_ = lean_ctor_get(v___y_439_, 2);
lean_inc_ref(v_lctx_468_);
v_localInstances_469_ = lean_ctor_get(v___y_439_, 3);
lean_inc_ref(v_localInstances_469_);
v_defEqCtx_x3f_470_ = lean_ctor_get(v___y_439_, 4);
lean_inc(v_defEqCtx_x3f_470_);
v_synthPendingDepth_471_ = lean_ctor_get(v___y_439_, 5);
lean_inc(v_synthPendingDepth_471_);
v_canUnfold_x3f_472_ = lean_ctor_get(v___y_439_, 6);
lean_inc(v_canUnfold_x3f_472_);
v_univApprox_473_ = lean_ctor_get_uint8(v___y_439_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_474_ = lean_ctor_get_uint8(v___y_439_, sizeof(void*)*7 + 2);
v_cacheInferType_475_ = lean_ctor_get_uint8(v___y_439_, sizeof(void*)*7 + 3);
if (v_isShared_465_ == 0)
{
v_config_477_ = v___x_464_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_500_, 0, v_foApprox_445_);
lean_ctor_set_uint8(v_reuseFailAlloc_500_, 1, v_ctxApprox_446_);
lean_ctor_set_uint8(v_reuseFailAlloc_500_, 2, v_quasiPatternApprox_447_);
lean_ctor_set_uint8(v_reuseFailAlloc_500_, 3, v_constApprox_448_);
lean_ctor_set_uint8(v_reuseFailAlloc_500_, 4, v_isDefEqStuckEx_449_);
lean_ctor_set_uint8(v_reuseFailAlloc_500_, 5, v_unificationHints_450_);
lean_ctor_set_uint8(v_reuseFailAlloc_500_, 6, v_proofIrrelevance_451_);
lean_ctor_set_uint8(v_reuseFailAlloc_500_, 7, v_assignSyntheticOpaque_452_);
lean_ctor_set_uint8(v_reuseFailAlloc_500_, 8, v_offsetCnstrs_453_);
lean_ctor_set_uint8(v_reuseFailAlloc_500_, 10, v_etaStruct_454_);
lean_ctor_set_uint8(v_reuseFailAlloc_500_, 11, v_univApprox_455_);
lean_ctor_set_uint8(v_reuseFailAlloc_500_, 12, v_iota_456_);
lean_ctor_set_uint8(v_reuseFailAlloc_500_, 13, v_beta_457_);
lean_ctor_set_uint8(v_reuseFailAlloc_500_, 14, v_proj_458_);
lean_ctor_set_uint8(v_reuseFailAlloc_500_, 15, v_zeta_459_);
lean_ctor_set_uint8(v_reuseFailAlloc_500_, 16, v_zetaDelta_460_);
lean_ctor_set_uint8(v_reuseFailAlloc_500_, 17, v_zetaUnused_461_);
lean_ctor_set_uint8(v_reuseFailAlloc_500_, 18, v_zetaHave_462_);
v_config_477_ = v_reuseFailAlloc_500_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
uint64_t v___x_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_492_; 
lean_ctor_set_uint8(v_config_477_, 9, v___x_435_);
v___x_478_ = l_Lean_Meta_Context_configKey(v___y_439_);
v_isSharedCheck_492_ = !lean_is_exclusive(v___y_439_);
if (v_isSharedCheck_492_ == 0)
{
lean_object* v_unused_493_; lean_object* v_unused_494_; lean_object* v_unused_495_; lean_object* v_unused_496_; lean_object* v_unused_497_; lean_object* v_unused_498_; lean_object* v_unused_499_; 
v_unused_493_ = lean_ctor_get(v___y_439_, 6);
lean_dec(v_unused_493_);
v_unused_494_ = lean_ctor_get(v___y_439_, 5);
lean_dec(v_unused_494_);
v_unused_495_ = lean_ctor_get(v___y_439_, 4);
lean_dec(v_unused_495_);
v_unused_496_ = lean_ctor_get(v___y_439_, 3);
lean_dec(v_unused_496_);
v_unused_497_ = lean_ctor_get(v___y_439_, 2);
lean_dec(v_unused_497_);
v_unused_498_ = lean_ctor_get(v___y_439_, 1);
lean_dec(v_unused_498_);
v_unused_499_ = lean_ctor_get(v___y_439_, 0);
lean_dec(v_unused_499_);
v___x_480_ = v___y_439_;
v_isShared_481_ = v_isSharedCheck_492_;
goto v_resetjp_479_;
}
else
{
lean_dec(v___y_439_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_492_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
uint64_t v___x_482_; uint64_t v___x_483_; uint64_t v___x_484_; uint64_t v___x_485_; uint64_t v_key_486_; lean_object* v___x_487_; lean_object* v___x_489_; 
v___x_482_ = 3ULL;
v___x_483_ = lean_uint64_shift_right(v___x_478_, v___x_482_);
v___x_484_ = lean_uint64_shift_left(v___x_483_, v___x_482_);
v___x_485_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_435_);
v_key_486_ = lean_uint64_lor(v___x_484_, v___x_485_);
v___x_487_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_487_, 0, v_config_477_);
lean_ctor_set_uint64(v___x_487_, sizeof(void*)*1, v_key_486_);
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 0, v___x_487_);
v___x_489_ = v___x_480_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v___x_487_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v_zetaDeltaSet_467_);
lean_ctor_set(v_reuseFailAlloc_491_, 2, v_lctx_468_);
lean_ctor_set(v_reuseFailAlloc_491_, 3, v_localInstances_469_);
lean_ctor_set(v_reuseFailAlloc_491_, 4, v_defEqCtx_x3f_470_);
lean_ctor_set(v_reuseFailAlloc_491_, 5, v_synthPendingDepth_471_);
lean_ctor_set(v_reuseFailAlloc_491_, 6, v_canUnfold_x3f_472_);
lean_ctor_set_uint8(v_reuseFailAlloc_491_, sizeof(void*)*7, v_trackZetaDelta_466_);
lean_ctor_set_uint8(v_reuseFailAlloc_491_, sizeof(void*)*7 + 1, v_univApprox_473_);
lean_ctor_set_uint8(v_reuseFailAlloc_491_, sizeof(void*)*7 + 2, v_inTypeClassResolution_474_);
lean_ctor_set_uint8(v_reuseFailAlloc_491_, sizeof(void*)*7 + 3, v_cacheInferType_475_);
v___x_489_ = v_reuseFailAlloc_491_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
lean_object* v___x_490_; 
v___x_490_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg(v_type_436_, v___f_437_, v___x_438_, v___x_438_, v___x_489_, v___y_440_, v___y_441_, v___y_442_);
lean_dec_ref(v___x_489_);
return v___x_490_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__1___boxed(lean_object* v___x_502_, lean_object* v_type_503_, lean_object* v___f_504_, lean_object* v___x_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
uint8_t v___x_7035__boxed_511_; uint8_t v___x_7037__boxed_512_; lean_object* v_res_513_; 
v___x_7035__boxed_511_ = lean_unbox(v___x_502_);
v___x_7037__boxed_512_ = lean_unbox(v___x_505_);
v_res_513_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__1(v___x_7035__boxed_511_, v_type_503_, v___f_504_, v___x_7037__boxed_512_, v___y_506_, v___y_507_, v___y_508_, v___y_509_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
lean_dec(v___y_507_);
return v_res_513_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__1(void){
_start:
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__0));
v___x_516_ = lean_string_utf8_byte_size(v___x_515_);
return v___x_516_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__5(void){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_520_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__4));
v___x_521_ = lean_string_utf8_byte_size(v___x_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport(lean_object* v_name_522_, lean_object* v_c_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_){
_start:
{
uint8_t v___x_529_; 
lean_inc_ref(v_c_523_);
v___x_529_ = l_Lean_AsyncConstantInfo_isUnsafe(v_c_523_);
if (v___x_529_ == 0)
{
lean_object* v___x_530_; lean_object* v_env_531_; uint8_t v___x_532_; uint8_t v___x_533_; 
v___x_530_ = lean_st_ref_get(v_a_527_);
v_env_531_ = lean_ctor_get(v___x_530_, 0);
lean_inc_ref(v_env_531_);
lean_dec(v___x_530_);
lean_inc(v_name_522_);
v___x_532_ = l_Lean_Meta_allowCompletion(v_env_531_, v_name_522_);
v___x_533_ = lean_bool_not(v___x_532_);
if (v___x_533_ == 0)
{
lean_object* v___x_534_; lean_object* v_env_538_; uint8_t v___x_539_; 
v___x_534_ = lean_st_ref_get(v_a_527_);
v_env_538_ = lean_ctor_get(v___x_534_, 0);
lean_inc_ref(v_env_538_);
lean_dec(v___x_534_);
lean_inc(v_name_522_);
v___x_539_ = l_Lean_Linter_isDeprecated(v_env_538_, v_name_522_);
if (v___x_539_ == 0)
{
lean_object* v___f_540_; lean_object* v___y_542_; lean_object* v___y_543_; lean_object* v___y_544_; lean_object* v___y_545_; 
lean_inc(v_name_522_);
v___f_540_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___boxed), 8, 1);
lean_closure_set(v___f_540_, 0, v_name_522_);
if (lean_obj_tag(v_name_522_) == 1)
{
lean_object* v_str_556_; uint8_t v___y_558_; lean_object* v___x_566_; uint8_t v___x_567_; 
v_str_556_ = lean_ctor_get(v_name_522_, 1);
v___x_566_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__2));
v___x_567_ = lean_string_dec_eq(v_str_556_, v___x_566_);
if (v___x_567_ == 0)
{
lean_object* v___x_568_; uint8_t v___x_569_; 
v___x_568_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__3));
v___x_569_ = lean_string_dec_eq(v_str_556_, v___x_568_);
if (v___x_569_ == 0)
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; uint8_t v___x_573_; 
v___x_570_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__4));
v___x_571_ = lean_string_utf8_byte_size(v_str_556_);
v___x_572_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__5, &l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__5_once, _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__5);
v___x_573_ = lean_nat_dec_le(v___x_572_, v___x_571_);
if (v___x_573_ == 0)
{
v___y_558_ = v___x_539_;
goto v___jp_557_;
}
else
{
lean_object* v___x_574_; lean_object* v___x_575_; uint8_t v___x_576_; 
v___x_574_ = lean_unsigned_to_nat(0u);
v___x_575_ = lean_nat_sub(v___x_571_, v___x_572_);
v___x_576_ = lean_string_memcmp(v_str_556_, v___x_570_, v___x_575_, v___x_574_, v___x_572_);
lean_dec(v___x_575_);
v___y_558_ = v___x_576_;
goto v___jp_557_;
}
}
else
{
lean_dec_ref_known(v_name_522_, 2);
lean_dec_ref(v___f_540_);
lean_dec_ref(v_c_523_);
goto v___jp_535_;
}
}
else
{
lean_dec_ref_known(v_name_522_, 2);
lean_dec_ref(v___f_540_);
lean_dec_ref(v_c_523_);
goto v___jp_535_;
}
v___jp_557_:
{
if (v___y_558_ == 0)
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; uint8_t v___x_562_; 
v___x_559_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__0));
v___x_560_ = lean_string_utf8_byte_size(v_str_556_);
v___x_561_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__1, &l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__1_once, _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__1);
v___x_562_ = lean_nat_dec_le(v___x_561_, v___x_560_);
if (v___x_562_ == 0)
{
v___y_542_ = v_a_524_;
v___y_543_ = v_a_525_;
v___y_544_ = v_a_526_;
v___y_545_ = v_a_527_;
goto v___jp_541_;
}
else
{
lean_object* v___x_563_; lean_object* v___x_564_; uint8_t v___x_565_; 
v___x_563_ = lean_unsigned_to_nat(0u);
v___x_564_ = lean_nat_sub(v___x_560_, v___x_561_);
v___x_565_ = lean_string_memcmp(v_str_556_, v___x_559_, v___x_564_, v___x_563_, v___x_561_);
lean_dec(v___x_564_);
if (v___x_565_ == 0)
{
v___y_542_ = v_a_524_;
v___y_543_ = v_a_525_;
v___y_544_ = v_a_526_;
v___y_545_ = v_a_527_;
goto v___jp_541_;
}
else
{
lean_dec_ref_known(v_name_522_, 2);
lean_dec_ref(v___f_540_);
lean_dec_ref(v_c_523_);
goto v___jp_535_;
}
}
}
else
{
lean_dec_ref_known(v_name_522_, 2);
lean_dec_ref(v___f_540_);
lean_dec_ref(v_c_523_);
goto v___jp_535_;
}
}
}
else
{
v___y_542_ = v_a_524_;
v___y_543_ = v_a_525_;
v___y_544_ = v_a_526_;
v___y_545_ = v_a_527_;
goto v___jp_541_;
}
v___jp_541_:
{
uint8_t v___x_546_; 
v___x_546_ = l_Lean_Name_isMetaprogramming(v_name_522_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; lean_object* v_type_548_; uint8_t v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___f_552_; lean_object* v___x_553_; 
v___x_547_ = l_Lean_AsyncConstantInfo_toConstantVal(v_c_523_);
v_type_548_ = lean_ctor_get(v___x_547_, 2);
lean_inc_ref(v_type_548_);
lean_dec_ref(v___x_547_);
v___x_549_ = 2;
v___x_550_ = lean_box(v___x_549_);
v___x_551_ = lean_box(v___x_546_);
v___f_552_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__1___boxed), 9, 4);
lean_closure_set(v___f_552_, 0, v___x_550_);
lean_closure_set(v___f_552_, 1, v_type_548_);
lean_closure_set(v___f_552_, 2, v___f_540_);
lean_closure_set(v___f_552_, 3, v___x_551_);
v___x_553_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1___redArg(v___f_552_, v___x_546_, v___y_542_, v___y_543_, v___y_544_, v___y_545_);
return v___x_553_;
}
else
{
lean_object* v___x_554_; lean_object* v___x_555_; 
lean_dec_ref(v___f_540_);
lean_dec_ref(v_c_523_);
v___x_554_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0));
v___x_555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
return v___x_555_;
}
}
}
else
{
lean_object* v___x_577_; lean_object* v___x_578_; 
lean_dec_ref(v_c_523_);
lean_dec(v_name_522_);
v___x_577_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0));
v___x_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
return v___x_578_;
}
v___jp_535_:
{
lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_536_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0));
v___x_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
return v___x_537_;
}
}
else
{
lean_object* v___x_579_; lean_object* v___x_580_; 
lean_dec_ref(v_c_523_);
lean_dec(v_name_522_);
v___x_579_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0));
v___x_580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_580_, 0, v___x_579_);
return v___x_580_;
}
}
else
{
lean_object* v___x_581_; lean_object* v___x_582_; 
lean_dec_ref(v_c_523_);
lean_dec(v_name_522_);
v___x_581_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0));
v___x_582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_582_, 0, v___x_581_);
return v___x_582_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___boxed(lean_object* v_name_583_, lean_object* v_c_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport(v_name_583_, v_c_584_, v_a_585_, v_a_586_, v_a_587_, v_a_588_);
lean_dec(v_a_588_);
lean_dec_ref(v_a_587_);
lean_dec(v_a_586_);
lean_dec_ref(v_a_585_);
return v_res_590_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_Rewrites_localHypotheses_spec__0(lean_object* v_a_591_, lean_object* v_x_592_){
_start:
{
if (lean_obj_tag(v_x_592_) == 0)
{
uint8_t v___x_593_; 
v___x_593_ = 0;
return v___x_593_;
}
else
{
lean_object* v_head_594_; lean_object* v_tail_595_; uint8_t v___x_596_; 
v_head_594_ = lean_ctor_get(v_x_592_, 0);
v_tail_595_ = lean_ctor_get(v_x_592_, 1);
v___x_596_ = l_Lean_instBEqFVarId_beq(v_a_591_, v_head_594_);
if (v___x_596_ == 0)
{
v_x_592_ = v_tail_595_;
goto _start;
}
else
{
return v___x_596_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_Rewrites_localHypotheses_spec__0___boxed(lean_object* v_a_598_, lean_object* v_x_599_){
_start:
{
uint8_t v_res_600_; lean_object* v_r_601_; 
v_res_600_ = l_List_elem___at___00Lean_Meta_Rewrites_localHypotheses_spec__0(v_a_598_, v_x_599_);
lean_dec(v_x_599_);
lean_dec(v_a_598_);
v_r_601_ = lean_box(v_res_600_);
return v_r_601_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_localHypotheses_spec__2(lean_object* v_except_602_, lean_object* v_as_603_, size_t v_sz_604_, size_t v_i_605_, lean_object* v_b_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
lean_object* v_a_613_; uint8_t v___x_617_; 
v___x_617_ = lean_usize_dec_lt(v_i_605_, v_sz_604_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; 
v___x_618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_618_, 0, v_b_606_);
return v___x_618_;
}
else
{
lean_object* v_a_619_; lean_object* v___x_620_; uint8_t v___x_621_; 
v_a_619_ = lean_array_uget_borrowed(v_as_603_, v_i_605_);
v___x_620_ = l_Lean_Expr_fvarId_x21(v_a_619_);
v___x_621_ = l_List_elem___at___00Lean_Meta_Rewrites_localHypotheses_spec__0(v___x_620_, v_except_602_);
lean_dec(v___x_620_);
if (v___x_621_ == 0)
{
lean_object* v___x_622_; 
lean_inc(v___y_610_);
lean_inc_ref(v___y_609_);
lean_inc(v___y_608_);
lean_inc_ref(v___y_607_);
lean_inc(v_a_619_);
v___x_622_ = lean_infer_type(v_a_619_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
if (lean_obj_tag(v___x_622_) == 0)
{
lean_object* v_a_623_; lean_object* v___x_624_; uint8_t v___x_625_; lean_object* v___x_626_; 
v_a_623_ = lean_ctor_get(v___x_622_, 0);
lean_inc(v_a_623_);
lean_dec_ref_known(v___x_622_, 1);
v___x_624_ = lean_box(0);
v___x_625_ = 0;
v___x_626_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_623_, v___x_624_, v___x_625_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
if (lean_obj_tag(v___x_626_) == 0)
{
lean_object* v_a_627_; lean_object* v_snd_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_699_; 
v_a_627_ = lean_ctor_get(v___x_626_, 0);
lean_inc(v_a_627_);
lean_dec_ref_known(v___x_626_, 1);
v_snd_628_ = lean_ctor_get(v_a_627_, 1);
v_isSharedCheck_699_ = !lean_is_exclusive(v_a_627_);
if (v_isSharedCheck_699_ == 0)
{
lean_object* v_unused_700_; 
v_unused_700_ = lean_ctor_get(v_a_627_, 0);
lean_dec(v_unused_700_);
v___x_630_ = v_a_627_;
v_isShared_631_ = v_isSharedCheck_699_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_snd_628_);
lean_dec(v_a_627_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_699_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v_snd_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_697_; 
v_snd_632_ = lean_ctor_get(v_snd_628_, 1);
v_isSharedCheck_697_ = !lean_is_exclusive(v_snd_628_);
if (v_isSharedCheck_697_ == 0)
{
lean_object* v_unused_698_; 
v_unused_698_ = lean_ctor_get(v_snd_628_, 0);
lean_dec(v_unused_698_);
v___x_634_ = v_snd_628_;
v_isShared_635_ = v_isSharedCheck_697_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_snd_632_);
lean_dec(v_snd_628_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_697_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_636_; 
v___x_636_ = l_Lean_Meta_whnfR(v_snd_632_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
if (lean_obj_tag(v___x_636_) == 0)
{
lean_object* v_a_637_; lean_object* v___x_638_; lean_object* v_fst_639_; 
v_a_637_ = lean_ctor_get(v___x_636_, 0);
lean_inc(v_a_637_);
lean_dec_ref_known(v___x_636_, 1);
v___x_638_ = l_Lean_Expr_getAppFnArgs(v_a_637_);
v_fst_639_ = lean_ctor_get(v___x_638_, 0);
lean_inc(v_fst_639_);
if (lean_obj_tag(v_fst_639_) == 1)
{
lean_object* v_pre_640_; 
v_pre_640_ = lean_ctor_get(v_fst_639_, 0);
if (lean_obj_tag(v_pre_640_) == 0)
{
lean_object* v_snd_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_687_; 
v_snd_641_ = lean_ctor_get(v___x_638_, 1);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_687_ == 0)
{
lean_object* v_unused_688_; 
v_unused_688_ = lean_ctor_get(v___x_638_, 0);
lean_dec(v_unused_688_);
v___x_643_ = v___x_638_;
v_isShared_644_ = v_isSharedCheck_687_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_snd_641_);
lean_dec(v___x_638_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_687_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v_str_645_; lean_object* v___x_646_; uint8_t v___x_647_; 
v_str_645_ = lean_ctor_get(v_fst_639_, 1);
lean_inc_ref(v_str_645_);
lean_dec_ref_known(v_fst_639_, 2);
v___x_646_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__1));
v___x_647_ = lean_string_dec_eq(v_str_645_, v___x_646_);
if (v___x_647_ == 0)
{
lean_object* v___x_648_; uint8_t v___x_649_; 
v___x_648_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__2));
v___x_649_ = lean_string_dec_eq(v_str_645_, v___x_648_);
lean_dec_ref(v_str_645_);
if (v___x_649_ == 0)
{
lean_del_object(v___x_643_);
lean_dec(v_snd_641_);
lean_del_object(v___x_634_);
lean_del_object(v___x_630_);
v_a_613_ = v_b_606_;
goto v___jp_612_;
}
else
{
lean_object* v___x_650_; lean_object* v___x_651_; uint8_t v___x_652_; 
v___x_650_ = lean_array_get_size(v_snd_641_);
lean_dec(v_snd_641_);
v___x_651_ = lean_unsigned_to_nat(2u);
v___x_652_ = lean_nat_dec_eq(v___x_650_, v___x_651_);
if (v___x_652_ == 0)
{
lean_del_object(v___x_643_);
lean_del_object(v___x_634_);
lean_del_object(v___x_630_);
v_a_613_ = v_b_606_;
goto v___jp_612_;
}
else
{
lean_object* v___x_653_; lean_object* v___x_655_; 
v___x_653_ = lean_box(v___x_621_);
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 1, v___x_651_);
lean_ctor_set(v___x_643_, 0, v___x_653_);
v___x_655_ = v___x_643_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v___x_653_);
lean_ctor_set(v_reuseFailAlloc_667_, 1, v___x_651_);
v___x_655_ = v_reuseFailAlloc_667_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
lean_object* v___x_657_; 
lean_inc(v_a_619_);
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 1, v___x_655_);
lean_ctor_set(v___x_634_, 0, v_a_619_);
v___x_657_ = v___x_634_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_a_619_);
lean_ctor_set(v_reuseFailAlloc_666_, 1, v___x_655_);
v___x_657_ = v_reuseFailAlloc_666_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_662_; 
v___x_658_ = lean_array_push(v_b_606_, v___x_657_);
v___x_659_ = lean_unsigned_to_nat(1u);
v___x_660_ = lean_box(v___x_617_);
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 1, v___x_659_);
lean_ctor_set(v___x_630_, 0, v___x_660_);
v___x_662_ = v___x_630_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v___x_660_);
lean_ctor_set(v_reuseFailAlloc_665_, 1, v___x_659_);
v___x_662_ = v_reuseFailAlloc_665_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
lean_object* v___x_663_; lean_object* v___x_664_; 
lean_inc(v_a_619_);
v___x_663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_663_, 0, v_a_619_);
lean_ctor_set(v___x_663_, 1, v___x_662_);
v___x_664_ = lean_array_push(v___x_658_, v___x_663_);
v_a_613_ = v___x_664_;
goto v___jp_612_;
}
}
}
}
}
}
else
{
lean_object* v___x_668_; lean_object* v___x_669_; uint8_t v___x_670_; 
lean_dec_ref(v_str_645_);
v___x_668_ = lean_array_get_size(v_snd_641_);
lean_dec(v_snd_641_);
v___x_669_ = lean_unsigned_to_nat(3u);
v___x_670_ = lean_nat_dec_eq(v___x_668_, v___x_669_);
if (v___x_670_ == 0)
{
lean_del_object(v___x_643_);
lean_del_object(v___x_634_);
lean_del_object(v___x_630_);
v_a_613_ = v_b_606_;
goto v___jp_612_;
}
else
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_674_; 
v___x_671_ = lean_unsigned_to_nat(2u);
v___x_672_ = lean_box(v___x_621_);
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 1, v___x_671_);
lean_ctor_set(v___x_643_, 0, v___x_672_);
v___x_674_ = v___x_643_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v___x_672_);
lean_ctor_set(v_reuseFailAlloc_686_, 1, v___x_671_);
v___x_674_ = v_reuseFailAlloc_686_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
lean_object* v___x_676_; 
lean_inc(v_a_619_);
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 1, v___x_674_);
lean_ctor_set(v___x_634_, 0, v_a_619_);
v___x_676_ = v___x_634_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_a_619_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v___x_674_);
v___x_676_ = v_reuseFailAlloc_685_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_681_; 
v___x_677_ = lean_array_push(v_b_606_, v___x_676_);
v___x_678_ = lean_unsigned_to_nat(1u);
v___x_679_ = lean_box(v___x_617_);
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 1, v___x_678_);
lean_ctor_set(v___x_630_, 0, v___x_679_);
v___x_681_ = v___x_630_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v___x_679_);
lean_ctor_set(v_reuseFailAlloc_684_, 1, v___x_678_);
v___x_681_ = v_reuseFailAlloc_684_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
lean_object* v___x_682_; lean_object* v___x_683_; 
lean_inc(v_a_619_);
v___x_682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_682_, 0, v_a_619_);
lean_ctor_set(v___x_682_, 1, v___x_681_);
v___x_683_ = lean_array_push(v___x_677_, v___x_682_);
v_a_613_ = v___x_683_;
goto v___jp_612_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_fst_639_, 2);
lean_dec_ref(v___x_638_);
lean_del_object(v___x_634_);
lean_del_object(v___x_630_);
v_a_613_ = v_b_606_;
goto v___jp_612_;
}
}
else
{
lean_dec(v_fst_639_);
lean_dec_ref(v___x_638_);
lean_del_object(v___x_634_);
lean_del_object(v___x_630_);
v_a_613_ = v_b_606_;
goto v___jp_612_;
}
}
else
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_696_; 
lean_del_object(v___x_634_);
lean_del_object(v___x_630_);
lean_dec_ref(v_b_606_);
v_a_689_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_696_ == 0)
{
v___x_691_ = v___x_636_;
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___x_636_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_694_; 
if (v_isShared_692_ == 0)
{
v___x_694_ = v___x_691_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_a_689_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
}
}
}
else
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_708_; 
lean_dec_ref(v_b_606_);
v_a_701_ = lean_ctor_get(v___x_626_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_708_ == 0)
{
v___x_703_ = v___x_626_;
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_626_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_706_; 
if (v_isShared_704_ == 0)
{
v___x_706_ = v___x_703_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_701_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
else
{
lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_716_; 
lean_dec_ref(v_b_606_);
v_a_709_ = lean_ctor_get(v___x_622_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_716_ == 0)
{
v___x_711_ = v___x_622_;
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_622_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_714_; 
if (v_isShared_712_ == 0)
{
v___x_714_ = v___x_711_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_a_709_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
else
{
v_a_613_ = v_b_606_;
goto v___jp_612_;
}
}
v___jp_612_:
{
size_t v___x_614_; size_t v___x_615_; 
v___x_614_ = ((size_t)1ULL);
v___x_615_ = lean_usize_add(v_i_605_, v___x_614_);
v_i_605_ = v___x_615_;
v_b_606_ = v_a_613_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_localHypotheses_spec__2___boxed(lean_object* v_except_717_, lean_object* v_as_718_, lean_object* v_sz_719_, lean_object* v_i_720_, lean_object* v_b_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
size_t v_sz_boxed_727_; size_t v_i_boxed_728_; lean_object* v_res_729_; 
v_sz_boxed_727_ = lean_unbox_usize(v_sz_719_);
lean_dec(v_sz_719_);
v_i_boxed_728_ = lean_unbox_usize(v_i_720_);
lean_dec(v_i_720_);
v_res_729_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_localHypotheses_spec__2(v_except_717_, v_as_718_, v_sz_boxed_727_, v_i_boxed_728_, v_b_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec_ref(v_as_718_);
lean_dec(v_except_717_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(lean_object* v_as_730_, size_t v_sz_731_, size_t v_i_732_, lean_object* v_b_733_){
_start:
{
uint8_t v___x_735_; 
v___x_735_ = lean_usize_dec_lt(v_i_732_, v_sz_731_);
if (v___x_735_ == 0)
{
lean_object* v___x_736_; 
v___x_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_736_, 0, v_b_733_);
return v___x_736_;
}
else
{
lean_object* v_snd_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_756_; 
v_snd_737_ = lean_ctor_get(v_b_733_, 1);
v_isSharedCheck_756_ = !lean_is_exclusive(v_b_733_);
if (v_isSharedCheck_756_ == 0)
{
lean_object* v_unused_757_; 
v_unused_757_ = lean_ctor_get(v_b_733_, 0);
lean_dec(v_unused_757_);
v___x_739_ = v_b_733_;
v_isShared_740_ = v_isSharedCheck_756_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_snd_737_);
lean_dec(v_b_733_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_756_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_741_; lean_object* v_a_743_; lean_object* v_a_750_; 
v___x_741_ = lean_box(0);
v_a_750_ = lean_array_uget_borrowed(v_as_730_, v_i_732_);
if (lean_obj_tag(v_a_750_) == 0)
{
v_a_743_ = v_snd_737_;
goto v___jp_742_;
}
else
{
lean_object* v_val_751_; uint8_t v___x_752_; uint8_t v___x_753_; 
v_val_751_ = lean_ctor_get(v_a_750_, 0);
v___x_752_ = l_Lean_LocalDecl_isImplementationDetail(v_val_751_);
v___x_753_ = lean_bool_not(v___x_752_);
if (v___x_753_ == 0)
{
v_a_743_ = v_snd_737_;
goto v___jp_742_;
}
else
{
lean_object* v___x_754_; lean_object* v___x_755_; 
lean_inc(v_val_751_);
v___x_754_ = l_Lean_LocalDecl_toExpr(v_val_751_);
v___x_755_ = lean_array_push(v_snd_737_, v___x_754_);
v_a_743_ = v___x_755_;
goto v___jp_742_;
}
}
v___jp_742_:
{
lean_object* v___x_745_; 
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 1, v_a_743_);
lean_ctor_set(v___x_739_, 0, v___x_741_);
v___x_745_ = v___x_739_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v___x_741_);
lean_ctor_set(v_reuseFailAlloc_749_, 1, v_a_743_);
v___x_745_ = v_reuseFailAlloc_749_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
size_t v___x_746_; size_t v___x_747_; 
v___x_746_ = ((size_t)1ULL);
v___x_747_ = lean_usize_add(v_i_732_, v___x_746_);
v_i_732_ = v___x_747_;
v_b_733_ = v___x_745_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___redArg___boxed(lean_object* v_as_758_, lean_object* v_sz_759_, lean_object* v_i_760_, lean_object* v_b_761_, lean_object* v___y_762_){
_start:
{
size_t v_sz_boxed_763_; size_t v_i_boxed_764_; lean_object* v_res_765_; 
v_sz_boxed_763_ = lean_unbox_usize(v_sz_759_);
lean_dec(v_sz_759_);
v_i_boxed_764_ = lean_unbox_usize(v_i_760_);
lean_dec(v_i_760_);
v_res_765_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(v_as_758_, v_sz_boxed_763_, v_i_boxed_764_, v_b_761_);
lean_dec_ref(v_as_758_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5(lean_object* v_as_766_, size_t v_sz_767_, size_t v_i_768_, lean_object* v_b_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_){
_start:
{
uint8_t v___x_775_; 
v___x_775_ = lean_usize_dec_lt(v_i_768_, v_sz_767_);
if (v___x_775_ == 0)
{
lean_object* v___x_776_; 
v___x_776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_776_, 0, v_b_769_);
return v___x_776_;
}
else
{
lean_object* v_snd_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_796_; 
v_snd_777_ = lean_ctor_get(v_b_769_, 1);
v_isSharedCheck_796_ = !lean_is_exclusive(v_b_769_);
if (v_isSharedCheck_796_ == 0)
{
lean_object* v_unused_797_; 
v_unused_797_ = lean_ctor_get(v_b_769_, 0);
lean_dec(v_unused_797_);
v___x_779_ = v_b_769_;
v_isShared_780_ = v_isSharedCheck_796_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_snd_777_);
lean_dec(v_b_769_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_796_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_781_; lean_object* v_a_783_; lean_object* v_a_790_; 
v___x_781_ = lean_box(0);
v_a_790_ = lean_array_uget_borrowed(v_as_766_, v_i_768_);
if (lean_obj_tag(v_a_790_) == 0)
{
v_a_783_ = v_snd_777_;
goto v___jp_782_;
}
else
{
lean_object* v_val_791_; uint8_t v___x_792_; uint8_t v___x_793_; 
v_val_791_ = lean_ctor_get(v_a_790_, 0);
v___x_792_ = l_Lean_LocalDecl_isImplementationDetail(v_val_791_);
v___x_793_ = lean_bool_not(v___x_792_);
if (v___x_793_ == 0)
{
v_a_783_ = v_snd_777_;
goto v___jp_782_;
}
else
{
lean_object* v___x_794_; lean_object* v___x_795_; 
lean_inc(v_val_791_);
v___x_794_ = l_Lean_LocalDecl_toExpr(v_val_791_);
v___x_795_ = lean_array_push(v_snd_777_, v___x_794_);
v_a_783_ = v___x_795_;
goto v___jp_782_;
}
}
v___jp_782_:
{
lean_object* v___x_785_; 
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 1, v_a_783_);
lean_ctor_set(v___x_779_, 0, v___x_781_);
v___x_785_ = v___x_779_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_781_);
lean_ctor_set(v_reuseFailAlloc_789_, 1, v_a_783_);
v___x_785_ = v_reuseFailAlloc_789_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
size_t v___x_786_; size_t v___x_787_; lean_object* v___x_788_; 
v___x_786_ = ((size_t)1ULL);
v___x_787_ = lean_usize_add(v_i_768_, v___x_786_);
v___x_788_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(v_as_766_, v_sz_767_, v___x_787_, v___x_785_);
return v___x_788_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5___boxed(lean_object* v_as_798_, lean_object* v_sz_799_, lean_object* v_i_800_, lean_object* v_b_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_){
_start:
{
size_t v_sz_boxed_807_; size_t v_i_boxed_808_; lean_object* v_res_809_; 
v_sz_boxed_807_ = lean_unbox_usize(v_sz_799_);
lean_dec(v_sz_799_);
v_i_boxed_808_ = lean_unbox_usize(v_i_800_);
lean_dec(v_i_800_);
v_res_809_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5(v_as_798_, v_sz_boxed_807_, v_i_boxed_808_, v_b_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec_ref(v_as_798_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2(lean_object* v_init_810_, lean_object* v_n_811_, lean_object* v_b_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
if (lean_obj_tag(v_n_811_) == 0)
{
lean_object* v_cs_818_; lean_object* v___x_819_; lean_object* v___x_820_; size_t v_sz_821_; size_t v___x_822_; lean_object* v___x_823_; 
v_cs_818_ = lean_ctor_get(v_n_811_, 0);
v___x_819_ = lean_box(0);
v___x_820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_820_, 0, v___x_819_);
lean_ctor_set(v___x_820_, 1, v_b_812_);
v_sz_821_ = lean_array_size(v_cs_818_);
v___x_822_ = ((size_t)0ULL);
v___x_823_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__4(v_init_810_, v_cs_818_, v_sz_821_, v___x_822_, v___x_820_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_838_; 
v_a_824_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_838_ == 0)
{
v___x_826_ = v___x_823_;
v_isShared_827_ = v_isSharedCheck_838_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___x_823_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_838_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v_fst_828_; 
v_fst_828_ = lean_ctor_get(v_a_824_, 0);
if (lean_obj_tag(v_fst_828_) == 0)
{
lean_object* v_snd_829_; lean_object* v___x_830_; lean_object* v___x_832_; 
v_snd_829_ = lean_ctor_get(v_a_824_, 1);
lean_inc(v_snd_829_);
lean_dec(v_a_824_);
v___x_830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_830_, 0, v_snd_829_);
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 0, v___x_830_);
v___x_832_ = v___x_826_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v___x_830_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
else
{
lean_object* v_val_834_; lean_object* v___x_836_; 
lean_inc_ref(v_fst_828_);
lean_dec(v_a_824_);
v_val_834_ = lean_ctor_get(v_fst_828_, 0);
lean_inc(v_val_834_);
lean_dec_ref_known(v_fst_828_, 1);
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 0, v_val_834_);
v___x_836_ = v___x_826_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_val_834_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
}
else
{
lean_object* v_a_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_846_; 
v_a_839_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_846_ == 0)
{
v___x_841_ = v___x_823_;
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_a_839_);
lean_dec(v___x_823_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_844_; 
if (v_isShared_842_ == 0)
{
v___x_844_ = v___x_841_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_a_839_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
}
else
{
lean_object* v_vs_847_; lean_object* v___x_848_; lean_object* v___x_849_; size_t v_sz_850_; size_t v___x_851_; lean_object* v___x_852_; 
v_vs_847_ = lean_ctor_get(v_n_811_, 0);
v___x_848_ = lean_box(0);
v___x_849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_849_, 0, v___x_848_);
lean_ctor_set(v___x_849_, 1, v_b_812_);
v_sz_850_ = lean_array_size(v_vs_847_);
v___x_851_ = ((size_t)0ULL);
v___x_852_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5(v_vs_847_, v_sz_850_, v___x_851_, v___x_849_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v_a_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_867_; 
v_a_853_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_867_ == 0)
{
v___x_855_ = v___x_852_;
v_isShared_856_ = v_isSharedCheck_867_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_a_853_);
lean_dec(v___x_852_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_867_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v_fst_857_; 
v_fst_857_ = lean_ctor_get(v_a_853_, 0);
if (lean_obj_tag(v_fst_857_) == 0)
{
lean_object* v_snd_858_; lean_object* v___x_859_; lean_object* v___x_861_; 
v_snd_858_ = lean_ctor_get(v_a_853_, 1);
lean_inc(v_snd_858_);
lean_dec(v_a_853_);
v___x_859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_859_, 0, v_snd_858_);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 0, v___x_859_);
v___x_861_ = v___x_855_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v___x_859_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
else
{
lean_object* v_val_863_; lean_object* v___x_865_; 
lean_inc_ref(v_fst_857_);
lean_dec(v_a_853_);
v_val_863_ = lean_ctor_get(v_fst_857_, 0);
lean_inc(v_val_863_);
lean_dec_ref_known(v_fst_857_, 1);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 0, v_val_863_);
v___x_865_ = v___x_855_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_val_863_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
}
else
{
lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_875_; 
v_a_868_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_875_ == 0)
{
v___x_870_ = v___x_852_;
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_dec(v___x_852_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_873_; 
if (v_isShared_871_ == 0)
{
v___x_873_ = v___x_870_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_a_868_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__4(lean_object* v_init_876_, lean_object* v_as_877_, size_t v_sz_878_, size_t v_i_879_, lean_object* v_b_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
uint8_t v___x_886_; 
v___x_886_ = lean_usize_dec_lt(v_i_879_, v_sz_878_);
if (v___x_886_ == 0)
{
lean_object* v___x_887_; 
v___x_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_887_, 0, v_b_880_);
return v___x_887_;
}
else
{
lean_object* v_snd_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_922_; 
v_snd_888_ = lean_ctor_get(v_b_880_, 1);
v_isSharedCheck_922_ = !lean_is_exclusive(v_b_880_);
if (v_isSharedCheck_922_ == 0)
{
lean_object* v_unused_923_; 
v_unused_923_ = lean_ctor_get(v_b_880_, 0);
lean_dec(v_unused_923_);
v___x_890_ = v_b_880_;
v_isShared_891_ = v_isSharedCheck_922_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_snd_888_);
lean_dec(v_b_880_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_922_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v_a_892_; lean_object* v___x_893_; 
v_a_892_ = lean_array_uget_borrowed(v_as_877_, v_i_879_);
lean_inc(v_snd_888_);
v___x_893_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2(v_init_876_, v_a_892_, v_snd_888_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
if (lean_obj_tag(v___x_893_) == 0)
{
lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_913_; 
v_a_894_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_913_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_913_ == 0)
{
v___x_896_ = v___x_893_;
v_isShared_897_ = v_isSharedCheck_913_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_893_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_913_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
if (lean_obj_tag(v_a_894_) == 0)
{
lean_object* v___x_898_; lean_object* v___x_900_; 
v___x_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_898_, 0, v_a_894_);
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 0, v___x_898_);
v___x_900_ = v___x_890_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v___x_898_);
lean_ctor_set(v_reuseFailAlloc_904_, 1, v_snd_888_);
v___x_900_ = v_reuseFailAlloc_904_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
lean_object* v___x_902_; 
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 0, v___x_900_);
v___x_902_ = v___x_896_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v___x_900_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
else
{
lean_object* v_a_905_; lean_object* v___x_906_; lean_object* v___x_908_; 
lean_del_object(v___x_896_);
lean_dec(v_snd_888_);
v_a_905_ = lean_ctor_get(v_a_894_, 0);
lean_inc(v_a_905_);
lean_dec_ref_known(v_a_894_, 1);
v___x_906_ = lean_box(0);
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 1, v_a_905_);
lean_ctor_set(v___x_890_, 0, v___x_906_);
v___x_908_ = v___x_890_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v___x_906_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v_a_905_);
v___x_908_ = v_reuseFailAlloc_912_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
size_t v___x_909_; size_t v___x_910_; 
v___x_909_ = ((size_t)1ULL);
v___x_910_ = lean_usize_add(v_i_879_, v___x_909_);
v_i_879_ = v___x_910_;
v_b_880_ = v___x_908_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_921_; 
lean_del_object(v___x_890_);
lean_dec(v_snd_888_);
v_a_914_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_921_ == 0)
{
v___x_916_ = v___x_893_;
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v___x_893_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_919_; 
if (v_isShared_917_ == 0)
{
v___x_919_ = v___x_916_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_a_914_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_init_924_, lean_object* v_as_925_, lean_object* v_sz_926_, lean_object* v_i_927_, lean_object* v_b_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_){
_start:
{
size_t v_sz_boxed_934_; size_t v_i_boxed_935_; lean_object* v_res_936_; 
v_sz_boxed_934_ = lean_unbox_usize(v_sz_926_);
lean_dec(v_sz_926_);
v_i_boxed_935_ = lean_unbox_usize(v_i_927_);
lean_dec(v_i_927_);
v_res_936_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__4(v_init_924_, v_as_925_, v_sz_boxed_934_, v_i_boxed_935_, v_b_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
lean_dec_ref(v_as_925_);
lean_dec_ref(v_init_924_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2___boxed(lean_object* v_init_937_, lean_object* v_n_938_, lean_object* v_b_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2(v_init_937_, v_n_938_, v_b_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec_ref(v_n_938_);
lean_dec_ref(v_init_937_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___redArg(lean_object* v_as_946_, size_t v_sz_947_, size_t v_i_948_, lean_object* v_b_949_){
_start:
{
uint8_t v___x_951_; 
v___x_951_ = lean_usize_dec_lt(v_i_948_, v_sz_947_);
if (v___x_951_ == 0)
{
lean_object* v___x_952_; 
v___x_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_952_, 0, v_b_949_);
return v___x_952_;
}
else
{
lean_object* v_snd_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_972_; 
v_snd_953_ = lean_ctor_get(v_b_949_, 1);
v_isSharedCheck_972_ = !lean_is_exclusive(v_b_949_);
if (v_isSharedCheck_972_ == 0)
{
lean_object* v_unused_973_; 
v_unused_973_ = lean_ctor_get(v_b_949_, 0);
lean_dec(v_unused_973_);
v___x_955_ = v_b_949_;
v_isShared_956_ = v_isSharedCheck_972_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_snd_953_);
lean_dec(v_b_949_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_972_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_957_; lean_object* v_a_959_; lean_object* v_a_966_; 
v___x_957_ = lean_box(0);
v_a_966_ = lean_array_uget_borrowed(v_as_946_, v_i_948_);
if (lean_obj_tag(v_a_966_) == 0)
{
v_a_959_ = v_snd_953_;
goto v___jp_958_;
}
else
{
lean_object* v_val_967_; uint8_t v___x_968_; uint8_t v___x_969_; 
v_val_967_ = lean_ctor_get(v_a_966_, 0);
v___x_968_ = l_Lean_LocalDecl_isImplementationDetail(v_val_967_);
v___x_969_ = lean_bool_not(v___x_968_);
if (v___x_969_ == 0)
{
v_a_959_ = v_snd_953_;
goto v___jp_958_;
}
else
{
lean_object* v___x_970_; lean_object* v___x_971_; 
lean_inc(v_val_967_);
v___x_970_ = l_Lean_LocalDecl_toExpr(v_val_967_);
v___x_971_ = lean_array_push(v_snd_953_, v___x_970_);
v_a_959_ = v___x_971_;
goto v___jp_958_;
}
}
v___jp_958_:
{
lean_object* v___x_961_; 
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 1, v_a_959_);
lean_ctor_set(v___x_955_, 0, v___x_957_);
v___x_961_ = v___x_955_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_957_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v_a_959_);
v___x_961_ = v_reuseFailAlloc_965_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
size_t v___x_962_; size_t v___x_963_; 
v___x_962_ = ((size_t)1ULL);
v___x_963_ = lean_usize_add(v_i_948_, v___x_962_);
v_i_948_ = v___x_963_;
v_b_949_ = v___x_961_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_as_974_, lean_object* v_sz_975_, lean_object* v_i_976_, lean_object* v_b_977_, lean_object* v___y_978_){
_start:
{
size_t v_sz_boxed_979_; size_t v_i_boxed_980_; lean_object* v_res_981_; 
v_sz_boxed_979_ = lean_unbox_usize(v_sz_975_);
lean_dec(v_sz_975_);
v_i_boxed_980_ = lean_unbox_usize(v_i_976_);
lean_dec(v_i_976_);
v_res_981_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___redArg(v_as_974_, v_sz_boxed_979_, v_i_boxed_980_, v_b_977_);
lean_dec_ref(v_as_974_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3(lean_object* v_as_982_, size_t v_sz_983_, size_t v_i_984_, lean_object* v_b_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_){
_start:
{
uint8_t v___x_991_; 
v___x_991_ = lean_usize_dec_lt(v_i_984_, v_sz_983_);
if (v___x_991_ == 0)
{
lean_object* v___x_992_; 
v___x_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_992_, 0, v_b_985_);
return v___x_992_;
}
else
{
lean_object* v_snd_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1012_; 
v_snd_993_ = lean_ctor_get(v_b_985_, 1);
v_isSharedCheck_1012_ = !lean_is_exclusive(v_b_985_);
if (v_isSharedCheck_1012_ == 0)
{
lean_object* v_unused_1013_; 
v_unused_1013_ = lean_ctor_get(v_b_985_, 0);
lean_dec(v_unused_1013_);
v___x_995_ = v_b_985_;
v_isShared_996_ = v_isSharedCheck_1012_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_snd_993_);
lean_dec(v_b_985_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1012_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_997_; lean_object* v_a_999_; lean_object* v_a_1006_; 
v___x_997_ = lean_box(0);
v_a_1006_ = lean_array_uget_borrowed(v_as_982_, v_i_984_);
if (lean_obj_tag(v_a_1006_) == 0)
{
v_a_999_ = v_snd_993_;
goto v___jp_998_;
}
else
{
lean_object* v_val_1007_; uint8_t v___x_1008_; uint8_t v___x_1009_; 
v_val_1007_ = lean_ctor_get(v_a_1006_, 0);
v___x_1008_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1007_);
v___x_1009_ = lean_bool_not(v___x_1008_);
if (v___x_1009_ == 0)
{
v_a_999_ = v_snd_993_;
goto v___jp_998_;
}
else
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
lean_inc(v_val_1007_);
v___x_1010_ = l_Lean_LocalDecl_toExpr(v_val_1007_);
v___x_1011_ = lean_array_push(v_snd_993_, v___x_1010_);
v_a_999_ = v___x_1011_;
goto v___jp_998_;
}
}
v___jp_998_:
{
lean_object* v___x_1001_; 
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 1, v_a_999_);
lean_ctor_set(v___x_995_, 0, v___x_997_);
v___x_1001_ = v___x_995_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v___x_997_);
lean_ctor_set(v_reuseFailAlloc_1005_, 1, v_a_999_);
v___x_1001_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
size_t v___x_1002_; size_t v___x_1003_; lean_object* v___x_1004_; 
v___x_1002_ = ((size_t)1ULL);
v___x_1003_ = lean_usize_add(v_i_984_, v___x_1002_);
v___x_1004_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___redArg(v_as_982_, v_sz_983_, v___x_1003_, v___x_1001_);
return v___x_1004_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3___boxed(lean_object* v_as_1014_, lean_object* v_sz_1015_, lean_object* v_i_1016_, lean_object* v_b_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
size_t v_sz_boxed_1023_; size_t v_i_boxed_1024_; lean_object* v_res_1025_; 
v_sz_boxed_1023_ = lean_unbox_usize(v_sz_1015_);
lean_dec(v_sz_1015_);
v_i_boxed_1024_ = lean_unbox_usize(v_i_1016_);
lean_dec(v_i_1016_);
v_res_1025_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3(v_as_1014_, v_sz_boxed_1023_, v_i_boxed_1024_, v_b_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec_ref(v_as_1014_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1(lean_object* v_t_1026_, lean_object* v_init_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_){
_start:
{
lean_object* v_root_1033_; lean_object* v_tail_1034_; lean_object* v___x_1035_; 
v_root_1033_ = lean_ctor_get(v_t_1026_, 0);
v_tail_1034_ = lean_ctor_get(v_t_1026_, 1);
lean_inc_ref(v_init_1027_);
v___x_1035_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2(v_init_1027_, v_root_1033_, v_init_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_);
lean_dec_ref(v_init_1027_);
if (lean_obj_tag(v___x_1035_) == 0)
{
lean_object* v_a_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1072_; 
v_a_1036_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1038_ = v___x_1035_;
v_isShared_1039_ = v_isSharedCheck_1072_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_a_1036_);
lean_dec(v___x_1035_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1072_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
if (lean_obj_tag(v_a_1036_) == 0)
{
lean_object* v_a_1040_; lean_object* v___x_1042_; 
v_a_1040_ = lean_ctor_get(v_a_1036_, 0);
lean_inc(v_a_1040_);
lean_dec_ref_known(v_a_1036_, 1);
if (v_isShared_1039_ == 0)
{
lean_ctor_set(v___x_1038_, 0, v_a_1040_);
v___x_1042_ = v___x_1038_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_a_1040_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
else
{
lean_object* v_a_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; size_t v_sz_1047_; size_t v___x_1048_; lean_object* v___x_1049_; 
lean_del_object(v___x_1038_);
v_a_1044_ = lean_ctor_get(v_a_1036_, 0);
lean_inc(v_a_1044_);
lean_dec_ref_known(v_a_1036_, 1);
v___x_1045_ = lean_box(0);
v___x_1046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1045_);
lean_ctor_set(v___x_1046_, 1, v_a_1044_);
v_sz_1047_ = lean_array_size(v_tail_1034_);
v___x_1048_ = ((size_t)0ULL);
v___x_1049_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3(v_tail_1034_, v_sz_1047_, v___x_1048_, v___x_1046_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_);
if (lean_obj_tag(v___x_1049_) == 0)
{
lean_object* v_a_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1063_; 
v_a_1050_ = lean_ctor_get(v___x_1049_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1052_ = v___x_1049_;
v_isShared_1053_ = v_isSharedCheck_1063_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_a_1050_);
lean_dec(v___x_1049_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1063_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v_fst_1054_; 
v_fst_1054_ = lean_ctor_get(v_a_1050_, 0);
if (lean_obj_tag(v_fst_1054_) == 0)
{
lean_object* v_snd_1055_; lean_object* v___x_1057_; 
v_snd_1055_ = lean_ctor_get(v_a_1050_, 1);
lean_inc(v_snd_1055_);
lean_dec(v_a_1050_);
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 0, v_snd_1055_);
v___x_1057_ = v___x_1052_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_snd_1055_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
else
{
lean_object* v_val_1059_; lean_object* v___x_1061_; 
lean_inc_ref(v_fst_1054_);
lean_dec(v_a_1050_);
v_val_1059_ = lean_ctor_get(v_fst_1054_, 0);
lean_inc(v_val_1059_);
lean_dec_ref_known(v_fst_1054_, 1);
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 0, v_val_1059_);
v___x_1061_ = v___x_1052_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_val_1059_);
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
else
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1071_; 
v_a_1064_ = lean_ctor_get(v___x_1049_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1049_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1066_ = v___x_1049_;
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1049_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1069_; 
if (v_isShared_1067_ == 0)
{
v___x_1069_ = v___x_1066_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_a_1064_);
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
}
else
{
lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1080_; 
v_a_1073_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1075_ = v___x_1035_;
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_1035_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1078_; 
if (v_isShared_1076_ == 0)
{
v___x_1078_ = v___x_1075_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_a_1073_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1___boxed(lean_object* v_t_1081_, lean_object* v_init_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1(v_t_1081_, v_init_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
lean_dec_ref(v_t_1081_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1(lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
lean_object* v_lctx_1096_; lean_object* v_decls_1097_; lean_object* v_hs_1098_; lean_object* v___x_1099_; 
v_lctx_1096_ = lean_ctor_get(v___y_1091_, 2);
v_decls_1097_ = lean_ctor_get(v_lctx_1096_, 1);
v_hs_1098_ = ((lean_object*)(l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1___closed__0));
v___x_1099_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1(v_decls_1097_, v_hs_1098_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1___boxed(lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1(v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1100_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_localHypotheses(lean_object* v_except_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_){
_start:
{
lean_object* v___x_1114_; 
v___x_1114_ = l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1(v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v_a_1115_; lean_object* v___x_1116_; size_t v_sz_1117_; size_t v___x_1118_; lean_object* v___x_1119_; 
v_a_1115_ = lean_ctor_get(v___x_1114_, 0);
lean_inc(v_a_1115_);
lean_dec_ref_known(v___x_1114_, 1);
v___x_1116_ = ((lean_object*)(l_Lean_Meta_Rewrites_localHypotheses___closed__0));
v_sz_1117_ = lean_array_size(v_a_1115_);
v___x_1118_ = ((size_t)0ULL);
v___x_1119_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_localHypotheses_spec__2(v_except_1108_, v_a_1115_, v_sz_1117_, v___x_1118_, v___x_1116_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_);
lean_dec(v_a_1115_);
return v___x_1119_;
}
else
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
v_a_1120_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1122_ = v___x_1114_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1114_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_a_1120_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_localHypotheses___boxed(lean_object* v_except_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_){
_start:
{
lean_object* v_res_1134_; 
v_res_1134_ = l_Lean_Meta_Rewrites_localHypotheses(v_except_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_);
lean_dec(v_a_1132_);
lean_dec_ref(v_a_1131_);
lean_dec(v_a_1130_);
lean_dec_ref(v_a_1129_);
lean_dec(v_except_1128_);
return v_res_1134_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7(lean_object* v_as_1135_, size_t v_sz_1136_, size_t v_i_1137_, lean_object* v_b_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v___x_1144_; 
v___x_1144_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___redArg(v_as_1135_, v_sz_1136_, v_i_1137_, v_b_1138_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___boxed(lean_object* v_as_1145_, lean_object* v_sz_1146_, lean_object* v_i_1147_, lean_object* v_b_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_){
_start:
{
size_t v_sz_boxed_1154_; size_t v_i_boxed_1155_; lean_object* v_res_1156_; 
v_sz_boxed_1154_ = lean_unbox_usize(v_sz_1146_);
lean_dec(v_sz_1146_);
v_i_boxed_1155_ = lean_unbox_usize(v_i_1147_);
lean_dec(v_i_1147_);
v_res_1156_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7(v_as_1145_, v_sz_boxed_1154_, v_i_boxed_1155_, v_b_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_);
lean_dec(v___y_1152_);
lean_dec_ref(v___y_1151_);
lean_dec(v___y_1150_);
lean_dec_ref(v___y_1149_);
lean_dec_ref(v_as_1145_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6(lean_object* v_as_1157_, size_t v_sz_1158_, size_t v_i_1159_, lean_object* v_b_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
lean_object* v___x_1166_; 
v___x_1166_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(v_as_1157_, v_sz_1158_, v_i_1159_, v_b_1160_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___boxed(lean_object* v_as_1167_, lean_object* v_sz_1168_, lean_object* v_i_1169_, lean_object* v_b_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_){
_start:
{
size_t v_sz_boxed_1176_; size_t v_i_boxed_1177_; lean_object* v_res_1178_; 
v_sz_boxed_1176_ = lean_unbox_usize(v_sz_1168_);
lean_dec(v_sz_1168_);
v_i_boxed_1177_ = lean_unbox_usize(v_i_1169_);
lean_dec(v_i_1169_);
v_res_1178_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6(v_as_1167_, v_sz_boxed_1176_, v_i_boxed_1177_, v_b_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
lean_dec(v___y_1174_);
lean_dec_ref(v___y_1173_);
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
lean_dec_ref(v_as_1167_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_createModuleTreeRef(lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_){
_start:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1209_ = ((lean_object*)(l_Lean_Meta_Rewrites_createModuleTreeRef___closed__0));
v___x_1210_ = ((lean_object*)(l_Lean_Meta_Rewrites_droppedKeys));
v___x_1211_ = lean_box(0);
v___x_1212_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v___x_1209_, v___x_1210_, v___x_1211_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_);
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_createModuleTreeRef___boxed(lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l_Lean_Meta_Rewrites_createModuleTreeRef(v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_);
lean_dec(v_a_1216_);
lean_dec_ref(v_a_1215_);
lean_dec(v_a_1214_);
lean_dec_ref(v_a_1213_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_1824551397____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1220_ = lean_box(0);
v___x_1221_ = lean_st_mk_ref(v___x_1220_);
v___x_1222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1221_);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_1824551397____hygCtx___hyg_2____boxed(lean_object* v_a_1223_){
_start:
{
lean_object* v_res_1224_; 
v_res_1224_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_1824551397____hygCtx___hyg_2_();
return v_res_1224_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_constantsPerImportTask(void){
_start:
{
lean_object* v___x_1225_; 
v___x_1225_ = lean_unsigned_to_nat(6500u);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_incPrio(lean_object* v_x_1226_, lean_object* v_x_1227_){
_start:
{
lean_object* v_snd_1228_; uint8_t v___x_1229_; 
v_snd_1228_ = lean_ctor_get(v_x_1227_, 1);
v___x_1229_ = lean_unbox(v_snd_1228_);
if (v___x_1229_ == 0)
{
lean_object* v_fst_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1242_; 
v_fst_1230_ = lean_ctor_get(v_x_1227_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v_x_1227_);
if (v_isSharedCheck_1242_ == 0)
{
lean_object* v_unused_1243_; 
v_unused_1243_ = lean_ctor_get(v_x_1227_, 1);
lean_dec(v_unused_1243_);
v___x_1232_ = v_x_1227_;
v_isShared_1233_ = v_isSharedCheck_1242_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_fst_1230_);
lean_dec(v_x_1227_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1242_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
uint8_t v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1239_; 
v___x_1234_ = 0;
v___x_1235_ = lean_unsigned_to_nat(2u);
v___x_1236_ = lean_nat_mul(v___x_1235_, v_x_1226_);
lean_dec(v_x_1226_);
v___x_1237_ = lean_box(v___x_1234_);
if (v_isShared_1233_ == 0)
{
lean_ctor_set(v___x_1232_, 1, v___x_1236_);
lean_ctor_set(v___x_1232_, 0, v___x_1237_);
v___x_1239_ = v___x_1232_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v___x_1237_);
lean_ctor_set(v_reuseFailAlloc_1241_, 1, v___x_1236_);
v___x_1239_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
lean_object* v___x_1240_; 
v___x_1240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1240_, 0, v_fst_1230_);
lean_ctor_set(v___x_1240_, 1, v___x_1239_);
return v___x_1240_;
}
}
}
else
{
lean_object* v_fst_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1254_; 
v_fst_1244_ = lean_ctor_get(v_x_1227_, 0);
v_isSharedCheck_1254_ = !lean_is_exclusive(v_x_1227_);
if (v_isSharedCheck_1254_ == 0)
{
lean_object* v_unused_1255_; 
v_unused_1255_ = lean_ctor_get(v_x_1227_, 1);
lean_dec(v_unused_1255_);
v___x_1246_ = v_x_1227_;
v_isShared_1247_ = v_isSharedCheck_1254_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_fst_1244_);
lean_dec(v_x_1227_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1254_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
uint8_t v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1251_; 
v___x_1248_ = 1;
v___x_1249_ = lean_box(v___x_1248_);
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 1, v_x_1226_);
lean_ctor_set(v___x_1246_, 0, v___x_1249_);
v___x_1251_ = v___x_1246_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v___x_1249_);
lean_ctor_set(v_reuseFailAlloc_1253_, 1, v_x_1226_);
v___x_1251_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
lean_object* v___x_1252_; 
v___x_1252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1252_, 0, v_fst_1244_);
lean_ctor_set(v___x_1252_, 1, v___x_1251_);
return v___x_1252_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwFindDecls(lean_object* v_moduleRef_1257_, lean_object* v_ty_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_){
_start:
{
lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1264_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_ext;
v___x_1265_ = ((lean_object*)(l_Lean_Meta_Rewrites_createModuleTreeRef___closed__0));
v___x_1266_ = ((lean_object*)(l_Lean_Meta_Rewrites_droppedKeys));
v___x_1267_ = lean_unsigned_to_nat(6500u);
v___x_1268_ = lean_box(0);
v___x_1269_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwFindDecls___closed__0));
v___x_1270_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_moduleRef_1257_, v___x_1264_, v___x_1265_, v___x_1266_, v___x_1267_, v___x_1268_, v___x_1269_, v_ty_1258_, v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwFindDecls___boxed(lean_object* v_moduleRef_1271_, lean_object* v_ty_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_){
_start:
{
lean_object* v_res_1278_; 
v_res_1278_ = l_Lean_Meta_Rewrites_rwFindDecls(v_moduleRef_1271_, v_ty_1272_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_);
lean_dec(v_a_1276_);
lean_dec_ref(v_a_1275_);
lean_dec(v_a_1274_);
lean_dec_ref(v_a_1273_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg(lean_object* v_mctx_1279_, lean_object* v_x_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
lean_object* v___x_1286_; 
v___x_1286_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp(lean_box(0), v_mctx_1279_, v_x_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_);
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1294_; 
v_a_1287_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1289_ = v___x_1286_;
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v___x_1286_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1292_; 
if (v_isShared_1290_ == 0)
{
v___x_1292_ = v___x_1289_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_a_1287_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
else
{
lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1302_; 
v_a_1295_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1297_ = v___x_1286_;
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_a_1295_);
lean_dec(v___x_1286_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1300_; 
if (v_isShared_1298_ == 0)
{
v___x_1300_ = v___x_1297_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_a_1295_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg___boxed(lean_object* v_mctx_1303_, lean_object* v_x_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg(v_mctx_1303_, v_x_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0(lean_object* v_00_u03b1_1311_, lean_object* v_mctx_1312_, lean_object* v_x_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
lean_object* v___x_1319_; 
v___x_1319_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg(v_mctx_1312_, v_x_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___boxed(lean_object* v_00_u03b1_1320_, lean_object* v_mctx_1321_, lean_object* v_x_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_){
_start:
{
lean_object* v_res_1328_; 
v_res_1328_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0(v_00_u03b1_1320_, v_mctx_1321_, v_x_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
lean_dec(v___y_1324_);
lean_dec_ref(v___y_1323_);
return v_res_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(lean_object* v_x_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
lean_object* v___x_1335_; 
v___x_1335_ = l_Lean_Meta_saveState___redArg(v___y_1331_, v___y_1333_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v_a_1336_; lean_object* v_r_1337_; 
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
lean_inc(v_a_1336_);
lean_dec_ref_known(v___x_1335_, 1);
lean_inc(v___y_1333_);
lean_inc_ref(v___y_1332_);
lean_inc(v___y_1331_);
lean_inc_ref(v___y_1330_);
v_r_1337_ = lean_apply_5(v_x_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, lean_box(0));
if (lean_obj_tag(v_r_1337_) == 0)
{
lean_object* v_a_1338_; lean_object* v___x_1339_; 
v_a_1338_ = lean_ctor_get(v_r_1337_, 0);
lean_inc(v_a_1338_);
lean_dec_ref_known(v_r_1337_, 1);
v___x_1339_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1336_, v___y_1331_, v___y_1333_);
lean_dec(v_a_1336_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1346_; 
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1346_ == 0)
{
lean_object* v_unused_1347_; 
v_unused_1347_ = lean_ctor_get(v___x_1339_, 0);
lean_dec(v_unused_1347_);
v___x_1341_ = v___x_1339_;
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
else
{
lean_dec(v___x_1339_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1344_; 
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 0, v_a_1338_);
v___x_1344_ = v___x_1341_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_a_1338_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
else
{
lean_object* v_a_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1355_; 
lean_dec(v_a_1338_);
v_a_1348_ = lean_ctor_get(v___x_1339_, 0);
v_isSharedCheck_1355_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1350_ = v___x_1339_;
v_isShared_1351_ = v_isSharedCheck_1355_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_a_1348_);
lean_dec(v___x_1339_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1355_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___x_1353_; 
if (v_isShared_1351_ == 0)
{
v___x_1353_ = v___x_1350_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v_a_1348_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
}
}
else
{
lean_object* v_a_1356_; lean_object* v___x_1357_; 
v_a_1356_ = lean_ctor_get(v_r_1337_, 0);
lean_inc(v_a_1356_);
lean_dec_ref_known(v_r_1337_, 1);
v___x_1357_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1336_, v___y_1331_, v___y_1333_);
lean_dec(v_a_1336_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1364_; 
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1364_ == 0)
{
lean_object* v_unused_1365_; 
v_unused_1365_ = lean_ctor_get(v___x_1357_, 0);
lean_dec(v_unused_1365_);
v___x_1359_ = v___x_1357_;
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
else
{
lean_dec(v___x_1357_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
if (v_isShared_1360_ == 0)
{
lean_ctor_set_tag(v___x_1359_, 1);
lean_ctor_set(v___x_1359_, 0, v_a_1356_);
v___x_1362_ = v___x_1359_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_a_1356_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
else
{
lean_object* v_a_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1373_; 
lean_dec(v_a_1356_);
v_a_1366_ = lean_ctor_get(v___x_1357_, 0);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1368_ = v___x_1357_;
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_a_1366_);
lean_dec(v___x_1357_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v___x_1371_; 
if (v_isShared_1369_ == 0)
{
v___x_1371_ = v___x_1368_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_a_1366_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
}
}
}
else
{
lean_object* v_a_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1381_; 
lean_dec_ref(v_x_1329_);
v_a_1374_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1376_ = v___x_1335_;
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_a_1374_);
lean_dec(v___x_1335_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1379_; 
if (v_isShared_1377_ == 0)
{
v___x_1379_ = v___x_1376_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_a_1374_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg___boxed(lean_object* v_x_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v_x_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_);
lean_dec(v___y_1386_);
lean_dec_ref(v___y_1385_);
lean_dec(v___y_1384_);
lean_dec_ref(v___y_1383_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1(lean_object* v_00_u03b1_1389_, lean_object* v_x_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
lean_object* v___x_1396_; 
v___x_1396_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v_x_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___boxed(lean_object* v_00_u03b1_1397_, lean_object* v_x_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_){
_start:
{
lean_object* v_res_1404_; 
v_res_1404_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1(v_00_u03b1_1397_, v_x_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_);
lean_dec(v___y_1402_);
lean_dec_ref(v___y_1401_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
return v_res_1404_;
}
}
static uint64_t _init_l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___closed__0(void){
_start:
{
uint8_t v___x_1405_; uint64_t v___x_1406_; 
v___x_1405_ = 2;
v___x_1406_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_1405_);
return v___x_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0(lean_object* v___x_1407_, uint8_t v___x_1408_, lean_object* v___x_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_){
_start:
{
lean_object* v___x_1415_; 
v___x_1415_ = l_Lean_Meta_mkFreshExprMVar(v___x_1407_, v___x_1408_, v___x_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_a_1416_; lean_object* v___x_1417_; uint8_t v_foApprox_1418_; uint8_t v_ctxApprox_1419_; uint8_t v_quasiPatternApprox_1420_; uint8_t v_constApprox_1421_; uint8_t v_isDefEqStuckEx_1422_; uint8_t v_unificationHints_1423_; uint8_t v_proofIrrelevance_1424_; uint8_t v_assignSyntheticOpaque_1425_; uint8_t v_offsetCnstrs_1426_; uint8_t v_etaStruct_1427_; uint8_t v_univApprox_1428_; uint8_t v_iota_1429_; uint8_t v_beta_1430_; uint8_t v_proj_1431_; uint8_t v_zeta_1432_; uint8_t v_zetaDelta_1433_; uint8_t v_zetaUnused_1434_; uint8_t v_zetaHave_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1494_; 
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
lean_inc(v_a_1416_);
lean_dec_ref_known(v___x_1415_, 1);
v___x_1417_ = l_Lean_Meta_Context_config(v___y_1410_);
v_foApprox_1418_ = lean_ctor_get_uint8(v___x_1417_, 0);
v_ctxApprox_1419_ = lean_ctor_get_uint8(v___x_1417_, 1);
v_quasiPatternApprox_1420_ = lean_ctor_get_uint8(v___x_1417_, 2);
v_constApprox_1421_ = lean_ctor_get_uint8(v___x_1417_, 3);
v_isDefEqStuckEx_1422_ = lean_ctor_get_uint8(v___x_1417_, 4);
v_unificationHints_1423_ = lean_ctor_get_uint8(v___x_1417_, 5);
v_proofIrrelevance_1424_ = lean_ctor_get_uint8(v___x_1417_, 6);
v_assignSyntheticOpaque_1425_ = lean_ctor_get_uint8(v___x_1417_, 7);
v_offsetCnstrs_1426_ = lean_ctor_get_uint8(v___x_1417_, 8);
v_etaStruct_1427_ = lean_ctor_get_uint8(v___x_1417_, 10);
v_univApprox_1428_ = lean_ctor_get_uint8(v___x_1417_, 11);
v_iota_1429_ = lean_ctor_get_uint8(v___x_1417_, 12);
v_beta_1430_ = lean_ctor_get_uint8(v___x_1417_, 13);
v_proj_1431_ = lean_ctor_get_uint8(v___x_1417_, 14);
v_zeta_1432_ = lean_ctor_get_uint8(v___x_1417_, 15);
v_zetaDelta_1433_ = lean_ctor_get_uint8(v___x_1417_, 16);
v_zetaUnused_1434_ = lean_ctor_get_uint8(v___x_1417_, 17);
v_zetaHave_1435_ = lean_ctor_get_uint8(v___x_1417_, 18);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1437_ = v___x_1417_;
v_isShared_1438_ = v_isSharedCheck_1494_;
goto v_resetjp_1436_;
}
else
{
lean_dec(v___x_1417_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1494_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
uint8_t v_trackZetaDelta_1439_; lean_object* v_zetaDeltaSet_1440_; lean_object* v_lctx_1441_; lean_object* v_localInstances_1442_; lean_object* v_defEqCtx_x3f_1443_; lean_object* v_synthPendingDepth_1444_; lean_object* v_canUnfold_x3f_1445_; uint8_t v_univApprox_1446_; uint8_t v_inTypeClassResolution_1447_; uint8_t v_cacheInferType_1448_; uint8_t v___x_1449_; lean_object* v_config_1451_; 
v_trackZetaDelta_1439_ = lean_ctor_get_uint8(v___y_1410_, sizeof(void*)*7);
v_zetaDeltaSet_1440_ = lean_ctor_get(v___y_1410_, 1);
lean_inc(v_zetaDeltaSet_1440_);
v_lctx_1441_ = lean_ctor_get(v___y_1410_, 2);
lean_inc_ref(v_lctx_1441_);
v_localInstances_1442_ = lean_ctor_get(v___y_1410_, 3);
lean_inc_ref(v_localInstances_1442_);
v_defEqCtx_x3f_1443_ = lean_ctor_get(v___y_1410_, 4);
lean_inc(v_defEqCtx_x3f_1443_);
v_synthPendingDepth_1444_ = lean_ctor_get(v___y_1410_, 5);
lean_inc(v_synthPendingDepth_1444_);
v_canUnfold_x3f_1445_ = lean_ctor_get(v___y_1410_, 6);
lean_inc(v_canUnfold_x3f_1445_);
v_univApprox_1446_ = lean_ctor_get_uint8(v___y_1410_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1447_ = lean_ctor_get_uint8(v___y_1410_, sizeof(void*)*7 + 2);
v_cacheInferType_1448_ = lean_ctor_get_uint8(v___y_1410_, sizeof(void*)*7 + 3);
v___x_1449_ = 2;
if (v_isShared_1438_ == 0)
{
v_config_1451_ = v___x_1437_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1493_, 0, v_foApprox_1418_);
lean_ctor_set_uint8(v_reuseFailAlloc_1493_, 1, v_ctxApprox_1419_);
lean_ctor_set_uint8(v_reuseFailAlloc_1493_, 2, v_quasiPatternApprox_1420_);
lean_ctor_set_uint8(v_reuseFailAlloc_1493_, 3, v_constApprox_1421_);
lean_ctor_set_uint8(v_reuseFailAlloc_1493_, 4, v_isDefEqStuckEx_1422_);
lean_ctor_set_uint8(v_reuseFailAlloc_1493_, 5, v_unificationHints_1423_);
lean_ctor_set_uint8(v_reuseFailAlloc_1493_, 6, v_proofIrrelevance_1424_);
lean_ctor_set_uint8(v_reuseFailAlloc_1493_, 7, v_assignSyntheticOpaque_1425_);
lean_ctor_set_uint8(v_reuseFailAlloc_1493_, 8, v_offsetCnstrs_1426_);
lean_ctor_set_uint8(v_reuseFailAlloc_1493_, 10, v_etaStruct_1427_);
lean_ctor_set_uint8(v_reuseFailAlloc_1493_, 11, v_univApprox_1428_);
lean_ctor_set_uint8(v_reuseFailAlloc_1493_, 12, v_iota_1429_);
lean_ctor_set_uint8(v_reuseFailAlloc_1493_, 13, v_beta_1430_);
lean_ctor_set_uint8(v_reuseFailAlloc_1493_, 14, v_proj_1431_);
lean_ctor_set_uint8(v_reuseFailAlloc_1493_, 15, v_zeta_1432_);
lean_ctor_set_uint8(v_reuseFailAlloc_1493_, 16, v_zetaDelta_1433_);
lean_ctor_set_uint8(v_reuseFailAlloc_1493_, 17, v_zetaUnused_1434_);
lean_ctor_set_uint8(v_reuseFailAlloc_1493_, 18, v_zetaHave_1435_);
v_config_1451_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
uint64_t v___x_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1485_; 
lean_ctor_set_uint8(v_config_1451_, 9, v___x_1449_);
v___x_1452_ = l_Lean_Meta_Context_configKey(v___y_1410_);
v_isSharedCheck_1485_ = !lean_is_exclusive(v___y_1410_);
if (v_isSharedCheck_1485_ == 0)
{
lean_object* v_unused_1486_; lean_object* v_unused_1487_; lean_object* v_unused_1488_; lean_object* v_unused_1489_; lean_object* v_unused_1490_; lean_object* v_unused_1491_; lean_object* v_unused_1492_; 
v_unused_1486_ = lean_ctor_get(v___y_1410_, 6);
lean_dec(v_unused_1486_);
v_unused_1487_ = lean_ctor_get(v___y_1410_, 5);
lean_dec(v_unused_1487_);
v_unused_1488_ = lean_ctor_get(v___y_1410_, 4);
lean_dec(v_unused_1488_);
v_unused_1489_ = lean_ctor_get(v___y_1410_, 3);
lean_dec(v_unused_1489_);
v_unused_1490_ = lean_ctor_get(v___y_1410_, 2);
lean_dec(v_unused_1490_);
v_unused_1491_ = lean_ctor_get(v___y_1410_, 1);
lean_dec(v_unused_1491_);
v_unused_1492_ = lean_ctor_get(v___y_1410_, 0);
lean_dec(v_unused_1492_);
v___x_1454_ = v___y_1410_;
v_isShared_1455_ = v_isSharedCheck_1485_;
goto v_resetjp_1453_;
}
else
{
lean_dec(v___y_1410_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1485_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
uint64_t v___x_1456_; uint64_t v___x_1457_; lean_object* v___x_1458_; uint8_t v___x_1459_; uint64_t v___x_1460_; uint64_t v___x_1461_; uint64_t v_key_1462_; lean_object* v___x_1463_; lean_object* v___x_1465_; 
v___x_1456_ = 3ULL;
v___x_1457_ = lean_uint64_shift_right(v___x_1452_, v___x_1456_);
v___x_1458_ = l_Lean_Expr_mvarId_x21(v_a_1416_);
lean_dec(v_a_1416_);
v___x_1459_ = 1;
v___x_1460_ = lean_uint64_shift_left(v___x_1457_, v___x_1456_);
v___x_1461_ = lean_uint64_once(&l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___closed__0, &l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___closed__0_once, _init_l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___closed__0);
v_key_1462_ = lean_uint64_lor(v___x_1460_, v___x_1461_);
v___x_1463_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1463_, 0, v_config_1451_);
lean_ctor_set_uint64(v___x_1463_, sizeof(void*)*1, v_key_1462_);
if (v_isShared_1455_ == 0)
{
lean_ctor_set(v___x_1454_, 0, v___x_1463_);
v___x_1465_ = v___x_1454_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v___x_1463_);
lean_ctor_set(v_reuseFailAlloc_1484_, 1, v_zetaDeltaSet_1440_);
lean_ctor_set(v_reuseFailAlloc_1484_, 2, v_lctx_1441_);
lean_ctor_set(v_reuseFailAlloc_1484_, 3, v_localInstances_1442_);
lean_ctor_set(v_reuseFailAlloc_1484_, 4, v_defEqCtx_x3f_1443_);
lean_ctor_set(v_reuseFailAlloc_1484_, 5, v_synthPendingDepth_1444_);
lean_ctor_set(v_reuseFailAlloc_1484_, 6, v_canUnfold_x3f_1445_);
lean_ctor_set_uint8(v_reuseFailAlloc_1484_, sizeof(void*)*7, v_trackZetaDelta_1439_);
lean_ctor_set_uint8(v_reuseFailAlloc_1484_, sizeof(void*)*7 + 1, v_univApprox_1446_);
lean_ctor_set_uint8(v_reuseFailAlloc_1484_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1447_);
lean_ctor_set_uint8(v_reuseFailAlloc_1484_, sizeof(void*)*7 + 3, v_cacheInferType_1448_);
v___x_1465_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
lean_object* v___x_1466_; 
v___x_1466_ = l_Lean_MVarId_refl(v___x_1458_, v___x_1459_, v___x_1465_, v___y_1411_, v___y_1412_, v___y_1413_);
lean_dec_ref(v___x_1465_);
if (lean_obj_tag(v___x_1466_) == 0)
{
lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1474_; 
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1466_);
if (v_isSharedCheck_1474_ == 0)
{
lean_object* v_unused_1475_; 
v_unused_1475_ = lean_ctor_get(v___x_1466_, 0);
lean_dec(v_unused_1475_);
v___x_1468_ = v___x_1466_;
v_isShared_1469_ = v_isSharedCheck_1474_;
goto v_resetjp_1467_;
}
else
{
lean_dec(v___x_1466_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1474_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1470_; lean_object* v___x_1472_; 
v___x_1470_ = lean_box(v___x_1459_);
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 0, v___x_1470_);
v___x_1472_ = v___x_1468_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v___x_1470_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
}
else
{
lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1483_; 
v_a_1476_ = lean_ctor_get(v___x_1466_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1466_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1478_ = v___x_1466_;
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1466_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1481_; 
if (v_isShared_1479_ == 0)
{
v___x_1481_ = v___x_1478_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_a_1476_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
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
lean_object* v_a_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1502_; 
lean_dec_ref(v___y_1410_);
v_a_1495_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1497_ = v___x_1415_;
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_a_1495_);
lean_dec(v___x_1415_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1500_; 
if (v_isShared_1498_ == 0)
{
v___x_1500_ = v___x_1497_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_a_1495_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___boxed(lean_object* v___x_1503_, lean_object* v___x_1504_, lean_object* v___x_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
uint8_t v___x_2362__boxed_1511_; lean_object* v_res_1512_; 
v___x_2362__boxed_1511_ = lean_unbox(v___x_1504_);
v_res_1512_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0(v___x_1503_, v___x_2362__boxed_1511_, v___x_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_);
lean_dec(v___y_1509_);
lean_dec_ref(v___y_1508_);
lean_dec(v___y_1507_);
return v_res_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(lean_object* v_mctx_1513_, lean_object* v_e_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_){
_start:
{
lean_object* v___x_1520_; uint8_t v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___f_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1520_, 0, v_e_1514_);
v___x_1521_ = 0;
v___x_1522_ = lean_box(0);
v___x_1523_ = lean_box(v___x_1521_);
v___f_1524_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1524_, 0, v___x_1520_);
lean_closure_set(v___f_1524_, 1, v___x_1523_);
lean_closure_set(v___f_1524_, 2, v___x_1522_);
v___x_1525_ = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___boxed), 8, 3);
lean_closure_set(v___x_1525_, 0, lean_box(0));
lean_closure_set(v___x_1525_, 1, v_mctx_1513_);
lean_closure_set(v___x_1525_, 2, v___f_1524_);
v___x_1526_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v___x_1525_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_);
if (lean_obj_tag(v___x_1526_) == 0)
{
return v___x_1526_;
}
else
{
lean_object* v_a_1527_; uint8_t v___y_1529_; uint8_t v___x_1539_; 
v_a_1527_ = lean_ctor_get(v___x_1526_, 0);
lean_inc(v_a_1527_);
v___x_1539_ = l_Lean_Exception_isInterrupt(v_a_1527_);
if (v___x_1539_ == 0)
{
uint8_t v___x_1540_; 
v___x_1540_ = l_Lean_Exception_isRuntime(v_a_1527_);
v___y_1529_ = v___x_1540_;
goto v___jp_1528_;
}
else
{
lean_dec(v_a_1527_);
v___y_1529_ = v___x_1539_;
goto v___jp_1528_;
}
v___jp_1528_:
{
if (v___y_1529_ == 0)
{
lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1537_; 
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1537_ == 0)
{
lean_object* v_unused_1538_; 
v_unused_1538_ = lean_ctor_get(v___x_1526_, 0);
lean_dec(v_unused_1538_);
v___x_1531_ = v___x_1526_;
v_isShared_1532_ = v_isSharedCheck_1537_;
goto v_resetjp_1530_;
}
else
{
lean_dec(v___x_1526_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1537_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1533_; lean_object* v___x_1535_; 
v___x_1533_ = lean_box(v___y_1529_);
if (v_isShared_1532_ == 0)
{
lean_ctor_set_tag(v___x_1531_, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1533_);
v___x_1535_ = v___x_1531_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v___x_1533_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
}
else
{
return v___x_1526_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___boxed(lean_object* v_mctx_1541_, lean_object* v_e_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_){
_start:
{
lean_object* v_res_1548_; 
v_res_1548_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(v_mctx_1541_, v_e_1542_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_);
lean_dec(v_a_1546_);
lean_dec_ref(v_a_1545_);
lean_dec(v_a_1544_);
lean_dec_ref(v_a_1543_);
return v_res_1548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult(lean_object* v_r_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_){
_start:
{
lean_object* v_result_1555_; lean_object* v_eNew_1556_; lean_object* v___x_1557_; 
v_result_1555_ = lean_ctor_get(v_r_1549_, 2);
lean_inc_ref(v_result_1555_);
lean_dec_ref(v_r_1549_);
v_eNew_1556_ = lean_ctor_get(v_result_1555_, 0);
lean_inc_ref(v_eNew_1556_);
lean_dec_ref(v_result_1555_);
v___x_1557_ = l_Lean_Meta_ppExpr(v_eNew_1556_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v_a_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1568_; 
v_a_1558_ = lean_ctor_get(v___x_1557_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v___x_1557_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1560_ = v___x_1557_;
v_isShared_1561_ = v_isSharedCheck_1568_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_a_1558_);
lean_dec(v___x_1557_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1568_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1566_; 
v___x_1562_ = l_Std_Format_defWidth;
v___x_1563_ = lean_unsigned_to_nat(0u);
v___x_1564_ = l_Std_Format_pretty(v_a_1558_, v___x_1562_, v___x_1563_, v___x_1563_);
if (v_isShared_1561_ == 0)
{
lean_ctor_set(v___x_1560_, 0, v___x_1564_);
v___x_1566_ = v___x_1560_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v___x_1564_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
}
else
{
lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1576_; 
v_a_1569_ = lean_ctor_get(v___x_1557_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1557_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1571_ = v___x_1557_;
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_dec(v___x_1557_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1574_; 
if (v_isShared_1572_ == 0)
{
v___x_1574_ = v___x_1571_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_a_1569_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult___boxed(lean_object* v_r_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult(v_r_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_);
lean_dec(v_a_1581_);
lean_dec_ref(v_a_1580_);
lean_dec(v_a_1579_);
lean_dec_ref(v_a_1578_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorIdx(uint8_t v_x_1584_){
_start:
{
switch(v_x_1584_)
{
case 0:
{
lean_object* v___x_1585_; 
v___x_1585_ = lean_unsigned_to_nat(0u);
return v___x_1585_;
}
case 1:
{
lean_object* v___x_1586_; 
v___x_1586_ = lean_unsigned_to_nat(1u);
return v___x_1586_;
}
default: 
{
lean_object* v___x_1587_; 
v___x_1587_ = lean_unsigned_to_nat(2u);
return v___x_1587_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorIdx___boxed(lean_object* v_x_1588_){
_start:
{
uint8_t v_x_boxed_1589_; lean_object* v_res_1590_; 
v_x_boxed_1589_ = lean_unbox(v_x_1588_);
v_res_1590_ = l_Lean_Meta_Rewrites_SideConditions_ctorIdx(v_x_boxed_1589_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_toCtorIdx(uint8_t v_x_1591_){
_start:
{
lean_object* v___x_1592_; 
v___x_1592_ = l_Lean_Meta_Rewrites_SideConditions_ctorIdx(v_x_1591_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_toCtorIdx___boxed(lean_object* v_x_1593_){
_start:
{
uint8_t v_x_4__boxed_1594_; lean_object* v_res_1595_; 
v_x_4__boxed_1594_ = lean_unbox(v_x_1593_);
v_res_1595_ = l_Lean_Meta_Rewrites_SideConditions_toCtorIdx(v_x_4__boxed_1594_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorElim___redArg(lean_object* v_k_1596_){
_start:
{
lean_inc(v_k_1596_);
return v_k_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorElim___redArg___boxed(lean_object* v_k_1597_){
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l_Lean_Meta_Rewrites_SideConditions_ctorElim___redArg(v_k_1597_);
lean_dec(v_k_1597_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorElim(lean_object* v_motive_1599_, lean_object* v_ctorIdx_1600_, uint8_t v_t_1601_, lean_object* v_h_1602_, lean_object* v_k_1603_){
_start:
{
lean_inc(v_k_1603_);
return v_k_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorElim___boxed(lean_object* v_motive_1604_, lean_object* v_ctorIdx_1605_, lean_object* v_t_1606_, lean_object* v_h_1607_, lean_object* v_k_1608_){
_start:
{
uint8_t v_t_boxed_1609_; lean_object* v_res_1610_; 
v_t_boxed_1609_ = lean_unbox(v_t_1606_);
v_res_1610_ = l_Lean_Meta_Rewrites_SideConditions_ctorElim(v_motive_1604_, v_ctorIdx_1605_, v_t_boxed_1609_, v_h_1607_, v_k_1608_);
lean_dec(v_k_1608_);
lean_dec(v_ctorIdx_1605_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_none_elim___redArg(lean_object* v_none_1611_){
_start:
{
lean_inc(v_none_1611_);
return v_none_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_none_elim___redArg___boxed(lean_object* v_none_1612_){
_start:
{
lean_object* v_res_1613_; 
v_res_1613_ = l_Lean_Meta_Rewrites_SideConditions_none_elim___redArg(v_none_1612_);
lean_dec(v_none_1612_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_none_elim(lean_object* v_motive_1614_, uint8_t v_t_1615_, lean_object* v_h_1616_, lean_object* v_none_1617_){
_start:
{
lean_inc(v_none_1617_);
return v_none_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_none_elim___boxed(lean_object* v_motive_1618_, lean_object* v_t_1619_, lean_object* v_h_1620_, lean_object* v_none_1621_){
_start:
{
uint8_t v_t_boxed_1622_; lean_object* v_res_1623_; 
v_t_boxed_1622_ = lean_unbox(v_t_1619_);
v_res_1623_ = l_Lean_Meta_Rewrites_SideConditions_none_elim(v_motive_1618_, v_t_boxed_1622_, v_h_1620_, v_none_1621_);
lean_dec(v_none_1621_);
return v_res_1623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_assumption_elim___redArg(lean_object* v_assumption_1624_){
_start:
{
lean_inc(v_assumption_1624_);
return v_assumption_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_assumption_elim___redArg___boxed(lean_object* v_assumption_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l_Lean_Meta_Rewrites_SideConditions_assumption_elim___redArg(v_assumption_1625_);
lean_dec(v_assumption_1625_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_assumption_elim(lean_object* v_motive_1627_, uint8_t v_t_1628_, lean_object* v_h_1629_, lean_object* v_assumption_1630_){
_start:
{
lean_inc(v_assumption_1630_);
return v_assumption_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_assumption_elim___boxed(lean_object* v_motive_1631_, lean_object* v_t_1632_, lean_object* v_h_1633_, lean_object* v_assumption_1634_){
_start:
{
uint8_t v_t_boxed_1635_; lean_object* v_res_1636_; 
v_t_boxed_1635_ = lean_unbox(v_t_1632_);
v_res_1636_ = l_Lean_Meta_Rewrites_SideConditions_assumption_elim(v_motive_1631_, v_t_boxed_1635_, v_h_1633_, v_assumption_1634_);
lean_dec(v_assumption_1634_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim___redArg(lean_object* v_solveByElim_1637_){
_start:
{
lean_inc(v_solveByElim_1637_);
return v_solveByElim_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim___redArg___boxed(lean_object* v_solveByElim_1638_){
_start:
{
lean_object* v_res_1639_; 
v_res_1639_ = l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim___redArg(v_solveByElim_1638_);
lean_dec(v_solveByElim_1638_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim(lean_object* v_motive_1640_, uint8_t v_t_1641_, lean_object* v_h_1642_, lean_object* v_solveByElim_1643_){
_start:
{
lean_inc(v_solveByElim_1643_);
return v_solveByElim_1643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim___boxed(lean_object* v_motive_1644_, lean_object* v_t_1645_, lean_object* v_h_1646_, lean_object* v_solveByElim_1647_){
_start:
{
uint8_t v_t_boxed_1648_; lean_object* v_res_1649_; 
v_t_boxed_1648_ = lean_unbox(v_t_1645_);
v_res_1649_ = l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim(v_motive_1644_, v_t_boxed_1648_, v_h_1646_, v_solveByElim_1647_);
lean_dec(v_solveByElim_1647_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__0(lean_object* v_x_1650_, lean_object* v_x_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_){
_start:
{
lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___x_1657_ = lean_box(0);
v___x_1658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1657_);
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__0___boxed(lean_object* v_x_1659_, lean_object* v_x_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_){
_start:
{
lean_object* v_res_1666_; 
v_res_1666_ = l_Lean_Meta_Rewrites_solveByElim___lam__0(v_x_1659_, v_x_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
lean_dec(v___y_1662_);
lean_dec_ref(v___y_1661_);
lean_dec(v_x_1660_);
lean_dec(v_x_1659_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__1(lean_object* v_x_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_){
_start:
{
uint8_t v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1673_ = 0;
v___x_1674_ = lean_box(v___x_1673_);
v___x_1675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1674_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__1___boxed(lean_object* v_x_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l_Lean_Meta_Rewrites_solveByElim___lam__1(v_x_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
lean_dec(v_x_1676_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0(lean_object* v_msgData_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_){
_start:
{
lean_object* v___x_1689_; lean_object* v_env_1690_; lean_object* v___x_1691_; lean_object* v_mctx_1692_; lean_object* v_lctx_1693_; lean_object* v_options_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1689_ = lean_st_ref_get(v___y_1687_);
v_env_1690_ = lean_ctor_get(v___x_1689_, 0);
lean_inc_ref(v_env_1690_);
lean_dec(v___x_1689_);
v___x_1691_ = lean_st_ref_get(v___y_1685_);
v_mctx_1692_ = lean_ctor_get(v___x_1691_, 0);
lean_inc_ref(v_mctx_1692_);
lean_dec(v___x_1691_);
v_lctx_1693_ = lean_ctor_get(v___y_1684_, 2);
v_options_1694_ = lean_ctor_get(v___y_1686_, 2);
lean_inc_ref(v_options_1694_);
lean_inc_ref(v_lctx_1693_);
v___x_1695_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1695_, 0, v_env_1690_);
lean_ctor_set(v___x_1695_, 1, v_mctx_1692_);
lean_ctor_set(v___x_1695_, 2, v_lctx_1693_);
lean_ctor_set(v___x_1695_, 3, v_options_1694_);
v___x_1696_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1696_, 0, v___x_1695_);
lean_ctor_set(v___x_1696_, 1, v_msgData_1683_);
v___x_1697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1696_);
return v___x_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0___boxed(lean_object* v_msgData_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_){
_start:
{
lean_object* v_res_1704_; 
v_res_1704_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0(v_msgData_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec(v___y_1700_);
lean_dec_ref(v___y_1699_);
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(lean_object* v_msg_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_){
_start:
{
lean_object* v_ref_1711_; lean_object* v___x_1712_; lean_object* v_a_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1721_; 
v_ref_1711_ = lean_ctor_get(v___y_1708_, 5);
v___x_1712_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0(v_msg_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_);
v_a_1713_ = lean_ctor_get(v___x_1712_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1712_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1715_ = v___x_1712_;
v_isShared_1716_ = v_isSharedCheck_1721_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_a_1713_);
lean_dec(v___x_1712_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1721_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1717_; lean_object* v___x_1719_; 
lean_inc(v_ref_1711_);
v___x_1717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1717_, 0, v_ref_1711_);
lean_ctor_set(v___x_1717_, 1, v_a_1713_);
if (v_isShared_1716_ == 0)
{
lean_ctor_set_tag(v___x_1715_, 1);
lean_ctor_set(v___x_1715_, 0, v___x_1717_);
v___x_1719_ = v___x_1715_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v___x_1717_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg___boxed(lean_object* v_msg_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_){
_start:
{
lean_object* v_res_1728_; 
v_res_1728_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(v_msg_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_);
lean_dec(v___y_1726_);
lean_dec_ref(v___y_1725_);
lean_dec(v___y_1724_);
lean_dec_ref(v___y_1723_);
return v_res_1728_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; 
v___x_1730_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__0));
v___x_1731_ = l_Lean_stringToMessageData(v___x_1730_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__2(lean_object* v_x_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1738_ = lean_obj_once(&l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1, &l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1_once, _init_l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1);
v___x_1739_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(v___x_1738_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__2___boxed(lean_object* v_x_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
lean_object* v_res_1746_; 
v_res_1746_ = l_Lean_Meta_Rewrites_solveByElim___lam__2(v_x_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
lean_dec(v_x_1740_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim(lean_object* v_goals_1756_, lean_object* v_depth_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_){
_start:
{
lean_object* v___f_1763_; lean_object* v___f_1764_; lean_object* v___f_1765_; uint8_t v___x_1766_; lean_object* v___x_1767_; uint8_t v___x_1768_; lean_object* v___x_1769_; uint8_t v___x_1770_; lean_object* v___x_1771_; lean_object* v_cfg_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___f_1763_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___closed__0));
v___f_1764_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___closed__1));
v___f_1765_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___closed__2));
v___x_1766_ = 0;
v___x_1767_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1767_, 0, v_depth_1757_);
lean_ctor_set(v___x_1767_, 1, v___f_1763_);
lean_ctor_set(v___x_1767_, 2, v___f_1764_);
lean_ctor_set(v___x_1767_, 3, v___f_1765_);
lean_ctor_set_uint8(v___x_1767_, sizeof(void*)*4, v___x_1766_);
v___x_1768_ = 1;
v___x_1769_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___closed__3));
v___x_1770_ = 1;
v___x_1771_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_1771_, 0, v___x_1767_);
lean_ctor_set(v___x_1771_, 1, v___x_1769_);
lean_ctor_set_uint8(v___x_1771_, sizeof(void*)*2, v___x_1770_);
lean_ctor_set_uint8(v___x_1771_, sizeof(void*)*2 + 1, v___x_1768_);
lean_ctor_set_uint8(v___x_1771_, sizeof(void*)*2 + 2, v___x_1766_);
v_cfg_1772_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_cfg_1772_, 0, v___x_1771_);
lean_ctor_set_uint8(v_cfg_1772_, sizeof(void*)*1, v___x_1768_);
lean_ctor_set_uint8(v_cfg_1772_, sizeof(void*)*1 + 1, v___x_1768_);
lean_ctor_set_uint8(v_cfg_1772_, sizeof(void*)*1 + 2, v___x_1768_);
lean_ctor_set_uint8(v_cfg_1772_, sizeof(void*)*1 + 3, v___x_1766_);
v___x_1773_ = lean_box(0);
v___x_1774_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___closed__4));
v___x_1775_ = l_Lean_Meta_SolveByElim_mkAssumptionSet(v___x_1766_, v___x_1766_, v___x_1773_, v___x_1773_, v___x_1774_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_);
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_object* v_a_1776_; lean_object* v_fst_1777_; lean_object* v_snd_1778_; lean_object* v___x_1779_; 
v_a_1776_ = lean_ctor_get(v___x_1775_, 0);
lean_inc(v_a_1776_);
lean_dec_ref_known(v___x_1775_, 1);
v_fst_1777_ = lean_ctor_get(v_a_1776_, 0);
lean_inc(v_fst_1777_);
v_snd_1778_ = lean_ctor_get(v_a_1776_, 1);
lean_inc(v_snd_1778_);
lean_dec(v_a_1776_);
v___x_1779_ = l_Lean_Meta_SolveByElim_solveByElim(v_cfg_1772_, v_fst_1777_, v_snd_1778_, v_goals_1756_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_);
if (lean_obj_tag(v___x_1779_) == 0)
{
lean_object* v_a_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1790_; 
v_a_1780_ = lean_ctor_get(v___x_1779_, 0);
v_isSharedCheck_1790_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1782_ = v___x_1779_;
v_isShared_1783_ = v_isSharedCheck_1790_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_a_1780_);
lean_dec(v___x_1779_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1790_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
if (lean_obj_tag(v_a_1780_) == 0)
{
lean_object* v___x_1784_; lean_object* v___x_1786_; 
v___x_1784_ = lean_box(0);
if (v_isShared_1783_ == 0)
{
lean_ctor_set(v___x_1782_, 0, v___x_1784_);
v___x_1786_ = v___x_1782_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v___x_1784_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
else
{
lean_object* v___x_1788_; lean_object* v___x_1789_; 
lean_del_object(v___x_1782_);
lean_dec(v_a_1780_);
v___x_1788_ = lean_obj_once(&l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1, &l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1_once, _init_l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1);
v___x_1789_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(v___x_1788_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_);
return v___x_1789_;
}
}
}
else
{
lean_object* v_a_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1798_; 
v_a_1791_ = lean_ctor_get(v___x_1779_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1793_ = v___x_1779_;
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_a_1791_);
lean_dec(v___x_1779_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1796_; 
if (v_isShared_1794_ == 0)
{
v___x_1796_ = v___x_1793_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_a_1791_);
v___x_1796_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
return v___x_1796_;
}
}
}
}
else
{
lean_object* v_a_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1806_; 
lean_dec_ref_known(v_cfg_1772_, 1);
lean_dec(v_goals_1756_);
v_a_1799_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1801_ = v___x_1775_;
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_a_1799_);
lean_dec(v___x_1775_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1804_; 
if (v_isShared_1802_ == 0)
{
v___x_1804_ = v___x_1801_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_a_1799_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___boxed(lean_object* v_goals_1807_, lean_object* v_depth_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_){
_start:
{
lean_object* v_res_1814_; 
v_res_1814_ = l_Lean_Meta_Rewrites_solveByElim(v_goals_1807_, v_depth_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_);
lean_dec(v_a_1812_);
lean_dec_ref(v_a_1811_);
lean_dec(v_a_1810_);
lean_dec_ref(v_a_1809_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0(lean_object* v_00_u03b1_1815_, lean_object* v_msg_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_){
_start:
{
lean_object* v___x_1822_; 
v___x_1822_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(v_msg_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
return v___x_1822_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___boxed(lean_object* v_00_u03b1_1823_, lean_object* v_msg_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_){
_start:
{
lean_object* v_res_1830_; 
v_res_1830_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0(v_00_u03b1_1823_, v_msg_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
lean_dec(v___y_1828_);
lean_dec_ref(v___y_1827_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
return v_res_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg(lean_object* v_e_1831_, lean_object* v___y_1832_){
_start:
{
uint8_t v___x_1834_; uint8_t v___x_1835_; 
v___x_1834_ = l_Lean_Expr_hasMVar(v_e_1831_);
v___x_1835_ = lean_bool_not(v___x_1834_);
if (v___x_1835_ == 0)
{
lean_object* v___x_1836_; lean_object* v_mctx_1837_; lean_object* v___x_1838_; lean_object* v_fst_1839_; lean_object* v_snd_1840_; lean_object* v___x_1841_; lean_object* v_cache_1842_; lean_object* v_zetaDeltaFVarIds_1843_; lean_object* v_postponed_1844_; lean_object* v_diag_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1854_; 
v___x_1836_ = lean_st_ref_get(v___y_1832_);
v_mctx_1837_ = lean_ctor_get(v___x_1836_, 0);
lean_inc_ref(v_mctx_1837_);
lean_dec(v___x_1836_);
v___x_1838_ = l_Lean_instantiateMVarsCore(v_mctx_1837_, v_e_1831_);
v_fst_1839_ = lean_ctor_get(v___x_1838_, 0);
lean_inc(v_fst_1839_);
v_snd_1840_ = lean_ctor_get(v___x_1838_, 1);
lean_inc(v_snd_1840_);
lean_dec_ref(v___x_1838_);
v___x_1841_ = lean_st_ref_take(v___y_1832_);
v_cache_1842_ = lean_ctor_get(v___x_1841_, 1);
v_zetaDeltaFVarIds_1843_ = lean_ctor_get(v___x_1841_, 2);
v_postponed_1844_ = lean_ctor_get(v___x_1841_, 3);
v_diag_1845_ = lean_ctor_get(v___x_1841_, 4);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1854_ == 0)
{
lean_object* v_unused_1855_; 
v_unused_1855_ = lean_ctor_get(v___x_1841_, 0);
lean_dec(v_unused_1855_);
v___x_1847_ = v___x_1841_;
v_isShared_1848_ = v_isSharedCheck_1854_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_diag_1845_);
lean_inc(v_postponed_1844_);
lean_inc(v_zetaDeltaFVarIds_1843_);
lean_inc(v_cache_1842_);
lean_dec(v___x_1841_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1854_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v___x_1850_; 
if (v_isShared_1848_ == 0)
{
lean_ctor_set(v___x_1847_, 0, v_snd_1840_);
v___x_1850_ = v___x_1847_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_snd_1840_);
lean_ctor_set(v_reuseFailAlloc_1853_, 1, v_cache_1842_);
lean_ctor_set(v_reuseFailAlloc_1853_, 2, v_zetaDeltaFVarIds_1843_);
lean_ctor_set(v_reuseFailAlloc_1853_, 3, v_postponed_1844_);
lean_ctor_set(v_reuseFailAlloc_1853_, 4, v_diag_1845_);
v___x_1850_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1851_ = lean_st_ref_set(v___y_1832_, v___x_1850_);
v___x_1852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1852_, 0, v_fst_1839_);
return v___x_1852_;
}
}
}
else
{
lean_object* v___x_1856_; 
v___x_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1856_, 0, v_e_1831_);
return v___x_1856_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg___boxed(lean_object* v_e_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_){
_start:
{
lean_object* v_res_1860_; 
v_res_1860_ = l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg(v_e_1857_, v___y_1858_);
lean_dec(v___y_1858_);
return v_res_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0(lean_object* v_e_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_){
_start:
{
lean_object* v___x_1867_; 
v___x_1867_ = l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg(v_e_1861_, v___y_1863_);
return v___x_1867_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___boxed(lean_object* v_e_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_){
_start:
{
lean_object* v_res_1874_; 
v_res_1874_ = l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0(v_e_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
return v_res_1874_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1875_; double v___x_1876_; 
v___x_1875_ = lean_unsigned_to_nat(0u);
v___x_1876_ = lean_float_of_nat(v___x_1875_);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2(lean_object* v_cls_1880_, lean_object* v_msg_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_){
_start:
{
lean_object* v_ref_1887_; lean_object* v___x_1888_; lean_object* v_a_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1933_; 
v_ref_1887_ = lean_ctor_get(v___y_1884_, 5);
v___x_1888_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0(v_msg_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_);
v_a_1889_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1891_ = v___x_1888_;
v_isShared_1892_ = v_isSharedCheck_1933_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_a_1889_);
lean_dec(v___x_1888_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1933_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1893_; lean_object* v_traceState_1894_; lean_object* v_env_1895_; lean_object* v_nextMacroScope_1896_; lean_object* v_ngen_1897_; lean_object* v_auxDeclNGen_1898_; lean_object* v_cache_1899_; lean_object* v_messages_1900_; lean_object* v_infoState_1901_; lean_object* v_snapshotTasks_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1932_; 
v___x_1893_ = lean_st_ref_take(v___y_1885_);
v_traceState_1894_ = lean_ctor_get(v___x_1893_, 4);
v_env_1895_ = lean_ctor_get(v___x_1893_, 0);
v_nextMacroScope_1896_ = lean_ctor_get(v___x_1893_, 1);
v_ngen_1897_ = lean_ctor_get(v___x_1893_, 2);
v_auxDeclNGen_1898_ = lean_ctor_get(v___x_1893_, 3);
v_cache_1899_ = lean_ctor_get(v___x_1893_, 5);
v_messages_1900_ = lean_ctor_get(v___x_1893_, 6);
v_infoState_1901_ = lean_ctor_get(v___x_1893_, 7);
v_snapshotTasks_1902_ = lean_ctor_get(v___x_1893_, 8);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1893_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1904_ = v___x_1893_;
v_isShared_1905_ = v_isSharedCheck_1932_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_snapshotTasks_1902_);
lean_inc(v_infoState_1901_);
lean_inc(v_messages_1900_);
lean_inc(v_cache_1899_);
lean_inc(v_traceState_1894_);
lean_inc(v_auxDeclNGen_1898_);
lean_inc(v_ngen_1897_);
lean_inc(v_nextMacroScope_1896_);
lean_inc(v_env_1895_);
lean_dec(v___x_1893_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1932_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
uint64_t v_tid_1906_; lean_object* v_traces_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1931_; 
v_tid_1906_ = lean_ctor_get_uint64(v_traceState_1894_, sizeof(void*)*1);
v_traces_1907_ = lean_ctor_get(v_traceState_1894_, 0);
v_isSharedCheck_1931_ = !lean_is_exclusive(v_traceState_1894_);
if (v_isSharedCheck_1931_ == 0)
{
v___x_1909_ = v_traceState_1894_;
v_isShared_1910_ = v_isSharedCheck_1931_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_traces_1907_);
lean_dec(v_traceState_1894_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1931_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1911_; double v___x_1912_; uint8_t v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1921_; 
v___x_1911_ = lean_box(0);
v___x_1912_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__0);
v___x_1913_ = 0;
v___x_1914_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__1));
v___x_1915_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1915_, 0, v_cls_1880_);
lean_ctor_set(v___x_1915_, 1, v___x_1911_);
lean_ctor_set(v___x_1915_, 2, v___x_1914_);
lean_ctor_set_float(v___x_1915_, sizeof(void*)*3, v___x_1912_);
lean_ctor_set_float(v___x_1915_, sizeof(void*)*3 + 8, v___x_1912_);
lean_ctor_set_uint8(v___x_1915_, sizeof(void*)*3 + 16, v___x_1913_);
v___x_1916_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__2));
v___x_1917_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1915_);
lean_ctor_set(v___x_1917_, 1, v_a_1889_);
lean_ctor_set(v___x_1917_, 2, v___x_1916_);
lean_inc(v_ref_1887_);
v___x_1918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1918_, 0, v_ref_1887_);
lean_ctor_set(v___x_1918_, 1, v___x_1917_);
v___x_1919_ = l_Lean_PersistentArray_push___redArg(v_traces_1907_, v___x_1918_);
if (v_isShared_1910_ == 0)
{
lean_ctor_set(v___x_1909_, 0, v___x_1919_);
v___x_1921_ = v___x_1909_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v___x_1919_);
lean_ctor_set_uint64(v_reuseFailAlloc_1930_, sizeof(void*)*1, v_tid_1906_);
v___x_1921_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
lean_object* v___x_1923_; 
if (v_isShared_1905_ == 0)
{
lean_ctor_set(v___x_1904_, 4, v___x_1921_);
v___x_1923_ = v___x_1904_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v_env_1895_);
lean_ctor_set(v_reuseFailAlloc_1929_, 1, v_nextMacroScope_1896_);
lean_ctor_set(v_reuseFailAlloc_1929_, 2, v_ngen_1897_);
lean_ctor_set(v_reuseFailAlloc_1929_, 3, v_auxDeclNGen_1898_);
lean_ctor_set(v_reuseFailAlloc_1929_, 4, v___x_1921_);
lean_ctor_set(v_reuseFailAlloc_1929_, 5, v_cache_1899_);
lean_ctor_set(v_reuseFailAlloc_1929_, 6, v_messages_1900_);
lean_ctor_set(v_reuseFailAlloc_1929_, 7, v_infoState_1901_);
lean_ctor_set(v_reuseFailAlloc_1929_, 8, v_snapshotTasks_1902_);
v___x_1923_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1927_; 
v___x_1924_ = lean_st_ref_set(v___y_1885_, v___x_1923_);
v___x_1925_ = lean_box(0);
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 0, v___x_1925_);
v___x_1927_ = v___x_1891_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1925_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___boxed(lean_object* v_cls_1934_, lean_object* v_msg_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_){
_start:
{
lean_object* v_res_1941_; 
v_res_1941_ = l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2(v_cls_1934_, v_msg_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_);
lean_dec(v___y_1939_);
lean_dec_ref(v___y_1938_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
return v_res_1941_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Rewrites_rwLemma_spec__1(lean_object* v_x_1942_, lean_object* v_x_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_){
_start:
{
if (lean_obj_tag(v_x_1942_) == 0)
{
lean_object* v___x_1949_; lean_object* v___x_1950_; 
v___x_1949_ = l_List_reverse___redArg(v_x_1943_);
v___x_1950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1950_, 0, v___x_1949_);
return v___x_1950_;
}
else
{
lean_object* v_head_1951_; lean_object* v_tail_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1970_; 
v_head_1951_ = lean_ctor_get(v_x_1942_, 0);
v_tail_1952_ = lean_ctor_get(v_x_1942_, 1);
v_isSharedCheck_1970_ = !lean_is_exclusive(v_x_1942_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1954_ = v_x_1942_;
v_isShared_1955_ = v_isSharedCheck_1970_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_tail_1952_);
lean_inc(v_head_1951_);
lean_dec(v_x_1942_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1970_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1956_; 
v___x_1956_ = l_Lean_MVarId_assumption(v_head_1951_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_);
if (lean_obj_tag(v___x_1956_) == 0)
{
lean_object* v_a_1957_; lean_object* v___x_1959_; 
v_a_1957_ = lean_ctor_get(v___x_1956_, 0);
lean_inc(v_a_1957_);
lean_dec_ref_known(v___x_1956_, 1);
if (v_isShared_1955_ == 0)
{
lean_ctor_set(v___x_1954_, 1, v_x_1943_);
lean_ctor_set(v___x_1954_, 0, v_a_1957_);
v___x_1959_ = v___x_1954_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_a_1957_);
lean_ctor_set(v_reuseFailAlloc_1961_, 1, v_x_1943_);
v___x_1959_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
v_x_1942_ = v_tail_1952_;
v_x_1943_ = v___x_1959_;
goto _start;
}
}
else
{
lean_object* v_a_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1969_; 
lean_del_object(v___x_1954_);
lean_dec(v_tail_1952_);
lean_dec(v_x_1943_);
v_a_1962_ = lean_ctor_get(v___x_1956_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1964_ = v___x_1956_;
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_a_1962_);
lean_dec(v___x_1956_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1967_; 
if (v_isShared_1965_ == 0)
{
v___x_1967_ = v___x_1964_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_a_1962_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Rewrites_rwLemma_spec__1___boxed(lean_object* v_x_1971_, lean_object* v_x_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_){
_start:
{
lean_object* v_res_1978_; 
v_res_1978_ = l_List_mapM_loop___at___00Lean_Meta_Rewrites_rwLemma_spec__1(v_x_1971_, v_x_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_);
lean_dec(v___y_1976_);
lean_dec_ref(v___y_1975_);
lean_dec(v___y_1974_);
lean_dec_ref(v___y_1973_);
return v_res_1978_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5(void){
_start:
{
lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1991_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_));
v___x_1992_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__4));
v___x_1993_ = l_Lean_Name_append(v___x_1992_, v___x_1991_);
return v___x_1993_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__7(void){
_start:
{
lean_object* v___x_1995_; lean_object* v___x_1996_; 
v___x_1995_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__6));
v___x_1996_ = l_Lean_stringToMessageData(v___x_1995_);
return v___x_1996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0(lean_object* v_weight_1998_, lean_object* v_goal_1999_, lean_object* v_target_2000_, uint8_t v_symm_2001_, uint8_t v_side_2002_, lean_object* v_lem_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_){
_start:
{
lean_object* v___y_2010_; lean_object* v___y_2011_; lean_object* v___y_2012_; lean_object* v___y_2013_; uint8_t v___y_2014_; lean_object* v___y_2035_; lean_object* v___y_2036_; lean_object* v___y_2037_; lean_object* v___y_2038_; lean_object* v___y_2039_; lean_object* v___y_2040_; lean_object* v_fst_2041_; uint8_t v_snd_2042_; lean_object* v___y_2066_; lean_object* v___y_2067_; uint8_t v___y_2068_; uint8_t v___y_2069_; lean_object* v___y_2070_; lean_object* v___y_2071_; lean_object* v___y_2072_; lean_object* v___y_2073_; lean_object* v___y_2093_; lean_object* v___y_2094_; lean_object* v___y_2095_; lean_object* v___y_2096_; uint8_t v___y_2097_; lean_object* v___y_2109_; lean_object* v___y_2110_; lean_object* v___y_2111_; lean_object* v___y_2112_; uint8_t v___y_2113_; lean_object* v___y_2125_; lean_object* v___y_2205_; lean_object* v___y_2206_; lean_object* v___y_2207_; lean_object* v___y_2208_; lean_object* v_val_2223_; 
if (lean_obj_tag(v_lem_2003_) == 0)
{
lean_object* v_val_2233_; 
v_val_2233_ = lean_ctor_get(v_lem_2003_, 0);
lean_inc(v_val_2233_);
lean_dec_ref_known(v_lem_2003_, 1);
v_val_2223_ = v_val_2233_;
goto v___jp_2222_;
}
else
{
lean_object* v_val_2234_; lean_object* v___x_2235_; 
v_val_2234_ = lean_ctor_get(v_lem_2003_, 0);
lean_inc(v_val_2234_);
lean_dec_ref_known(v_lem_2003_, 1);
v___x_2235_ = l_Lean_Meta_saveState___redArg(v___y_2005_, v___y_2007_);
if (lean_obj_tag(v___x_2235_) == 0)
{
lean_object* v_a_2236_; lean_object* v___x_2237_; 
v_a_2236_ = lean_ctor_get(v___x_2235_, 0);
lean_inc(v_a_2236_);
lean_dec_ref_known(v___x_2235_, 1);
v___x_2237_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_val_2234_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_);
if (lean_obj_tag(v___x_2237_) == 0)
{
lean_object* v_a_2238_; 
lean_dec(v_a_2236_);
v_a_2238_ = lean_ctor_get(v___x_2237_, 0);
lean_inc(v_a_2238_);
lean_dec_ref_known(v___x_2237_, 1);
v_val_2223_ = v_a_2238_;
goto v___jp_2222_;
}
else
{
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2268_; 
lean_dec_ref(v_target_2000_);
lean_dec(v_goal_1999_);
lean_dec(v_weight_1998_);
v_a_2239_ = lean_ctor_get(v___x_2237_, 0);
v_isSharedCheck_2268_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2268_ == 0)
{
v___x_2241_ = v___x_2237_;
v_isShared_2242_ = v_isSharedCheck_2268_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_2237_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2268_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
uint8_t v___y_2244_; uint8_t v___x_2266_; 
v___x_2266_ = l_Lean_Exception_isInterrupt(v_a_2239_);
if (v___x_2266_ == 0)
{
uint8_t v___x_2267_; 
lean_inc(v_a_2239_);
v___x_2267_ = l_Lean_Exception_isRuntime(v_a_2239_);
v___y_2244_ = v___x_2267_;
goto v___jp_2243_;
}
else
{
v___y_2244_ = v___x_2266_;
goto v___jp_2243_;
}
v___jp_2243_:
{
if (v___y_2244_ == 0)
{
lean_object* v___x_2245_; 
lean_del_object(v___x_2241_);
lean_dec(v_a_2239_);
v___x_2245_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2236_, v___y_2005_, v___y_2007_);
lean_dec(v_a_2236_);
if (lean_obj_tag(v___x_2245_) == 0)
{
lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2253_; 
v_isSharedCheck_2253_ = !lean_is_exclusive(v___x_2245_);
if (v_isSharedCheck_2253_ == 0)
{
lean_object* v_unused_2254_; 
v_unused_2254_ = lean_ctor_get(v___x_2245_, 0);
lean_dec(v_unused_2254_);
v___x_2247_ = v___x_2245_;
v_isShared_2248_ = v_isSharedCheck_2253_;
goto v_resetjp_2246_;
}
else
{
lean_dec(v___x_2245_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2253_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v___x_2249_; lean_object* v___x_2251_; 
v___x_2249_ = lean_box(0);
if (v_isShared_2248_ == 0)
{
lean_ctor_set(v___x_2247_, 0, v___x_2249_);
v___x_2251_ = v___x_2247_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v___x_2249_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
}
}
}
else
{
lean_object* v_a_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2262_; 
v_a_2255_ = lean_ctor_get(v___x_2245_, 0);
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2245_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2257_ = v___x_2245_;
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_a_2255_);
lean_dec(v___x_2245_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
lean_object* v___x_2260_; 
if (v_isShared_2258_ == 0)
{
v___x_2260_ = v___x_2257_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_a_2255_);
v___x_2260_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
return v___x_2260_;
}
}
}
}
else
{
lean_object* v___x_2264_; 
lean_dec(v_a_2236_);
if (v_isShared_2242_ == 0)
{
v___x_2264_ = v___x_2241_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_a_2239_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
}
}
}
}
else
{
lean_object* v_a_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2276_; 
lean_dec(v_val_2234_);
lean_dec_ref(v_target_2000_);
lean_dec(v_goal_1999_);
lean_dec(v_weight_1998_);
v_a_2269_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2276_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2271_ = v___x_2235_;
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_a_2269_);
lean_dec(v___x_2235_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
lean_object* v___x_2274_; 
if (v_isShared_2272_ == 0)
{
v___x_2274_ = v___x_2271_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v_a_2269_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
return v___x_2274_;
}
}
}
}
v___jp_2009_:
{
if (v___y_2014_ == 0)
{
lean_object* v___x_2015_; 
lean_dec_ref(v___y_2012_);
v___x_2015_ = l_Lean_Meta_SavedState_restore___redArg(v___y_2011_, v___y_2013_, v___y_2010_);
lean_dec_ref(v___y_2011_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2023_; 
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2023_ == 0)
{
lean_object* v_unused_2024_; 
v_unused_2024_ = lean_ctor_get(v___x_2015_, 0);
lean_dec(v_unused_2024_);
v___x_2017_ = v___x_2015_;
v_isShared_2018_ = v_isSharedCheck_2023_;
goto v_resetjp_2016_;
}
else
{
lean_dec(v___x_2015_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2023_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2019_; lean_object* v___x_2021_; 
v___x_2019_ = lean_box(0);
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 0, v___x_2019_);
v___x_2021_ = v___x_2017_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v___x_2019_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
}
else
{
lean_object* v_a_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2032_; 
v_a_2025_ = lean_ctor_get(v___x_2015_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2027_ = v___x_2015_;
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_a_2025_);
lean_dec(v___x_2015_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2030_; 
if (v_isShared_2028_ == 0)
{
v___x_2030_ = v___x_2027_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_a_2025_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
return v___x_2030_;
}
}
}
}
else
{
lean_object* v___x_2033_; 
lean_dec_ref(v___y_2011_);
v___x_2033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2033_, 0, v___y_2012_);
return v___x_2033_;
}
}
v___jp_2034_:
{
lean_object* v___x_2043_; lean_object* v_mctx_2044_; lean_object* v___x_2045_; 
v___x_2043_ = lean_st_ref_get(v___y_2040_);
v_mctx_2044_ = lean_ctor_get(v___x_2043_, 0);
lean_inc_ref_n(v_mctx_2044_, 2);
lean_dec(v___x_2043_);
v___x_2045_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(v_mctx_2044_, v___y_2035_, v___y_2039_, v___y_2040_, v___y_2038_, v___y_2036_);
if (lean_obj_tag(v___x_2045_) == 0)
{
lean_object* v_a_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2056_; 
v_a_2046_ = lean_ctor_get(v___x_2045_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2048_ = v___x_2045_;
v_isShared_2049_ = v_isSharedCheck_2056_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_a_2046_);
lean_dec(v___x_2045_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2056_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v___x_2050_; uint8_t v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2054_; 
v___x_2050_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2050_, 0, v_fst_2041_);
lean_ctor_set(v___x_2050_, 1, v_weight_1998_);
lean_ctor_set(v___x_2050_, 2, v___y_2037_);
lean_ctor_set(v___x_2050_, 3, v_mctx_2044_);
lean_ctor_set_uint8(v___x_2050_, sizeof(void*)*4, v_snd_2042_);
v___x_2051_ = lean_unbox(v_a_2046_);
lean_dec(v_a_2046_);
lean_ctor_set_uint8(v___x_2050_, sizeof(void*)*4 + 1, v___x_2051_);
v___x_2052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2052_, 0, v___x_2050_);
if (v_isShared_2049_ == 0)
{
lean_ctor_set(v___x_2048_, 0, v___x_2052_);
v___x_2054_ = v___x_2048_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v___x_2052_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
else
{
lean_object* v_a_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2064_; 
lean_dec_ref(v_mctx_2044_);
lean_dec_ref(v_fst_2041_);
lean_dec_ref(v___y_2037_);
lean_dec(v_weight_1998_);
v_a_2057_ = lean_ctor_get(v___x_2045_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2059_ = v___x_2045_;
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_dec(v___x_2045_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2062_; 
if (v_isShared_2060_ == 0)
{
v___x_2062_ = v___x_2059_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_a_2057_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
}
v___jp_2065_:
{
lean_object* v___x_2074_; 
v___x_2074_ = l_Lean_Meta_Rewrites_rewriteResultLemma(v___y_2067_);
if (lean_obj_tag(v___x_2074_) == 1)
{
lean_object* v_val_2075_; lean_object* v___x_2076_; lean_object* v_a_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; uint8_t v___x_2080_; 
v_val_2075_ = lean_ctor_get(v___x_2074_, 0);
lean_inc(v_val_2075_);
lean_dec_ref_known(v___x_2074_, 1);
v___x_2076_ = l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg(v_val_2075_, v___y_2071_);
v_a_2077_ = lean_ctor_get(v___x_2076_, 0);
lean_inc(v_a_2077_);
lean_dec_ref(v___x_2076_);
v___x_2078_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__1));
v___x_2079_ = lean_unsigned_to_nat(4u);
v___x_2080_ = l_Lean_Expr_isAppOfArity(v_a_2077_, v___x_2078_, v___x_2079_);
if (v___x_2080_ == 0)
{
v___y_2035_ = v___y_2066_;
v___y_2036_ = v___y_2073_;
v___y_2037_ = v___y_2067_;
v___y_2038_ = v___y_2072_;
v___y_2039_ = v___y_2070_;
v___y_2040_ = v___y_2071_;
v_fst_2041_ = v_a_2077_;
v_snd_2042_ = v___y_2068_;
goto v___jp_2034_;
}
else
{
lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; 
v___x_2081_ = lean_unsigned_to_nat(3u);
v___x_2082_ = l_Lean_Expr_getAppNumArgs(v_a_2077_);
v___x_2083_ = lean_nat_sub(v___x_2082_, v___x_2081_);
lean_dec(v___x_2082_);
v___x_2084_ = lean_unsigned_to_nat(1u);
v___x_2085_ = lean_nat_sub(v___x_2083_, v___x_2084_);
lean_dec(v___x_2083_);
v___x_2086_ = l_Lean_Expr_getRevArg_x21(v_a_2077_, v___x_2085_);
lean_dec(v_a_2077_);
v___y_2035_ = v___y_2066_;
v___y_2036_ = v___y_2073_;
v___y_2037_ = v___y_2067_;
v___y_2038_ = v___y_2072_;
v___y_2039_ = v___y_2070_;
v___y_2040_ = v___y_2071_;
v_fst_2041_ = v___x_2086_;
v_snd_2042_ = v___y_2069_;
goto v___jp_2034_;
}
}
else
{
lean_object* v___x_2087_; lean_object* v___x_2088_; 
lean_dec(v___x_2074_);
lean_dec_ref(v___y_2067_);
lean_dec_ref(v___y_2066_);
lean_dec(v_weight_1998_);
v___x_2087_ = lean_box(0);
v___x_2088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2087_);
return v___x_2088_;
}
}
v___jp_2089_:
{
lean_object* v___x_2090_; lean_object* v___x_2091_; 
v___x_2090_ = lean_box(0);
v___x_2091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2090_);
return v___x_2091_;
}
v___jp_2092_:
{
if (v___y_2097_ == 0)
{
lean_object* v___x_2098_; 
lean_dec_ref(v___y_2094_);
v___x_2098_ = l_Lean_Meta_SavedState_restore___redArg(v___y_2095_, v___y_2096_, v___y_2093_);
lean_dec_ref(v___y_2095_);
if (lean_obj_tag(v___x_2098_) == 0)
{
lean_dec_ref_known(v___x_2098_, 1);
goto v___jp_2089_;
}
else
{
lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2106_; 
v_a_2099_ = lean_ctor_get(v___x_2098_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2101_ = v___x_2098_;
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_dec(v___x_2098_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2104_; 
if (v_isShared_2102_ == 0)
{
v___x_2104_ = v___x_2101_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_a_2099_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
return v___x_2104_;
}
}
}
}
else
{
lean_object* v___x_2107_; 
lean_dec_ref(v___y_2095_);
v___x_2107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2107_, 0, v___y_2094_);
return v___x_2107_;
}
}
v___jp_2108_:
{
if (v___y_2113_ == 0)
{
lean_object* v___x_2114_; 
lean_dec_ref(v___y_2110_);
v___x_2114_ = l_Lean_Meta_SavedState_restore___redArg(v___y_2112_, v___y_2111_, v___y_2109_);
lean_dec_ref(v___y_2112_);
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_dec_ref_known(v___x_2114_, 1);
goto v___jp_2089_;
}
else
{
lean_object* v_a_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2122_; 
v_a_2115_ = lean_ctor_get(v___x_2114_, 0);
v_isSharedCheck_2122_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2122_ == 0)
{
v___x_2117_ = v___x_2114_;
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_a_2115_);
lean_dec(v___x_2114_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
lean_object* v___x_2120_; 
if (v_isShared_2118_ == 0)
{
v___x_2120_ = v___x_2117_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v_a_2115_);
v___x_2120_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
return v___x_2120_;
}
}
}
}
else
{
lean_object* v___x_2123_; 
lean_dec_ref(v___y_2112_);
v___x_2123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2123_, 0, v___y_2110_);
return v___x_2123_;
}
}
v___jp_2124_:
{
lean_object* v___x_2126_; 
v___x_2126_ = l_Lean_Meta_saveState___redArg(v___y_2005_, v___y_2007_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v_a_2127_; uint8_t v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; 
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
lean_inc(v_a_2127_);
lean_dec_ref_known(v___x_2126_, 1);
v___x_2128_ = 1;
v___x_2129_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__2));
lean_inc_ref(v___y_2125_);
v___x_2130_ = l_Lean_MVarId_rewrite(v_goal_1999_, v_target_2000_, v___y_2125_, v_symm_2001_, v___x_2129_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v_a_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2192_; 
lean_dec(v_a_2127_);
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2133_ = v___x_2130_;
v_isShared_2134_ = v_isSharedCheck_2192_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_a_2131_);
lean_dec(v___x_2130_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2192_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v_eNew_2135_; lean_object* v_mvarIds_2136_; uint8_t v___x_2137_; 
v_eNew_2135_ = lean_ctor_get(v_a_2131_, 0);
v_mvarIds_2136_ = lean_ctor_get(v_a_2131_, 2);
v___x_2137_ = l_List_isEmpty___redArg(v_mvarIds_2136_);
if (v___x_2137_ == 0)
{
lean_inc_ref(v_eNew_2135_);
lean_del_object(v___x_2133_);
lean_dec_ref(v___y_2125_);
switch(v_side_2002_)
{
case 0:
{
if (v___x_2137_ == 0)
{
lean_dec_ref(v_eNew_2135_);
lean_dec(v_a_2131_);
lean_dec(v_weight_1998_);
goto v___jp_2089_;
}
else
{
v___y_2066_ = v_eNew_2135_;
v___y_2067_ = v_a_2131_;
v___y_2068_ = v___x_2137_;
v___y_2069_ = v___x_2128_;
v___y_2070_ = v___y_2004_;
v___y_2071_ = v___y_2005_;
v___y_2072_ = v___y_2006_;
v___y_2073_ = v___y_2007_;
goto v___jp_2065_;
}
}
case 1:
{
lean_object* v___x_2138_; 
v___x_2138_ = l_Lean_Meta_saveState___redArg(v___y_2005_, v___y_2007_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v_a_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; 
v_a_2139_ = lean_ctor_get(v___x_2138_, 0);
lean_inc(v_a_2139_);
lean_dec_ref_known(v___x_2138_, 1);
v___x_2140_ = lean_box(0);
lean_inc(v_mvarIds_2136_);
v___x_2141_ = l_List_mapM_loop___at___00Lean_Meta_Rewrites_rwLemma_spec__1(v_mvarIds_2136_, v___x_2140_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_dec_ref_known(v___x_2141_, 1);
lean_dec(v_a_2139_);
v___y_2066_ = v_eNew_2135_;
v___y_2067_ = v_a_2131_;
v___y_2068_ = v___x_2137_;
v___y_2069_ = v___x_2128_;
v___y_2070_ = v___y_2004_;
v___y_2071_ = v___y_2005_;
v___y_2072_ = v___y_2006_;
v___y_2073_ = v___y_2007_;
goto v___jp_2065_;
}
else
{
lean_object* v_a_2142_; uint8_t v___x_2143_; 
lean_dec_ref(v_eNew_2135_);
lean_dec(v_a_2131_);
lean_dec(v_weight_1998_);
v_a_2142_ = lean_ctor_get(v___x_2141_, 0);
lean_inc(v_a_2142_);
lean_dec_ref_known(v___x_2141_, 1);
v___x_2143_ = l_Lean_Exception_isInterrupt(v_a_2142_);
if (v___x_2143_ == 0)
{
uint8_t v___x_2144_; 
lean_inc(v_a_2142_);
v___x_2144_ = l_Lean_Exception_isRuntime(v_a_2142_);
v___y_2109_ = v___y_2007_;
v___y_2110_ = v_a_2142_;
v___y_2111_ = v___y_2005_;
v___y_2112_ = v_a_2139_;
v___y_2113_ = v___x_2144_;
goto v___jp_2108_;
}
else
{
v___y_2109_ = v___y_2007_;
v___y_2110_ = v_a_2142_;
v___y_2111_ = v___y_2005_;
v___y_2112_ = v_a_2139_;
v___y_2113_ = v___x_2143_;
goto v___jp_2108_;
}
}
}
else
{
lean_object* v_a_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2152_; 
lean_dec_ref(v_eNew_2135_);
lean_dec(v_a_2131_);
lean_dec(v_weight_1998_);
v_a_2145_ = lean_ctor_get(v___x_2138_, 0);
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2147_ = v___x_2138_;
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_a_2145_);
lean_dec(v___x_2138_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v___x_2150_; 
if (v_isShared_2148_ == 0)
{
v___x_2150_ = v___x_2147_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v_a_2145_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
return v___x_2150_;
}
}
}
}
default: 
{
lean_object* v___x_2153_; 
v___x_2153_ = l_Lean_Meta_saveState___redArg(v___y_2005_, v___y_2007_);
if (lean_obj_tag(v___x_2153_) == 0)
{
lean_object* v_a_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; 
v_a_2154_ = lean_ctor_get(v___x_2153_, 0);
lean_inc(v_a_2154_);
lean_dec_ref_known(v___x_2153_, 1);
v___x_2155_ = lean_unsigned_to_nat(6u);
lean_inc(v_mvarIds_2136_);
v___x_2156_ = l_Lean_Meta_Rewrites_solveByElim(v_mvarIds_2136_, v___x_2155_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_);
if (lean_obj_tag(v___x_2156_) == 0)
{
lean_dec_ref_known(v___x_2156_, 1);
lean_dec(v_a_2154_);
v___y_2066_ = v_eNew_2135_;
v___y_2067_ = v_a_2131_;
v___y_2068_ = v___x_2137_;
v___y_2069_ = v___x_2128_;
v___y_2070_ = v___y_2004_;
v___y_2071_ = v___y_2005_;
v___y_2072_ = v___y_2006_;
v___y_2073_ = v___y_2007_;
goto v___jp_2065_;
}
else
{
lean_object* v_a_2157_; uint8_t v___x_2158_; 
lean_dec_ref(v_eNew_2135_);
lean_dec(v_a_2131_);
lean_dec(v_weight_1998_);
v_a_2157_ = lean_ctor_get(v___x_2156_, 0);
lean_inc(v_a_2157_);
lean_dec_ref_known(v___x_2156_, 1);
v___x_2158_ = l_Lean_Exception_isInterrupt(v_a_2157_);
if (v___x_2158_ == 0)
{
uint8_t v___x_2159_; 
lean_inc(v_a_2157_);
v___x_2159_ = l_Lean_Exception_isRuntime(v_a_2157_);
v___y_2093_ = v___y_2007_;
v___y_2094_ = v_a_2157_;
v___y_2095_ = v_a_2154_;
v___y_2096_ = v___y_2005_;
v___y_2097_ = v___x_2159_;
goto v___jp_2092_;
}
else
{
v___y_2093_ = v___y_2007_;
v___y_2094_ = v_a_2157_;
v___y_2095_ = v_a_2154_;
v___y_2096_ = v___y_2005_;
v___y_2097_ = v___x_2158_;
goto v___jp_2092_;
}
}
}
else
{
lean_object* v_a_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2167_; 
lean_dec_ref(v_eNew_2135_);
lean_dec(v_a_2131_);
lean_dec(v_weight_1998_);
v_a_2160_ = lean_ctor_get(v___x_2153_, 0);
v_isSharedCheck_2167_ = !lean_is_exclusive(v___x_2153_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2162_ = v___x_2153_;
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_a_2160_);
lean_dec(v___x_2153_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___x_2165_; 
if (v_isShared_2163_ == 0)
{
v___x_2165_ = v___x_2162_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v_a_2160_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
}
}
}
}
}
}
else
{
lean_object* v___x_2168_; lean_object* v_mctx_2169_; lean_object* v___x_2170_; 
v___x_2168_ = lean_st_ref_get(v___y_2005_);
v_mctx_2169_ = lean_ctor_get(v___x_2168_, 0);
lean_inc_ref_n(v_mctx_2169_, 2);
lean_dec(v___x_2168_);
lean_inc_ref(v_eNew_2135_);
v___x_2170_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(v_mctx_2169_, v_eNew_2135_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_object* v_a_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2183_; 
v_a_2171_ = lean_ctor_get(v___x_2170_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2173_ = v___x_2170_;
v_isShared_2174_ = v_isSharedCheck_2183_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_a_2171_);
lean_dec(v___x_2170_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2183_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2175_; uint8_t v___x_2176_; lean_object* v___x_2178_; 
v___x_2175_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2175_, 0, v___y_2125_);
lean_ctor_set(v___x_2175_, 1, v_weight_1998_);
lean_ctor_set(v___x_2175_, 2, v_a_2131_);
lean_ctor_set(v___x_2175_, 3, v_mctx_2169_);
lean_ctor_set_uint8(v___x_2175_, sizeof(void*)*4, v_symm_2001_);
v___x_2176_ = lean_unbox(v_a_2171_);
lean_dec(v_a_2171_);
lean_ctor_set_uint8(v___x_2175_, sizeof(void*)*4 + 1, v___x_2176_);
if (v_isShared_2134_ == 0)
{
lean_ctor_set_tag(v___x_2133_, 1);
lean_ctor_set(v___x_2133_, 0, v___x_2175_);
v___x_2178_ = v___x_2133_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v___x_2175_);
v___x_2178_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
lean_object* v___x_2180_; 
if (v_isShared_2174_ == 0)
{
lean_ctor_set(v___x_2173_, 0, v___x_2178_);
v___x_2180_ = v___x_2173_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v___x_2178_);
v___x_2180_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
return v___x_2180_;
}
}
}
}
else
{
lean_object* v_a_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2191_; 
lean_dec_ref(v_mctx_2169_);
lean_del_object(v___x_2133_);
lean_dec(v_a_2131_);
lean_dec_ref(v___y_2125_);
lean_dec(v_weight_1998_);
v_a_2184_ = lean_ctor_get(v___x_2170_, 0);
v_isSharedCheck_2191_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2186_ = v___x_2170_;
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_a_2184_);
lean_dec(v___x_2170_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2189_; 
if (v_isShared_2187_ == 0)
{
v___x_2189_ = v___x_2186_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_a_2184_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
}
}
}
}
else
{
lean_object* v_a_2193_; uint8_t v___x_2194_; 
lean_dec_ref(v___y_2125_);
lean_dec(v_weight_1998_);
v_a_2193_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_a_2193_);
lean_dec_ref_known(v___x_2130_, 1);
v___x_2194_ = l_Lean_Exception_isInterrupt(v_a_2193_);
if (v___x_2194_ == 0)
{
uint8_t v___x_2195_; 
lean_inc(v_a_2193_);
v___x_2195_ = l_Lean_Exception_isRuntime(v_a_2193_);
v___y_2010_ = v___y_2007_;
v___y_2011_ = v_a_2127_;
v___y_2012_ = v_a_2193_;
v___y_2013_ = v___y_2005_;
v___y_2014_ = v___x_2195_;
goto v___jp_2009_;
}
else
{
v___y_2010_ = v___y_2007_;
v___y_2011_ = v_a_2127_;
v___y_2012_ = v_a_2193_;
v___y_2013_ = v___y_2005_;
v___y_2014_ = v___x_2194_;
goto v___jp_2009_;
}
}
}
else
{
lean_object* v_a_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2203_; 
lean_dec_ref(v___y_2125_);
lean_dec_ref(v_target_2000_);
lean_dec(v_goal_1999_);
lean_dec(v_weight_1998_);
v_a_2196_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2203_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2198_ = v___x_2126_;
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_a_2196_);
lean_dec(v___x_2126_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v___x_2201_; 
if (v_isShared_2199_ == 0)
{
v___x_2201_ = v___x_2198_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_a_2196_);
v___x_2201_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
return v___x_2201_;
}
}
}
}
v___jp_2204_:
{
lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
lean_inc_ref(v___y_2208_);
v___x_2209_ = l_Lean_stringToMessageData(v___y_2208_);
lean_inc_ref(v___y_2206_);
v___x_2210_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2210_, 0, v___y_2206_);
lean_ctor_set(v___x_2210_, 1, v___x_2209_);
lean_inc_ref(v___y_2205_);
v___x_2211_ = l_Lean_MessageData_ofExpr(v___y_2205_);
v___x_2212_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2212_, 0, v___x_2210_);
lean_ctor_set(v___x_2212_, 1, v___x_2211_);
lean_inc(v___y_2207_);
v___x_2213_ = l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2(v___y_2207_, v___x_2212_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_);
if (lean_obj_tag(v___x_2213_) == 0)
{
lean_dec_ref_known(v___x_2213_, 1);
v___y_2125_ = v___y_2205_;
goto v___jp_2124_;
}
else
{
lean_object* v_a_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2221_; 
lean_dec_ref(v___y_2205_);
lean_dec_ref(v_target_2000_);
lean_dec(v_goal_1999_);
lean_dec(v_weight_1998_);
v_a_2214_ = lean_ctor_get(v___x_2213_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2213_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2216_ = v___x_2213_;
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_a_2214_);
lean_dec(v___x_2213_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2219_; 
if (v_isShared_2217_ == 0)
{
v___x_2219_ = v___x_2216_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_a_2214_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
}
}
v___jp_2222_:
{
lean_object* v_options_2224_; uint8_t v_hasTrace_2225_; 
v_options_2224_ = lean_ctor_get(v___y_2006_, 2);
v_hasTrace_2225_ = lean_ctor_get_uint8(v_options_2224_, sizeof(void*)*1);
if (v_hasTrace_2225_ == 0)
{
v___y_2125_ = v_val_2223_;
goto v___jp_2124_;
}
else
{
lean_object* v_inheritedTraceOptions_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; uint8_t v___x_2229_; 
v_inheritedTraceOptions_2226_ = lean_ctor_get(v___y_2006_, 13);
v___x_2227_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_));
v___x_2228_ = lean_obj_once(&l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5, &l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5_once, _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5);
v___x_2229_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2226_, v_options_2224_, v___x_2228_);
if (v___x_2229_ == 0)
{
v___y_2125_ = v_val_2223_;
goto v___jp_2124_;
}
else
{
lean_object* v___x_2230_; 
v___x_2230_ = lean_obj_once(&l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__7, &l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__7_once, _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__7);
if (v_symm_2001_ == 0)
{
lean_object* v___x_2231_; 
v___x_2231_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__1));
v___y_2205_ = v_val_2223_;
v___y_2206_ = v___x_2230_;
v___y_2207_ = v___x_2227_;
v___y_2208_ = v___x_2231_;
goto v___jp_2204_;
}
else
{
lean_object* v___x_2232_; 
v___x_2232_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__8));
v___y_2205_ = v_val_2223_;
v___y_2206_ = v___x_2230_;
v___y_2207_ = v___x_2227_;
v___y_2208_ = v___x_2232_;
goto v___jp_2204_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0___boxed(lean_object* v_weight_2277_, lean_object* v_goal_2278_, lean_object* v_target_2279_, lean_object* v_symm_2280_, lean_object* v_side_2281_, lean_object* v_lem_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_){
_start:
{
uint8_t v_symm_boxed_2288_; uint8_t v_side_boxed_2289_; lean_object* v_res_2290_; 
v_symm_boxed_2288_ = lean_unbox(v_symm_2280_);
v_side_boxed_2289_ = lean_unbox(v_side_2281_);
v_res_2290_ = l_Lean_Meta_Rewrites_rwLemma___lam__0(v_weight_2277_, v_goal_2278_, v_target_2279_, v_symm_boxed_2288_, v_side_boxed_2289_, v_lem_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_);
lean_dec(v___y_2286_);
lean_dec_ref(v___y_2285_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
return v_res_2290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma(lean_object* v_ctx_2291_, lean_object* v_goal_2292_, lean_object* v_target_2293_, uint8_t v_side_2294_, lean_object* v_lem_2295_, uint8_t v_symm_2296_, lean_object* v_weight_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_){
_start:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___f_2305_; lean_object* v___x_2306_; 
v___x_2303_ = lean_box(v_symm_2296_);
v___x_2304_ = lean_box(v_side_2294_);
v___f_2305_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___boxed), 11, 6);
lean_closure_set(v___f_2305_, 0, v_weight_2297_);
lean_closure_set(v___f_2305_, 1, v_goal_2292_);
lean_closure_set(v___f_2305_, 2, v_target_2293_);
lean_closure_set(v___f_2305_, 3, v___x_2303_);
lean_closure_set(v___f_2305_, 4, v___x_2304_);
lean_closure_set(v___f_2305_, 5, v_lem_2295_);
v___x_2306_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg(v_ctx_2291_, v___f_2305_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_);
return v___x_2306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___boxed(lean_object* v_ctx_2307_, lean_object* v_goal_2308_, lean_object* v_target_2309_, lean_object* v_side_2310_, lean_object* v_lem_2311_, lean_object* v_symm_2312_, lean_object* v_weight_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_){
_start:
{
uint8_t v_side_boxed_2319_; uint8_t v_symm_boxed_2320_; lean_object* v_res_2321_; 
v_side_boxed_2319_ = lean_unbox(v_side_2310_);
v_symm_boxed_2320_ = lean_unbox(v_symm_2312_);
v_res_2321_ = l_Lean_Meta_Rewrites_rwLemma(v_ctx_2307_, v_goal_2308_, v_target_2309_, v_side_boxed_2319_, v_lem_2311_, v_symm_boxed_2320_, v_weight_2313_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_);
lean_dec(v_a_2317_);
lean_dec_ref(v_a_2316_);
lean_dec(v_a_2315_);
lean_dec_ref(v_a_2314_);
return v_res_2321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(lean_object* v_type_2322_, lean_object* v_k_2323_, uint8_t v_cleanupAnnotations_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_){
_start:
{
lean_object* v___f_2330_; uint8_t v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; 
v___f_2330_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2330_, 0, v_k_2323_);
v___x_2331_ = 0;
v___x_2332_ = lean_box(0);
v___x_2333_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_2331_, v___x_2332_, v_type_2322_, v___f_2330_, v_cleanupAnnotations_2324_, v___x_2331_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_);
if (lean_obj_tag(v___x_2333_) == 0)
{
lean_object* v_a_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2341_; 
v_a_2334_ = lean_ctor_get(v___x_2333_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2336_ = v___x_2333_;
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_a_2334_);
lean_dec(v___x_2333_);
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
v_reuseFailAlloc_2340_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2349_; 
v_a_2342_ = lean_ctor_get(v___x_2333_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2344_ = v___x_2333_;
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_a_2342_);
lean_dec(v___x_2333_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg___boxed(lean_object* v_type_2350_, lean_object* v_k_2351_, lean_object* v_cleanupAnnotations_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2358_; lean_object* v_res_2359_; 
v_cleanupAnnotations_boxed_2358_ = lean_unbox(v_cleanupAnnotations_2352_);
v_res_2359_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(v_type_2350_, v_k_2351_, v_cleanupAnnotations_boxed_2358_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_);
lean_dec(v___y_2356_);
lean_dec_ref(v___y_2355_);
lean_dec(v___y_2354_);
lean_dec_ref(v___y_2353_);
return v_res_2359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1(lean_object* v_00_u03b1_2360_, lean_object* v_type_2361_, lean_object* v_k_2362_, uint8_t v_cleanupAnnotations_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_){
_start:
{
lean_object* v___x_2369_; 
v___x_2369_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(v_type_2361_, v_k_2362_, v_cleanupAnnotations_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_);
return v___x_2369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___boxed(lean_object* v_00_u03b1_2370_, lean_object* v_type_2371_, lean_object* v_k_2372_, lean_object* v_cleanupAnnotations_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2379_; lean_object* v_res_2380_; 
v_cleanupAnnotations_boxed_2379_ = lean_unbox(v_cleanupAnnotations_2373_);
v_res_2380_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1(v_00_u03b1_2370_, v_type_2371_, v_k_2372_, v_cleanupAnnotations_boxed_2379_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
return v_res_2380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(lean_object* v_e_2381_, lean_object* v_k_2382_, uint8_t v_cleanupAnnotations_2383_, uint8_t v_preserveNondepLet_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_){
_start:
{
lean_object* v___f_2390_; uint8_t v___x_2391_; uint8_t v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___f_2390_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2390_, 0, v_k_2382_);
v___x_2391_ = 1;
v___x_2392_ = 0;
v___x_2393_ = lean_box(0);
v___x_2394_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2381_, v___x_2391_, v___x_2391_, v_preserveNondepLet_2384_, v___x_2392_, v___x_2393_, v___f_2390_, v_cleanupAnnotations_2383_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_);
if (lean_obj_tag(v___x_2394_) == 0)
{
lean_object* v_a_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2402_; 
v_a_2395_ = lean_ctor_get(v___x_2394_, 0);
v_isSharedCheck_2402_ = !lean_is_exclusive(v___x_2394_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2397_ = v___x_2394_;
v_isShared_2398_ = v_isSharedCheck_2402_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_a_2395_);
lean_dec(v___x_2394_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2402_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v___x_2400_; 
if (v_isShared_2398_ == 0)
{
v___x_2400_ = v___x_2397_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v_a_2395_);
v___x_2400_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
return v___x_2400_;
}
}
}
else
{
lean_object* v_a_2403_; lean_object* v___x_2405_; uint8_t v_isShared_2406_; uint8_t v_isSharedCheck_2410_; 
v_a_2403_ = lean_ctor_get(v___x_2394_, 0);
v_isSharedCheck_2410_ = !lean_is_exclusive(v___x_2394_);
if (v_isSharedCheck_2410_ == 0)
{
v___x_2405_ = v___x_2394_;
v_isShared_2406_ = v_isSharedCheck_2410_;
goto v_resetjp_2404_;
}
else
{
lean_inc(v_a_2403_);
lean_dec(v___x_2394_);
v___x_2405_ = lean_box(0);
v_isShared_2406_ = v_isSharedCheck_2410_;
goto v_resetjp_2404_;
}
v_resetjp_2404_:
{
lean_object* v___x_2408_; 
if (v_isShared_2406_ == 0)
{
v___x_2408_ = v___x_2405_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v_a_2403_);
v___x_2408_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
return v___x_2408_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg___boxed(lean_object* v_e_2411_, lean_object* v_k_2412_, lean_object* v_cleanupAnnotations_2413_, lean_object* v_preserveNondepLet_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2420_; uint8_t v_preserveNondepLet_boxed_2421_; lean_object* v_res_2422_; 
v_cleanupAnnotations_boxed_2420_ = lean_unbox(v_cleanupAnnotations_2413_);
v_preserveNondepLet_boxed_2421_ = lean_unbox(v_preserveNondepLet_2414_);
v_res_2422_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(v_e_2411_, v_k_2412_, v_cleanupAnnotations_boxed_2420_, v_preserveNondepLet_boxed_2421_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_);
lean_dec(v___y_2418_);
lean_dec_ref(v___y_2417_);
lean_dec(v___y_2416_);
lean_dec_ref(v___y_2415_);
return v_res_2422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2(lean_object* v_00_u03b1_2423_, lean_object* v_e_2424_, lean_object* v_k_2425_, uint8_t v_cleanupAnnotations_2426_, uint8_t v_preserveNondepLet_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_){
_start:
{
lean_object* v___x_2433_; 
v___x_2433_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(v_e_2424_, v_k_2425_, v_cleanupAnnotations_2426_, v_preserveNondepLet_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_);
return v___x_2433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___boxed(lean_object* v_00_u03b1_2434_, lean_object* v_e_2435_, lean_object* v_k_2436_, lean_object* v_cleanupAnnotations_2437_, lean_object* v_preserveNondepLet_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2444_; uint8_t v_preserveNondepLet_boxed_2445_; lean_object* v_res_2446_; 
v_cleanupAnnotations_boxed_2444_ = lean_unbox(v_cleanupAnnotations_2437_);
v_preserveNondepLet_boxed_2445_ = lean_unbox(v_preserveNondepLet_2438_);
v_res_2446_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2(v_00_u03b1_2434_, v_e_2435_, v_k_2436_, v_cleanupAnnotations_boxed_2444_, v_preserveNondepLet_boxed_2445_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_);
lean_dec(v___y_2442_);
lean_dec_ref(v___y_2441_);
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
return v_res_2446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(lean_object* v_f_2447_, lean_object* v_e_x27_2448_, lean_object* v_a_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_){
_start:
{
lean_object* v___x_2455_; 
lean_inc(v___y_2453_);
lean_inc_ref(v___y_2452_);
lean_inc(v___y_2451_);
lean_inc_ref(v___y_2450_);
lean_inc_ref(v_e_x27_2448_);
v___x_2455_ = lean_apply_7(v_f_2447_, v_a_2449_, v_e_x27_2448_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_, lean_box(0));
if (lean_obj_tag(v___x_2455_) == 0)
{
lean_object* v_a_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2464_; 
v_a_2456_ = lean_ctor_get(v___x_2455_, 0);
v_isSharedCheck_2464_ = !lean_is_exclusive(v___x_2455_);
if (v_isSharedCheck_2464_ == 0)
{
v___x_2458_ = v___x_2455_;
v_isShared_2459_ = v_isSharedCheck_2464_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_a_2456_);
lean_dec(v___x_2455_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2464_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v___x_2460_; lean_object* v___x_2462_; 
v___x_2460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2460_, 0, v_e_x27_2448_);
lean_ctor_set(v___x_2460_, 1, v_a_2456_);
if (v_isShared_2459_ == 0)
{
lean_ctor_set(v___x_2458_, 0, v___x_2460_);
v___x_2462_ = v___x_2458_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v___x_2460_);
v___x_2462_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
return v___x_2462_;
}
}
}
else
{
lean_object* v_a_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2472_; 
lean_dec_ref(v_e_x27_2448_);
v_a_2465_ = lean_ctor_get(v___x_2455_, 0);
v_isSharedCheck_2472_ = !lean_is_exclusive(v___x_2455_);
if (v_isSharedCheck_2472_ == 0)
{
v___x_2467_ = v___x_2455_;
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_a_2465_);
lean_dec(v___x_2455_);
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
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0___boxed(lean_object* v_f_2473_, lean_object* v_e_x27_2474_, lean_object* v_a_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_){
_start:
{
lean_object* v_res_2481_; 
v_res_2481_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2473_, v_e_x27_2474_, v_a_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_);
lean_dec(v___y_2479_);
lean_dec_ref(v___y_2478_);
lean_dec(v___y_2477_);
lean_dec_ref(v___y_2476_);
return v_res_2481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg(lean_object* v_f_2482_, lean_object* v_x_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_){
_start:
{
switch(lean_obj_tag(v_x_2483_))
{
case 7:
{
lean_object* v_binderName_2490_; lean_object* v_binderType_2491_; lean_object* v_body_2492_; uint8_t v_binderInfo_2493_; lean_object* v___x_2494_; 
v_binderName_2490_ = lean_ctor_get(v_x_2483_, 0);
v_binderType_2491_ = lean_ctor_get(v_x_2483_, 1);
v_body_2492_ = lean_ctor_get(v_x_2483_, 2);
v_binderInfo_2493_ = lean_ctor_get_uint8(v_x_2483_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2491_);
lean_inc_ref(v_f_2482_);
v___x_2494_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2482_, v_binderType_2491_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_);
if (lean_obj_tag(v___x_2494_) == 0)
{
lean_object* v_a_2495_; lean_object* v_fst_2496_; lean_object* v_snd_2497_; lean_object* v___x_2498_; 
v_a_2495_ = lean_ctor_get(v___x_2494_, 0);
lean_inc(v_a_2495_);
lean_dec_ref_known(v___x_2494_, 1);
v_fst_2496_ = lean_ctor_get(v_a_2495_, 0);
lean_inc(v_fst_2496_);
v_snd_2497_ = lean_ctor_get(v_a_2495_, 1);
lean_inc(v_snd_2497_);
lean_dec(v_a_2495_);
lean_inc_ref(v_body_2492_);
v___x_2498_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2482_, v_body_2492_, v_snd_2497_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_);
if (lean_obj_tag(v___x_2498_) == 0)
{
lean_object* v_a_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2528_; 
v_a_2499_ = lean_ctor_get(v___x_2498_, 0);
v_isSharedCheck_2528_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_2528_ == 0)
{
v___x_2501_ = v___x_2498_;
v_isShared_2502_ = v_isSharedCheck_2528_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_a_2499_);
lean_dec(v___x_2498_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2528_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v_fst_2503_; lean_object* v_snd_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2527_; 
v_fst_2503_ = lean_ctor_get(v_a_2499_, 0);
v_snd_2504_ = lean_ctor_get(v_a_2499_, 1);
v_isSharedCheck_2527_ = !lean_is_exclusive(v_a_2499_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2506_ = v_a_2499_;
v_isShared_2507_ = v_isSharedCheck_2527_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_snd_2504_);
lean_inc(v_fst_2503_);
lean_dec(v_a_2499_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2527_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
lean_object* v___y_2509_; uint8_t v___y_2517_; size_t v___x_2521_; size_t v___x_2522_; uint8_t v___x_2523_; 
v___x_2521_ = lean_ptr_addr(v_binderType_2491_);
v___x_2522_ = lean_ptr_addr(v_fst_2496_);
v___x_2523_ = lean_usize_dec_eq(v___x_2521_, v___x_2522_);
if (v___x_2523_ == 0)
{
v___y_2517_ = v___x_2523_;
goto v___jp_2516_;
}
else
{
size_t v___x_2524_; size_t v___x_2525_; uint8_t v___x_2526_; 
v___x_2524_ = lean_ptr_addr(v_body_2492_);
v___x_2525_ = lean_ptr_addr(v_fst_2503_);
v___x_2526_ = lean_usize_dec_eq(v___x_2524_, v___x_2525_);
v___y_2517_ = v___x_2526_;
goto v___jp_2516_;
}
v___jp_2508_:
{
lean_object* v___x_2511_; 
if (v_isShared_2507_ == 0)
{
lean_ctor_set(v___x_2506_, 0, v___y_2509_);
v___x_2511_ = v___x_2506_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v___y_2509_);
lean_ctor_set(v_reuseFailAlloc_2515_, 1, v_snd_2504_);
v___x_2511_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
lean_object* v___x_2513_; 
if (v_isShared_2502_ == 0)
{
lean_ctor_set(v___x_2501_, 0, v___x_2511_);
v___x_2513_ = v___x_2501_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v___x_2511_);
v___x_2513_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
return v___x_2513_;
}
}
}
v___jp_2516_:
{
if (v___y_2517_ == 0)
{
lean_object* v___x_2518_; 
lean_inc(v_binderName_2490_);
lean_dec_ref_known(v_x_2483_, 3);
v___x_2518_ = l_Lean_Expr_forallE___override(v_binderName_2490_, v_fst_2496_, v_fst_2503_, v_binderInfo_2493_);
v___y_2509_ = v___x_2518_;
goto v___jp_2508_;
}
else
{
uint8_t v___x_2519_; 
v___x_2519_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2493_, v_binderInfo_2493_);
if (v___x_2519_ == 0)
{
lean_object* v___x_2520_; 
lean_inc(v_binderName_2490_);
lean_dec_ref_known(v_x_2483_, 3);
v___x_2520_ = l_Lean_Expr_forallE___override(v_binderName_2490_, v_fst_2496_, v_fst_2503_, v_binderInfo_2493_);
v___y_2509_ = v___x_2520_;
goto v___jp_2508_;
}
else
{
lean_dec(v_fst_2503_);
lean_dec(v_fst_2496_);
v___y_2509_ = v_x_2483_;
goto v___jp_2508_;
}
}
}
}
}
}
else
{
lean_dec(v_fst_2496_);
lean_dec_ref_known(v_x_2483_, 3);
return v___x_2498_;
}
}
else
{
lean_dec_ref_known(v_x_2483_, 3);
lean_dec_ref(v_f_2482_);
return v___x_2494_;
}
}
case 6:
{
lean_object* v_binderName_2529_; lean_object* v_binderType_2530_; lean_object* v_body_2531_; uint8_t v_binderInfo_2532_; lean_object* v___x_2533_; 
v_binderName_2529_ = lean_ctor_get(v_x_2483_, 0);
v_binderType_2530_ = lean_ctor_get(v_x_2483_, 1);
v_body_2531_ = lean_ctor_get(v_x_2483_, 2);
v_binderInfo_2532_ = lean_ctor_get_uint8(v_x_2483_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2530_);
lean_inc_ref(v_f_2482_);
v___x_2533_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2482_, v_binderType_2530_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_);
if (lean_obj_tag(v___x_2533_) == 0)
{
lean_object* v_a_2534_; lean_object* v_fst_2535_; lean_object* v_snd_2536_; lean_object* v___x_2537_; 
v_a_2534_ = lean_ctor_get(v___x_2533_, 0);
lean_inc(v_a_2534_);
lean_dec_ref_known(v___x_2533_, 1);
v_fst_2535_ = lean_ctor_get(v_a_2534_, 0);
lean_inc(v_fst_2535_);
v_snd_2536_ = lean_ctor_get(v_a_2534_, 1);
lean_inc(v_snd_2536_);
lean_dec(v_a_2534_);
lean_inc_ref(v_body_2531_);
v___x_2537_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2482_, v_body_2531_, v_snd_2536_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_);
if (lean_obj_tag(v___x_2537_) == 0)
{
lean_object* v_a_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2567_; 
v_a_2538_ = lean_ctor_get(v___x_2537_, 0);
v_isSharedCheck_2567_ = !lean_is_exclusive(v___x_2537_);
if (v_isSharedCheck_2567_ == 0)
{
v___x_2540_ = v___x_2537_;
v_isShared_2541_ = v_isSharedCheck_2567_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_a_2538_);
lean_dec(v___x_2537_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2567_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v_fst_2542_; lean_object* v_snd_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2566_; 
v_fst_2542_ = lean_ctor_get(v_a_2538_, 0);
v_snd_2543_ = lean_ctor_get(v_a_2538_, 1);
v_isSharedCheck_2566_ = !lean_is_exclusive(v_a_2538_);
if (v_isSharedCheck_2566_ == 0)
{
v___x_2545_ = v_a_2538_;
v_isShared_2546_ = v_isSharedCheck_2566_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_snd_2543_);
lean_inc(v_fst_2542_);
lean_dec(v_a_2538_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2566_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v___y_2548_; uint8_t v___y_2556_; size_t v___x_2560_; size_t v___x_2561_; uint8_t v___x_2562_; 
v___x_2560_ = lean_ptr_addr(v_binderType_2530_);
v___x_2561_ = lean_ptr_addr(v_fst_2535_);
v___x_2562_ = lean_usize_dec_eq(v___x_2560_, v___x_2561_);
if (v___x_2562_ == 0)
{
v___y_2556_ = v___x_2562_;
goto v___jp_2555_;
}
else
{
size_t v___x_2563_; size_t v___x_2564_; uint8_t v___x_2565_; 
v___x_2563_ = lean_ptr_addr(v_body_2531_);
v___x_2564_ = lean_ptr_addr(v_fst_2542_);
v___x_2565_ = lean_usize_dec_eq(v___x_2563_, v___x_2564_);
v___y_2556_ = v___x_2565_;
goto v___jp_2555_;
}
v___jp_2547_:
{
lean_object* v___x_2550_; 
if (v_isShared_2546_ == 0)
{
lean_ctor_set(v___x_2545_, 0, v___y_2548_);
v___x_2550_ = v___x_2545_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v___y_2548_);
lean_ctor_set(v_reuseFailAlloc_2554_, 1, v_snd_2543_);
v___x_2550_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
lean_object* v___x_2552_; 
if (v_isShared_2541_ == 0)
{
lean_ctor_set(v___x_2540_, 0, v___x_2550_);
v___x_2552_ = v___x_2540_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v___x_2550_);
v___x_2552_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
return v___x_2552_;
}
}
}
v___jp_2555_:
{
if (v___y_2556_ == 0)
{
lean_object* v___x_2557_; 
lean_inc(v_binderName_2529_);
lean_dec_ref_known(v_x_2483_, 3);
v___x_2557_ = l_Lean_Expr_lam___override(v_binderName_2529_, v_fst_2535_, v_fst_2542_, v_binderInfo_2532_);
v___y_2548_ = v___x_2557_;
goto v___jp_2547_;
}
else
{
uint8_t v___x_2558_; 
v___x_2558_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2532_, v_binderInfo_2532_);
if (v___x_2558_ == 0)
{
lean_object* v___x_2559_; 
lean_inc(v_binderName_2529_);
lean_dec_ref_known(v_x_2483_, 3);
v___x_2559_ = l_Lean_Expr_lam___override(v_binderName_2529_, v_fst_2535_, v_fst_2542_, v_binderInfo_2532_);
v___y_2548_ = v___x_2559_;
goto v___jp_2547_;
}
else
{
lean_dec(v_fst_2542_);
lean_dec(v_fst_2535_);
v___y_2548_ = v_x_2483_;
goto v___jp_2547_;
}
}
}
}
}
}
else
{
lean_dec(v_fst_2535_);
lean_dec_ref_known(v_x_2483_, 3);
return v___x_2537_;
}
}
else
{
lean_dec_ref_known(v_x_2483_, 3);
lean_dec_ref(v_f_2482_);
return v___x_2533_;
}
}
case 10:
{
lean_object* v_data_2568_; lean_object* v_expr_2569_; lean_object* v___x_2570_; 
v_data_2568_ = lean_ctor_get(v_x_2483_, 0);
v_expr_2569_ = lean_ctor_get(v_x_2483_, 1);
lean_inc_ref(v_expr_2569_);
v___x_2570_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2482_, v_expr_2569_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_);
if (lean_obj_tag(v___x_2570_) == 0)
{
lean_object* v_a_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2593_; 
v_a_2571_ = lean_ctor_get(v___x_2570_, 0);
v_isSharedCheck_2593_ = !lean_is_exclusive(v___x_2570_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2573_ = v___x_2570_;
v_isShared_2574_ = v_isSharedCheck_2593_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_a_2571_);
lean_dec(v___x_2570_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2593_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v_fst_2575_; lean_object* v_snd_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2592_; 
v_fst_2575_ = lean_ctor_get(v_a_2571_, 0);
v_snd_2576_ = lean_ctor_get(v_a_2571_, 1);
v_isSharedCheck_2592_ = !lean_is_exclusive(v_a_2571_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2578_ = v_a_2571_;
v_isShared_2579_ = v_isSharedCheck_2592_;
goto v_resetjp_2577_;
}
else
{
lean_inc(v_snd_2576_);
lean_inc(v_fst_2575_);
lean_dec(v_a_2571_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2592_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v___y_2581_; size_t v___x_2588_; size_t v___x_2589_; uint8_t v___x_2590_; 
v___x_2588_ = lean_ptr_addr(v_expr_2569_);
v___x_2589_ = lean_ptr_addr(v_fst_2575_);
v___x_2590_ = lean_usize_dec_eq(v___x_2588_, v___x_2589_);
if (v___x_2590_ == 0)
{
lean_object* v___x_2591_; 
lean_inc(v_data_2568_);
lean_dec_ref_known(v_x_2483_, 2);
v___x_2591_ = l_Lean_Expr_mdata___override(v_data_2568_, v_fst_2575_);
v___y_2581_ = v___x_2591_;
goto v___jp_2580_;
}
else
{
lean_dec(v_fst_2575_);
v___y_2581_ = v_x_2483_;
goto v___jp_2580_;
}
v___jp_2580_:
{
lean_object* v___x_2583_; 
if (v_isShared_2579_ == 0)
{
lean_ctor_set(v___x_2578_, 0, v___y_2581_);
v___x_2583_ = v___x_2578_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v___y_2581_);
lean_ctor_set(v_reuseFailAlloc_2587_, 1, v_snd_2576_);
v___x_2583_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
lean_object* v___x_2585_; 
if (v_isShared_2574_ == 0)
{
lean_ctor_set(v___x_2573_, 0, v___x_2583_);
v___x_2585_ = v___x_2573_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v___x_2583_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_x_2483_, 2);
return v___x_2570_;
}
}
case 8:
{
lean_object* v_declName_2594_; lean_object* v_type_2595_; lean_object* v_value_2596_; lean_object* v_body_2597_; uint8_t v_nondep_2598_; lean_object* v___x_2599_; 
v_declName_2594_ = lean_ctor_get(v_x_2483_, 0);
v_type_2595_ = lean_ctor_get(v_x_2483_, 1);
v_value_2596_ = lean_ctor_get(v_x_2483_, 2);
v_body_2597_ = lean_ctor_get(v_x_2483_, 3);
v_nondep_2598_ = lean_ctor_get_uint8(v_x_2483_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_2595_);
lean_inc_ref(v_f_2482_);
v___x_2599_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2482_, v_type_2595_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_);
if (lean_obj_tag(v___x_2599_) == 0)
{
lean_object* v_a_2600_; lean_object* v_fst_2601_; lean_object* v_snd_2602_; lean_object* v___x_2603_; 
v_a_2600_ = lean_ctor_get(v___x_2599_, 0);
lean_inc(v_a_2600_);
lean_dec_ref_known(v___x_2599_, 1);
v_fst_2601_ = lean_ctor_get(v_a_2600_, 0);
lean_inc(v_fst_2601_);
v_snd_2602_ = lean_ctor_get(v_a_2600_, 1);
lean_inc(v_snd_2602_);
lean_dec(v_a_2600_);
lean_inc_ref(v_value_2596_);
lean_inc_ref(v_f_2482_);
v___x_2603_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2482_, v_value_2596_, v_snd_2602_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_);
if (lean_obj_tag(v___x_2603_) == 0)
{
lean_object* v_a_2604_; lean_object* v_fst_2605_; lean_object* v_snd_2606_; lean_object* v___x_2607_; 
v_a_2604_ = lean_ctor_get(v___x_2603_, 0);
lean_inc(v_a_2604_);
lean_dec_ref_known(v___x_2603_, 1);
v_fst_2605_ = lean_ctor_get(v_a_2604_, 0);
lean_inc(v_fst_2605_);
v_snd_2606_ = lean_ctor_get(v_a_2604_, 1);
lean_inc(v_snd_2606_);
lean_dec(v_a_2604_);
lean_inc_ref(v_body_2597_);
v___x_2607_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2482_, v_body_2597_, v_snd_2606_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_);
if (lean_obj_tag(v___x_2607_) == 0)
{
lean_object* v_a_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2639_; 
v_a_2608_ = lean_ctor_get(v___x_2607_, 0);
v_isSharedCheck_2639_ = !lean_is_exclusive(v___x_2607_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2610_ = v___x_2607_;
v_isShared_2611_ = v_isSharedCheck_2639_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_a_2608_);
lean_dec(v___x_2607_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2639_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v_fst_2612_; lean_object* v_snd_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2638_; 
v_fst_2612_ = lean_ctor_get(v_a_2608_, 0);
v_snd_2613_ = lean_ctor_get(v_a_2608_, 1);
v_isSharedCheck_2638_ = !lean_is_exclusive(v_a_2608_);
if (v_isSharedCheck_2638_ == 0)
{
v___x_2615_ = v_a_2608_;
v_isShared_2616_ = v_isSharedCheck_2638_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_snd_2613_);
lean_inc(v_fst_2612_);
lean_dec(v_a_2608_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2638_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
lean_object* v___y_2618_; uint8_t v___y_2626_; size_t v___x_2632_; size_t v___x_2633_; uint8_t v___x_2634_; 
v___x_2632_ = lean_ptr_addr(v_type_2595_);
v___x_2633_ = lean_ptr_addr(v_fst_2601_);
v___x_2634_ = lean_usize_dec_eq(v___x_2632_, v___x_2633_);
if (v___x_2634_ == 0)
{
v___y_2626_ = v___x_2634_;
goto v___jp_2625_;
}
else
{
size_t v___x_2635_; size_t v___x_2636_; uint8_t v___x_2637_; 
v___x_2635_ = lean_ptr_addr(v_value_2596_);
v___x_2636_ = lean_ptr_addr(v_fst_2605_);
v___x_2637_ = lean_usize_dec_eq(v___x_2635_, v___x_2636_);
v___y_2626_ = v___x_2637_;
goto v___jp_2625_;
}
v___jp_2617_:
{
lean_object* v___x_2620_; 
if (v_isShared_2616_ == 0)
{
lean_ctor_set(v___x_2615_, 0, v___y_2618_);
v___x_2620_ = v___x_2615_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v___y_2618_);
lean_ctor_set(v_reuseFailAlloc_2624_, 1, v_snd_2613_);
v___x_2620_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
lean_object* v___x_2622_; 
if (v_isShared_2611_ == 0)
{
lean_ctor_set(v___x_2610_, 0, v___x_2620_);
v___x_2622_ = v___x_2610_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v___x_2620_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
v___jp_2625_:
{
if (v___y_2626_ == 0)
{
lean_object* v___x_2627_; 
lean_inc(v_declName_2594_);
lean_dec_ref_known(v_x_2483_, 4);
v___x_2627_ = l_Lean_Expr_letE___override(v_declName_2594_, v_fst_2601_, v_fst_2605_, v_fst_2612_, v_nondep_2598_);
v___y_2618_ = v___x_2627_;
goto v___jp_2617_;
}
else
{
size_t v___x_2628_; size_t v___x_2629_; uint8_t v___x_2630_; 
v___x_2628_ = lean_ptr_addr(v_body_2597_);
v___x_2629_ = lean_ptr_addr(v_fst_2612_);
v___x_2630_ = lean_usize_dec_eq(v___x_2628_, v___x_2629_);
if (v___x_2630_ == 0)
{
lean_object* v___x_2631_; 
lean_inc(v_declName_2594_);
lean_dec_ref_known(v_x_2483_, 4);
v___x_2631_ = l_Lean_Expr_letE___override(v_declName_2594_, v_fst_2601_, v_fst_2605_, v_fst_2612_, v_nondep_2598_);
v___y_2618_ = v___x_2631_;
goto v___jp_2617_;
}
else
{
lean_dec(v_fst_2612_);
lean_dec(v_fst_2605_);
lean_dec(v_fst_2601_);
v___y_2618_ = v_x_2483_;
goto v___jp_2617_;
}
}
}
}
}
}
else
{
lean_dec(v_fst_2605_);
lean_dec(v_fst_2601_);
lean_dec_ref_known(v_x_2483_, 4);
return v___x_2607_;
}
}
else
{
lean_dec(v_fst_2601_);
lean_dec_ref_known(v_x_2483_, 4);
lean_dec_ref(v_f_2482_);
return v___x_2603_;
}
}
else
{
lean_dec_ref_known(v_x_2483_, 4);
lean_dec_ref(v_f_2482_);
return v___x_2599_;
}
}
case 5:
{
lean_object* v_fn_2640_; lean_object* v_arg_2641_; lean_object* v___x_2642_; 
v_fn_2640_ = lean_ctor_get(v_x_2483_, 0);
v_arg_2641_ = lean_ctor_get(v_x_2483_, 1);
lean_inc_ref(v_fn_2640_);
lean_inc_ref(v_f_2482_);
v___x_2642_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2482_, v_fn_2640_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_);
if (lean_obj_tag(v___x_2642_) == 0)
{
lean_object* v_a_2643_; lean_object* v_fst_2644_; lean_object* v_snd_2645_; lean_object* v___x_2646_; 
v_a_2643_ = lean_ctor_get(v___x_2642_, 0);
lean_inc(v_a_2643_);
lean_dec_ref_known(v___x_2642_, 1);
v_fst_2644_ = lean_ctor_get(v_a_2643_, 0);
lean_inc(v_fst_2644_);
v_snd_2645_ = lean_ctor_get(v_a_2643_, 1);
lean_inc(v_snd_2645_);
lean_dec(v_a_2643_);
lean_inc_ref(v_arg_2641_);
v___x_2646_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2482_, v_arg_2641_, v_snd_2645_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_);
if (lean_obj_tag(v___x_2646_) == 0)
{
lean_object* v_a_2647_; lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2674_; 
v_a_2647_ = lean_ctor_get(v___x_2646_, 0);
v_isSharedCheck_2674_ = !lean_is_exclusive(v___x_2646_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2649_ = v___x_2646_;
v_isShared_2650_ = v_isSharedCheck_2674_;
goto v_resetjp_2648_;
}
else
{
lean_inc(v_a_2647_);
lean_dec(v___x_2646_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2674_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
lean_object* v_fst_2651_; lean_object* v_snd_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2673_; 
v_fst_2651_ = lean_ctor_get(v_a_2647_, 0);
v_snd_2652_ = lean_ctor_get(v_a_2647_, 1);
v_isSharedCheck_2673_ = !lean_is_exclusive(v_a_2647_);
if (v_isSharedCheck_2673_ == 0)
{
v___x_2654_ = v_a_2647_;
v_isShared_2655_ = v_isSharedCheck_2673_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_snd_2652_);
lean_inc(v_fst_2651_);
lean_dec(v_a_2647_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2673_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v___y_2657_; uint8_t v___y_2665_; size_t v___x_2667_; size_t v___x_2668_; uint8_t v___x_2669_; 
v___x_2667_ = lean_ptr_addr(v_fn_2640_);
v___x_2668_ = lean_ptr_addr(v_fst_2644_);
v___x_2669_ = lean_usize_dec_eq(v___x_2667_, v___x_2668_);
if (v___x_2669_ == 0)
{
v___y_2665_ = v___x_2669_;
goto v___jp_2664_;
}
else
{
size_t v___x_2670_; size_t v___x_2671_; uint8_t v___x_2672_; 
v___x_2670_ = lean_ptr_addr(v_arg_2641_);
v___x_2671_ = lean_ptr_addr(v_fst_2651_);
v___x_2672_ = lean_usize_dec_eq(v___x_2670_, v___x_2671_);
v___y_2665_ = v___x_2672_;
goto v___jp_2664_;
}
v___jp_2656_:
{
lean_object* v___x_2659_; 
if (v_isShared_2655_ == 0)
{
lean_ctor_set(v___x_2654_, 0, v___y_2657_);
v___x_2659_ = v___x_2654_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v___y_2657_);
lean_ctor_set(v_reuseFailAlloc_2663_, 1, v_snd_2652_);
v___x_2659_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
lean_object* v___x_2661_; 
if (v_isShared_2650_ == 0)
{
lean_ctor_set(v___x_2649_, 0, v___x_2659_);
v___x_2661_ = v___x_2649_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v___x_2659_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
return v___x_2661_;
}
}
}
v___jp_2664_:
{
if (v___y_2665_ == 0)
{
lean_object* v___x_2666_; 
lean_dec_ref_known(v_x_2483_, 2);
v___x_2666_ = l_Lean_Expr_app___override(v_fst_2644_, v_fst_2651_);
v___y_2657_ = v___x_2666_;
goto v___jp_2656_;
}
else
{
lean_dec(v_fst_2651_);
lean_dec(v_fst_2644_);
v___y_2657_ = v_x_2483_;
goto v___jp_2656_;
}
}
}
}
}
else
{
lean_dec(v_fst_2644_);
lean_dec_ref_known(v_x_2483_, 2);
return v___x_2646_;
}
}
else
{
lean_dec_ref_known(v_x_2483_, 2);
lean_dec_ref(v_f_2482_);
return v___x_2642_;
}
}
case 11:
{
lean_object* v_typeName_2675_; lean_object* v_idx_2676_; lean_object* v_struct_2677_; lean_object* v___x_2678_; 
v_typeName_2675_ = lean_ctor_get(v_x_2483_, 0);
v_idx_2676_ = lean_ctor_get(v_x_2483_, 1);
v_struct_2677_ = lean_ctor_get(v_x_2483_, 2);
lean_inc_ref(v_struct_2677_);
v___x_2678_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2482_, v_struct_2677_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_);
if (lean_obj_tag(v___x_2678_) == 0)
{
lean_object* v_a_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2701_; 
v_a_2679_ = lean_ctor_get(v___x_2678_, 0);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___x_2678_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2681_ = v___x_2678_;
v_isShared_2682_ = v_isSharedCheck_2701_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_a_2679_);
lean_dec(v___x_2678_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2701_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v_fst_2683_; lean_object* v_snd_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2700_; 
v_fst_2683_ = lean_ctor_get(v_a_2679_, 0);
v_snd_2684_ = lean_ctor_get(v_a_2679_, 1);
v_isSharedCheck_2700_ = !lean_is_exclusive(v_a_2679_);
if (v_isSharedCheck_2700_ == 0)
{
v___x_2686_ = v_a_2679_;
v_isShared_2687_ = v_isSharedCheck_2700_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_snd_2684_);
lean_inc(v_fst_2683_);
lean_dec(v_a_2679_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2700_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v___y_2689_; size_t v___x_2696_; size_t v___x_2697_; uint8_t v___x_2698_; 
v___x_2696_ = lean_ptr_addr(v_struct_2677_);
v___x_2697_ = lean_ptr_addr(v_fst_2683_);
v___x_2698_ = lean_usize_dec_eq(v___x_2696_, v___x_2697_);
if (v___x_2698_ == 0)
{
lean_object* v___x_2699_; 
lean_inc(v_idx_2676_);
lean_inc(v_typeName_2675_);
lean_dec_ref_known(v_x_2483_, 3);
v___x_2699_ = l_Lean_Expr_proj___override(v_typeName_2675_, v_idx_2676_, v_fst_2683_);
v___y_2689_ = v___x_2699_;
goto v___jp_2688_;
}
else
{
lean_dec(v_fst_2683_);
v___y_2689_ = v_x_2483_;
goto v___jp_2688_;
}
v___jp_2688_:
{
lean_object* v___x_2691_; 
if (v_isShared_2687_ == 0)
{
lean_ctor_set(v___x_2686_, 0, v___y_2689_);
v___x_2691_ = v___x_2686_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v___y_2689_);
lean_ctor_set(v_reuseFailAlloc_2695_, 1, v_snd_2684_);
v___x_2691_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
lean_object* v___x_2693_; 
if (v_isShared_2682_ == 0)
{
lean_ctor_set(v___x_2681_, 0, v___x_2691_);
v___x_2693_ = v___x_2681_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v___x_2691_);
v___x_2693_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
return v___x_2693_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_x_2483_, 3);
return v___x_2678_;
}
}
default: 
{
lean_object* v___x_2702_; lean_object* v___x_2703_; 
lean_dec_ref(v_f_2482_);
v___x_2702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2702_, 0, v_x_2483_);
lean_ctor_set(v___x_2702_, 1, v___y_2484_);
v___x_2703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2702_);
return v___x_2703_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___boxed(lean_object* v_f_2704_, lean_object* v_x_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_){
_start:
{
lean_object* v_res_2712_; 
v_res_2712_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg(v_f_2704_, v_x_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_);
lean_dec(v___y_2710_);
lean_dec_ref(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
return v_res_2712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg(lean_object* v_f_2713_, lean_object* v_init_2714_, lean_object* v_e_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_){
_start:
{
lean_object* v___x_2721_; 
v___x_2721_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg(v_f_2713_, v_e_2715_, v_init_2714_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_);
if (lean_obj_tag(v___x_2721_) == 0)
{
lean_object* v_a_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2730_; 
v_a_2722_ = lean_ctor_get(v___x_2721_, 0);
v_isSharedCheck_2730_ = !lean_is_exclusive(v___x_2721_);
if (v_isSharedCheck_2730_ == 0)
{
v___x_2724_ = v___x_2721_;
v_isShared_2725_ = v_isSharedCheck_2730_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_a_2722_);
lean_dec(v___x_2721_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2730_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v_snd_2726_; lean_object* v___x_2728_; 
v_snd_2726_ = lean_ctor_get(v_a_2722_, 1);
lean_inc(v_snd_2726_);
lean_dec(v_a_2722_);
if (v_isShared_2725_ == 0)
{
lean_ctor_set(v___x_2724_, 0, v_snd_2726_);
v___x_2728_ = v___x_2724_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v_snd_2726_);
v___x_2728_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
return v___x_2728_;
}
}
}
else
{
lean_object* v_a_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2738_; 
v_a_2731_ = lean_ctor_get(v___x_2721_, 0);
v_isSharedCheck_2738_ = !lean_is_exclusive(v___x_2721_);
if (v_isSharedCheck_2738_ == 0)
{
v___x_2733_ = v___x_2721_;
v_isShared_2734_ = v_isSharedCheck_2738_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_a_2731_);
lean_dec(v___x_2721_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2738_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v___x_2736_; 
if (v_isShared_2734_ == 0)
{
v___x_2736_ = v___x_2733_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v_a_2731_);
v___x_2736_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
return v___x_2736_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg___boxed(lean_object* v_f_2739_, lean_object* v_init_2740_, lean_object* v_e_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_){
_start:
{
lean_object* v_res_2747_; 
v_res_2747_ = l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg(v_f_2739_, v_init_2740_, v_e_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
return v_res_2747_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(lean_object* v_op_2750_, lean_object* v_as_2751_, size_t v_i_2752_, size_t v_stop_2753_, lean_object* v_b_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_){
_start:
{
lean_object* v_a_2761_; uint8_t v___x_2765_; 
v___x_2765_ = lean_usize_dec_eq(v_i_2752_, v_stop_2753_);
if (v___x_2765_ == 0)
{
lean_object* v___x_2766_; lean_object* v___x_2767_; 
v___x_2766_ = lean_array_uget_borrowed(v_as_2751_, v_i_2752_);
lean_inc(v___y_2758_);
lean_inc_ref(v___y_2757_);
lean_inc(v___y_2756_);
lean_inc_ref(v___y_2755_);
lean_inc(v___x_2766_);
v___x_2767_ = lean_infer_type(v___x_2766_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_);
if (lean_obj_tag(v___x_2767_) == 0)
{
lean_object* v_a_2768_; lean_object* v___x_2769_; 
v_a_2768_ = lean_ctor_get(v___x_2767_, 0);
lean_inc(v_a_2768_);
lean_dec_ref_known(v___x_2767_, 1);
lean_inc_ref(v_op_2750_);
v___x_2769_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v_op_2750_, v_a_2768_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_);
if (lean_obj_tag(v___x_2769_) == 0)
{
lean_object* v_a_2770_; lean_object* v___x_2771_; 
v_a_2770_ = lean_ctor_get(v___x_2769_, 0);
lean_inc(v_a_2770_);
lean_dec_ref_known(v___x_2769_, 1);
v___x_2771_ = l_Array_append___redArg(v_b_2754_, v_a_2770_);
lean_dec(v_a_2770_);
v_a_2761_ = v___x_2771_;
goto v___jp_2760_;
}
else
{
lean_dec_ref(v_b_2754_);
if (lean_obj_tag(v___x_2769_) == 0)
{
lean_object* v_a_2772_; 
v_a_2772_ = lean_ctor_get(v___x_2769_, 0);
lean_inc(v_a_2772_);
lean_dec_ref_known(v___x_2769_, 1);
v_a_2761_ = v_a_2772_;
goto v___jp_2760_;
}
else
{
lean_dec_ref(v_op_2750_);
return v___x_2769_;
}
}
}
else
{
lean_object* v_a_2773_; lean_object* v___x_2775_; uint8_t v_isShared_2776_; uint8_t v_isSharedCheck_2780_; 
lean_dec_ref(v_b_2754_);
lean_dec_ref(v_op_2750_);
v_a_2773_ = lean_ctor_get(v___x_2767_, 0);
v_isSharedCheck_2780_ = !lean_is_exclusive(v___x_2767_);
if (v_isSharedCheck_2780_ == 0)
{
v___x_2775_ = v___x_2767_;
v_isShared_2776_ = v_isSharedCheck_2780_;
goto v_resetjp_2774_;
}
else
{
lean_inc(v_a_2773_);
lean_dec(v___x_2767_);
v___x_2775_ = lean_box(0);
v_isShared_2776_ = v_isSharedCheck_2780_;
goto v_resetjp_2774_;
}
v_resetjp_2774_:
{
lean_object* v___x_2778_; 
if (v_isShared_2776_ == 0)
{
v___x_2778_ = v___x_2775_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v_a_2773_);
v___x_2778_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
return v___x_2778_;
}
}
}
}
else
{
lean_object* v___x_2781_; 
lean_dec_ref(v_op_2750_);
v___x_2781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2781_, 0, v_b_2754_);
return v___x_2781_;
}
v___jp_2760_:
{
size_t v___x_2762_; size_t v___x_2763_; 
v___x_2762_ = ((size_t)1ULL);
v___x_2763_ = lean_usize_add(v_i_2752_, v___x_2762_);
v_i_2752_ = v___x_2763_;
v_b_2754_ = v_a_2761_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0(lean_object* v_op_2782_, lean_object* v_args_2783_, lean_object* v_body_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_){
_start:
{
lean_object* v___x_2790_; 
lean_inc_ref(v_op_2782_);
v___x_2790_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v_op_2782_, v_body_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_);
if (lean_obj_tag(v___x_2790_) == 0)
{
lean_object* v_a_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2812_; 
v_a_2791_ = lean_ctor_get(v___x_2790_, 0);
v_isSharedCheck_2812_ = !lean_is_exclusive(v___x_2790_);
if (v_isSharedCheck_2812_ == 0)
{
v___x_2793_ = v___x_2790_;
v_isShared_2794_ = v_isSharedCheck_2812_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_a_2791_);
lean_dec(v___x_2790_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2812_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; uint8_t v___x_2798_; 
v___x_2795_ = l_Array_reverse___redArg(v_a_2791_);
v___x_2796_ = lean_unsigned_to_nat(0u);
v___x_2797_ = lean_array_get_size(v_args_2783_);
v___x_2798_ = lean_nat_dec_lt(v___x_2796_, v___x_2797_);
if (v___x_2798_ == 0)
{
lean_object* v___x_2800_; 
lean_dec_ref(v_op_2782_);
if (v_isShared_2794_ == 0)
{
lean_ctor_set(v___x_2793_, 0, v___x_2795_);
v___x_2800_ = v___x_2793_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v___x_2795_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
return v___x_2800_;
}
}
else
{
uint8_t v___x_2802_; 
v___x_2802_ = lean_nat_dec_le(v___x_2797_, v___x_2797_);
if (v___x_2802_ == 0)
{
if (v___x_2798_ == 0)
{
lean_object* v___x_2804_; 
lean_dec_ref(v_op_2782_);
if (v_isShared_2794_ == 0)
{
lean_ctor_set(v___x_2793_, 0, v___x_2795_);
v___x_2804_ = v___x_2793_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v___x_2795_);
v___x_2804_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
return v___x_2804_;
}
}
else
{
size_t v___x_2806_; size_t v___x_2807_; lean_object* v___x_2808_; 
lean_del_object(v___x_2793_);
v___x_2806_ = ((size_t)0ULL);
v___x_2807_ = lean_usize_of_nat(v___x_2797_);
v___x_2808_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(v_op_2782_, v_args_2783_, v___x_2806_, v___x_2807_, v___x_2795_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_);
return v___x_2808_;
}
}
else
{
size_t v___x_2809_; size_t v___x_2810_; lean_object* v___x_2811_; 
lean_del_object(v___x_2793_);
v___x_2809_ = ((size_t)0ULL);
v___x_2810_ = lean_usize_of_nat(v___x_2797_);
v___x_2811_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(v_op_2782_, v_args_2783_, v___x_2809_, v___x_2810_, v___x_2795_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_);
return v___x_2811_;
}
}
}
}
else
{
lean_dec_ref(v_op_2782_);
return v___x_2790_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed(lean_object* v_op_2813_, lean_object* v_args_2814_, lean_object* v_body_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_){
_start:
{
lean_object* v_res_2821_; 
v_res_2821_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0(v_op_2813_, v_args_2814_, v_body_2815_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_);
lean_dec(v___y_2819_);
lean_dec_ref(v___y_2818_);
lean_dec(v___y_2817_);
lean_dec_ref(v___y_2816_);
lean_dec_ref(v_args_2814_);
return v_res_2821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3___boxed(lean_object* v_op_2822_, lean_object* v_a_2823_, lean_object* v_f_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_){
_start:
{
lean_object* v_res_2830_; 
v_res_2830_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3(v_op_2822_, v_a_2823_, v_f_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2827_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2825_);
return v_res_2830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(lean_object* v_op_2831_, lean_object* v_e_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_){
_start:
{
switch(lean_obj_tag(v_e_2832_))
{
case 0:
{
lean_object* v___x_2838_; lean_object* v___x_2839_; 
lean_dec_ref_known(v_e_2832_, 1);
lean_dec_ref(v_op_2831_);
v___x_2838_ = ((lean_object*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___closed__0));
v___x_2839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2839_, 0, v___x_2838_);
return v___x_2839_;
}
case 7:
{
lean_object* v___f_2840_; uint8_t v___x_2841_; lean_object* v___x_2842_; 
v___f_2840_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2840_, 0, v_op_2831_);
v___x_2841_ = 0;
v___x_2842_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(v_e_2832_, v___f_2840_, v___x_2841_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_);
return v___x_2842_;
}
case 6:
{
lean_object* v___f_2843_; uint8_t v___x_2844_; uint8_t v___x_2845_; lean_object* v___x_2846_; 
v___f_2843_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2843_, 0, v_op_2831_);
v___x_2844_ = 0;
v___x_2845_ = 1;
v___x_2846_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(v_e_2832_, v___f_2843_, v___x_2844_, v___x_2845_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_);
return v___x_2846_;
}
case 8:
{
lean_object* v___f_2847_; uint8_t v___x_2848_; uint8_t v___x_2849_; lean_object* v___x_2850_; 
v___f_2847_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2847_, 0, v_op_2831_);
v___x_2848_ = 0;
v___x_2849_ = 1;
v___x_2850_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(v_e_2832_, v___f_2847_, v___x_2848_, v___x_2849_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_);
return v___x_2850_;
}
default: 
{
lean_object* v___x_2851_; 
lean_inc_ref(v_op_2831_);
lean_inc(v_a_2836_);
lean_inc_ref(v_a_2835_);
lean_inc(v_a_2834_);
lean_inc_ref(v_a_2833_);
lean_inc_ref(v_e_2832_);
v___x_2851_ = lean_apply_6(v_op_2831_, v_e_2832_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_, lean_box(0));
if (lean_obj_tag(v___x_2851_) == 0)
{
lean_object* v_a_2852_; lean_object* v___f_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; 
v_a_2852_ = lean_ctor_get(v___x_2851_, 0);
lean_inc(v_a_2852_);
lean_dec_ref_known(v___x_2851_, 1);
v___f_2853_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3___boxed), 8, 1);
lean_closure_set(v___f_2853_, 0, v_op_2831_);
v___x_2854_ = l_Array_reverse___redArg(v_a_2852_);
v___x_2855_ = l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg(v___f_2853_, v___x_2854_, v_e_2832_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_);
return v___x_2855_;
}
else
{
lean_dec_ref(v_e_2832_);
lean_dec_ref(v_op_2831_);
return v___x_2851_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3(lean_object* v_op_2856_, lean_object* v_a_2857_, lean_object* v_f_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_){
_start:
{
lean_object* v___x_2864_; 
v___x_2864_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v_op_2856_, v_f_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_);
if (lean_obj_tag(v___x_2864_) == 0)
{
lean_object* v_a_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2873_; 
v_a_2865_ = lean_ctor_get(v___x_2864_, 0);
v_isSharedCheck_2873_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2867_ = v___x_2864_;
v_isShared_2868_ = v_isSharedCheck_2873_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_a_2865_);
lean_dec(v___x_2864_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2873_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
lean_object* v___x_2869_; lean_object* v___x_2871_; 
v___x_2869_ = l_Array_append___redArg(v_a_2857_, v_a_2865_);
lean_dec(v_a_2865_);
if (v_isShared_2868_ == 0)
{
lean_ctor_set(v___x_2867_, 0, v___x_2869_);
v___x_2871_ = v___x_2867_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v___x_2869_);
v___x_2871_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
return v___x_2871_;
}
}
}
else
{
lean_dec_ref(v_a_2857_);
return v___x_2864_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg___boxed(lean_object* v_op_2874_, lean_object* v_as_2875_, lean_object* v_i_2876_, lean_object* v_stop_2877_, lean_object* v_b_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_){
_start:
{
size_t v_i_boxed_2884_; size_t v_stop_boxed_2885_; lean_object* v_res_2886_; 
v_i_boxed_2884_ = lean_unbox_usize(v_i_2876_);
lean_dec(v_i_2876_);
v_stop_boxed_2885_ = lean_unbox_usize(v_stop_2877_);
lean_dec(v_stop_2877_);
v_res_2886_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(v_op_2874_, v_as_2875_, v_i_boxed_2884_, v_stop_boxed_2885_, v_b_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec_ref(v_as_2875_);
return v_res_2886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___boxed(lean_object* v_op_2887_, lean_object* v_e_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_){
_start:
{
lean_object* v_res_2894_; 
v_res_2894_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v_op_2887_, v_e_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_);
lean_dec(v_a_2892_);
lean_dec_ref(v_a_2891_);
lean_dec(v_a_2890_);
lean_dec_ref(v_a_2889_);
return v_res_2894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches(lean_object* v_00_u03b1_2895_, lean_object* v_op_2896_, lean_object* v_e_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_){
_start:
{
lean_object* v___x_2903_; 
v___x_2903_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v_op_2896_, v_e_2897_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_);
return v___x_2903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___boxed(lean_object* v_00_u03b1_2904_, lean_object* v_op_2905_, lean_object* v_e_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_){
_start:
{
lean_object* v_res_2912_; 
v_res_2912_ = l_Lean_Meta_Rewrites_getSubexpressionMatches(v_00_u03b1_2904_, v_op_2905_, v_e_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_);
lean_dec(v_a_2910_);
lean_dec_ref(v_a_2909_);
lean_dec(v_a_2908_);
lean_dec_ref(v_a_2907_);
return v_res_2912_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0(lean_object* v_00_u03b1_2913_, lean_object* v_op_2914_, lean_object* v_as_2915_, size_t v_i_2916_, size_t v_stop_2917_, lean_object* v_b_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_){
_start:
{
lean_object* v___x_2924_; 
v___x_2924_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(v_op_2914_, v_as_2915_, v_i_2916_, v_stop_2917_, v_b_2918_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_);
return v___x_2924_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___boxed(lean_object* v_00_u03b1_2925_, lean_object* v_op_2926_, lean_object* v_as_2927_, lean_object* v_i_2928_, lean_object* v_stop_2929_, lean_object* v_b_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_){
_start:
{
size_t v_i_boxed_2936_; size_t v_stop_boxed_2937_; lean_object* v_res_2938_; 
v_i_boxed_2936_ = lean_unbox_usize(v_i_2928_);
lean_dec(v_i_2928_);
v_stop_boxed_2937_ = lean_unbox_usize(v_stop_2929_);
lean_dec(v_stop_2929_);
v_res_2938_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0(v_00_u03b1_2925_, v_op_2926_, v_as_2927_, v_i_boxed_2936_, v_stop_boxed_2937_, v_b_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_);
lean_dec(v___y_2934_);
lean_dec_ref(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec_ref(v___y_2931_);
lean_dec_ref(v_as_2927_);
return v_res_2938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3(lean_object* v_00_u03b1_2939_, lean_object* v_f_2940_, lean_object* v_x_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_){
_start:
{
lean_object* v___x_2948_; 
v___x_2948_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg(v_f_2940_, v_x_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_);
return v___x_2948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___boxed(lean_object* v_00_u03b1_2949_, lean_object* v_f_2950_, lean_object* v_x_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_){
_start:
{
lean_object* v_res_2958_; 
v_res_2958_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3(v_00_u03b1_2949_, v_f_2950_, v_x_2951_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_);
lean_dec(v___y_2956_);
lean_dec_ref(v___y_2955_);
lean_dec(v___y_2954_);
lean_dec_ref(v___y_2953_);
return v_res_2958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3(lean_object* v_00_u03b1_2959_, lean_object* v_f_2960_, lean_object* v_init_2961_, lean_object* v_e_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_){
_start:
{
lean_object* v___x_2968_; 
v___x_2968_ = l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg(v_f_2960_, v_init_2961_, v_e_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_);
return v___x_2968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___boxed(lean_object* v_00_u03b1_2969_, lean_object* v_f_2970_, lean_object* v_init_2971_, lean_object* v_e_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_){
_start:
{
lean_object* v_res_2978_; 
v_res_2978_ = l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3(v_00_u03b1_2969_, v_f_2970_, v_init_2971_, v_e_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_);
lean_dec(v___y_2976_);
lean_dec_ref(v___y_2975_);
lean_dec(v___y_2974_);
lean_dec_ref(v___y_2973_);
return v_res_2978_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__3(size_t v_sz_2979_, size_t v_i_2980_, lean_object* v_bs_2981_){
_start:
{
uint8_t v___x_2982_; 
v___x_2982_ = lean_usize_dec_lt(v_i_2980_, v_sz_2979_);
if (v___x_2982_ == 0)
{
return v_bs_2981_;
}
else
{
lean_object* v_v_2983_; lean_object* v_fst_2984_; lean_object* v_snd_2985_; lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_2999_; 
v_v_2983_ = lean_array_uget(v_bs_2981_, v_i_2980_);
v_fst_2984_ = lean_ctor_get(v_v_2983_, 0);
v_snd_2985_ = lean_ctor_get(v_v_2983_, 1);
v_isSharedCheck_2999_ = !lean_is_exclusive(v_v_2983_);
if (v_isSharedCheck_2999_ == 0)
{
v___x_2987_ = v_v_2983_;
v_isShared_2988_ = v_isSharedCheck_2999_;
goto v_resetjp_2986_;
}
else
{
lean_inc(v_snd_2985_);
lean_inc(v_fst_2984_);
lean_dec(v_v_2983_);
v___x_2987_ = lean_box(0);
v_isShared_2988_ = v_isSharedCheck_2999_;
goto v_resetjp_2986_;
}
v_resetjp_2986_:
{
lean_object* v___x_2989_; lean_object* v_bs_x27_2990_; lean_object* v___x_2991_; lean_object* v___x_2993_; 
v___x_2989_ = lean_unsigned_to_nat(0u);
v_bs_x27_2990_ = lean_array_uset(v_bs_2981_, v_i_2980_, v___x_2989_);
v___x_2991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2991_, 0, v_fst_2984_);
if (v_isShared_2988_ == 0)
{
lean_ctor_set(v___x_2987_, 0, v___x_2991_);
v___x_2993_ = v___x_2987_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v___x_2991_);
lean_ctor_set(v_reuseFailAlloc_2998_, 1, v_snd_2985_);
v___x_2993_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
size_t v___x_2994_; size_t v___x_2995_; lean_object* v___x_2996_; 
v___x_2994_ = ((size_t)1ULL);
v___x_2995_ = lean_usize_add(v_i_2980_, v___x_2994_);
v___x_2996_ = lean_array_uset(v_bs_x27_2990_, v_i_2980_, v___x_2993_);
v_i_2980_ = v___x_2995_;
v_bs_2981_ = v___x_2996_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__3___boxed(lean_object* v_sz_3000_, lean_object* v_i_3001_, lean_object* v_bs_3002_){
_start:
{
size_t v_sz_boxed_3003_; size_t v_i_boxed_3004_; lean_object* v_res_3005_; 
v_sz_boxed_3003_ = lean_unbox_usize(v_sz_3000_);
lean_dec(v_sz_3000_);
v_i_boxed_3004_ = lean_unbox_usize(v_i_3001_);
lean_dec(v_i_3001_);
v_res_3005_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__3(v_sz_boxed_3003_, v_i_boxed_3004_, v_bs_3002_);
return v_res_3005_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0___redArg(lean_object* v_xs_3006_, lean_object* v_j_3007_){
_start:
{
lean_object* v_zero_3008_; uint8_t v_isZero_3009_; 
v_zero_3008_ = lean_unsigned_to_nat(0u);
v_isZero_3009_ = lean_nat_dec_eq(v_j_3007_, v_zero_3008_);
if (v_isZero_3009_ == 1)
{
lean_dec(v_j_3007_);
return v_xs_3006_;
}
else
{
lean_object* v___x_3010_; lean_object* v_snd_3011_; lean_object* v_snd_3012_; lean_object* v_one_3013_; lean_object* v_n_3014_; lean_object* v___x_3015_; lean_object* v_snd_3016_; lean_object* v_snd_3017_; uint8_t v___x_3018_; 
v___x_3010_ = lean_array_fget_borrowed(v_xs_3006_, v_j_3007_);
v_snd_3011_ = lean_ctor_get(v___x_3010_, 1);
v_snd_3012_ = lean_ctor_get(v_snd_3011_, 1);
v_one_3013_ = lean_unsigned_to_nat(1u);
v_n_3014_ = lean_nat_sub(v_j_3007_, v_one_3013_);
v___x_3015_ = lean_array_fget_borrowed(v_xs_3006_, v_n_3014_);
v_snd_3016_ = lean_ctor_get(v___x_3015_, 1);
v_snd_3017_ = lean_ctor_get(v_snd_3016_, 1);
v___x_3018_ = lean_nat_dec_lt(v_snd_3017_, v_snd_3012_);
if (v___x_3018_ == 0)
{
lean_dec(v_n_3014_);
lean_dec(v_j_3007_);
return v_xs_3006_;
}
else
{
lean_object* v___x_3019_; 
v___x_3019_ = lean_array_fswap(v_xs_3006_, v_j_3007_, v_n_3014_);
lean_dec(v_j_3007_);
v_xs_3006_ = v___x_3019_;
v_j_3007_ = v_n_3014_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0(lean_object* v_xs_3021_, lean_object* v_i_3022_, lean_object* v_fuel_3023_){
_start:
{
lean_object* v_zero_3024_; uint8_t v_isZero_3025_; 
v_zero_3024_ = lean_unsigned_to_nat(0u);
v_isZero_3025_ = lean_nat_dec_eq(v_fuel_3023_, v_zero_3024_);
if (v_isZero_3025_ == 1)
{
lean_dec(v_fuel_3023_);
lean_dec(v_i_3022_);
return v_xs_3021_;
}
else
{
lean_object* v___x_3026_; uint8_t v___x_3027_; 
v___x_3026_ = lean_array_get_size(v_xs_3021_);
v___x_3027_ = lean_nat_dec_lt(v_i_3022_, v___x_3026_);
if (v___x_3027_ == 0)
{
lean_dec(v_fuel_3023_);
lean_dec(v_i_3022_);
return v_xs_3021_;
}
else
{
lean_object* v_one_3028_; lean_object* v_n_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; 
v_one_3028_ = lean_unsigned_to_nat(1u);
v_n_3029_ = lean_nat_sub(v_fuel_3023_, v_one_3028_);
lean_dec(v_fuel_3023_);
lean_inc(v_i_3022_);
v___x_3030_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0___redArg(v_xs_3021_, v_i_3022_);
v___x_3031_ = lean_nat_add(v_i_3022_, v_one_3028_);
lean_dec(v_i_3022_);
v_xs_3021_ = v___x_3030_;
v_i_3022_ = v___x_3031_;
v_fuel_3023_ = v_n_3029_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__2(size_t v_sz_3033_, size_t v_i_3034_, lean_object* v_bs_3035_){
_start:
{
uint8_t v___x_3036_; 
v___x_3036_ = lean_usize_dec_lt(v_i_3034_, v_sz_3033_);
if (v___x_3036_ == 0)
{
return v_bs_3035_;
}
else
{
lean_object* v_v_3037_; lean_object* v_fst_3038_; lean_object* v_snd_3039_; lean_object* v___x_3041_; uint8_t v_isShared_3042_; uint8_t v_isSharedCheck_3053_; 
v_v_3037_ = lean_array_uget(v_bs_3035_, v_i_3034_);
v_fst_3038_ = lean_ctor_get(v_v_3037_, 0);
v_snd_3039_ = lean_ctor_get(v_v_3037_, 1);
v_isSharedCheck_3053_ = !lean_is_exclusive(v_v_3037_);
if (v_isSharedCheck_3053_ == 0)
{
v___x_3041_ = v_v_3037_;
v_isShared_3042_ = v_isSharedCheck_3053_;
goto v_resetjp_3040_;
}
else
{
lean_inc(v_snd_3039_);
lean_inc(v_fst_3038_);
lean_dec(v_v_3037_);
v___x_3041_ = lean_box(0);
v_isShared_3042_ = v_isSharedCheck_3053_;
goto v_resetjp_3040_;
}
v_resetjp_3040_:
{
lean_object* v___x_3043_; lean_object* v_bs_x27_3044_; lean_object* v___x_3045_; lean_object* v___x_3047_; 
v___x_3043_ = lean_unsigned_to_nat(0u);
v_bs_x27_3044_ = lean_array_uset(v_bs_3035_, v_i_3034_, v___x_3043_);
v___x_3045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3045_, 0, v_fst_3038_);
if (v_isShared_3042_ == 0)
{
lean_ctor_set(v___x_3041_, 0, v___x_3045_);
v___x_3047_ = v___x_3041_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v___x_3045_);
lean_ctor_set(v_reuseFailAlloc_3052_, 1, v_snd_3039_);
v___x_3047_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
size_t v___x_3048_; size_t v___x_3049_; lean_object* v___x_3050_; 
v___x_3048_ = ((size_t)1ULL);
v___x_3049_ = lean_usize_add(v_i_3034_, v___x_3048_);
v___x_3050_ = lean_array_uset(v_bs_x27_3044_, v_i_3034_, v___x_3047_);
v_i_3034_ = v___x_3049_;
v_bs_3035_ = v___x_3050_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__2___boxed(lean_object* v_sz_3054_, lean_object* v_i_3055_, lean_object* v_bs_3056_){
_start:
{
size_t v_sz_boxed_3057_; size_t v_i_boxed_3058_; lean_object* v_res_3059_; 
v_sz_boxed_3057_ = lean_unbox_usize(v_sz_3054_);
lean_dec(v_sz_3054_);
v_i_boxed_3058_ = lean_unbox_usize(v_i_3055_);
lean_dec(v_i_3055_);
v_res_3059_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__2(v_sz_boxed_3057_, v_i_boxed_3058_, v_bs_3056_);
return v_res_3059_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg(lean_object* v_forbidden_3060_, lean_object* v_as_3061_, size_t v_sz_3062_, size_t v_i_3063_, lean_object* v_b_3064_){
_start:
{
lean_object* v_a_3067_; uint8_t v___x_3071_; 
v___x_3071_ = lean_usize_dec_lt(v_i_3063_, v_sz_3062_);
if (v___x_3071_ == 0)
{
lean_object* v___x_3072_; 
v___x_3072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3072_, 0, v_b_3064_);
return v___x_3072_;
}
else
{
lean_object* v_a_3073_; lean_object* v_snd_3074_; lean_object* v_snd_3075_; lean_object* v_fst_3076_; lean_object* v_fst_3077_; lean_object* v___x_3079_; uint8_t v_isShared_3080_; uint8_t v_isSharedCheck_3127_; 
v_a_3073_ = lean_array_uget(v_as_3061_, v_i_3063_);
v_snd_3074_ = lean_ctor_get(v_a_3073_, 1);
lean_inc(v_snd_3074_);
v_snd_3075_ = lean_ctor_get(v_b_3064_, 1);
lean_inc(v_snd_3075_);
v_fst_3076_ = lean_ctor_get(v_a_3073_, 0);
v_fst_3077_ = lean_ctor_get(v_snd_3074_, 0);
v_isSharedCheck_3127_ = !lean_is_exclusive(v_snd_3074_);
if (v_isSharedCheck_3127_ == 0)
{
lean_object* v_unused_3128_; 
v_unused_3128_ = lean_ctor_get(v_snd_3074_, 1);
lean_dec(v_unused_3128_);
v___x_3079_ = v_snd_3074_;
v_isShared_3080_ = v_isSharedCheck_3127_;
goto v_resetjp_3078_;
}
else
{
lean_inc(v_fst_3077_);
lean_dec(v_snd_3074_);
v___x_3079_ = lean_box(0);
v_isShared_3080_ = v_isSharedCheck_3127_;
goto v_resetjp_3078_;
}
v_resetjp_3078_:
{
lean_object* v_fst_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3125_; 
v_fst_3081_ = lean_ctor_get(v_b_3064_, 0);
v_isSharedCheck_3125_ = !lean_is_exclusive(v_b_3064_);
if (v_isSharedCheck_3125_ == 0)
{
lean_object* v_unused_3126_; 
v_unused_3126_ = lean_ctor_get(v_b_3064_, 1);
lean_dec(v_unused_3126_);
v___x_3083_ = v_b_3064_;
v_isShared_3084_ = v_isSharedCheck_3125_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_fst_3081_);
lean_dec(v_b_3064_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3125_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v_fst_3085_; lean_object* v_snd_3086_; lean_object* v___x_3088_; uint8_t v_isShared_3089_; uint8_t v_isSharedCheck_3124_; 
v_fst_3085_ = lean_ctor_get(v_snd_3075_, 0);
v_snd_3086_ = lean_ctor_get(v_snd_3075_, 1);
v_isSharedCheck_3124_ = !lean_is_exclusive(v_snd_3075_);
if (v_isSharedCheck_3124_ == 0)
{
v___x_3088_ = v_snd_3075_;
v_isShared_3089_ = v_isSharedCheck_3124_;
goto v_resetjp_3087_;
}
else
{
lean_inc(v_snd_3086_);
lean_inc(v_fst_3085_);
lean_dec(v_snd_3075_);
v___x_3088_ = lean_box(0);
v_isShared_3089_ = v_isSharedCheck_3124_;
goto v_resetjp_3087_;
}
v_resetjp_3087_:
{
uint8_t v___x_3102_; 
v___x_3102_ = l_Lean_NameSet_contains(v_forbidden_3060_, v_fst_3076_);
if (v___x_3102_ == 0)
{
uint8_t v___x_3103_; 
lean_inc(v_fst_3076_);
v___x_3103_ = lean_unbox(v_fst_3077_);
lean_dec(v_fst_3077_);
if (v___x_3103_ == 0)
{
uint8_t v___x_3104_; 
lean_del_object(v___x_3088_);
lean_del_object(v___x_3083_);
v___x_3104_ = l_Lean_NameSet_contains(v_fst_3081_, v_fst_3076_);
if (v___x_3104_ == 0)
{
if (v___x_3071_ == 0)
{
lean_dec(v_fst_3076_);
lean_dec(v_a_3073_);
goto v___jp_3097_;
}
else
{
lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; 
lean_del_object(v___x_3079_);
v___x_3105_ = lean_array_push(v_snd_3086_, v_a_3073_);
v___x_3106_ = l_Lean_NameSet_insert(v_fst_3081_, v_fst_3076_);
v___x_3107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3107_, 0, v_fst_3085_);
lean_ctor_set(v___x_3107_, 1, v___x_3105_);
v___x_3108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3108_, 0, v___x_3106_);
lean_ctor_set(v___x_3108_, 1, v___x_3107_);
v_a_3067_ = v___x_3108_;
goto v___jp_3066_;
}
}
else
{
lean_dec(v_fst_3076_);
lean_dec(v_a_3073_);
goto v___jp_3097_;
}
}
else
{
uint8_t v___x_3109_; 
lean_del_object(v___x_3079_);
v___x_3109_ = l_Lean_NameSet_contains(v_fst_3085_, v_fst_3076_);
if (v___x_3109_ == 0)
{
if (v___x_3071_ == 0)
{
lean_dec(v_fst_3076_);
lean_dec(v_a_3073_);
goto v___jp_3090_;
}
else
{
lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; 
lean_del_object(v___x_3088_);
lean_del_object(v___x_3083_);
v___x_3110_ = lean_array_push(v_snd_3086_, v_a_3073_);
v___x_3111_ = l_Lean_NameSet_insert(v_fst_3085_, v_fst_3076_);
v___x_3112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3112_, 0, v___x_3111_);
lean_ctor_set(v___x_3112_, 1, v___x_3110_);
v___x_3113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3113_, 0, v_fst_3081_);
lean_ctor_set(v___x_3113_, 1, v___x_3112_);
v_a_3067_ = v___x_3113_;
goto v___jp_3066_;
}
}
else
{
lean_dec(v_fst_3076_);
lean_dec(v_a_3073_);
goto v___jp_3090_;
}
}
}
else
{
lean_object* v___x_3115_; uint8_t v_isShared_3116_; uint8_t v_isSharedCheck_3121_; 
lean_del_object(v___x_3088_);
lean_del_object(v___x_3083_);
lean_del_object(v___x_3079_);
lean_dec(v_fst_3077_);
v_isSharedCheck_3121_ = !lean_is_exclusive(v_a_3073_);
if (v_isSharedCheck_3121_ == 0)
{
lean_object* v_unused_3122_; lean_object* v_unused_3123_; 
v_unused_3122_ = lean_ctor_get(v_a_3073_, 1);
lean_dec(v_unused_3122_);
v_unused_3123_ = lean_ctor_get(v_a_3073_, 0);
lean_dec(v_unused_3123_);
v___x_3115_ = v_a_3073_;
v_isShared_3116_ = v_isSharedCheck_3121_;
goto v_resetjp_3114_;
}
else
{
lean_dec(v_a_3073_);
v___x_3115_ = lean_box(0);
v_isShared_3116_ = v_isSharedCheck_3121_;
goto v_resetjp_3114_;
}
v_resetjp_3114_:
{
lean_object* v___x_3118_; 
if (v_isShared_3116_ == 0)
{
lean_ctor_set(v___x_3115_, 1, v_snd_3086_);
lean_ctor_set(v___x_3115_, 0, v_fst_3085_);
v___x_3118_ = v___x_3115_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v_fst_3085_);
lean_ctor_set(v_reuseFailAlloc_3120_, 1, v_snd_3086_);
v___x_3118_ = v_reuseFailAlloc_3120_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
lean_object* v___x_3119_; 
v___x_3119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3119_, 0, v_fst_3081_);
lean_ctor_set(v___x_3119_, 1, v___x_3118_);
v_a_3067_ = v___x_3119_;
goto v___jp_3066_;
}
}
}
v___jp_3090_:
{
lean_object* v___x_3092_; 
if (v_isShared_3089_ == 0)
{
v___x_3092_ = v___x_3088_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3096_; 
v_reuseFailAlloc_3096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3096_, 0, v_fst_3085_);
lean_ctor_set(v_reuseFailAlloc_3096_, 1, v_snd_3086_);
v___x_3092_ = v_reuseFailAlloc_3096_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
lean_object* v___x_3094_; 
if (v_isShared_3084_ == 0)
{
lean_ctor_set(v___x_3083_, 1, v___x_3092_);
v___x_3094_ = v___x_3083_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v_fst_3081_);
lean_ctor_set(v_reuseFailAlloc_3095_, 1, v___x_3092_);
v___x_3094_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
v_a_3067_ = v___x_3094_;
goto v___jp_3066_;
}
}
}
v___jp_3097_:
{
lean_object* v___x_3099_; 
if (v_isShared_3080_ == 0)
{
lean_ctor_set(v___x_3079_, 1, v_snd_3086_);
lean_ctor_set(v___x_3079_, 0, v_fst_3085_);
v___x_3099_ = v___x_3079_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v_fst_3085_);
lean_ctor_set(v_reuseFailAlloc_3101_, 1, v_snd_3086_);
v___x_3099_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
lean_object* v___x_3100_; 
v___x_3100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3100_, 0, v_fst_3081_);
lean_ctor_set(v___x_3100_, 1, v___x_3099_);
v_a_3067_ = v___x_3100_;
goto v___jp_3066_;
}
}
}
}
}
}
v___jp_3066_:
{
size_t v___x_3068_; size_t v___x_3069_; 
v___x_3068_ = ((size_t)1ULL);
v___x_3069_ = lean_usize_add(v_i_3063_, v___x_3068_);
v_i_3063_ = v___x_3069_;
v_b_3064_ = v_a_3067_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg___boxed(lean_object* v_forbidden_3129_, lean_object* v_as_3130_, lean_object* v_sz_3131_, lean_object* v_i_3132_, lean_object* v_b_3133_, lean_object* v___y_3134_){
_start:
{
size_t v_sz_boxed_3135_; size_t v_i_boxed_3136_; lean_object* v_res_3137_; 
v_sz_boxed_3135_ = lean_unbox_usize(v_sz_3131_);
lean_dec(v_sz_3131_);
v_i_boxed_3136_ = lean_unbox_usize(v_i_3132_);
lean_dec(v_i_3132_);
v_res_3137_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg(v_forbidden_3129_, v_as_3130_, v_sz_boxed_3135_, v_i_boxed_3136_, v_b_3133_);
lean_dec_ref(v_as_3130_);
lean_dec(v_forbidden_3129_);
return v_res_3137_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__2(void){
_start:
{
lean_object* v___x_3141_; lean_object* v___x_3142_; 
v___x_3141_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__1));
v___x_3142_ = l_Lean_MessageData_ofFormat(v___x_3141_);
return v___x_3142_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__3(void){
_start:
{
lean_object* v___x_3143_; lean_object* v___x_3144_; 
v___x_3143_ = lean_box(1);
v___x_3144_ = l_Lean_MessageData_ofFormat(v___x_3143_);
return v___x_3144_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4(lean_object* v_a_3147_, lean_object* v_a_3148_){
_start:
{
if (lean_obj_tag(v_a_3147_) == 0)
{
lean_object* v___x_3149_; 
v___x_3149_ = l_List_reverse___redArg(v_a_3148_);
return v___x_3149_;
}
else
{
lean_object* v_head_3150_; lean_object* v_snd_3151_; lean_object* v_tail_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3197_; 
v_head_3150_ = lean_ctor_get(v_a_3147_, 0);
lean_inc(v_head_3150_);
v_snd_3151_ = lean_ctor_get(v_head_3150_, 1);
lean_inc(v_snd_3151_);
v_tail_3152_ = lean_ctor_get(v_a_3147_, 1);
v_isSharedCheck_3197_ = !lean_is_exclusive(v_a_3147_);
if (v_isSharedCheck_3197_ == 0)
{
lean_object* v_unused_3198_; 
v_unused_3198_ = lean_ctor_get(v_a_3147_, 0);
lean_dec(v_unused_3198_);
v___x_3154_ = v_a_3147_;
v_isShared_3155_ = v_isSharedCheck_3197_;
goto v_resetjp_3153_;
}
else
{
lean_inc(v_tail_3152_);
lean_dec(v_a_3147_);
v___x_3154_ = lean_box(0);
v_isShared_3155_ = v_isSharedCheck_3197_;
goto v_resetjp_3153_;
}
v_resetjp_3153_:
{
lean_object* v_fst_3156_; lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3195_; 
v_fst_3156_ = lean_ctor_get(v_head_3150_, 0);
v_isSharedCheck_3195_ = !lean_is_exclusive(v_head_3150_);
if (v_isSharedCheck_3195_ == 0)
{
lean_object* v_unused_3196_; 
v_unused_3196_ = lean_ctor_get(v_head_3150_, 1);
lean_dec(v_unused_3196_);
v___x_3158_ = v_head_3150_;
v_isShared_3159_ = v_isSharedCheck_3195_;
goto v_resetjp_3157_;
}
else
{
lean_inc(v_fst_3156_);
lean_dec(v_head_3150_);
v___x_3158_ = lean_box(0);
v_isShared_3159_ = v_isSharedCheck_3195_;
goto v_resetjp_3157_;
}
v_resetjp_3157_:
{
lean_object* v_fst_3160_; lean_object* v_snd_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3194_; 
v_fst_3160_ = lean_ctor_get(v_snd_3151_, 0);
v_snd_3161_ = lean_ctor_get(v_snd_3151_, 1);
v_isSharedCheck_3194_ = !lean_is_exclusive(v_snd_3151_);
if (v_isSharedCheck_3194_ == 0)
{
v___x_3163_ = v_snd_3151_;
v_isShared_3164_ = v_isSharedCheck_3194_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_snd_3161_);
lean_inc(v_fst_3160_);
lean_dec(v_snd_3151_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3194_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3168_; 
v___x_3165_ = l_Lean_MessageData_ofName(v_fst_3156_);
v___x_3166_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__2, &l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__2_once, _init_l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__2);
if (v_isShared_3164_ == 0)
{
lean_ctor_set_tag(v___x_3163_, 7);
lean_ctor_set(v___x_3163_, 1, v___x_3166_);
lean_ctor_set(v___x_3163_, 0, v___x_3165_);
v___x_3168_ = v___x_3163_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v___x_3165_);
lean_ctor_set(v_reuseFailAlloc_3193_, 1, v___x_3166_);
v___x_3168_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
lean_object* v___x_3169_; lean_object* v___x_3171_; 
v___x_3169_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__3, &l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__3_once, _init_l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__3);
if (v_isShared_3159_ == 0)
{
lean_ctor_set_tag(v___x_3158_, 7);
lean_ctor_set(v___x_3158_, 1, v___x_3169_);
lean_ctor_set(v___x_3158_, 0, v___x_3168_);
v___x_3171_ = v___x_3158_;
goto v_reusejp_3170_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v___x_3168_);
lean_ctor_set(v_reuseFailAlloc_3192_, 1, v___x_3169_);
v___x_3171_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3170_;
}
v_reusejp_3170_:
{
lean_object* v___y_3173_; uint8_t v___x_3189_; 
v___x_3189_ = lean_unbox(v_fst_3160_);
lean_dec(v_fst_3160_);
if (v___x_3189_ == 0)
{
lean_object* v___x_3190_; 
v___x_3190_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__4));
v___y_3173_ = v___x_3190_;
goto v___jp_3172_;
}
else
{
lean_object* v___x_3191_; 
v___x_3191_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__5));
v___y_3173_ = v___x_3191_;
goto v___jp_3172_;
}
v___jp_3172_:
{
lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3186_; 
lean_inc_ref(v___y_3173_);
v___x_3174_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3174_, 0, v___y_3173_);
v___x_3175_ = l_Lean_MessageData_ofFormat(v___x_3174_);
v___x_3176_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3176_, 0, v___x_3175_);
lean_ctor_set(v___x_3176_, 1, v___x_3166_);
v___x_3177_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3177_, 0, v___x_3176_);
lean_ctor_set(v___x_3177_, 1, v___x_3169_);
v___x_3178_ = l_Nat_reprFast(v_snd_3161_);
v___x_3179_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3179_, 0, v___x_3178_);
v___x_3180_ = l_Lean_MessageData_ofFormat(v___x_3179_);
v___x_3181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3181_, 0, v___x_3177_);
lean_ctor_set(v___x_3181_, 1, v___x_3180_);
v___x_3182_ = l_Lean_MessageData_paren(v___x_3181_);
v___x_3183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3171_);
lean_ctor_set(v___x_3183_, 1, v___x_3182_);
v___x_3184_ = l_Lean_MessageData_paren(v___x_3183_);
if (v_isShared_3155_ == 0)
{
lean_ctor_set(v___x_3154_, 1, v_a_3148_);
lean_ctor_set(v___x_3154_, 0, v___x_3184_);
v___x_3186_ = v___x_3154_;
goto v_reusejp_3185_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v___x_3184_);
lean_ctor_set(v_reuseFailAlloc_3188_, 1, v_a_3148_);
v___x_3186_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3185_;
}
v_reusejp_3185_:
{
v_a_3147_ = v_tail_3152_;
v_a_3148_ = v___x_3186_;
goto _start;
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
static lean_object* _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__1(void){
_start:
{
lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; 
v___x_3201_ = ((lean_object*)(l_Lean_Meta_Rewrites_rewriteCandidates___closed__0));
v___x_3202_ = l_Lean_NameSet_empty;
v___x_3203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3203_, 0, v___x_3202_);
lean_ctor_set(v___x_3203_, 1, v___x_3201_);
return v___x_3203_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__2(void){
_start:
{
lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; 
v___x_3204_ = lean_obj_once(&l_Lean_Meta_Rewrites_rewriteCandidates___closed__1, &l_Lean_Meta_Rewrites_rewriteCandidates___closed__1_once, _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__1);
v___x_3205_ = l_Lean_NameSet_empty;
v___x_3206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3206_, 0, v___x_3205_);
lean_ctor_set(v___x_3206_, 1, v___x_3204_);
return v___x_3206_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__3(void){
_start:
{
lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; 
v___x_3207_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_));
v___x_3208_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__4));
v___x_3209_ = l_Lean_Name_append(v___x_3208_, v___x_3207_);
return v___x_3209_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__5(void){
_start:
{
lean_object* v___x_3211_; lean_object* v___x_3212_; 
v___x_3211_ = ((lean_object*)(l_Lean_Meta_Rewrites_rewriteCandidates___closed__4));
v___x_3212_ = l_Lean_stringToMessageData(v___x_3211_);
return v___x_3212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rewriteCandidates(lean_object* v_hyps_3213_, lean_object* v_moduleRef_3214_, lean_object* v_target_3215_, lean_object* v_forbidden_3216_, lean_object* v_a_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_){
_start:
{
lean_object* v___x_3222_; lean_object* v___x_3223_; 
v___x_3222_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_rwFindDecls___boxed), 7, 1);
lean_closure_set(v___x_3222_, 0, v_moduleRef_3214_);
v___x_3223_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v___x_3222_, v_target_3215_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_);
if (lean_obj_tag(v___x_3223_) == 0)
{
lean_object* v_a_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; size_t v_sz_3229_; size_t v___x_3230_; lean_object* v___x_3231_; 
v_a_3224_ = lean_ctor_get(v___x_3223_, 0);
lean_inc(v_a_3224_);
lean_dec_ref_known(v___x_3223_, 1);
v___x_3225_ = lean_unsigned_to_nat(0u);
v___x_3226_ = lean_array_get_size(v_a_3224_);
v___x_3227_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0(v_a_3224_, v___x_3225_, v___x_3226_);
v___x_3228_ = lean_obj_once(&l_Lean_Meta_Rewrites_rewriteCandidates___closed__2, &l_Lean_Meta_Rewrites_rewriteCandidates___closed__2_once, _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__2);
v_sz_3229_ = lean_array_size(v___x_3227_);
v___x_3230_ = ((size_t)0ULL);
v___x_3231_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg(v_forbidden_3216_, v___x_3227_, v_sz_3229_, v___x_3230_, v___x_3228_);
lean_dec_ref(v___x_3227_);
if (lean_obj_tag(v___x_3231_) == 0)
{
lean_object* v_a_3232_; lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3275_; 
v_a_3232_ = lean_ctor_get(v___x_3231_, 0);
v_isSharedCheck_3275_ = !lean_is_exclusive(v___x_3231_);
if (v_isSharedCheck_3275_ == 0)
{
v___x_3234_ = v___x_3231_;
v_isShared_3235_ = v_isSharedCheck_3275_;
goto v_resetjp_3233_;
}
else
{
lean_inc(v_a_3232_);
lean_dec(v___x_3231_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3275_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
lean_object* v_snd_3236_; lean_object* v_snd_3237_; lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3273_; 
v_snd_3236_ = lean_ctor_get(v_a_3232_, 1);
lean_inc(v_snd_3236_);
lean_dec(v_a_3232_);
v_snd_3237_ = lean_ctor_get(v_snd_3236_, 1);
v_isSharedCheck_3273_ = !lean_is_exclusive(v_snd_3236_);
if (v_isSharedCheck_3273_ == 0)
{
lean_object* v_unused_3274_; 
v_unused_3274_ = lean_ctor_get(v_snd_3236_, 0);
lean_dec(v_unused_3274_);
v___x_3239_ = v_snd_3236_;
v_isShared_3240_ = v_isSharedCheck_3273_;
goto v_resetjp_3238_;
}
else
{
lean_inc(v_snd_3237_);
lean_dec(v_snd_3236_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3273_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
lean_object* v_options_3250_; uint8_t v_hasTrace_3251_; 
v_options_3250_ = lean_ctor_get(v_a_3219_, 2);
v_hasTrace_3251_ = lean_ctor_get_uint8(v_options_3250_, sizeof(void*)*1);
if (v_hasTrace_3251_ == 0)
{
lean_del_object(v___x_3239_);
goto v___jp_3241_;
}
else
{
lean_object* v_inheritedTraceOptions_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; uint8_t v___x_3255_; 
v_inheritedTraceOptions_3252_ = lean_ctor_get(v_a_3219_, 13);
v___x_3253_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_));
v___x_3254_ = lean_obj_once(&l_Lean_Meta_Rewrites_rewriteCandidates___closed__3, &l_Lean_Meta_Rewrites_rewriteCandidates___closed__3_once, _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__3);
v___x_3255_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3252_, v_options_3250_, v___x_3254_);
if (v___x_3255_ == 0)
{
lean_del_object(v___x_3239_);
goto v___jp_3241_;
}
else
{
lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3262_; 
v___x_3256_ = lean_obj_once(&l_Lean_Meta_Rewrites_rewriteCandidates___closed__5, &l_Lean_Meta_Rewrites_rewriteCandidates___closed__5_once, _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__5);
lean_inc(v_snd_3237_);
v___x_3257_ = lean_array_to_list(v_snd_3237_);
v___x_3258_ = lean_box(0);
v___x_3259_ = l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4(v___x_3257_, v___x_3258_);
v___x_3260_ = l_Lean_MessageData_ofList(v___x_3259_);
if (v_isShared_3240_ == 0)
{
lean_ctor_set_tag(v___x_3239_, 7);
lean_ctor_set(v___x_3239_, 1, v___x_3260_);
lean_ctor_set(v___x_3239_, 0, v___x_3256_);
v___x_3262_ = v___x_3239_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3272_; 
v_reuseFailAlloc_3272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3272_, 0, v___x_3256_);
lean_ctor_set(v_reuseFailAlloc_3272_, 1, v___x_3260_);
v___x_3262_ = v_reuseFailAlloc_3272_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
lean_object* v___x_3263_; 
v___x_3263_ = l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2(v___x_3253_, v___x_3262_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_);
if (lean_obj_tag(v___x_3263_) == 0)
{
lean_dec_ref_known(v___x_3263_, 1);
goto v___jp_3241_;
}
else
{
lean_object* v_a_3264_; lean_object* v___x_3266_; uint8_t v_isShared_3267_; uint8_t v_isSharedCheck_3271_; 
lean_dec(v_snd_3237_);
lean_del_object(v___x_3234_);
lean_dec_ref(v_hyps_3213_);
v_a_3264_ = lean_ctor_get(v___x_3263_, 0);
v_isSharedCheck_3271_ = !lean_is_exclusive(v___x_3263_);
if (v_isSharedCheck_3271_ == 0)
{
v___x_3266_ = v___x_3263_;
v_isShared_3267_ = v_isSharedCheck_3271_;
goto v_resetjp_3265_;
}
else
{
lean_inc(v_a_3264_);
lean_dec(v___x_3263_);
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
}
}
v___jp_3241_:
{
size_t v_sz_3242_; lean_object* v___x_3243_; size_t v_sz_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3248_; 
v_sz_3242_ = lean_array_size(v_hyps_3213_);
v___x_3243_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__2(v_sz_3242_, v___x_3230_, v_hyps_3213_);
v_sz_3244_ = lean_array_size(v_snd_3237_);
v___x_3245_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__3(v_sz_3244_, v___x_3230_, v_snd_3237_);
v___x_3246_ = l_Array_append___redArg(v___x_3243_, v___x_3245_);
lean_dec_ref(v___x_3245_);
if (v_isShared_3235_ == 0)
{
lean_ctor_set(v___x_3234_, 0, v___x_3246_);
v___x_3248_ = v___x_3234_;
goto v_reusejp_3247_;
}
else
{
lean_object* v_reuseFailAlloc_3249_; 
v_reuseFailAlloc_3249_ = lean_alloc_ctor(0, 1, 0);
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
}
else
{
lean_object* v_a_3276_; lean_object* v___x_3278_; uint8_t v_isShared_3279_; uint8_t v_isSharedCheck_3283_; 
lean_dec_ref(v_hyps_3213_);
v_a_3276_ = lean_ctor_get(v___x_3231_, 0);
v_isSharedCheck_3283_ = !lean_is_exclusive(v___x_3231_);
if (v_isSharedCheck_3283_ == 0)
{
v___x_3278_ = v___x_3231_;
v_isShared_3279_ = v_isSharedCheck_3283_;
goto v_resetjp_3277_;
}
else
{
lean_inc(v_a_3276_);
lean_dec(v___x_3231_);
v___x_3278_ = lean_box(0);
v_isShared_3279_ = v_isSharedCheck_3283_;
goto v_resetjp_3277_;
}
v_resetjp_3277_:
{
lean_object* v___x_3281_; 
if (v_isShared_3279_ == 0)
{
v___x_3281_ = v___x_3278_;
goto v_reusejp_3280_;
}
else
{
lean_object* v_reuseFailAlloc_3282_; 
v_reuseFailAlloc_3282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3282_, 0, v_a_3276_);
v___x_3281_ = v_reuseFailAlloc_3282_;
goto v_reusejp_3280_;
}
v_reusejp_3280_:
{
return v___x_3281_;
}
}
}
}
else
{
lean_object* v_a_3284_; lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3291_; 
lean_dec_ref(v_hyps_3213_);
v_a_3284_ = lean_ctor_get(v___x_3223_, 0);
v_isSharedCheck_3291_ = !lean_is_exclusive(v___x_3223_);
if (v_isSharedCheck_3291_ == 0)
{
v___x_3286_ = v___x_3223_;
v_isShared_3287_ = v_isSharedCheck_3291_;
goto v_resetjp_3285_;
}
else
{
lean_inc(v_a_3284_);
lean_dec(v___x_3223_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3291_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
lean_object* v___x_3289_; 
if (v_isShared_3287_ == 0)
{
v___x_3289_ = v___x_3286_;
goto v_reusejp_3288_;
}
else
{
lean_object* v_reuseFailAlloc_3290_; 
v_reuseFailAlloc_3290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3290_, 0, v_a_3284_);
v___x_3289_ = v_reuseFailAlloc_3290_;
goto v_reusejp_3288_;
}
v_reusejp_3288_:
{
return v___x_3289_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rewriteCandidates___boxed(lean_object* v_hyps_3292_, lean_object* v_moduleRef_3293_, lean_object* v_target_3294_, lean_object* v_forbidden_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_){
_start:
{
lean_object* v_res_3301_; 
v_res_3301_ = l_Lean_Meta_Rewrites_rewriteCandidates(v_hyps_3292_, v_moduleRef_3293_, v_target_3294_, v_forbidden_3295_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_);
lean_dec(v_a_3299_);
lean_dec_ref(v_a_3298_);
lean_dec(v_a_3297_);
lean_dec_ref(v_a_3296_);
lean_dec(v_forbidden_3295_);
return v_res_3301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1(lean_object* v_forbidden_3302_, lean_object* v_as_3303_, size_t v_sz_3304_, size_t v_i_3305_, lean_object* v_b_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_){
_start:
{
lean_object* v___x_3312_; 
v___x_3312_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg(v_forbidden_3302_, v_as_3303_, v_sz_3304_, v_i_3305_, v_b_3306_);
return v___x_3312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___boxed(lean_object* v_forbidden_3313_, lean_object* v_as_3314_, lean_object* v_sz_3315_, lean_object* v_i_3316_, lean_object* v_b_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_){
_start:
{
size_t v_sz_boxed_3323_; size_t v_i_boxed_3324_; lean_object* v_res_3325_; 
v_sz_boxed_3323_ = lean_unbox_usize(v_sz_3315_);
lean_dec(v_sz_3315_);
v_i_boxed_3324_ = lean_unbox_usize(v_i_3316_);
lean_dec(v_i_3316_);
v_res_3325_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1(v_forbidden_3313_, v_as_3314_, v_sz_boxed_3323_, v_i_boxed_3324_, v_b_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_);
lean_dec(v___y_3321_);
lean_dec_ref(v___y_3320_);
lean_dec(v___y_3319_);
lean_dec_ref(v___y_3318_);
lean_dec_ref(v_as_3314_);
lean_dec(v_forbidden_3313_);
return v_res_3325_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0(lean_object* v_xs_3326_, lean_object* v_j_3327_, lean_object* v_h_3328_){
_start:
{
lean_object* v___x_3329_; 
v___x_3329_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0___redArg(v_xs_3326_, v_j_3327_);
return v___x_3329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_newGoal(lean_object* v_r_3330_){
_start:
{
uint8_t v_rfl_x3f_3331_; 
v_rfl_x3f_3331_ = lean_ctor_get_uint8(v_r_3330_, sizeof(void*)*4 + 1);
if (v_rfl_x3f_3331_ == 0)
{
lean_object* v_result_3332_; lean_object* v_eNew_3333_; lean_object* v___x_3334_; 
v_result_3332_ = lean_ctor_get(v_r_3330_, 2);
v_eNew_3333_ = lean_ctor_get(v_result_3332_, 0);
lean_inc_ref(v_eNew_3333_);
v___x_3334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3334_, 0, v_eNew_3333_);
return v___x_3334_;
}
else
{
lean_object* v___x_3335_; 
v___x_3335_ = lean_box(0);
return v___x_3335_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_newGoal___boxed(lean_object* v_r_3336_){
_start:
{
lean_object* v_res_3337_; 
v_res_3337_ = l_Lean_Meta_Rewrites_RewriteResult_newGoal(v_r_3336_);
lean_dec_ref(v_r_3336_);
return v_res_3337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0(lean_object* v_x_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_){
_start:
{
lean_object* v___x_3348_; 
lean_inc(v___y_3342_);
lean_inc_ref(v___y_3341_);
lean_inc(v___y_3340_);
lean_inc_ref(v___y_3339_);
v___x_3348_ = lean_apply_9(v_x_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_, lean_box(0));
return v___x_3348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0___boxed(lean_object* v_x_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_){
_start:
{
lean_object* v_res_3359_; 
v_res_3359_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0(v_x_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_);
lean_dec(v___y_3353_);
lean_dec_ref(v___y_3352_);
lean_dec(v___y_3351_);
lean_dec_ref(v___y_3350_);
return v_res_3359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg(lean_object* v_mctx_3360_, lean_object* v_x_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_){
_start:
{
lean_object* v___f_3371_; lean_object* v___x_3372_; 
lean_inc(v___y_3365_);
lean_inc_ref(v___y_3364_);
lean_inc(v___y_3363_);
lean_inc_ref(v___y_3362_);
v___f_3371_ = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3371_, 0, v_x_3361_);
lean_closure_set(v___f_3371_, 1, v___y_3362_);
lean_closure_set(v___f_3371_, 2, v___y_3363_);
lean_closure_set(v___f_3371_, 3, v___y_3364_);
lean_closure_set(v___f_3371_, 4, v___y_3365_);
v___x_3372_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp(lean_box(0), v_mctx_3360_, v___f_3371_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_);
if (lean_obj_tag(v___x_3372_) == 0)
{
return v___x_3372_;
}
else
{
lean_object* v_a_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3380_; 
v_a_3373_ = lean_ctor_get(v___x_3372_, 0);
v_isSharedCheck_3380_ = !lean_is_exclusive(v___x_3372_);
if (v_isSharedCheck_3380_ == 0)
{
v___x_3375_ = v___x_3372_;
v_isShared_3376_ = v_isSharedCheck_3380_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_a_3373_);
lean_dec(v___x_3372_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3380_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v___x_3378_; 
if (v_isShared_3376_ == 0)
{
v___x_3378_ = v___x_3375_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v_a_3373_);
v___x_3378_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
return v___x_3378_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___boxed(lean_object* v_mctx_3381_, lean_object* v_x_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_){
_start:
{
lean_object* v_res_3392_; 
v_res_3392_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg(v_mctx_3381_, v_x_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_);
lean_dec(v___y_3390_);
lean_dec_ref(v___y_3389_);
lean_dec(v___y_3388_);
lean_dec_ref(v___y_3387_);
lean_dec(v___y_3386_);
lean_dec_ref(v___y_3385_);
lean_dec(v___y_3384_);
lean_dec_ref(v___y_3383_);
return v_res_3392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0(lean_object* v_00_u03b1_3393_, lean_object* v_mctx_3394_, lean_object* v_x_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_){
_start:
{
lean_object* v___x_3405_; 
v___x_3405_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg(v_mctx_3394_, v_x_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_);
return v___x_3405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___boxed(lean_object* v_00_u03b1_3406_, lean_object* v_mctx_3407_, lean_object* v_x_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_){
_start:
{
lean_object* v_res_3418_; 
v_res_3418_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0(v_00_u03b1_3406_, v_mctx_3407_, v_x_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_);
lean_dec(v___y_3416_);
lean_dec_ref(v___y_3415_);
lean_dec(v___y_3414_);
lean_dec_ref(v___y_3413_);
lean_dec(v___y_3412_);
lean_dec_ref(v___y_3411_);
lean_dec(v___y_3410_);
lean_dec_ref(v___y_3409_);
return v_res_3418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0(lean_object* v_expr_3419_, uint8_t v_symm_3420_, lean_object* v_r_3421_, lean_object* v_ref_3422_, lean_object* v_checkState_x3f_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_){
_start:
{
lean_object* v___x_3433_; 
v___x_3433_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_3425_, v___y_3427_, v___y_3429_, v___y_3431_);
if (lean_obj_tag(v___x_3433_) == 0)
{
lean_object* v_a_3434_; lean_object* v_ref_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___y_3445_; 
v_a_3434_ = lean_ctor_get(v___x_3433_, 0);
lean_inc(v_a_3434_);
lean_dec_ref_known(v___x_3433_, 1);
v_ref_3435_ = lean_ctor_get(v___y_3430_, 5);
v___x_3436_ = lean_box(v_symm_3420_);
v___x_3437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3437_, 0, v_expr_3419_);
lean_ctor_set(v___x_3437_, 1, v___x_3436_);
v___x_3438_ = lean_box(0);
v___x_3439_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3439_, 0, v___x_3437_);
lean_ctor_set(v___x_3439_, 1, v___x_3438_);
v___x_3440_ = l_Lean_Meta_Rewrites_RewriteResult_newGoal(v_r_3421_);
v___x_3441_ = l_Lean_Option_toLOption___redArg(v___x_3440_);
v___x_3442_ = lean_box(0);
lean_inc(v_ref_3435_);
v___x_3443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3443_, 0, v_ref_3435_);
if (lean_obj_tag(v_checkState_x3f_3423_) == 0)
{
v___y_3445_ = v_a_3434_;
goto v___jp_3444_;
}
else
{
lean_object* v_val_3448_; 
lean_dec(v_a_3434_);
v_val_3448_ = lean_ctor_get(v_checkState_x3f_3423_, 0);
lean_inc(v_val_3448_);
lean_dec_ref_known(v_checkState_x3f_3423_, 1);
v___y_3445_ = v_val_3448_;
goto v___jp_3444_;
}
v___jp_3444_:
{
lean_object* v___x_3446_; lean_object* v___x_3447_; 
v___x_3446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3446_, 0, v___y_3445_);
v___x_3447_ = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion(v_ref_3422_, v___x_3439_, v___x_3441_, v___x_3442_, v___x_3443_, v___x_3446_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_);
return v___x_3447_;
}
}
else
{
lean_object* v_a_3449_; lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3456_; 
lean_dec(v_checkState_x3f_3423_);
lean_dec(v_ref_3422_);
lean_dec_ref(v_expr_3419_);
v_a_3449_ = lean_ctor_get(v___x_3433_, 0);
v_isSharedCheck_3456_ = !lean_is_exclusive(v___x_3433_);
if (v_isSharedCheck_3456_ == 0)
{
v___x_3451_ = v___x_3433_;
v_isShared_3452_ = v_isSharedCheck_3456_;
goto v_resetjp_3450_;
}
else
{
lean_inc(v_a_3449_);
lean_dec(v___x_3433_);
v___x_3451_ = lean_box(0);
v_isShared_3452_ = v_isSharedCheck_3456_;
goto v_resetjp_3450_;
}
v_resetjp_3450_:
{
lean_object* v___x_3454_; 
if (v_isShared_3452_ == 0)
{
v___x_3454_ = v___x_3451_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v_a_3449_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0___boxed(lean_object* v_expr_3457_, lean_object* v_symm_3458_, lean_object* v_r_3459_, lean_object* v_ref_3460_, lean_object* v_checkState_x3f_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_){
_start:
{
uint8_t v_symm_boxed_3471_; lean_object* v_res_3472_; 
v_symm_boxed_3471_ = lean_unbox(v_symm_3458_);
v_res_3472_ = l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0(v_expr_3457_, v_symm_boxed_3471_, v_r_3459_, v_ref_3460_, v_checkState_x3f_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_);
lean_dec(v___y_3469_);
lean_dec_ref(v___y_3468_);
lean_dec(v___y_3467_);
lean_dec_ref(v___y_3466_);
lean_dec(v___y_3465_);
lean_dec_ref(v___y_3464_);
lean_dec(v___y_3463_);
lean_dec_ref(v___y_3462_);
lean_dec_ref(v_r_3459_);
return v_res_3472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion(lean_object* v_ref_3473_, lean_object* v_r_3474_, lean_object* v_checkState_x3f_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_){
_start:
{
lean_object* v_expr_3485_; uint8_t v_symm_3486_; lean_object* v_mctx_3487_; lean_object* v___x_3488_; lean_object* v___f_3489_; lean_object* v___x_3490_; 
v_expr_3485_ = lean_ctor_get(v_r_3474_, 0);
lean_inc_ref(v_expr_3485_);
v_symm_3486_ = lean_ctor_get_uint8(v_r_3474_, sizeof(void*)*4);
v_mctx_3487_ = lean_ctor_get(v_r_3474_, 3);
lean_inc_ref(v_mctx_3487_);
v___x_3488_ = lean_box(v_symm_3486_);
v___f_3489_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0___boxed), 14, 5);
lean_closure_set(v___f_3489_, 0, v_expr_3485_);
lean_closure_set(v___f_3489_, 1, v___x_3488_);
lean_closure_set(v___f_3489_, 2, v_r_3474_);
lean_closure_set(v___f_3489_, 3, v_ref_3473_);
lean_closure_set(v___f_3489_, 4, v_checkState_x3f_3475_);
v___x_3490_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg(v_mctx_3487_, v___f_3489_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_);
return v___x_3490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___boxed(lean_object* v_ref_3491_, lean_object* v_r_3492_, lean_object* v_checkState_x3f_3493_, lean_object* v_a_3494_, lean_object* v_a_3495_, lean_object* v_a_3496_, lean_object* v_a_3497_, lean_object* v_a_3498_, lean_object* v_a_3499_, lean_object* v_a_3500_, lean_object* v_a_3501_, lean_object* v_a_3502_){
_start:
{
lean_object* v_res_3503_; 
v_res_3503_ = l_Lean_Meta_Rewrites_RewriteResult_addSuggestion(v_ref_3491_, v_r_3492_, v_checkState_x3f_3493_, v_a_3494_, v_a_3495_, v_a_3496_, v_a_3497_, v_a_3498_, v_a_3499_, v_a_3500_, v_a_3501_);
lean_dec(v_a_3501_);
lean_dec_ref(v_a_3500_);
lean_dec(v_a_3499_);
lean_dec_ref(v_a_3498_);
lean_dec(v_a_3497_);
lean_dec_ref(v_a_3496_);
lean_dec(v_a_3495_);
lean_dec_ref(v_a_3494_);
return v_res_3503_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3___redArg(lean_object* v_a_3504_, lean_object* v_b_3505_, lean_object* v_x_3506_){
_start:
{
if (lean_obj_tag(v_x_3506_) == 0)
{
lean_dec(v_b_3505_);
lean_dec_ref(v_a_3504_);
return v_x_3506_;
}
else
{
lean_object* v_key_3507_; lean_object* v_value_3508_; lean_object* v_tail_3509_; lean_object* v___x_3511_; uint8_t v_isShared_3512_; uint8_t v_isSharedCheck_3521_; 
v_key_3507_ = lean_ctor_get(v_x_3506_, 0);
v_value_3508_ = lean_ctor_get(v_x_3506_, 1);
v_tail_3509_ = lean_ctor_get(v_x_3506_, 2);
v_isSharedCheck_3521_ = !lean_is_exclusive(v_x_3506_);
if (v_isSharedCheck_3521_ == 0)
{
v___x_3511_ = v_x_3506_;
v_isShared_3512_ = v_isSharedCheck_3521_;
goto v_resetjp_3510_;
}
else
{
lean_inc(v_tail_3509_);
lean_inc(v_value_3508_);
lean_inc(v_key_3507_);
lean_dec(v_x_3506_);
v___x_3511_ = lean_box(0);
v_isShared_3512_ = v_isSharedCheck_3521_;
goto v_resetjp_3510_;
}
v_resetjp_3510_:
{
uint8_t v___x_3513_; 
v___x_3513_ = lean_string_dec_eq(v_key_3507_, v_a_3504_);
if (v___x_3513_ == 0)
{
lean_object* v___x_3514_; lean_object* v___x_3516_; 
v___x_3514_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3___redArg(v_a_3504_, v_b_3505_, v_tail_3509_);
if (v_isShared_3512_ == 0)
{
lean_ctor_set(v___x_3511_, 2, v___x_3514_);
v___x_3516_ = v___x_3511_;
goto v_reusejp_3515_;
}
else
{
lean_object* v_reuseFailAlloc_3517_; 
v_reuseFailAlloc_3517_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3517_, 0, v_key_3507_);
lean_ctor_set(v_reuseFailAlloc_3517_, 1, v_value_3508_);
lean_ctor_set(v_reuseFailAlloc_3517_, 2, v___x_3514_);
v___x_3516_ = v_reuseFailAlloc_3517_;
goto v_reusejp_3515_;
}
v_reusejp_3515_:
{
return v___x_3516_;
}
}
else
{
lean_object* v___x_3519_; 
lean_dec(v_value_3508_);
lean_dec(v_key_3507_);
if (v_isShared_3512_ == 0)
{
lean_ctor_set(v___x_3511_, 1, v_b_3505_);
lean_ctor_set(v___x_3511_, 0, v_a_3504_);
v___x_3519_ = v___x_3511_;
goto v_reusejp_3518_;
}
else
{
lean_object* v_reuseFailAlloc_3520_; 
v_reuseFailAlloc_3520_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3520_, 0, v_a_3504_);
lean_ctor_set(v_reuseFailAlloc_3520_, 1, v_b_3505_);
lean_ctor_set(v_reuseFailAlloc_3520_, 2, v_tail_3509_);
v___x_3519_ = v_reuseFailAlloc_3520_;
goto v_reusejp_3518_;
}
v_reusejp_3518_:
{
return v___x_3519_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_x_3522_, lean_object* v_x_3523_){
_start:
{
if (lean_obj_tag(v_x_3523_) == 0)
{
return v_x_3522_;
}
else
{
lean_object* v_key_3524_; lean_object* v_value_3525_; lean_object* v_tail_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3549_; 
v_key_3524_ = lean_ctor_get(v_x_3523_, 0);
v_value_3525_ = lean_ctor_get(v_x_3523_, 1);
v_tail_3526_ = lean_ctor_get(v_x_3523_, 2);
v_isSharedCheck_3549_ = !lean_is_exclusive(v_x_3523_);
if (v_isSharedCheck_3549_ == 0)
{
v___x_3528_ = v_x_3523_;
v_isShared_3529_ = v_isSharedCheck_3549_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_tail_3526_);
lean_inc(v_value_3525_);
lean_inc(v_key_3524_);
lean_dec(v_x_3523_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3549_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v___x_3530_; uint64_t v___x_3531_; uint64_t v___x_3532_; uint64_t v___x_3533_; uint64_t v_fold_3534_; uint64_t v___x_3535_; uint64_t v___x_3536_; uint64_t v___x_3537_; size_t v___x_3538_; size_t v___x_3539_; size_t v___x_3540_; size_t v___x_3541_; size_t v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3545_; 
v___x_3530_ = lean_array_get_size(v_x_3522_);
v___x_3531_ = lean_string_hash(v_key_3524_);
v___x_3532_ = 32ULL;
v___x_3533_ = lean_uint64_shift_right(v___x_3531_, v___x_3532_);
v_fold_3534_ = lean_uint64_xor(v___x_3531_, v___x_3533_);
v___x_3535_ = 16ULL;
v___x_3536_ = lean_uint64_shift_right(v_fold_3534_, v___x_3535_);
v___x_3537_ = lean_uint64_xor(v_fold_3534_, v___x_3536_);
v___x_3538_ = lean_uint64_to_usize(v___x_3537_);
v___x_3539_ = lean_usize_of_nat(v___x_3530_);
v___x_3540_ = ((size_t)1ULL);
v___x_3541_ = lean_usize_sub(v___x_3539_, v___x_3540_);
v___x_3542_ = lean_usize_land(v___x_3538_, v___x_3541_);
v___x_3543_ = lean_array_uget_borrowed(v_x_3522_, v___x_3542_);
lean_inc(v___x_3543_);
if (v_isShared_3529_ == 0)
{
lean_ctor_set(v___x_3528_, 2, v___x_3543_);
v___x_3545_ = v___x_3528_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3548_; 
v_reuseFailAlloc_3548_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3548_, 0, v_key_3524_);
lean_ctor_set(v_reuseFailAlloc_3548_, 1, v_value_3525_);
lean_ctor_set(v_reuseFailAlloc_3548_, 2, v___x_3543_);
v___x_3545_ = v_reuseFailAlloc_3548_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
lean_object* v___x_3546_; 
v___x_3546_ = lean_array_uset(v_x_3522_, v___x_3542_, v___x_3545_);
v_x_3522_ = v___x_3546_;
v_x_3523_ = v_tail_3526_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3___redArg(lean_object* v_i_3550_, lean_object* v_source_3551_, lean_object* v_target_3552_){
_start:
{
lean_object* v___x_3553_; uint8_t v___x_3554_; 
v___x_3553_ = lean_array_get_size(v_source_3551_);
v___x_3554_ = lean_nat_dec_lt(v_i_3550_, v___x_3553_);
if (v___x_3554_ == 0)
{
lean_dec_ref(v_source_3551_);
lean_dec(v_i_3550_);
return v_target_3552_;
}
else
{
lean_object* v_es_3555_; lean_object* v___x_3556_; lean_object* v_source_3557_; lean_object* v_target_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; 
v_es_3555_ = lean_array_fget(v_source_3551_, v_i_3550_);
v___x_3556_ = lean_box(0);
v_source_3557_ = lean_array_fset(v_source_3551_, v_i_3550_, v___x_3556_);
v_target_3558_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3_spec__5___redArg(v_target_3552_, v_es_3555_);
v___x_3559_ = lean_unsigned_to_nat(1u);
v___x_3560_ = lean_nat_add(v_i_3550_, v___x_3559_);
lean_dec(v_i_3550_);
v_i_3550_ = v___x_3560_;
v_source_3551_ = v_source_3557_;
v_target_3552_ = v_target_3558_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2___redArg(lean_object* v_data_3562_){
_start:
{
lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v_nbuckets_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; 
v___x_3563_ = lean_array_get_size(v_data_3562_);
v___x_3564_ = lean_unsigned_to_nat(2u);
v_nbuckets_3565_ = lean_nat_mul(v___x_3563_, v___x_3564_);
v___x_3566_ = lean_unsigned_to_nat(0u);
v___x_3567_ = lean_box(0);
v___x_3568_ = lean_mk_array(v_nbuckets_3565_, v___x_3567_);
v___x_3569_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3___redArg(v___x_3566_, v_data_3562_, v___x_3568_);
return v___x_3569_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(lean_object* v_a_3570_, lean_object* v_x_3571_){
_start:
{
if (lean_obj_tag(v_x_3571_) == 0)
{
uint8_t v___x_3572_; 
v___x_3572_ = 0;
return v___x_3572_;
}
else
{
lean_object* v_key_3573_; lean_object* v_tail_3574_; uint8_t v___x_3575_; 
v_key_3573_ = lean_ctor_get(v_x_3571_, 0);
v_tail_3574_ = lean_ctor_get(v_x_3571_, 2);
v___x_3575_ = lean_string_dec_eq(v_key_3573_, v_a_3570_);
if (v___x_3575_ == 0)
{
v_x_3571_ = v_tail_3574_;
goto _start;
}
else
{
return v___x_3575_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg___boxed(lean_object* v_a_3577_, lean_object* v_x_3578_){
_start:
{
uint8_t v_res_3579_; lean_object* v_r_3580_; 
v_res_3579_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(v_a_3577_, v_x_3578_);
lean_dec(v_x_3578_);
lean_dec_ref(v_a_3577_);
v_r_3580_ = lean_box(v_res_3579_);
return v_r_3580_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1___redArg(lean_object* v_m_3581_, lean_object* v_a_3582_, lean_object* v_b_3583_){
_start:
{
lean_object* v_size_3584_; lean_object* v_buckets_3585_; lean_object* v___x_3587_; uint8_t v_isShared_3588_; uint8_t v_isSharedCheck_3628_; 
v_size_3584_ = lean_ctor_get(v_m_3581_, 0);
v_buckets_3585_ = lean_ctor_get(v_m_3581_, 1);
v_isSharedCheck_3628_ = !lean_is_exclusive(v_m_3581_);
if (v_isSharedCheck_3628_ == 0)
{
v___x_3587_ = v_m_3581_;
v_isShared_3588_ = v_isSharedCheck_3628_;
goto v_resetjp_3586_;
}
else
{
lean_inc(v_buckets_3585_);
lean_inc(v_size_3584_);
lean_dec(v_m_3581_);
v___x_3587_ = lean_box(0);
v_isShared_3588_ = v_isSharedCheck_3628_;
goto v_resetjp_3586_;
}
v_resetjp_3586_:
{
lean_object* v___x_3589_; uint64_t v___x_3590_; uint64_t v___x_3591_; uint64_t v___x_3592_; uint64_t v_fold_3593_; uint64_t v___x_3594_; uint64_t v___x_3595_; uint64_t v___x_3596_; size_t v___x_3597_; size_t v___x_3598_; size_t v___x_3599_; size_t v___x_3600_; size_t v___x_3601_; lean_object* v_bkt_3602_; uint8_t v___x_3603_; 
v___x_3589_ = lean_array_get_size(v_buckets_3585_);
v___x_3590_ = lean_string_hash(v_a_3582_);
v___x_3591_ = 32ULL;
v___x_3592_ = lean_uint64_shift_right(v___x_3590_, v___x_3591_);
v_fold_3593_ = lean_uint64_xor(v___x_3590_, v___x_3592_);
v___x_3594_ = 16ULL;
v___x_3595_ = lean_uint64_shift_right(v_fold_3593_, v___x_3594_);
v___x_3596_ = lean_uint64_xor(v_fold_3593_, v___x_3595_);
v___x_3597_ = lean_uint64_to_usize(v___x_3596_);
v___x_3598_ = lean_usize_of_nat(v___x_3589_);
v___x_3599_ = ((size_t)1ULL);
v___x_3600_ = lean_usize_sub(v___x_3598_, v___x_3599_);
v___x_3601_ = lean_usize_land(v___x_3597_, v___x_3600_);
v_bkt_3602_ = lean_array_uget_borrowed(v_buckets_3585_, v___x_3601_);
v___x_3603_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(v_a_3582_, v_bkt_3602_);
if (v___x_3603_ == 0)
{
lean_object* v___x_3604_; lean_object* v_size_x27_3605_; lean_object* v___x_3606_; lean_object* v_buckets_x27_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; uint8_t v___x_3613_; 
v___x_3604_ = lean_unsigned_to_nat(1u);
v_size_x27_3605_ = lean_nat_add(v_size_3584_, v___x_3604_);
lean_dec(v_size_3584_);
lean_inc(v_bkt_3602_);
v___x_3606_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3606_, 0, v_a_3582_);
lean_ctor_set(v___x_3606_, 1, v_b_3583_);
lean_ctor_set(v___x_3606_, 2, v_bkt_3602_);
v_buckets_x27_3607_ = lean_array_uset(v_buckets_3585_, v___x_3601_, v___x_3606_);
v___x_3608_ = lean_unsigned_to_nat(4u);
v___x_3609_ = lean_nat_mul(v_size_x27_3605_, v___x_3608_);
v___x_3610_ = lean_unsigned_to_nat(3u);
v___x_3611_ = lean_nat_div(v___x_3609_, v___x_3610_);
lean_dec(v___x_3609_);
v___x_3612_ = lean_array_get_size(v_buckets_x27_3607_);
v___x_3613_ = lean_nat_dec_le(v___x_3611_, v___x_3612_);
lean_dec(v___x_3611_);
if (v___x_3613_ == 0)
{
lean_object* v_val_3614_; lean_object* v___x_3616_; 
v_val_3614_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2___redArg(v_buckets_x27_3607_);
if (v_isShared_3588_ == 0)
{
lean_ctor_set(v___x_3587_, 1, v_val_3614_);
lean_ctor_set(v___x_3587_, 0, v_size_x27_3605_);
v___x_3616_ = v___x_3587_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v_size_x27_3605_);
lean_ctor_set(v_reuseFailAlloc_3617_, 1, v_val_3614_);
v___x_3616_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
return v___x_3616_;
}
}
else
{
lean_object* v___x_3619_; 
if (v_isShared_3588_ == 0)
{
lean_ctor_set(v___x_3587_, 1, v_buckets_x27_3607_);
lean_ctor_set(v___x_3587_, 0, v_size_x27_3605_);
v___x_3619_ = v___x_3587_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v_size_x27_3605_);
lean_ctor_set(v_reuseFailAlloc_3620_, 1, v_buckets_x27_3607_);
v___x_3619_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
return v___x_3619_;
}
}
}
else
{
lean_object* v___x_3621_; lean_object* v_buckets_x27_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3626_; 
lean_inc(v_bkt_3602_);
v___x_3621_ = lean_box(0);
v_buckets_x27_3622_ = lean_array_uset(v_buckets_3585_, v___x_3601_, v___x_3621_);
v___x_3623_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3___redArg(v_a_3582_, v_b_3583_, v_bkt_3602_);
v___x_3624_ = lean_array_uset(v_buckets_x27_3622_, v___x_3601_, v___x_3623_);
if (v_isShared_3588_ == 0)
{
lean_ctor_set(v___x_3587_, 1, v___x_3624_);
v___x_3626_ = v___x_3587_;
goto v_reusejp_3625_;
}
else
{
lean_object* v_reuseFailAlloc_3627_; 
v_reuseFailAlloc_3627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3627_, 0, v_size_3584_);
lean_ctor_set(v_reuseFailAlloc_3627_, 1, v___x_3624_);
v___x_3626_ = v_reuseFailAlloc_3627_;
goto v_reusejp_3625_;
}
v_reusejp_3625_:
{
return v___x_3626_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg(lean_object* v_m_3629_, lean_object* v_a_3630_){
_start:
{
lean_object* v_buckets_3631_; lean_object* v___x_3632_; uint64_t v___x_3633_; uint64_t v___x_3634_; uint64_t v___x_3635_; uint64_t v_fold_3636_; uint64_t v___x_3637_; uint64_t v___x_3638_; uint64_t v___x_3639_; size_t v___x_3640_; size_t v___x_3641_; size_t v___x_3642_; size_t v___x_3643_; size_t v___x_3644_; lean_object* v___x_3645_; uint8_t v___x_3646_; 
v_buckets_3631_ = lean_ctor_get(v_m_3629_, 1);
v___x_3632_ = lean_array_get_size(v_buckets_3631_);
v___x_3633_ = lean_string_hash(v_a_3630_);
v___x_3634_ = 32ULL;
v___x_3635_ = lean_uint64_shift_right(v___x_3633_, v___x_3634_);
v_fold_3636_ = lean_uint64_xor(v___x_3633_, v___x_3635_);
v___x_3637_ = 16ULL;
v___x_3638_ = lean_uint64_shift_right(v_fold_3636_, v___x_3637_);
v___x_3639_ = lean_uint64_xor(v_fold_3636_, v___x_3638_);
v___x_3640_ = lean_uint64_to_usize(v___x_3639_);
v___x_3641_ = lean_usize_of_nat(v___x_3632_);
v___x_3642_ = ((size_t)1ULL);
v___x_3643_ = lean_usize_sub(v___x_3641_, v___x_3642_);
v___x_3644_ = lean_usize_land(v___x_3640_, v___x_3643_);
v___x_3645_ = lean_array_uget_borrowed(v_buckets_3631_, v___x_3644_);
v___x_3646_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(v_a_3630_, v___x_3645_);
return v___x_3646_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg___boxed(lean_object* v_m_3647_, lean_object* v_a_3648_){
_start:
{
uint8_t v_res_3649_; lean_object* v_r_3650_; 
v_res_3649_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg(v_m_3647_, v_a_3648_);
lean_dec_ref(v_a_3648_);
lean_dec_ref(v_m_3647_);
v_r_3650_ = lean_box(v_res_3649_);
return v_r_3650_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg(lean_object* v_cfg_3651_, lean_object* v_as_x27_3652_, lean_object* v_b_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_){
_start:
{
if (lean_obj_tag(v_as_x27_3652_) == 0)
{
lean_object* v___x_3659_; 
lean_dec_ref(v_cfg_3651_);
v___x_3659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3659_, 0, v_b_3653_);
return v___x_3659_;
}
else
{
lean_object* v_head_3660_; lean_object* v_snd_3661_; lean_object* v_tail_3662_; lean_object* v_fst_3663_; lean_object* v_fst_3664_; lean_object* v_snd_3665_; lean_object* v___x_3666_; 
v_head_3660_ = lean_ctor_get(v_as_x27_3652_, 0);
v_snd_3661_ = lean_ctor_get(v_head_3660_, 1);
v_tail_3662_ = lean_ctor_get(v_as_x27_3652_, 1);
v_fst_3663_ = lean_ctor_get(v_head_3660_, 0);
v_fst_3664_ = lean_ctor_get(v_snd_3661_, 0);
v_snd_3665_ = lean_ctor_get(v_snd_3661_, 1);
v___x_3666_ = l_Lean_getRemainingHeartbeats___redArg(v___y_3656_);
if (lean_obj_tag(v___x_3666_) == 0)
{
lean_object* v_snd_3667_; lean_object* v___x_3669_; uint8_t v_isShared_3670_; uint8_t v_isSharedCheck_3811_; 
v_snd_3667_ = lean_ctor_get(v_b_3653_, 1);
v_isSharedCheck_3811_ = !lean_is_exclusive(v_b_3653_);
if (v_isSharedCheck_3811_ == 0)
{
lean_object* v_unused_3812_; 
v_unused_3812_ = lean_ctor_get(v_b_3653_, 0);
lean_dec(v_unused_3812_);
v___x_3669_ = v_b_3653_;
v_isShared_3670_ = v_isSharedCheck_3811_;
goto v_resetjp_3668_;
}
else
{
lean_inc(v_snd_3667_);
lean_dec(v_b_3653_);
v___x_3669_ = lean_box(0);
v_isShared_3670_ = v_isSharedCheck_3811_;
goto v_resetjp_3668_;
}
v_resetjp_3668_:
{
lean_object* v_a_3671_; lean_object* v___x_3673_; uint8_t v_isShared_3674_; uint8_t v_isSharedCheck_3810_; 
v_a_3671_ = lean_ctor_get(v___x_3666_, 0);
v_isSharedCheck_3810_ = !lean_is_exclusive(v___x_3666_);
if (v_isSharedCheck_3810_ == 0)
{
v___x_3673_ = v___x_3666_;
v_isShared_3674_ = v_isSharedCheck_3810_;
goto v_resetjp_3672_;
}
else
{
lean_inc(v_a_3671_);
lean_dec(v___x_3666_);
v___x_3673_ = lean_box(0);
v_isShared_3674_ = v_isSharedCheck_3810_;
goto v_resetjp_3672_;
}
v_resetjp_3672_:
{
lean_object* v_fst_3675_; lean_object* v_snd_3676_; lean_object* v___x_3678_; uint8_t v_isShared_3679_; uint8_t v_isSharedCheck_3809_; 
v_fst_3675_ = lean_ctor_get(v_snd_3667_, 0);
v_snd_3676_ = lean_ctor_get(v_snd_3667_, 1);
v_isSharedCheck_3809_ = !lean_is_exclusive(v_snd_3667_);
if (v_isSharedCheck_3809_ == 0)
{
v___x_3678_ = v_snd_3667_;
v_isShared_3679_ = v_isSharedCheck_3809_;
goto v_resetjp_3677_;
}
else
{
lean_inc(v_snd_3676_);
lean_inc(v_fst_3675_);
lean_dec(v_snd_3667_);
v___x_3678_ = lean_box(0);
v_isShared_3679_ = v_isSharedCheck_3809_;
goto v_resetjp_3677_;
}
v_resetjp_3677_:
{
uint8_t v_stopAtRfl_3680_; lean_object* v_max_3681_; lean_object* v_minHeartbeats_3682_; lean_object* v_goal_3683_; lean_object* v_target_3684_; uint8_t v_side_3685_; lean_object* v_mctx_3686_; uint8_t v___x_3687_; 
v_stopAtRfl_3680_ = lean_ctor_get_uint8(v_cfg_3651_, sizeof(void*)*5);
v_max_3681_ = lean_ctor_get(v_cfg_3651_, 0);
v_minHeartbeats_3682_ = lean_ctor_get(v_cfg_3651_, 1);
v_goal_3683_ = lean_ctor_get(v_cfg_3651_, 2);
v_target_3684_ = lean_ctor_get(v_cfg_3651_, 3);
v_side_3685_ = lean_ctor_get_uint8(v_cfg_3651_, sizeof(void*)*5 + 1);
v_mctx_3686_ = lean_ctor_get(v_cfg_3651_, 4);
v___x_3687_ = lean_nat_dec_lt(v_a_3671_, v_minHeartbeats_3682_);
lean_dec(v_a_3671_);
if (v___x_3687_ == 0)
{
lean_object* v___x_3688_; uint8_t v___x_3689_; 
v___x_3688_ = lean_array_get_size(v_snd_3676_);
v___x_3689_ = lean_nat_dec_le(v_max_3681_, v___x_3688_);
if (v___x_3689_ == 0)
{
lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; 
lean_del_object(v___x_3673_);
v___x_3690_ = lean_box(v_side_3685_);
lean_inc(v_snd_3665_);
lean_inc(v_fst_3664_);
lean_inc(v_fst_3663_);
lean_inc_ref(v_target_3684_);
lean_inc(v_goal_3683_);
lean_inc_ref_n(v_mctx_3686_, 2);
v___x_3691_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_rwLemma___boxed), 12, 7);
lean_closure_set(v___x_3691_, 0, v_mctx_3686_);
lean_closure_set(v___x_3691_, 1, v_goal_3683_);
lean_closure_set(v___x_3691_, 2, v_target_3684_);
lean_closure_set(v___x_3691_, 3, v___x_3690_);
lean_closure_set(v___x_3691_, 4, v_fst_3663_);
lean_closure_set(v___x_3691_, 5, v_fst_3664_);
lean_closure_set(v___x_3691_, 6, v_snd_3665_);
v___x_3692_ = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___boxed), 8, 3);
lean_closure_set(v___x_3692_, 0, lean_box(0));
lean_closure_set(v___x_3692_, 1, v_mctx_3686_);
lean_closure_set(v___x_3692_, 2, v___x_3691_);
v___x_3693_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v___x_3692_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_);
if (lean_obj_tag(v___x_3693_) == 0)
{
lean_object* v_a_3694_; lean_object* v___x_3695_; 
v_a_3694_ = lean_ctor_get(v___x_3693_, 0);
lean_inc(v_a_3694_);
lean_dec_ref_known(v___x_3693_, 1);
v___x_3695_ = lean_box(0);
if (lean_obj_tag(v_a_3694_) == 0)
{
lean_object* v___x_3697_; 
if (v_isShared_3679_ == 0)
{
v___x_3697_ = v___x_3678_;
goto v_reusejp_3696_;
}
else
{
lean_object* v_reuseFailAlloc_3702_; 
v_reuseFailAlloc_3702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3702_, 0, v_fst_3675_);
lean_ctor_set(v_reuseFailAlloc_3702_, 1, v_snd_3676_);
v___x_3697_ = v_reuseFailAlloc_3702_;
goto v_reusejp_3696_;
}
v_reusejp_3696_:
{
lean_object* v___x_3699_; 
if (v_isShared_3670_ == 0)
{
lean_ctor_set(v___x_3669_, 1, v___x_3697_);
lean_ctor_set(v___x_3669_, 0, v___x_3695_);
v___x_3699_ = v___x_3669_;
goto v_reusejp_3698_;
}
else
{
lean_object* v_reuseFailAlloc_3701_; 
v_reuseFailAlloc_3701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3701_, 0, v___x_3695_);
lean_ctor_set(v_reuseFailAlloc_3701_, 1, v___x_3697_);
v___x_3699_ = v_reuseFailAlloc_3701_;
goto v_reusejp_3698_;
}
v_reusejp_3698_:
{
v_as_x27_3652_ = v_tail_3662_;
v_b_3653_ = v___x_3699_;
goto _start;
}
}
}
else
{
lean_object* v_val_3703_; lean_object* v___x_3705_; uint8_t v_isShared_3706_; uint8_t v_isSharedCheck_3780_; 
v_val_3703_ = lean_ctor_get(v_a_3694_, 0);
v_isSharedCheck_3780_ = !lean_is_exclusive(v_a_3694_);
if (v_isSharedCheck_3780_ == 0)
{
v___x_3705_ = v_a_3694_;
v_isShared_3706_ = v_isSharedCheck_3780_;
goto v_resetjp_3704_;
}
else
{
lean_inc(v_val_3703_);
lean_dec(v_a_3694_);
v___x_3705_ = lean_box(0);
v_isShared_3706_ = v_isSharedCheck_3780_;
goto v_resetjp_3704_;
}
v_resetjp_3704_:
{
lean_object* v_result_3707_; lean_object* v_mctx_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; 
v_result_3707_ = lean_ctor_get(v_val_3703_, 2);
v_mctx_3708_ = lean_ctor_get(v_val_3703_, 3);
lean_inc(v_val_3703_);
v___x_3709_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult___boxed), 6, 1);
lean_closure_set(v___x_3709_, 0, v_val_3703_);
lean_inc_ref(v_mctx_3708_);
v___x_3710_ = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___boxed), 8, 3);
lean_closure_set(v___x_3710_, 0, lean_box(0));
lean_closure_set(v___x_3710_, 1, v_mctx_3708_);
lean_closure_set(v___x_3710_, 2, v___x_3709_);
v___x_3711_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v___x_3710_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_);
if (lean_obj_tag(v___x_3711_) == 0)
{
lean_object* v_a_3712_; uint8_t v___x_3713_; 
v_a_3712_ = lean_ctor_get(v___x_3711_, 0);
lean_inc(v_a_3712_);
lean_dec_ref_known(v___x_3711_, 1);
v___x_3713_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg(v_fst_3675_, v_a_3712_);
if (v___x_3713_ == 0)
{
lean_object* v_eNew_3714_; lean_object* v___x_3715_; 
v_eNew_3714_ = lean_ctor_get(v_result_3707_, 0);
lean_inc_ref(v_eNew_3714_);
lean_inc_ref(v_mctx_3708_);
v___x_3715_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(v_mctx_3708_, v_eNew_3714_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_);
if (lean_obj_tag(v___x_3715_) == 0)
{
if (v_stopAtRfl_3680_ == 0)
{
lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3720_; 
lean_dec_ref_known(v___x_3715_, 1);
lean_del_object(v___x_3705_);
v___x_3716_ = lean_box(0);
v___x_3717_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1___redArg(v_fst_3675_, v_a_3712_, v___x_3716_);
v___x_3718_ = lean_array_push(v_snd_3676_, v_val_3703_);
if (v_isShared_3679_ == 0)
{
lean_ctor_set(v___x_3678_, 1, v___x_3718_);
lean_ctor_set(v___x_3678_, 0, v___x_3717_);
v___x_3720_ = v___x_3678_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v___x_3717_);
lean_ctor_set(v_reuseFailAlloc_3725_, 1, v___x_3718_);
v___x_3720_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
lean_object* v___x_3722_; 
if (v_isShared_3670_ == 0)
{
lean_ctor_set(v___x_3669_, 1, v___x_3720_);
lean_ctor_set(v___x_3669_, 0, v___x_3695_);
v___x_3722_ = v___x_3669_;
goto v_reusejp_3721_;
}
else
{
lean_object* v_reuseFailAlloc_3724_; 
v_reuseFailAlloc_3724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3724_, 0, v___x_3695_);
lean_ctor_set(v_reuseFailAlloc_3724_, 1, v___x_3720_);
v___x_3722_ = v_reuseFailAlloc_3724_;
goto v_reusejp_3721_;
}
v_reusejp_3721_:
{
v_as_x27_3652_ = v_tail_3662_;
v_b_3653_ = v___x_3722_;
goto _start;
}
}
}
else
{
lean_object* v_a_3726_; lean_object* v___x_3728_; uint8_t v_isShared_3729_; uint8_t v_isSharedCheck_3756_; 
v_a_3726_ = lean_ctor_get(v___x_3715_, 0);
v_isSharedCheck_3756_ = !lean_is_exclusive(v___x_3715_);
if (v_isSharedCheck_3756_ == 0)
{
v___x_3728_ = v___x_3715_;
v_isShared_3729_ = v_isSharedCheck_3756_;
goto v_resetjp_3727_;
}
else
{
lean_inc(v_a_3726_);
lean_dec(v___x_3715_);
v___x_3728_ = lean_box(0);
v_isShared_3729_ = v_isSharedCheck_3756_;
goto v_resetjp_3727_;
}
v_resetjp_3727_:
{
uint8_t v___x_3730_; 
v___x_3730_ = lean_unbox(v_a_3726_);
lean_dec(v_a_3726_);
if (v___x_3730_ == 0)
{
lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3735_; 
lean_del_object(v___x_3728_);
lean_del_object(v___x_3705_);
v___x_3731_ = lean_box(0);
v___x_3732_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1___redArg(v_fst_3675_, v_a_3712_, v___x_3731_);
v___x_3733_ = lean_array_push(v_snd_3676_, v_val_3703_);
if (v_isShared_3679_ == 0)
{
lean_ctor_set(v___x_3678_, 1, v___x_3733_);
lean_ctor_set(v___x_3678_, 0, v___x_3732_);
v___x_3735_ = v___x_3678_;
goto v_reusejp_3734_;
}
else
{
lean_object* v_reuseFailAlloc_3740_; 
v_reuseFailAlloc_3740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3740_, 0, v___x_3732_);
lean_ctor_set(v_reuseFailAlloc_3740_, 1, v___x_3733_);
v___x_3735_ = v_reuseFailAlloc_3740_;
goto v_reusejp_3734_;
}
v_reusejp_3734_:
{
lean_object* v___x_3737_; 
if (v_isShared_3670_ == 0)
{
lean_ctor_set(v___x_3669_, 1, v___x_3735_);
lean_ctor_set(v___x_3669_, 0, v___x_3695_);
v___x_3737_ = v___x_3669_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v___x_3695_);
lean_ctor_set(v_reuseFailAlloc_3739_, 1, v___x_3735_);
v___x_3737_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3736_;
}
v_reusejp_3736_:
{
v_as_x27_3652_ = v_tail_3662_;
v_b_3653_ = v___x_3737_;
goto _start;
}
}
}
else
{
lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3745_; 
lean_dec(v_a_3712_);
lean_dec_ref(v_cfg_3651_);
v___x_3741_ = lean_unsigned_to_nat(1u);
v___x_3742_ = lean_mk_empty_array_with_capacity(v___x_3741_);
v___x_3743_ = lean_array_push(v___x_3742_, v_val_3703_);
if (v_isShared_3706_ == 0)
{
lean_ctor_set(v___x_3705_, 0, v___x_3743_);
v___x_3745_ = v___x_3705_;
goto v_reusejp_3744_;
}
else
{
lean_object* v_reuseFailAlloc_3755_; 
v_reuseFailAlloc_3755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3755_, 0, v___x_3743_);
v___x_3745_ = v_reuseFailAlloc_3755_;
goto v_reusejp_3744_;
}
v_reusejp_3744_:
{
lean_object* v___x_3747_; 
if (v_isShared_3679_ == 0)
{
v___x_3747_ = v___x_3678_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v_fst_3675_);
lean_ctor_set(v_reuseFailAlloc_3754_, 1, v_snd_3676_);
v___x_3747_ = v_reuseFailAlloc_3754_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
lean_object* v___x_3749_; 
if (v_isShared_3670_ == 0)
{
lean_ctor_set(v___x_3669_, 1, v___x_3747_);
lean_ctor_set(v___x_3669_, 0, v___x_3745_);
v___x_3749_ = v___x_3669_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v___x_3745_);
lean_ctor_set(v_reuseFailAlloc_3753_, 1, v___x_3747_);
v___x_3749_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
lean_object* v___x_3751_; 
if (v_isShared_3729_ == 0)
{
lean_ctor_set(v___x_3728_, 0, v___x_3749_);
v___x_3751_ = v___x_3728_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v___x_3749_);
v___x_3751_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3750_;
}
v_reusejp_3750_:
{
return v___x_3751_;
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
lean_object* v_a_3757_; lean_object* v___x_3759_; uint8_t v_isShared_3760_; uint8_t v_isSharedCheck_3764_; 
lean_dec(v_a_3712_);
lean_del_object(v___x_3705_);
lean_dec(v_val_3703_);
lean_del_object(v___x_3678_);
lean_dec(v_snd_3676_);
lean_dec(v_fst_3675_);
lean_del_object(v___x_3669_);
lean_dec_ref(v_cfg_3651_);
v_a_3757_ = lean_ctor_get(v___x_3715_, 0);
v_isSharedCheck_3764_ = !lean_is_exclusive(v___x_3715_);
if (v_isSharedCheck_3764_ == 0)
{
v___x_3759_ = v___x_3715_;
v_isShared_3760_ = v_isSharedCheck_3764_;
goto v_resetjp_3758_;
}
else
{
lean_inc(v_a_3757_);
lean_dec(v___x_3715_);
v___x_3759_ = lean_box(0);
v_isShared_3760_ = v_isSharedCheck_3764_;
goto v_resetjp_3758_;
}
v_resetjp_3758_:
{
lean_object* v___x_3762_; 
if (v_isShared_3760_ == 0)
{
v___x_3762_ = v___x_3759_;
goto v_reusejp_3761_;
}
else
{
lean_object* v_reuseFailAlloc_3763_; 
v_reuseFailAlloc_3763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3763_, 0, v_a_3757_);
v___x_3762_ = v_reuseFailAlloc_3763_;
goto v_reusejp_3761_;
}
v_reusejp_3761_:
{
return v___x_3762_;
}
}
}
}
else
{
lean_object* v___x_3766_; 
lean_dec(v_a_3712_);
lean_del_object(v___x_3705_);
lean_dec(v_val_3703_);
if (v_isShared_3679_ == 0)
{
v___x_3766_ = v___x_3678_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3771_; 
v_reuseFailAlloc_3771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3771_, 0, v_fst_3675_);
lean_ctor_set(v_reuseFailAlloc_3771_, 1, v_snd_3676_);
v___x_3766_ = v_reuseFailAlloc_3771_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
lean_object* v___x_3768_; 
if (v_isShared_3670_ == 0)
{
lean_ctor_set(v___x_3669_, 1, v___x_3766_);
lean_ctor_set(v___x_3669_, 0, v___x_3695_);
v___x_3768_ = v___x_3669_;
goto v_reusejp_3767_;
}
else
{
lean_object* v_reuseFailAlloc_3770_; 
v_reuseFailAlloc_3770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3770_, 0, v___x_3695_);
lean_ctor_set(v_reuseFailAlloc_3770_, 1, v___x_3766_);
v___x_3768_ = v_reuseFailAlloc_3770_;
goto v_reusejp_3767_;
}
v_reusejp_3767_:
{
v_as_x27_3652_ = v_tail_3662_;
v_b_3653_ = v___x_3768_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3772_; lean_object* v___x_3774_; uint8_t v_isShared_3775_; uint8_t v_isSharedCheck_3779_; 
lean_del_object(v___x_3705_);
lean_dec(v_val_3703_);
lean_del_object(v___x_3678_);
lean_dec(v_snd_3676_);
lean_dec(v_fst_3675_);
lean_del_object(v___x_3669_);
lean_dec_ref(v_cfg_3651_);
v_a_3772_ = lean_ctor_get(v___x_3711_, 0);
v_isSharedCheck_3779_ = !lean_is_exclusive(v___x_3711_);
if (v_isSharedCheck_3779_ == 0)
{
v___x_3774_ = v___x_3711_;
v_isShared_3775_ = v_isSharedCheck_3779_;
goto v_resetjp_3773_;
}
else
{
lean_inc(v_a_3772_);
lean_dec(v___x_3711_);
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
}
else
{
lean_object* v_a_3781_; lean_object* v___x_3783_; uint8_t v_isShared_3784_; uint8_t v_isSharedCheck_3788_; 
lean_del_object(v___x_3678_);
lean_dec(v_snd_3676_);
lean_dec(v_fst_3675_);
lean_del_object(v___x_3669_);
lean_dec_ref(v_cfg_3651_);
v_a_3781_ = lean_ctor_get(v___x_3693_, 0);
v_isSharedCheck_3788_ = !lean_is_exclusive(v___x_3693_);
if (v_isSharedCheck_3788_ == 0)
{
v___x_3783_ = v___x_3693_;
v_isShared_3784_ = v_isSharedCheck_3788_;
goto v_resetjp_3782_;
}
else
{
lean_inc(v_a_3781_);
lean_dec(v___x_3693_);
v___x_3783_ = lean_box(0);
v_isShared_3784_ = v_isSharedCheck_3788_;
goto v_resetjp_3782_;
}
v_resetjp_3782_:
{
lean_object* v___x_3786_; 
if (v_isShared_3784_ == 0)
{
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
return v___x_3786_;
}
}
}
}
else
{
lean_object* v___x_3789_; lean_object* v___x_3791_; 
lean_dec_ref(v_cfg_3651_);
lean_inc(v_snd_3676_);
v___x_3789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3789_, 0, v_snd_3676_);
if (v_isShared_3679_ == 0)
{
v___x_3791_ = v___x_3678_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v_fst_3675_);
lean_ctor_set(v_reuseFailAlloc_3798_, 1, v_snd_3676_);
v___x_3791_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3790_;
}
v_reusejp_3790_:
{
lean_object* v___x_3793_; 
if (v_isShared_3670_ == 0)
{
lean_ctor_set(v___x_3669_, 1, v___x_3791_);
lean_ctor_set(v___x_3669_, 0, v___x_3789_);
v___x_3793_ = v___x_3669_;
goto v_reusejp_3792_;
}
else
{
lean_object* v_reuseFailAlloc_3797_; 
v_reuseFailAlloc_3797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3797_, 0, v___x_3789_);
lean_ctor_set(v_reuseFailAlloc_3797_, 1, v___x_3791_);
v___x_3793_ = v_reuseFailAlloc_3797_;
goto v_reusejp_3792_;
}
v_reusejp_3792_:
{
lean_object* v___x_3795_; 
if (v_isShared_3674_ == 0)
{
lean_ctor_set(v___x_3673_, 0, v___x_3793_);
v___x_3795_ = v___x_3673_;
goto v_reusejp_3794_;
}
else
{
lean_object* v_reuseFailAlloc_3796_; 
v_reuseFailAlloc_3796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3796_, 0, v___x_3793_);
v___x_3795_ = v_reuseFailAlloc_3796_;
goto v_reusejp_3794_;
}
v_reusejp_3794_:
{
return v___x_3795_;
}
}
}
}
}
else
{
lean_object* v___x_3799_; lean_object* v___x_3801_; 
lean_dec_ref(v_cfg_3651_);
lean_inc(v_snd_3676_);
v___x_3799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3799_, 0, v_snd_3676_);
if (v_isShared_3679_ == 0)
{
v___x_3801_ = v___x_3678_;
goto v_reusejp_3800_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3808_, 0, v_fst_3675_);
lean_ctor_set(v_reuseFailAlloc_3808_, 1, v_snd_3676_);
v___x_3801_ = v_reuseFailAlloc_3808_;
goto v_reusejp_3800_;
}
v_reusejp_3800_:
{
lean_object* v___x_3803_; 
if (v_isShared_3670_ == 0)
{
lean_ctor_set(v___x_3669_, 1, v___x_3801_);
lean_ctor_set(v___x_3669_, 0, v___x_3799_);
v___x_3803_ = v___x_3669_;
goto v_reusejp_3802_;
}
else
{
lean_object* v_reuseFailAlloc_3807_; 
v_reuseFailAlloc_3807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3807_, 0, v___x_3799_);
lean_ctor_set(v_reuseFailAlloc_3807_, 1, v___x_3801_);
v___x_3803_ = v_reuseFailAlloc_3807_;
goto v_reusejp_3802_;
}
v_reusejp_3802_:
{
lean_object* v___x_3805_; 
if (v_isShared_3674_ == 0)
{
lean_ctor_set(v___x_3673_, 0, v___x_3803_);
v___x_3805_ = v___x_3673_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3806_; 
v_reuseFailAlloc_3806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3806_, 0, v___x_3803_);
v___x_3805_ = v_reuseFailAlloc_3806_;
goto v_reusejp_3804_;
}
v_reusejp_3804_:
{
return v___x_3805_;
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
lean_object* v_a_3813_; lean_object* v___x_3815_; uint8_t v_isShared_3816_; uint8_t v_isSharedCheck_3820_; 
lean_dec_ref(v_b_3653_);
lean_dec_ref(v_cfg_3651_);
v_a_3813_ = lean_ctor_get(v___x_3666_, 0);
v_isSharedCheck_3820_ = !lean_is_exclusive(v___x_3666_);
if (v_isSharedCheck_3820_ == 0)
{
v___x_3815_ = v___x_3666_;
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
else
{
lean_inc(v_a_3813_);
lean_dec(v___x_3666_);
v___x_3815_ = lean_box(0);
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
v_resetjp_3814_:
{
lean_object* v___x_3818_; 
if (v_isShared_3816_ == 0)
{
v___x_3818_ = v___x_3815_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v_a_3813_);
v___x_3818_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3817_;
}
v_reusejp_3817_:
{
return v___x_3818_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg___boxed(lean_object* v_cfg_3821_, lean_object* v_as_x27_3822_, lean_object* v_b_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_){
_start:
{
lean_object* v_res_3829_; 
v_res_3829_ = l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg(v_cfg_3821_, v_as_x27_3822_, v_b_3823_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_);
lean_dec(v___y_3827_);
lean_dec_ref(v___y_3826_);
lean_dec(v___y_3825_);
lean_dec_ref(v___y_3824_);
lean_dec(v_as_x27_3822_);
return v_res_3829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_takeListAux(lean_object* v_cfg_3830_, lean_object* v_seen_3831_, lean_object* v_acc_3832_, lean_object* v_xs_3833_, lean_object* v_a_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_, lean_object* v_a_3837_){
_start:
{
lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; 
v___x_3839_ = lean_box(0);
v___x_3840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3840_, 0, v_seen_3831_);
lean_ctor_set(v___x_3840_, 1, v_acc_3832_);
v___x_3841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3841_, 0, v___x_3839_);
lean_ctor_set(v___x_3841_, 1, v___x_3840_);
v___x_3842_ = l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg(v_cfg_3830_, v_xs_3833_, v___x_3841_, v_a_3834_, v_a_3835_, v_a_3836_, v_a_3837_);
if (lean_obj_tag(v___x_3842_) == 0)
{
lean_object* v_a_3843_; lean_object* v___x_3845_; uint8_t v_isShared_3846_; uint8_t v_isSharedCheck_3857_; 
v_a_3843_ = lean_ctor_get(v___x_3842_, 0);
v_isSharedCheck_3857_ = !lean_is_exclusive(v___x_3842_);
if (v_isSharedCheck_3857_ == 0)
{
v___x_3845_ = v___x_3842_;
v_isShared_3846_ = v_isSharedCheck_3857_;
goto v_resetjp_3844_;
}
else
{
lean_inc(v_a_3843_);
lean_dec(v___x_3842_);
v___x_3845_ = lean_box(0);
v_isShared_3846_ = v_isSharedCheck_3857_;
goto v_resetjp_3844_;
}
v_resetjp_3844_:
{
lean_object* v_fst_3847_; 
v_fst_3847_ = lean_ctor_get(v_a_3843_, 0);
if (lean_obj_tag(v_fst_3847_) == 0)
{
lean_object* v_snd_3848_; lean_object* v_snd_3849_; lean_object* v___x_3851_; 
v_snd_3848_ = lean_ctor_get(v_a_3843_, 1);
lean_inc(v_snd_3848_);
lean_dec(v_a_3843_);
v_snd_3849_ = lean_ctor_get(v_snd_3848_, 1);
lean_inc(v_snd_3849_);
lean_dec(v_snd_3848_);
if (v_isShared_3846_ == 0)
{
lean_ctor_set(v___x_3845_, 0, v_snd_3849_);
v___x_3851_ = v___x_3845_;
goto v_reusejp_3850_;
}
else
{
lean_object* v_reuseFailAlloc_3852_; 
v_reuseFailAlloc_3852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3852_, 0, v_snd_3849_);
v___x_3851_ = v_reuseFailAlloc_3852_;
goto v_reusejp_3850_;
}
v_reusejp_3850_:
{
return v___x_3851_;
}
}
else
{
lean_object* v_val_3853_; lean_object* v___x_3855_; 
lean_inc_ref(v_fst_3847_);
lean_dec(v_a_3843_);
v_val_3853_ = lean_ctor_get(v_fst_3847_, 0);
lean_inc(v_val_3853_);
lean_dec_ref_known(v_fst_3847_, 1);
if (v_isShared_3846_ == 0)
{
lean_ctor_set(v___x_3845_, 0, v_val_3853_);
v___x_3855_ = v___x_3845_;
goto v_reusejp_3854_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v_val_3853_);
v___x_3855_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3854_;
}
v_reusejp_3854_:
{
return v___x_3855_;
}
}
}
}
else
{
lean_object* v_a_3858_; lean_object* v___x_3860_; uint8_t v_isShared_3861_; uint8_t v_isSharedCheck_3865_; 
v_a_3858_ = lean_ctor_get(v___x_3842_, 0);
v_isSharedCheck_3865_ = !lean_is_exclusive(v___x_3842_);
if (v_isSharedCheck_3865_ == 0)
{
v___x_3860_ = v___x_3842_;
v_isShared_3861_ = v_isSharedCheck_3865_;
goto v_resetjp_3859_;
}
else
{
lean_inc(v_a_3858_);
lean_dec(v___x_3842_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_takeListAux___boxed(lean_object* v_cfg_3866_, lean_object* v_seen_3867_, lean_object* v_acc_3868_, lean_object* v_xs_3869_, lean_object* v_a_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_, lean_object* v_a_3873_, lean_object* v_a_3874_){
_start:
{
lean_object* v_res_3875_; 
v_res_3875_ = l_Lean_Meta_Rewrites_takeListAux(v_cfg_3866_, v_seen_3867_, v_acc_3868_, v_xs_3869_, v_a_3870_, v_a_3871_, v_a_3872_, v_a_3873_);
lean_dec(v_a_3873_);
lean_dec_ref(v_a_3872_);
lean_dec(v_a_3871_);
lean_dec_ref(v_a_3870_);
lean_dec(v_xs_3869_);
return v_res_3875_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0(lean_object* v_00_u03b2_3876_, lean_object* v_m_3877_, lean_object* v_a_3878_){
_start:
{
uint8_t v___x_3879_; 
v___x_3879_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg(v_m_3877_, v_a_3878_);
return v___x_3879_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___boxed(lean_object* v_00_u03b2_3880_, lean_object* v_m_3881_, lean_object* v_a_3882_){
_start:
{
uint8_t v_res_3883_; lean_object* v_r_3884_; 
v_res_3883_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0(v_00_u03b2_3880_, v_m_3881_, v_a_3882_);
lean_dec_ref(v_a_3882_);
lean_dec_ref(v_m_3881_);
v_r_3884_ = lean_box(v_res_3883_);
return v_r_3884_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1(lean_object* v_00_u03b2_3885_, lean_object* v_m_3886_, lean_object* v_a_3887_, lean_object* v_b_3888_){
_start:
{
lean_object* v___x_3889_; 
v___x_3889_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1___redArg(v_m_3886_, v_a_3887_, v_b_3888_);
return v___x_3889_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2(lean_object* v_cfg_3890_, lean_object* v_as_3891_, lean_object* v_as_x27_3892_, lean_object* v_b_3893_, lean_object* v_a_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_){
_start:
{
lean_object* v___x_3900_; 
v___x_3900_ = l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg(v_cfg_3890_, v_as_x27_3892_, v_b_3893_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_);
return v___x_3900_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___boxed(lean_object* v_cfg_3901_, lean_object* v_as_3902_, lean_object* v_as_x27_3903_, lean_object* v_b_3904_, lean_object* v_a_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_){
_start:
{
lean_object* v_res_3911_; 
v_res_3911_ = l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2(v_cfg_3901_, v_as_3902_, v_as_x27_3903_, v_b_3904_, v_a_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_);
lean_dec(v___y_3909_);
lean_dec_ref(v___y_3908_);
lean_dec(v___y_3907_);
lean_dec_ref(v___y_3906_);
lean_dec(v_as_x27_3903_);
lean_dec(v_as_3902_);
return v_res_3911_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0(lean_object* v_00_u03b2_3912_, lean_object* v_a_3913_, lean_object* v_x_3914_){
_start:
{
uint8_t v___x_3915_; 
v___x_3915_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(v_a_3913_, v_x_3914_);
return v___x_3915_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3916_, lean_object* v_a_3917_, lean_object* v_x_3918_){
_start:
{
uint8_t v_res_3919_; lean_object* v_r_3920_; 
v_res_3919_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0(v_00_u03b2_3916_, v_a_3917_, v_x_3918_);
lean_dec(v_x_3918_);
lean_dec_ref(v_a_3917_);
v_r_3920_ = lean_box(v_res_3919_);
return v_r_3920_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2(lean_object* v_00_u03b2_3921_, lean_object* v_data_3922_){
_start:
{
lean_object* v___x_3923_; 
v___x_3923_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2___redArg(v_data_3922_);
return v___x_3923_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3(lean_object* v_00_u03b2_3924_, lean_object* v_a_3925_, lean_object* v_b_3926_, lean_object* v_x_3927_){
_start:
{
lean_object* v___x_3928_; 
v___x_3928_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3___redArg(v_a_3925_, v_b_3926_, v_x_3927_);
return v___x_3928_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_3929_, lean_object* v_i_3930_, lean_object* v_source_3931_, lean_object* v_target_3932_){
_start:
{
lean_object* v___x_3933_; 
v___x_3933_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3___redArg(v_i_3930_, v_source_3931_, v_target_3932_);
return v___x_3933_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_3934_, lean_object* v_x_3935_, lean_object* v_x_3936_){
_start:
{
lean_object* v___x_3937_; 
v___x_3937_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3_spec__5___redArg(v_x_3935_, v_x_3936_);
return v___x_3937_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_findRewrites___closed__0(void){
_start:
{
lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; 
v___x_3938_ = lean_box(0);
v___x_3939_ = lean_unsigned_to_nat(16u);
v___x_3940_ = lean_mk_array(v___x_3939_, v___x_3938_);
return v___x_3940_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_findRewrites___closed__1(void){
_start:
{
lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; 
v___x_3941_ = lean_obj_once(&l_Lean_Meta_Rewrites_findRewrites___closed__0, &l_Lean_Meta_Rewrites_findRewrites___closed__0_once, _init_l_Lean_Meta_Rewrites_findRewrites___closed__0);
v___x_3942_ = lean_unsigned_to_nat(0u);
v___x_3943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3943_, 0, v___x_3942_);
lean_ctor_set(v___x_3943_, 1, v___x_3941_);
return v___x_3943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_findRewrites(lean_object* v_hyps_3944_, lean_object* v_moduleRef_3945_, lean_object* v_goal_3946_, lean_object* v_target_3947_, lean_object* v_forbidden_3948_, uint8_t v_side_3949_, uint8_t v_stopAtRfl_3950_, lean_object* v_max_3951_, lean_object* v_leavePercentHeartbeats_3952_, lean_object* v_a_3953_, lean_object* v_a_3954_, lean_object* v_a_3955_, lean_object* v_a_3956_){
_start:
{
lean_object* v___x_3958_; lean_object* v___x_3959_; 
v___x_3958_ = lean_st_ref_get(v_a_3954_);
lean_inc_ref(v_target_3947_);
v___x_3959_ = l_Lean_Meta_Rewrites_rewriteCandidates(v_hyps_3944_, v_moduleRef_3945_, v_target_3947_, v_forbidden_3948_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_);
if (lean_obj_tag(v___x_3959_) == 0)
{
lean_object* v_a_3960_; lean_object* v___x_3961_; 
v_a_3960_ = lean_ctor_get(v___x_3959_, 0);
lean_inc(v_a_3960_);
lean_dec_ref_known(v___x_3959_, 1);
v___x_3961_ = l_Lean_getMaxHeartbeats___redArg(v_a_3955_);
if (lean_obj_tag(v___x_3961_) == 0)
{
lean_object* v_a_3962_; lean_object* v_mctx_3963_; lean_object* v_minHeartbeats_3965_; lean_object* v___y_3966_; lean_object* v___y_3967_; lean_object* v___y_3968_; lean_object* v___y_3969_; lean_object* v___x_3992_; uint8_t v___x_3993_; 
v_a_3962_ = lean_ctor_get(v___x_3961_, 0);
lean_inc(v_a_3962_);
lean_dec_ref_known(v___x_3961_, 1);
v_mctx_3963_ = lean_ctor_get(v___x_3958_, 0);
lean_inc_ref(v_mctx_3963_);
lean_dec(v___x_3958_);
v___x_3992_ = lean_unsigned_to_nat(0u);
v___x_3993_ = lean_nat_dec_eq(v_a_3962_, v___x_3992_);
lean_dec(v_a_3962_);
if (v___x_3993_ == 0)
{
lean_object* v___x_3994_; 
v___x_3994_ = l_Lean_getRemainingHeartbeats___redArg(v_a_3955_);
if (lean_obj_tag(v___x_3994_) == 0)
{
lean_object* v_a_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; 
v_a_3995_ = lean_ctor_get(v___x_3994_, 0);
lean_inc(v_a_3995_);
lean_dec_ref_known(v___x_3994_, 1);
v___x_3996_ = lean_nat_mul(v_leavePercentHeartbeats_3952_, v_a_3995_);
lean_dec(v_a_3995_);
v___x_3997_ = lean_unsigned_to_nat(100u);
v___x_3998_ = lean_nat_div(v___x_3996_, v___x_3997_);
lean_dec(v___x_3996_);
v_minHeartbeats_3965_ = v___x_3998_;
v___y_3966_ = v_a_3953_;
v___y_3967_ = v_a_3954_;
v___y_3968_ = v_a_3955_;
v___y_3969_ = v_a_3956_;
goto v___jp_3964_;
}
else
{
lean_object* v_a_3999_; lean_object* v___x_4001_; uint8_t v_isShared_4002_; uint8_t v_isSharedCheck_4006_; 
lean_dec_ref(v_mctx_3963_);
lean_dec(v_a_3960_);
lean_dec(v_max_3951_);
lean_dec_ref(v_target_3947_);
lean_dec(v_goal_3946_);
v_a_3999_ = lean_ctor_get(v___x_3994_, 0);
v_isSharedCheck_4006_ = !lean_is_exclusive(v___x_3994_);
if (v_isSharedCheck_4006_ == 0)
{
v___x_4001_ = v___x_3994_;
v_isShared_4002_ = v_isSharedCheck_4006_;
goto v_resetjp_4000_;
}
else
{
lean_inc(v_a_3999_);
lean_dec(v___x_3994_);
v___x_4001_ = lean_box(0);
v_isShared_4002_ = v_isSharedCheck_4006_;
goto v_resetjp_4000_;
}
v_resetjp_4000_:
{
lean_object* v___x_4004_; 
if (v_isShared_4002_ == 0)
{
v___x_4004_ = v___x_4001_;
goto v_reusejp_4003_;
}
else
{
lean_object* v_reuseFailAlloc_4005_; 
v_reuseFailAlloc_4005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4005_, 0, v_a_3999_);
v___x_4004_ = v_reuseFailAlloc_4005_;
goto v_reusejp_4003_;
}
v_reusejp_4003_:
{
return v___x_4004_;
}
}
}
}
else
{
v_minHeartbeats_3965_ = v___x_3992_;
v___y_3966_ = v_a_3953_;
v___y_3967_ = v_a_3954_;
v___y_3968_ = v_a_3955_;
v___y_3969_ = v_a_3956_;
goto v___jp_3964_;
}
v___jp_3964_:
{
lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; 
lean_inc(v_max_3951_);
v___x_3970_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_3970_, 0, v_max_3951_);
lean_ctor_set(v___x_3970_, 1, v_minHeartbeats_3965_);
lean_ctor_set(v___x_3970_, 2, v_goal_3946_);
lean_ctor_set(v___x_3970_, 3, v_target_3947_);
lean_ctor_set(v___x_3970_, 4, v_mctx_3963_);
lean_ctor_set_uint8(v___x_3970_, sizeof(void*)*5, v_stopAtRfl_3950_);
lean_ctor_set_uint8(v___x_3970_, sizeof(void*)*5 + 1, v_side_3949_);
v___x_3971_ = lean_obj_once(&l_Lean_Meta_Rewrites_findRewrites___closed__1, &l_Lean_Meta_Rewrites_findRewrites___closed__1_once, _init_l_Lean_Meta_Rewrites_findRewrites___closed__1);
v___x_3972_ = lean_mk_empty_array_with_capacity(v_max_3951_);
lean_dec(v_max_3951_);
v___x_3973_ = lean_array_to_list(v_a_3960_);
v___x_3974_ = l_Lean_Meta_Rewrites_takeListAux(v___x_3970_, v___x_3971_, v___x_3972_, v___x_3973_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_);
lean_dec(v___x_3973_);
if (lean_obj_tag(v___x_3974_) == 0)
{
lean_object* v_a_3975_; lean_object* v___x_3977_; uint8_t v_isShared_3978_; uint8_t v_isSharedCheck_3983_; 
v_a_3975_ = lean_ctor_get(v___x_3974_, 0);
v_isSharedCheck_3983_ = !lean_is_exclusive(v___x_3974_);
if (v_isSharedCheck_3983_ == 0)
{
v___x_3977_ = v___x_3974_;
v_isShared_3978_ = v_isSharedCheck_3983_;
goto v_resetjp_3976_;
}
else
{
lean_inc(v_a_3975_);
lean_dec(v___x_3974_);
v___x_3977_ = lean_box(0);
v_isShared_3978_ = v_isSharedCheck_3983_;
goto v_resetjp_3976_;
}
v_resetjp_3976_:
{
lean_object* v___x_3979_; lean_object* v___x_3981_; 
v___x_3979_ = lean_array_to_list(v_a_3975_);
if (v_isShared_3978_ == 0)
{
lean_ctor_set(v___x_3977_, 0, v___x_3979_);
v___x_3981_ = v___x_3977_;
goto v_reusejp_3980_;
}
else
{
lean_object* v_reuseFailAlloc_3982_; 
v_reuseFailAlloc_3982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3982_, 0, v___x_3979_);
v___x_3981_ = v_reuseFailAlloc_3982_;
goto v_reusejp_3980_;
}
v_reusejp_3980_:
{
return v___x_3981_;
}
}
}
else
{
lean_object* v_a_3984_; lean_object* v___x_3986_; uint8_t v_isShared_3987_; uint8_t v_isSharedCheck_3991_; 
v_a_3984_ = lean_ctor_get(v___x_3974_, 0);
v_isSharedCheck_3991_ = !lean_is_exclusive(v___x_3974_);
if (v_isSharedCheck_3991_ == 0)
{
v___x_3986_ = v___x_3974_;
v_isShared_3987_ = v_isSharedCheck_3991_;
goto v_resetjp_3985_;
}
else
{
lean_inc(v_a_3984_);
lean_dec(v___x_3974_);
v___x_3986_ = lean_box(0);
v_isShared_3987_ = v_isSharedCheck_3991_;
goto v_resetjp_3985_;
}
v_resetjp_3985_:
{
lean_object* v___x_3989_; 
if (v_isShared_3987_ == 0)
{
v___x_3989_ = v___x_3986_;
goto v_reusejp_3988_;
}
else
{
lean_object* v_reuseFailAlloc_3990_; 
v_reuseFailAlloc_3990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3990_, 0, v_a_3984_);
v___x_3989_ = v_reuseFailAlloc_3990_;
goto v_reusejp_3988_;
}
v_reusejp_3988_:
{
return v___x_3989_;
}
}
}
}
}
else
{
lean_object* v_a_4007_; lean_object* v___x_4009_; uint8_t v_isShared_4010_; uint8_t v_isSharedCheck_4014_; 
lean_dec(v_a_3960_);
lean_dec(v___x_3958_);
lean_dec(v_max_3951_);
lean_dec_ref(v_target_3947_);
lean_dec(v_goal_3946_);
v_a_4007_ = lean_ctor_get(v___x_3961_, 0);
v_isSharedCheck_4014_ = !lean_is_exclusive(v___x_3961_);
if (v_isSharedCheck_4014_ == 0)
{
v___x_4009_ = v___x_3961_;
v_isShared_4010_ = v_isSharedCheck_4014_;
goto v_resetjp_4008_;
}
else
{
lean_inc(v_a_4007_);
lean_dec(v___x_3961_);
v___x_4009_ = lean_box(0);
v_isShared_4010_ = v_isSharedCheck_4014_;
goto v_resetjp_4008_;
}
v_resetjp_4008_:
{
lean_object* v___x_4012_; 
if (v_isShared_4010_ == 0)
{
v___x_4012_ = v___x_4009_;
goto v_reusejp_4011_;
}
else
{
lean_object* v_reuseFailAlloc_4013_; 
v_reuseFailAlloc_4013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4013_, 0, v_a_4007_);
v___x_4012_ = v_reuseFailAlloc_4013_;
goto v_reusejp_4011_;
}
v_reusejp_4011_:
{
return v___x_4012_;
}
}
}
}
else
{
lean_object* v_a_4015_; lean_object* v___x_4017_; uint8_t v_isShared_4018_; uint8_t v_isSharedCheck_4022_; 
lean_dec(v___x_3958_);
lean_dec(v_max_3951_);
lean_dec_ref(v_target_3947_);
lean_dec(v_goal_3946_);
v_a_4015_ = lean_ctor_get(v___x_3959_, 0);
v_isSharedCheck_4022_ = !lean_is_exclusive(v___x_3959_);
if (v_isSharedCheck_4022_ == 0)
{
v___x_4017_ = v___x_3959_;
v_isShared_4018_ = v_isSharedCheck_4022_;
goto v_resetjp_4016_;
}
else
{
lean_inc(v_a_4015_);
lean_dec(v___x_3959_);
v___x_4017_ = lean_box(0);
v_isShared_4018_ = v_isSharedCheck_4022_;
goto v_resetjp_4016_;
}
v_resetjp_4016_:
{
lean_object* v___x_4020_; 
if (v_isShared_4018_ == 0)
{
v___x_4020_ = v___x_4017_;
goto v_reusejp_4019_;
}
else
{
lean_object* v_reuseFailAlloc_4021_; 
v_reuseFailAlloc_4021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4021_, 0, v_a_4015_);
v___x_4020_ = v_reuseFailAlloc_4021_;
goto v_reusejp_4019_;
}
v_reusejp_4019_:
{
return v___x_4020_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_findRewrites___boxed(lean_object* v_hyps_4023_, lean_object* v_moduleRef_4024_, lean_object* v_goal_4025_, lean_object* v_target_4026_, lean_object* v_forbidden_4027_, lean_object* v_side_4028_, lean_object* v_stopAtRfl_4029_, lean_object* v_max_4030_, lean_object* v_leavePercentHeartbeats_4031_, lean_object* v_a_4032_, lean_object* v_a_4033_, lean_object* v_a_4034_, lean_object* v_a_4035_, lean_object* v_a_4036_){
_start:
{
uint8_t v_side_boxed_4037_; uint8_t v_stopAtRfl_boxed_4038_; lean_object* v_res_4039_; 
v_side_boxed_4037_ = lean_unbox(v_side_4028_);
v_stopAtRfl_boxed_4038_ = lean_unbox(v_stopAtRfl_4029_);
v_res_4039_ = l_Lean_Meta_Rewrites_findRewrites(v_hyps_4023_, v_moduleRef_4024_, v_goal_4025_, v_target_4026_, v_forbidden_4027_, v_side_boxed_4037_, v_stopAtRfl_boxed_4038_, v_max_4030_, v_leavePercentHeartbeats_4031_, v_a_4032_, v_a_4033_, v_a_4034_, v_a_4035_);
lean_dec(v_a_4035_);
lean_dec_ref(v_a_4034_);
lean_dec(v_a_4033_);
lean_dec_ref(v_a_4032_);
lean_dec(v_leavePercentHeartbeats_4031_);
lean_dec(v_forbidden_4027_);
return v_res_4039_;
}
}
lean_object* runtime_initialize_Lean_Meta_LazyDiscrTree(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Rewrite(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Refl(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_SolveByElim(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_Heartbeats(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Rewrites(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_LazyDiscrTree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Refl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_SolveByElim(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_TryThis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_Heartbeats(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Rewrites_forwardWeight = _init_l_Lean_Meta_Rewrites_forwardWeight();
lean_mark_persistent(l_Lean_Meta_Rewrites_forwardWeight);
l_Lean_Meta_Rewrites_backwardWeight = _init_l_Lean_Meta_Rewrites_backwardWeight();
lean_mark_persistent(l_Lean_Meta_Rewrites_backwardWeight);
res = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_1824551397____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_ext = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_ext);
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_constantsPerImportTask = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_constantsPerImportTask();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_constantsPerImportTask);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Rewrites(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_LazyDiscrTree(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Rewrite(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Refl(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_SolveByElim(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin);
lean_object* initialize_Lean_Util_Heartbeats(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Rewrites(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_LazyDiscrTree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Refl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_SolveByElim(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_TryThis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Heartbeats(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Rewrites(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Rewrites(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Rewrites(builtin);
}
#ifdef __cplusplus
}
#endif

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
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
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
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
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
lean_object* v_keyedConfig_444_; uint8_t v_trackZetaDelta_445_; lean_object* v_zetaDeltaSet_446_; lean_object* v_lctx_447_; lean_object* v_localInstances_448_; lean_object* v_defEqCtx_x3f_449_; lean_object* v_synthPendingDepth_450_; lean_object* v_customCanUnfoldPredicate_x3f_451_; uint8_t v_univApprox_452_; uint8_t v_inTypeClassResolution_453_; uint8_t v_cacheInferType_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_463_; 
v_keyedConfig_444_ = lean_ctor_get(v___y_439_, 0);
v_trackZetaDelta_445_ = lean_ctor_get_uint8(v___y_439_, sizeof(void*)*7);
v_zetaDeltaSet_446_ = lean_ctor_get(v___y_439_, 1);
v_lctx_447_ = lean_ctor_get(v___y_439_, 2);
v_localInstances_448_ = lean_ctor_get(v___y_439_, 3);
v_defEqCtx_x3f_449_ = lean_ctor_get(v___y_439_, 4);
v_synthPendingDepth_450_ = lean_ctor_get(v___y_439_, 5);
v_customCanUnfoldPredicate_x3f_451_ = lean_ctor_get(v___y_439_, 6);
v_univApprox_452_ = lean_ctor_get_uint8(v___y_439_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_453_ = lean_ctor_get_uint8(v___y_439_, sizeof(void*)*7 + 2);
v_cacheInferType_454_ = lean_ctor_get_uint8(v___y_439_, sizeof(void*)*7 + 3);
v_isSharedCheck_463_ = !lean_is_exclusive(v___y_439_);
if (v_isSharedCheck_463_ == 0)
{
v___x_456_ = v___y_439_;
v_isShared_457_ = v_isSharedCheck_463_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_451_);
lean_inc(v_synthPendingDepth_450_);
lean_inc(v_defEqCtx_x3f_449_);
lean_inc(v_localInstances_448_);
lean_inc(v_lctx_447_);
lean_inc(v_zetaDeltaSet_446_);
lean_inc(v_keyedConfig_444_);
lean_dec(v___y_439_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_463_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_458_; lean_object* v___x_460_; 
v___x_458_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_435_, v_keyedConfig_444_);
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 0, v___x_458_);
v___x_460_ = v___x_456_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v___x_458_);
lean_ctor_set(v_reuseFailAlloc_462_, 1, v_zetaDeltaSet_446_);
lean_ctor_set(v_reuseFailAlloc_462_, 2, v_lctx_447_);
lean_ctor_set(v_reuseFailAlloc_462_, 3, v_localInstances_448_);
lean_ctor_set(v_reuseFailAlloc_462_, 4, v_defEqCtx_x3f_449_);
lean_ctor_set(v_reuseFailAlloc_462_, 5, v_synthPendingDepth_450_);
lean_ctor_set(v_reuseFailAlloc_462_, 6, v_customCanUnfoldPredicate_x3f_451_);
lean_ctor_set_uint8(v_reuseFailAlloc_462_, sizeof(void*)*7, v_trackZetaDelta_445_);
lean_ctor_set_uint8(v_reuseFailAlloc_462_, sizeof(void*)*7 + 1, v_univApprox_452_);
lean_ctor_set_uint8(v_reuseFailAlloc_462_, sizeof(void*)*7 + 2, v_inTypeClassResolution_453_);
lean_ctor_set_uint8(v_reuseFailAlloc_462_, sizeof(void*)*7 + 3, v_cacheInferType_454_);
v___x_460_ = v_reuseFailAlloc_462_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
lean_object* v___x_461_; 
v___x_461_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg(v_type_436_, v___f_437_, v___x_438_, v___x_438_, v___x_460_, v___y_440_, v___y_441_, v___y_442_);
lean_dec_ref(v___x_460_);
return v___x_461_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__1___boxed(lean_object* v___x_464_, lean_object* v_type_465_, lean_object* v___f_466_, lean_object* v___x_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_){
_start:
{
uint8_t v___x_6864__boxed_473_; uint8_t v___x_6866__boxed_474_; lean_object* v_res_475_; 
v___x_6864__boxed_473_ = lean_unbox(v___x_464_);
v___x_6866__boxed_474_ = lean_unbox(v___x_467_);
v_res_475_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__1(v___x_6864__boxed_473_, v_type_465_, v___f_466_, v___x_6866__boxed_474_, v___y_468_, v___y_469_, v___y_470_, v___y_471_);
lean_dec(v___y_471_);
lean_dec_ref(v___y_470_);
lean_dec(v___y_469_);
return v_res_475_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__1(void){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__0));
v___x_478_ = lean_string_utf8_byte_size(v___x_477_);
return v___x_478_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__5(void){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__4));
v___x_483_ = lean_string_utf8_byte_size(v___x_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport(lean_object* v_name_484_, lean_object* v_c_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_){
_start:
{
uint8_t v___x_491_; 
lean_inc_ref(v_c_485_);
v___x_491_ = l_Lean_AsyncConstantInfo_isUnsafe(v_c_485_);
if (v___x_491_ == 0)
{
lean_object* v___x_492_; lean_object* v_env_496_; uint8_t v___x_497_; 
v___x_492_ = lean_st_ref_get(v_a_489_);
v_env_496_ = lean_ctor_get(v___x_492_, 0);
lean_inc_ref(v_env_496_);
lean_dec(v___x_492_);
lean_inc(v_name_484_);
v___x_497_ = l_Lean_Meta_allowCompletion(v_env_496_, v_name_484_);
if (v___x_497_ == 0)
{
lean_dec_ref(v_c_485_);
lean_dec(v_name_484_);
goto v___jp_493_;
}
else
{
if (v___x_491_ == 0)
{
lean_object* v___x_498_; lean_object* v_env_502_; uint8_t v___x_503_; 
v___x_498_ = lean_st_ref_get(v_a_489_);
v_env_502_ = lean_ctor_get(v___x_498_, 0);
lean_inc_ref(v_env_502_);
lean_dec(v___x_498_);
lean_inc(v_name_484_);
v___x_503_ = l_Lean_Linter_isDeprecated(v_env_502_, v_name_484_);
if (v___x_503_ == 0)
{
lean_object* v___f_504_; lean_object* v___y_506_; lean_object* v___y_507_; lean_object* v___y_508_; lean_object* v___y_509_; 
lean_inc(v_name_484_);
v___f_504_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___boxed), 8, 1);
lean_closure_set(v___f_504_, 0, v_name_484_);
if (lean_obj_tag(v_name_484_) == 1)
{
lean_object* v_str_520_; uint8_t v___y_522_; lean_object* v___x_530_; uint8_t v___x_531_; 
v_str_520_ = lean_ctor_get(v_name_484_, 1);
v___x_530_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__2));
v___x_531_ = lean_string_dec_eq(v_str_520_, v___x_530_);
if (v___x_531_ == 0)
{
lean_object* v___x_532_; uint8_t v___x_533_; 
v___x_532_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__3));
v___x_533_ = lean_string_dec_eq(v_str_520_, v___x_532_);
if (v___x_533_ == 0)
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; uint8_t v___x_537_; 
v___x_534_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__4));
v___x_535_ = lean_string_utf8_byte_size(v_str_520_);
v___x_536_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__5, &l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__5_once, _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__5);
v___x_537_ = lean_nat_dec_le(v___x_536_, v___x_535_);
if (v___x_537_ == 0)
{
v___y_522_ = v___x_503_;
goto v___jp_521_;
}
else
{
lean_object* v___x_538_; lean_object* v___x_539_; uint8_t v___x_540_; 
v___x_538_ = lean_unsigned_to_nat(0u);
v___x_539_ = lean_nat_sub(v___x_535_, v___x_536_);
v___x_540_ = lean_string_memcmp(v_str_520_, v___x_534_, v___x_539_, v___x_538_, v___x_536_);
lean_dec(v___x_539_);
v___y_522_ = v___x_540_;
goto v___jp_521_;
}
}
else
{
lean_dec_ref_known(v_name_484_, 2);
lean_dec_ref(v___f_504_);
lean_dec_ref(v_c_485_);
goto v___jp_499_;
}
}
else
{
lean_dec_ref_known(v_name_484_, 2);
lean_dec_ref(v___f_504_);
lean_dec_ref(v_c_485_);
goto v___jp_499_;
}
v___jp_521_:
{
if (v___y_522_ == 0)
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; uint8_t v___x_526_; 
v___x_523_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__0));
v___x_524_ = lean_string_utf8_byte_size(v_str_520_);
v___x_525_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__1, &l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__1_once, _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__1);
v___x_526_ = lean_nat_dec_le(v___x_525_, v___x_524_);
if (v___x_526_ == 0)
{
v___y_506_ = v_a_486_;
v___y_507_ = v_a_487_;
v___y_508_ = v_a_488_;
v___y_509_ = v_a_489_;
goto v___jp_505_;
}
else
{
lean_object* v___x_527_; lean_object* v___x_528_; uint8_t v___x_529_; 
v___x_527_ = lean_unsigned_to_nat(0u);
v___x_528_ = lean_nat_sub(v___x_524_, v___x_525_);
v___x_529_ = lean_string_memcmp(v_str_520_, v___x_523_, v___x_528_, v___x_527_, v___x_525_);
lean_dec(v___x_528_);
if (v___x_529_ == 0)
{
v___y_506_ = v_a_486_;
v___y_507_ = v_a_487_;
v___y_508_ = v_a_488_;
v___y_509_ = v_a_489_;
goto v___jp_505_;
}
else
{
lean_dec_ref_known(v_name_484_, 2);
lean_dec_ref(v___f_504_);
lean_dec_ref(v_c_485_);
goto v___jp_499_;
}
}
}
else
{
lean_dec_ref_known(v_name_484_, 2);
lean_dec_ref(v___f_504_);
lean_dec_ref(v_c_485_);
goto v___jp_499_;
}
}
}
else
{
v___y_506_ = v_a_486_;
v___y_507_ = v_a_487_;
v___y_508_ = v_a_488_;
v___y_509_ = v_a_489_;
goto v___jp_505_;
}
v___jp_505_:
{
uint8_t v___x_510_; 
v___x_510_ = l_Lean_Name_isMetaprogramming(v_name_484_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; lean_object* v_type_512_; uint8_t v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___f_516_; lean_object* v___x_517_; 
v___x_511_ = l_Lean_AsyncConstantInfo_toConstantVal(v_c_485_);
v_type_512_ = lean_ctor_get(v___x_511_, 2);
lean_inc_ref(v_type_512_);
lean_dec_ref(v___x_511_);
v___x_513_ = 2;
v___x_514_ = lean_box(v___x_513_);
v___x_515_ = lean_box(v___x_510_);
v___f_516_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__1___boxed), 9, 4);
lean_closure_set(v___f_516_, 0, v___x_514_);
lean_closure_set(v___f_516_, 1, v_type_512_);
lean_closure_set(v___f_516_, 2, v___f_504_);
lean_closure_set(v___f_516_, 3, v___x_515_);
v___x_517_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1___redArg(v___f_516_, v___x_510_, v___y_506_, v___y_507_, v___y_508_, v___y_509_);
return v___x_517_;
}
else
{
lean_object* v___x_518_; lean_object* v___x_519_; 
lean_dec_ref(v___f_504_);
lean_dec_ref(v_c_485_);
v___x_518_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0));
v___x_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_519_, 0, v___x_518_);
return v___x_519_;
}
}
}
else
{
lean_object* v___x_541_; lean_object* v___x_542_; 
lean_dec_ref(v_c_485_);
lean_dec(v_name_484_);
v___x_541_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0));
v___x_542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
return v___x_542_;
}
v___jp_499_:
{
lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_500_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0));
v___x_501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_501_, 0, v___x_500_);
return v___x_501_;
}
}
else
{
lean_dec_ref(v_c_485_);
lean_dec(v_name_484_);
goto v___jp_493_;
}
}
v___jp_493_:
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0));
v___x_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
return v___x_495_;
}
}
else
{
lean_object* v___x_543_; lean_object* v___x_544_; 
lean_dec_ref(v_c_485_);
lean_dec(v_name_484_);
v___x_543_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0));
v___x_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
return v___x_544_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___boxed(lean_object* v_name_545_, lean_object* v_c_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport(v_name_545_, v_c_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_);
lean_dec(v_a_550_);
lean_dec_ref(v_a_549_);
lean_dec(v_a_548_);
lean_dec_ref(v_a_547_);
return v_res_552_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_Rewrites_localHypotheses_spec__0(lean_object* v_a_553_, lean_object* v_x_554_){
_start:
{
if (lean_obj_tag(v_x_554_) == 0)
{
uint8_t v___x_555_; 
v___x_555_ = 0;
return v___x_555_;
}
else
{
lean_object* v_head_556_; lean_object* v_tail_557_; uint8_t v___x_558_; 
v_head_556_ = lean_ctor_get(v_x_554_, 0);
v_tail_557_ = lean_ctor_get(v_x_554_, 1);
v___x_558_ = l_Lean_instBEqFVarId_beq(v_a_553_, v_head_556_);
if (v___x_558_ == 0)
{
v_x_554_ = v_tail_557_;
goto _start;
}
else
{
return v___x_558_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_Rewrites_localHypotheses_spec__0___boxed(lean_object* v_a_560_, lean_object* v_x_561_){
_start:
{
uint8_t v_res_562_; lean_object* v_r_563_; 
v_res_562_ = l_List_elem___at___00Lean_Meta_Rewrites_localHypotheses_spec__0(v_a_560_, v_x_561_);
lean_dec(v_x_561_);
lean_dec(v_a_560_);
v_r_563_ = lean_box(v_res_562_);
return v_r_563_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_localHypotheses_spec__2(lean_object* v_except_564_, lean_object* v_as_565_, size_t v_sz_566_, size_t v_i_567_, lean_object* v_b_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
lean_object* v_a_575_; uint8_t v___x_579_; 
v___x_579_ = lean_usize_dec_lt(v_i_567_, v_sz_566_);
if (v___x_579_ == 0)
{
lean_object* v___x_580_; 
v___x_580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_580_, 0, v_b_568_);
return v___x_580_;
}
else
{
lean_object* v_a_581_; lean_object* v___x_582_; uint8_t v___x_583_; 
v_a_581_ = lean_array_uget_borrowed(v_as_565_, v_i_567_);
v___x_582_ = l_Lean_Expr_fvarId_x21(v_a_581_);
v___x_583_ = l_List_elem___at___00Lean_Meta_Rewrites_localHypotheses_spec__0(v___x_582_, v_except_564_);
lean_dec(v___x_582_);
if (v___x_583_ == 0)
{
lean_object* v___x_584_; 
lean_inc(v___y_572_);
lean_inc_ref(v___y_571_);
lean_inc(v___y_570_);
lean_inc_ref(v___y_569_);
lean_inc(v_a_581_);
v___x_584_ = lean_infer_type(v_a_581_, v___y_569_, v___y_570_, v___y_571_, v___y_572_);
if (lean_obj_tag(v___x_584_) == 0)
{
lean_object* v_a_585_; lean_object* v___x_586_; uint8_t v___x_587_; lean_object* v___x_588_; 
v_a_585_ = lean_ctor_get(v___x_584_, 0);
lean_inc(v_a_585_);
lean_dec_ref_known(v___x_584_, 1);
v___x_586_ = lean_box(0);
v___x_587_ = 0;
v___x_588_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_585_, v___x_586_, v___x_587_, v___y_569_, v___y_570_, v___y_571_, v___y_572_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_object* v_a_589_; lean_object* v_snd_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_661_; 
v_a_589_ = lean_ctor_get(v___x_588_, 0);
lean_inc(v_a_589_);
lean_dec_ref_known(v___x_588_, 1);
v_snd_590_ = lean_ctor_get(v_a_589_, 1);
v_isSharedCheck_661_ = !lean_is_exclusive(v_a_589_);
if (v_isSharedCheck_661_ == 0)
{
lean_object* v_unused_662_; 
v_unused_662_ = lean_ctor_get(v_a_589_, 0);
lean_dec(v_unused_662_);
v___x_592_ = v_a_589_;
v_isShared_593_ = v_isSharedCheck_661_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_snd_590_);
lean_dec(v_a_589_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_661_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v_snd_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_659_; 
v_snd_594_ = lean_ctor_get(v_snd_590_, 1);
v_isSharedCheck_659_ = !lean_is_exclusive(v_snd_590_);
if (v_isSharedCheck_659_ == 0)
{
lean_object* v_unused_660_; 
v_unused_660_ = lean_ctor_get(v_snd_590_, 0);
lean_dec(v_unused_660_);
v___x_596_ = v_snd_590_;
v_isShared_597_ = v_isSharedCheck_659_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_snd_594_);
lean_dec(v_snd_590_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_659_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_598_; 
v___x_598_ = l_Lean_Meta_whnfR(v_snd_594_, v___y_569_, v___y_570_, v___y_571_, v___y_572_);
if (lean_obj_tag(v___x_598_) == 0)
{
lean_object* v_a_599_; lean_object* v___x_600_; lean_object* v_fst_601_; 
v_a_599_ = lean_ctor_get(v___x_598_, 0);
lean_inc(v_a_599_);
lean_dec_ref_known(v___x_598_, 1);
v___x_600_ = l_Lean_Expr_getAppFnArgs(v_a_599_);
v_fst_601_ = lean_ctor_get(v___x_600_, 0);
lean_inc(v_fst_601_);
if (lean_obj_tag(v_fst_601_) == 1)
{
lean_object* v_pre_602_; 
v_pre_602_ = lean_ctor_get(v_fst_601_, 0);
if (lean_obj_tag(v_pre_602_) == 0)
{
lean_object* v_snd_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_649_; 
v_snd_603_ = lean_ctor_get(v___x_600_, 1);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_649_ == 0)
{
lean_object* v_unused_650_; 
v_unused_650_ = lean_ctor_get(v___x_600_, 0);
lean_dec(v_unused_650_);
v___x_605_ = v___x_600_;
v_isShared_606_ = v_isSharedCheck_649_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_snd_603_);
lean_dec(v___x_600_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_649_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v_str_607_; lean_object* v___x_608_; uint8_t v___x_609_; 
v_str_607_ = lean_ctor_get(v_fst_601_, 1);
lean_inc_ref(v_str_607_);
lean_dec_ref_known(v_fst_601_, 2);
v___x_608_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__1));
v___x_609_ = lean_string_dec_eq(v_str_607_, v___x_608_);
if (v___x_609_ == 0)
{
lean_object* v___x_610_; uint8_t v___x_611_; 
v___x_610_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__2));
v___x_611_ = lean_string_dec_eq(v_str_607_, v___x_610_);
lean_dec_ref(v_str_607_);
if (v___x_611_ == 0)
{
lean_del_object(v___x_605_);
lean_dec(v_snd_603_);
lean_del_object(v___x_596_);
lean_del_object(v___x_592_);
v_a_575_ = v_b_568_;
goto v___jp_574_;
}
else
{
lean_object* v___x_612_; lean_object* v___x_613_; uint8_t v___x_614_; 
v___x_612_ = lean_array_get_size(v_snd_603_);
lean_dec(v_snd_603_);
v___x_613_ = lean_unsigned_to_nat(2u);
v___x_614_ = lean_nat_dec_eq(v___x_612_, v___x_613_);
if (v___x_614_ == 0)
{
lean_del_object(v___x_605_);
lean_del_object(v___x_596_);
lean_del_object(v___x_592_);
v_a_575_ = v_b_568_;
goto v___jp_574_;
}
else
{
lean_object* v___x_615_; lean_object* v___x_617_; 
v___x_615_ = lean_box(v___x_583_);
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 1, v___x_613_);
lean_ctor_set(v___x_605_, 0, v___x_615_);
v___x_617_ = v___x_605_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v___x_615_);
lean_ctor_set(v_reuseFailAlloc_629_, 1, v___x_613_);
v___x_617_ = v_reuseFailAlloc_629_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
lean_object* v___x_619_; 
lean_inc(v_a_581_);
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 1, v___x_617_);
lean_ctor_set(v___x_596_, 0, v_a_581_);
v___x_619_ = v___x_596_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_a_581_);
lean_ctor_set(v_reuseFailAlloc_628_, 1, v___x_617_);
v___x_619_ = v_reuseFailAlloc_628_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_624_; 
v___x_620_ = lean_array_push(v_b_568_, v___x_619_);
v___x_621_ = lean_unsigned_to_nat(1u);
v___x_622_ = lean_box(v___x_579_);
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 1, v___x_621_);
lean_ctor_set(v___x_592_, 0, v___x_622_);
v___x_624_ = v___x_592_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v___x_622_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v___x_621_);
v___x_624_ = v_reuseFailAlloc_627_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
lean_object* v___x_625_; lean_object* v___x_626_; 
lean_inc(v_a_581_);
v___x_625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_625_, 0, v_a_581_);
lean_ctor_set(v___x_625_, 1, v___x_624_);
v___x_626_ = lean_array_push(v___x_620_, v___x_625_);
v_a_575_ = v___x_626_;
goto v___jp_574_;
}
}
}
}
}
}
else
{
lean_object* v___x_630_; lean_object* v___x_631_; uint8_t v___x_632_; 
lean_dec_ref(v_str_607_);
v___x_630_ = lean_array_get_size(v_snd_603_);
lean_dec(v_snd_603_);
v___x_631_ = lean_unsigned_to_nat(3u);
v___x_632_ = lean_nat_dec_eq(v___x_630_, v___x_631_);
if (v___x_632_ == 0)
{
lean_del_object(v___x_605_);
lean_del_object(v___x_596_);
lean_del_object(v___x_592_);
v_a_575_ = v_b_568_;
goto v___jp_574_;
}
else
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_636_; 
v___x_633_ = lean_unsigned_to_nat(2u);
v___x_634_ = lean_box(v___x_583_);
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 1, v___x_633_);
lean_ctor_set(v___x_605_, 0, v___x_634_);
v___x_636_ = v___x_605_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v___x_634_);
lean_ctor_set(v_reuseFailAlloc_648_, 1, v___x_633_);
v___x_636_ = v_reuseFailAlloc_648_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
lean_object* v___x_638_; 
lean_inc(v_a_581_);
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 1, v___x_636_);
lean_ctor_set(v___x_596_, 0, v_a_581_);
v___x_638_ = v___x_596_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_a_581_);
lean_ctor_set(v_reuseFailAlloc_647_, 1, v___x_636_);
v___x_638_ = v_reuseFailAlloc_647_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_643_; 
v___x_639_ = lean_array_push(v_b_568_, v___x_638_);
v___x_640_ = lean_unsigned_to_nat(1u);
v___x_641_ = lean_box(v___x_579_);
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 1, v___x_640_);
lean_ctor_set(v___x_592_, 0, v___x_641_);
v___x_643_ = v___x_592_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v___x_641_);
lean_ctor_set(v_reuseFailAlloc_646_, 1, v___x_640_);
v___x_643_ = v_reuseFailAlloc_646_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
lean_object* v___x_644_; lean_object* v___x_645_; 
lean_inc(v_a_581_);
v___x_644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_644_, 0, v_a_581_);
lean_ctor_set(v___x_644_, 1, v___x_643_);
v___x_645_ = lean_array_push(v___x_639_, v___x_644_);
v_a_575_ = v___x_645_;
goto v___jp_574_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_fst_601_, 2);
lean_dec_ref(v___x_600_);
lean_del_object(v___x_596_);
lean_del_object(v___x_592_);
v_a_575_ = v_b_568_;
goto v___jp_574_;
}
}
else
{
lean_dec(v_fst_601_);
lean_dec_ref(v___x_600_);
lean_del_object(v___x_596_);
lean_del_object(v___x_592_);
v_a_575_ = v_b_568_;
goto v___jp_574_;
}
}
else
{
lean_object* v_a_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_658_; 
lean_del_object(v___x_596_);
lean_del_object(v___x_592_);
lean_dec_ref(v_b_568_);
v_a_651_ = lean_ctor_get(v___x_598_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_658_ == 0)
{
v___x_653_ = v___x_598_;
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_a_651_);
lean_dec(v___x_598_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_656_; 
if (v_isShared_654_ == 0)
{
v___x_656_ = v___x_653_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_a_651_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
}
}
}
else
{
lean_object* v_a_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_670_; 
lean_dec_ref(v_b_568_);
v_a_663_ = lean_ctor_get(v___x_588_, 0);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_670_ == 0)
{
v___x_665_ = v___x_588_;
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_a_663_);
lean_dec(v___x_588_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_668_; 
if (v_isShared_666_ == 0)
{
v___x_668_ = v___x_665_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_a_663_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
}
else
{
lean_object* v_a_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_678_; 
lean_dec_ref(v_b_568_);
v_a_671_ = lean_ctor_get(v___x_584_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_678_ == 0)
{
v___x_673_ = v___x_584_;
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_a_671_);
lean_dec(v___x_584_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_676_; 
if (v_isShared_674_ == 0)
{
v___x_676_ = v___x_673_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_a_671_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
}
else
{
v_a_575_ = v_b_568_;
goto v___jp_574_;
}
}
v___jp_574_:
{
size_t v___x_576_; size_t v___x_577_; 
v___x_576_ = ((size_t)1ULL);
v___x_577_ = lean_usize_add(v_i_567_, v___x_576_);
v_i_567_ = v___x_577_;
v_b_568_ = v_a_575_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_localHypotheses_spec__2___boxed(lean_object* v_except_679_, lean_object* v_as_680_, lean_object* v_sz_681_, lean_object* v_i_682_, lean_object* v_b_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
size_t v_sz_boxed_689_; size_t v_i_boxed_690_; lean_object* v_res_691_; 
v_sz_boxed_689_ = lean_unbox_usize(v_sz_681_);
lean_dec(v_sz_681_);
v_i_boxed_690_ = lean_unbox_usize(v_i_682_);
lean_dec(v_i_682_);
v_res_691_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_localHypotheses_spec__2(v_except_679_, v_as_680_, v_sz_boxed_689_, v_i_boxed_690_, v_b_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec_ref(v_as_680_);
lean_dec(v_except_679_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(lean_object* v_as_692_, size_t v_sz_693_, size_t v_i_694_, lean_object* v_b_695_){
_start:
{
uint8_t v___x_697_; 
v___x_697_ = lean_usize_dec_lt(v_i_694_, v_sz_693_);
if (v___x_697_ == 0)
{
lean_object* v___x_698_; 
v___x_698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_698_, 0, v_b_695_);
return v___x_698_;
}
else
{
lean_object* v_snd_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_717_; 
v_snd_699_ = lean_ctor_get(v_b_695_, 1);
v_isSharedCheck_717_ = !lean_is_exclusive(v_b_695_);
if (v_isSharedCheck_717_ == 0)
{
lean_object* v_unused_718_; 
v_unused_718_ = lean_ctor_get(v_b_695_, 0);
lean_dec(v_unused_718_);
v___x_701_ = v_b_695_;
v_isShared_702_ = v_isSharedCheck_717_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_snd_699_);
lean_dec(v_b_695_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_717_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_703_; lean_object* v_a_705_; lean_object* v_a_712_; 
v___x_703_ = lean_box(0);
v_a_712_ = lean_array_uget_borrowed(v_as_692_, v_i_694_);
if (lean_obj_tag(v_a_712_) == 0)
{
v_a_705_ = v_snd_699_;
goto v___jp_704_;
}
else
{
lean_object* v_val_713_; uint8_t v___x_714_; 
v_val_713_ = lean_ctor_get(v_a_712_, 0);
v___x_714_ = l_Lean_LocalDecl_isImplementationDetail(v_val_713_);
if (v___x_714_ == 0)
{
lean_object* v___x_715_; lean_object* v___x_716_; 
lean_inc(v_val_713_);
v___x_715_ = l_Lean_LocalDecl_toExpr(v_val_713_);
v___x_716_ = lean_array_push(v_snd_699_, v___x_715_);
v_a_705_ = v___x_716_;
goto v___jp_704_;
}
else
{
v_a_705_ = v_snd_699_;
goto v___jp_704_;
}
}
v___jp_704_:
{
lean_object* v___x_707_; 
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 1, v_a_705_);
lean_ctor_set(v___x_701_, 0, v___x_703_);
v___x_707_ = v___x_701_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v___x_703_);
lean_ctor_set(v_reuseFailAlloc_711_, 1, v_a_705_);
v___x_707_ = v_reuseFailAlloc_711_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
size_t v___x_708_; size_t v___x_709_; 
v___x_708_ = ((size_t)1ULL);
v___x_709_ = lean_usize_add(v_i_694_, v___x_708_);
v_i_694_ = v___x_709_;
v_b_695_ = v___x_707_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___redArg___boxed(lean_object* v_as_719_, lean_object* v_sz_720_, lean_object* v_i_721_, lean_object* v_b_722_, lean_object* v___y_723_){
_start:
{
size_t v_sz_boxed_724_; size_t v_i_boxed_725_; lean_object* v_res_726_; 
v_sz_boxed_724_ = lean_unbox_usize(v_sz_720_);
lean_dec(v_sz_720_);
v_i_boxed_725_ = lean_unbox_usize(v_i_721_);
lean_dec(v_i_721_);
v_res_726_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(v_as_719_, v_sz_boxed_724_, v_i_boxed_725_, v_b_722_);
lean_dec_ref(v_as_719_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5(lean_object* v_as_727_, size_t v_sz_728_, size_t v_i_729_, lean_object* v_b_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_){
_start:
{
uint8_t v___x_736_; 
v___x_736_ = lean_usize_dec_lt(v_i_729_, v_sz_728_);
if (v___x_736_ == 0)
{
lean_object* v___x_737_; 
v___x_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_737_, 0, v_b_730_);
return v___x_737_;
}
else
{
lean_object* v_snd_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_756_; 
v_snd_738_ = lean_ctor_get(v_b_730_, 1);
v_isSharedCheck_756_ = !lean_is_exclusive(v_b_730_);
if (v_isSharedCheck_756_ == 0)
{
lean_object* v_unused_757_; 
v_unused_757_ = lean_ctor_get(v_b_730_, 0);
lean_dec(v_unused_757_);
v___x_740_ = v_b_730_;
v_isShared_741_ = v_isSharedCheck_756_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_snd_738_);
lean_dec(v_b_730_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_756_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_742_; lean_object* v_a_744_; lean_object* v_a_751_; 
v___x_742_ = lean_box(0);
v_a_751_ = lean_array_uget_borrowed(v_as_727_, v_i_729_);
if (lean_obj_tag(v_a_751_) == 0)
{
v_a_744_ = v_snd_738_;
goto v___jp_743_;
}
else
{
lean_object* v_val_752_; uint8_t v___x_753_; 
v_val_752_ = lean_ctor_get(v_a_751_, 0);
v___x_753_ = l_Lean_LocalDecl_isImplementationDetail(v_val_752_);
if (v___x_753_ == 0)
{
lean_object* v___x_754_; lean_object* v___x_755_; 
lean_inc(v_val_752_);
v___x_754_ = l_Lean_LocalDecl_toExpr(v_val_752_);
v___x_755_ = lean_array_push(v_snd_738_, v___x_754_);
v_a_744_ = v___x_755_;
goto v___jp_743_;
}
else
{
v_a_744_ = v_snd_738_;
goto v___jp_743_;
}
}
v___jp_743_:
{
lean_object* v___x_746_; 
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 1, v_a_744_);
lean_ctor_set(v___x_740_, 0, v___x_742_);
v___x_746_ = v___x_740_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v___x_742_);
lean_ctor_set(v_reuseFailAlloc_750_, 1, v_a_744_);
v___x_746_ = v_reuseFailAlloc_750_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
size_t v___x_747_; size_t v___x_748_; lean_object* v___x_749_; 
v___x_747_ = ((size_t)1ULL);
v___x_748_ = lean_usize_add(v_i_729_, v___x_747_);
v___x_749_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(v_as_727_, v_sz_728_, v___x_748_, v___x_746_);
return v___x_749_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5___boxed(lean_object* v_as_758_, lean_object* v_sz_759_, lean_object* v_i_760_, lean_object* v_b_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
size_t v_sz_boxed_767_; size_t v_i_boxed_768_; lean_object* v_res_769_; 
v_sz_boxed_767_ = lean_unbox_usize(v_sz_759_);
lean_dec(v_sz_759_);
v_i_boxed_768_ = lean_unbox_usize(v_i_760_);
lean_dec(v_i_760_);
v_res_769_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5(v_as_758_, v_sz_boxed_767_, v_i_boxed_768_, v_b_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec_ref(v_as_758_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2(lean_object* v_init_770_, lean_object* v_n_771_, lean_object* v_b_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
if (lean_obj_tag(v_n_771_) == 0)
{
lean_object* v_cs_778_; lean_object* v___x_779_; lean_object* v___x_780_; size_t v_sz_781_; size_t v___x_782_; lean_object* v___x_783_; 
v_cs_778_ = lean_ctor_get(v_n_771_, 0);
v___x_779_ = lean_box(0);
v___x_780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_780_, 0, v___x_779_);
lean_ctor_set(v___x_780_, 1, v_b_772_);
v_sz_781_ = lean_array_size(v_cs_778_);
v___x_782_ = ((size_t)0ULL);
v___x_783_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__4(v_init_770_, v_cs_778_, v_sz_781_, v___x_782_, v___x_780_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
if (lean_obj_tag(v___x_783_) == 0)
{
lean_object* v_a_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_798_; 
v_a_784_ = lean_ctor_get(v___x_783_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_798_ == 0)
{
v___x_786_ = v___x_783_;
v_isShared_787_ = v_isSharedCheck_798_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_a_784_);
lean_dec(v___x_783_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_798_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v_fst_788_; 
v_fst_788_ = lean_ctor_get(v_a_784_, 0);
if (lean_obj_tag(v_fst_788_) == 0)
{
lean_object* v_snd_789_; lean_object* v___x_790_; lean_object* v___x_792_; 
v_snd_789_ = lean_ctor_get(v_a_784_, 1);
lean_inc(v_snd_789_);
lean_dec(v_a_784_);
v___x_790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_790_, 0, v_snd_789_);
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 0, v___x_790_);
v___x_792_ = v___x_786_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_790_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
else
{
lean_object* v_val_794_; lean_object* v___x_796_; 
lean_inc_ref(v_fst_788_);
lean_dec(v_a_784_);
v_val_794_ = lean_ctor_get(v_fst_788_, 0);
lean_inc(v_val_794_);
lean_dec_ref_known(v_fst_788_, 1);
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 0, v_val_794_);
v___x_796_ = v___x_786_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_val_794_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
}
else
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_806_; 
v_a_799_ = lean_ctor_get(v___x_783_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_806_ == 0)
{
v___x_801_ = v___x_783_;
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_783_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_804_; 
if (v_isShared_802_ == 0)
{
v___x_804_ = v___x_801_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_a_799_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
else
{
lean_object* v_vs_807_; lean_object* v___x_808_; lean_object* v___x_809_; size_t v_sz_810_; size_t v___x_811_; lean_object* v___x_812_; 
v_vs_807_ = lean_ctor_get(v_n_771_, 0);
v___x_808_ = lean_box(0);
v___x_809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_809_, 0, v___x_808_);
lean_ctor_set(v___x_809_, 1, v_b_772_);
v_sz_810_ = lean_array_size(v_vs_807_);
v___x_811_ = ((size_t)0ULL);
v___x_812_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5(v_vs_807_, v_sz_810_, v___x_811_, v___x_809_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_827_; 
v_a_813_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_827_ == 0)
{
v___x_815_ = v___x_812_;
v_isShared_816_ = v_isSharedCheck_827_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_dec(v___x_812_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_827_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v_fst_817_; 
v_fst_817_ = lean_ctor_get(v_a_813_, 0);
if (lean_obj_tag(v_fst_817_) == 0)
{
lean_object* v_snd_818_; lean_object* v___x_819_; lean_object* v___x_821_; 
v_snd_818_ = lean_ctor_get(v_a_813_, 1);
lean_inc(v_snd_818_);
lean_dec(v_a_813_);
v___x_819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_819_, 0, v_snd_818_);
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 0, v___x_819_);
v___x_821_ = v___x_815_;
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
lean_object* v_val_823_; lean_object* v___x_825_; 
lean_inc_ref(v_fst_817_);
lean_dec(v_a_813_);
v_val_823_ = lean_ctor_get(v_fst_817_, 0);
lean_inc(v_val_823_);
lean_dec_ref_known(v_fst_817_, 1);
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 0, v_val_823_);
v___x_825_ = v___x_815_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_val_823_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
}
else
{
lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_835_; 
v_a_828_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_835_ == 0)
{
v___x_830_ = v___x_812_;
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___x_812_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_833_; 
if (v_isShared_831_ == 0)
{
v___x_833_ = v___x_830_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_a_828_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__4(lean_object* v_init_836_, lean_object* v_as_837_, size_t v_sz_838_, size_t v_i_839_, lean_object* v_b_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
uint8_t v___x_846_; 
v___x_846_ = lean_usize_dec_lt(v_i_839_, v_sz_838_);
if (v___x_846_ == 0)
{
lean_object* v___x_847_; 
v___x_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_847_, 0, v_b_840_);
return v___x_847_;
}
else
{
lean_object* v_snd_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_882_; 
v_snd_848_ = lean_ctor_get(v_b_840_, 1);
v_isSharedCheck_882_ = !lean_is_exclusive(v_b_840_);
if (v_isSharedCheck_882_ == 0)
{
lean_object* v_unused_883_; 
v_unused_883_ = lean_ctor_get(v_b_840_, 0);
lean_dec(v_unused_883_);
v___x_850_ = v_b_840_;
v_isShared_851_ = v_isSharedCheck_882_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_snd_848_);
lean_dec(v_b_840_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_882_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v_a_852_; lean_object* v___x_853_; 
v_a_852_ = lean_array_uget_borrowed(v_as_837_, v_i_839_);
lean_inc(v_snd_848_);
v___x_853_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2(v_init_836_, v_a_852_, v_snd_848_, v___y_841_, v___y_842_, v___y_843_, v___y_844_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_a_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_873_; 
v_a_854_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_873_ == 0)
{
v___x_856_ = v___x_853_;
v_isShared_857_ = v_isSharedCheck_873_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_a_854_);
lean_dec(v___x_853_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_873_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
if (lean_obj_tag(v_a_854_) == 0)
{
lean_object* v___x_858_; lean_object* v___x_860_; 
v___x_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_858_, 0, v_a_854_);
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 0, v___x_858_);
v___x_860_ = v___x_850_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v___x_858_);
lean_ctor_set(v_reuseFailAlloc_864_, 1, v_snd_848_);
v___x_860_ = v_reuseFailAlloc_864_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
lean_object* v___x_862_; 
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 0, v___x_860_);
v___x_862_ = v___x_856_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v___x_860_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
else
{
lean_object* v_a_865_; lean_object* v___x_866_; lean_object* v___x_868_; 
lean_del_object(v___x_856_);
lean_dec(v_snd_848_);
v_a_865_ = lean_ctor_get(v_a_854_, 0);
lean_inc(v_a_865_);
lean_dec_ref_known(v_a_854_, 1);
v___x_866_ = lean_box(0);
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 1, v_a_865_);
lean_ctor_set(v___x_850_, 0, v___x_866_);
v___x_868_ = v___x_850_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_866_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v_a_865_);
v___x_868_ = v_reuseFailAlloc_872_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
size_t v___x_869_; size_t v___x_870_; 
v___x_869_ = ((size_t)1ULL);
v___x_870_ = lean_usize_add(v_i_839_, v___x_869_);
v_i_839_ = v___x_870_;
v_b_840_ = v___x_868_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_881_; 
lean_del_object(v___x_850_);
lean_dec(v_snd_848_);
v_a_874_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_881_ == 0)
{
v___x_876_ = v___x_853_;
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_a_874_);
lean_dec(v___x_853_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_879_; 
if (v_isShared_877_ == 0)
{
v___x_879_ = v___x_876_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_a_874_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_init_884_, lean_object* v_as_885_, lean_object* v_sz_886_, lean_object* v_i_887_, lean_object* v_b_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_){
_start:
{
size_t v_sz_boxed_894_; size_t v_i_boxed_895_; lean_object* v_res_896_; 
v_sz_boxed_894_ = lean_unbox_usize(v_sz_886_);
lean_dec(v_sz_886_);
v_i_boxed_895_ = lean_unbox_usize(v_i_887_);
lean_dec(v_i_887_);
v_res_896_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__4(v_init_884_, v_as_885_, v_sz_boxed_894_, v_i_boxed_895_, v_b_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_);
lean_dec(v___y_892_);
lean_dec_ref(v___y_891_);
lean_dec(v___y_890_);
lean_dec_ref(v___y_889_);
lean_dec_ref(v_as_885_);
lean_dec_ref(v_init_884_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2___boxed(lean_object* v_init_897_, lean_object* v_n_898_, lean_object* v_b_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2(v_init_897_, v_n_898_, v_b_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec_ref(v_n_898_);
lean_dec_ref(v_init_897_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___redArg(lean_object* v_as_906_, size_t v_sz_907_, size_t v_i_908_, lean_object* v_b_909_){
_start:
{
uint8_t v___x_911_; 
v___x_911_ = lean_usize_dec_lt(v_i_908_, v_sz_907_);
if (v___x_911_ == 0)
{
lean_object* v___x_912_; 
v___x_912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_912_, 0, v_b_909_);
return v___x_912_;
}
else
{
lean_object* v_snd_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_931_; 
v_snd_913_ = lean_ctor_get(v_b_909_, 1);
v_isSharedCheck_931_ = !lean_is_exclusive(v_b_909_);
if (v_isSharedCheck_931_ == 0)
{
lean_object* v_unused_932_; 
v_unused_932_ = lean_ctor_get(v_b_909_, 0);
lean_dec(v_unused_932_);
v___x_915_ = v_b_909_;
v_isShared_916_ = v_isSharedCheck_931_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_snd_913_);
lean_dec(v_b_909_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_931_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_917_; lean_object* v_a_919_; lean_object* v_a_926_; 
v___x_917_ = lean_box(0);
v_a_926_ = lean_array_uget_borrowed(v_as_906_, v_i_908_);
if (lean_obj_tag(v_a_926_) == 0)
{
v_a_919_ = v_snd_913_;
goto v___jp_918_;
}
else
{
lean_object* v_val_927_; uint8_t v___x_928_; 
v_val_927_ = lean_ctor_get(v_a_926_, 0);
v___x_928_ = l_Lean_LocalDecl_isImplementationDetail(v_val_927_);
if (v___x_928_ == 0)
{
lean_object* v___x_929_; lean_object* v___x_930_; 
lean_inc(v_val_927_);
v___x_929_ = l_Lean_LocalDecl_toExpr(v_val_927_);
v___x_930_ = lean_array_push(v_snd_913_, v___x_929_);
v_a_919_ = v___x_930_;
goto v___jp_918_;
}
else
{
v_a_919_ = v_snd_913_;
goto v___jp_918_;
}
}
v___jp_918_:
{
lean_object* v___x_921_; 
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 1, v_a_919_);
lean_ctor_set(v___x_915_, 0, v___x_917_);
v___x_921_ = v___x_915_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_917_);
lean_ctor_set(v_reuseFailAlloc_925_, 1, v_a_919_);
v___x_921_ = v_reuseFailAlloc_925_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
size_t v___x_922_; size_t v___x_923_; 
v___x_922_ = ((size_t)1ULL);
v___x_923_ = lean_usize_add(v_i_908_, v___x_922_);
v_i_908_ = v___x_923_;
v_b_909_ = v___x_921_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_as_933_, lean_object* v_sz_934_, lean_object* v_i_935_, lean_object* v_b_936_, lean_object* v___y_937_){
_start:
{
size_t v_sz_boxed_938_; size_t v_i_boxed_939_; lean_object* v_res_940_; 
v_sz_boxed_938_ = lean_unbox_usize(v_sz_934_);
lean_dec(v_sz_934_);
v_i_boxed_939_ = lean_unbox_usize(v_i_935_);
lean_dec(v_i_935_);
v_res_940_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___redArg(v_as_933_, v_sz_boxed_938_, v_i_boxed_939_, v_b_936_);
lean_dec_ref(v_as_933_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3(lean_object* v_as_941_, size_t v_sz_942_, size_t v_i_943_, lean_object* v_b_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
uint8_t v___x_950_; 
v___x_950_ = lean_usize_dec_lt(v_i_943_, v_sz_942_);
if (v___x_950_ == 0)
{
lean_object* v___x_951_; 
v___x_951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_951_, 0, v_b_944_);
return v___x_951_;
}
else
{
lean_object* v_snd_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_970_; 
v_snd_952_ = lean_ctor_get(v_b_944_, 1);
v_isSharedCheck_970_ = !lean_is_exclusive(v_b_944_);
if (v_isSharedCheck_970_ == 0)
{
lean_object* v_unused_971_; 
v_unused_971_ = lean_ctor_get(v_b_944_, 0);
lean_dec(v_unused_971_);
v___x_954_ = v_b_944_;
v_isShared_955_ = v_isSharedCheck_970_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_snd_952_);
lean_dec(v_b_944_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_970_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_956_; lean_object* v_a_958_; lean_object* v_a_965_; 
v___x_956_ = lean_box(0);
v_a_965_ = lean_array_uget_borrowed(v_as_941_, v_i_943_);
if (lean_obj_tag(v_a_965_) == 0)
{
v_a_958_ = v_snd_952_;
goto v___jp_957_;
}
else
{
lean_object* v_val_966_; uint8_t v___x_967_; 
v_val_966_ = lean_ctor_get(v_a_965_, 0);
v___x_967_ = l_Lean_LocalDecl_isImplementationDetail(v_val_966_);
if (v___x_967_ == 0)
{
lean_object* v___x_968_; lean_object* v___x_969_; 
lean_inc(v_val_966_);
v___x_968_ = l_Lean_LocalDecl_toExpr(v_val_966_);
v___x_969_ = lean_array_push(v_snd_952_, v___x_968_);
v_a_958_ = v___x_969_;
goto v___jp_957_;
}
else
{
v_a_958_ = v_snd_952_;
goto v___jp_957_;
}
}
v___jp_957_:
{
lean_object* v___x_960_; 
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 1, v_a_958_);
lean_ctor_set(v___x_954_, 0, v___x_956_);
v___x_960_ = v___x_954_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v___x_956_);
lean_ctor_set(v_reuseFailAlloc_964_, 1, v_a_958_);
v___x_960_ = v_reuseFailAlloc_964_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
size_t v___x_961_; size_t v___x_962_; lean_object* v___x_963_; 
v___x_961_ = ((size_t)1ULL);
v___x_962_ = lean_usize_add(v_i_943_, v___x_961_);
v___x_963_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___redArg(v_as_941_, v_sz_942_, v___x_962_, v___x_960_);
return v___x_963_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3___boxed(lean_object* v_as_972_, lean_object* v_sz_973_, lean_object* v_i_974_, lean_object* v_b_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
size_t v_sz_boxed_981_; size_t v_i_boxed_982_; lean_object* v_res_983_; 
v_sz_boxed_981_ = lean_unbox_usize(v_sz_973_);
lean_dec(v_sz_973_);
v_i_boxed_982_ = lean_unbox_usize(v_i_974_);
lean_dec(v_i_974_);
v_res_983_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3(v_as_972_, v_sz_boxed_981_, v_i_boxed_982_, v_b_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec_ref(v_as_972_);
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1(lean_object* v_t_984_, lean_object* v_init_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_){
_start:
{
lean_object* v_root_991_; lean_object* v_tail_992_; lean_object* v___x_993_; 
v_root_991_ = lean_ctor_get(v_t_984_, 0);
v_tail_992_ = lean_ctor_get(v_t_984_, 1);
lean_inc_ref(v_init_985_);
v___x_993_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2(v_init_985_, v_root_991_, v_init_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_);
lean_dec_ref(v_init_985_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1030_; 
v_a_994_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_996_ = v___x_993_;
v_isShared_997_ = v_isSharedCheck_1030_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v___x_993_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1030_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
if (lean_obj_tag(v_a_994_) == 0)
{
lean_object* v_a_998_; lean_object* v___x_1000_; 
v_a_998_ = lean_ctor_get(v_a_994_, 0);
lean_inc(v_a_998_);
lean_dec_ref_known(v_a_994_, 1);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 0, v_a_998_);
v___x_1000_ = v___x_996_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_a_998_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
else
{
lean_object* v_a_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; size_t v_sz_1005_; size_t v___x_1006_; lean_object* v___x_1007_; 
lean_del_object(v___x_996_);
v_a_1002_ = lean_ctor_get(v_a_994_, 0);
lean_inc(v_a_1002_);
lean_dec_ref_known(v_a_994_, 1);
v___x_1003_ = lean_box(0);
v___x_1004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1003_);
lean_ctor_set(v___x_1004_, 1, v_a_1002_);
v_sz_1005_ = lean_array_size(v_tail_992_);
v___x_1006_ = ((size_t)0ULL);
v___x_1007_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3(v_tail_992_, v_sz_1005_, v___x_1006_, v___x_1004_, v___y_986_, v___y_987_, v___y_988_, v___y_989_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v_a_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1021_; 
v_a_1008_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1010_ = v___x_1007_;
v_isShared_1011_ = v_isSharedCheck_1021_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_a_1008_);
lean_dec(v___x_1007_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1021_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v_fst_1012_; 
v_fst_1012_ = lean_ctor_get(v_a_1008_, 0);
if (lean_obj_tag(v_fst_1012_) == 0)
{
lean_object* v_snd_1013_; lean_object* v___x_1015_; 
v_snd_1013_ = lean_ctor_get(v_a_1008_, 1);
lean_inc(v_snd_1013_);
lean_dec(v_a_1008_);
if (v_isShared_1011_ == 0)
{
lean_ctor_set(v___x_1010_, 0, v_snd_1013_);
v___x_1015_ = v___x_1010_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_snd_1013_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
else
{
lean_object* v_val_1017_; lean_object* v___x_1019_; 
lean_inc_ref(v_fst_1012_);
lean_dec(v_a_1008_);
v_val_1017_ = lean_ctor_get(v_fst_1012_, 0);
lean_inc(v_val_1017_);
lean_dec_ref_known(v_fst_1012_, 1);
if (v_isShared_1011_ == 0)
{
lean_ctor_set(v___x_1010_, 0, v_val_1017_);
v___x_1019_ = v___x_1010_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_val_1017_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
}
else
{
lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1029_; 
v_a_1022_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1024_ = v___x_1007_;
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_1007_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1027_; 
if (v_isShared_1025_ == 0)
{
v___x_1027_ = v___x_1024_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_a_1022_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
}
}
}
else
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1038_; 
v_a_1031_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1033_ = v___x_993_;
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_993_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1036_; 
if (v_isShared_1034_ == 0)
{
v___x_1036_ = v___x_1033_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_a_1031_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1___boxed(lean_object* v_t_1039_, lean_object* v_init_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1(v_t_1039_, v_init_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
lean_dec(v___y_1044_);
lean_dec_ref(v___y_1043_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
lean_dec_ref(v_t_1039_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1(lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
lean_object* v_lctx_1054_; lean_object* v_decls_1055_; lean_object* v_hs_1056_; lean_object* v___x_1057_; 
v_lctx_1054_ = lean_ctor_get(v___y_1049_, 2);
v_decls_1055_ = lean_ctor_get(v_lctx_1054_, 1);
v_hs_1056_ = ((lean_object*)(l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1___closed__0));
v___x_1057_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1(v_decls_1055_, v_hs_1056_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1___boxed(lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1(v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_localHypotheses(lean_object* v_except_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_){
_start:
{
lean_object* v___x_1072_; 
v___x_1072_ = l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1(v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v_a_1073_; lean_object* v___x_1074_; size_t v_sz_1075_; size_t v___x_1076_; lean_object* v___x_1077_; 
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
lean_inc(v_a_1073_);
lean_dec_ref_known(v___x_1072_, 1);
v___x_1074_ = ((lean_object*)(l_Lean_Meta_Rewrites_localHypotheses___closed__0));
v_sz_1075_ = lean_array_size(v_a_1073_);
v___x_1076_ = ((size_t)0ULL);
v___x_1077_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_localHypotheses_spec__2(v_except_1066_, v_a_1073_, v_sz_1075_, v___x_1076_, v___x_1074_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_);
lean_dec(v_a_1073_);
return v___x_1077_;
}
else
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1085_; 
v_a_1078_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1080_ = v___x_1072_;
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___x_1072_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1083_; 
if (v_isShared_1081_ == 0)
{
v___x_1083_ = v___x_1080_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_a_1078_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_localHypotheses___boxed(lean_object* v_except_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_){
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l_Lean_Meta_Rewrites_localHypotheses(v_except_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_);
lean_dec(v_a_1090_);
lean_dec_ref(v_a_1089_);
lean_dec(v_a_1088_);
lean_dec_ref(v_a_1087_);
lean_dec(v_except_1086_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7(lean_object* v_as_1093_, size_t v_sz_1094_, size_t v_i_1095_, lean_object* v_b_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_){
_start:
{
lean_object* v___x_1102_; 
v___x_1102_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___redArg(v_as_1093_, v_sz_1094_, v_i_1095_, v_b_1096_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___boxed(lean_object* v_as_1103_, lean_object* v_sz_1104_, lean_object* v_i_1105_, lean_object* v_b_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_){
_start:
{
size_t v_sz_boxed_1112_; size_t v_i_boxed_1113_; lean_object* v_res_1114_; 
v_sz_boxed_1112_ = lean_unbox_usize(v_sz_1104_);
lean_dec(v_sz_1104_);
v_i_boxed_1113_ = lean_unbox_usize(v_i_1105_);
lean_dec(v_i_1105_);
v_res_1114_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7(v_as_1103_, v_sz_boxed_1112_, v_i_boxed_1113_, v_b_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_);
lean_dec(v___y_1110_);
lean_dec_ref(v___y_1109_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
lean_dec_ref(v_as_1103_);
return v_res_1114_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6(lean_object* v_as_1115_, size_t v_sz_1116_, size_t v_i_1117_, lean_object* v_b_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_){
_start:
{
lean_object* v___x_1124_; 
v___x_1124_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(v_as_1115_, v_sz_1116_, v_i_1117_, v_b_1118_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___boxed(lean_object* v_as_1125_, lean_object* v_sz_1126_, lean_object* v_i_1127_, lean_object* v_b_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_){
_start:
{
size_t v_sz_boxed_1134_; size_t v_i_boxed_1135_; lean_object* v_res_1136_; 
v_sz_boxed_1134_ = lean_unbox_usize(v_sz_1126_);
lean_dec(v_sz_1126_);
v_i_boxed_1135_ = lean_unbox_usize(v_i_1127_);
lean_dec(v_i_1127_);
v_res_1136_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6(v_as_1125_, v_sz_boxed_1134_, v_i_boxed_1135_, v_b_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
lean_dec(v___y_1130_);
lean_dec_ref(v___y_1129_);
lean_dec_ref(v_as_1125_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_createModuleTreeRef(lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_){
_start:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1167_ = ((lean_object*)(l_Lean_Meta_Rewrites_createModuleTreeRef___closed__0));
v___x_1168_ = ((lean_object*)(l_Lean_Meta_Rewrites_droppedKeys));
v___x_1169_ = lean_box(0);
v___x_1170_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v___x_1167_, v___x_1168_, v___x_1169_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_createModuleTreeRef___boxed(lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l_Lean_Meta_Rewrites_createModuleTreeRef(v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_);
lean_dec(v_a_1174_);
lean_dec_ref(v_a_1173_);
lean_dec(v_a_1172_);
lean_dec_ref(v_a_1171_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_1824551397____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1178_ = lean_box(0);
v___x_1179_ = lean_st_mk_ref(v___x_1178_);
v___x_1180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1179_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_1824551397____hygCtx___hyg_2____boxed(lean_object* v_a_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_1824551397____hygCtx___hyg_2_();
return v_res_1182_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_constantsPerImportTask(void){
_start:
{
lean_object* v___x_1183_; 
v___x_1183_ = lean_unsigned_to_nat(6500u);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_incPrio(lean_object* v_x_1184_, lean_object* v_x_1185_){
_start:
{
lean_object* v_snd_1186_; uint8_t v___x_1187_; 
v_snd_1186_ = lean_ctor_get(v_x_1185_, 1);
v___x_1187_ = lean_unbox(v_snd_1186_);
if (v___x_1187_ == 0)
{
lean_object* v_fst_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1200_; 
v_fst_1188_ = lean_ctor_get(v_x_1185_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v_x_1185_);
if (v_isSharedCheck_1200_ == 0)
{
lean_object* v_unused_1201_; 
v_unused_1201_ = lean_ctor_get(v_x_1185_, 1);
lean_dec(v_unused_1201_);
v___x_1190_ = v_x_1185_;
v_isShared_1191_ = v_isSharedCheck_1200_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_fst_1188_);
lean_dec(v_x_1185_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1200_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
uint8_t v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1197_; 
v___x_1192_ = 0;
v___x_1193_ = lean_unsigned_to_nat(2u);
v___x_1194_ = lean_nat_mul(v___x_1193_, v_x_1184_);
lean_dec(v_x_1184_);
v___x_1195_ = lean_box(v___x_1192_);
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 1, v___x_1194_);
lean_ctor_set(v___x_1190_, 0, v___x_1195_);
v___x_1197_ = v___x_1190_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1195_);
lean_ctor_set(v_reuseFailAlloc_1199_, 1, v___x_1194_);
v___x_1197_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
lean_object* v___x_1198_; 
v___x_1198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1198_, 0, v_fst_1188_);
lean_ctor_set(v___x_1198_, 1, v___x_1197_);
return v___x_1198_;
}
}
}
else
{
lean_object* v_fst_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1212_; 
v_fst_1202_ = lean_ctor_get(v_x_1185_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v_x_1185_);
if (v_isSharedCheck_1212_ == 0)
{
lean_object* v_unused_1213_; 
v_unused_1213_ = lean_ctor_get(v_x_1185_, 1);
lean_dec(v_unused_1213_);
v___x_1204_ = v_x_1185_;
v_isShared_1205_ = v_isSharedCheck_1212_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_fst_1202_);
lean_dec(v_x_1185_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1212_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
uint8_t v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1209_; 
v___x_1206_ = 1;
v___x_1207_ = lean_box(v___x_1206_);
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 1, v_x_1184_);
lean_ctor_set(v___x_1204_, 0, v___x_1207_);
v___x_1209_ = v___x_1204_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v___x_1207_);
lean_ctor_set(v_reuseFailAlloc_1211_, 1, v_x_1184_);
v___x_1209_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
lean_object* v___x_1210_; 
v___x_1210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1210_, 0, v_fst_1202_);
lean_ctor_set(v___x_1210_, 1, v___x_1209_);
return v___x_1210_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwFindDecls(lean_object* v_moduleRef_1215_, lean_object* v_ty_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_){
_start:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1222_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_ext;
v___x_1223_ = ((lean_object*)(l_Lean_Meta_Rewrites_createModuleTreeRef___closed__0));
v___x_1224_ = ((lean_object*)(l_Lean_Meta_Rewrites_droppedKeys));
v___x_1225_ = lean_unsigned_to_nat(6500u);
v___x_1226_ = lean_box(0);
v___x_1227_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwFindDecls___closed__0));
v___x_1228_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_moduleRef_1215_, v___x_1222_, v___x_1223_, v___x_1224_, v___x_1225_, v___x_1226_, v___x_1227_, v_ty_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_);
return v___x_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwFindDecls___boxed(lean_object* v_moduleRef_1229_, lean_object* v_ty_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l_Lean_Meta_Rewrites_rwFindDecls(v_moduleRef_1229_, v_ty_1230_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_);
lean_dec(v_a_1234_);
lean_dec_ref(v_a_1233_);
lean_dec(v_a_1232_);
lean_dec_ref(v_a_1231_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg(lean_object* v_mctx_1237_, lean_object* v_x_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
lean_object* v___x_1244_; 
v___x_1244_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp(lean_box(0), v_mctx_1237_, v_x_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_object* v_a_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1252_; 
v_a_1245_ = lean_ctor_get(v___x_1244_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1247_ = v___x_1244_;
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_a_1245_);
lean_dec(v___x_1244_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1250_; 
if (v_isShared_1248_ == 0)
{
v___x_1250_ = v___x_1247_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_a_1245_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
else
{
lean_object* v_a_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1260_; 
v_a_1253_ = lean_ctor_get(v___x_1244_, 0);
v_isSharedCheck_1260_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1255_ = v___x_1244_;
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_a_1253_);
lean_dec(v___x_1244_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1258_; 
if (v_isShared_1256_ == 0)
{
v___x_1258_ = v___x_1255_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_a_1253_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg___boxed(lean_object* v_mctx_1261_, lean_object* v_x_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
lean_object* v_res_1268_; 
v_res_1268_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg(v_mctx_1261_, v_x_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
lean_dec(v___y_1264_);
lean_dec_ref(v___y_1263_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0(lean_object* v_00_u03b1_1269_, lean_object* v_mctx_1270_, lean_object* v_x_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_){
_start:
{
lean_object* v___x_1277_; 
v___x_1277_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg(v_mctx_1270_, v_x_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___boxed(lean_object* v_00_u03b1_1278_, lean_object* v_mctx_1279_, lean_object* v_x_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_){
_start:
{
lean_object* v_res_1286_; 
v_res_1286_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0(v_00_u03b1_1278_, v_mctx_1279_, v_x_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(lean_object* v_x_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_){
_start:
{
lean_object* v___x_1293_; 
v___x_1293_ = l_Lean_Meta_saveState___redArg(v___y_1289_, v___y_1291_);
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v_a_1294_; lean_object* v_r_1295_; 
v_a_1294_ = lean_ctor_get(v___x_1293_, 0);
lean_inc(v_a_1294_);
lean_dec_ref_known(v___x_1293_, 1);
lean_inc(v___y_1291_);
lean_inc_ref(v___y_1290_);
lean_inc(v___y_1289_);
lean_inc_ref(v___y_1288_);
v_r_1295_ = lean_apply_5(v_x_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, lean_box(0));
if (lean_obj_tag(v_r_1295_) == 0)
{
lean_object* v_a_1296_; lean_object* v___x_1297_; 
v_a_1296_ = lean_ctor_get(v_r_1295_, 0);
lean_inc(v_a_1296_);
lean_dec_ref_known(v_r_1295_, 1);
v___x_1297_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1294_, v___y_1289_, v___y_1291_);
lean_dec(v_a_1294_);
if (lean_obj_tag(v___x_1297_) == 0)
{
lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1304_; 
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1304_ == 0)
{
lean_object* v_unused_1305_; 
v_unused_1305_ = lean_ctor_get(v___x_1297_, 0);
lean_dec(v_unused_1305_);
v___x_1299_ = v___x_1297_;
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
else
{
lean_dec(v___x_1297_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1302_; 
if (v_isShared_1300_ == 0)
{
lean_ctor_set(v___x_1299_, 0, v_a_1296_);
v___x_1302_ = v___x_1299_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_a_1296_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
else
{
lean_object* v_a_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1313_; 
lean_dec(v_a_1296_);
v_a_1306_ = lean_ctor_get(v___x_1297_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1308_ = v___x_1297_;
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_a_1306_);
lean_dec(v___x_1297_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1311_; 
if (v_isShared_1309_ == 0)
{
v___x_1311_ = v___x_1308_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_a_1306_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
}
else
{
lean_object* v_a_1314_; lean_object* v___x_1315_; 
v_a_1314_ = lean_ctor_get(v_r_1295_, 0);
lean_inc(v_a_1314_);
lean_dec_ref_known(v_r_1295_, 1);
v___x_1315_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1294_, v___y_1289_, v___y_1291_);
lean_dec(v_a_1294_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1322_; 
v_isSharedCheck_1322_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1322_ == 0)
{
lean_object* v_unused_1323_; 
v_unused_1323_ = lean_ctor_get(v___x_1315_, 0);
lean_dec(v_unused_1323_);
v___x_1317_ = v___x_1315_;
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
else
{
lean_dec(v___x_1315_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1320_; 
if (v_isShared_1318_ == 0)
{
lean_ctor_set_tag(v___x_1317_, 1);
lean_ctor_set(v___x_1317_, 0, v_a_1314_);
v___x_1320_ = v___x_1317_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_a_1314_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
}
else
{
lean_object* v_a_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1331_; 
lean_dec(v_a_1314_);
v_a_1324_ = lean_ctor_get(v___x_1315_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1326_ = v___x_1315_;
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_a_1324_);
lean_dec(v___x_1315_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1329_; 
if (v_isShared_1327_ == 0)
{
v___x_1329_ = v___x_1326_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_a_1324_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
}
}
}
else
{
lean_object* v_a_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1339_; 
lean_dec_ref(v_x_1287_);
v_a_1332_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1334_ = v___x_1293_;
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_a_1332_);
lean_dec(v___x_1293_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1337_; 
if (v_isShared_1335_ == 0)
{
v___x_1337_ = v___x_1334_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_a_1332_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg___boxed(lean_object* v_x_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v_x_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_);
lean_dec(v___y_1344_);
lean_dec_ref(v___y_1343_);
lean_dec(v___y_1342_);
lean_dec_ref(v___y_1341_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1(lean_object* v_00_u03b1_1347_, lean_object* v_x_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_){
_start:
{
lean_object* v___x_1354_; 
v___x_1354_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v_x_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___boxed(lean_object* v_00_u03b1_1355_, lean_object* v_x_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_){
_start:
{
lean_object* v_res_1362_; 
v_res_1362_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1(v_00_u03b1_1355_, v_x_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_);
lean_dec(v___y_1360_);
lean_dec_ref(v___y_1359_);
lean_dec(v___y_1358_);
lean_dec_ref(v___y_1357_);
return v_res_1362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0(lean_object* v___x_1363_, uint8_t v___x_1364_, lean_object* v___x_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_){
_start:
{
lean_object* v___x_1371_; 
v___x_1371_ = l_Lean_Meta_mkFreshExprMVar(v___x_1363_, v___x_1364_, v___x_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_);
if (lean_obj_tag(v___x_1371_) == 0)
{
lean_object* v_a_1372_; lean_object* v_keyedConfig_1373_; uint8_t v_trackZetaDelta_1374_; lean_object* v_zetaDeltaSet_1375_; lean_object* v_lctx_1376_; lean_object* v_localInstances_1377_; lean_object* v_defEqCtx_x3f_1378_; lean_object* v_synthPendingDepth_1379_; lean_object* v_customCanUnfoldPredicate_x3f_1380_; uint8_t v_univApprox_1381_; uint8_t v_inTypeClassResolution_1382_; uint8_t v_cacheInferType_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1412_; 
v_a_1372_ = lean_ctor_get(v___x_1371_, 0);
lean_inc(v_a_1372_);
lean_dec_ref_known(v___x_1371_, 1);
v_keyedConfig_1373_ = lean_ctor_get(v___y_1366_, 0);
v_trackZetaDelta_1374_ = lean_ctor_get_uint8(v___y_1366_, sizeof(void*)*7);
v_zetaDeltaSet_1375_ = lean_ctor_get(v___y_1366_, 1);
v_lctx_1376_ = lean_ctor_get(v___y_1366_, 2);
v_localInstances_1377_ = lean_ctor_get(v___y_1366_, 3);
v_defEqCtx_x3f_1378_ = lean_ctor_get(v___y_1366_, 4);
v_synthPendingDepth_1379_ = lean_ctor_get(v___y_1366_, 5);
v_customCanUnfoldPredicate_x3f_1380_ = lean_ctor_get(v___y_1366_, 6);
v_univApprox_1381_ = lean_ctor_get_uint8(v___y_1366_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1382_ = lean_ctor_get_uint8(v___y_1366_, sizeof(void*)*7 + 2);
v_cacheInferType_1383_ = lean_ctor_get_uint8(v___y_1366_, sizeof(void*)*7 + 3);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___y_1366_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1385_ = v___y_1366_;
v_isShared_1386_ = v_isSharedCheck_1412_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_1380_);
lean_inc(v_synthPendingDepth_1379_);
lean_inc(v_defEqCtx_x3f_1378_);
lean_inc(v_localInstances_1377_);
lean_inc(v_lctx_1376_);
lean_inc(v_zetaDeltaSet_1375_);
lean_inc(v_keyedConfig_1373_);
lean_dec(v___y_1366_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1412_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1387_; uint8_t v___x_1388_; uint8_t v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1392_; 
v___x_1387_ = l_Lean_Expr_mvarId_x21(v_a_1372_);
lean_dec(v_a_1372_);
v___x_1388_ = 1;
v___x_1389_ = 2;
v___x_1390_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1389_, v_keyedConfig_1373_);
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 0, v___x_1390_);
v___x_1392_ = v___x_1385_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v___x_1390_);
lean_ctor_set(v_reuseFailAlloc_1411_, 1, v_zetaDeltaSet_1375_);
lean_ctor_set(v_reuseFailAlloc_1411_, 2, v_lctx_1376_);
lean_ctor_set(v_reuseFailAlloc_1411_, 3, v_localInstances_1377_);
lean_ctor_set(v_reuseFailAlloc_1411_, 4, v_defEqCtx_x3f_1378_);
lean_ctor_set(v_reuseFailAlloc_1411_, 5, v_synthPendingDepth_1379_);
lean_ctor_set(v_reuseFailAlloc_1411_, 6, v_customCanUnfoldPredicate_x3f_1380_);
lean_ctor_set_uint8(v_reuseFailAlloc_1411_, sizeof(void*)*7, v_trackZetaDelta_1374_);
lean_ctor_set_uint8(v_reuseFailAlloc_1411_, sizeof(void*)*7 + 1, v_univApprox_1381_);
lean_ctor_set_uint8(v_reuseFailAlloc_1411_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1382_);
lean_ctor_set_uint8(v_reuseFailAlloc_1411_, sizeof(void*)*7 + 3, v_cacheInferType_1383_);
v___x_1392_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
lean_object* v___x_1393_; 
v___x_1393_ = l_Lean_MVarId_refl(v___x_1387_, v___x_1388_, v___x_1392_, v___y_1367_, v___y_1368_, v___y_1369_);
lean_dec_ref(v___x_1392_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1401_; 
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1401_ == 0)
{
lean_object* v_unused_1402_; 
v_unused_1402_ = lean_ctor_get(v___x_1393_, 0);
lean_dec(v_unused_1402_);
v___x_1395_ = v___x_1393_;
v_isShared_1396_ = v_isSharedCheck_1401_;
goto v_resetjp_1394_;
}
else
{
lean_dec(v___x_1393_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1401_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1397_; lean_object* v___x_1399_; 
v___x_1397_ = lean_box(v___x_1388_);
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 0, v___x_1397_);
v___x_1399_ = v___x_1395_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v___x_1397_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
}
else
{
lean_object* v_a_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1410_; 
v_a_1403_ = lean_ctor_get(v___x_1393_, 0);
v_isSharedCheck_1410_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1405_ = v___x_1393_;
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_a_1403_);
lean_dec(v___x_1393_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1408_; 
if (v_isShared_1406_ == 0)
{
v___x_1408_ = v___x_1405_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_a_1403_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
}
}
}
else
{
lean_object* v_a_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1420_; 
lean_dec_ref(v___y_1366_);
v_a_1413_ = lean_ctor_get(v___x_1371_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1371_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1415_ = v___x_1371_;
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_a_1413_);
lean_dec(v___x_1371_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1418_; 
if (v_isShared_1416_ == 0)
{
v___x_1418_ = v___x_1415_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_a_1413_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___boxed(lean_object* v___x_1421_, lean_object* v___x_1422_, lean_object* v___x_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_){
_start:
{
uint8_t v___x_2168__boxed_1429_; lean_object* v_res_1430_; 
v___x_2168__boxed_1429_ = lean_unbox(v___x_1422_);
v_res_1430_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0(v___x_1421_, v___x_2168__boxed_1429_, v___x_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
lean_dec(v___y_1425_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(lean_object* v_mctx_1431_, lean_object* v_e_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_){
_start:
{
lean_object* v___x_1438_; uint8_t v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___f_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1438_, 0, v_e_1432_);
v___x_1439_ = 0;
v___x_1440_ = lean_box(0);
v___x_1441_ = lean_box(v___x_1439_);
v___f_1442_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1442_, 0, v___x_1438_);
lean_closure_set(v___f_1442_, 1, v___x_1441_);
lean_closure_set(v___f_1442_, 2, v___x_1440_);
v___x_1443_ = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___boxed), 8, 3);
lean_closure_set(v___x_1443_, 0, lean_box(0));
lean_closure_set(v___x_1443_, 1, v_mctx_1431_);
lean_closure_set(v___x_1443_, 2, v___f_1442_);
v___x_1444_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v___x_1443_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_);
if (lean_obj_tag(v___x_1444_) == 0)
{
return v___x_1444_;
}
else
{
lean_object* v_a_1445_; uint8_t v___y_1447_; uint8_t v___x_1457_; 
v_a_1445_ = lean_ctor_get(v___x_1444_, 0);
lean_inc(v_a_1445_);
v___x_1457_ = l_Lean_Exception_isInterrupt(v_a_1445_);
if (v___x_1457_ == 0)
{
uint8_t v___x_1458_; 
v___x_1458_ = l_Lean_Exception_isRuntime(v_a_1445_);
v___y_1447_ = v___x_1458_;
goto v___jp_1446_;
}
else
{
lean_dec(v_a_1445_);
v___y_1447_ = v___x_1457_;
goto v___jp_1446_;
}
v___jp_1446_:
{
if (v___y_1447_ == 0)
{
lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1455_; 
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1455_ == 0)
{
lean_object* v_unused_1456_; 
v_unused_1456_ = lean_ctor_get(v___x_1444_, 0);
lean_dec(v_unused_1456_);
v___x_1449_ = v___x_1444_;
v_isShared_1450_ = v_isSharedCheck_1455_;
goto v_resetjp_1448_;
}
else
{
lean_dec(v___x_1444_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1455_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1451_; lean_object* v___x_1453_; 
v___x_1451_ = lean_box(v___y_1447_);
if (v_isShared_1450_ == 0)
{
lean_ctor_set_tag(v___x_1449_, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1451_);
v___x_1453_ = v___x_1449_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v___x_1451_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
return v___x_1453_;
}
}
}
else
{
return v___x_1444_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___boxed(lean_object* v_mctx_1459_, lean_object* v_e_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_){
_start:
{
lean_object* v_res_1466_; 
v_res_1466_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(v_mctx_1459_, v_e_1460_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_);
lean_dec(v_a_1464_);
lean_dec_ref(v_a_1463_);
lean_dec(v_a_1462_);
lean_dec_ref(v_a_1461_);
return v_res_1466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult(lean_object* v_r_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_){
_start:
{
lean_object* v_result_1473_; lean_object* v_eNew_1474_; lean_object* v___x_1475_; 
v_result_1473_ = lean_ctor_get(v_r_1467_, 2);
lean_inc_ref(v_result_1473_);
lean_dec_ref(v_r_1467_);
v_eNew_1474_ = lean_ctor_get(v_result_1473_, 0);
lean_inc_ref(v_eNew_1474_);
lean_dec_ref(v_result_1473_);
v___x_1475_ = l_Lean_Meta_ppExpr(v_eNew_1474_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1486_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1478_ = v___x_1475_;
v_isShared_1479_ = v_isSharedCheck_1486_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1475_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1486_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1484_; 
v___x_1480_ = l_Std_Format_defWidth;
v___x_1481_ = lean_unsigned_to_nat(0u);
v___x_1482_ = l_Std_Format_pretty(v_a_1476_, v___x_1480_, v___x_1481_, v___x_1481_);
if (v_isShared_1479_ == 0)
{
lean_ctor_set(v___x_1478_, 0, v___x_1482_);
v___x_1484_ = v___x_1478_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v___x_1482_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
else
{
lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1494_; 
v_a_1487_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1489_ = v___x_1475_;
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v___x_1475_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1492_; 
if (v_isShared_1490_ == 0)
{
v___x_1492_ = v___x_1489_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_a_1487_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult___boxed(lean_object* v_r_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult(v_r_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_);
lean_dec(v_a_1499_);
lean_dec_ref(v_a_1498_);
lean_dec(v_a_1497_);
lean_dec_ref(v_a_1496_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorIdx(uint8_t v_x_1502_){
_start:
{
switch(v_x_1502_)
{
case 0:
{
lean_object* v___x_1503_; 
v___x_1503_ = lean_unsigned_to_nat(0u);
return v___x_1503_;
}
case 1:
{
lean_object* v___x_1504_; 
v___x_1504_ = lean_unsigned_to_nat(1u);
return v___x_1504_;
}
default: 
{
lean_object* v___x_1505_; 
v___x_1505_ = lean_unsigned_to_nat(2u);
return v___x_1505_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorIdx___boxed(lean_object* v_x_1506_){
_start:
{
uint8_t v_x_boxed_1507_; lean_object* v_res_1508_; 
v_x_boxed_1507_ = lean_unbox(v_x_1506_);
v_res_1508_ = l_Lean_Meta_Rewrites_SideConditions_ctorIdx(v_x_boxed_1507_);
return v_res_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_toCtorIdx(uint8_t v_x_1509_){
_start:
{
lean_object* v___x_1510_; 
v___x_1510_ = l_Lean_Meta_Rewrites_SideConditions_ctorIdx(v_x_1509_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_toCtorIdx___boxed(lean_object* v_x_1511_){
_start:
{
uint8_t v_x_4__boxed_1512_; lean_object* v_res_1513_; 
v_x_4__boxed_1512_ = lean_unbox(v_x_1511_);
v_res_1513_ = l_Lean_Meta_Rewrites_SideConditions_toCtorIdx(v_x_4__boxed_1512_);
return v_res_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorElim___redArg(lean_object* v_k_1514_){
_start:
{
lean_inc(v_k_1514_);
return v_k_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorElim___redArg___boxed(lean_object* v_k_1515_){
_start:
{
lean_object* v_res_1516_; 
v_res_1516_ = l_Lean_Meta_Rewrites_SideConditions_ctorElim___redArg(v_k_1515_);
lean_dec(v_k_1515_);
return v_res_1516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorElim(lean_object* v_motive_1517_, lean_object* v_ctorIdx_1518_, uint8_t v_t_1519_, lean_object* v_h_1520_, lean_object* v_k_1521_){
_start:
{
lean_inc(v_k_1521_);
return v_k_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorElim___boxed(lean_object* v_motive_1522_, lean_object* v_ctorIdx_1523_, lean_object* v_t_1524_, lean_object* v_h_1525_, lean_object* v_k_1526_){
_start:
{
uint8_t v_t_boxed_1527_; lean_object* v_res_1528_; 
v_t_boxed_1527_ = lean_unbox(v_t_1524_);
v_res_1528_ = l_Lean_Meta_Rewrites_SideConditions_ctorElim(v_motive_1522_, v_ctorIdx_1523_, v_t_boxed_1527_, v_h_1525_, v_k_1526_);
lean_dec(v_k_1526_);
lean_dec(v_ctorIdx_1523_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_none_elim___redArg(lean_object* v_none_1529_){
_start:
{
lean_inc(v_none_1529_);
return v_none_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_none_elim___redArg___boxed(lean_object* v_none_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l_Lean_Meta_Rewrites_SideConditions_none_elim___redArg(v_none_1530_);
lean_dec(v_none_1530_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_none_elim(lean_object* v_motive_1532_, uint8_t v_t_1533_, lean_object* v_h_1534_, lean_object* v_none_1535_){
_start:
{
lean_inc(v_none_1535_);
return v_none_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_none_elim___boxed(lean_object* v_motive_1536_, lean_object* v_t_1537_, lean_object* v_h_1538_, lean_object* v_none_1539_){
_start:
{
uint8_t v_t_boxed_1540_; lean_object* v_res_1541_; 
v_t_boxed_1540_ = lean_unbox(v_t_1537_);
v_res_1541_ = l_Lean_Meta_Rewrites_SideConditions_none_elim(v_motive_1536_, v_t_boxed_1540_, v_h_1538_, v_none_1539_);
lean_dec(v_none_1539_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_assumption_elim___redArg(lean_object* v_assumption_1542_){
_start:
{
lean_inc(v_assumption_1542_);
return v_assumption_1542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_assumption_elim___redArg___boxed(lean_object* v_assumption_1543_){
_start:
{
lean_object* v_res_1544_; 
v_res_1544_ = l_Lean_Meta_Rewrites_SideConditions_assumption_elim___redArg(v_assumption_1543_);
lean_dec(v_assumption_1543_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_assumption_elim(lean_object* v_motive_1545_, uint8_t v_t_1546_, lean_object* v_h_1547_, lean_object* v_assumption_1548_){
_start:
{
lean_inc(v_assumption_1548_);
return v_assumption_1548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_assumption_elim___boxed(lean_object* v_motive_1549_, lean_object* v_t_1550_, lean_object* v_h_1551_, lean_object* v_assumption_1552_){
_start:
{
uint8_t v_t_boxed_1553_; lean_object* v_res_1554_; 
v_t_boxed_1553_ = lean_unbox(v_t_1550_);
v_res_1554_ = l_Lean_Meta_Rewrites_SideConditions_assumption_elim(v_motive_1549_, v_t_boxed_1553_, v_h_1551_, v_assumption_1552_);
lean_dec(v_assumption_1552_);
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim___redArg(lean_object* v_solveByElim_1555_){
_start:
{
lean_inc(v_solveByElim_1555_);
return v_solveByElim_1555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim___redArg___boxed(lean_object* v_solveByElim_1556_){
_start:
{
lean_object* v_res_1557_; 
v_res_1557_ = l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim___redArg(v_solveByElim_1556_);
lean_dec(v_solveByElim_1556_);
return v_res_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim(lean_object* v_motive_1558_, uint8_t v_t_1559_, lean_object* v_h_1560_, lean_object* v_solveByElim_1561_){
_start:
{
lean_inc(v_solveByElim_1561_);
return v_solveByElim_1561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim___boxed(lean_object* v_motive_1562_, lean_object* v_t_1563_, lean_object* v_h_1564_, lean_object* v_solveByElim_1565_){
_start:
{
uint8_t v_t_boxed_1566_; lean_object* v_res_1567_; 
v_t_boxed_1566_ = lean_unbox(v_t_1563_);
v_res_1567_ = l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim(v_motive_1562_, v_t_boxed_1566_, v_h_1564_, v_solveByElim_1565_);
lean_dec(v_solveByElim_1565_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__0(lean_object* v_x_1568_, lean_object* v_x_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_){
_start:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1575_ = lean_box(0);
v___x_1576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1575_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__0___boxed(lean_object* v_x_1577_, lean_object* v_x_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_){
_start:
{
lean_object* v_res_1584_; 
v_res_1584_ = l_Lean_Meta_Rewrites_solveByElim___lam__0(v_x_1577_, v_x_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1581_);
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1579_);
lean_dec(v_x_1578_);
lean_dec(v_x_1577_);
return v_res_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__1(lean_object* v_x_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_){
_start:
{
uint8_t v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1591_ = 0;
v___x_1592_ = lean_box(v___x_1591_);
v___x_1593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1592_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__1___boxed(lean_object* v_x_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_){
_start:
{
lean_object* v_res_1600_; 
v_res_1600_ = l_Lean_Meta_Rewrites_solveByElim___lam__1(v_x_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1597_);
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1595_);
lean_dec(v_x_1594_);
return v_res_1600_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0(lean_object* v_msgData_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_){
_start:
{
lean_object* v___x_1607_; lean_object* v_env_1608_; lean_object* v___x_1609_; lean_object* v_mctx_1610_; lean_object* v_lctx_1611_; lean_object* v_options_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1607_ = lean_st_ref_get(v___y_1605_);
v_env_1608_ = lean_ctor_get(v___x_1607_, 0);
lean_inc_ref(v_env_1608_);
lean_dec(v___x_1607_);
v___x_1609_ = lean_st_ref_get(v___y_1603_);
v_mctx_1610_ = lean_ctor_get(v___x_1609_, 0);
lean_inc_ref(v_mctx_1610_);
lean_dec(v___x_1609_);
v_lctx_1611_ = lean_ctor_get(v___y_1602_, 2);
v_options_1612_ = lean_ctor_get(v___y_1604_, 2);
lean_inc_ref(v_options_1612_);
lean_inc_ref(v_lctx_1611_);
v___x_1613_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1613_, 0, v_env_1608_);
lean_ctor_set(v___x_1613_, 1, v_mctx_1610_);
lean_ctor_set(v___x_1613_, 2, v_lctx_1611_);
lean_ctor_set(v___x_1613_, 3, v_options_1612_);
v___x_1614_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1613_);
lean_ctor_set(v___x_1614_, 1, v_msgData_1601_);
v___x_1615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1614_);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0___boxed(lean_object* v_msgData_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_){
_start:
{
lean_object* v_res_1622_; 
v_res_1622_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0(v_msgData_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1617_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(lean_object* v_msg_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_){
_start:
{
lean_object* v_ref_1629_; lean_object* v___x_1630_; lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1639_; 
v_ref_1629_ = lean_ctor_get(v___y_1626_, 5);
v___x_1630_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0(v_msg_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_);
v_a_1631_ = lean_ctor_get(v___x_1630_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1633_ = v___x_1630_;
v_isShared_1634_ = v_isSharedCheck_1639_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_dec(v___x_1630_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1639_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1635_; lean_object* v___x_1637_; 
lean_inc(v_ref_1629_);
v___x_1635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1635_, 0, v_ref_1629_);
lean_ctor_set(v___x_1635_, 1, v_a_1631_);
if (v_isShared_1634_ == 0)
{
lean_ctor_set_tag(v___x_1633_, 1);
lean_ctor_set(v___x_1633_, 0, v___x_1635_);
v___x_1637_ = v___x_1633_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v___x_1635_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg___boxed(lean_object* v_msg_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(v_msg_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
return v_res_1646_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1648_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__0));
v___x_1649_ = l_Lean_stringToMessageData(v___x_1648_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__2(lean_object* v_x_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_){
_start:
{
lean_object* v___x_1656_; lean_object* v___x_1657_; 
v___x_1656_ = lean_obj_once(&l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1, &l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1_once, _init_l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1);
v___x_1657_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(v___x_1656_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__2___boxed(lean_object* v_x_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_){
_start:
{
lean_object* v_res_1664_; 
v_res_1664_ = l_Lean_Meta_Rewrites_solveByElim___lam__2(v_x_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_);
lean_dec(v___y_1662_);
lean_dec_ref(v___y_1661_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
lean_dec(v_x_1658_);
return v_res_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim(lean_object* v_goals_1674_, lean_object* v_depth_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_){
_start:
{
lean_object* v___f_1681_; lean_object* v___f_1682_; lean_object* v___f_1683_; uint8_t v___x_1684_; lean_object* v___x_1685_; uint8_t v___x_1686_; lean_object* v___x_1687_; uint8_t v___x_1688_; lean_object* v___x_1689_; lean_object* v_cfg_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___f_1681_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___closed__0));
v___f_1682_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___closed__1));
v___f_1683_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___closed__2));
v___x_1684_ = 0;
v___x_1685_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1685_, 0, v_depth_1675_);
lean_ctor_set(v___x_1685_, 1, v___f_1681_);
lean_ctor_set(v___x_1685_, 2, v___f_1682_);
lean_ctor_set(v___x_1685_, 3, v___f_1683_);
lean_ctor_set_uint8(v___x_1685_, sizeof(void*)*4, v___x_1684_);
v___x_1686_ = 1;
v___x_1687_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___closed__3));
v___x_1688_ = 1;
v___x_1689_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_1689_, 0, v___x_1685_);
lean_ctor_set(v___x_1689_, 1, v___x_1687_);
lean_ctor_set_uint8(v___x_1689_, sizeof(void*)*2, v___x_1688_);
lean_ctor_set_uint8(v___x_1689_, sizeof(void*)*2 + 1, v___x_1686_);
lean_ctor_set_uint8(v___x_1689_, sizeof(void*)*2 + 2, v___x_1684_);
v_cfg_1690_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_cfg_1690_, 0, v___x_1689_);
lean_ctor_set_uint8(v_cfg_1690_, sizeof(void*)*1, v___x_1686_);
lean_ctor_set_uint8(v_cfg_1690_, sizeof(void*)*1 + 1, v___x_1686_);
lean_ctor_set_uint8(v_cfg_1690_, sizeof(void*)*1 + 2, v___x_1686_);
lean_ctor_set_uint8(v_cfg_1690_, sizeof(void*)*1 + 3, v___x_1684_);
v___x_1691_ = lean_box(0);
v___x_1692_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___closed__4));
v___x_1693_ = l_Lean_Meta_SolveByElim_mkAssumptionSet(v___x_1684_, v___x_1684_, v___x_1691_, v___x_1691_, v___x_1692_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_);
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_object* v_a_1694_; lean_object* v_fst_1695_; lean_object* v_snd_1696_; lean_object* v___x_1697_; 
v_a_1694_ = lean_ctor_get(v___x_1693_, 0);
lean_inc(v_a_1694_);
lean_dec_ref_known(v___x_1693_, 1);
v_fst_1695_ = lean_ctor_get(v_a_1694_, 0);
lean_inc(v_fst_1695_);
v_snd_1696_ = lean_ctor_get(v_a_1694_, 1);
lean_inc(v_snd_1696_);
lean_dec(v_a_1694_);
v___x_1697_ = l_Lean_Meta_SolveByElim_solveByElim(v_cfg_1690_, v_fst_1695_, v_snd_1696_, v_goals_1674_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_);
if (lean_obj_tag(v___x_1697_) == 0)
{
lean_object* v_a_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1708_; 
v_a_1698_ = lean_ctor_get(v___x_1697_, 0);
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1700_ = v___x_1697_;
v_isShared_1701_ = v_isSharedCheck_1708_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_a_1698_);
lean_dec(v___x_1697_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1708_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
if (lean_obj_tag(v_a_1698_) == 0)
{
lean_object* v___x_1702_; lean_object* v___x_1704_; 
v___x_1702_ = lean_box(0);
if (v_isShared_1701_ == 0)
{
lean_ctor_set(v___x_1700_, 0, v___x_1702_);
v___x_1704_ = v___x_1700_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v___x_1702_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
else
{
lean_object* v___x_1706_; lean_object* v___x_1707_; 
lean_del_object(v___x_1700_);
lean_dec(v_a_1698_);
v___x_1706_ = lean_obj_once(&l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1, &l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1_once, _init_l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1);
v___x_1707_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(v___x_1706_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_);
return v___x_1707_;
}
}
}
else
{
lean_object* v_a_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1716_; 
v_a_1709_ = lean_ctor_get(v___x_1697_, 0);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1711_ = v___x_1697_;
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_a_1709_);
lean_dec(v___x_1697_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1714_; 
if (v_isShared_1712_ == 0)
{
v___x_1714_ = v___x_1711_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v_a_1709_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
return v___x_1714_;
}
}
}
}
else
{
lean_object* v_a_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1724_; 
lean_dec_ref_known(v_cfg_1690_, 1);
lean_dec(v_goals_1674_);
v_a_1717_ = lean_ctor_get(v___x_1693_, 0);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1719_ = v___x_1693_;
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_a_1717_);
lean_dec(v___x_1693_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1722_; 
if (v_isShared_1720_ == 0)
{
v___x_1722_ = v___x_1719_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_a_1717_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___boxed(lean_object* v_goals_1725_, lean_object* v_depth_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_){
_start:
{
lean_object* v_res_1732_; 
v_res_1732_ = l_Lean_Meta_Rewrites_solveByElim(v_goals_1725_, v_depth_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_);
lean_dec(v_a_1730_);
lean_dec_ref(v_a_1729_);
lean_dec(v_a_1728_);
lean_dec_ref(v_a_1727_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0(lean_object* v_00_u03b1_1733_, lean_object* v_msg_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
lean_object* v___x_1740_; 
v___x_1740_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(v_msg_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___boxed(lean_object* v_00_u03b1_1741_, lean_object* v_msg_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_){
_start:
{
lean_object* v_res_1748_; 
v_res_1748_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0(v_00_u03b1_1741_, v_msg_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_);
lean_dec(v___y_1746_);
lean_dec_ref(v___y_1745_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg(lean_object* v_e_1749_, lean_object* v___y_1750_){
_start:
{
uint8_t v___x_1752_; 
v___x_1752_ = l_Lean_Expr_hasMVar(v_e_1749_);
if (v___x_1752_ == 0)
{
lean_object* v___x_1753_; 
v___x_1753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1753_, 0, v_e_1749_);
return v___x_1753_;
}
else
{
lean_object* v___x_1754_; lean_object* v_mctx_1755_; lean_object* v___x_1756_; lean_object* v_fst_1757_; lean_object* v_snd_1758_; lean_object* v___x_1759_; lean_object* v_cache_1760_; lean_object* v_zetaDeltaFVarIds_1761_; lean_object* v_postponed_1762_; lean_object* v_diag_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1772_; 
v___x_1754_ = lean_st_ref_get(v___y_1750_);
v_mctx_1755_ = lean_ctor_get(v___x_1754_, 0);
lean_inc_ref(v_mctx_1755_);
lean_dec(v___x_1754_);
v___x_1756_ = l_Lean_instantiateMVarsCore(v_mctx_1755_, v_e_1749_);
v_fst_1757_ = lean_ctor_get(v___x_1756_, 0);
lean_inc(v_fst_1757_);
v_snd_1758_ = lean_ctor_get(v___x_1756_, 1);
lean_inc(v_snd_1758_);
lean_dec_ref(v___x_1756_);
v___x_1759_ = lean_st_ref_take(v___y_1750_);
v_cache_1760_ = lean_ctor_get(v___x_1759_, 1);
v_zetaDeltaFVarIds_1761_ = lean_ctor_get(v___x_1759_, 2);
v_postponed_1762_ = lean_ctor_get(v___x_1759_, 3);
v_diag_1763_ = lean_ctor_get(v___x_1759_, 4);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1772_ == 0)
{
lean_object* v_unused_1773_; 
v_unused_1773_ = lean_ctor_get(v___x_1759_, 0);
lean_dec(v_unused_1773_);
v___x_1765_ = v___x_1759_;
v_isShared_1766_ = v_isSharedCheck_1772_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_diag_1763_);
lean_inc(v_postponed_1762_);
lean_inc(v_zetaDeltaFVarIds_1761_);
lean_inc(v_cache_1760_);
lean_dec(v___x_1759_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1772_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1768_; 
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 0, v_snd_1758_);
v___x_1768_ = v___x_1765_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_snd_1758_);
lean_ctor_set(v_reuseFailAlloc_1771_, 1, v_cache_1760_);
lean_ctor_set(v_reuseFailAlloc_1771_, 2, v_zetaDeltaFVarIds_1761_);
lean_ctor_set(v_reuseFailAlloc_1771_, 3, v_postponed_1762_);
lean_ctor_set(v_reuseFailAlloc_1771_, 4, v_diag_1763_);
v___x_1768_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1769_ = lean_st_ref_set(v___y_1750_, v___x_1768_);
v___x_1770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1770_, 0, v_fst_1757_);
return v___x_1770_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg___boxed(lean_object* v_e_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg(v_e_1774_, v___y_1775_);
lean_dec(v___y_1775_);
return v_res_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0(lean_object* v_e_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_){
_start:
{
lean_object* v___x_1784_; 
v___x_1784_ = l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg(v_e_1778_, v___y_1780_);
return v___x_1784_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___boxed(lean_object* v_e_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
lean_object* v_res_1791_; 
v_res_1791_ = l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0(v_e_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
return v_res_1791_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1792_; double v___x_1793_; 
v___x_1792_ = lean_unsigned_to_nat(0u);
v___x_1793_ = lean_float_of_nat(v___x_1792_);
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2(lean_object* v_cls_1797_, lean_object* v_msg_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_){
_start:
{
lean_object* v_ref_1804_; lean_object* v___x_1805_; lean_object* v_a_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1850_; 
v_ref_1804_ = lean_ctor_get(v___y_1801_, 5);
v___x_1805_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0(v_msg_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_);
v_a_1806_ = lean_ctor_get(v___x_1805_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1808_ = v___x_1805_;
v_isShared_1809_ = v_isSharedCheck_1850_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_a_1806_);
lean_dec(v___x_1805_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1850_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1810_; lean_object* v_traceState_1811_; lean_object* v_env_1812_; lean_object* v_nextMacroScope_1813_; lean_object* v_ngen_1814_; lean_object* v_auxDeclNGen_1815_; lean_object* v_cache_1816_; lean_object* v_messages_1817_; lean_object* v_infoState_1818_; lean_object* v_snapshotTasks_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1849_; 
v___x_1810_ = lean_st_ref_take(v___y_1802_);
v_traceState_1811_ = lean_ctor_get(v___x_1810_, 4);
v_env_1812_ = lean_ctor_get(v___x_1810_, 0);
v_nextMacroScope_1813_ = lean_ctor_get(v___x_1810_, 1);
v_ngen_1814_ = lean_ctor_get(v___x_1810_, 2);
v_auxDeclNGen_1815_ = lean_ctor_get(v___x_1810_, 3);
v_cache_1816_ = lean_ctor_get(v___x_1810_, 5);
v_messages_1817_ = lean_ctor_get(v___x_1810_, 6);
v_infoState_1818_ = lean_ctor_get(v___x_1810_, 7);
v_snapshotTasks_1819_ = lean_ctor_get(v___x_1810_, 8);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1821_ = v___x_1810_;
v_isShared_1822_ = v_isSharedCheck_1849_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_snapshotTasks_1819_);
lean_inc(v_infoState_1818_);
lean_inc(v_messages_1817_);
lean_inc(v_cache_1816_);
lean_inc(v_traceState_1811_);
lean_inc(v_auxDeclNGen_1815_);
lean_inc(v_ngen_1814_);
lean_inc(v_nextMacroScope_1813_);
lean_inc(v_env_1812_);
lean_dec(v___x_1810_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1849_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
uint64_t v_tid_1823_; lean_object* v_traces_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1848_; 
v_tid_1823_ = lean_ctor_get_uint64(v_traceState_1811_, sizeof(void*)*1);
v_traces_1824_ = lean_ctor_get(v_traceState_1811_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v_traceState_1811_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1826_ = v_traceState_1811_;
v_isShared_1827_ = v_isSharedCheck_1848_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_traces_1824_);
lean_dec(v_traceState_1811_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1848_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1828_; double v___x_1829_; uint8_t v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1838_; 
v___x_1828_ = lean_box(0);
v___x_1829_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__0);
v___x_1830_ = 0;
v___x_1831_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__1));
v___x_1832_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1832_, 0, v_cls_1797_);
lean_ctor_set(v___x_1832_, 1, v___x_1828_);
lean_ctor_set(v___x_1832_, 2, v___x_1831_);
lean_ctor_set_float(v___x_1832_, sizeof(void*)*3, v___x_1829_);
lean_ctor_set_float(v___x_1832_, sizeof(void*)*3 + 8, v___x_1829_);
lean_ctor_set_uint8(v___x_1832_, sizeof(void*)*3 + 16, v___x_1830_);
v___x_1833_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__2));
v___x_1834_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1832_);
lean_ctor_set(v___x_1834_, 1, v_a_1806_);
lean_ctor_set(v___x_1834_, 2, v___x_1833_);
lean_inc(v_ref_1804_);
v___x_1835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1835_, 0, v_ref_1804_);
lean_ctor_set(v___x_1835_, 1, v___x_1834_);
v___x_1836_ = l_Lean_PersistentArray_push___redArg(v_traces_1824_, v___x_1835_);
if (v_isShared_1827_ == 0)
{
lean_ctor_set(v___x_1826_, 0, v___x_1836_);
v___x_1838_ = v___x_1826_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v___x_1836_);
lean_ctor_set_uint64(v_reuseFailAlloc_1847_, sizeof(void*)*1, v_tid_1823_);
v___x_1838_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
lean_object* v___x_1840_; 
if (v_isShared_1822_ == 0)
{
lean_ctor_set(v___x_1821_, 4, v___x_1838_);
v___x_1840_ = v___x_1821_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v_env_1812_);
lean_ctor_set(v_reuseFailAlloc_1846_, 1, v_nextMacroScope_1813_);
lean_ctor_set(v_reuseFailAlloc_1846_, 2, v_ngen_1814_);
lean_ctor_set(v_reuseFailAlloc_1846_, 3, v_auxDeclNGen_1815_);
lean_ctor_set(v_reuseFailAlloc_1846_, 4, v___x_1838_);
lean_ctor_set(v_reuseFailAlloc_1846_, 5, v_cache_1816_);
lean_ctor_set(v_reuseFailAlloc_1846_, 6, v_messages_1817_);
lean_ctor_set(v_reuseFailAlloc_1846_, 7, v_infoState_1818_);
lean_ctor_set(v_reuseFailAlloc_1846_, 8, v_snapshotTasks_1819_);
v___x_1840_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1844_; 
v___x_1841_ = lean_st_ref_set(v___y_1802_, v___x_1840_);
v___x_1842_ = lean_box(0);
if (v_isShared_1809_ == 0)
{
lean_ctor_set(v___x_1808_, 0, v___x_1842_);
v___x_1844_ = v___x_1808_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v___x_1842_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___boxed(lean_object* v_cls_1851_, lean_object* v_msg_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_){
_start:
{
lean_object* v_res_1858_; 
v_res_1858_ = l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2(v_cls_1851_, v_msg_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
lean_dec(v___y_1856_);
lean_dec_ref(v___y_1855_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
return v_res_1858_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Rewrites_rwLemma_spec__1(lean_object* v_x_1859_, lean_object* v_x_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_){
_start:
{
if (lean_obj_tag(v_x_1859_) == 0)
{
lean_object* v___x_1866_; lean_object* v___x_1867_; 
v___x_1866_ = l_List_reverse___redArg(v_x_1860_);
v___x_1867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1867_, 0, v___x_1866_);
return v___x_1867_;
}
else
{
lean_object* v_head_1868_; lean_object* v_tail_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1887_; 
v_head_1868_ = lean_ctor_get(v_x_1859_, 0);
v_tail_1869_ = lean_ctor_get(v_x_1859_, 1);
v_isSharedCheck_1887_ = !lean_is_exclusive(v_x_1859_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1871_ = v_x_1859_;
v_isShared_1872_ = v_isSharedCheck_1887_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_tail_1869_);
lean_inc(v_head_1868_);
lean_dec(v_x_1859_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1887_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1873_; 
v___x_1873_ = l_Lean_MVarId_assumption(v_head_1868_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
if (lean_obj_tag(v___x_1873_) == 0)
{
lean_object* v_a_1874_; lean_object* v___x_1876_; 
v_a_1874_ = lean_ctor_get(v___x_1873_, 0);
lean_inc(v_a_1874_);
lean_dec_ref_known(v___x_1873_, 1);
if (v_isShared_1872_ == 0)
{
lean_ctor_set(v___x_1871_, 1, v_x_1860_);
lean_ctor_set(v___x_1871_, 0, v_a_1874_);
v___x_1876_ = v___x_1871_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_a_1874_);
lean_ctor_set(v_reuseFailAlloc_1878_, 1, v_x_1860_);
v___x_1876_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
v_x_1859_ = v_tail_1869_;
v_x_1860_ = v___x_1876_;
goto _start;
}
}
else
{
lean_object* v_a_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1886_; 
lean_del_object(v___x_1871_);
lean_dec(v_tail_1869_);
lean_dec(v_x_1860_);
v_a_1879_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1881_ = v___x_1873_;
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_a_1879_);
lean_dec(v___x_1873_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1884_; 
if (v_isShared_1882_ == 0)
{
v___x_1884_ = v___x_1881_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v_a_1879_);
v___x_1884_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
return v___x_1884_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Rewrites_rwLemma_spec__1___boxed(lean_object* v_x_1888_, lean_object* v_x_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_){
_start:
{
lean_object* v_res_1895_; 
v_res_1895_ = l_List_mapM_loop___at___00Lean_Meta_Rewrites_rwLemma_spec__1(v_x_1888_, v_x_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
return v_res_1895_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5(void){
_start:
{
lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; 
v___x_1908_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_));
v___x_1909_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__4));
v___x_1910_ = l_Lean_Name_append(v___x_1909_, v___x_1908_);
return v___x_1910_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__7(void){
_start:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; 
v___x_1912_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__6));
v___x_1913_ = l_Lean_stringToMessageData(v___x_1912_);
return v___x_1913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0(lean_object* v_weight_1915_, lean_object* v_goal_1916_, lean_object* v_target_1917_, uint8_t v_symm_1918_, uint8_t v_side_1919_, lean_object* v_lem_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_){
_start:
{
lean_object* v___y_1927_; lean_object* v___y_1928_; lean_object* v___y_1929_; lean_object* v___y_1930_; uint8_t v___y_1931_; lean_object* v___y_1952_; lean_object* v___y_1953_; lean_object* v___y_1954_; lean_object* v___y_1955_; lean_object* v___y_1956_; lean_object* v___y_1957_; lean_object* v_fst_1958_; uint8_t v_snd_1959_; uint8_t v___y_1983_; lean_object* v___y_1984_; lean_object* v___y_1985_; uint8_t v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_2010_; lean_object* v___y_2011_; lean_object* v___y_2012_; lean_object* v___y_2013_; uint8_t v___y_2014_; lean_object* v___y_2026_; lean_object* v___y_2027_; lean_object* v___y_2028_; lean_object* v___y_2029_; uint8_t v___y_2030_; lean_object* v___y_2042_; lean_object* v___y_2122_; lean_object* v___y_2123_; lean_object* v___y_2124_; lean_object* v___y_2125_; lean_object* v_val_2140_; 
if (lean_obj_tag(v_lem_1920_) == 0)
{
lean_object* v_val_2150_; 
v_val_2150_ = lean_ctor_get(v_lem_1920_, 0);
lean_inc(v_val_2150_);
lean_dec_ref_known(v_lem_1920_, 1);
v_val_2140_ = v_val_2150_;
goto v___jp_2139_;
}
else
{
lean_object* v_val_2151_; lean_object* v___x_2152_; 
v_val_2151_ = lean_ctor_get(v_lem_1920_, 0);
lean_inc(v_val_2151_);
lean_dec_ref_known(v_lem_1920_, 1);
v___x_2152_ = l_Lean_Meta_saveState___redArg(v___y_1922_, v___y_1924_);
if (lean_obj_tag(v___x_2152_) == 0)
{
lean_object* v_a_2153_; lean_object* v___x_2154_; 
v_a_2153_ = lean_ctor_get(v___x_2152_, 0);
lean_inc(v_a_2153_);
lean_dec_ref_known(v___x_2152_, 1);
v___x_2154_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_val_2151_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_);
if (lean_obj_tag(v___x_2154_) == 0)
{
lean_object* v_a_2155_; 
lean_dec(v_a_2153_);
v_a_2155_ = lean_ctor_get(v___x_2154_, 0);
lean_inc(v_a_2155_);
lean_dec_ref_known(v___x_2154_, 1);
v_val_2140_ = v_a_2155_;
goto v___jp_2139_;
}
else
{
lean_object* v_a_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2185_; 
lean_dec_ref(v_target_1917_);
lean_dec(v_goal_1916_);
lean_dec(v_weight_1915_);
v_a_2156_ = lean_ctor_get(v___x_2154_, 0);
v_isSharedCheck_2185_ = !lean_is_exclusive(v___x_2154_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2158_ = v___x_2154_;
v_isShared_2159_ = v_isSharedCheck_2185_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_a_2156_);
lean_dec(v___x_2154_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2185_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
uint8_t v___y_2161_; uint8_t v___x_2183_; 
v___x_2183_ = l_Lean_Exception_isInterrupt(v_a_2156_);
if (v___x_2183_ == 0)
{
uint8_t v___x_2184_; 
lean_inc(v_a_2156_);
v___x_2184_ = l_Lean_Exception_isRuntime(v_a_2156_);
v___y_2161_ = v___x_2184_;
goto v___jp_2160_;
}
else
{
v___y_2161_ = v___x_2183_;
goto v___jp_2160_;
}
v___jp_2160_:
{
if (v___y_2161_ == 0)
{
lean_object* v___x_2162_; 
lean_del_object(v___x_2158_);
lean_dec(v_a_2156_);
v___x_2162_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2153_, v___y_1922_, v___y_1924_);
lean_dec(v_a_2153_);
if (lean_obj_tag(v___x_2162_) == 0)
{
lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2170_; 
v_isSharedCheck_2170_ = !lean_is_exclusive(v___x_2162_);
if (v_isSharedCheck_2170_ == 0)
{
lean_object* v_unused_2171_; 
v_unused_2171_ = lean_ctor_get(v___x_2162_, 0);
lean_dec(v_unused_2171_);
v___x_2164_ = v___x_2162_;
v_isShared_2165_ = v_isSharedCheck_2170_;
goto v_resetjp_2163_;
}
else
{
lean_dec(v___x_2162_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2170_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2166_; lean_object* v___x_2168_; 
v___x_2166_ = lean_box(0);
if (v_isShared_2165_ == 0)
{
lean_ctor_set(v___x_2164_, 0, v___x_2166_);
v___x_2168_ = v___x_2164_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v___x_2166_);
v___x_2168_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
return v___x_2168_;
}
}
}
else
{
lean_object* v_a_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2179_; 
v_a_2172_ = lean_ctor_get(v___x_2162_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2162_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2174_ = v___x_2162_;
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_a_2172_);
lean_dec(v___x_2162_);
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
else
{
lean_object* v___x_2181_; 
lean_dec(v_a_2153_);
if (v_isShared_2159_ == 0)
{
v___x_2181_ = v___x_2158_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_a_2156_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
}
}
}
}
else
{
lean_object* v_a_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2193_; 
lean_dec(v_val_2151_);
lean_dec_ref(v_target_1917_);
lean_dec(v_goal_1916_);
lean_dec(v_weight_1915_);
v_a_2186_ = lean_ctor_get(v___x_2152_, 0);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2152_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2188_ = v___x_2152_;
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_a_2186_);
lean_dec(v___x_2152_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2191_; 
if (v_isShared_2189_ == 0)
{
v___x_2191_ = v___x_2188_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_a_2186_);
v___x_2191_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
return v___x_2191_;
}
}
}
}
v___jp_1926_:
{
if (v___y_1931_ == 0)
{
lean_object* v___x_1932_; 
lean_dec_ref(v___y_1930_);
v___x_1932_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1929_, v___y_1928_, v___y_1927_);
lean_dec_ref(v___y_1929_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1940_; 
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1940_ == 0)
{
lean_object* v_unused_1941_; 
v_unused_1941_ = lean_ctor_get(v___x_1932_, 0);
lean_dec(v_unused_1941_);
v___x_1934_ = v___x_1932_;
v_isShared_1935_ = v_isSharedCheck_1940_;
goto v_resetjp_1933_;
}
else
{
lean_dec(v___x_1932_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1940_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1936_; lean_object* v___x_1938_; 
v___x_1936_ = lean_box(0);
if (v_isShared_1935_ == 0)
{
lean_ctor_set(v___x_1934_, 0, v___x_1936_);
v___x_1938_ = v___x_1934_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v___x_1936_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
}
else
{
lean_object* v_a_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1949_; 
v_a_1942_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1944_ = v___x_1932_;
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_a_1942_);
lean_dec(v___x_1932_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1947_; 
if (v_isShared_1945_ == 0)
{
v___x_1947_ = v___x_1944_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_a_1942_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
}
else
{
lean_object* v___x_1950_; 
lean_dec_ref(v___y_1929_);
v___x_1950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1950_, 0, v___y_1930_);
return v___x_1950_;
}
}
v___jp_1951_:
{
lean_object* v___x_1960_; lean_object* v_mctx_1961_; lean_object* v___x_1962_; 
v___x_1960_ = lean_st_ref_get(v___y_1954_);
v_mctx_1961_ = lean_ctor_get(v___x_1960_, 0);
lean_inc_ref_n(v_mctx_1961_, 2);
lean_dec(v___x_1960_);
v___x_1962_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(v_mctx_1961_, v___y_1953_, v___y_1955_, v___y_1954_, v___y_1957_, v___y_1952_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1973_; 
v_a_1963_ = lean_ctor_get(v___x_1962_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1965_ = v___x_1962_;
v_isShared_1966_ = v_isSharedCheck_1973_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_dec(v___x_1962_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1973_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1967_; uint8_t v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1971_; 
v___x_1967_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1967_, 0, v_fst_1958_);
lean_ctor_set(v___x_1967_, 1, v_weight_1915_);
lean_ctor_set(v___x_1967_, 2, v___y_1956_);
lean_ctor_set(v___x_1967_, 3, v_mctx_1961_);
lean_ctor_set_uint8(v___x_1967_, sizeof(void*)*4, v_snd_1959_);
v___x_1968_ = lean_unbox(v_a_1963_);
lean_dec(v_a_1963_);
lean_ctor_set_uint8(v___x_1967_, sizeof(void*)*4 + 1, v___x_1968_);
v___x_1969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1969_, 0, v___x_1967_);
if (v_isShared_1966_ == 0)
{
lean_ctor_set(v___x_1965_, 0, v___x_1969_);
v___x_1971_ = v___x_1965_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v___x_1969_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
else
{
lean_object* v_a_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1981_; 
lean_dec_ref(v_mctx_1961_);
lean_dec_ref(v_fst_1958_);
lean_dec_ref(v___y_1956_);
lean_dec(v_weight_1915_);
v_a_1974_ = lean_ctor_get(v___x_1962_, 0);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1976_ = v___x_1962_;
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_a_1974_);
lean_dec(v___x_1962_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1979_; 
if (v_isShared_1977_ == 0)
{
v___x_1979_ = v___x_1976_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v_a_1974_);
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
v___jp_1982_:
{
lean_object* v___x_1991_; 
v___x_1991_ = l_Lean_Meta_Rewrites_rewriteResultLemma(v___y_1985_);
if (lean_obj_tag(v___x_1991_) == 1)
{
lean_object* v_val_1992_; lean_object* v___x_1993_; lean_object* v_a_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; uint8_t v___x_1997_; 
v_val_1992_ = lean_ctor_get(v___x_1991_, 0);
lean_inc(v_val_1992_);
lean_dec_ref_known(v___x_1991_, 1);
v___x_1993_ = l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg(v_val_1992_, v___y_1988_);
v_a_1994_ = lean_ctor_get(v___x_1993_, 0);
lean_inc(v_a_1994_);
lean_dec_ref(v___x_1993_);
v___x_1995_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__1));
v___x_1996_ = lean_unsigned_to_nat(4u);
v___x_1997_ = l_Lean_Expr_isAppOfArity(v_a_1994_, v___x_1995_, v___x_1996_);
if (v___x_1997_ == 0)
{
v___y_1952_ = v___y_1990_;
v___y_1953_ = v___y_1984_;
v___y_1954_ = v___y_1988_;
v___y_1955_ = v___y_1987_;
v___y_1956_ = v___y_1985_;
v___y_1957_ = v___y_1989_;
v_fst_1958_ = v_a_1994_;
v_snd_1959_ = v___y_1986_;
goto v___jp_1951_;
}
else
{
lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; 
v___x_1998_ = lean_unsigned_to_nat(3u);
v___x_1999_ = l_Lean_Expr_getAppNumArgs(v_a_1994_);
v___x_2000_ = lean_nat_sub(v___x_1999_, v___x_1998_);
lean_dec(v___x_1999_);
v___x_2001_ = lean_unsigned_to_nat(1u);
v___x_2002_ = lean_nat_sub(v___x_2000_, v___x_2001_);
lean_dec(v___x_2000_);
v___x_2003_ = l_Lean_Expr_getRevArg_x21(v_a_1994_, v___x_2002_);
lean_dec(v_a_1994_);
v___y_1952_ = v___y_1990_;
v___y_1953_ = v___y_1984_;
v___y_1954_ = v___y_1988_;
v___y_1955_ = v___y_1987_;
v___y_1956_ = v___y_1985_;
v___y_1957_ = v___y_1989_;
v_fst_1958_ = v___x_2003_;
v_snd_1959_ = v___y_1983_;
goto v___jp_1951_;
}
}
else
{
lean_object* v___x_2004_; lean_object* v___x_2005_; 
lean_dec(v___x_1991_);
lean_dec_ref(v___y_1985_);
lean_dec_ref(v___y_1984_);
lean_dec(v_weight_1915_);
v___x_2004_ = lean_box(0);
v___x_2005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2005_, 0, v___x_2004_);
return v___x_2005_;
}
}
v___jp_2006_:
{
lean_object* v___x_2007_; lean_object* v___x_2008_; 
v___x_2007_ = lean_box(0);
v___x_2008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2008_, 0, v___x_2007_);
return v___x_2008_;
}
v___jp_2009_:
{
if (v___y_2014_ == 0)
{
lean_object* v___x_2015_; 
lean_dec_ref(v___y_2010_);
v___x_2015_ = l_Lean_Meta_SavedState_restore___redArg(v___y_2013_, v___y_2012_, v___y_2011_);
lean_dec_ref(v___y_2013_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_dec_ref_known(v___x_2015_, 1);
goto v___jp_2006_;
}
else
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2023_; 
v_a_2016_ = lean_ctor_get(v___x_2015_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2018_ = v___x_2015_;
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v___x_2015_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2021_; 
if (v_isShared_2019_ == 0)
{
v___x_2021_ = v___x_2018_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_a_2016_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
}
}
else
{
lean_object* v___x_2024_; 
lean_dec_ref(v___y_2013_);
v___x_2024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2024_, 0, v___y_2010_);
return v___x_2024_;
}
}
v___jp_2025_:
{
if (v___y_2030_ == 0)
{
lean_object* v___x_2031_; 
lean_dec_ref(v___y_2028_);
v___x_2031_ = l_Lean_Meta_SavedState_restore___redArg(v___y_2029_, v___y_2027_, v___y_2026_);
lean_dec_ref(v___y_2029_);
if (lean_obj_tag(v___x_2031_) == 0)
{
lean_dec_ref_known(v___x_2031_, 1);
goto v___jp_2006_;
}
else
{
lean_object* v_a_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2039_; 
v_a_2032_ = lean_ctor_get(v___x_2031_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2034_ = v___x_2031_;
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_a_2032_);
lean_dec(v___x_2031_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2037_; 
if (v_isShared_2035_ == 0)
{
v___x_2037_ = v___x_2034_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_a_2032_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
}
else
{
lean_object* v___x_2040_; 
lean_dec_ref(v___y_2029_);
v___x_2040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2040_, 0, v___y_2028_);
return v___x_2040_;
}
}
v___jp_2041_:
{
lean_object* v___x_2043_; 
v___x_2043_ = l_Lean_Meta_saveState___redArg(v___y_1922_, v___y_1924_);
if (lean_obj_tag(v___x_2043_) == 0)
{
lean_object* v_a_2044_; uint8_t v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; 
v_a_2044_ = lean_ctor_get(v___x_2043_, 0);
lean_inc(v_a_2044_);
lean_dec_ref_known(v___x_2043_, 1);
v___x_2045_ = 1;
v___x_2046_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__2));
lean_inc_ref(v___y_2042_);
v___x_2047_ = l_Lean_MVarId_rewrite(v_goal_1916_, v_target_1917_, v___y_2042_, v_symm_1918_, v___x_2046_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_);
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v_a_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2109_; 
lean_dec(v_a_2044_);
v_a_2048_ = lean_ctor_get(v___x_2047_, 0);
v_isSharedCheck_2109_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2050_ = v___x_2047_;
v_isShared_2051_ = v_isSharedCheck_2109_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_a_2048_);
lean_dec(v___x_2047_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2109_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v_eNew_2052_; lean_object* v_mvarIds_2053_; uint8_t v___x_2054_; 
v_eNew_2052_ = lean_ctor_get(v_a_2048_, 0);
v_mvarIds_2053_ = lean_ctor_get(v_a_2048_, 2);
v___x_2054_ = l_List_isEmpty___redArg(v_mvarIds_2053_);
if (v___x_2054_ == 0)
{
lean_inc_ref(v_eNew_2052_);
lean_del_object(v___x_2050_);
lean_dec_ref(v___y_2042_);
switch(v_side_1919_)
{
case 0:
{
if (v___x_2054_ == 0)
{
lean_dec_ref(v_eNew_2052_);
lean_dec(v_a_2048_);
lean_dec(v_weight_1915_);
goto v___jp_2006_;
}
else
{
v___y_1983_ = v___x_2045_;
v___y_1984_ = v_eNew_2052_;
v___y_1985_ = v_a_2048_;
v___y_1986_ = v___x_2054_;
v___y_1987_ = v___y_1921_;
v___y_1988_ = v___y_1922_;
v___y_1989_ = v___y_1923_;
v___y_1990_ = v___y_1924_;
goto v___jp_1982_;
}
}
case 1:
{
lean_object* v___x_2055_; 
v___x_2055_ = l_Lean_Meta_saveState___redArg(v___y_1922_, v___y_1924_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v_a_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
lean_inc(v_a_2056_);
lean_dec_ref_known(v___x_2055_, 1);
v___x_2057_ = lean_box(0);
lean_inc(v_mvarIds_2053_);
v___x_2058_ = l_List_mapM_loop___at___00Lean_Meta_Rewrites_rwLemma_spec__1(v_mvarIds_2053_, v___x_2057_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_);
if (lean_obj_tag(v___x_2058_) == 0)
{
lean_dec_ref_known(v___x_2058_, 1);
lean_dec(v_a_2056_);
v___y_1983_ = v___x_2045_;
v___y_1984_ = v_eNew_2052_;
v___y_1985_ = v_a_2048_;
v___y_1986_ = v___x_2054_;
v___y_1987_ = v___y_1921_;
v___y_1988_ = v___y_1922_;
v___y_1989_ = v___y_1923_;
v___y_1990_ = v___y_1924_;
goto v___jp_1982_;
}
else
{
lean_object* v_a_2059_; uint8_t v___x_2060_; 
lean_dec_ref(v_eNew_2052_);
lean_dec(v_a_2048_);
lean_dec(v_weight_1915_);
v_a_2059_ = lean_ctor_get(v___x_2058_, 0);
lean_inc(v_a_2059_);
lean_dec_ref_known(v___x_2058_, 1);
v___x_2060_ = l_Lean_Exception_isInterrupt(v_a_2059_);
if (v___x_2060_ == 0)
{
uint8_t v___x_2061_; 
lean_inc(v_a_2059_);
v___x_2061_ = l_Lean_Exception_isRuntime(v_a_2059_);
v___y_2026_ = v___y_1924_;
v___y_2027_ = v___y_1922_;
v___y_2028_ = v_a_2059_;
v___y_2029_ = v_a_2056_;
v___y_2030_ = v___x_2061_;
goto v___jp_2025_;
}
else
{
v___y_2026_ = v___y_1924_;
v___y_2027_ = v___y_1922_;
v___y_2028_ = v_a_2059_;
v___y_2029_ = v_a_2056_;
v___y_2030_ = v___x_2060_;
goto v___jp_2025_;
}
}
}
else
{
lean_object* v_a_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2069_; 
lean_dec_ref(v_eNew_2052_);
lean_dec(v_a_2048_);
lean_dec(v_weight_1915_);
v_a_2062_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2064_ = v___x_2055_;
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_a_2062_);
lean_dec(v___x_2055_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2067_; 
if (v_isShared_2065_ == 0)
{
v___x_2067_ = v___x_2064_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_a_2062_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
return v___x_2067_;
}
}
}
}
default: 
{
lean_object* v___x_2070_; 
v___x_2070_ = l_Lean_Meta_saveState___redArg(v___y_1922_, v___y_1924_);
if (lean_obj_tag(v___x_2070_) == 0)
{
lean_object* v_a_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; 
v_a_2071_ = lean_ctor_get(v___x_2070_, 0);
lean_inc(v_a_2071_);
lean_dec_ref_known(v___x_2070_, 1);
v___x_2072_ = lean_unsigned_to_nat(6u);
lean_inc(v_mvarIds_2053_);
v___x_2073_ = l_Lean_Meta_Rewrites_solveByElim(v_mvarIds_2053_, v___x_2072_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_);
if (lean_obj_tag(v___x_2073_) == 0)
{
lean_dec_ref_known(v___x_2073_, 1);
lean_dec(v_a_2071_);
v___y_1983_ = v___x_2045_;
v___y_1984_ = v_eNew_2052_;
v___y_1985_ = v_a_2048_;
v___y_1986_ = v___x_2054_;
v___y_1987_ = v___y_1921_;
v___y_1988_ = v___y_1922_;
v___y_1989_ = v___y_1923_;
v___y_1990_ = v___y_1924_;
goto v___jp_1982_;
}
else
{
lean_object* v_a_2074_; uint8_t v___x_2075_; 
lean_dec_ref(v_eNew_2052_);
lean_dec(v_a_2048_);
lean_dec(v_weight_1915_);
v_a_2074_ = lean_ctor_get(v___x_2073_, 0);
lean_inc(v_a_2074_);
lean_dec_ref_known(v___x_2073_, 1);
v___x_2075_ = l_Lean_Exception_isInterrupt(v_a_2074_);
if (v___x_2075_ == 0)
{
uint8_t v___x_2076_; 
lean_inc(v_a_2074_);
v___x_2076_ = l_Lean_Exception_isRuntime(v_a_2074_);
v___y_2010_ = v_a_2074_;
v___y_2011_ = v___y_1924_;
v___y_2012_ = v___y_1922_;
v___y_2013_ = v_a_2071_;
v___y_2014_ = v___x_2076_;
goto v___jp_2009_;
}
else
{
v___y_2010_ = v_a_2074_;
v___y_2011_ = v___y_1924_;
v___y_2012_ = v___y_1922_;
v___y_2013_ = v_a_2071_;
v___y_2014_ = v___x_2075_;
goto v___jp_2009_;
}
}
}
else
{
lean_object* v_a_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2084_; 
lean_dec_ref(v_eNew_2052_);
lean_dec(v_a_2048_);
lean_dec(v_weight_1915_);
v_a_2077_ = lean_ctor_get(v___x_2070_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2070_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2079_ = v___x_2070_;
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_a_2077_);
lean_dec(v___x_2070_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2082_; 
if (v_isShared_2080_ == 0)
{
v___x_2082_ = v___x_2079_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_a_2077_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
}
}
}
}
else
{
lean_object* v___x_2085_; lean_object* v_mctx_2086_; lean_object* v___x_2087_; 
v___x_2085_ = lean_st_ref_get(v___y_1922_);
v_mctx_2086_ = lean_ctor_get(v___x_2085_, 0);
lean_inc_ref_n(v_mctx_2086_, 2);
lean_dec(v___x_2085_);
lean_inc_ref(v_eNew_2052_);
v___x_2087_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(v_mctx_2086_, v_eNew_2052_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v_a_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2100_; 
v_a_2088_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2100_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2100_ == 0)
{
v___x_2090_ = v___x_2087_;
v_isShared_2091_ = v_isSharedCheck_2100_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_a_2088_);
lean_dec(v___x_2087_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2100_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v___x_2092_; uint8_t v___x_2093_; lean_object* v___x_2095_; 
v___x_2092_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2092_, 0, v___y_2042_);
lean_ctor_set(v___x_2092_, 1, v_weight_1915_);
lean_ctor_set(v___x_2092_, 2, v_a_2048_);
lean_ctor_set(v___x_2092_, 3, v_mctx_2086_);
lean_ctor_set_uint8(v___x_2092_, sizeof(void*)*4, v_symm_1918_);
v___x_2093_ = lean_unbox(v_a_2088_);
lean_dec(v_a_2088_);
lean_ctor_set_uint8(v___x_2092_, sizeof(void*)*4 + 1, v___x_2093_);
if (v_isShared_2051_ == 0)
{
lean_ctor_set_tag(v___x_2050_, 1);
lean_ctor_set(v___x_2050_, 0, v___x_2092_);
v___x_2095_ = v___x_2050_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v___x_2092_);
v___x_2095_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
lean_object* v___x_2097_; 
if (v_isShared_2091_ == 0)
{
lean_ctor_set(v___x_2090_, 0, v___x_2095_);
v___x_2097_ = v___x_2090_;
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
else
{
lean_object* v_a_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2108_; 
lean_dec_ref(v_mctx_2086_);
lean_del_object(v___x_2050_);
lean_dec(v_a_2048_);
lean_dec_ref(v___y_2042_);
lean_dec(v_weight_1915_);
v_a_2101_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2108_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2103_ = v___x_2087_;
v_isShared_2104_ = v_isSharedCheck_2108_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_a_2101_);
lean_dec(v___x_2087_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2108_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v___x_2106_; 
if (v_isShared_2104_ == 0)
{
v___x_2106_ = v___x_2103_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v_a_2101_);
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
else
{
lean_object* v_a_2110_; uint8_t v___x_2111_; 
lean_dec_ref(v___y_2042_);
lean_dec(v_weight_1915_);
v_a_2110_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_a_2110_);
lean_dec_ref_known(v___x_2047_, 1);
v___x_2111_ = l_Lean_Exception_isInterrupt(v_a_2110_);
if (v___x_2111_ == 0)
{
uint8_t v___x_2112_; 
lean_inc(v_a_2110_);
v___x_2112_ = l_Lean_Exception_isRuntime(v_a_2110_);
v___y_1927_ = v___y_1924_;
v___y_1928_ = v___y_1922_;
v___y_1929_ = v_a_2044_;
v___y_1930_ = v_a_2110_;
v___y_1931_ = v___x_2112_;
goto v___jp_1926_;
}
else
{
v___y_1927_ = v___y_1924_;
v___y_1928_ = v___y_1922_;
v___y_1929_ = v_a_2044_;
v___y_1930_ = v_a_2110_;
v___y_1931_ = v___x_2111_;
goto v___jp_1926_;
}
}
}
else
{
lean_object* v_a_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2120_; 
lean_dec_ref(v___y_2042_);
lean_dec_ref(v_target_1917_);
lean_dec(v_goal_1916_);
lean_dec(v_weight_1915_);
v_a_2113_ = lean_ctor_get(v___x_2043_, 0);
v_isSharedCheck_2120_ = !lean_is_exclusive(v___x_2043_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2115_ = v___x_2043_;
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_a_2113_);
lean_dec(v___x_2043_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___x_2118_; 
if (v_isShared_2116_ == 0)
{
v___x_2118_ = v___x_2115_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v_a_2113_);
v___x_2118_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
return v___x_2118_;
}
}
}
}
v___jp_2121_:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; 
lean_inc_ref(v___y_2125_);
v___x_2126_ = l_Lean_stringToMessageData(v___y_2125_);
lean_inc_ref(v___y_2123_);
v___x_2127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2127_, 0, v___y_2123_);
lean_ctor_set(v___x_2127_, 1, v___x_2126_);
lean_inc_ref(v___y_2122_);
v___x_2128_ = l_Lean_MessageData_ofExpr(v___y_2122_);
v___x_2129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2127_);
lean_ctor_set(v___x_2129_, 1, v___x_2128_);
lean_inc(v___y_2124_);
v___x_2130_ = l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2(v___y_2124_, v___x_2129_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_dec_ref_known(v___x_2130_, 1);
v___y_2042_ = v___y_2122_;
goto v___jp_2041_;
}
else
{
lean_object* v_a_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2138_; 
lean_dec_ref(v___y_2122_);
lean_dec_ref(v_target_1917_);
lean_dec(v_goal_1916_);
lean_dec(v_weight_1915_);
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
v_isSharedCheck_2138_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2133_ = v___x_2130_;
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_a_2131_);
lean_dec(v___x_2130_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v___x_2136_; 
if (v_isShared_2134_ == 0)
{
v___x_2136_ = v___x_2133_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v_a_2131_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
return v___x_2136_;
}
}
}
}
v___jp_2139_:
{
lean_object* v_options_2141_; uint8_t v_hasTrace_2142_; 
v_options_2141_ = lean_ctor_get(v___y_1923_, 2);
v_hasTrace_2142_ = lean_ctor_get_uint8(v_options_2141_, sizeof(void*)*1);
if (v_hasTrace_2142_ == 0)
{
v___y_2042_ = v_val_2140_;
goto v___jp_2041_;
}
else
{
lean_object* v_inheritedTraceOptions_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; uint8_t v___x_2146_; 
v_inheritedTraceOptions_2143_ = lean_ctor_get(v___y_1923_, 13);
v___x_2144_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_));
v___x_2145_ = lean_obj_once(&l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5, &l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5_once, _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5);
v___x_2146_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2143_, v_options_2141_, v___x_2145_);
if (v___x_2146_ == 0)
{
v___y_2042_ = v_val_2140_;
goto v___jp_2041_;
}
else
{
lean_object* v___x_2147_; 
v___x_2147_ = lean_obj_once(&l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__7, &l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__7_once, _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__7);
if (v_symm_1918_ == 0)
{
lean_object* v___x_2148_; 
v___x_2148_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__1));
v___y_2122_ = v_val_2140_;
v___y_2123_ = v___x_2147_;
v___y_2124_ = v___x_2144_;
v___y_2125_ = v___x_2148_;
goto v___jp_2121_;
}
else
{
lean_object* v___x_2149_; 
v___x_2149_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__8));
v___y_2122_ = v_val_2140_;
v___y_2123_ = v___x_2147_;
v___y_2124_ = v___x_2144_;
v___y_2125_ = v___x_2149_;
goto v___jp_2121_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0___boxed(lean_object* v_weight_2194_, lean_object* v_goal_2195_, lean_object* v_target_2196_, lean_object* v_symm_2197_, lean_object* v_side_2198_, lean_object* v_lem_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_){
_start:
{
uint8_t v_symm_boxed_2205_; uint8_t v_side_boxed_2206_; lean_object* v_res_2207_; 
v_symm_boxed_2205_ = lean_unbox(v_symm_2197_);
v_side_boxed_2206_ = lean_unbox(v_side_2198_);
v_res_2207_ = l_Lean_Meta_Rewrites_rwLemma___lam__0(v_weight_2194_, v_goal_2195_, v_target_2196_, v_symm_boxed_2205_, v_side_boxed_2206_, v_lem_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
lean_dec(v___y_2203_);
lean_dec_ref(v___y_2202_);
lean_dec(v___y_2201_);
lean_dec_ref(v___y_2200_);
return v_res_2207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma(lean_object* v_ctx_2208_, lean_object* v_goal_2209_, lean_object* v_target_2210_, uint8_t v_side_2211_, lean_object* v_lem_2212_, uint8_t v_symm_2213_, lean_object* v_weight_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_){
_start:
{
lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___f_2222_; lean_object* v___x_2223_; 
v___x_2220_ = lean_box(v_symm_2213_);
v___x_2221_ = lean_box(v_side_2211_);
v___f_2222_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___boxed), 11, 6);
lean_closure_set(v___f_2222_, 0, v_weight_2214_);
lean_closure_set(v___f_2222_, 1, v_goal_2209_);
lean_closure_set(v___f_2222_, 2, v_target_2210_);
lean_closure_set(v___f_2222_, 3, v___x_2220_);
lean_closure_set(v___f_2222_, 4, v___x_2221_);
lean_closure_set(v___f_2222_, 5, v_lem_2212_);
v___x_2223_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg(v_ctx_2208_, v___f_2222_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_);
return v___x_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___boxed(lean_object* v_ctx_2224_, lean_object* v_goal_2225_, lean_object* v_target_2226_, lean_object* v_side_2227_, lean_object* v_lem_2228_, lean_object* v_symm_2229_, lean_object* v_weight_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_){
_start:
{
uint8_t v_side_boxed_2236_; uint8_t v_symm_boxed_2237_; lean_object* v_res_2238_; 
v_side_boxed_2236_ = lean_unbox(v_side_2227_);
v_symm_boxed_2237_ = lean_unbox(v_symm_2229_);
v_res_2238_ = l_Lean_Meta_Rewrites_rwLemma(v_ctx_2224_, v_goal_2225_, v_target_2226_, v_side_boxed_2236_, v_lem_2228_, v_symm_boxed_2237_, v_weight_2230_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2234_);
lean_dec(v_a_2234_);
lean_dec_ref(v_a_2233_);
lean_dec(v_a_2232_);
lean_dec_ref(v_a_2231_);
return v_res_2238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(lean_object* v_type_2239_, lean_object* v_k_2240_, uint8_t v_cleanupAnnotations_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_){
_start:
{
lean_object* v___f_2247_; uint8_t v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___f_2247_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2247_, 0, v_k_2240_);
v___x_2248_ = 0;
v___x_2249_ = lean_box(0);
v___x_2250_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_2248_, v___x_2249_, v_type_2239_, v___f_2247_, v_cleanupAnnotations_2241_, v___x_2248_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
if (lean_obj_tag(v___x_2250_) == 0)
{
lean_object* v_a_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2258_; 
v_a_2251_ = lean_ctor_get(v___x_2250_, 0);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2250_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2253_ = v___x_2250_;
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_a_2251_);
lean_dec(v___x_2250_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v___x_2256_; 
if (v_isShared_2254_ == 0)
{
v___x_2256_ = v___x_2253_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v_a_2251_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
}
}
}
else
{
lean_object* v_a_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2266_; 
v_a_2259_ = lean_ctor_get(v___x_2250_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2250_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2261_ = v___x_2250_;
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_a_2259_);
lean_dec(v___x_2250_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v___x_2264_; 
if (v_isShared_2262_ == 0)
{
v___x_2264_ = v___x_2261_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_a_2259_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg___boxed(lean_object* v_type_2267_, lean_object* v_k_2268_, lean_object* v_cleanupAnnotations_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2275_; lean_object* v_res_2276_; 
v_cleanupAnnotations_boxed_2275_ = lean_unbox(v_cleanupAnnotations_2269_);
v_res_2276_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(v_type_2267_, v_k_2268_, v_cleanupAnnotations_boxed_2275_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_);
lean_dec(v___y_2273_);
lean_dec_ref(v___y_2272_);
lean_dec(v___y_2271_);
lean_dec_ref(v___y_2270_);
return v_res_2276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1(lean_object* v_00_u03b1_2277_, lean_object* v_type_2278_, lean_object* v_k_2279_, uint8_t v_cleanupAnnotations_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_){
_start:
{
lean_object* v___x_2286_; 
v___x_2286_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(v_type_2278_, v_k_2279_, v_cleanupAnnotations_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
return v___x_2286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___boxed(lean_object* v_00_u03b1_2287_, lean_object* v_type_2288_, lean_object* v_k_2289_, lean_object* v_cleanupAnnotations_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2296_; lean_object* v_res_2297_; 
v_cleanupAnnotations_boxed_2296_ = lean_unbox(v_cleanupAnnotations_2290_);
v_res_2297_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1(v_00_u03b1_2287_, v_type_2288_, v_k_2289_, v_cleanupAnnotations_boxed_2296_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
return v_res_2297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(lean_object* v_e_2298_, lean_object* v_k_2299_, uint8_t v_cleanupAnnotations_2300_, uint8_t v_preserveNondepLet_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_){
_start:
{
lean_object* v___f_2307_; uint8_t v___x_2308_; uint8_t v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; 
v___f_2307_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2307_, 0, v_k_2299_);
v___x_2308_ = 1;
v___x_2309_ = 0;
v___x_2310_ = lean_box(0);
v___x_2311_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2298_, v___x_2308_, v___x_2308_, v_preserveNondepLet_2301_, v___x_2309_, v___x_2310_, v___f_2307_, v_cleanupAnnotations_2300_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_);
if (lean_obj_tag(v___x_2311_) == 0)
{
lean_object* v_a_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2319_; 
v_a_2312_ = lean_ctor_get(v___x_2311_, 0);
v_isSharedCheck_2319_ = !lean_is_exclusive(v___x_2311_);
if (v_isSharedCheck_2319_ == 0)
{
v___x_2314_ = v___x_2311_;
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_a_2312_);
lean_dec(v___x_2311_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v___x_2317_; 
if (v_isShared_2315_ == 0)
{
v___x_2317_ = v___x_2314_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_a_2312_);
v___x_2317_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
return v___x_2317_;
}
}
}
else
{
lean_object* v_a_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2327_; 
v_a_2320_ = lean_ctor_get(v___x_2311_, 0);
v_isSharedCheck_2327_ = !lean_is_exclusive(v___x_2311_);
if (v_isSharedCheck_2327_ == 0)
{
v___x_2322_ = v___x_2311_;
v_isShared_2323_ = v_isSharedCheck_2327_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_a_2320_);
lean_dec(v___x_2311_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2327_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v___x_2325_; 
if (v_isShared_2323_ == 0)
{
v___x_2325_ = v___x_2322_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v_a_2320_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg___boxed(lean_object* v_e_2328_, lean_object* v_k_2329_, lean_object* v_cleanupAnnotations_2330_, lean_object* v_preserveNondepLet_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2337_; uint8_t v_preserveNondepLet_boxed_2338_; lean_object* v_res_2339_; 
v_cleanupAnnotations_boxed_2337_ = lean_unbox(v_cleanupAnnotations_2330_);
v_preserveNondepLet_boxed_2338_ = lean_unbox(v_preserveNondepLet_2331_);
v_res_2339_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(v_e_2328_, v_k_2329_, v_cleanupAnnotations_boxed_2337_, v_preserveNondepLet_boxed_2338_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
lean_dec(v___y_2335_);
lean_dec_ref(v___y_2334_);
lean_dec(v___y_2333_);
lean_dec_ref(v___y_2332_);
return v_res_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2(lean_object* v_00_u03b1_2340_, lean_object* v_e_2341_, lean_object* v_k_2342_, uint8_t v_cleanupAnnotations_2343_, uint8_t v_preserveNondepLet_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_){
_start:
{
lean_object* v___x_2350_; 
v___x_2350_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(v_e_2341_, v_k_2342_, v_cleanupAnnotations_2343_, v_preserveNondepLet_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_);
return v___x_2350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___boxed(lean_object* v_00_u03b1_2351_, lean_object* v_e_2352_, lean_object* v_k_2353_, lean_object* v_cleanupAnnotations_2354_, lean_object* v_preserveNondepLet_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2361_; uint8_t v_preserveNondepLet_boxed_2362_; lean_object* v_res_2363_; 
v_cleanupAnnotations_boxed_2361_ = lean_unbox(v_cleanupAnnotations_2354_);
v_preserveNondepLet_boxed_2362_ = lean_unbox(v_preserveNondepLet_2355_);
v_res_2363_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2(v_00_u03b1_2351_, v_e_2352_, v_k_2353_, v_cleanupAnnotations_boxed_2361_, v_preserveNondepLet_boxed_2362_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_);
lean_dec(v___y_2359_);
lean_dec_ref(v___y_2358_);
lean_dec(v___y_2357_);
lean_dec_ref(v___y_2356_);
return v_res_2363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(lean_object* v_f_2364_, lean_object* v_e_x27_2365_, lean_object* v_a_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_){
_start:
{
lean_object* v___x_2372_; 
lean_inc(v___y_2370_);
lean_inc_ref(v___y_2369_);
lean_inc(v___y_2368_);
lean_inc_ref(v___y_2367_);
lean_inc_ref(v_e_x27_2365_);
v___x_2372_ = lean_apply_7(v_f_2364_, v_a_2366_, v_e_x27_2365_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, lean_box(0));
if (lean_obj_tag(v___x_2372_) == 0)
{
lean_object* v_a_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2381_; 
v_a_2373_ = lean_ctor_get(v___x_2372_, 0);
v_isSharedCheck_2381_ = !lean_is_exclusive(v___x_2372_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2375_ = v___x_2372_;
v_isShared_2376_ = v_isSharedCheck_2381_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_a_2373_);
lean_dec(v___x_2372_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2381_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2377_; lean_object* v___x_2379_; 
v___x_2377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2377_, 0, v_e_x27_2365_);
lean_ctor_set(v___x_2377_, 1, v_a_2373_);
if (v_isShared_2376_ == 0)
{
lean_ctor_set(v___x_2375_, 0, v___x_2377_);
v___x_2379_ = v___x_2375_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v___x_2377_);
v___x_2379_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
return v___x_2379_;
}
}
}
else
{
lean_object* v_a_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2389_; 
lean_dec_ref(v_e_x27_2365_);
v_a_2382_ = lean_ctor_get(v___x_2372_, 0);
v_isSharedCheck_2389_ = !lean_is_exclusive(v___x_2372_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2384_ = v___x_2372_;
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_a_2382_);
lean_dec(v___x_2372_);
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
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0___boxed(lean_object* v_f_2390_, lean_object* v_e_x27_2391_, lean_object* v_a_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_){
_start:
{
lean_object* v_res_2398_; 
v_res_2398_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2390_, v_e_x27_2391_, v_a_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_);
lean_dec(v___y_2396_);
lean_dec_ref(v___y_2395_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
return v_res_2398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg(lean_object* v_f_2399_, lean_object* v_x_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_){
_start:
{
switch(lean_obj_tag(v_x_2400_))
{
case 7:
{
lean_object* v_binderName_2407_; lean_object* v_binderType_2408_; lean_object* v_body_2409_; uint8_t v_binderInfo_2410_; lean_object* v___x_2411_; 
v_binderName_2407_ = lean_ctor_get(v_x_2400_, 0);
v_binderType_2408_ = lean_ctor_get(v_x_2400_, 1);
v_body_2409_ = lean_ctor_get(v_x_2400_, 2);
v_binderInfo_2410_ = lean_ctor_get_uint8(v_x_2400_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2408_);
lean_inc_ref(v_f_2399_);
v___x_2411_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2399_, v_binderType_2408_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
if (lean_obj_tag(v___x_2411_) == 0)
{
lean_object* v_a_2412_; lean_object* v_fst_2413_; lean_object* v_snd_2414_; lean_object* v___x_2415_; 
v_a_2412_ = lean_ctor_get(v___x_2411_, 0);
lean_inc(v_a_2412_);
lean_dec_ref_known(v___x_2411_, 1);
v_fst_2413_ = lean_ctor_get(v_a_2412_, 0);
lean_inc(v_fst_2413_);
v_snd_2414_ = lean_ctor_get(v_a_2412_, 1);
lean_inc(v_snd_2414_);
lean_dec(v_a_2412_);
lean_inc_ref(v_body_2409_);
v___x_2415_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2399_, v_body_2409_, v_snd_2414_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
if (lean_obj_tag(v___x_2415_) == 0)
{
lean_object* v_a_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2445_; 
v_a_2416_ = lean_ctor_get(v___x_2415_, 0);
v_isSharedCheck_2445_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2445_ == 0)
{
v___x_2418_ = v___x_2415_;
v_isShared_2419_ = v_isSharedCheck_2445_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_a_2416_);
lean_dec(v___x_2415_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2445_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v_fst_2420_; lean_object* v_snd_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2444_; 
v_fst_2420_ = lean_ctor_get(v_a_2416_, 0);
v_snd_2421_ = lean_ctor_get(v_a_2416_, 1);
v_isSharedCheck_2444_ = !lean_is_exclusive(v_a_2416_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2423_ = v_a_2416_;
v_isShared_2424_ = v_isSharedCheck_2444_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_snd_2421_);
lean_inc(v_fst_2420_);
lean_dec(v_a_2416_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2444_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
lean_object* v___y_2426_; uint8_t v___y_2434_; size_t v___x_2438_; size_t v___x_2439_; uint8_t v___x_2440_; 
v___x_2438_ = lean_ptr_addr(v_binderType_2408_);
v___x_2439_ = lean_ptr_addr(v_fst_2413_);
v___x_2440_ = lean_usize_dec_eq(v___x_2438_, v___x_2439_);
if (v___x_2440_ == 0)
{
v___y_2434_ = v___x_2440_;
goto v___jp_2433_;
}
else
{
size_t v___x_2441_; size_t v___x_2442_; uint8_t v___x_2443_; 
v___x_2441_ = lean_ptr_addr(v_body_2409_);
v___x_2442_ = lean_ptr_addr(v_fst_2420_);
v___x_2443_ = lean_usize_dec_eq(v___x_2441_, v___x_2442_);
v___y_2434_ = v___x_2443_;
goto v___jp_2433_;
}
v___jp_2425_:
{
lean_object* v___x_2428_; 
if (v_isShared_2424_ == 0)
{
lean_ctor_set(v___x_2423_, 0, v___y_2426_);
v___x_2428_ = v___x_2423_;
goto v_reusejp_2427_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v___y_2426_);
lean_ctor_set(v_reuseFailAlloc_2432_, 1, v_snd_2421_);
v___x_2428_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2427_;
}
v_reusejp_2427_:
{
lean_object* v___x_2430_; 
if (v_isShared_2419_ == 0)
{
lean_ctor_set(v___x_2418_, 0, v___x_2428_);
v___x_2430_ = v___x_2418_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v___x_2428_);
v___x_2430_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
return v___x_2430_;
}
}
}
v___jp_2433_:
{
if (v___y_2434_ == 0)
{
lean_object* v___x_2435_; 
lean_inc(v_binderName_2407_);
lean_dec_ref_known(v_x_2400_, 3);
v___x_2435_ = l_Lean_Expr_forallE___override(v_binderName_2407_, v_fst_2413_, v_fst_2420_, v_binderInfo_2410_);
v___y_2426_ = v___x_2435_;
goto v___jp_2425_;
}
else
{
uint8_t v___x_2436_; 
v___x_2436_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2410_, v_binderInfo_2410_);
if (v___x_2436_ == 0)
{
lean_object* v___x_2437_; 
lean_inc(v_binderName_2407_);
lean_dec_ref_known(v_x_2400_, 3);
v___x_2437_ = l_Lean_Expr_forallE___override(v_binderName_2407_, v_fst_2413_, v_fst_2420_, v_binderInfo_2410_);
v___y_2426_ = v___x_2437_;
goto v___jp_2425_;
}
else
{
lean_dec(v_fst_2420_);
lean_dec(v_fst_2413_);
v___y_2426_ = v_x_2400_;
goto v___jp_2425_;
}
}
}
}
}
}
else
{
lean_dec(v_fst_2413_);
lean_dec_ref_known(v_x_2400_, 3);
return v___x_2415_;
}
}
else
{
lean_dec_ref_known(v_x_2400_, 3);
lean_dec_ref(v_f_2399_);
return v___x_2411_;
}
}
case 6:
{
lean_object* v_binderName_2446_; lean_object* v_binderType_2447_; lean_object* v_body_2448_; uint8_t v_binderInfo_2449_; lean_object* v___x_2450_; 
v_binderName_2446_ = lean_ctor_get(v_x_2400_, 0);
v_binderType_2447_ = lean_ctor_get(v_x_2400_, 1);
v_body_2448_ = lean_ctor_get(v_x_2400_, 2);
v_binderInfo_2449_ = lean_ctor_get_uint8(v_x_2400_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2447_);
lean_inc_ref(v_f_2399_);
v___x_2450_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2399_, v_binderType_2447_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
if (lean_obj_tag(v___x_2450_) == 0)
{
lean_object* v_a_2451_; lean_object* v_fst_2452_; lean_object* v_snd_2453_; lean_object* v___x_2454_; 
v_a_2451_ = lean_ctor_get(v___x_2450_, 0);
lean_inc(v_a_2451_);
lean_dec_ref_known(v___x_2450_, 1);
v_fst_2452_ = lean_ctor_get(v_a_2451_, 0);
lean_inc(v_fst_2452_);
v_snd_2453_ = lean_ctor_get(v_a_2451_, 1);
lean_inc(v_snd_2453_);
lean_dec(v_a_2451_);
lean_inc_ref(v_body_2448_);
v___x_2454_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2399_, v_body_2448_, v_snd_2453_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_object* v_a_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2484_; 
v_a_2455_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2457_ = v___x_2454_;
v_isShared_2458_ = v_isSharedCheck_2484_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_a_2455_);
lean_dec(v___x_2454_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2484_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
lean_object* v_fst_2459_; lean_object* v_snd_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2483_; 
v_fst_2459_ = lean_ctor_get(v_a_2455_, 0);
v_snd_2460_ = lean_ctor_get(v_a_2455_, 1);
v_isSharedCheck_2483_ = !lean_is_exclusive(v_a_2455_);
if (v_isSharedCheck_2483_ == 0)
{
v___x_2462_ = v_a_2455_;
v_isShared_2463_ = v_isSharedCheck_2483_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_snd_2460_);
lean_inc(v_fst_2459_);
lean_dec(v_a_2455_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2483_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___y_2465_; uint8_t v___y_2473_; size_t v___x_2477_; size_t v___x_2478_; uint8_t v___x_2479_; 
v___x_2477_ = lean_ptr_addr(v_binderType_2447_);
v___x_2478_ = lean_ptr_addr(v_fst_2452_);
v___x_2479_ = lean_usize_dec_eq(v___x_2477_, v___x_2478_);
if (v___x_2479_ == 0)
{
v___y_2473_ = v___x_2479_;
goto v___jp_2472_;
}
else
{
size_t v___x_2480_; size_t v___x_2481_; uint8_t v___x_2482_; 
v___x_2480_ = lean_ptr_addr(v_body_2448_);
v___x_2481_ = lean_ptr_addr(v_fst_2459_);
v___x_2482_ = lean_usize_dec_eq(v___x_2480_, v___x_2481_);
v___y_2473_ = v___x_2482_;
goto v___jp_2472_;
}
v___jp_2464_:
{
lean_object* v___x_2467_; 
if (v_isShared_2463_ == 0)
{
lean_ctor_set(v___x_2462_, 0, v___y_2465_);
v___x_2467_ = v___x_2462_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v___y_2465_);
lean_ctor_set(v_reuseFailAlloc_2471_, 1, v_snd_2460_);
v___x_2467_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
lean_object* v___x_2469_; 
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 0, v___x_2467_);
v___x_2469_ = v___x_2457_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v___x_2467_);
v___x_2469_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
return v___x_2469_;
}
}
}
v___jp_2472_:
{
if (v___y_2473_ == 0)
{
lean_object* v___x_2474_; 
lean_inc(v_binderName_2446_);
lean_dec_ref_known(v_x_2400_, 3);
v___x_2474_ = l_Lean_Expr_lam___override(v_binderName_2446_, v_fst_2452_, v_fst_2459_, v_binderInfo_2449_);
v___y_2465_ = v___x_2474_;
goto v___jp_2464_;
}
else
{
uint8_t v___x_2475_; 
v___x_2475_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2449_, v_binderInfo_2449_);
if (v___x_2475_ == 0)
{
lean_object* v___x_2476_; 
lean_inc(v_binderName_2446_);
lean_dec_ref_known(v_x_2400_, 3);
v___x_2476_ = l_Lean_Expr_lam___override(v_binderName_2446_, v_fst_2452_, v_fst_2459_, v_binderInfo_2449_);
v___y_2465_ = v___x_2476_;
goto v___jp_2464_;
}
else
{
lean_dec(v_fst_2459_);
lean_dec(v_fst_2452_);
v___y_2465_ = v_x_2400_;
goto v___jp_2464_;
}
}
}
}
}
}
else
{
lean_dec(v_fst_2452_);
lean_dec_ref_known(v_x_2400_, 3);
return v___x_2454_;
}
}
else
{
lean_dec_ref_known(v_x_2400_, 3);
lean_dec_ref(v_f_2399_);
return v___x_2450_;
}
}
case 10:
{
lean_object* v_data_2485_; lean_object* v_expr_2486_; lean_object* v___x_2487_; 
v_data_2485_ = lean_ctor_get(v_x_2400_, 0);
v_expr_2486_ = lean_ctor_get(v_x_2400_, 1);
lean_inc_ref(v_expr_2486_);
v___x_2487_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2399_, v_expr_2486_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
if (lean_obj_tag(v___x_2487_) == 0)
{
lean_object* v_a_2488_; lean_object* v___x_2490_; uint8_t v_isShared_2491_; uint8_t v_isSharedCheck_2510_; 
v_a_2488_ = lean_ctor_get(v___x_2487_, 0);
v_isSharedCheck_2510_ = !lean_is_exclusive(v___x_2487_);
if (v_isSharedCheck_2510_ == 0)
{
v___x_2490_ = v___x_2487_;
v_isShared_2491_ = v_isSharedCheck_2510_;
goto v_resetjp_2489_;
}
else
{
lean_inc(v_a_2488_);
lean_dec(v___x_2487_);
v___x_2490_ = lean_box(0);
v_isShared_2491_ = v_isSharedCheck_2510_;
goto v_resetjp_2489_;
}
v_resetjp_2489_:
{
lean_object* v_fst_2492_; lean_object* v_snd_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2509_; 
v_fst_2492_ = lean_ctor_get(v_a_2488_, 0);
v_snd_2493_ = lean_ctor_get(v_a_2488_, 1);
v_isSharedCheck_2509_ = !lean_is_exclusive(v_a_2488_);
if (v_isSharedCheck_2509_ == 0)
{
v___x_2495_ = v_a_2488_;
v_isShared_2496_ = v_isSharedCheck_2509_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_snd_2493_);
lean_inc(v_fst_2492_);
lean_dec(v_a_2488_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2509_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v___y_2498_; size_t v___x_2505_; size_t v___x_2506_; uint8_t v___x_2507_; 
v___x_2505_ = lean_ptr_addr(v_expr_2486_);
v___x_2506_ = lean_ptr_addr(v_fst_2492_);
v___x_2507_ = lean_usize_dec_eq(v___x_2505_, v___x_2506_);
if (v___x_2507_ == 0)
{
lean_object* v___x_2508_; 
lean_inc(v_data_2485_);
lean_dec_ref_known(v_x_2400_, 2);
v___x_2508_ = l_Lean_Expr_mdata___override(v_data_2485_, v_fst_2492_);
v___y_2498_ = v___x_2508_;
goto v___jp_2497_;
}
else
{
lean_dec(v_fst_2492_);
v___y_2498_ = v_x_2400_;
goto v___jp_2497_;
}
v___jp_2497_:
{
lean_object* v___x_2500_; 
if (v_isShared_2496_ == 0)
{
lean_ctor_set(v___x_2495_, 0, v___y_2498_);
v___x_2500_ = v___x_2495_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v___y_2498_);
lean_ctor_set(v_reuseFailAlloc_2504_, 1, v_snd_2493_);
v___x_2500_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
lean_object* v___x_2502_; 
if (v_isShared_2491_ == 0)
{
lean_ctor_set(v___x_2490_, 0, v___x_2500_);
v___x_2502_ = v___x_2490_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v___x_2500_);
v___x_2502_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
return v___x_2502_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_x_2400_, 2);
return v___x_2487_;
}
}
case 8:
{
lean_object* v_declName_2511_; lean_object* v_type_2512_; lean_object* v_value_2513_; lean_object* v_body_2514_; uint8_t v_nondep_2515_; lean_object* v___x_2516_; 
v_declName_2511_ = lean_ctor_get(v_x_2400_, 0);
v_type_2512_ = lean_ctor_get(v_x_2400_, 1);
v_value_2513_ = lean_ctor_get(v_x_2400_, 2);
v_body_2514_ = lean_ctor_get(v_x_2400_, 3);
v_nondep_2515_ = lean_ctor_get_uint8(v_x_2400_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_2512_);
lean_inc_ref(v_f_2399_);
v___x_2516_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2399_, v_type_2512_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
if (lean_obj_tag(v___x_2516_) == 0)
{
lean_object* v_a_2517_; lean_object* v_fst_2518_; lean_object* v_snd_2519_; lean_object* v___x_2520_; 
v_a_2517_ = lean_ctor_get(v___x_2516_, 0);
lean_inc(v_a_2517_);
lean_dec_ref_known(v___x_2516_, 1);
v_fst_2518_ = lean_ctor_get(v_a_2517_, 0);
lean_inc(v_fst_2518_);
v_snd_2519_ = lean_ctor_get(v_a_2517_, 1);
lean_inc(v_snd_2519_);
lean_dec(v_a_2517_);
lean_inc_ref(v_value_2513_);
lean_inc_ref(v_f_2399_);
v___x_2520_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2399_, v_value_2513_, v_snd_2519_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
if (lean_obj_tag(v___x_2520_) == 0)
{
lean_object* v_a_2521_; lean_object* v_fst_2522_; lean_object* v_snd_2523_; lean_object* v___x_2524_; 
v_a_2521_ = lean_ctor_get(v___x_2520_, 0);
lean_inc(v_a_2521_);
lean_dec_ref_known(v___x_2520_, 1);
v_fst_2522_ = lean_ctor_get(v_a_2521_, 0);
lean_inc(v_fst_2522_);
v_snd_2523_ = lean_ctor_get(v_a_2521_, 1);
lean_inc(v_snd_2523_);
lean_dec(v_a_2521_);
lean_inc_ref(v_body_2514_);
v___x_2524_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2399_, v_body_2514_, v_snd_2523_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
if (lean_obj_tag(v___x_2524_) == 0)
{
lean_object* v_a_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2556_; 
v_a_2525_ = lean_ctor_get(v___x_2524_, 0);
v_isSharedCheck_2556_ = !lean_is_exclusive(v___x_2524_);
if (v_isSharedCheck_2556_ == 0)
{
v___x_2527_ = v___x_2524_;
v_isShared_2528_ = v_isSharedCheck_2556_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_a_2525_);
lean_dec(v___x_2524_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2556_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v_fst_2529_; lean_object* v_snd_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2555_; 
v_fst_2529_ = lean_ctor_get(v_a_2525_, 0);
v_snd_2530_ = lean_ctor_get(v_a_2525_, 1);
v_isSharedCheck_2555_ = !lean_is_exclusive(v_a_2525_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2532_ = v_a_2525_;
v_isShared_2533_ = v_isSharedCheck_2555_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_snd_2530_);
lean_inc(v_fst_2529_);
lean_dec(v_a_2525_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2555_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v___y_2535_; uint8_t v___y_2543_; size_t v___x_2549_; size_t v___x_2550_; uint8_t v___x_2551_; 
v___x_2549_ = lean_ptr_addr(v_type_2512_);
v___x_2550_ = lean_ptr_addr(v_fst_2518_);
v___x_2551_ = lean_usize_dec_eq(v___x_2549_, v___x_2550_);
if (v___x_2551_ == 0)
{
v___y_2543_ = v___x_2551_;
goto v___jp_2542_;
}
else
{
size_t v___x_2552_; size_t v___x_2553_; uint8_t v___x_2554_; 
v___x_2552_ = lean_ptr_addr(v_value_2513_);
v___x_2553_ = lean_ptr_addr(v_fst_2522_);
v___x_2554_ = lean_usize_dec_eq(v___x_2552_, v___x_2553_);
v___y_2543_ = v___x_2554_;
goto v___jp_2542_;
}
v___jp_2534_:
{
lean_object* v___x_2537_; 
if (v_isShared_2533_ == 0)
{
lean_ctor_set(v___x_2532_, 0, v___y_2535_);
v___x_2537_ = v___x_2532_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v___y_2535_);
lean_ctor_set(v_reuseFailAlloc_2541_, 1, v_snd_2530_);
v___x_2537_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
lean_object* v___x_2539_; 
if (v_isShared_2528_ == 0)
{
lean_ctor_set(v___x_2527_, 0, v___x_2537_);
v___x_2539_ = v___x_2527_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v___x_2537_);
v___x_2539_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
return v___x_2539_;
}
}
}
v___jp_2542_:
{
if (v___y_2543_ == 0)
{
lean_object* v___x_2544_; 
lean_inc(v_declName_2511_);
lean_dec_ref_known(v_x_2400_, 4);
v___x_2544_ = l_Lean_Expr_letE___override(v_declName_2511_, v_fst_2518_, v_fst_2522_, v_fst_2529_, v_nondep_2515_);
v___y_2535_ = v___x_2544_;
goto v___jp_2534_;
}
else
{
size_t v___x_2545_; size_t v___x_2546_; uint8_t v___x_2547_; 
v___x_2545_ = lean_ptr_addr(v_body_2514_);
v___x_2546_ = lean_ptr_addr(v_fst_2529_);
v___x_2547_ = lean_usize_dec_eq(v___x_2545_, v___x_2546_);
if (v___x_2547_ == 0)
{
lean_object* v___x_2548_; 
lean_inc(v_declName_2511_);
lean_dec_ref_known(v_x_2400_, 4);
v___x_2548_ = l_Lean_Expr_letE___override(v_declName_2511_, v_fst_2518_, v_fst_2522_, v_fst_2529_, v_nondep_2515_);
v___y_2535_ = v___x_2548_;
goto v___jp_2534_;
}
else
{
lean_dec(v_fst_2529_);
lean_dec(v_fst_2522_);
lean_dec(v_fst_2518_);
v___y_2535_ = v_x_2400_;
goto v___jp_2534_;
}
}
}
}
}
}
else
{
lean_dec(v_fst_2522_);
lean_dec(v_fst_2518_);
lean_dec_ref_known(v_x_2400_, 4);
return v___x_2524_;
}
}
else
{
lean_dec(v_fst_2518_);
lean_dec_ref_known(v_x_2400_, 4);
lean_dec_ref(v_f_2399_);
return v___x_2520_;
}
}
else
{
lean_dec_ref_known(v_x_2400_, 4);
lean_dec_ref(v_f_2399_);
return v___x_2516_;
}
}
case 5:
{
lean_object* v_fn_2557_; lean_object* v_arg_2558_; lean_object* v___x_2559_; 
v_fn_2557_ = lean_ctor_get(v_x_2400_, 0);
v_arg_2558_ = lean_ctor_get(v_x_2400_, 1);
lean_inc_ref(v_fn_2557_);
lean_inc_ref(v_f_2399_);
v___x_2559_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2399_, v_fn_2557_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
if (lean_obj_tag(v___x_2559_) == 0)
{
lean_object* v_a_2560_; lean_object* v_fst_2561_; lean_object* v_snd_2562_; lean_object* v___x_2563_; 
v_a_2560_ = lean_ctor_get(v___x_2559_, 0);
lean_inc(v_a_2560_);
lean_dec_ref_known(v___x_2559_, 1);
v_fst_2561_ = lean_ctor_get(v_a_2560_, 0);
lean_inc(v_fst_2561_);
v_snd_2562_ = lean_ctor_get(v_a_2560_, 1);
lean_inc(v_snd_2562_);
lean_dec(v_a_2560_);
lean_inc_ref(v_arg_2558_);
v___x_2563_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2399_, v_arg_2558_, v_snd_2562_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
if (lean_obj_tag(v___x_2563_) == 0)
{
lean_object* v_a_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2591_; 
v_a_2564_ = lean_ctor_get(v___x_2563_, 0);
v_isSharedCheck_2591_ = !lean_is_exclusive(v___x_2563_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2566_ = v___x_2563_;
v_isShared_2567_ = v_isSharedCheck_2591_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_a_2564_);
lean_dec(v___x_2563_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2591_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v_fst_2568_; lean_object* v_snd_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2590_; 
v_fst_2568_ = lean_ctor_get(v_a_2564_, 0);
v_snd_2569_ = lean_ctor_get(v_a_2564_, 1);
v_isSharedCheck_2590_ = !lean_is_exclusive(v_a_2564_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2571_ = v_a_2564_;
v_isShared_2572_ = v_isSharedCheck_2590_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_snd_2569_);
lean_inc(v_fst_2568_);
lean_dec(v_a_2564_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2590_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___y_2574_; uint8_t v___y_2582_; size_t v___x_2584_; size_t v___x_2585_; uint8_t v___x_2586_; 
v___x_2584_ = lean_ptr_addr(v_fn_2557_);
v___x_2585_ = lean_ptr_addr(v_fst_2561_);
v___x_2586_ = lean_usize_dec_eq(v___x_2584_, v___x_2585_);
if (v___x_2586_ == 0)
{
v___y_2582_ = v___x_2586_;
goto v___jp_2581_;
}
else
{
size_t v___x_2587_; size_t v___x_2588_; uint8_t v___x_2589_; 
v___x_2587_ = lean_ptr_addr(v_arg_2558_);
v___x_2588_ = lean_ptr_addr(v_fst_2568_);
v___x_2589_ = lean_usize_dec_eq(v___x_2587_, v___x_2588_);
v___y_2582_ = v___x_2589_;
goto v___jp_2581_;
}
v___jp_2573_:
{
lean_object* v___x_2576_; 
if (v_isShared_2572_ == 0)
{
lean_ctor_set(v___x_2571_, 0, v___y_2574_);
v___x_2576_ = v___x_2571_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v___y_2574_);
lean_ctor_set(v_reuseFailAlloc_2580_, 1, v_snd_2569_);
v___x_2576_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
lean_object* v___x_2578_; 
if (v_isShared_2567_ == 0)
{
lean_ctor_set(v___x_2566_, 0, v___x_2576_);
v___x_2578_ = v___x_2566_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v___x_2576_);
v___x_2578_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
return v___x_2578_;
}
}
}
v___jp_2581_:
{
if (v___y_2582_ == 0)
{
lean_object* v___x_2583_; 
lean_dec_ref_known(v_x_2400_, 2);
v___x_2583_ = l_Lean_Expr_app___override(v_fst_2561_, v_fst_2568_);
v___y_2574_ = v___x_2583_;
goto v___jp_2573_;
}
else
{
lean_dec(v_fst_2568_);
lean_dec(v_fst_2561_);
v___y_2574_ = v_x_2400_;
goto v___jp_2573_;
}
}
}
}
}
else
{
lean_dec(v_fst_2561_);
lean_dec_ref_known(v_x_2400_, 2);
return v___x_2563_;
}
}
else
{
lean_dec_ref_known(v_x_2400_, 2);
lean_dec_ref(v_f_2399_);
return v___x_2559_;
}
}
case 11:
{
lean_object* v_typeName_2592_; lean_object* v_idx_2593_; lean_object* v_struct_2594_; lean_object* v___x_2595_; 
v_typeName_2592_ = lean_ctor_get(v_x_2400_, 0);
v_idx_2593_ = lean_ctor_get(v_x_2400_, 1);
v_struct_2594_ = lean_ctor_get(v_x_2400_, 2);
lean_inc_ref(v_struct_2594_);
v___x_2595_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2399_, v_struct_2594_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_object* v_a_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2618_; 
v_a_2596_ = lean_ctor_get(v___x_2595_, 0);
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2598_ = v___x_2595_;
v_isShared_2599_ = v_isSharedCheck_2618_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_a_2596_);
lean_dec(v___x_2595_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2618_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v_fst_2600_; lean_object* v_snd_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2617_; 
v_fst_2600_ = lean_ctor_get(v_a_2596_, 0);
v_snd_2601_ = lean_ctor_get(v_a_2596_, 1);
v_isSharedCheck_2617_ = !lean_is_exclusive(v_a_2596_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2603_ = v_a_2596_;
v_isShared_2604_ = v_isSharedCheck_2617_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_snd_2601_);
lean_inc(v_fst_2600_);
lean_dec(v_a_2596_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2617_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v___y_2606_; size_t v___x_2613_; size_t v___x_2614_; uint8_t v___x_2615_; 
v___x_2613_ = lean_ptr_addr(v_struct_2594_);
v___x_2614_ = lean_ptr_addr(v_fst_2600_);
v___x_2615_ = lean_usize_dec_eq(v___x_2613_, v___x_2614_);
if (v___x_2615_ == 0)
{
lean_object* v___x_2616_; 
lean_inc(v_idx_2593_);
lean_inc(v_typeName_2592_);
lean_dec_ref_known(v_x_2400_, 3);
v___x_2616_ = l_Lean_Expr_proj___override(v_typeName_2592_, v_idx_2593_, v_fst_2600_);
v___y_2606_ = v___x_2616_;
goto v___jp_2605_;
}
else
{
lean_dec(v_fst_2600_);
v___y_2606_ = v_x_2400_;
goto v___jp_2605_;
}
v___jp_2605_:
{
lean_object* v___x_2608_; 
if (v_isShared_2604_ == 0)
{
lean_ctor_set(v___x_2603_, 0, v___y_2606_);
v___x_2608_ = v___x_2603_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v___y_2606_);
lean_ctor_set(v_reuseFailAlloc_2612_, 1, v_snd_2601_);
v___x_2608_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
lean_object* v___x_2610_; 
if (v_isShared_2599_ == 0)
{
lean_ctor_set(v___x_2598_, 0, v___x_2608_);
v___x_2610_ = v___x_2598_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v___x_2608_);
v___x_2610_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
return v___x_2610_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_x_2400_, 3);
return v___x_2595_;
}
}
default: 
{
lean_object* v___x_2619_; lean_object* v___x_2620_; 
lean_dec_ref(v_f_2399_);
v___x_2619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2619_, 0, v_x_2400_);
lean_ctor_set(v___x_2619_, 1, v___y_2401_);
v___x_2620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2620_, 0, v___x_2619_);
return v___x_2620_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___boxed(lean_object* v_f_2621_, lean_object* v_x_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_){
_start:
{
lean_object* v_res_2629_; 
v_res_2629_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg(v_f_2621_, v_x_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_);
lean_dec(v___y_2627_);
lean_dec_ref(v___y_2626_);
lean_dec(v___y_2625_);
lean_dec_ref(v___y_2624_);
return v_res_2629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg(lean_object* v_f_2630_, lean_object* v_init_2631_, lean_object* v_e_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_){
_start:
{
lean_object* v___x_2638_; 
v___x_2638_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg(v_f_2630_, v_e_2632_, v_init_2631_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
if (lean_obj_tag(v___x_2638_) == 0)
{
lean_object* v_a_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2647_; 
v_a_2639_ = lean_ctor_get(v___x_2638_, 0);
v_isSharedCheck_2647_ = !lean_is_exclusive(v___x_2638_);
if (v_isSharedCheck_2647_ == 0)
{
v___x_2641_ = v___x_2638_;
v_isShared_2642_ = v_isSharedCheck_2647_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_a_2639_);
lean_dec(v___x_2638_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2647_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v_snd_2643_; lean_object* v___x_2645_; 
v_snd_2643_ = lean_ctor_get(v_a_2639_, 1);
lean_inc(v_snd_2643_);
lean_dec(v_a_2639_);
if (v_isShared_2642_ == 0)
{
lean_ctor_set(v___x_2641_, 0, v_snd_2643_);
v___x_2645_ = v___x_2641_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_snd_2643_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
return v___x_2645_;
}
}
}
else
{
lean_object* v_a_2648_; lean_object* v___x_2650_; uint8_t v_isShared_2651_; uint8_t v_isSharedCheck_2655_; 
v_a_2648_ = lean_ctor_get(v___x_2638_, 0);
v_isSharedCheck_2655_ = !lean_is_exclusive(v___x_2638_);
if (v_isSharedCheck_2655_ == 0)
{
v___x_2650_ = v___x_2638_;
v_isShared_2651_ = v_isSharedCheck_2655_;
goto v_resetjp_2649_;
}
else
{
lean_inc(v_a_2648_);
lean_dec(v___x_2638_);
v___x_2650_ = lean_box(0);
v_isShared_2651_ = v_isSharedCheck_2655_;
goto v_resetjp_2649_;
}
v_resetjp_2649_:
{
lean_object* v___x_2653_; 
if (v_isShared_2651_ == 0)
{
v___x_2653_ = v___x_2650_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v_a_2648_);
v___x_2653_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
return v___x_2653_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg___boxed(lean_object* v_f_2656_, lean_object* v_init_2657_, lean_object* v_e_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_){
_start:
{
lean_object* v_res_2664_; 
v_res_2664_ = l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg(v_f_2656_, v_init_2657_, v_e_2658_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_);
lean_dec(v___y_2662_);
lean_dec_ref(v___y_2661_);
lean_dec(v___y_2660_);
lean_dec_ref(v___y_2659_);
return v_res_2664_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(lean_object* v_op_2667_, lean_object* v_as_2668_, size_t v_i_2669_, size_t v_stop_2670_, lean_object* v_b_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_){
_start:
{
lean_object* v_a_2678_; uint8_t v___x_2682_; 
v___x_2682_ = lean_usize_dec_eq(v_i_2669_, v_stop_2670_);
if (v___x_2682_ == 0)
{
lean_object* v___x_2683_; lean_object* v___x_2684_; 
v___x_2683_ = lean_array_uget_borrowed(v_as_2668_, v_i_2669_);
lean_inc(v___y_2675_);
lean_inc_ref(v___y_2674_);
lean_inc(v___y_2673_);
lean_inc_ref(v___y_2672_);
lean_inc(v___x_2683_);
v___x_2684_ = lean_infer_type(v___x_2683_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_);
if (lean_obj_tag(v___x_2684_) == 0)
{
lean_object* v_a_2685_; lean_object* v___x_2686_; 
v_a_2685_ = lean_ctor_get(v___x_2684_, 0);
lean_inc(v_a_2685_);
lean_dec_ref_known(v___x_2684_, 1);
lean_inc_ref(v_op_2667_);
v___x_2686_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v_op_2667_, v_a_2685_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_);
if (lean_obj_tag(v___x_2686_) == 0)
{
lean_object* v_a_2687_; lean_object* v___x_2688_; 
v_a_2687_ = lean_ctor_get(v___x_2686_, 0);
lean_inc(v_a_2687_);
lean_dec_ref_known(v___x_2686_, 1);
v___x_2688_ = l_Array_append___redArg(v_b_2671_, v_a_2687_);
lean_dec(v_a_2687_);
v_a_2678_ = v___x_2688_;
goto v___jp_2677_;
}
else
{
lean_dec_ref(v_b_2671_);
if (lean_obj_tag(v___x_2686_) == 0)
{
lean_object* v_a_2689_; 
v_a_2689_ = lean_ctor_get(v___x_2686_, 0);
lean_inc(v_a_2689_);
lean_dec_ref_known(v___x_2686_, 1);
v_a_2678_ = v_a_2689_;
goto v___jp_2677_;
}
else
{
lean_dec_ref(v_op_2667_);
return v___x_2686_;
}
}
}
else
{
lean_object* v_a_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2697_; 
lean_dec_ref(v_b_2671_);
lean_dec_ref(v_op_2667_);
v_a_2690_ = lean_ctor_get(v___x_2684_, 0);
v_isSharedCheck_2697_ = !lean_is_exclusive(v___x_2684_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2692_ = v___x_2684_;
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_a_2690_);
lean_dec(v___x_2684_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___x_2695_; 
if (v_isShared_2693_ == 0)
{
v___x_2695_ = v___x_2692_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v_a_2690_);
v___x_2695_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
return v___x_2695_;
}
}
}
}
else
{
lean_object* v___x_2698_; 
lean_dec_ref(v_op_2667_);
v___x_2698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2698_, 0, v_b_2671_);
return v___x_2698_;
}
v___jp_2677_:
{
size_t v___x_2679_; size_t v___x_2680_; 
v___x_2679_ = ((size_t)1ULL);
v___x_2680_ = lean_usize_add(v_i_2669_, v___x_2679_);
v_i_2669_ = v___x_2680_;
v_b_2671_ = v_a_2678_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0(lean_object* v_op_2699_, lean_object* v_args_2700_, lean_object* v_body_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_){
_start:
{
lean_object* v___x_2707_; 
lean_inc_ref(v_op_2699_);
v___x_2707_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v_op_2699_, v_body_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_);
if (lean_obj_tag(v___x_2707_) == 0)
{
lean_object* v_a_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2729_; 
v_a_2708_ = lean_ctor_get(v___x_2707_, 0);
v_isSharedCheck_2729_ = !lean_is_exclusive(v___x_2707_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2710_ = v___x_2707_;
v_isShared_2711_ = v_isSharedCheck_2729_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_a_2708_);
lean_dec(v___x_2707_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2729_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; uint8_t v___x_2715_; 
v___x_2712_ = l_Array_reverse___redArg(v_a_2708_);
v___x_2713_ = lean_unsigned_to_nat(0u);
v___x_2714_ = lean_array_get_size(v_args_2700_);
v___x_2715_ = lean_nat_dec_lt(v___x_2713_, v___x_2714_);
if (v___x_2715_ == 0)
{
lean_object* v___x_2717_; 
lean_dec_ref(v_op_2699_);
if (v_isShared_2711_ == 0)
{
lean_ctor_set(v___x_2710_, 0, v___x_2712_);
v___x_2717_ = v___x_2710_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v___x_2712_);
v___x_2717_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
return v___x_2717_;
}
}
else
{
uint8_t v___x_2719_; 
v___x_2719_ = lean_nat_dec_le(v___x_2714_, v___x_2714_);
if (v___x_2719_ == 0)
{
if (v___x_2715_ == 0)
{
lean_object* v___x_2721_; 
lean_dec_ref(v_op_2699_);
if (v_isShared_2711_ == 0)
{
lean_ctor_set(v___x_2710_, 0, v___x_2712_);
v___x_2721_ = v___x_2710_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v___x_2712_);
v___x_2721_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
return v___x_2721_;
}
}
else
{
size_t v___x_2723_; size_t v___x_2724_; lean_object* v___x_2725_; 
lean_del_object(v___x_2710_);
v___x_2723_ = ((size_t)0ULL);
v___x_2724_ = lean_usize_of_nat(v___x_2714_);
v___x_2725_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(v_op_2699_, v_args_2700_, v___x_2723_, v___x_2724_, v___x_2712_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_);
return v___x_2725_;
}
}
else
{
size_t v___x_2726_; size_t v___x_2727_; lean_object* v___x_2728_; 
lean_del_object(v___x_2710_);
v___x_2726_ = ((size_t)0ULL);
v___x_2727_ = lean_usize_of_nat(v___x_2714_);
v___x_2728_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(v_op_2699_, v_args_2700_, v___x_2726_, v___x_2727_, v___x_2712_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_);
return v___x_2728_;
}
}
}
}
else
{
lean_dec_ref(v_op_2699_);
return v___x_2707_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed(lean_object* v_op_2730_, lean_object* v_args_2731_, lean_object* v_body_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_){
_start:
{
lean_object* v_res_2738_; 
v_res_2738_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0(v_op_2730_, v_args_2731_, v_body_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_);
lean_dec(v___y_2736_);
lean_dec_ref(v___y_2735_);
lean_dec(v___y_2734_);
lean_dec_ref(v___y_2733_);
lean_dec_ref(v_args_2731_);
return v_res_2738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3___boxed(lean_object* v_op_2739_, lean_object* v_a_2740_, lean_object* v_f_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_){
_start:
{
lean_object* v_res_2747_; 
v_res_2747_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3(v_op_2739_, v_a_2740_, v_f_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
return v_res_2747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(lean_object* v_op_2748_, lean_object* v_e_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_){
_start:
{
switch(lean_obj_tag(v_e_2749_))
{
case 0:
{
lean_object* v___x_2755_; lean_object* v___x_2756_; 
lean_dec_ref_known(v_e_2749_, 1);
lean_dec_ref(v_op_2748_);
v___x_2755_ = ((lean_object*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___closed__0));
v___x_2756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2756_, 0, v___x_2755_);
return v___x_2756_;
}
case 7:
{
lean_object* v___f_2757_; uint8_t v___x_2758_; lean_object* v___x_2759_; 
v___f_2757_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2757_, 0, v_op_2748_);
v___x_2758_ = 0;
v___x_2759_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(v_e_2749_, v___f_2757_, v___x_2758_, v_a_2750_, v_a_2751_, v_a_2752_, v_a_2753_);
return v___x_2759_;
}
case 6:
{
lean_object* v___f_2760_; uint8_t v___x_2761_; uint8_t v___x_2762_; lean_object* v___x_2763_; 
v___f_2760_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2760_, 0, v_op_2748_);
v___x_2761_ = 0;
v___x_2762_ = 1;
v___x_2763_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(v_e_2749_, v___f_2760_, v___x_2761_, v___x_2762_, v_a_2750_, v_a_2751_, v_a_2752_, v_a_2753_);
return v___x_2763_;
}
case 8:
{
lean_object* v___f_2764_; uint8_t v___x_2765_; uint8_t v___x_2766_; lean_object* v___x_2767_; 
v___f_2764_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2764_, 0, v_op_2748_);
v___x_2765_ = 0;
v___x_2766_ = 1;
v___x_2767_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(v_e_2749_, v___f_2764_, v___x_2765_, v___x_2766_, v_a_2750_, v_a_2751_, v_a_2752_, v_a_2753_);
return v___x_2767_;
}
default: 
{
lean_object* v___x_2768_; 
lean_inc_ref(v_op_2748_);
lean_inc(v_a_2753_);
lean_inc_ref(v_a_2752_);
lean_inc(v_a_2751_);
lean_inc_ref(v_a_2750_);
lean_inc_ref(v_e_2749_);
v___x_2768_ = lean_apply_6(v_op_2748_, v_e_2749_, v_a_2750_, v_a_2751_, v_a_2752_, v_a_2753_, lean_box(0));
if (lean_obj_tag(v___x_2768_) == 0)
{
lean_object* v_a_2769_; lean_object* v___f_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; 
v_a_2769_ = lean_ctor_get(v___x_2768_, 0);
lean_inc(v_a_2769_);
lean_dec_ref_known(v___x_2768_, 1);
v___f_2770_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3___boxed), 8, 1);
lean_closure_set(v___f_2770_, 0, v_op_2748_);
v___x_2771_ = l_Array_reverse___redArg(v_a_2769_);
v___x_2772_ = l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg(v___f_2770_, v___x_2771_, v_e_2749_, v_a_2750_, v_a_2751_, v_a_2752_, v_a_2753_);
return v___x_2772_;
}
else
{
lean_dec_ref(v_e_2749_);
lean_dec_ref(v_op_2748_);
return v___x_2768_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3(lean_object* v_op_2773_, lean_object* v_a_2774_, lean_object* v_f_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_){
_start:
{
lean_object* v___x_2781_; 
v___x_2781_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v_op_2773_, v_f_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_);
if (lean_obj_tag(v___x_2781_) == 0)
{
lean_object* v_a_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2790_; 
v_a_2782_ = lean_ctor_get(v___x_2781_, 0);
v_isSharedCheck_2790_ = !lean_is_exclusive(v___x_2781_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2784_ = v___x_2781_;
v_isShared_2785_ = v_isSharedCheck_2790_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_a_2782_);
lean_dec(v___x_2781_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2790_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___x_2786_; lean_object* v___x_2788_; 
v___x_2786_ = l_Array_append___redArg(v_a_2774_, v_a_2782_);
lean_dec(v_a_2782_);
if (v_isShared_2785_ == 0)
{
lean_ctor_set(v___x_2784_, 0, v___x_2786_);
v___x_2788_ = v___x_2784_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v___x_2786_);
v___x_2788_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
return v___x_2788_;
}
}
}
else
{
lean_dec_ref(v_a_2774_);
return v___x_2781_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg___boxed(lean_object* v_op_2791_, lean_object* v_as_2792_, lean_object* v_i_2793_, lean_object* v_stop_2794_, lean_object* v_b_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_){
_start:
{
size_t v_i_boxed_2801_; size_t v_stop_boxed_2802_; lean_object* v_res_2803_; 
v_i_boxed_2801_ = lean_unbox_usize(v_i_2793_);
lean_dec(v_i_2793_);
v_stop_boxed_2802_ = lean_unbox_usize(v_stop_2794_);
lean_dec(v_stop_2794_);
v_res_2803_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(v_op_2791_, v_as_2792_, v_i_boxed_2801_, v_stop_boxed_2802_, v_b_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_);
lean_dec(v___y_2799_);
lean_dec_ref(v___y_2798_);
lean_dec(v___y_2797_);
lean_dec_ref(v___y_2796_);
lean_dec_ref(v_as_2792_);
return v_res_2803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___boxed(lean_object* v_op_2804_, lean_object* v_e_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_){
_start:
{
lean_object* v_res_2811_; 
v_res_2811_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v_op_2804_, v_e_2805_, v_a_2806_, v_a_2807_, v_a_2808_, v_a_2809_);
lean_dec(v_a_2809_);
lean_dec_ref(v_a_2808_);
lean_dec(v_a_2807_);
lean_dec_ref(v_a_2806_);
return v_res_2811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches(lean_object* v_00_u03b1_2812_, lean_object* v_op_2813_, lean_object* v_e_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_){
_start:
{
lean_object* v___x_2820_; 
v___x_2820_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v_op_2813_, v_e_2814_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_);
return v___x_2820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___boxed(lean_object* v_00_u03b1_2821_, lean_object* v_op_2822_, lean_object* v_e_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_){
_start:
{
lean_object* v_res_2829_; 
v_res_2829_ = l_Lean_Meta_Rewrites_getSubexpressionMatches(v_00_u03b1_2821_, v_op_2822_, v_e_2823_, v_a_2824_, v_a_2825_, v_a_2826_, v_a_2827_);
lean_dec(v_a_2827_);
lean_dec_ref(v_a_2826_);
lean_dec(v_a_2825_);
lean_dec_ref(v_a_2824_);
return v_res_2829_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0(lean_object* v_00_u03b1_2830_, lean_object* v_op_2831_, lean_object* v_as_2832_, size_t v_i_2833_, size_t v_stop_2834_, lean_object* v_b_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_){
_start:
{
lean_object* v___x_2841_; 
v___x_2841_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(v_op_2831_, v_as_2832_, v_i_2833_, v_stop_2834_, v_b_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
return v___x_2841_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___boxed(lean_object* v_00_u03b1_2842_, lean_object* v_op_2843_, lean_object* v_as_2844_, lean_object* v_i_2845_, lean_object* v_stop_2846_, lean_object* v_b_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_){
_start:
{
size_t v_i_boxed_2853_; size_t v_stop_boxed_2854_; lean_object* v_res_2855_; 
v_i_boxed_2853_ = lean_unbox_usize(v_i_2845_);
lean_dec(v_i_2845_);
v_stop_boxed_2854_ = lean_unbox_usize(v_stop_2846_);
lean_dec(v_stop_2846_);
v_res_2855_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0(v_00_u03b1_2842_, v_op_2843_, v_as_2844_, v_i_boxed_2853_, v_stop_boxed_2854_, v_b_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_);
lean_dec(v___y_2851_);
lean_dec_ref(v___y_2850_);
lean_dec(v___y_2849_);
lean_dec_ref(v___y_2848_);
lean_dec_ref(v_as_2844_);
return v_res_2855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3(lean_object* v_00_u03b1_2856_, lean_object* v_f_2857_, lean_object* v_x_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_){
_start:
{
lean_object* v___x_2865_; 
v___x_2865_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg(v_f_2857_, v_x_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
return v___x_2865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___boxed(lean_object* v_00_u03b1_2866_, lean_object* v_f_2867_, lean_object* v_x_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_){
_start:
{
lean_object* v_res_2875_; 
v_res_2875_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3(v_00_u03b1_2866_, v_f_2867_, v_x_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
return v_res_2875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3(lean_object* v_00_u03b1_2876_, lean_object* v_f_2877_, lean_object* v_init_2878_, lean_object* v_e_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_){
_start:
{
lean_object* v___x_2885_; 
v___x_2885_ = l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg(v_f_2877_, v_init_2878_, v_e_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
return v___x_2885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___boxed(lean_object* v_00_u03b1_2886_, lean_object* v_f_2887_, lean_object* v_init_2888_, lean_object* v_e_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_){
_start:
{
lean_object* v_res_2895_; 
v_res_2895_ = l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3(v_00_u03b1_2886_, v_f_2887_, v_init_2888_, v_e_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_);
lean_dec(v___y_2893_);
lean_dec_ref(v___y_2892_);
lean_dec(v___y_2891_);
lean_dec_ref(v___y_2890_);
return v_res_2895_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__3(size_t v_sz_2896_, size_t v_i_2897_, lean_object* v_bs_2898_){
_start:
{
uint8_t v___x_2899_; 
v___x_2899_ = lean_usize_dec_lt(v_i_2897_, v_sz_2896_);
if (v___x_2899_ == 0)
{
return v_bs_2898_;
}
else
{
lean_object* v_v_2900_; lean_object* v_fst_2901_; lean_object* v_snd_2902_; lean_object* v___x_2904_; uint8_t v_isShared_2905_; uint8_t v_isSharedCheck_2916_; 
v_v_2900_ = lean_array_uget(v_bs_2898_, v_i_2897_);
v_fst_2901_ = lean_ctor_get(v_v_2900_, 0);
v_snd_2902_ = lean_ctor_get(v_v_2900_, 1);
v_isSharedCheck_2916_ = !lean_is_exclusive(v_v_2900_);
if (v_isSharedCheck_2916_ == 0)
{
v___x_2904_ = v_v_2900_;
v_isShared_2905_ = v_isSharedCheck_2916_;
goto v_resetjp_2903_;
}
else
{
lean_inc(v_snd_2902_);
lean_inc(v_fst_2901_);
lean_dec(v_v_2900_);
v___x_2904_ = lean_box(0);
v_isShared_2905_ = v_isSharedCheck_2916_;
goto v_resetjp_2903_;
}
v_resetjp_2903_:
{
lean_object* v___x_2906_; lean_object* v_bs_x27_2907_; lean_object* v___x_2908_; lean_object* v___x_2910_; 
v___x_2906_ = lean_unsigned_to_nat(0u);
v_bs_x27_2907_ = lean_array_uset(v_bs_2898_, v_i_2897_, v___x_2906_);
v___x_2908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2908_, 0, v_fst_2901_);
if (v_isShared_2905_ == 0)
{
lean_ctor_set(v___x_2904_, 0, v___x_2908_);
v___x_2910_ = v___x_2904_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v___x_2908_);
lean_ctor_set(v_reuseFailAlloc_2915_, 1, v_snd_2902_);
v___x_2910_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
size_t v___x_2911_; size_t v___x_2912_; lean_object* v___x_2913_; 
v___x_2911_ = ((size_t)1ULL);
v___x_2912_ = lean_usize_add(v_i_2897_, v___x_2911_);
v___x_2913_ = lean_array_uset(v_bs_x27_2907_, v_i_2897_, v___x_2910_);
v_i_2897_ = v___x_2912_;
v_bs_2898_ = v___x_2913_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__3___boxed(lean_object* v_sz_2917_, lean_object* v_i_2918_, lean_object* v_bs_2919_){
_start:
{
size_t v_sz_boxed_2920_; size_t v_i_boxed_2921_; lean_object* v_res_2922_; 
v_sz_boxed_2920_ = lean_unbox_usize(v_sz_2917_);
lean_dec(v_sz_2917_);
v_i_boxed_2921_ = lean_unbox_usize(v_i_2918_);
lean_dec(v_i_2918_);
v_res_2922_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__3(v_sz_boxed_2920_, v_i_boxed_2921_, v_bs_2919_);
return v_res_2922_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0___redArg(lean_object* v_xs_2923_, lean_object* v_j_2924_){
_start:
{
lean_object* v_zero_2925_; uint8_t v_isZero_2926_; 
v_zero_2925_ = lean_unsigned_to_nat(0u);
v_isZero_2926_ = lean_nat_dec_eq(v_j_2924_, v_zero_2925_);
if (v_isZero_2926_ == 1)
{
lean_dec(v_j_2924_);
return v_xs_2923_;
}
else
{
lean_object* v___x_2927_; lean_object* v_snd_2928_; lean_object* v_snd_2929_; lean_object* v_one_2930_; lean_object* v_n_2931_; lean_object* v___x_2932_; lean_object* v_snd_2933_; lean_object* v_snd_2934_; uint8_t v___x_2935_; 
v___x_2927_ = lean_array_fget_borrowed(v_xs_2923_, v_j_2924_);
v_snd_2928_ = lean_ctor_get(v___x_2927_, 1);
v_snd_2929_ = lean_ctor_get(v_snd_2928_, 1);
v_one_2930_ = lean_unsigned_to_nat(1u);
v_n_2931_ = lean_nat_sub(v_j_2924_, v_one_2930_);
v___x_2932_ = lean_array_fget_borrowed(v_xs_2923_, v_n_2931_);
v_snd_2933_ = lean_ctor_get(v___x_2932_, 1);
v_snd_2934_ = lean_ctor_get(v_snd_2933_, 1);
v___x_2935_ = lean_nat_dec_lt(v_snd_2934_, v_snd_2929_);
if (v___x_2935_ == 0)
{
lean_dec(v_n_2931_);
lean_dec(v_j_2924_);
return v_xs_2923_;
}
else
{
lean_object* v___x_2936_; 
v___x_2936_ = lean_array_fswap(v_xs_2923_, v_j_2924_, v_n_2931_);
lean_dec(v_j_2924_);
v_xs_2923_ = v___x_2936_;
v_j_2924_ = v_n_2931_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0(lean_object* v_xs_2938_, lean_object* v_i_2939_, lean_object* v_fuel_2940_){
_start:
{
lean_object* v_zero_2941_; uint8_t v_isZero_2942_; 
v_zero_2941_ = lean_unsigned_to_nat(0u);
v_isZero_2942_ = lean_nat_dec_eq(v_fuel_2940_, v_zero_2941_);
if (v_isZero_2942_ == 1)
{
lean_dec(v_fuel_2940_);
lean_dec(v_i_2939_);
return v_xs_2938_;
}
else
{
lean_object* v___x_2943_; uint8_t v___x_2944_; 
v___x_2943_ = lean_array_get_size(v_xs_2938_);
v___x_2944_ = lean_nat_dec_lt(v_i_2939_, v___x_2943_);
if (v___x_2944_ == 0)
{
lean_dec(v_fuel_2940_);
lean_dec(v_i_2939_);
return v_xs_2938_;
}
else
{
lean_object* v_one_2945_; lean_object* v_n_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; 
v_one_2945_ = lean_unsigned_to_nat(1u);
v_n_2946_ = lean_nat_sub(v_fuel_2940_, v_one_2945_);
lean_dec(v_fuel_2940_);
lean_inc(v_i_2939_);
v___x_2947_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0___redArg(v_xs_2938_, v_i_2939_);
v___x_2948_ = lean_nat_add(v_i_2939_, v_one_2945_);
lean_dec(v_i_2939_);
v_xs_2938_ = v___x_2947_;
v_i_2939_ = v___x_2948_;
v_fuel_2940_ = v_n_2946_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__2(size_t v_sz_2950_, size_t v_i_2951_, lean_object* v_bs_2952_){
_start:
{
uint8_t v___x_2953_; 
v___x_2953_ = lean_usize_dec_lt(v_i_2951_, v_sz_2950_);
if (v___x_2953_ == 0)
{
return v_bs_2952_;
}
else
{
lean_object* v_v_2954_; lean_object* v_fst_2955_; lean_object* v_snd_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_2970_; 
v_v_2954_ = lean_array_uget(v_bs_2952_, v_i_2951_);
v_fst_2955_ = lean_ctor_get(v_v_2954_, 0);
v_snd_2956_ = lean_ctor_get(v_v_2954_, 1);
v_isSharedCheck_2970_ = !lean_is_exclusive(v_v_2954_);
if (v_isSharedCheck_2970_ == 0)
{
v___x_2958_ = v_v_2954_;
v_isShared_2959_ = v_isSharedCheck_2970_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_snd_2956_);
lean_inc(v_fst_2955_);
lean_dec(v_v_2954_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_2970_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v___x_2960_; lean_object* v_bs_x27_2961_; lean_object* v___x_2962_; lean_object* v___x_2964_; 
v___x_2960_ = lean_unsigned_to_nat(0u);
v_bs_x27_2961_ = lean_array_uset(v_bs_2952_, v_i_2951_, v___x_2960_);
v___x_2962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2962_, 0, v_fst_2955_);
if (v_isShared_2959_ == 0)
{
lean_ctor_set(v___x_2958_, 0, v___x_2962_);
v___x_2964_ = v___x_2958_;
goto v_reusejp_2963_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v___x_2962_);
lean_ctor_set(v_reuseFailAlloc_2969_, 1, v_snd_2956_);
v___x_2964_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2963_;
}
v_reusejp_2963_:
{
size_t v___x_2965_; size_t v___x_2966_; lean_object* v___x_2967_; 
v___x_2965_ = ((size_t)1ULL);
v___x_2966_ = lean_usize_add(v_i_2951_, v___x_2965_);
v___x_2967_ = lean_array_uset(v_bs_x27_2961_, v_i_2951_, v___x_2964_);
v_i_2951_ = v___x_2966_;
v_bs_2952_ = v___x_2967_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__2___boxed(lean_object* v_sz_2971_, lean_object* v_i_2972_, lean_object* v_bs_2973_){
_start:
{
size_t v_sz_boxed_2974_; size_t v_i_boxed_2975_; lean_object* v_res_2976_; 
v_sz_boxed_2974_ = lean_unbox_usize(v_sz_2971_);
lean_dec(v_sz_2971_);
v_i_boxed_2975_ = lean_unbox_usize(v_i_2972_);
lean_dec(v_i_2972_);
v_res_2976_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__2(v_sz_boxed_2974_, v_i_boxed_2975_, v_bs_2973_);
return v_res_2976_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg(lean_object* v_forbidden_2977_, lean_object* v_as_2978_, size_t v_sz_2979_, size_t v_i_2980_, lean_object* v_b_2981_){
_start:
{
lean_object* v_a_2984_; uint8_t v___x_2988_; 
v___x_2988_ = lean_usize_dec_lt(v_i_2980_, v_sz_2979_);
if (v___x_2988_ == 0)
{
lean_object* v___x_2989_; 
v___x_2989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2989_, 0, v_b_2981_);
return v___x_2989_;
}
else
{
lean_object* v_a_2990_; lean_object* v_snd_2991_; lean_object* v_snd_2992_; lean_object* v_fst_2993_; lean_object* v_fst_2994_; lean_object* v___x_2996_; uint8_t v_isShared_2997_; uint8_t v_isSharedCheck_3044_; 
v_a_2990_ = lean_array_uget(v_as_2978_, v_i_2980_);
v_snd_2991_ = lean_ctor_get(v_a_2990_, 1);
lean_inc(v_snd_2991_);
v_snd_2992_ = lean_ctor_get(v_b_2981_, 1);
lean_inc(v_snd_2992_);
v_fst_2993_ = lean_ctor_get(v_a_2990_, 0);
v_fst_2994_ = lean_ctor_get(v_snd_2991_, 0);
v_isSharedCheck_3044_ = !lean_is_exclusive(v_snd_2991_);
if (v_isSharedCheck_3044_ == 0)
{
lean_object* v_unused_3045_; 
v_unused_3045_ = lean_ctor_get(v_snd_2991_, 1);
lean_dec(v_unused_3045_);
v___x_2996_ = v_snd_2991_;
v_isShared_2997_ = v_isSharedCheck_3044_;
goto v_resetjp_2995_;
}
else
{
lean_inc(v_fst_2994_);
lean_dec(v_snd_2991_);
v___x_2996_ = lean_box(0);
v_isShared_2997_ = v_isSharedCheck_3044_;
goto v_resetjp_2995_;
}
v_resetjp_2995_:
{
lean_object* v_fst_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3042_; 
v_fst_2998_ = lean_ctor_get(v_b_2981_, 0);
v_isSharedCheck_3042_ = !lean_is_exclusive(v_b_2981_);
if (v_isSharedCheck_3042_ == 0)
{
lean_object* v_unused_3043_; 
v_unused_3043_ = lean_ctor_get(v_b_2981_, 1);
lean_dec(v_unused_3043_);
v___x_3000_ = v_b_2981_;
v_isShared_3001_ = v_isSharedCheck_3042_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_fst_2998_);
lean_dec(v_b_2981_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3042_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v_fst_3002_; lean_object* v_snd_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3041_; 
v_fst_3002_ = lean_ctor_get(v_snd_2992_, 0);
v_snd_3003_ = lean_ctor_get(v_snd_2992_, 1);
v_isSharedCheck_3041_ = !lean_is_exclusive(v_snd_2992_);
if (v_isSharedCheck_3041_ == 0)
{
v___x_3005_ = v_snd_2992_;
v_isShared_3006_ = v_isSharedCheck_3041_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_snd_3003_);
lean_inc(v_fst_3002_);
lean_dec(v_snd_2992_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3041_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
uint8_t v___x_3019_; 
v___x_3019_ = l_Lean_NameSet_contains(v_forbidden_2977_, v_fst_2993_);
if (v___x_3019_ == 0)
{
uint8_t v___x_3020_; 
lean_inc(v_fst_2993_);
v___x_3020_ = lean_unbox(v_fst_2994_);
lean_dec(v_fst_2994_);
if (v___x_3020_ == 0)
{
uint8_t v___x_3021_; 
lean_del_object(v___x_3005_);
lean_del_object(v___x_3000_);
v___x_3021_ = l_Lean_NameSet_contains(v_fst_2998_, v_fst_2993_);
if (v___x_3021_ == 0)
{
if (v___x_2988_ == 0)
{
lean_dec(v_fst_2993_);
lean_dec(v_a_2990_);
goto v___jp_3014_;
}
else
{
lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; 
lean_del_object(v___x_2996_);
v___x_3022_ = lean_array_push(v_snd_3003_, v_a_2990_);
v___x_3023_ = l_Lean_NameSet_insert(v_fst_2998_, v_fst_2993_);
v___x_3024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3024_, 0, v_fst_3002_);
lean_ctor_set(v___x_3024_, 1, v___x_3022_);
v___x_3025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3025_, 0, v___x_3023_);
lean_ctor_set(v___x_3025_, 1, v___x_3024_);
v_a_2984_ = v___x_3025_;
goto v___jp_2983_;
}
}
else
{
lean_dec(v_fst_2993_);
lean_dec(v_a_2990_);
goto v___jp_3014_;
}
}
else
{
uint8_t v___x_3026_; 
lean_del_object(v___x_2996_);
v___x_3026_ = l_Lean_NameSet_contains(v_fst_3002_, v_fst_2993_);
if (v___x_3026_ == 0)
{
if (v___x_2988_ == 0)
{
lean_dec(v_fst_2993_);
lean_dec(v_a_2990_);
goto v___jp_3007_;
}
else
{
lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; 
lean_del_object(v___x_3005_);
lean_del_object(v___x_3000_);
v___x_3027_ = lean_array_push(v_snd_3003_, v_a_2990_);
v___x_3028_ = l_Lean_NameSet_insert(v_fst_3002_, v_fst_2993_);
v___x_3029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3028_);
lean_ctor_set(v___x_3029_, 1, v___x_3027_);
v___x_3030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3030_, 0, v_fst_2998_);
lean_ctor_set(v___x_3030_, 1, v___x_3029_);
v_a_2984_ = v___x_3030_;
goto v___jp_2983_;
}
}
else
{
lean_dec(v_fst_2993_);
lean_dec(v_a_2990_);
goto v___jp_3007_;
}
}
}
else
{
lean_object* v___x_3032_; uint8_t v_isShared_3033_; uint8_t v_isSharedCheck_3038_; 
lean_del_object(v___x_3005_);
lean_del_object(v___x_3000_);
lean_del_object(v___x_2996_);
lean_dec(v_fst_2994_);
v_isSharedCheck_3038_ = !lean_is_exclusive(v_a_2990_);
if (v_isSharedCheck_3038_ == 0)
{
lean_object* v_unused_3039_; lean_object* v_unused_3040_; 
v_unused_3039_ = lean_ctor_get(v_a_2990_, 1);
lean_dec(v_unused_3039_);
v_unused_3040_ = lean_ctor_get(v_a_2990_, 0);
lean_dec(v_unused_3040_);
v___x_3032_ = v_a_2990_;
v_isShared_3033_ = v_isSharedCheck_3038_;
goto v_resetjp_3031_;
}
else
{
lean_dec(v_a_2990_);
v___x_3032_ = lean_box(0);
v_isShared_3033_ = v_isSharedCheck_3038_;
goto v_resetjp_3031_;
}
v_resetjp_3031_:
{
lean_object* v___x_3035_; 
if (v_isShared_3033_ == 0)
{
lean_ctor_set(v___x_3032_, 1, v_snd_3003_);
lean_ctor_set(v___x_3032_, 0, v_fst_3002_);
v___x_3035_ = v___x_3032_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v_fst_3002_);
lean_ctor_set(v_reuseFailAlloc_3037_, 1, v_snd_3003_);
v___x_3035_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
lean_object* v___x_3036_; 
v___x_3036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3036_, 0, v_fst_2998_);
lean_ctor_set(v___x_3036_, 1, v___x_3035_);
v_a_2984_ = v___x_3036_;
goto v___jp_2983_;
}
}
}
v___jp_3007_:
{
lean_object* v___x_3009_; 
if (v_isShared_3006_ == 0)
{
v___x_3009_ = v___x_3005_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_fst_3002_);
lean_ctor_set(v_reuseFailAlloc_3013_, 1, v_snd_3003_);
v___x_3009_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
lean_object* v___x_3011_; 
if (v_isShared_3001_ == 0)
{
lean_ctor_set(v___x_3000_, 1, v___x_3009_);
v___x_3011_ = v___x_3000_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v_fst_2998_);
lean_ctor_set(v_reuseFailAlloc_3012_, 1, v___x_3009_);
v___x_3011_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
v_a_2984_ = v___x_3011_;
goto v___jp_2983_;
}
}
}
v___jp_3014_:
{
lean_object* v___x_3016_; 
if (v_isShared_2997_ == 0)
{
lean_ctor_set(v___x_2996_, 1, v_snd_3003_);
lean_ctor_set(v___x_2996_, 0, v_fst_3002_);
v___x_3016_ = v___x_2996_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3018_; 
v_reuseFailAlloc_3018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3018_, 0, v_fst_3002_);
lean_ctor_set(v_reuseFailAlloc_3018_, 1, v_snd_3003_);
v___x_3016_ = v_reuseFailAlloc_3018_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
lean_object* v___x_3017_; 
v___x_3017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3017_, 0, v_fst_2998_);
lean_ctor_set(v___x_3017_, 1, v___x_3016_);
v_a_2984_ = v___x_3017_;
goto v___jp_2983_;
}
}
}
}
}
}
v___jp_2983_:
{
size_t v___x_2985_; size_t v___x_2986_; 
v___x_2985_ = ((size_t)1ULL);
v___x_2986_ = lean_usize_add(v_i_2980_, v___x_2985_);
v_i_2980_ = v___x_2986_;
v_b_2981_ = v_a_2984_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg___boxed(lean_object* v_forbidden_3046_, lean_object* v_as_3047_, lean_object* v_sz_3048_, lean_object* v_i_3049_, lean_object* v_b_3050_, lean_object* v___y_3051_){
_start:
{
size_t v_sz_boxed_3052_; size_t v_i_boxed_3053_; lean_object* v_res_3054_; 
v_sz_boxed_3052_ = lean_unbox_usize(v_sz_3048_);
lean_dec(v_sz_3048_);
v_i_boxed_3053_ = lean_unbox_usize(v_i_3049_);
lean_dec(v_i_3049_);
v_res_3054_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg(v_forbidden_3046_, v_as_3047_, v_sz_boxed_3052_, v_i_boxed_3053_, v_b_3050_);
lean_dec_ref(v_as_3047_);
lean_dec(v_forbidden_3046_);
return v_res_3054_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__2(void){
_start:
{
lean_object* v___x_3058_; lean_object* v___x_3059_; 
v___x_3058_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__1));
v___x_3059_ = l_Lean_MessageData_ofFormat(v___x_3058_);
return v___x_3059_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__3(void){
_start:
{
lean_object* v___x_3060_; lean_object* v___x_3061_; 
v___x_3060_ = lean_box(1);
v___x_3061_ = l_Lean_MessageData_ofFormat(v___x_3060_);
return v___x_3061_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4(lean_object* v_a_3064_, lean_object* v_a_3065_){
_start:
{
if (lean_obj_tag(v_a_3064_) == 0)
{
lean_object* v___x_3066_; 
v___x_3066_ = l_List_reverse___redArg(v_a_3065_);
return v___x_3066_;
}
else
{
lean_object* v_head_3067_; lean_object* v_snd_3068_; lean_object* v_tail_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3114_; 
v_head_3067_ = lean_ctor_get(v_a_3064_, 0);
lean_inc(v_head_3067_);
v_snd_3068_ = lean_ctor_get(v_head_3067_, 1);
lean_inc(v_snd_3068_);
v_tail_3069_ = lean_ctor_get(v_a_3064_, 1);
v_isSharedCheck_3114_ = !lean_is_exclusive(v_a_3064_);
if (v_isSharedCheck_3114_ == 0)
{
lean_object* v_unused_3115_; 
v_unused_3115_ = lean_ctor_get(v_a_3064_, 0);
lean_dec(v_unused_3115_);
v___x_3071_ = v_a_3064_;
v_isShared_3072_ = v_isSharedCheck_3114_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_tail_3069_);
lean_dec(v_a_3064_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3114_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
lean_object* v_fst_3073_; lean_object* v___x_3075_; uint8_t v_isShared_3076_; uint8_t v_isSharedCheck_3112_; 
v_fst_3073_ = lean_ctor_get(v_head_3067_, 0);
v_isSharedCheck_3112_ = !lean_is_exclusive(v_head_3067_);
if (v_isSharedCheck_3112_ == 0)
{
lean_object* v_unused_3113_; 
v_unused_3113_ = lean_ctor_get(v_head_3067_, 1);
lean_dec(v_unused_3113_);
v___x_3075_ = v_head_3067_;
v_isShared_3076_ = v_isSharedCheck_3112_;
goto v_resetjp_3074_;
}
else
{
lean_inc(v_fst_3073_);
lean_dec(v_head_3067_);
v___x_3075_ = lean_box(0);
v_isShared_3076_ = v_isSharedCheck_3112_;
goto v_resetjp_3074_;
}
v_resetjp_3074_:
{
lean_object* v_fst_3077_; lean_object* v_snd_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3111_; 
v_fst_3077_ = lean_ctor_get(v_snd_3068_, 0);
v_snd_3078_ = lean_ctor_get(v_snd_3068_, 1);
v_isSharedCheck_3111_ = !lean_is_exclusive(v_snd_3068_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3080_ = v_snd_3068_;
v_isShared_3081_ = v_isSharedCheck_3111_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_snd_3078_);
lean_inc(v_fst_3077_);
lean_dec(v_snd_3068_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3111_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3085_; 
v___x_3082_ = l_Lean_MessageData_ofName(v_fst_3073_);
v___x_3083_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__2, &l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__2_once, _init_l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__2);
if (v_isShared_3081_ == 0)
{
lean_ctor_set_tag(v___x_3080_, 7);
lean_ctor_set(v___x_3080_, 1, v___x_3083_);
lean_ctor_set(v___x_3080_, 0, v___x_3082_);
v___x_3085_ = v___x_3080_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v___x_3082_);
lean_ctor_set(v_reuseFailAlloc_3110_, 1, v___x_3083_);
v___x_3085_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
lean_object* v___x_3086_; lean_object* v___x_3088_; 
v___x_3086_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__3, &l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__3_once, _init_l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__3);
if (v_isShared_3076_ == 0)
{
lean_ctor_set_tag(v___x_3075_, 7);
lean_ctor_set(v___x_3075_, 1, v___x_3086_);
lean_ctor_set(v___x_3075_, 0, v___x_3085_);
v___x_3088_ = v___x_3075_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v___x_3085_);
lean_ctor_set(v_reuseFailAlloc_3109_, 1, v___x_3086_);
v___x_3088_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
lean_object* v___y_3090_; uint8_t v___x_3106_; 
v___x_3106_ = lean_unbox(v_fst_3077_);
lean_dec(v_fst_3077_);
if (v___x_3106_ == 0)
{
lean_object* v___x_3107_; 
v___x_3107_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__4));
v___y_3090_ = v___x_3107_;
goto v___jp_3089_;
}
else
{
lean_object* v___x_3108_; 
v___x_3108_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__5));
v___y_3090_ = v___x_3108_;
goto v___jp_3089_;
}
v___jp_3089_:
{
lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3103_; 
lean_inc_ref(v___y_3090_);
v___x_3091_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3091_, 0, v___y_3090_);
v___x_3092_ = l_Lean_MessageData_ofFormat(v___x_3091_);
v___x_3093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3093_, 0, v___x_3092_);
lean_ctor_set(v___x_3093_, 1, v___x_3083_);
v___x_3094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3094_, 0, v___x_3093_);
lean_ctor_set(v___x_3094_, 1, v___x_3086_);
v___x_3095_ = l_Nat_reprFast(v_snd_3078_);
v___x_3096_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3096_, 0, v___x_3095_);
v___x_3097_ = l_Lean_MessageData_ofFormat(v___x_3096_);
v___x_3098_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3098_, 0, v___x_3094_);
lean_ctor_set(v___x_3098_, 1, v___x_3097_);
v___x_3099_ = l_Lean_MessageData_paren(v___x_3098_);
v___x_3100_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3100_, 0, v___x_3088_);
lean_ctor_set(v___x_3100_, 1, v___x_3099_);
v___x_3101_ = l_Lean_MessageData_paren(v___x_3100_);
if (v_isShared_3072_ == 0)
{
lean_ctor_set(v___x_3071_, 1, v_a_3065_);
lean_ctor_set(v___x_3071_, 0, v___x_3101_);
v___x_3103_ = v___x_3071_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v___x_3101_);
lean_ctor_set(v_reuseFailAlloc_3105_, 1, v_a_3065_);
v___x_3103_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
v_a_3064_ = v_tail_3069_;
v_a_3065_ = v___x_3103_;
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
lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; 
v___x_3118_ = ((lean_object*)(l_Lean_Meta_Rewrites_rewriteCandidates___closed__0));
v___x_3119_ = l_Lean_NameSet_empty;
v___x_3120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3120_, 0, v___x_3119_);
lean_ctor_set(v___x_3120_, 1, v___x_3118_);
return v___x_3120_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__2(void){
_start:
{
lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; 
v___x_3121_ = lean_obj_once(&l_Lean_Meta_Rewrites_rewriteCandidates___closed__1, &l_Lean_Meta_Rewrites_rewriteCandidates___closed__1_once, _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__1);
v___x_3122_ = l_Lean_NameSet_empty;
v___x_3123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3123_, 0, v___x_3122_);
lean_ctor_set(v___x_3123_, 1, v___x_3121_);
return v___x_3123_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__3(void){
_start:
{
lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; 
v___x_3124_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_));
v___x_3125_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__4));
v___x_3126_ = l_Lean_Name_append(v___x_3125_, v___x_3124_);
return v___x_3126_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__5(void){
_start:
{
lean_object* v___x_3128_; lean_object* v___x_3129_; 
v___x_3128_ = ((lean_object*)(l_Lean_Meta_Rewrites_rewriteCandidates___closed__4));
v___x_3129_ = l_Lean_stringToMessageData(v___x_3128_);
return v___x_3129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rewriteCandidates(lean_object* v_hyps_3130_, lean_object* v_moduleRef_3131_, lean_object* v_target_3132_, lean_object* v_forbidden_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_){
_start:
{
lean_object* v___x_3139_; lean_object* v___x_3140_; 
v___x_3139_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_rwFindDecls___boxed), 7, 1);
lean_closure_set(v___x_3139_, 0, v_moduleRef_3131_);
v___x_3140_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v___x_3139_, v_target_3132_, v_a_3134_, v_a_3135_, v_a_3136_, v_a_3137_);
if (lean_obj_tag(v___x_3140_) == 0)
{
lean_object* v_a_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; size_t v_sz_3146_; size_t v___x_3147_; lean_object* v___x_3148_; 
v_a_3141_ = lean_ctor_get(v___x_3140_, 0);
lean_inc(v_a_3141_);
lean_dec_ref_known(v___x_3140_, 1);
v___x_3142_ = lean_unsigned_to_nat(0u);
v___x_3143_ = lean_array_get_size(v_a_3141_);
v___x_3144_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0(v_a_3141_, v___x_3142_, v___x_3143_);
v___x_3145_ = lean_obj_once(&l_Lean_Meta_Rewrites_rewriteCandidates___closed__2, &l_Lean_Meta_Rewrites_rewriteCandidates___closed__2_once, _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__2);
v_sz_3146_ = lean_array_size(v___x_3144_);
v___x_3147_ = ((size_t)0ULL);
v___x_3148_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg(v_forbidden_3133_, v___x_3144_, v_sz_3146_, v___x_3147_, v___x_3145_);
lean_dec_ref(v___x_3144_);
if (lean_obj_tag(v___x_3148_) == 0)
{
lean_object* v_a_3149_; lean_object* v___x_3151_; uint8_t v_isShared_3152_; uint8_t v_isSharedCheck_3192_; 
v_a_3149_ = lean_ctor_get(v___x_3148_, 0);
v_isSharedCheck_3192_ = !lean_is_exclusive(v___x_3148_);
if (v_isSharedCheck_3192_ == 0)
{
v___x_3151_ = v___x_3148_;
v_isShared_3152_ = v_isSharedCheck_3192_;
goto v_resetjp_3150_;
}
else
{
lean_inc(v_a_3149_);
lean_dec(v___x_3148_);
v___x_3151_ = lean_box(0);
v_isShared_3152_ = v_isSharedCheck_3192_;
goto v_resetjp_3150_;
}
v_resetjp_3150_:
{
lean_object* v_snd_3153_; lean_object* v_snd_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3190_; 
v_snd_3153_ = lean_ctor_get(v_a_3149_, 1);
lean_inc(v_snd_3153_);
lean_dec(v_a_3149_);
v_snd_3154_ = lean_ctor_get(v_snd_3153_, 1);
v_isSharedCheck_3190_ = !lean_is_exclusive(v_snd_3153_);
if (v_isSharedCheck_3190_ == 0)
{
lean_object* v_unused_3191_; 
v_unused_3191_ = lean_ctor_get(v_snd_3153_, 0);
lean_dec(v_unused_3191_);
v___x_3156_ = v_snd_3153_;
v_isShared_3157_ = v_isSharedCheck_3190_;
goto v_resetjp_3155_;
}
else
{
lean_inc(v_snd_3154_);
lean_dec(v_snd_3153_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3190_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
lean_object* v_options_3167_; uint8_t v_hasTrace_3168_; 
v_options_3167_ = lean_ctor_get(v_a_3136_, 2);
v_hasTrace_3168_ = lean_ctor_get_uint8(v_options_3167_, sizeof(void*)*1);
if (v_hasTrace_3168_ == 0)
{
lean_del_object(v___x_3156_);
goto v___jp_3158_;
}
else
{
lean_object* v_inheritedTraceOptions_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; uint8_t v___x_3172_; 
v_inheritedTraceOptions_3169_ = lean_ctor_get(v_a_3136_, 13);
v___x_3170_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_));
v___x_3171_ = lean_obj_once(&l_Lean_Meta_Rewrites_rewriteCandidates___closed__3, &l_Lean_Meta_Rewrites_rewriteCandidates___closed__3_once, _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__3);
v___x_3172_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3169_, v_options_3167_, v___x_3171_);
if (v___x_3172_ == 0)
{
lean_del_object(v___x_3156_);
goto v___jp_3158_;
}
else
{
lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3179_; 
v___x_3173_ = lean_obj_once(&l_Lean_Meta_Rewrites_rewriteCandidates___closed__5, &l_Lean_Meta_Rewrites_rewriteCandidates___closed__5_once, _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__5);
lean_inc(v_snd_3154_);
v___x_3174_ = lean_array_to_list(v_snd_3154_);
v___x_3175_ = lean_box(0);
v___x_3176_ = l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4(v___x_3174_, v___x_3175_);
v___x_3177_ = l_Lean_MessageData_ofList(v___x_3176_);
if (v_isShared_3157_ == 0)
{
lean_ctor_set_tag(v___x_3156_, 7);
lean_ctor_set(v___x_3156_, 1, v___x_3177_);
lean_ctor_set(v___x_3156_, 0, v___x_3173_);
v___x_3179_ = v___x_3156_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v___x_3173_);
lean_ctor_set(v_reuseFailAlloc_3189_, 1, v___x_3177_);
v___x_3179_ = v_reuseFailAlloc_3189_;
goto v_reusejp_3178_;
}
v_reusejp_3178_:
{
lean_object* v___x_3180_; 
v___x_3180_ = l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2(v___x_3170_, v___x_3179_, v_a_3134_, v_a_3135_, v_a_3136_, v_a_3137_);
if (lean_obj_tag(v___x_3180_) == 0)
{
lean_dec_ref_known(v___x_3180_, 1);
goto v___jp_3158_;
}
else
{
lean_object* v_a_3181_; lean_object* v___x_3183_; uint8_t v_isShared_3184_; uint8_t v_isSharedCheck_3188_; 
lean_dec(v_snd_3154_);
lean_del_object(v___x_3151_);
lean_dec_ref(v_hyps_3130_);
v_a_3181_ = lean_ctor_get(v___x_3180_, 0);
v_isSharedCheck_3188_ = !lean_is_exclusive(v___x_3180_);
if (v_isSharedCheck_3188_ == 0)
{
v___x_3183_ = v___x_3180_;
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
else
{
lean_inc(v_a_3181_);
lean_dec(v___x_3180_);
v___x_3183_ = lean_box(0);
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
v_resetjp_3182_:
{
lean_object* v___x_3186_; 
if (v_isShared_3184_ == 0)
{
v___x_3186_ = v___x_3183_;
goto v_reusejp_3185_;
}
else
{
lean_object* v_reuseFailAlloc_3187_; 
v_reuseFailAlloc_3187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3187_, 0, v_a_3181_);
v___x_3186_ = v_reuseFailAlloc_3187_;
goto v_reusejp_3185_;
}
v_reusejp_3185_:
{
return v___x_3186_;
}
}
}
}
}
}
v___jp_3158_:
{
size_t v_sz_3159_; lean_object* v___x_3160_; size_t v_sz_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3165_; 
v_sz_3159_ = lean_array_size(v_hyps_3130_);
v___x_3160_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__2(v_sz_3159_, v___x_3147_, v_hyps_3130_);
v_sz_3161_ = lean_array_size(v_snd_3154_);
v___x_3162_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__3(v_sz_3161_, v___x_3147_, v_snd_3154_);
v___x_3163_ = l_Array_append___redArg(v___x_3160_, v___x_3162_);
lean_dec_ref(v___x_3162_);
if (v_isShared_3152_ == 0)
{
lean_ctor_set(v___x_3151_, 0, v___x_3163_);
v___x_3165_ = v___x_3151_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v___x_3163_);
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
}
else
{
lean_object* v_a_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3200_; 
lean_dec_ref(v_hyps_3130_);
v_a_3193_ = lean_ctor_get(v___x_3148_, 0);
v_isSharedCheck_3200_ = !lean_is_exclusive(v___x_3148_);
if (v_isSharedCheck_3200_ == 0)
{
v___x_3195_ = v___x_3148_;
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_a_3193_);
lean_dec(v___x_3148_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v___x_3198_; 
if (v_isShared_3196_ == 0)
{
v___x_3198_ = v___x_3195_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v_a_3193_);
v___x_3198_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
return v___x_3198_;
}
}
}
}
else
{
lean_object* v_a_3201_; lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3208_; 
lean_dec_ref(v_hyps_3130_);
v_a_3201_ = lean_ctor_get(v___x_3140_, 0);
v_isSharedCheck_3208_ = !lean_is_exclusive(v___x_3140_);
if (v_isSharedCheck_3208_ == 0)
{
v___x_3203_ = v___x_3140_;
v_isShared_3204_ = v_isSharedCheck_3208_;
goto v_resetjp_3202_;
}
else
{
lean_inc(v_a_3201_);
lean_dec(v___x_3140_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3208_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
lean_object* v___x_3206_; 
if (v_isShared_3204_ == 0)
{
v___x_3206_ = v___x_3203_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v_a_3201_);
v___x_3206_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
return v___x_3206_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rewriteCandidates___boxed(lean_object* v_hyps_3209_, lean_object* v_moduleRef_3210_, lean_object* v_target_3211_, lean_object* v_forbidden_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_, lean_object* v_a_3215_, lean_object* v_a_3216_, lean_object* v_a_3217_){
_start:
{
lean_object* v_res_3218_; 
v_res_3218_ = l_Lean_Meta_Rewrites_rewriteCandidates(v_hyps_3209_, v_moduleRef_3210_, v_target_3211_, v_forbidden_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_);
lean_dec(v_a_3216_);
lean_dec_ref(v_a_3215_);
lean_dec(v_a_3214_);
lean_dec_ref(v_a_3213_);
lean_dec(v_forbidden_3212_);
return v_res_3218_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1(lean_object* v_forbidden_3219_, lean_object* v_as_3220_, size_t v_sz_3221_, size_t v_i_3222_, lean_object* v_b_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_){
_start:
{
lean_object* v___x_3229_; 
v___x_3229_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg(v_forbidden_3219_, v_as_3220_, v_sz_3221_, v_i_3222_, v_b_3223_);
return v___x_3229_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___boxed(lean_object* v_forbidden_3230_, lean_object* v_as_3231_, lean_object* v_sz_3232_, lean_object* v_i_3233_, lean_object* v_b_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_){
_start:
{
size_t v_sz_boxed_3240_; size_t v_i_boxed_3241_; lean_object* v_res_3242_; 
v_sz_boxed_3240_ = lean_unbox_usize(v_sz_3232_);
lean_dec(v_sz_3232_);
v_i_boxed_3241_ = lean_unbox_usize(v_i_3233_);
lean_dec(v_i_3233_);
v_res_3242_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1(v_forbidden_3230_, v_as_3231_, v_sz_boxed_3240_, v_i_boxed_3241_, v_b_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_);
lean_dec(v___y_3238_);
lean_dec_ref(v___y_3237_);
lean_dec(v___y_3236_);
lean_dec_ref(v___y_3235_);
lean_dec_ref(v_as_3231_);
lean_dec(v_forbidden_3230_);
return v_res_3242_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0(lean_object* v_xs_3243_, lean_object* v_j_3244_, lean_object* v_h_3245_){
_start:
{
lean_object* v___x_3246_; 
v___x_3246_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0___redArg(v_xs_3243_, v_j_3244_);
return v___x_3246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_newGoal(lean_object* v_r_3247_){
_start:
{
uint8_t v_rfl_x3f_3248_; 
v_rfl_x3f_3248_ = lean_ctor_get_uint8(v_r_3247_, sizeof(void*)*4 + 1);
if (v_rfl_x3f_3248_ == 0)
{
lean_object* v_result_3249_; lean_object* v_eNew_3250_; lean_object* v___x_3251_; 
v_result_3249_ = lean_ctor_get(v_r_3247_, 2);
v_eNew_3250_ = lean_ctor_get(v_result_3249_, 0);
lean_inc_ref(v_eNew_3250_);
v___x_3251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3251_, 0, v_eNew_3250_);
return v___x_3251_;
}
else
{
lean_object* v___x_3252_; 
v___x_3252_ = lean_box(0);
return v___x_3252_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_newGoal___boxed(lean_object* v_r_3253_){
_start:
{
lean_object* v_res_3254_; 
v_res_3254_ = l_Lean_Meta_Rewrites_RewriteResult_newGoal(v_r_3253_);
lean_dec_ref(v_r_3253_);
return v_res_3254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0(lean_object* v_x_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_){
_start:
{
lean_object* v___x_3265_; 
lean_inc(v___y_3259_);
lean_inc_ref(v___y_3258_);
lean_inc(v___y_3257_);
lean_inc_ref(v___y_3256_);
v___x_3265_ = lean_apply_9(v_x_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_, v___y_3262_, v___y_3263_, lean_box(0));
return v___x_3265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0___boxed(lean_object* v_x_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_){
_start:
{
lean_object* v_res_3276_; 
v_res_3276_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0(v_x_3266_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_);
lean_dec(v___y_3270_);
lean_dec_ref(v___y_3269_);
lean_dec(v___y_3268_);
lean_dec_ref(v___y_3267_);
return v_res_3276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg(lean_object* v_mctx_3277_, lean_object* v_x_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_){
_start:
{
lean_object* v___f_3288_; lean_object* v___x_3289_; 
lean_inc(v___y_3282_);
lean_inc_ref(v___y_3281_);
lean_inc(v___y_3280_);
lean_inc_ref(v___y_3279_);
v___f_3288_ = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3288_, 0, v_x_3278_);
lean_closure_set(v___f_3288_, 1, v___y_3279_);
lean_closure_set(v___f_3288_, 2, v___y_3280_);
lean_closure_set(v___f_3288_, 3, v___y_3281_);
lean_closure_set(v___f_3288_, 4, v___y_3282_);
v___x_3289_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp(lean_box(0), v_mctx_3277_, v___f_3288_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_);
if (lean_obj_tag(v___x_3289_) == 0)
{
return v___x_3289_;
}
else
{
lean_object* v_a_3290_; lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3297_; 
v_a_3290_ = lean_ctor_get(v___x_3289_, 0);
v_isSharedCheck_3297_ = !lean_is_exclusive(v___x_3289_);
if (v_isSharedCheck_3297_ == 0)
{
v___x_3292_ = v___x_3289_;
v_isShared_3293_ = v_isSharedCheck_3297_;
goto v_resetjp_3291_;
}
else
{
lean_inc(v_a_3290_);
lean_dec(v___x_3289_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3297_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
lean_object* v___x_3295_; 
if (v_isShared_3293_ == 0)
{
v___x_3295_ = v___x_3292_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3296_; 
v_reuseFailAlloc_3296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3296_, 0, v_a_3290_);
v___x_3295_ = v_reuseFailAlloc_3296_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
return v___x_3295_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___boxed(lean_object* v_mctx_3298_, lean_object* v_x_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_){
_start:
{
lean_object* v_res_3309_; 
v_res_3309_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg(v_mctx_3298_, v_x_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_);
lean_dec(v___y_3307_);
lean_dec_ref(v___y_3306_);
lean_dec(v___y_3305_);
lean_dec_ref(v___y_3304_);
lean_dec(v___y_3303_);
lean_dec_ref(v___y_3302_);
lean_dec(v___y_3301_);
lean_dec_ref(v___y_3300_);
return v_res_3309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0(lean_object* v_00_u03b1_3310_, lean_object* v_mctx_3311_, lean_object* v_x_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_){
_start:
{
lean_object* v___x_3322_; 
v___x_3322_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg(v_mctx_3311_, v_x_3312_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_);
return v___x_3322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___boxed(lean_object* v_00_u03b1_3323_, lean_object* v_mctx_3324_, lean_object* v_x_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_){
_start:
{
lean_object* v_res_3335_; 
v_res_3335_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0(v_00_u03b1_3323_, v_mctx_3324_, v_x_3325_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_);
lean_dec(v___y_3333_);
lean_dec_ref(v___y_3332_);
lean_dec(v___y_3331_);
lean_dec_ref(v___y_3330_);
lean_dec(v___y_3329_);
lean_dec_ref(v___y_3328_);
lean_dec(v___y_3327_);
lean_dec_ref(v___y_3326_);
return v_res_3335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0(lean_object* v_expr_3336_, uint8_t v_symm_3337_, lean_object* v_r_3338_, lean_object* v_ref_3339_, lean_object* v_checkState_x3f_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_){
_start:
{
lean_object* v___x_3350_; 
v___x_3350_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_3342_, v___y_3344_, v___y_3346_, v___y_3348_);
if (lean_obj_tag(v___x_3350_) == 0)
{
lean_object* v_a_3351_; lean_object* v_ref_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___y_3362_; 
v_a_3351_ = lean_ctor_get(v___x_3350_, 0);
lean_inc(v_a_3351_);
lean_dec_ref_known(v___x_3350_, 1);
v_ref_3352_ = lean_ctor_get(v___y_3347_, 5);
v___x_3353_ = lean_box(v_symm_3337_);
v___x_3354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3354_, 0, v_expr_3336_);
lean_ctor_set(v___x_3354_, 1, v___x_3353_);
v___x_3355_ = lean_box(0);
v___x_3356_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3356_, 0, v___x_3354_);
lean_ctor_set(v___x_3356_, 1, v___x_3355_);
v___x_3357_ = l_Lean_Meta_Rewrites_RewriteResult_newGoal(v_r_3338_);
v___x_3358_ = l_Lean_Option_toLOption___redArg(v___x_3357_);
v___x_3359_ = lean_box(0);
lean_inc(v_ref_3352_);
v___x_3360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3360_, 0, v_ref_3352_);
if (lean_obj_tag(v_checkState_x3f_3340_) == 0)
{
v___y_3362_ = v_a_3351_;
goto v___jp_3361_;
}
else
{
lean_object* v_val_3365_; 
lean_dec(v_a_3351_);
v_val_3365_ = lean_ctor_get(v_checkState_x3f_3340_, 0);
lean_inc(v_val_3365_);
lean_dec_ref_known(v_checkState_x3f_3340_, 1);
v___y_3362_ = v_val_3365_;
goto v___jp_3361_;
}
v___jp_3361_:
{
lean_object* v___x_3363_; lean_object* v___x_3364_; 
v___x_3363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3363_, 0, v___y_3362_);
v___x_3364_ = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion(v_ref_3339_, v___x_3356_, v___x_3358_, v___x_3359_, v___x_3360_, v___x_3363_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_);
return v___x_3364_;
}
}
else
{
lean_object* v_a_3366_; lean_object* v___x_3368_; uint8_t v_isShared_3369_; uint8_t v_isSharedCheck_3373_; 
lean_dec(v_checkState_x3f_3340_);
lean_dec(v_ref_3339_);
lean_dec_ref(v_expr_3336_);
v_a_3366_ = lean_ctor_get(v___x_3350_, 0);
v_isSharedCheck_3373_ = !lean_is_exclusive(v___x_3350_);
if (v_isSharedCheck_3373_ == 0)
{
v___x_3368_ = v___x_3350_;
v_isShared_3369_ = v_isSharedCheck_3373_;
goto v_resetjp_3367_;
}
else
{
lean_inc(v_a_3366_);
lean_dec(v___x_3350_);
v___x_3368_ = lean_box(0);
v_isShared_3369_ = v_isSharedCheck_3373_;
goto v_resetjp_3367_;
}
v_resetjp_3367_:
{
lean_object* v___x_3371_; 
if (v_isShared_3369_ == 0)
{
v___x_3371_ = v___x_3368_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3372_; 
v_reuseFailAlloc_3372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3372_, 0, v_a_3366_);
v___x_3371_ = v_reuseFailAlloc_3372_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
return v___x_3371_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0___boxed(lean_object* v_expr_3374_, lean_object* v_symm_3375_, lean_object* v_r_3376_, lean_object* v_ref_3377_, lean_object* v_checkState_x3f_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_){
_start:
{
uint8_t v_symm_boxed_3388_; lean_object* v_res_3389_; 
v_symm_boxed_3388_ = lean_unbox(v_symm_3375_);
v_res_3389_ = l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0(v_expr_3374_, v_symm_boxed_3388_, v_r_3376_, v_ref_3377_, v_checkState_x3f_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_);
lean_dec(v___y_3386_);
lean_dec_ref(v___y_3385_);
lean_dec(v___y_3384_);
lean_dec_ref(v___y_3383_);
lean_dec(v___y_3382_);
lean_dec_ref(v___y_3381_);
lean_dec(v___y_3380_);
lean_dec_ref(v___y_3379_);
lean_dec_ref(v_r_3376_);
return v_res_3389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion(lean_object* v_ref_3390_, lean_object* v_r_3391_, lean_object* v_checkState_x3f_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_, lean_object* v_a_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_){
_start:
{
lean_object* v_expr_3402_; uint8_t v_symm_3403_; lean_object* v_mctx_3404_; lean_object* v___x_3405_; lean_object* v___f_3406_; lean_object* v___x_3407_; 
v_expr_3402_ = lean_ctor_get(v_r_3391_, 0);
lean_inc_ref(v_expr_3402_);
v_symm_3403_ = lean_ctor_get_uint8(v_r_3391_, sizeof(void*)*4);
v_mctx_3404_ = lean_ctor_get(v_r_3391_, 3);
lean_inc_ref(v_mctx_3404_);
v___x_3405_ = lean_box(v_symm_3403_);
v___f_3406_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0___boxed), 14, 5);
lean_closure_set(v___f_3406_, 0, v_expr_3402_);
lean_closure_set(v___f_3406_, 1, v___x_3405_);
lean_closure_set(v___f_3406_, 2, v_r_3391_);
lean_closure_set(v___f_3406_, 3, v_ref_3390_);
lean_closure_set(v___f_3406_, 4, v_checkState_x3f_3392_);
v___x_3407_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg(v_mctx_3404_, v___f_3406_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_);
return v___x_3407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___boxed(lean_object* v_ref_3408_, lean_object* v_r_3409_, lean_object* v_checkState_x3f_3410_, lean_object* v_a_3411_, lean_object* v_a_3412_, lean_object* v_a_3413_, lean_object* v_a_3414_, lean_object* v_a_3415_, lean_object* v_a_3416_, lean_object* v_a_3417_, lean_object* v_a_3418_, lean_object* v_a_3419_){
_start:
{
lean_object* v_res_3420_; 
v_res_3420_ = l_Lean_Meta_Rewrites_RewriteResult_addSuggestion(v_ref_3408_, v_r_3409_, v_checkState_x3f_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_, v_a_3418_);
lean_dec(v_a_3418_);
lean_dec_ref(v_a_3417_);
lean_dec(v_a_3416_);
lean_dec_ref(v_a_3415_);
lean_dec(v_a_3414_);
lean_dec_ref(v_a_3413_);
lean_dec(v_a_3412_);
lean_dec_ref(v_a_3411_);
return v_res_3420_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3___redArg(lean_object* v_a_3421_, lean_object* v_b_3422_, lean_object* v_x_3423_){
_start:
{
if (lean_obj_tag(v_x_3423_) == 0)
{
lean_dec(v_b_3422_);
lean_dec_ref(v_a_3421_);
return v_x_3423_;
}
else
{
lean_object* v_key_3424_; lean_object* v_value_3425_; lean_object* v_tail_3426_; lean_object* v___x_3428_; uint8_t v_isShared_3429_; uint8_t v_isSharedCheck_3438_; 
v_key_3424_ = lean_ctor_get(v_x_3423_, 0);
v_value_3425_ = lean_ctor_get(v_x_3423_, 1);
v_tail_3426_ = lean_ctor_get(v_x_3423_, 2);
v_isSharedCheck_3438_ = !lean_is_exclusive(v_x_3423_);
if (v_isSharedCheck_3438_ == 0)
{
v___x_3428_ = v_x_3423_;
v_isShared_3429_ = v_isSharedCheck_3438_;
goto v_resetjp_3427_;
}
else
{
lean_inc(v_tail_3426_);
lean_inc(v_value_3425_);
lean_inc(v_key_3424_);
lean_dec(v_x_3423_);
v___x_3428_ = lean_box(0);
v_isShared_3429_ = v_isSharedCheck_3438_;
goto v_resetjp_3427_;
}
v_resetjp_3427_:
{
uint8_t v___x_3430_; 
v___x_3430_ = lean_string_dec_eq(v_key_3424_, v_a_3421_);
if (v___x_3430_ == 0)
{
lean_object* v___x_3431_; lean_object* v___x_3433_; 
v___x_3431_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3___redArg(v_a_3421_, v_b_3422_, v_tail_3426_);
if (v_isShared_3429_ == 0)
{
lean_ctor_set(v___x_3428_, 2, v___x_3431_);
v___x_3433_ = v___x_3428_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v_key_3424_);
lean_ctor_set(v_reuseFailAlloc_3434_, 1, v_value_3425_);
lean_ctor_set(v_reuseFailAlloc_3434_, 2, v___x_3431_);
v___x_3433_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
return v___x_3433_;
}
}
else
{
lean_object* v___x_3436_; 
lean_dec(v_value_3425_);
lean_dec(v_key_3424_);
if (v_isShared_3429_ == 0)
{
lean_ctor_set(v___x_3428_, 1, v_b_3422_);
lean_ctor_set(v___x_3428_, 0, v_a_3421_);
v___x_3436_ = v___x_3428_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3437_; 
v_reuseFailAlloc_3437_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3437_, 0, v_a_3421_);
lean_ctor_set(v_reuseFailAlloc_3437_, 1, v_b_3422_);
lean_ctor_set(v_reuseFailAlloc_3437_, 2, v_tail_3426_);
v___x_3436_ = v_reuseFailAlloc_3437_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
return v___x_3436_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_x_3439_, lean_object* v_x_3440_){
_start:
{
if (lean_obj_tag(v_x_3440_) == 0)
{
return v_x_3439_;
}
else
{
lean_object* v_key_3441_; lean_object* v_value_3442_; lean_object* v_tail_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3466_; 
v_key_3441_ = lean_ctor_get(v_x_3440_, 0);
v_value_3442_ = lean_ctor_get(v_x_3440_, 1);
v_tail_3443_ = lean_ctor_get(v_x_3440_, 2);
v_isSharedCheck_3466_ = !lean_is_exclusive(v_x_3440_);
if (v_isSharedCheck_3466_ == 0)
{
v___x_3445_ = v_x_3440_;
v_isShared_3446_ = v_isSharedCheck_3466_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_tail_3443_);
lean_inc(v_value_3442_);
lean_inc(v_key_3441_);
lean_dec(v_x_3440_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3466_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
lean_object* v___x_3447_; uint64_t v___x_3448_; uint64_t v___x_3449_; uint64_t v___x_3450_; uint64_t v_fold_3451_; uint64_t v___x_3452_; uint64_t v___x_3453_; uint64_t v___x_3454_; size_t v___x_3455_; size_t v___x_3456_; size_t v___x_3457_; size_t v___x_3458_; size_t v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3462_; 
v___x_3447_ = lean_array_get_size(v_x_3439_);
v___x_3448_ = lean_string_hash(v_key_3441_);
v___x_3449_ = 32ULL;
v___x_3450_ = lean_uint64_shift_right(v___x_3448_, v___x_3449_);
v_fold_3451_ = lean_uint64_xor(v___x_3448_, v___x_3450_);
v___x_3452_ = 16ULL;
v___x_3453_ = lean_uint64_shift_right(v_fold_3451_, v___x_3452_);
v___x_3454_ = lean_uint64_xor(v_fold_3451_, v___x_3453_);
v___x_3455_ = lean_uint64_to_usize(v___x_3454_);
v___x_3456_ = lean_usize_of_nat(v___x_3447_);
v___x_3457_ = ((size_t)1ULL);
v___x_3458_ = lean_usize_sub(v___x_3456_, v___x_3457_);
v___x_3459_ = lean_usize_land(v___x_3455_, v___x_3458_);
v___x_3460_ = lean_array_uget_borrowed(v_x_3439_, v___x_3459_);
lean_inc(v___x_3460_);
if (v_isShared_3446_ == 0)
{
lean_ctor_set(v___x_3445_, 2, v___x_3460_);
v___x_3462_ = v___x_3445_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v_key_3441_);
lean_ctor_set(v_reuseFailAlloc_3465_, 1, v_value_3442_);
lean_ctor_set(v_reuseFailAlloc_3465_, 2, v___x_3460_);
v___x_3462_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
lean_object* v___x_3463_; 
v___x_3463_ = lean_array_uset(v_x_3439_, v___x_3459_, v___x_3462_);
v_x_3439_ = v___x_3463_;
v_x_3440_ = v_tail_3443_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3___redArg(lean_object* v_i_3467_, lean_object* v_source_3468_, lean_object* v_target_3469_){
_start:
{
lean_object* v___x_3470_; uint8_t v___x_3471_; 
v___x_3470_ = lean_array_get_size(v_source_3468_);
v___x_3471_ = lean_nat_dec_lt(v_i_3467_, v___x_3470_);
if (v___x_3471_ == 0)
{
lean_dec_ref(v_source_3468_);
lean_dec(v_i_3467_);
return v_target_3469_;
}
else
{
lean_object* v_es_3472_; lean_object* v___x_3473_; lean_object* v_source_3474_; lean_object* v_target_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; 
v_es_3472_ = lean_array_fget(v_source_3468_, v_i_3467_);
v___x_3473_ = lean_box(0);
v_source_3474_ = lean_array_fset(v_source_3468_, v_i_3467_, v___x_3473_);
v_target_3475_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3_spec__5___redArg(v_target_3469_, v_es_3472_);
v___x_3476_ = lean_unsigned_to_nat(1u);
v___x_3477_ = lean_nat_add(v_i_3467_, v___x_3476_);
lean_dec(v_i_3467_);
v_i_3467_ = v___x_3477_;
v_source_3468_ = v_source_3474_;
v_target_3469_ = v_target_3475_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2___redArg(lean_object* v_data_3479_){
_start:
{
lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v_nbuckets_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; 
v___x_3480_ = lean_array_get_size(v_data_3479_);
v___x_3481_ = lean_unsigned_to_nat(2u);
v_nbuckets_3482_ = lean_nat_mul(v___x_3480_, v___x_3481_);
v___x_3483_ = lean_unsigned_to_nat(0u);
v___x_3484_ = lean_box(0);
v___x_3485_ = lean_mk_array(v_nbuckets_3482_, v___x_3484_);
v___x_3486_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3___redArg(v___x_3483_, v_data_3479_, v___x_3485_);
return v___x_3486_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(lean_object* v_a_3487_, lean_object* v_x_3488_){
_start:
{
if (lean_obj_tag(v_x_3488_) == 0)
{
uint8_t v___x_3489_; 
v___x_3489_ = 0;
return v___x_3489_;
}
else
{
lean_object* v_key_3490_; lean_object* v_tail_3491_; uint8_t v___x_3492_; 
v_key_3490_ = lean_ctor_get(v_x_3488_, 0);
v_tail_3491_ = lean_ctor_get(v_x_3488_, 2);
v___x_3492_ = lean_string_dec_eq(v_key_3490_, v_a_3487_);
if (v___x_3492_ == 0)
{
v_x_3488_ = v_tail_3491_;
goto _start;
}
else
{
return v___x_3492_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg___boxed(lean_object* v_a_3494_, lean_object* v_x_3495_){
_start:
{
uint8_t v_res_3496_; lean_object* v_r_3497_; 
v_res_3496_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(v_a_3494_, v_x_3495_);
lean_dec(v_x_3495_);
lean_dec_ref(v_a_3494_);
v_r_3497_ = lean_box(v_res_3496_);
return v_r_3497_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1___redArg(lean_object* v_m_3498_, lean_object* v_a_3499_, lean_object* v_b_3500_){
_start:
{
lean_object* v_size_3501_; lean_object* v_buckets_3502_; lean_object* v___x_3504_; uint8_t v_isShared_3505_; uint8_t v_isSharedCheck_3545_; 
v_size_3501_ = lean_ctor_get(v_m_3498_, 0);
v_buckets_3502_ = lean_ctor_get(v_m_3498_, 1);
v_isSharedCheck_3545_ = !lean_is_exclusive(v_m_3498_);
if (v_isSharedCheck_3545_ == 0)
{
v___x_3504_ = v_m_3498_;
v_isShared_3505_ = v_isSharedCheck_3545_;
goto v_resetjp_3503_;
}
else
{
lean_inc(v_buckets_3502_);
lean_inc(v_size_3501_);
lean_dec(v_m_3498_);
v___x_3504_ = lean_box(0);
v_isShared_3505_ = v_isSharedCheck_3545_;
goto v_resetjp_3503_;
}
v_resetjp_3503_:
{
lean_object* v___x_3506_; uint64_t v___x_3507_; uint64_t v___x_3508_; uint64_t v___x_3509_; uint64_t v_fold_3510_; uint64_t v___x_3511_; uint64_t v___x_3512_; uint64_t v___x_3513_; size_t v___x_3514_; size_t v___x_3515_; size_t v___x_3516_; size_t v___x_3517_; size_t v___x_3518_; lean_object* v_bkt_3519_; uint8_t v___x_3520_; 
v___x_3506_ = lean_array_get_size(v_buckets_3502_);
v___x_3507_ = lean_string_hash(v_a_3499_);
v___x_3508_ = 32ULL;
v___x_3509_ = lean_uint64_shift_right(v___x_3507_, v___x_3508_);
v_fold_3510_ = lean_uint64_xor(v___x_3507_, v___x_3509_);
v___x_3511_ = 16ULL;
v___x_3512_ = lean_uint64_shift_right(v_fold_3510_, v___x_3511_);
v___x_3513_ = lean_uint64_xor(v_fold_3510_, v___x_3512_);
v___x_3514_ = lean_uint64_to_usize(v___x_3513_);
v___x_3515_ = lean_usize_of_nat(v___x_3506_);
v___x_3516_ = ((size_t)1ULL);
v___x_3517_ = lean_usize_sub(v___x_3515_, v___x_3516_);
v___x_3518_ = lean_usize_land(v___x_3514_, v___x_3517_);
v_bkt_3519_ = lean_array_uget_borrowed(v_buckets_3502_, v___x_3518_);
v___x_3520_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(v_a_3499_, v_bkt_3519_);
if (v___x_3520_ == 0)
{
lean_object* v___x_3521_; lean_object* v_size_x27_3522_; lean_object* v___x_3523_; lean_object* v_buckets_x27_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; uint8_t v___x_3530_; 
v___x_3521_ = lean_unsigned_to_nat(1u);
v_size_x27_3522_ = lean_nat_add(v_size_3501_, v___x_3521_);
lean_dec(v_size_3501_);
lean_inc(v_bkt_3519_);
v___x_3523_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3523_, 0, v_a_3499_);
lean_ctor_set(v___x_3523_, 1, v_b_3500_);
lean_ctor_set(v___x_3523_, 2, v_bkt_3519_);
v_buckets_x27_3524_ = lean_array_uset(v_buckets_3502_, v___x_3518_, v___x_3523_);
v___x_3525_ = lean_unsigned_to_nat(4u);
v___x_3526_ = lean_nat_mul(v_size_x27_3522_, v___x_3525_);
v___x_3527_ = lean_unsigned_to_nat(3u);
v___x_3528_ = lean_nat_div(v___x_3526_, v___x_3527_);
lean_dec(v___x_3526_);
v___x_3529_ = lean_array_get_size(v_buckets_x27_3524_);
v___x_3530_ = lean_nat_dec_le(v___x_3528_, v___x_3529_);
lean_dec(v___x_3528_);
if (v___x_3530_ == 0)
{
lean_object* v_val_3531_; lean_object* v___x_3533_; 
v_val_3531_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2___redArg(v_buckets_x27_3524_);
if (v_isShared_3505_ == 0)
{
lean_ctor_set(v___x_3504_, 1, v_val_3531_);
lean_ctor_set(v___x_3504_, 0, v_size_x27_3522_);
v___x_3533_ = v___x_3504_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v_size_x27_3522_);
lean_ctor_set(v_reuseFailAlloc_3534_, 1, v_val_3531_);
v___x_3533_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3532_;
}
v_reusejp_3532_:
{
return v___x_3533_;
}
}
else
{
lean_object* v___x_3536_; 
if (v_isShared_3505_ == 0)
{
lean_ctor_set(v___x_3504_, 1, v_buckets_x27_3524_);
lean_ctor_set(v___x_3504_, 0, v_size_x27_3522_);
v___x_3536_ = v___x_3504_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v_size_x27_3522_);
lean_ctor_set(v_reuseFailAlloc_3537_, 1, v_buckets_x27_3524_);
v___x_3536_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
return v___x_3536_;
}
}
}
else
{
lean_object* v___x_3538_; lean_object* v_buckets_x27_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3543_; 
lean_inc(v_bkt_3519_);
v___x_3538_ = lean_box(0);
v_buckets_x27_3539_ = lean_array_uset(v_buckets_3502_, v___x_3518_, v___x_3538_);
v___x_3540_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3___redArg(v_a_3499_, v_b_3500_, v_bkt_3519_);
v___x_3541_ = lean_array_uset(v_buckets_x27_3539_, v___x_3518_, v___x_3540_);
if (v_isShared_3505_ == 0)
{
lean_ctor_set(v___x_3504_, 1, v___x_3541_);
v___x_3543_ = v___x_3504_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v_size_3501_);
lean_ctor_set(v_reuseFailAlloc_3544_, 1, v___x_3541_);
v___x_3543_ = v_reuseFailAlloc_3544_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
return v___x_3543_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg(lean_object* v_m_3546_, lean_object* v_a_3547_){
_start:
{
lean_object* v_buckets_3548_; lean_object* v___x_3549_; uint64_t v___x_3550_; uint64_t v___x_3551_; uint64_t v___x_3552_; uint64_t v_fold_3553_; uint64_t v___x_3554_; uint64_t v___x_3555_; uint64_t v___x_3556_; size_t v___x_3557_; size_t v___x_3558_; size_t v___x_3559_; size_t v___x_3560_; size_t v___x_3561_; lean_object* v___x_3562_; uint8_t v___x_3563_; 
v_buckets_3548_ = lean_ctor_get(v_m_3546_, 1);
v___x_3549_ = lean_array_get_size(v_buckets_3548_);
v___x_3550_ = lean_string_hash(v_a_3547_);
v___x_3551_ = 32ULL;
v___x_3552_ = lean_uint64_shift_right(v___x_3550_, v___x_3551_);
v_fold_3553_ = lean_uint64_xor(v___x_3550_, v___x_3552_);
v___x_3554_ = 16ULL;
v___x_3555_ = lean_uint64_shift_right(v_fold_3553_, v___x_3554_);
v___x_3556_ = lean_uint64_xor(v_fold_3553_, v___x_3555_);
v___x_3557_ = lean_uint64_to_usize(v___x_3556_);
v___x_3558_ = lean_usize_of_nat(v___x_3549_);
v___x_3559_ = ((size_t)1ULL);
v___x_3560_ = lean_usize_sub(v___x_3558_, v___x_3559_);
v___x_3561_ = lean_usize_land(v___x_3557_, v___x_3560_);
v___x_3562_ = lean_array_uget_borrowed(v_buckets_3548_, v___x_3561_);
v___x_3563_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(v_a_3547_, v___x_3562_);
return v___x_3563_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg___boxed(lean_object* v_m_3564_, lean_object* v_a_3565_){
_start:
{
uint8_t v_res_3566_; lean_object* v_r_3567_; 
v_res_3566_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg(v_m_3564_, v_a_3565_);
lean_dec_ref(v_a_3565_);
lean_dec_ref(v_m_3564_);
v_r_3567_ = lean_box(v_res_3566_);
return v_r_3567_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg(lean_object* v_cfg_3568_, lean_object* v_as_x27_3569_, lean_object* v_b_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_){
_start:
{
if (lean_obj_tag(v_as_x27_3569_) == 0)
{
lean_object* v___x_3576_; 
lean_dec_ref(v_cfg_3568_);
v___x_3576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3576_, 0, v_b_3570_);
return v___x_3576_;
}
else
{
lean_object* v_head_3577_; lean_object* v_snd_3578_; lean_object* v_tail_3579_; lean_object* v_fst_3580_; lean_object* v_fst_3581_; lean_object* v_snd_3582_; lean_object* v___x_3583_; 
v_head_3577_ = lean_ctor_get(v_as_x27_3569_, 0);
v_snd_3578_ = lean_ctor_get(v_head_3577_, 1);
v_tail_3579_ = lean_ctor_get(v_as_x27_3569_, 1);
v_fst_3580_ = lean_ctor_get(v_head_3577_, 0);
v_fst_3581_ = lean_ctor_get(v_snd_3578_, 0);
v_snd_3582_ = lean_ctor_get(v_snd_3578_, 1);
v___x_3583_ = l_Lean_getRemainingHeartbeats___redArg(v___y_3573_);
if (lean_obj_tag(v___x_3583_) == 0)
{
lean_object* v_snd_3584_; lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3728_; 
v_snd_3584_ = lean_ctor_get(v_b_3570_, 1);
v_isSharedCheck_3728_ = !lean_is_exclusive(v_b_3570_);
if (v_isSharedCheck_3728_ == 0)
{
lean_object* v_unused_3729_; 
v_unused_3729_ = lean_ctor_get(v_b_3570_, 0);
lean_dec(v_unused_3729_);
v___x_3586_ = v_b_3570_;
v_isShared_3587_ = v_isSharedCheck_3728_;
goto v_resetjp_3585_;
}
else
{
lean_inc(v_snd_3584_);
lean_dec(v_b_3570_);
v___x_3586_ = lean_box(0);
v_isShared_3587_ = v_isSharedCheck_3728_;
goto v_resetjp_3585_;
}
v_resetjp_3585_:
{
lean_object* v_a_3588_; lean_object* v___x_3590_; uint8_t v_isShared_3591_; uint8_t v_isSharedCheck_3727_; 
v_a_3588_ = lean_ctor_get(v___x_3583_, 0);
v_isSharedCheck_3727_ = !lean_is_exclusive(v___x_3583_);
if (v_isSharedCheck_3727_ == 0)
{
v___x_3590_ = v___x_3583_;
v_isShared_3591_ = v_isSharedCheck_3727_;
goto v_resetjp_3589_;
}
else
{
lean_inc(v_a_3588_);
lean_dec(v___x_3583_);
v___x_3590_ = lean_box(0);
v_isShared_3591_ = v_isSharedCheck_3727_;
goto v_resetjp_3589_;
}
v_resetjp_3589_:
{
lean_object* v_fst_3592_; lean_object* v_snd_3593_; lean_object* v___x_3595_; uint8_t v_isShared_3596_; uint8_t v_isSharedCheck_3726_; 
v_fst_3592_ = lean_ctor_get(v_snd_3584_, 0);
v_snd_3593_ = lean_ctor_get(v_snd_3584_, 1);
v_isSharedCheck_3726_ = !lean_is_exclusive(v_snd_3584_);
if (v_isSharedCheck_3726_ == 0)
{
v___x_3595_ = v_snd_3584_;
v_isShared_3596_ = v_isSharedCheck_3726_;
goto v_resetjp_3594_;
}
else
{
lean_inc(v_snd_3593_);
lean_inc(v_fst_3592_);
lean_dec(v_snd_3584_);
v___x_3595_ = lean_box(0);
v_isShared_3596_ = v_isSharedCheck_3726_;
goto v_resetjp_3594_;
}
v_resetjp_3594_:
{
uint8_t v_stopAtRfl_3597_; lean_object* v_max_3598_; lean_object* v_minHeartbeats_3599_; lean_object* v_goal_3600_; lean_object* v_target_3601_; uint8_t v_side_3602_; lean_object* v_mctx_3603_; uint8_t v___x_3604_; 
v_stopAtRfl_3597_ = lean_ctor_get_uint8(v_cfg_3568_, sizeof(void*)*5);
v_max_3598_ = lean_ctor_get(v_cfg_3568_, 0);
v_minHeartbeats_3599_ = lean_ctor_get(v_cfg_3568_, 1);
v_goal_3600_ = lean_ctor_get(v_cfg_3568_, 2);
v_target_3601_ = lean_ctor_get(v_cfg_3568_, 3);
v_side_3602_ = lean_ctor_get_uint8(v_cfg_3568_, sizeof(void*)*5 + 1);
v_mctx_3603_ = lean_ctor_get(v_cfg_3568_, 4);
v___x_3604_ = lean_nat_dec_lt(v_a_3588_, v_minHeartbeats_3599_);
lean_dec(v_a_3588_);
if (v___x_3604_ == 0)
{
lean_object* v___x_3605_; uint8_t v___x_3606_; 
v___x_3605_ = lean_array_get_size(v_snd_3593_);
v___x_3606_ = lean_nat_dec_le(v_max_3598_, v___x_3605_);
if (v___x_3606_ == 0)
{
lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; 
lean_del_object(v___x_3590_);
v___x_3607_ = lean_box(v_side_3602_);
lean_inc(v_snd_3582_);
lean_inc(v_fst_3581_);
lean_inc(v_fst_3580_);
lean_inc_ref(v_target_3601_);
lean_inc(v_goal_3600_);
lean_inc_ref_n(v_mctx_3603_, 2);
v___x_3608_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_rwLemma___boxed), 12, 7);
lean_closure_set(v___x_3608_, 0, v_mctx_3603_);
lean_closure_set(v___x_3608_, 1, v_goal_3600_);
lean_closure_set(v___x_3608_, 2, v_target_3601_);
lean_closure_set(v___x_3608_, 3, v___x_3607_);
lean_closure_set(v___x_3608_, 4, v_fst_3580_);
lean_closure_set(v___x_3608_, 5, v_fst_3581_);
lean_closure_set(v___x_3608_, 6, v_snd_3582_);
v___x_3609_ = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___boxed), 8, 3);
lean_closure_set(v___x_3609_, 0, lean_box(0));
lean_closure_set(v___x_3609_, 1, v_mctx_3603_);
lean_closure_set(v___x_3609_, 2, v___x_3608_);
v___x_3610_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v___x_3609_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_);
if (lean_obj_tag(v___x_3610_) == 0)
{
lean_object* v_a_3611_; lean_object* v___x_3612_; 
v_a_3611_ = lean_ctor_get(v___x_3610_, 0);
lean_inc(v_a_3611_);
lean_dec_ref_known(v___x_3610_, 1);
v___x_3612_ = lean_box(0);
if (lean_obj_tag(v_a_3611_) == 0)
{
lean_object* v___x_3614_; 
if (v_isShared_3596_ == 0)
{
v___x_3614_ = v___x_3595_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v_fst_3592_);
lean_ctor_set(v_reuseFailAlloc_3619_, 1, v_snd_3593_);
v___x_3614_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
lean_object* v___x_3616_; 
if (v_isShared_3587_ == 0)
{
lean_ctor_set(v___x_3586_, 1, v___x_3614_);
lean_ctor_set(v___x_3586_, 0, v___x_3612_);
v___x_3616_ = v___x_3586_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v___x_3612_);
lean_ctor_set(v_reuseFailAlloc_3618_, 1, v___x_3614_);
v___x_3616_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
v_as_x27_3569_ = v_tail_3579_;
v_b_3570_ = v___x_3616_;
goto _start;
}
}
}
else
{
lean_object* v_val_3620_; lean_object* v___x_3622_; uint8_t v_isShared_3623_; uint8_t v_isSharedCheck_3697_; 
v_val_3620_ = lean_ctor_get(v_a_3611_, 0);
v_isSharedCheck_3697_ = !lean_is_exclusive(v_a_3611_);
if (v_isSharedCheck_3697_ == 0)
{
v___x_3622_ = v_a_3611_;
v_isShared_3623_ = v_isSharedCheck_3697_;
goto v_resetjp_3621_;
}
else
{
lean_inc(v_val_3620_);
lean_dec(v_a_3611_);
v___x_3622_ = lean_box(0);
v_isShared_3623_ = v_isSharedCheck_3697_;
goto v_resetjp_3621_;
}
v_resetjp_3621_:
{
lean_object* v_result_3624_; lean_object* v_mctx_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; 
v_result_3624_ = lean_ctor_get(v_val_3620_, 2);
v_mctx_3625_ = lean_ctor_get(v_val_3620_, 3);
lean_inc(v_val_3620_);
v___x_3626_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult___boxed), 6, 1);
lean_closure_set(v___x_3626_, 0, v_val_3620_);
lean_inc_ref(v_mctx_3625_);
v___x_3627_ = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___boxed), 8, 3);
lean_closure_set(v___x_3627_, 0, lean_box(0));
lean_closure_set(v___x_3627_, 1, v_mctx_3625_);
lean_closure_set(v___x_3627_, 2, v___x_3626_);
v___x_3628_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v___x_3627_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_);
if (lean_obj_tag(v___x_3628_) == 0)
{
lean_object* v_a_3629_; uint8_t v___x_3630_; 
v_a_3629_ = lean_ctor_get(v___x_3628_, 0);
lean_inc(v_a_3629_);
lean_dec_ref_known(v___x_3628_, 1);
v___x_3630_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg(v_fst_3592_, v_a_3629_);
if (v___x_3630_ == 0)
{
lean_object* v_eNew_3631_; lean_object* v___x_3632_; 
v_eNew_3631_ = lean_ctor_get(v_result_3624_, 0);
lean_inc_ref(v_eNew_3631_);
lean_inc_ref(v_mctx_3625_);
v___x_3632_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(v_mctx_3625_, v_eNew_3631_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_);
if (lean_obj_tag(v___x_3632_) == 0)
{
if (v_stopAtRfl_3597_ == 0)
{
lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3637_; 
lean_dec_ref_known(v___x_3632_, 1);
lean_del_object(v___x_3622_);
v___x_3633_ = lean_box(0);
v___x_3634_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1___redArg(v_fst_3592_, v_a_3629_, v___x_3633_);
v___x_3635_ = lean_array_push(v_snd_3593_, v_val_3620_);
if (v_isShared_3596_ == 0)
{
lean_ctor_set(v___x_3595_, 1, v___x_3635_);
lean_ctor_set(v___x_3595_, 0, v___x_3634_);
v___x_3637_ = v___x_3595_;
goto v_reusejp_3636_;
}
else
{
lean_object* v_reuseFailAlloc_3642_; 
v_reuseFailAlloc_3642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3642_, 0, v___x_3634_);
lean_ctor_set(v_reuseFailAlloc_3642_, 1, v___x_3635_);
v___x_3637_ = v_reuseFailAlloc_3642_;
goto v_reusejp_3636_;
}
v_reusejp_3636_:
{
lean_object* v___x_3639_; 
if (v_isShared_3587_ == 0)
{
lean_ctor_set(v___x_3586_, 1, v___x_3637_);
lean_ctor_set(v___x_3586_, 0, v___x_3612_);
v___x_3639_ = v___x_3586_;
goto v_reusejp_3638_;
}
else
{
lean_object* v_reuseFailAlloc_3641_; 
v_reuseFailAlloc_3641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3641_, 0, v___x_3612_);
lean_ctor_set(v_reuseFailAlloc_3641_, 1, v___x_3637_);
v___x_3639_ = v_reuseFailAlloc_3641_;
goto v_reusejp_3638_;
}
v_reusejp_3638_:
{
v_as_x27_3569_ = v_tail_3579_;
v_b_3570_ = v___x_3639_;
goto _start;
}
}
}
else
{
lean_object* v_a_3643_; lean_object* v___x_3645_; uint8_t v_isShared_3646_; uint8_t v_isSharedCheck_3673_; 
v_a_3643_ = lean_ctor_get(v___x_3632_, 0);
v_isSharedCheck_3673_ = !lean_is_exclusive(v___x_3632_);
if (v_isSharedCheck_3673_ == 0)
{
v___x_3645_ = v___x_3632_;
v_isShared_3646_ = v_isSharedCheck_3673_;
goto v_resetjp_3644_;
}
else
{
lean_inc(v_a_3643_);
lean_dec(v___x_3632_);
v___x_3645_ = lean_box(0);
v_isShared_3646_ = v_isSharedCheck_3673_;
goto v_resetjp_3644_;
}
v_resetjp_3644_:
{
uint8_t v___x_3647_; 
v___x_3647_ = lean_unbox(v_a_3643_);
lean_dec(v_a_3643_);
if (v___x_3647_ == 0)
{
lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3652_; 
lean_del_object(v___x_3645_);
lean_del_object(v___x_3622_);
v___x_3648_ = lean_box(0);
v___x_3649_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1___redArg(v_fst_3592_, v_a_3629_, v___x_3648_);
v___x_3650_ = lean_array_push(v_snd_3593_, v_val_3620_);
if (v_isShared_3596_ == 0)
{
lean_ctor_set(v___x_3595_, 1, v___x_3650_);
lean_ctor_set(v___x_3595_, 0, v___x_3649_);
v___x_3652_ = v___x_3595_;
goto v_reusejp_3651_;
}
else
{
lean_object* v_reuseFailAlloc_3657_; 
v_reuseFailAlloc_3657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3657_, 0, v___x_3649_);
lean_ctor_set(v_reuseFailAlloc_3657_, 1, v___x_3650_);
v___x_3652_ = v_reuseFailAlloc_3657_;
goto v_reusejp_3651_;
}
v_reusejp_3651_:
{
lean_object* v___x_3654_; 
if (v_isShared_3587_ == 0)
{
lean_ctor_set(v___x_3586_, 1, v___x_3652_);
lean_ctor_set(v___x_3586_, 0, v___x_3612_);
v___x_3654_ = v___x_3586_;
goto v_reusejp_3653_;
}
else
{
lean_object* v_reuseFailAlloc_3656_; 
v_reuseFailAlloc_3656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3656_, 0, v___x_3612_);
lean_ctor_set(v_reuseFailAlloc_3656_, 1, v___x_3652_);
v___x_3654_ = v_reuseFailAlloc_3656_;
goto v_reusejp_3653_;
}
v_reusejp_3653_:
{
v_as_x27_3569_ = v_tail_3579_;
v_b_3570_ = v___x_3654_;
goto _start;
}
}
}
else
{
lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3662_; 
lean_dec(v_a_3629_);
lean_dec_ref(v_cfg_3568_);
v___x_3658_ = lean_unsigned_to_nat(1u);
v___x_3659_ = lean_mk_empty_array_with_capacity(v___x_3658_);
v___x_3660_ = lean_array_push(v___x_3659_, v_val_3620_);
if (v_isShared_3623_ == 0)
{
lean_ctor_set(v___x_3622_, 0, v___x_3660_);
v___x_3662_ = v___x_3622_;
goto v_reusejp_3661_;
}
else
{
lean_object* v_reuseFailAlloc_3672_; 
v_reuseFailAlloc_3672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3672_, 0, v___x_3660_);
v___x_3662_ = v_reuseFailAlloc_3672_;
goto v_reusejp_3661_;
}
v_reusejp_3661_:
{
lean_object* v___x_3664_; 
if (v_isShared_3596_ == 0)
{
v___x_3664_ = v___x_3595_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3671_, 0, v_fst_3592_);
lean_ctor_set(v_reuseFailAlloc_3671_, 1, v_snd_3593_);
v___x_3664_ = v_reuseFailAlloc_3671_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
lean_object* v___x_3666_; 
if (v_isShared_3587_ == 0)
{
lean_ctor_set(v___x_3586_, 1, v___x_3664_);
lean_ctor_set(v___x_3586_, 0, v___x_3662_);
v___x_3666_ = v___x_3586_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v___x_3662_);
lean_ctor_set(v_reuseFailAlloc_3670_, 1, v___x_3664_);
v___x_3666_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
lean_object* v___x_3668_; 
if (v_isShared_3646_ == 0)
{
lean_ctor_set(v___x_3645_, 0, v___x_3666_);
v___x_3668_ = v___x_3645_;
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
return v___x_3668_;
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
lean_object* v_a_3674_; lean_object* v___x_3676_; uint8_t v_isShared_3677_; uint8_t v_isSharedCheck_3681_; 
lean_dec(v_a_3629_);
lean_del_object(v___x_3622_);
lean_dec(v_val_3620_);
lean_del_object(v___x_3595_);
lean_dec(v_snd_3593_);
lean_dec(v_fst_3592_);
lean_del_object(v___x_3586_);
lean_dec_ref(v_cfg_3568_);
v_a_3674_ = lean_ctor_get(v___x_3632_, 0);
v_isSharedCheck_3681_ = !lean_is_exclusive(v___x_3632_);
if (v_isSharedCheck_3681_ == 0)
{
v___x_3676_ = v___x_3632_;
v_isShared_3677_ = v_isSharedCheck_3681_;
goto v_resetjp_3675_;
}
else
{
lean_inc(v_a_3674_);
lean_dec(v___x_3632_);
v___x_3676_ = lean_box(0);
v_isShared_3677_ = v_isSharedCheck_3681_;
goto v_resetjp_3675_;
}
v_resetjp_3675_:
{
lean_object* v___x_3679_; 
if (v_isShared_3677_ == 0)
{
v___x_3679_ = v___x_3676_;
goto v_reusejp_3678_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v_a_3674_);
v___x_3679_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3678_;
}
v_reusejp_3678_:
{
return v___x_3679_;
}
}
}
}
else
{
lean_object* v___x_3683_; 
lean_dec(v_a_3629_);
lean_del_object(v___x_3622_);
lean_dec(v_val_3620_);
if (v_isShared_3596_ == 0)
{
v___x_3683_ = v___x_3595_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v_fst_3592_);
lean_ctor_set(v_reuseFailAlloc_3688_, 1, v_snd_3593_);
v___x_3683_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
lean_object* v___x_3685_; 
if (v_isShared_3587_ == 0)
{
lean_ctor_set(v___x_3586_, 1, v___x_3683_);
lean_ctor_set(v___x_3586_, 0, v___x_3612_);
v___x_3685_ = v___x_3586_;
goto v_reusejp_3684_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v___x_3612_);
lean_ctor_set(v_reuseFailAlloc_3687_, 1, v___x_3683_);
v___x_3685_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3684_;
}
v_reusejp_3684_:
{
v_as_x27_3569_ = v_tail_3579_;
v_b_3570_ = v___x_3685_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3689_; lean_object* v___x_3691_; uint8_t v_isShared_3692_; uint8_t v_isSharedCheck_3696_; 
lean_del_object(v___x_3622_);
lean_dec(v_val_3620_);
lean_del_object(v___x_3595_);
lean_dec(v_snd_3593_);
lean_dec(v_fst_3592_);
lean_del_object(v___x_3586_);
lean_dec_ref(v_cfg_3568_);
v_a_3689_ = lean_ctor_get(v___x_3628_, 0);
v_isSharedCheck_3696_ = !lean_is_exclusive(v___x_3628_);
if (v_isSharedCheck_3696_ == 0)
{
v___x_3691_ = v___x_3628_;
v_isShared_3692_ = v_isSharedCheck_3696_;
goto v_resetjp_3690_;
}
else
{
lean_inc(v_a_3689_);
lean_dec(v___x_3628_);
v___x_3691_ = lean_box(0);
v_isShared_3692_ = v_isSharedCheck_3696_;
goto v_resetjp_3690_;
}
v_resetjp_3690_:
{
lean_object* v___x_3694_; 
if (v_isShared_3692_ == 0)
{
v___x_3694_ = v___x_3691_;
goto v_reusejp_3693_;
}
else
{
lean_object* v_reuseFailAlloc_3695_; 
v_reuseFailAlloc_3695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3695_, 0, v_a_3689_);
v___x_3694_ = v_reuseFailAlloc_3695_;
goto v_reusejp_3693_;
}
v_reusejp_3693_:
{
return v___x_3694_;
}
}
}
}
}
}
else
{
lean_object* v_a_3698_; lean_object* v___x_3700_; uint8_t v_isShared_3701_; uint8_t v_isSharedCheck_3705_; 
lean_del_object(v___x_3595_);
lean_dec(v_snd_3593_);
lean_dec(v_fst_3592_);
lean_del_object(v___x_3586_);
lean_dec_ref(v_cfg_3568_);
v_a_3698_ = lean_ctor_get(v___x_3610_, 0);
v_isSharedCheck_3705_ = !lean_is_exclusive(v___x_3610_);
if (v_isSharedCheck_3705_ == 0)
{
v___x_3700_ = v___x_3610_;
v_isShared_3701_ = v_isSharedCheck_3705_;
goto v_resetjp_3699_;
}
else
{
lean_inc(v_a_3698_);
lean_dec(v___x_3610_);
v___x_3700_ = lean_box(0);
v_isShared_3701_ = v_isSharedCheck_3705_;
goto v_resetjp_3699_;
}
v_resetjp_3699_:
{
lean_object* v___x_3703_; 
if (v_isShared_3701_ == 0)
{
v___x_3703_ = v___x_3700_;
goto v_reusejp_3702_;
}
else
{
lean_object* v_reuseFailAlloc_3704_; 
v_reuseFailAlloc_3704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3704_, 0, v_a_3698_);
v___x_3703_ = v_reuseFailAlloc_3704_;
goto v_reusejp_3702_;
}
v_reusejp_3702_:
{
return v___x_3703_;
}
}
}
}
else
{
lean_object* v___x_3706_; lean_object* v___x_3708_; 
lean_dec_ref(v_cfg_3568_);
lean_inc(v_snd_3593_);
v___x_3706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3706_, 0, v_snd_3593_);
if (v_isShared_3596_ == 0)
{
v___x_3708_ = v___x_3595_;
goto v_reusejp_3707_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v_fst_3592_);
lean_ctor_set(v_reuseFailAlloc_3715_, 1, v_snd_3593_);
v___x_3708_ = v_reuseFailAlloc_3715_;
goto v_reusejp_3707_;
}
v_reusejp_3707_:
{
lean_object* v___x_3710_; 
if (v_isShared_3587_ == 0)
{
lean_ctor_set(v___x_3586_, 1, v___x_3708_);
lean_ctor_set(v___x_3586_, 0, v___x_3706_);
v___x_3710_ = v___x_3586_;
goto v_reusejp_3709_;
}
else
{
lean_object* v_reuseFailAlloc_3714_; 
v_reuseFailAlloc_3714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3714_, 0, v___x_3706_);
lean_ctor_set(v_reuseFailAlloc_3714_, 1, v___x_3708_);
v___x_3710_ = v_reuseFailAlloc_3714_;
goto v_reusejp_3709_;
}
v_reusejp_3709_:
{
lean_object* v___x_3712_; 
if (v_isShared_3591_ == 0)
{
lean_ctor_set(v___x_3590_, 0, v___x_3710_);
v___x_3712_ = v___x_3590_;
goto v_reusejp_3711_;
}
else
{
lean_object* v_reuseFailAlloc_3713_; 
v_reuseFailAlloc_3713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3713_, 0, v___x_3710_);
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
}
else
{
lean_object* v___x_3716_; lean_object* v___x_3718_; 
lean_dec_ref(v_cfg_3568_);
lean_inc(v_snd_3593_);
v___x_3716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3716_, 0, v_snd_3593_);
if (v_isShared_3596_ == 0)
{
v___x_3718_ = v___x_3595_;
goto v_reusejp_3717_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v_fst_3592_);
lean_ctor_set(v_reuseFailAlloc_3725_, 1, v_snd_3593_);
v___x_3718_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3717_;
}
v_reusejp_3717_:
{
lean_object* v___x_3720_; 
if (v_isShared_3587_ == 0)
{
lean_ctor_set(v___x_3586_, 1, v___x_3718_);
lean_ctor_set(v___x_3586_, 0, v___x_3716_);
v___x_3720_ = v___x_3586_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3724_; 
v_reuseFailAlloc_3724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3724_, 0, v___x_3716_);
lean_ctor_set(v_reuseFailAlloc_3724_, 1, v___x_3718_);
v___x_3720_ = v_reuseFailAlloc_3724_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
lean_object* v___x_3722_; 
if (v_isShared_3591_ == 0)
{
lean_ctor_set(v___x_3590_, 0, v___x_3720_);
v___x_3722_ = v___x_3590_;
goto v_reusejp_3721_;
}
else
{
lean_object* v_reuseFailAlloc_3723_; 
v_reuseFailAlloc_3723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3723_, 0, v___x_3720_);
v___x_3722_ = v_reuseFailAlloc_3723_;
goto v_reusejp_3721_;
}
v_reusejp_3721_:
{
return v___x_3722_;
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
lean_object* v_a_3730_; lean_object* v___x_3732_; uint8_t v_isShared_3733_; uint8_t v_isSharedCheck_3737_; 
lean_dec_ref(v_b_3570_);
lean_dec_ref(v_cfg_3568_);
v_a_3730_ = lean_ctor_get(v___x_3583_, 0);
v_isSharedCheck_3737_ = !lean_is_exclusive(v___x_3583_);
if (v_isSharedCheck_3737_ == 0)
{
v___x_3732_ = v___x_3583_;
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
else
{
lean_inc(v_a_3730_);
lean_dec(v___x_3583_);
v___x_3732_ = lean_box(0);
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
v_resetjp_3731_:
{
lean_object* v___x_3735_; 
if (v_isShared_3733_ == 0)
{
v___x_3735_ = v___x_3732_;
goto v_reusejp_3734_;
}
else
{
lean_object* v_reuseFailAlloc_3736_; 
v_reuseFailAlloc_3736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3736_, 0, v_a_3730_);
v___x_3735_ = v_reuseFailAlloc_3736_;
goto v_reusejp_3734_;
}
v_reusejp_3734_:
{
return v___x_3735_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg___boxed(lean_object* v_cfg_3738_, lean_object* v_as_x27_3739_, lean_object* v_b_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_){
_start:
{
lean_object* v_res_3746_; 
v_res_3746_ = l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg(v_cfg_3738_, v_as_x27_3739_, v_b_3740_, v___y_3741_, v___y_3742_, v___y_3743_, v___y_3744_);
lean_dec(v___y_3744_);
lean_dec_ref(v___y_3743_);
lean_dec(v___y_3742_);
lean_dec_ref(v___y_3741_);
lean_dec(v_as_x27_3739_);
return v_res_3746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_takeListAux(lean_object* v_cfg_3747_, lean_object* v_seen_3748_, lean_object* v_acc_3749_, lean_object* v_xs_3750_, lean_object* v_a_3751_, lean_object* v_a_3752_, lean_object* v_a_3753_, lean_object* v_a_3754_){
_start:
{
lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; 
v___x_3756_ = lean_box(0);
v___x_3757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3757_, 0, v_seen_3748_);
lean_ctor_set(v___x_3757_, 1, v_acc_3749_);
v___x_3758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3758_, 0, v___x_3756_);
lean_ctor_set(v___x_3758_, 1, v___x_3757_);
v___x_3759_ = l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg(v_cfg_3747_, v_xs_3750_, v___x_3758_, v_a_3751_, v_a_3752_, v_a_3753_, v_a_3754_);
if (lean_obj_tag(v___x_3759_) == 0)
{
lean_object* v_a_3760_; lean_object* v___x_3762_; uint8_t v_isShared_3763_; uint8_t v_isSharedCheck_3774_; 
v_a_3760_ = lean_ctor_get(v___x_3759_, 0);
v_isSharedCheck_3774_ = !lean_is_exclusive(v___x_3759_);
if (v_isSharedCheck_3774_ == 0)
{
v___x_3762_ = v___x_3759_;
v_isShared_3763_ = v_isSharedCheck_3774_;
goto v_resetjp_3761_;
}
else
{
lean_inc(v_a_3760_);
lean_dec(v___x_3759_);
v___x_3762_ = lean_box(0);
v_isShared_3763_ = v_isSharedCheck_3774_;
goto v_resetjp_3761_;
}
v_resetjp_3761_:
{
lean_object* v_fst_3764_; 
v_fst_3764_ = lean_ctor_get(v_a_3760_, 0);
if (lean_obj_tag(v_fst_3764_) == 0)
{
lean_object* v_snd_3765_; lean_object* v_snd_3766_; lean_object* v___x_3768_; 
v_snd_3765_ = lean_ctor_get(v_a_3760_, 1);
lean_inc(v_snd_3765_);
lean_dec(v_a_3760_);
v_snd_3766_ = lean_ctor_get(v_snd_3765_, 1);
lean_inc(v_snd_3766_);
lean_dec(v_snd_3765_);
if (v_isShared_3763_ == 0)
{
lean_ctor_set(v___x_3762_, 0, v_snd_3766_);
v___x_3768_ = v___x_3762_;
goto v_reusejp_3767_;
}
else
{
lean_object* v_reuseFailAlloc_3769_; 
v_reuseFailAlloc_3769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3769_, 0, v_snd_3766_);
v___x_3768_ = v_reuseFailAlloc_3769_;
goto v_reusejp_3767_;
}
v_reusejp_3767_:
{
return v___x_3768_;
}
}
else
{
lean_object* v_val_3770_; lean_object* v___x_3772_; 
lean_inc_ref(v_fst_3764_);
lean_dec(v_a_3760_);
v_val_3770_ = lean_ctor_get(v_fst_3764_, 0);
lean_inc(v_val_3770_);
lean_dec_ref_known(v_fst_3764_, 1);
if (v_isShared_3763_ == 0)
{
lean_ctor_set(v___x_3762_, 0, v_val_3770_);
v___x_3772_ = v___x_3762_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3773_; 
v_reuseFailAlloc_3773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3773_, 0, v_val_3770_);
v___x_3772_ = v_reuseFailAlloc_3773_;
goto v_reusejp_3771_;
}
v_reusejp_3771_:
{
return v___x_3772_;
}
}
}
}
else
{
lean_object* v_a_3775_; lean_object* v___x_3777_; uint8_t v_isShared_3778_; uint8_t v_isSharedCheck_3782_; 
v_a_3775_ = lean_ctor_get(v___x_3759_, 0);
v_isSharedCheck_3782_ = !lean_is_exclusive(v___x_3759_);
if (v_isSharedCheck_3782_ == 0)
{
v___x_3777_ = v___x_3759_;
v_isShared_3778_ = v_isSharedCheck_3782_;
goto v_resetjp_3776_;
}
else
{
lean_inc(v_a_3775_);
lean_dec(v___x_3759_);
v___x_3777_ = lean_box(0);
v_isShared_3778_ = v_isSharedCheck_3782_;
goto v_resetjp_3776_;
}
v_resetjp_3776_:
{
lean_object* v___x_3780_; 
if (v_isShared_3778_ == 0)
{
v___x_3780_ = v___x_3777_;
goto v_reusejp_3779_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v_a_3775_);
v___x_3780_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3779_;
}
v_reusejp_3779_:
{
return v___x_3780_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_takeListAux___boxed(lean_object* v_cfg_3783_, lean_object* v_seen_3784_, lean_object* v_acc_3785_, lean_object* v_xs_3786_, lean_object* v_a_3787_, lean_object* v_a_3788_, lean_object* v_a_3789_, lean_object* v_a_3790_, lean_object* v_a_3791_){
_start:
{
lean_object* v_res_3792_; 
v_res_3792_ = l_Lean_Meta_Rewrites_takeListAux(v_cfg_3783_, v_seen_3784_, v_acc_3785_, v_xs_3786_, v_a_3787_, v_a_3788_, v_a_3789_, v_a_3790_);
lean_dec(v_a_3790_);
lean_dec_ref(v_a_3789_);
lean_dec(v_a_3788_);
lean_dec_ref(v_a_3787_);
lean_dec(v_xs_3786_);
return v_res_3792_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0(lean_object* v_00_u03b2_3793_, lean_object* v_m_3794_, lean_object* v_a_3795_){
_start:
{
uint8_t v___x_3796_; 
v___x_3796_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg(v_m_3794_, v_a_3795_);
return v___x_3796_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___boxed(lean_object* v_00_u03b2_3797_, lean_object* v_m_3798_, lean_object* v_a_3799_){
_start:
{
uint8_t v_res_3800_; lean_object* v_r_3801_; 
v_res_3800_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0(v_00_u03b2_3797_, v_m_3798_, v_a_3799_);
lean_dec_ref(v_a_3799_);
lean_dec_ref(v_m_3798_);
v_r_3801_ = lean_box(v_res_3800_);
return v_r_3801_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1(lean_object* v_00_u03b2_3802_, lean_object* v_m_3803_, lean_object* v_a_3804_, lean_object* v_b_3805_){
_start:
{
lean_object* v___x_3806_; 
v___x_3806_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1___redArg(v_m_3803_, v_a_3804_, v_b_3805_);
return v___x_3806_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2(lean_object* v_cfg_3807_, lean_object* v_as_3808_, lean_object* v_as_x27_3809_, lean_object* v_b_3810_, lean_object* v_a_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_){
_start:
{
lean_object* v___x_3817_; 
v___x_3817_ = l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg(v_cfg_3807_, v_as_x27_3809_, v_b_3810_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_);
return v___x_3817_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___boxed(lean_object* v_cfg_3818_, lean_object* v_as_3819_, lean_object* v_as_x27_3820_, lean_object* v_b_3821_, lean_object* v_a_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_){
_start:
{
lean_object* v_res_3828_; 
v_res_3828_ = l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2(v_cfg_3818_, v_as_3819_, v_as_x27_3820_, v_b_3821_, v_a_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
lean_dec(v___y_3826_);
lean_dec_ref(v___y_3825_);
lean_dec(v___y_3824_);
lean_dec_ref(v___y_3823_);
lean_dec(v_as_x27_3820_);
lean_dec(v_as_3819_);
return v_res_3828_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0(lean_object* v_00_u03b2_3829_, lean_object* v_a_3830_, lean_object* v_x_3831_){
_start:
{
uint8_t v___x_3832_; 
v___x_3832_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(v_a_3830_, v_x_3831_);
return v___x_3832_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3833_, lean_object* v_a_3834_, lean_object* v_x_3835_){
_start:
{
uint8_t v_res_3836_; lean_object* v_r_3837_; 
v_res_3836_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0(v_00_u03b2_3833_, v_a_3834_, v_x_3835_);
lean_dec(v_x_3835_);
lean_dec_ref(v_a_3834_);
v_r_3837_ = lean_box(v_res_3836_);
return v_r_3837_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2(lean_object* v_00_u03b2_3838_, lean_object* v_data_3839_){
_start:
{
lean_object* v___x_3840_; 
v___x_3840_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2___redArg(v_data_3839_);
return v___x_3840_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3(lean_object* v_00_u03b2_3841_, lean_object* v_a_3842_, lean_object* v_b_3843_, lean_object* v_x_3844_){
_start:
{
lean_object* v___x_3845_; 
v___x_3845_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3___redArg(v_a_3842_, v_b_3843_, v_x_3844_);
return v___x_3845_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_3846_, lean_object* v_i_3847_, lean_object* v_source_3848_, lean_object* v_target_3849_){
_start:
{
lean_object* v___x_3850_; 
v___x_3850_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3___redArg(v_i_3847_, v_source_3848_, v_target_3849_);
return v___x_3850_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_3851_, lean_object* v_x_3852_, lean_object* v_x_3853_){
_start:
{
lean_object* v___x_3854_; 
v___x_3854_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3_spec__5___redArg(v_x_3852_, v_x_3853_);
return v___x_3854_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_findRewrites___closed__0(void){
_start:
{
lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; 
v___x_3855_ = lean_box(0);
v___x_3856_ = lean_unsigned_to_nat(16u);
v___x_3857_ = lean_mk_array(v___x_3856_, v___x_3855_);
return v___x_3857_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_findRewrites___closed__1(void){
_start:
{
lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; 
v___x_3858_ = lean_obj_once(&l_Lean_Meta_Rewrites_findRewrites___closed__0, &l_Lean_Meta_Rewrites_findRewrites___closed__0_once, _init_l_Lean_Meta_Rewrites_findRewrites___closed__0);
v___x_3859_ = lean_unsigned_to_nat(0u);
v___x_3860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3860_, 0, v___x_3859_);
lean_ctor_set(v___x_3860_, 1, v___x_3858_);
return v___x_3860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_findRewrites(lean_object* v_hyps_3861_, lean_object* v_moduleRef_3862_, lean_object* v_goal_3863_, lean_object* v_target_3864_, lean_object* v_forbidden_3865_, uint8_t v_side_3866_, uint8_t v_stopAtRfl_3867_, lean_object* v_max_3868_, lean_object* v_leavePercentHeartbeats_3869_, lean_object* v_a_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_, lean_object* v_a_3873_){
_start:
{
lean_object* v___x_3875_; lean_object* v___x_3876_; 
v___x_3875_ = lean_st_ref_get(v_a_3871_);
lean_inc_ref(v_target_3864_);
v___x_3876_ = l_Lean_Meta_Rewrites_rewriteCandidates(v_hyps_3861_, v_moduleRef_3862_, v_target_3864_, v_forbidden_3865_, v_a_3870_, v_a_3871_, v_a_3872_, v_a_3873_);
if (lean_obj_tag(v___x_3876_) == 0)
{
lean_object* v_a_3877_; lean_object* v___x_3878_; 
v_a_3877_ = lean_ctor_get(v___x_3876_, 0);
lean_inc(v_a_3877_);
lean_dec_ref_known(v___x_3876_, 1);
v___x_3878_ = l_Lean_getMaxHeartbeats___redArg(v_a_3872_);
if (lean_obj_tag(v___x_3878_) == 0)
{
lean_object* v_a_3879_; lean_object* v_mctx_3880_; lean_object* v_minHeartbeats_3882_; lean_object* v___y_3883_; lean_object* v___y_3884_; lean_object* v___y_3885_; lean_object* v___y_3886_; lean_object* v___x_3909_; uint8_t v___x_3910_; 
v_a_3879_ = lean_ctor_get(v___x_3878_, 0);
lean_inc(v_a_3879_);
lean_dec_ref_known(v___x_3878_, 1);
v_mctx_3880_ = lean_ctor_get(v___x_3875_, 0);
lean_inc_ref(v_mctx_3880_);
lean_dec(v___x_3875_);
v___x_3909_ = lean_unsigned_to_nat(0u);
v___x_3910_ = lean_nat_dec_eq(v_a_3879_, v___x_3909_);
lean_dec(v_a_3879_);
if (v___x_3910_ == 0)
{
lean_object* v___x_3911_; 
v___x_3911_ = l_Lean_getRemainingHeartbeats___redArg(v_a_3872_);
if (lean_obj_tag(v___x_3911_) == 0)
{
lean_object* v_a_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; 
v_a_3912_ = lean_ctor_get(v___x_3911_, 0);
lean_inc(v_a_3912_);
lean_dec_ref_known(v___x_3911_, 1);
v___x_3913_ = lean_nat_mul(v_leavePercentHeartbeats_3869_, v_a_3912_);
lean_dec(v_a_3912_);
v___x_3914_ = lean_unsigned_to_nat(100u);
v___x_3915_ = lean_nat_div(v___x_3913_, v___x_3914_);
lean_dec(v___x_3913_);
v_minHeartbeats_3882_ = v___x_3915_;
v___y_3883_ = v_a_3870_;
v___y_3884_ = v_a_3871_;
v___y_3885_ = v_a_3872_;
v___y_3886_ = v_a_3873_;
goto v___jp_3881_;
}
else
{
lean_object* v_a_3916_; lean_object* v___x_3918_; uint8_t v_isShared_3919_; uint8_t v_isSharedCheck_3923_; 
lean_dec_ref(v_mctx_3880_);
lean_dec(v_a_3877_);
lean_dec(v_max_3868_);
lean_dec_ref(v_target_3864_);
lean_dec(v_goal_3863_);
v_a_3916_ = lean_ctor_get(v___x_3911_, 0);
v_isSharedCheck_3923_ = !lean_is_exclusive(v___x_3911_);
if (v_isSharedCheck_3923_ == 0)
{
v___x_3918_ = v___x_3911_;
v_isShared_3919_ = v_isSharedCheck_3923_;
goto v_resetjp_3917_;
}
else
{
lean_inc(v_a_3916_);
lean_dec(v___x_3911_);
v___x_3918_ = lean_box(0);
v_isShared_3919_ = v_isSharedCheck_3923_;
goto v_resetjp_3917_;
}
v_resetjp_3917_:
{
lean_object* v___x_3921_; 
if (v_isShared_3919_ == 0)
{
v___x_3921_ = v___x_3918_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3922_; 
v_reuseFailAlloc_3922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3922_, 0, v_a_3916_);
v___x_3921_ = v_reuseFailAlloc_3922_;
goto v_reusejp_3920_;
}
v_reusejp_3920_:
{
return v___x_3921_;
}
}
}
}
else
{
v_minHeartbeats_3882_ = v___x_3909_;
v___y_3883_ = v_a_3870_;
v___y_3884_ = v_a_3871_;
v___y_3885_ = v_a_3872_;
v___y_3886_ = v_a_3873_;
goto v___jp_3881_;
}
v___jp_3881_:
{
lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; 
lean_inc(v_max_3868_);
v___x_3887_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_3887_, 0, v_max_3868_);
lean_ctor_set(v___x_3887_, 1, v_minHeartbeats_3882_);
lean_ctor_set(v___x_3887_, 2, v_goal_3863_);
lean_ctor_set(v___x_3887_, 3, v_target_3864_);
lean_ctor_set(v___x_3887_, 4, v_mctx_3880_);
lean_ctor_set_uint8(v___x_3887_, sizeof(void*)*5, v_stopAtRfl_3867_);
lean_ctor_set_uint8(v___x_3887_, sizeof(void*)*5 + 1, v_side_3866_);
v___x_3888_ = lean_obj_once(&l_Lean_Meta_Rewrites_findRewrites___closed__1, &l_Lean_Meta_Rewrites_findRewrites___closed__1_once, _init_l_Lean_Meta_Rewrites_findRewrites___closed__1);
v___x_3889_ = lean_mk_empty_array_with_capacity(v_max_3868_);
lean_dec(v_max_3868_);
v___x_3890_ = lean_array_to_list(v_a_3877_);
v___x_3891_ = l_Lean_Meta_Rewrites_takeListAux(v___x_3887_, v___x_3888_, v___x_3889_, v___x_3890_, v___y_3883_, v___y_3884_, v___y_3885_, v___y_3886_);
lean_dec(v___x_3890_);
if (lean_obj_tag(v___x_3891_) == 0)
{
lean_object* v_a_3892_; lean_object* v___x_3894_; uint8_t v_isShared_3895_; uint8_t v_isSharedCheck_3900_; 
v_a_3892_ = lean_ctor_get(v___x_3891_, 0);
v_isSharedCheck_3900_ = !lean_is_exclusive(v___x_3891_);
if (v_isSharedCheck_3900_ == 0)
{
v___x_3894_ = v___x_3891_;
v_isShared_3895_ = v_isSharedCheck_3900_;
goto v_resetjp_3893_;
}
else
{
lean_inc(v_a_3892_);
lean_dec(v___x_3891_);
v___x_3894_ = lean_box(0);
v_isShared_3895_ = v_isSharedCheck_3900_;
goto v_resetjp_3893_;
}
v_resetjp_3893_:
{
lean_object* v___x_3896_; lean_object* v___x_3898_; 
v___x_3896_ = lean_array_to_list(v_a_3892_);
if (v_isShared_3895_ == 0)
{
lean_ctor_set(v___x_3894_, 0, v___x_3896_);
v___x_3898_ = v___x_3894_;
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
else
{
lean_object* v_a_3901_; lean_object* v___x_3903_; uint8_t v_isShared_3904_; uint8_t v_isSharedCheck_3908_; 
v_a_3901_ = lean_ctor_get(v___x_3891_, 0);
v_isSharedCheck_3908_ = !lean_is_exclusive(v___x_3891_);
if (v_isSharedCheck_3908_ == 0)
{
v___x_3903_ = v___x_3891_;
v_isShared_3904_ = v_isSharedCheck_3908_;
goto v_resetjp_3902_;
}
else
{
lean_inc(v_a_3901_);
lean_dec(v___x_3891_);
v___x_3903_ = lean_box(0);
v_isShared_3904_ = v_isSharedCheck_3908_;
goto v_resetjp_3902_;
}
v_resetjp_3902_:
{
lean_object* v___x_3906_; 
if (v_isShared_3904_ == 0)
{
v___x_3906_ = v___x_3903_;
goto v_reusejp_3905_;
}
else
{
lean_object* v_reuseFailAlloc_3907_; 
v_reuseFailAlloc_3907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3907_, 0, v_a_3901_);
v___x_3906_ = v_reuseFailAlloc_3907_;
goto v_reusejp_3905_;
}
v_reusejp_3905_:
{
return v___x_3906_;
}
}
}
}
}
else
{
lean_object* v_a_3924_; lean_object* v___x_3926_; uint8_t v_isShared_3927_; uint8_t v_isSharedCheck_3931_; 
lean_dec(v_a_3877_);
lean_dec(v___x_3875_);
lean_dec(v_max_3868_);
lean_dec_ref(v_target_3864_);
lean_dec(v_goal_3863_);
v_a_3924_ = lean_ctor_get(v___x_3878_, 0);
v_isSharedCheck_3931_ = !lean_is_exclusive(v___x_3878_);
if (v_isSharedCheck_3931_ == 0)
{
v___x_3926_ = v___x_3878_;
v_isShared_3927_ = v_isSharedCheck_3931_;
goto v_resetjp_3925_;
}
else
{
lean_inc(v_a_3924_);
lean_dec(v___x_3878_);
v___x_3926_ = lean_box(0);
v_isShared_3927_ = v_isSharedCheck_3931_;
goto v_resetjp_3925_;
}
v_resetjp_3925_:
{
lean_object* v___x_3929_; 
if (v_isShared_3927_ == 0)
{
v___x_3929_ = v___x_3926_;
goto v_reusejp_3928_;
}
else
{
lean_object* v_reuseFailAlloc_3930_; 
v_reuseFailAlloc_3930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3930_, 0, v_a_3924_);
v___x_3929_ = v_reuseFailAlloc_3930_;
goto v_reusejp_3928_;
}
v_reusejp_3928_:
{
return v___x_3929_;
}
}
}
}
else
{
lean_object* v_a_3932_; lean_object* v___x_3934_; uint8_t v_isShared_3935_; uint8_t v_isSharedCheck_3939_; 
lean_dec(v___x_3875_);
lean_dec(v_max_3868_);
lean_dec_ref(v_target_3864_);
lean_dec(v_goal_3863_);
v_a_3932_ = lean_ctor_get(v___x_3876_, 0);
v_isSharedCheck_3939_ = !lean_is_exclusive(v___x_3876_);
if (v_isSharedCheck_3939_ == 0)
{
v___x_3934_ = v___x_3876_;
v_isShared_3935_ = v_isSharedCheck_3939_;
goto v_resetjp_3933_;
}
else
{
lean_inc(v_a_3932_);
lean_dec(v___x_3876_);
v___x_3934_ = lean_box(0);
v_isShared_3935_ = v_isSharedCheck_3939_;
goto v_resetjp_3933_;
}
v_resetjp_3933_:
{
lean_object* v___x_3937_; 
if (v_isShared_3935_ == 0)
{
v___x_3937_ = v___x_3934_;
goto v_reusejp_3936_;
}
else
{
lean_object* v_reuseFailAlloc_3938_; 
v_reuseFailAlloc_3938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3938_, 0, v_a_3932_);
v___x_3937_ = v_reuseFailAlloc_3938_;
goto v_reusejp_3936_;
}
v_reusejp_3936_:
{
return v___x_3937_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_findRewrites___boxed(lean_object* v_hyps_3940_, lean_object* v_moduleRef_3941_, lean_object* v_goal_3942_, lean_object* v_target_3943_, lean_object* v_forbidden_3944_, lean_object* v_side_3945_, lean_object* v_stopAtRfl_3946_, lean_object* v_max_3947_, lean_object* v_leavePercentHeartbeats_3948_, lean_object* v_a_3949_, lean_object* v_a_3950_, lean_object* v_a_3951_, lean_object* v_a_3952_, lean_object* v_a_3953_){
_start:
{
uint8_t v_side_boxed_3954_; uint8_t v_stopAtRfl_boxed_3955_; lean_object* v_res_3956_; 
v_side_boxed_3954_ = lean_unbox(v_side_3945_);
v_stopAtRfl_boxed_3955_ = lean_unbox(v_stopAtRfl_3946_);
v_res_3956_ = l_Lean_Meta_Rewrites_findRewrites(v_hyps_3940_, v_moduleRef_3941_, v_goal_3942_, v_target_3943_, v_forbidden_3944_, v_side_boxed_3954_, v_stopAtRfl_boxed_3955_, v_max_3947_, v_leavePercentHeartbeats_3948_, v_a_3949_, v_a_3950_, v_a_3951_, v_a_3952_);
lean_dec(v_a_3952_);
lean_dec_ref(v_a_3951_);
lean_dec(v_a_3950_);
lean_dec_ref(v_a_3949_);
lean_dec(v_leavePercentHeartbeats_3948_);
lean_dec(v_forbidden_3944_);
return v_res_3956_;
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

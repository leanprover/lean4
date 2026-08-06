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
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_ctorElim___redArg(lean_object* v_k_128_){
_start:
{
lean_inc(v_k_128_);
return v_k_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_ctorElim___redArg___boxed(lean_object* v_k_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Lean_Meta_Rewrites_RwDirection_ctorElim___redArg(v_k_129_);
lean_dec(v_k_129_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_ctorElim(lean_object* v_motive_131_, lean_object* v_ctorIdx_132_, uint8_t v_t_133_, lean_object* v_h_134_, lean_object* v_k_135_){
_start:
{
lean_inc(v_k_135_);
return v_k_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_ctorElim___boxed(lean_object* v_motive_136_, lean_object* v_ctorIdx_137_, lean_object* v_t_138_, lean_object* v_h_139_, lean_object* v_k_140_){
_start:
{
uint8_t v_t_boxed_141_; lean_object* v_res_142_; 
v_t_boxed_141_ = lean_unbox(v_t_138_);
v_res_142_ = l_Lean_Meta_Rewrites_RwDirection_ctorElim(v_motive_136_, v_ctorIdx_137_, v_t_boxed_141_, v_h_139_, v_k_140_);
lean_dec(v_k_140_);
lean_dec(v_ctorIdx_137_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_forward_elim___redArg(lean_object* v_forward_143_){
_start:
{
lean_inc(v_forward_143_);
return v_forward_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_forward_elim___redArg___boxed(lean_object* v_forward_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Lean_Meta_Rewrites_RwDirection_forward_elim___redArg(v_forward_144_);
lean_dec(v_forward_144_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_forward_elim(lean_object* v_motive_146_, uint8_t v_t_147_, lean_object* v_h_148_, lean_object* v_forward_149_){
_start:
{
lean_inc(v_forward_149_);
return v_forward_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_forward_elim___boxed(lean_object* v_motive_150_, lean_object* v_t_151_, lean_object* v_h_152_, lean_object* v_forward_153_){
_start:
{
uint8_t v_t_boxed_154_; lean_object* v_res_155_; 
v_t_boxed_154_ = lean_unbox(v_t_151_);
v_res_155_ = l_Lean_Meta_Rewrites_RwDirection_forward_elim(v_motive_150_, v_t_boxed_154_, v_h_152_, v_forward_153_);
lean_dec(v_forward_153_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_backward_elim___redArg(lean_object* v_backward_156_){
_start:
{
lean_inc(v_backward_156_);
return v_backward_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_backward_elim___redArg___boxed(lean_object* v_backward_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_Lean_Meta_Rewrites_RwDirection_backward_elim___redArg(v_backward_157_);
lean_dec(v_backward_157_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_backward_elim(lean_object* v_motive_159_, uint8_t v_t_160_, lean_object* v_h_161_, lean_object* v_backward_162_){
_start:
{
lean_inc(v_backward_162_);
return v_backward_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_backward_elim___boxed(lean_object* v_motive_163_, lean_object* v_t_164_, lean_object* v_h_165_, lean_object* v_backward_166_){
_start:
{
uint8_t v_t_boxed_167_; lean_object* v_res_168_; 
v_t_boxed_167_ = lean_unbox(v_t_164_);
v_res_168_ = l_Lean_Meta_Rewrites_RwDirection_backward_elim(v_motive_163_, v_t_boxed_167_, v_h_165_, v_backward_166_);
lean_dec(v_backward_166_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___lam__0(lean_object* v_k_169_, lean_object* v_b_170_, lean_object* v_c_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_){
_start:
{
lean_object* v___x_177_; 
lean_inc(v___y_175_);
lean_inc_ref(v___y_174_);
lean_inc(v___y_173_);
lean_inc_ref(v___y_172_);
v___x_177_ = lean_apply_7(v_k_169_, v_b_170_, v_c_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_, lean_box(0));
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___lam__0___boxed(lean_object* v_k_178_, lean_object* v_b_179_, lean_object* v_c_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___lam__0(v_k_178_, v_b_179_, v_c_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_);
lean_dec(v___y_184_);
lean_dec_ref(v___y_183_);
lean_dec(v___y_182_);
lean_dec_ref(v___y_181_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg(lean_object* v_type_187_, lean_object* v_k_188_, uint8_t v_cleanupAnnotations_189_, uint8_t v_whnfType_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_){
_start:
{
lean_object* v___f_196_; lean_object* v___x_197_; 
v___f_196_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_196_, 0, v_k_188_);
v___x_197_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_187_, v___f_196_, v_cleanupAnnotations_189_, v_whnfType_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_);
if (lean_obj_tag(v___x_197_) == 0)
{
lean_object* v_a_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_205_; 
v_a_198_ = lean_ctor_get(v___x_197_, 0);
v_isSharedCheck_205_ = !lean_is_exclusive(v___x_197_);
if (v_isSharedCheck_205_ == 0)
{
v___x_200_ = v___x_197_;
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_a_198_);
lean_dec(v___x_197_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_203_; 
if (v_isShared_201_ == 0)
{
v___x_203_ = v___x_200_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_a_198_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
}
else
{
lean_object* v_a_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_213_; 
v_a_206_ = lean_ctor_get(v___x_197_, 0);
v_isSharedCheck_213_ = !lean_is_exclusive(v___x_197_);
if (v_isSharedCheck_213_ == 0)
{
v___x_208_ = v___x_197_;
v_isShared_209_ = v_isSharedCheck_213_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_a_206_);
lean_dec(v___x_197_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_213_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_211_; 
if (v_isShared_209_ == 0)
{
v___x_211_ = v___x_208_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_a_206_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___boxed(lean_object* v_type_214_, lean_object* v_k_215_, lean_object* v_cleanupAnnotations_216_, lean_object* v_whnfType_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_223_; uint8_t v_whnfType_boxed_224_; lean_object* v_res_225_; 
v_cleanupAnnotations_boxed_223_ = lean_unbox(v_cleanupAnnotations_216_);
v_whnfType_boxed_224_ = lean_unbox(v_whnfType_217_);
v_res_225_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg(v_type_214_, v_k_215_, v_cleanupAnnotations_boxed_223_, v_whnfType_boxed_224_, v___y_218_, v___y_219_, v___y_220_, v___y_221_);
lean_dec(v___y_221_);
lean_dec_ref(v___y_220_);
lean_dec(v___y_219_);
lean_dec_ref(v___y_218_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0(lean_object* v_00_u03b1_226_, lean_object* v_type_227_, lean_object* v_k_228_, uint8_t v_cleanupAnnotations_229_, uint8_t v_whnfType_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg(v_type_227_, v_k_228_, v_cleanupAnnotations_229_, v_whnfType_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___boxed(lean_object* v_00_u03b1_237_, lean_object* v_type_238_, lean_object* v_k_239_, lean_object* v_cleanupAnnotations_240_, lean_object* v_whnfType_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_247_; uint8_t v_whnfType_boxed_248_; lean_object* v_res_249_; 
v_cleanupAnnotations_boxed_247_ = lean_unbox(v_cleanupAnnotations_240_);
v_whnfType_boxed_248_ = lean_unbox(v_whnfType_241_);
v_res_249_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0(v_00_u03b1_237_, v_type_238_, v_k_239_, v_cleanupAnnotations_boxed_247_, v_whnfType_boxed_248_, v___y_242_, v___y_243_, v___y_244_, v___y_245_);
lean_dec(v___y_245_);
lean_dec_ref(v___y_244_);
lean_dec(v___y_243_);
lean_dec_ref(v___y_242_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1___redArg(lean_object* v_k_250_, uint8_t v_allowLevelAssignments_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_251_, v_k_250_, v___y_252_, v___y_253_, v___y_254_, v___y_255_);
if (lean_obj_tag(v___x_257_) == 0)
{
lean_object* v_a_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_265_; 
v_a_258_ = lean_ctor_get(v___x_257_, 0);
v_isSharedCheck_265_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_265_ == 0)
{
v___x_260_ = v___x_257_;
v_isShared_261_ = v_isSharedCheck_265_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_a_258_);
lean_dec(v___x_257_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_265_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___x_263_; 
if (v_isShared_261_ == 0)
{
v___x_263_ = v___x_260_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v_a_258_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
}
else
{
lean_object* v_a_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_273_; 
v_a_266_ = lean_ctor_get(v___x_257_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_273_ == 0)
{
v___x_268_ = v___x_257_;
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_a_266_);
lean_dec(v___x_257_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_271_; 
if (v_isShared_269_ == 0)
{
v___x_271_ = v___x_268_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_a_266_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1___redArg___boxed(lean_object* v_k_274_, lean_object* v_allowLevelAssignments_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_281_; lean_object* v_res_282_; 
v_allowLevelAssignments_boxed_281_ = lean_unbox(v_allowLevelAssignments_275_);
v_res_282_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1___redArg(v_k_274_, v_allowLevelAssignments_boxed_281_, v___y_276_, v___y_277_, v___y_278_, v___y_279_);
lean_dec(v___y_279_);
lean_dec_ref(v___y_278_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_276_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1(lean_object* v_00_u03b1_283_, lean_object* v_k_284_, uint8_t v_allowLevelAssignments_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1___redArg(v_k_284_, v_allowLevelAssignments_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1___boxed(lean_object* v_00_u03b1_292_, lean_object* v_k_293_, lean_object* v_allowLevelAssignments_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_300_; lean_object* v_res_301_; 
v_allowLevelAssignments_boxed_300_ = lean_unbox(v_allowLevelAssignments_294_);
v_res_301_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1(v_00_u03b1_292_, v_k_293_, v_allowLevelAssignments_boxed_300_, v___y_295_, v___y_296_, v___y_297_, v___y_298_);
lean_dec(v___y_298_);
lean_dec_ref(v___y_297_);
lean_dec(v___y_296_);
lean_dec_ref(v___y_295_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0(lean_object* v_name_306_, lean_object* v_x_307_, lean_object* v_type_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_){
_start:
{
lean_object* v___x_317_; lean_object* v_fst_318_; 
v___x_317_ = l_Lean_Expr_getAppFnArgs(v_type_308_);
v_fst_318_ = lean_ctor_get(v___x_317_, 0);
lean_inc(v_fst_318_);
if (lean_obj_tag(v_fst_318_) == 1)
{
lean_object* v_pre_319_; 
v_pre_319_ = lean_ctor_get(v_fst_318_, 0);
if (lean_obj_tag(v_pre_319_) == 0)
{
lean_object* v_snd_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_419_; 
v_snd_320_ = lean_ctor_get(v___x_317_, 1);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_317_);
if (v_isSharedCheck_419_ == 0)
{
lean_object* v_unused_420_; 
v_unused_420_ = lean_ctor_get(v___x_317_, 0);
lean_dec(v_unused_420_);
v___x_322_ = v___x_317_;
v_isShared_323_ = v_isSharedCheck_419_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_snd_320_);
lean_dec(v___x_317_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_419_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v_str_324_; lean_object* v___x_325_; uint8_t v___x_326_; 
v_str_324_ = lean_ctor_get(v_fst_318_, 1);
lean_inc_ref(v_str_324_);
lean_dec_ref_known(v_fst_318_, 2);
v___x_325_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__1));
v___x_326_ = lean_string_dec_eq(v_str_324_, v___x_325_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; uint8_t v___x_328_; 
v___x_327_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__2));
v___x_328_ = lean_string_dec_eq(v_str_324_, v___x_327_);
lean_dec_ref(v_str_324_);
if (v___x_328_ == 0)
{
lean_del_object(v___x_322_);
lean_dec(v_snd_320_);
lean_dec(v_name_306_);
goto v___jp_314_;
}
else
{
lean_object* v___x_329_; lean_object* v___x_330_; uint8_t v___x_331_; 
v___x_329_ = lean_array_get_size(v_snd_320_);
v___x_330_ = lean_unsigned_to_nat(2u);
v___x_331_ = lean_nat_dec_eq(v___x_329_, v___x_330_);
if (v___x_331_ == 0)
{
lean_del_object(v___x_322_);
lean_dec(v_snd_320_);
lean_dec(v_name_306_);
goto v___jp_314_;
}
else
{
lean_object* v___x_332_; lean_object* v___x_333_; uint8_t v___x_334_; lean_object* v___x_335_; lean_object* v___x_337_; 
v___x_332_ = lean_unsigned_to_nat(0u);
v___x_333_ = lean_array_fget_borrowed(v_snd_320_, v___x_332_);
v___x_334_ = 0;
v___x_335_ = lean_box(v___x_334_);
lean_inc(v_name_306_);
if (v_isShared_323_ == 0)
{
lean_ctor_set(v___x_322_, 1, v___x_335_);
lean_ctor_set(v___x_322_, 0, v_name_306_);
v___x_337_ = v___x_322_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_name_306_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v___x_335_);
v___x_337_ = v_reuseFailAlloc_373_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
lean_object* v___x_338_; 
lean_inc(v___x_333_);
v___x_338_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(v___x_333_, v___x_337_, v___y_309_, v___y_310_, v___y_311_, v___y_312_);
if (lean_obj_tag(v___x_338_) == 0)
{
lean_object* v_a_339_; lean_object* v___x_340_; lean_object* v___x_341_; uint8_t v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v_a_339_ = lean_ctor_get(v___x_338_, 0);
lean_inc(v_a_339_);
lean_dec_ref_known(v___x_338_, 1);
v___x_340_ = lean_unsigned_to_nat(1u);
v___x_341_ = lean_array_fget(v_snd_320_, v___x_340_);
lean_dec(v_snd_320_);
v___x_342_ = 1;
v___x_343_ = lean_box(v___x_342_);
v___x_344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_344_, 0, v_name_306_);
lean_ctor_set(v___x_344_, 1, v___x_343_);
v___x_345_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(v___x_341_, v___x_344_, v___y_309_, v___y_310_, v___y_311_, v___y_312_);
if (lean_obj_tag(v___x_345_) == 0)
{
lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_356_; 
v_a_346_ = lean_ctor_get(v___x_345_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_345_);
if (v_isSharedCheck_356_ == 0)
{
v___x_348_ = v___x_345_;
v_isShared_349_ = v_isSharedCheck_356_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v___x_345_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_356_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_354_; 
v___x_350_ = lean_mk_empty_array_with_capacity(v___x_330_);
v___x_351_ = lean_array_push(v___x_350_, v_a_339_);
v___x_352_ = lean_array_push(v___x_351_, v_a_346_);
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 0, v___x_352_);
v___x_354_ = v___x_348_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v___x_352_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
else
{
lean_object* v_a_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_364_; 
lean_dec(v_a_339_);
v_a_357_ = lean_ctor_get(v___x_345_, 0);
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_345_);
if (v_isSharedCheck_364_ == 0)
{
v___x_359_ = v___x_345_;
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_a_357_);
lean_dec(v___x_345_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_362_; 
if (v_isShared_360_ == 0)
{
v___x_362_ = v___x_359_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v_a_357_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
}
}
else
{
lean_object* v_a_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_372_; 
lean_dec(v_snd_320_);
lean_dec(v_name_306_);
v_a_365_ = lean_ctor_get(v___x_338_, 0);
v_isSharedCheck_372_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_372_ == 0)
{
v___x_367_ = v___x_338_;
v_isShared_368_ = v_isSharedCheck_372_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_a_365_);
lean_dec(v___x_338_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_372_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_370_; 
if (v_isShared_368_ == 0)
{
v___x_370_ = v___x_367_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v_a_365_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_374_; lean_object* v___x_375_; uint8_t v___x_376_; 
lean_dec_ref(v_str_324_);
v___x_374_ = lean_array_get_size(v_snd_320_);
v___x_375_ = lean_unsigned_to_nat(3u);
v___x_376_ = lean_nat_dec_eq(v___x_374_, v___x_375_);
if (v___x_376_ == 0)
{
lean_del_object(v___x_322_);
lean_dec(v_snd_320_);
lean_dec(v_name_306_);
goto v___jp_314_;
}
else
{
lean_object* v___x_377_; lean_object* v___x_378_; uint8_t v___x_379_; lean_object* v___x_380_; lean_object* v___x_382_; 
v___x_377_ = lean_unsigned_to_nat(1u);
v___x_378_ = lean_array_fget_borrowed(v_snd_320_, v___x_377_);
v___x_379_ = 0;
v___x_380_ = lean_box(v___x_379_);
lean_inc(v_name_306_);
if (v_isShared_323_ == 0)
{
lean_ctor_set(v___x_322_, 1, v___x_380_);
lean_ctor_set(v___x_322_, 0, v_name_306_);
v___x_382_ = v___x_322_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_name_306_);
lean_ctor_set(v_reuseFailAlloc_418_, 1, v___x_380_);
v___x_382_ = v_reuseFailAlloc_418_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
lean_object* v___x_383_; 
lean_inc(v___x_378_);
v___x_383_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(v___x_378_, v___x_382_, v___y_309_, v___y_310_, v___y_311_, v___y_312_);
if (lean_obj_tag(v___x_383_) == 0)
{
lean_object* v_a_384_; lean_object* v___x_385_; lean_object* v___x_386_; uint8_t v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v_a_384_ = lean_ctor_get(v___x_383_, 0);
lean_inc(v_a_384_);
lean_dec_ref_known(v___x_383_, 1);
v___x_385_ = lean_unsigned_to_nat(2u);
v___x_386_ = lean_array_fget(v_snd_320_, v___x_385_);
lean_dec(v_snd_320_);
v___x_387_ = 1;
v___x_388_ = lean_box(v___x_387_);
v___x_389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_389_, 0, v_name_306_);
lean_ctor_set(v___x_389_, 1, v___x_388_);
v___x_390_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(v___x_386_, v___x_389_, v___y_309_, v___y_310_, v___y_311_, v___y_312_);
if (lean_obj_tag(v___x_390_) == 0)
{
lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_401_; 
v_a_391_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_401_ == 0)
{
v___x_393_ = v___x_390_;
v_isShared_394_ = v_isSharedCheck_401_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_390_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_401_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_399_; 
v___x_395_ = lean_mk_empty_array_with_capacity(v___x_385_);
v___x_396_ = lean_array_push(v___x_395_, v_a_384_);
v___x_397_ = lean_array_push(v___x_396_, v_a_391_);
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 0, v___x_397_);
v___x_399_ = v___x_393_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v___x_397_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
}
else
{
lean_object* v_a_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_409_; 
lean_dec(v_a_384_);
v_a_402_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_409_ == 0)
{
v___x_404_ = v___x_390_;
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_a_402_);
lean_dec(v___x_390_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_407_; 
if (v_isShared_405_ == 0)
{
v___x_407_ = v___x_404_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_a_402_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
}
else
{
lean_object* v_a_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_417_; 
lean_dec(v_snd_320_);
lean_dec(v_name_306_);
v_a_410_ = lean_ctor_get(v___x_383_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_383_);
if (v_isSharedCheck_417_ == 0)
{
v___x_412_ = v___x_383_;
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_a_410_);
lean_dec(v___x_383_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_415_; 
if (v_isShared_413_ == 0)
{
v___x_415_ = v___x_412_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_a_410_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
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
lean_dec_ref_known(v_fst_318_, 2);
lean_dec_ref(v___x_317_);
lean_dec(v_name_306_);
goto v___jp_314_;
}
}
else
{
lean_dec(v_fst_318_);
lean_dec_ref(v___x_317_);
lean_dec(v_name_306_);
goto v___jp_314_;
}
v___jp_314_:
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0));
v___x_316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
return v___x_316_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___boxed(lean_object* v_name_421_, lean_object* v_x_422_, lean_object* v_type_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0(v_name_421_, v_x_422_, v_type_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_);
lean_dec(v___y_427_);
lean_dec_ref(v___y_426_);
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
lean_dec_ref(v_x_422_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__1(uint8_t v___x_430_, lean_object* v_type_431_, lean_object* v___f_432_, uint8_t v___x_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
lean_object* v_keyedConfig_439_; uint8_t v_trackZetaDelta_440_; lean_object* v_zetaDeltaSet_441_; lean_object* v_lctx_442_; lean_object* v_localInstances_443_; lean_object* v_defEqCtx_x3f_444_; lean_object* v_synthPendingDepth_445_; lean_object* v_customCanUnfoldPredicate_x3f_446_; uint8_t v_univApprox_447_; uint8_t v_inTypeClassResolution_448_; uint8_t v_cacheInferType_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_458_; 
v_keyedConfig_439_ = lean_ctor_get(v___y_434_, 0);
v_trackZetaDelta_440_ = lean_ctor_get_uint8(v___y_434_, sizeof(void*)*7);
v_zetaDeltaSet_441_ = lean_ctor_get(v___y_434_, 1);
v_lctx_442_ = lean_ctor_get(v___y_434_, 2);
v_localInstances_443_ = lean_ctor_get(v___y_434_, 3);
v_defEqCtx_x3f_444_ = lean_ctor_get(v___y_434_, 4);
v_synthPendingDepth_445_ = lean_ctor_get(v___y_434_, 5);
v_customCanUnfoldPredicate_x3f_446_ = lean_ctor_get(v___y_434_, 6);
v_univApprox_447_ = lean_ctor_get_uint8(v___y_434_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_448_ = lean_ctor_get_uint8(v___y_434_, sizeof(void*)*7 + 2);
v_cacheInferType_449_ = lean_ctor_get_uint8(v___y_434_, sizeof(void*)*7 + 3);
v_isSharedCheck_458_ = !lean_is_exclusive(v___y_434_);
if (v_isSharedCheck_458_ == 0)
{
v___x_451_ = v___y_434_;
v_isShared_452_ = v_isSharedCheck_458_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_446_);
lean_inc(v_synthPendingDepth_445_);
lean_inc(v_defEqCtx_x3f_444_);
lean_inc(v_localInstances_443_);
lean_inc(v_lctx_442_);
lean_inc(v_zetaDeltaSet_441_);
lean_inc(v_keyedConfig_439_);
lean_dec(v___y_434_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_458_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_453_; lean_object* v___x_455_; 
v___x_453_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_430_, v_keyedConfig_439_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 0, v___x_453_);
v___x_455_ = v___x_451_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v___x_453_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v_zetaDeltaSet_441_);
lean_ctor_set(v_reuseFailAlloc_457_, 2, v_lctx_442_);
lean_ctor_set(v_reuseFailAlloc_457_, 3, v_localInstances_443_);
lean_ctor_set(v_reuseFailAlloc_457_, 4, v_defEqCtx_x3f_444_);
lean_ctor_set(v_reuseFailAlloc_457_, 5, v_synthPendingDepth_445_);
lean_ctor_set(v_reuseFailAlloc_457_, 6, v_customCanUnfoldPredicate_x3f_446_);
lean_ctor_set_uint8(v_reuseFailAlloc_457_, sizeof(void*)*7, v_trackZetaDelta_440_);
lean_ctor_set_uint8(v_reuseFailAlloc_457_, sizeof(void*)*7 + 1, v_univApprox_447_);
lean_ctor_set_uint8(v_reuseFailAlloc_457_, sizeof(void*)*7 + 2, v_inTypeClassResolution_448_);
lean_ctor_set_uint8(v_reuseFailAlloc_457_, sizeof(void*)*7 + 3, v_cacheInferType_449_);
v___x_455_ = v_reuseFailAlloc_457_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
lean_object* v___x_456_; 
v___x_456_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg(v_type_431_, v___f_432_, v___x_433_, v___x_433_, v___x_455_, v___y_435_, v___y_436_, v___y_437_);
lean_dec_ref(v___x_455_);
return v___x_456_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__1___boxed(lean_object* v___x_459_, lean_object* v_type_460_, lean_object* v___f_461_, lean_object* v___x_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
uint8_t v___x_6864__boxed_468_; uint8_t v___x_6866__boxed_469_; lean_object* v_res_470_; 
v___x_6864__boxed_468_ = lean_unbox(v___x_459_);
v___x_6866__boxed_469_ = lean_unbox(v___x_462_);
v_res_470_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__1(v___x_6864__boxed_468_, v_type_460_, v___f_461_, v___x_6866__boxed_469_, v___y_463_, v___y_464_, v___y_465_, v___y_466_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
lean_dec(v___y_464_);
return v_res_470_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__1(void){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_472_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__0));
v___x_473_ = lean_string_utf8_byte_size(v___x_472_);
return v___x_473_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__5(void){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__4));
v___x_478_ = lean_string_utf8_byte_size(v___x_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport(lean_object* v_name_479_, lean_object* v_c_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_){
_start:
{
uint8_t v___x_486_; 
lean_inc_ref(v_c_480_);
v___x_486_ = l_Lean_AsyncConstantInfo_isUnsafe(v_c_480_);
if (v___x_486_ == 0)
{
lean_object* v___x_487_; lean_object* v_env_491_; uint8_t v___x_492_; 
v___x_487_ = lean_st_ref_get(v_a_484_);
v_env_491_ = lean_ctor_get(v___x_487_, 0);
lean_inc_ref(v_env_491_);
lean_dec(v___x_487_);
lean_inc(v_name_479_);
v___x_492_ = l_Lean_Meta_allowCompletion(v_env_491_, v_name_479_);
if (v___x_492_ == 0)
{
lean_dec_ref(v_c_480_);
lean_dec(v_name_479_);
goto v___jp_488_;
}
else
{
if (v___x_486_ == 0)
{
lean_object* v___x_493_; lean_object* v_env_497_; uint8_t v___x_498_; 
v___x_493_ = lean_st_ref_get(v_a_484_);
v_env_497_ = lean_ctor_get(v___x_493_, 0);
lean_inc_ref(v_env_497_);
lean_dec(v___x_493_);
lean_inc(v_name_479_);
v___x_498_ = l_Lean_Linter_isDeprecated(v_env_497_, v_name_479_);
if (v___x_498_ == 0)
{
lean_object* v___f_499_; lean_object* v___y_501_; lean_object* v___y_502_; lean_object* v___y_503_; lean_object* v___y_504_; 
lean_inc(v_name_479_);
v___f_499_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___boxed), 8, 1);
lean_closure_set(v___f_499_, 0, v_name_479_);
if (lean_obj_tag(v_name_479_) == 1)
{
lean_object* v_str_515_; uint8_t v___y_517_; lean_object* v___x_525_; uint8_t v___x_526_; 
v_str_515_ = lean_ctor_get(v_name_479_, 1);
v___x_525_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__2));
v___x_526_ = lean_string_dec_eq(v_str_515_, v___x_525_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; uint8_t v___x_528_; 
v___x_527_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__3));
v___x_528_ = lean_string_dec_eq(v_str_515_, v___x_527_);
if (v___x_528_ == 0)
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; uint8_t v___x_532_; 
v___x_529_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__4));
v___x_530_ = lean_string_utf8_byte_size(v_str_515_);
v___x_531_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__5, &l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__5_once, _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__5);
v___x_532_ = lean_nat_dec_le(v___x_531_, v___x_530_);
if (v___x_532_ == 0)
{
v___y_517_ = v___x_498_;
goto v___jp_516_;
}
else
{
lean_object* v___x_533_; lean_object* v___x_534_; uint8_t v___x_535_; 
v___x_533_ = lean_unsigned_to_nat(0u);
v___x_534_ = lean_nat_sub(v___x_530_, v___x_531_);
v___x_535_ = lean_string_memcmp(v_str_515_, v___x_529_, v___x_534_, v___x_533_, v___x_531_);
lean_dec(v___x_534_);
v___y_517_ = v___x_535_;
goto v___jp_516_;
}
}
else
{
lean_dec_ref_known(v_name_479_, 2);
lean_dec_ref(v___f_499_);
lean_dec_ref(v_c_480_);
goto v___jp_494_;
}
}
else
{
lean_dec_ref_known(v_name_479_, 2);
lean_dec_ref(v___f_499_);
lean_dec_ref(v_c_480_);
goto v___jp_494_;
}
v___jp_516_:
{
if (v___y_517_ == 0)
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; uint8_t v___x_521_; 
v___x_518_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__0));
v___x_519_ = lean_string_utf8_byte_size(v_str_515_);
v___x_520_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__1, &l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__1_once, _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__1);
v___x_521_ = lean_nat_dec_le(v___x_520_, v___x_519_);
if (v___x_521_ == 0)
{
v___y_501_ = v_a_481_;
v___y_502_ = v_a_482_;
v___y_503_ = v_a_483_;
v___y_504_ = v_a_484_;
goto v___jp_500_;
}
else
{
lean_object* v___x_522_; lean_object* v___x_523_; uint8_t v___x_524_; 
v___x_522_ = lean_unsigned_to_nat(0u);
v___x_523_ = lean_nat_sub(v___x_519_, v___x_520_);
v___x_524_ = lean_string_memcmp(v_str_515_, v___x_518_, v___x_523_, v___x_522_, v___x_520_);
lean_dec(v___x_523_);
if (v___x_524_ == 0)
{
v___y_501_ = v_a_481_;
v___y_502_ = v_a_482_;
v___y_503_ = v_a_483_;
v___y_504_ = v_a_484_;
goto v___jp_500_;
}
else
{
lean_dec_ref_known(v_name_479_, 2);
lean_dec_ref(v___f_499_);
lean_dec_ref(v_c_480_);
goto v___jp_494_;
}
}
}
else
{
lean_dec_ref_known(v_name_479_, 2);
lean_dec_ref(v___f_499_);
lean_dec_ref(v_c_480_);
goto v___jp_494_;
}
}
}
else
{
v___y_501_ = v_a_481_;
v___y_502_ = v_a_482_;
v___y_503_ = v_a_483_;
v___y_504_ = v_a_484_;
goto v___jp_500_;
}
v___jp_500_:
{
uint8_t v___x_505_; 
v___x_505_ = l_Lean_Name_isMetaprogramming(v_name_479_);
if (v___x_505_ == 0)
{
lean_object* v___x_506_; lean_object* v_type_507_; uint8_t v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___f_511_; lean_object* v___x_512_; 
v___x_506_ = l_Lean_AsyncConstantInfo_toConstantVal(v_c_480_);
v_type_507_ = lean_ctor_get(v___x_506_, 2);
lean_inc_ref(v_type_507_);
lean_dec_ref(v___x_506_);
v___x_508_ = 2;
v___x_509_ = lean_box(v___x_508_);
v___x_510_ = lean_box(v___x_505_);
v___f_511_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__1___boxed), 9, 4);
lean_closure_set(v___f_511_, 0, v___x_509_);
lean_closure_set(v___f_511_, 1, v_type_507_);
lean_closure_set(v___f_511_, 2, v___f_499_);
lean_closure_set(v___f_511_, 3, v___x_510_);
v___x_512_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1___redArg(v___f_511_, v___x_505_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
return v___x_512_;
}
else
{
lean_object* v___x_513_; lean_object* v___x_514_; 
lean_dec_ref(v___f_499_);
lean_dec_ref(v_c_480_);
v___x_513_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0));
v___x_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_514_, 0, v___x_513_);
return v___x_514_;
}
}
}
else
{
lean_object* v___x_536_; lean_object* v___x_537_; 
lean_dec_ref(v_c_480_);
lean_dec(v_name_479_);
v___x_536_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0));
v___x_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
return v___x_537_;
}
v___jp_494_:
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0));
v___x_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_496_, 0, v___x_495_);
return v___x_496_;
}
}
else
{
lean_dec_ref(v_c_480_);
lean_dec(v_name_479_);
goto v___jp_488_;
}
}
v___jp_488_:
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0));
v___x_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
return v___x_490_;
}
}
else
{
lean_object* v___x_538_; lean_object* v___x_539_; 
lean_dec_ref(v_c_480_);
lean_dec(v_name_479_);
v___x_538_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0));
v___x_539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_539_, 0, v___x_538_);
return v___x_539_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___boxed(lean_object* v_name_540_, lean_object* v_c_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport(v_name_540_, v_c_541_, v_a_542_, v_a_543_, v_a_544_, v_a_545_);
lean_dec(v_a_545_);
lean_dec_ref(v_a_544_);
lean_dec(v_a_543_);
lean_dec_ref(v_a_542_);
return v_res_547_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_Rewrites_localHypotheses_spec__0(lean_object* v_a_548_, lean_object* v_x_549_){
_start:
{
if (lean_obj_tag(v_x_549_) == 0)
{
uint8_t v___x_550_; 
v___x_550_ = 0;
return v___x_550_;
}
else
{
lean_object* v_head_551_; lean_object* v_tail_552_; uint8_t v___x_553_; 
v_head_551_ = lean_ctor_get(v_x_549_, 0);
v_tail_552_ = lean_ctor_get(v_x_549_, 1);
v___x_553_ = l_Lean_instBEqFVarId_beq(v_a_548_, v_head_551_);
if (v___x_553_ == 0)
{
v_x_549_ = v_tail_552_;
goto _start;
}
else
{
return v___x_553_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_Rewrites_localHypotheses_spec__0___boxed(lean_object* v_a_555_, lean_object* v_x_556_){
_start:
{
uint8_t v_res_557_; lean_object* v_r_558_; 
v_res_557_ = l_List_elem___at___00Lean_Meta_Rewrites_localHypotheses_spec__0(v_a_555_, v_x_556_);
lean_dec(v_x_556_);
lean_dec(v_a_555_);
v_r_558_ = lean_box(v_res_557_);
return v_r_558_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_localHypotheses_spec__2(lean_object* v_except_559_, lean_object* v_as_560_, size_t v_sz_561_, size_t v_i_562_, lean_object* v_b_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_){
_start:
{
lean_object* v_a_570_; uint8_t v___x_574_; 
v___x_574_ = lean_usize_dec_lt(v_i_562_, v_sz_561_);
if (v___x_574_ == 0)
{
lean_object* v___x_575_; 
v___x_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_575_, 0, v_b_563_);
return v___x_575_;
}
else
{
lean_object* v_a_576_; lean_object* v___x_577_; uint8_t v___x_578_; 
v_a_576_ = lean_array_uget_borrowed(v_as_560_, v_i_562_);
v___x_577_ = l_Lean_Expr_fvarId_x21(v_a_576_);
v___x_578_ = l_List_elem___at___00Lean_Meta_Rewrites_localHypotheses_spec__0(v___x_577_, v_except_559_);
lean_dec(v___x_577_);
if (v___x_578_ == 0)
{
lean_object* v___x_579_; 
lean_inc(v___y_567_);
lean_inc_ref(v___y_566_);
lean_inc(v___y_565_);
lean_inc_ref(v___y_564_);
lean_inc(v_a_576_);
v___x_579_ = lean_infer_type(v_a_576_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
if (lean_obj_tag(v___x_579_) == 0)
{
lean_object* v_a_580_; lean_object* v___x_581_; uint8_t v___x_582_; lean_object* v___x_583_; 
v_a_580_ = lean_ctor_get(v___x_579_, 0);
lean_inc(v_a_580_);
lean_dec_ref_known(v___x_579_, 1);
v___x_581_ = lean_box(0);
v___x_582_ = 0;
v___x_583_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_580_, v___x_581_, v___x_582_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
if (lean_obj_tag(v___x_583_) == 0)
{
lean_object* v_a_584_; lean_object* v_snd_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_656_; 
v_a_584_ = lean_ctor_get(v___x_583_, 0);
lean_inc(v_a_584_);
lean_dec_ref_known(v___x_583_, 1);
v_snd_585_ = lean_ctor_get(v_a_584_, 1);
v_isSharedCheck_656_ = !lean_is_exclusive(v_a_584_);
if (v_isSharedCheck_656_ == 0)
{
lean_object* v_unused_657_; 
v_unused_657_ = lean_ctor_get(v_a_584_, 0);
lean_dec(v_unused_657_);
v___x_587_ = v_a_584_;
v_isShared_588_ = v_isSharedCheck_656_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_snd_585_);
lean_dec(v_a_584_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_656_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v_snd_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_654_; 
v_snd_589_ = lean_ctor_get(v_snd_585_, 1);
v_isSharedCheck_654_ = !lean_is_exclusive(v_snd_585_);
if (v_isSharedCheck_654_ == 0)
{
lean_object* v_unused_655_; 
v_unused_655_ = lean_ctor_get(v_snd_585_, 0);
lean_dec(v_unused_655_);
v___x_591_ = v_snd_585_;
v_isShared_592_ = v_isSharedCheck_654_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_snd_589_);
lean_dec(v_snd_585_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_654_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_593_; 
v___x_593_ = l_Lean_Meta_whnfR(v_snd_589_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
if (lean_obj_tag(v___x_593_) == 0)
{
lean_object* v_a_594_; lean_object* v___x_595_; lean_object* v_fst_596_; 
v_a_594_ = lean_ctor_get(v___x_593_, 0);
lean_inc(v_a_594_);
lean_dec_ref_known(v___x_593_, 1);
v___x_595_ = l_Lean_Expr_getAppFnArgs(v_a_594_);
v_fst_596_ = lean_ctor_get(v___x_595_, 0);
lean_inc(v_fst_596_);
if (lean_obj_tag(v_fst_596_) == 1)
{
lean_object* v_pre_597_; 
v_pre_597_ = lean_ctor_get(v_fst_596_, 0);
if (lean_obj_tag(v_pre_597_) == 0)
{
lean_object* v_snd_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_644_; 
v_snd_598_ = lean_ctor_get(v___x_595_, 1);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_644_ == 0)
{
lean_object* v_unused_645_; 
v_unused_645_ = lean_ctor_get(v___x_595_, 0);
lean_dec(v_unused_645_);
v___x_600_ = v___x_595_;
v_isShared_601_ = v_isSharedCheck_644_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_snd_598_);
lean_dec(v___x_595_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_644_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v_str_602_; lean_object* v___x_603_; uint8_t v___x_604_; 
v_str_602_ = lean_ctor_get(v_fst_596_, 1);
lean_inc_ref(v_str_602_);
lean_dec_ref_known(v_fst_596_, 2);
v___x_603_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__1));
v___x_604_ = lean_string_dec_eq(v_str_602_, v___x_603_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; uint8_t v___x_606_; 
v___x_605_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__2));
v___x_606_ = lean_string_dec_eq(v_str_602_, v___x_605_);
lean_dec_ref(v_str_602_);
if (v___x_606_ == 0)
{
lean_del_object(v___x_600_);
lean_dec(v_snd_598_);
lean_del_object(v___x_591_);
lean_del_object(v___x_587_);
v_a_570_ = v_b_563_;
goto v___jp_569_;
}
else
{
lean_object* v___x_607_; lean_object* v___x_608_; uint8_t v___x_609_; 
v___x_607_ = lean_array_get_size(v_snd_598_);
lean_dec(v_snd_598_);
v___x_608_ = lean_unsigned_to_nat(2u);
v___x_609_ = lean_nat_dec_eq(v___x_607_, v___x_608_);
if (v___x_609_ == 0)
{
lean_del_object(v___x_600_);
lean_del_object(v___x_591_);
lean_del_object(v___x_587_);
v_a_570_ = v_b_563_;
goto v___jp_569_;
}
else
{
lean_object* v___x_610_; lean_object* v___x_612_; 
v___x_610_ = lean_box(v___x_578_);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 1, v___x_608_);
lean_ctor_set(v___x_600_, 0, v___x_610_);
v___x_612_ = v___x_600_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v___x_610_);
lean_ctor_set(v_reuseFailAlloc_624_, 1, v___x_608_);
v___x_612_ = v_reuseFailAlloc_624_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
lean_object* v___x_614_; 
lean_inc(v_a_576_);
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 1, v___x_612_);
lean_ctor_set(v___x_591_, 0, v_a_576_);
v___x_614_ = v___x_591_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_a_576_);
lean_ctor_set(v_reuseFailAlloc_623_, 1, v___x_612_);
v___x_614_ = v_reuseFailAlloc_623_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_619_; 
v___x_615_ = lean_array_push(v_b_563_, v___x_614_);
v___x_616_ = lean_unsigned_to_nat(1u);
v___x_617_ = lean_box(v___x_574_);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 1, v___x_616_);
lean_ctor_set(v___x_587_, 0, v___x_617_);
v___x_619_ = v___x_587_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v___x_617_);
lean_ctor_set(v_reuseFailAlloc_622_, 1, v___x_616_);
v___x_619_ = v_reuseFailAlloc_622_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
lean_object* v___x_620_; lean_object* v___x_621_; 
lean_inc(v_a_576_);
v___x_620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_620_, 0, v_a_576_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
v___x_621_ = lean_array_push(v___x_615_, v___x_620_);
v_a_570_ = v___x_621_;
goto v___jp_569_;
}
}
}
}
}
}
else
{
lean_object* v___x_625_; lean_object* v___x_626_; uint8_t v___x_627_; 
lean_dec_ref(v_str_602_);
v___x_625_ = lean_array_get_size(v_snd_598_);
lean_dec(v_snd_598_);
v___x_626_ = lean_unsigned_to_nat(3u);
v___x_627_ = lean_nat_dec_eq(v___x_625_, v___x_626_);
if (v___x_627_ == 0)
{
lean_del_object(v___x_600_);
lean_del_object(v___x_591_);
lean_del_object(v___x_587_);
v_a_570_ = v_b_563_;
goto v___jp_569_;
}
else
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_631_; 
v___x_628_ = lean_unsigned_to_nat(2u);
v___x_629_ = lean_box(v___x_578_);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 1, v___x_628_);
lean_ctor_set(v___x_600_, 0, v___x_629_);
v___x_631_ = v___x_600_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v___x_629_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v___x_628_);
v___x_631_ = v_reuseFailAlloc_643_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
lean_object* v___x_633_; 
lean_inc(v_a_576_);
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 1, v___x_631_);
lean_ctor_set(v___x_591_, 0, v_a_576_);
v___x_633_ = v___x_591_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_a_576_);
lean_ctor_set(v_reuseFailAlloc_642_, 1, v___x_631_);
v___x_633_ = v_reuseFailAlloc_642_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_638_; 
v___x_634_ = lean_array_push(v_b_563_, v___x_633_);
v___x_635_ = lean_unsigned_to_nat(1u);
v___x_636_ = lean_box(v___x_574_);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 1, v___x_635_);
lean_ctor_set(v___x_587_, 0, v___x_636_);
v___x_638_ = v___x_587_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v___x_636_);
lean_ctor_set(v_reuseFailAlloc_641_, 1, v___x_635_);
v___x_638_ = v_reuseFailAlloc_641_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
lean_object* v___x_639_; lean_object* v___x_640_; 
lean_inc(v_a_576_);
v___x_639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_639_, 0, v_a_576_);
lean_ctor_set(v___x_639_, 1, v___x_638_);
v___x_640_ = lean_array_push(v___x_634_, v___x_639_);
v_a_570_ = v___x_640_;
goto v___jp_569_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_fst_596_, 2);
lean_dec_ref(v___x_595_);
lean_del_object(v___x_591_);
lean_del_object(v___x_587_);
v_a_570_ = v_b_563_;
goto v___jp_569_;
}
}
else
{
lean_dec(v_fst_596_);
lean_dec_ref(v___x_595_);
lean_del_object(v___x_591_);
lean_del_object(v___x_587_);
v_a_570_ = v_b_563_;
goto v___jp_569_;
}
}
else
{
lean_object* v_a_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_653_; 
lean_del_object(v___x_591_);
lean_del_object(v___x_587_);
lean_dec_ref(v_b_563_);
v_a_646_ = lean_ctor_get(v___x_593_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_653_ == 0)
{
v___x_648_ = v___x_593_;
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_a_646_);
lean_dec(v___x_593_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_651_; 
if (v_isShared_649_ == 0)
{
v___x_651_ = v___x_648_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_a_646_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
}
}
}
else
{
lean_object* v_a_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_665_; 
lean_dec_ref(v_b_563_);
v_a_658_ = lean_ctor_get(v___x_583_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_665_ == 0)
{
v___x_660_ = v___x_583_;
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_a_658_);
lean_dec(v___x_583_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_663_; 
if (v_isShared_661_ == 0)
{
v___x_663_ = v___x_660_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_a_658_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
}
else
{
lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_673_; 
lean_dec_ref(v_b_563_);
v_a_666_ = lean_ctor_get(v___x_579_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_673_ == 0)
{
v___x_668_ = v___x_579_;
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v___x_579_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_671_; 
if (v_isShared_669_ == 0)
{
v___x_671_ = v___x_668_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_a_666_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
}
else
{
v_a_570_ = v_b_563_;
goto v___jp_569_;
}
}
v___jp_569_:
{
size_t v___x_571_; size_t v___x_572_; 
v___x_571_ = ((size_t)1ULL);
v___x_572_ = lean_usize_add(v_i_562_, v___x_571_);
v_i_562_ = v___x_572_;
v_b_563_ = v_a_570_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_localHypotheses_spec__2___boxed(lean_object* v_except_674_, lean_object* v_as_675_, lean_object* v_sz_676_, lean_object* v_i_677_, lean_object* v_b_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
size_t v_sz_boxed_684_; size_t v_i_boxed_685_; lean_object* v_res_686_; 
v_sz_boxed_684_ = lean_unbox_usize(v_sz_676_);
lean_dec(v_sz_676_);
v_i_boxed_685_ = lean_unbox_usize(v_i_677_);
lean_dec(v_i_677_);
v_res_686_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_localHypotheses_spec__2(v_except_674_, v_as_675_, v_sz_boxed_684_, v_i_boxed_685_, v_b_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
lean_dec_ref(v_as_675_);
lean_dec(v_except_674_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(lean_object* v_as_687_, size_t v_sz_688_, size_t v_i_689_, lean_object* v_b_690_){
_start:
{
uint8_t v___x_692_; 
v___x_692_ = lean_usize_dec_lt(v_i_689_, v_sz_688_);
if (v___x_692_ == 0)
{
lean_object* v___x_693_; 
v___x_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_693_, 0, v_b_690_);
return v___x_693_;
}
else
{
lean_object* v_snd_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_712_; 
v_snd_694_ = lean_ctor_get(v_b_690_, 1);
v_isSharedCheck_712_ = !lean_is_exclusive(v_b_690_);
if (v_isSharedCheck_712_ == 0)
{
lean_object* v_unused_713_; 
v_unused_713_ = lean_ctor_get(v_b_690_, 0);
lean_dec(v_unused_713_);
v___x_696_ = v_b_690_;
v_isShared_697_ = v_isSharedCheck_712_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_snd_694_);
lean_dec(v_b_690_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_712_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_698_; lean_object* v_a_700_; lean_object* v_a_707_; 
v___x_698_ = lean_box(0);
v_a_707_ = lean_array_uget_borrowed(v_as_687_, v_i_689_);
if (lean_obj_tag(v_a_707_) == 0)
{
v_a_700_ = v_snd_694_;
goto v___jp_699_;
}
else
{
lean_object* v_val_708_; uint8_t v___x_709_; 
v_val_708_ = lean_ctor_get(v_a_707_, 0);
v___x_709_ = l_Lean_LocalDecl_isImplementationDetail(v_val_708_);
if (v___x_709_ == 0)
{
lean_object* v___x_710_; lean_object* v___x_711_; 
lean_inc(v_val_708_);
v___x_710_ = l_Lean_LocalDecl_toExpr(v_val_708_);
v___x_711_ = lean_array_push(v_snd_694_, v___x_710_);
v_a_700_ = v___x_711_;
goto v___jp_699_;
}
else
{
v_a_700_ = v_snd_694_;
goto v___jp_699_;
}
}
v___jp_699_:
{
lean_object* v___x_702_; 
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 1, v_a_700_);
lean_ctor_set(v___x_696_, 0, v___x_698_);
v___x_702_ = v___x_696_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_698_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v_a_700_);
v___x_702_ = v_reuseFailAlloc_706_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
size_t v___x_703_; size_t v___x_704_; 
v___x_703_ = ((size_t)1ULL);
v___x_704_ = lean_usize_add(v_i_689_, v___x_703_);
v_i_689_ = v___x_704_;
v_b_690_ = v___x_702_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___redArg___boxed(lean_object* v_as_714_, lean_object* v_sz_715_, lean_object* v_i_716_, lean_object* v_b_717_, lean_object* v___y_718_){
_start:
{
size_t v_sz_boxed_719_; size_t v_i_boxed_720_; lean_object* v_res_721_; 
v_sz_boxed_719_ = lean_unbox_usize(v_sz_715_);
lean_dec(v_sz_715_);
v_i_boxed_720_ = lean_unbox_usize(v_i_716_);
lean_dec(v_i_716_);
v_res_721_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(v_as_714_, v_sz_boxed_719_, v_i_boxed_720_, v_b_717_);
lean_dec_ref(v_as_714_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5(lean_object* v_as_722_, size_t v_sz_723_, size_t v_i_724_, lean_object* v_b_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
uint8_t v___x_731_; 
v___x_731_ = lean_usize_dec_lt(v_i_724_, v_sz_723_);
if (v___x_731_ == 0)
{
lean_object* v___x_732_; 
v___x_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_732_, 0, v_b_725_);
return v___x_732_;
}
else
{
lean_object* v_snd_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_751_; 
v_snd_733_ = lean_ctor_get(v_b_725_, 1);
v_isSharedCheck_751_ = !lean_is_exclusive(v_b_725_);
if (v_isSharedCheck_751_ == 0)
{
lean_object* v_unused_752_; 
v_unused_752_ = lean_ctor_get(v_b_725_, 0);
lean_dec(v_unused_752_);
v___x_735_ = v_b_725_;
v_isShared_736_ = v_isSharedCheck_751_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_snd_733_);
lean_dec(v_b_725_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_751_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_737_; lean_object* v_a_739_; lean_object* v_a_746_; 
v___x_737_ = lean_box(0);
v_a_746_ = lean_array_uget_borrowed(v_as_722_, v_i_724_);
if (lean_obj_tag(v_a_746_) == 0)
{
v_a_739_ = v_snd_733_;
goto v___jp_738_;
}
else
{
lean_object* v_val_747_; uint8_t v___x_748_; 
v_val_747_ = lean_ctor_get(v_a_746_, 0);
v___x_748_ = l_Lean_LocalDecl_isImplementationDetail(v_val_747_);
if (v___x_748_ == 0)
{
lean_object* v___x_749_; lean_object* v___x_750_; 
lean_inc(v_val_747_);
v___x_749_ = l_Lean_LocalDecl_toExpr(v_val_747_);
v___x_750_ = lean_array_push(v_snd_733_, v___x_749_);
v_a_739_ = v___x_750_;
goto v___jp_738_;
}
else
{
v_a_739_ = v_snd_733_;
goto v___jp_738_;
}
}
v___jp_738_:
{
lean_object* v___x_741_; 
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 1, v_a_739_);
lean_ctor_set(v___x_735_, 0, v___x_737_);
v___x_741_ = v___x_735_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_737_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v_a_739_);
v___x_741_ = v_reuseFailAlloc_745_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
size_t v___x_742_; size_t v___x_743_; lean_object* v___x_744_; 
v___x_742_ = ((size_t)1ULL);
v___x_743_ = lean_usize_add(v_i_724_, v___x_742_);
v___x_744_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(v_as_722_, v_sz_723_, v___x_743_, v___x_741_);
return v___x_744_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5___boxed(lean_object* v_as_753_, lean_object* v_sz_754_, lean_object* v_i_755_, lean_object* v_b_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_){
_start:
{
size_t v_sz_boxed_762_; size_t v_i_boxed_763_; lean_object* v_res_764_; 
v_sz_boxed_762_ = lean_unbox_usize(v_sz_754_);
lean_dec(v_sz_754_);
v_i_boxed_763_ = lean_unbox_usize(v_i_755_);
lean_dec(v_i_755_);
v_res_764_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5(v_as_753_, v_sz_boxed_762_, v_i_boxed_763_, v_b_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_757_);
lean_dec_ref(v_as_753_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2(lean_object* v_init_765_, lean_object* v_n_766_, lean_object* v_b_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_){
_start:
{
if (lean_obj_tag(v_n_766_) == 0)
{
lean_object* v_cs_773_; lean_object* v___x_774_; lean_object* v___x_775_; size_t v_sz_776_; size_t v___x_777_; lean_object* v___x_778_; 
v_cs_773_ = lean_ctor_get(v_n_766_, 0);
v___x_774_ = lean_box(0);
v___x_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_775_, 0, v___x_774_);
lean_ctor_set(v___x_775_, 1, v_b_767_);
v_sz_776_ = lean_array_size(v_cs_773_);
v___x_777_ = ((size_t)0ULL);
v___x_778_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__4(v_init_765_, v_cs_773_, v_sz_776_, v___x_777_, v___x_775_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
if (lean_obj_tag(v___x_778_) == 0)
{
lean_object* v_a_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_793_; 
v_a_779_ = lean_ctor_get(v___x_778_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_793_ == 0)
{
v___x_781_ = v___x_778_;
v_isShared_782_ = v_isSharedCheck_793_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_dec(v___x_778_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_793_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v_fst_783_; 
v_fst_783_ = lean_ctor_get(v_a_779_, 0);
if (lean_obj_tag(v_fst_783_) == 0)
{
lean_object* v_snd_784_; lean_object* v___x_785_; lean_object* v___x_787_; 
v_snd_784_ = lean_ctor_get(v_a_779_, 1);
lean_inc(v_snd_784_);
lean_dec(v_a_779_);
v___x_785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_785_, 0, v_snd_784_);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 0, v___x_785_);
v___x_787_ = v___x_781_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v___x_785_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
return v___x_787_;
}
}
else
{
lean_object* v_val_789_; lean_object* v___x_791_; 
lean_inc_ref(v_fst_783_);
lean_dec(v_a_779_);
v_val_789_ = lean_ctor_get(v_fst_783_, 0);
lean_inc(v_val_789_);
lean_dec_ref_known(v_fst_783_, 1);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 0, v_val_789_);
v___x_791_ = v___x_781_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_val_789_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
else
{
lean_object* v_a_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_801_; 
v_a_794_ = lean_ctor_get(v___x_778_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_801_ == 0)
{
v___x_796_ = v___x_778_;
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_a_794_);
lean_dec(v___x_778_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_799_; 
if (v_isShared_797_ == 0)
{
v___x_799_ = v___x_796_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_a_794_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
}
else
{
lean_object* v_vs_802_; lean_object* v___x_803_; lean_object* v___x_804_; size_t v_sz_805_; size_t v___x_806_; lean_object* v___x_807_; 
v_vs_802_ = lean_ctor_get(v_n_766_, 0);
v___x_803_ = lean_box(0);
v___x_804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_804_, 0, v___x_803_);
lean_ctor_set(v___x_804_, 1, v_b_767_);
v_sz_805_ = lean_array_size(v_vs_802_);
v___x_806_ = ((size_t)0ULL);
v___x_807_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5(v_vs_802_, v_sz_805_, v___x_806_, v___x_804_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
if (lean_obj_tag(v___x_807_) == 0)
{
lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_822_; 
v_a_808_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_822_ == 0)
{
v___x_810_ = v___x_807_;
v_isShared_811_ = v_isSharedCheck_822_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_807_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_822_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v_fst_812_; 
v_fst_812_ = lean_ctor_get(v_a_808_, 0);
if (lean_obj_tag(v_fst_812_) == 0)
{
lean_object* v_snd_813_; lean_object* v___x_814_; lean_object* v___x_816_; 
v_snd_813_ = lean_ctor_get(v_a_808_, 1);
lean_inc(v_snd_813_);
lean_dec(v_a_808_);
v___x_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_814_, 0, v_snd_813_);
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 0, v___x_814_);
v___x_816_ = v___x_810_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_814_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
else
{
lean_object* v_val_818_; lean_object* v___x_820_; 
lean_inc_ref(v_fst_812_);
lean_dec(v_a_808_);
v_val_818_ = lean_ctor_get(v_fst_812_, 0);
lean_inc(v_val_818_);
lean_dec_ref_known(v_fst_812_, 1);
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 0, v_val_818_);
v___x_820_ = v___x_810_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_val_818_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
}
else
{
lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_830_; 
v_a_823_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_830_ == 0)
{
v___x_825_ = v___x_807_;
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___x_807_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_828_; 
if (v_isShared_826_ == 0)
{
v___x_828_ = v___x_825_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_a_823_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__4(lean_object* v_init_831_, lean_object* v_as_832_, size_t v_sz_833_, size_t v_i_834_, lean_object* v_b_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
uint8_t v___x_841_; 
v___x_841_ = lean_usize_dec_lt(v_i_834_, v_sz_833_);
if (v___x_841_ == 0)
{
lean_object* v___x_842_; 
v___x_842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_842_, 0, v_b_835_);
return v___x_842_;
}
else
{
lean_object* v_snd_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_877_; 
v_snd_843_ = lean_ctor_get(v_b_835_, 1);
v_isSharedCheck_877_ = !lean_is_exclusive(v_b_835_);
if (v_isSharedCheck_877_ == 0)
{
lean_object* v_unused_878_; 
v_unused_878_ = lean_ctor_get(v_b_835_, 0);
lean_dec(v_unused_878_);
v___x_845_ = v_b_835_;
v_isShared_846_ = v_isSharedCheck_877_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_snd_843_);
lean_dec(v_b_835_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_877_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v_a_847_; lean_object* v___x_848_; 
v_a_847_ = lean_array_uget_borrowed(v_as_832_, v_i_834_);
lean_inc(v_snd_843_);
v___x_848_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2(v_init_831_, v_a_847_, v_snd_843_, v___y_836_, v___y_837_, v___y_838_, v___y_839_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_868_; 
v_a_849_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_868_ == 0)
{
v___x_851_ = v___x_848_;
v_isShared_852_ = v_isSharedCheck_868_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_848_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_868_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
if (lean_obj_tag(v_a_849_) == 0)
{
lean_object* v___x_853_; lean_object* v___x_855_; 
v___x_853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_853_, 0, v_a_849_);
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 0, v___x_853_);
v___x_855_ = v___x_845_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v___x_853_);
lean_ctor_set(v_reuseFailAlloc_859_, 1, v_snd_843_);
v___x_855_ = v_reuseFailAlloc_859_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
lean_object* v___x_857_; 
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 0, v___x_855_);
v___x_857_ = v___x_851_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v___x_855_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
else
{
lean_object* v_a_860_; lean_object* v___x_861_; lean_object* v___x_863_; 
lean_del_object(v___x_851_);
lean_dec(v_snd_843_);
v_a_860_ = lean_ctor_get(v_a_849_, 0);
lean_inc(v_a_860_);
lean_dec_ref_known(v_a_849_, 1);
v___x_861_ = lean_box(0);
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 1, v_a_860_);
lean_ctor_set(v___x_845_, 0, v___x_861_);
v___x_863_ = v___x_845_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v___x_861_);
lean_ctor_set(v_reuseFailAlloc_867_, 1, v_a_860_);
v___x_863_ = v_reuseFailAlloc_867_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
size_t v___x_864_; size_t v___x_865_; 
v___x_864_ = ((size_t)1ULL);
v___x_865_ = lean_usize_add(v_i_834_, v___x_864_);
v_i_834_ = v___x_865_;
v_b_835_ = v___x_863_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_876_; 
lean_del_object(v___x_845_);
lean_dec(v_snd_843_);
v_a_869_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_876_ == 0)
{
v___x_871_ = v___x_848_;
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___x_848_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_874_; 
if (v_isShared_872_ == 0)
{
v___x_874_ = v___x_871_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_a_869_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_init_879_, lean_object* v_as_880_, lean_object* v_sz_881_, lean_object* v_i_882_, lean_object* v_b_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_){
_start:
{
size_t v_sz_boxed_889_; size_t v_i_boxed_890_; lean_object* v_res_891_; 
v_sz_boxed_889_ = lean_unbox_usize(v_sz_881_);
lean_dec(v_sz_881_);
v_i_boxed_890_ = lean_unbox_usize(v_i_882_);
lean_dec(v_i_882_);
v_res_891_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__4(v_init_879_, v_as_880_, v_sz_boxed_889_, v_i_boxed_890_, v_b_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
lean_dec(v___y_885_);
lean_dec_ref(v___y_884_);
lean_dec_ref(v_as_880_);
lean_dec_ref(v_init_879_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2___boxed(lean_object* v_init_892_, lean_object* v_n_893_, lean_object* v_b_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2(v_init_892_, v_n_893_, v_b_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
lean_dec_ref(v_n_893_);
lean_dec_ref(v_init_892_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___redArg(lean_object* v_as_901_, size_t v_sz_902_, size_t v_i_903_, lean_object* v_b_904_){
_start:
{
uint8_t v___x_906_; 
v___x_906_ = lean_usize_dec_lt(v_i_903_, v_sz_902_);
if (v___x_906_ == 0)
{
lean_object* v___x_907_; 
v___x_907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_907_, 0, v_b_904_);
return v___x_907_;
}
else
{
lean_object* v_snd_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_926_; 
v_snd_908_ = lean_ctor_get(v_b_904_, 1);
v_isSharedCheck_926_ = !lean_is_exclusive(v_b_904_);
if (v_isSharedCheck_926_ == 0)
{
lean_object* v_unused_927_; 
v_unused_927_ = lean_ctor_get(v_b_904_, 0);
lean_dec(v_unused_927_);
v___x_910_ = v_b_904_;
v_isShared_911_ = v_isSharedCheck_926_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_snd_908_);
lean_dec(v_b_904_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_926_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_912_; lean_object* v_a_914_; lean_object* v_a_921_; 
v___x_912_ = lean_box(0);
v_a_921_ = lean_array_uget_borrowed(v_as_901_, v_i_903_);
if (lean_obj_tag(v_a_921_) == 0)
{
v_a_914_ = v_snd_908_;
goto v___jp_913_;
}
else
{
lean_object* v_val_922_; uint8_t v___x_923_; 
v_val_922_ = lean_ctor_get(v_a_921_, 0);
v___x_923_ = l_Lean_LocalDecl_isImplementationDetail(v_val_922_);
if (v___x_923_ == 0)
{
lean_object* v___x_924_; lean_object* v___x_925_; 
lean_inc(v_val_922_);
v___x_924_ = l_Lean_LocalDecl_toExpr(v_val_922_);
v___x_925_ = lean_array_push(v_snd_908_, v___x_924_);
v_a_914_ = v___x_925_;
goto v___jp_913_;
}
else
{
v_a_914_ = v_snd_908_;
goto v___jp_913_;
}
}
v___jp_913_:
{
lean_object* v___x_916_; 
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 1, v_a_914_);
lean_ctor_set(v___x_910_, 0, v___x_912_);
v___x_916_ = v___x_910_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_912_);
lean_ctor_set(v_reuseFailAlloc_920_, 1, v_a_914_);
v___x_916_ = v_reuseFailAlloc_920_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
size_t v___x_917_; size_t v___x_918_; 
v___x_917_ = ((size_t)1ULL);
v___x_918_ = lean_usize_add(v_i_903_, v___x_917_);
v_i_903_ = v___x_918_;
v_b_904_ = v___x_916_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_as_928_, lean_object* v_sz_929_, lean_object* v_i_930_, lean_object* v_b_931_, lean_object* v___y_932_){
_start:
{
size_t v_sz_boxed_933_; size_t v_i_boxed_934_; lean_object* v_res_935_; 
v_sz_boxed_933_ = lean_unbox_usize(v_sz_929_);
lean_dec(v_sz_929_);
v_i_boxed_934_ = lean_unbox_usize(v_i_930_);
lean_dec(v_i_930_);
v_res_935_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___redArg(v_as_928_, v_sz_boxed_933_, v_i_boxed_934_, v_b_931_);
lean_dec_ref(v_as_928_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3(lean_object* v_as_936_, size_t v_sz_937_, size_t v_i_938_, lean_object* v_b_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
uint8_t v___x_945_; 
v___x_945_ = lean_usize_dec_lt(v_i_938_, v_sz_937_);
if (v___x_945_ == 0)
{
lean_object* v___x_946_; 
v___x_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_946_, 0, v_b_939_);
return v___x_946_;
}
else
{
lean_object* v_snd_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_965_; 
v_snd_947_ = lean_ctor_get(v_b_939_, 1);
v_isSharedCheck_965_ = !lean_is_exclusive(v_b_939_);
if (v_isSharedCheck_965_ == 0)
{
lean_object* v_unused_966_; 
v_unused_966_ = lean_ctor_get(v_b_939_, 0);
lean_dec(v_unused_966_);
v___x_949_ = v_b_939_;
v_isShared_950_ = v_isSharedCheck_965_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_snd_947_);
lean_dec(v_b_939_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_965_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_951_; lean_object* v_a_953_; lean_object* v_a_960_; 
v___x_951_ = lean_box(0);
v_a_960_ = lean_array_uget_borrowed(v_as_936_, v_i_938_);
if (lean_obj_tag(v_a_960_) == 0)
{
v_a_953_ = v_snd_947_;
goto v___jp_952_;
}
else
{
lean_object* v_val_961_; uint8_t v___x_962_; 
v_val_961_ = lean_ctor_get(v_a_960_, 0);
v___x_962_ = l_Lean_LocalDecl_isImplementationDetail(v_val_961_);
if (v___x_962_ == 0)
{
lean_object* v___x_963_; lean_object* v___x_964_; 
lean_inc(v_val_961_);
v___x_963_ = l_Lean_LocalDecl_toExpr(v_val_961_);
v___x_964_ = lean_array_push(v_snd_947_, v___x_963_);
v_a_953_ = v___x_964_;
goto v___jp_952_;
}
else
{
v_a_953_ = v_snd_947_;
goto v___jp_952_;
}
}
v___jp_952_:
{
lean_object* v___x_955_; 
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 1, v_a_953_);
lean_ctor_set(v___x_949_, 0, v___x_951_);
v___x_955_ = v___x_949_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v___x_951_);
lean_ctor_set(v_reuseFailAlloc_959_, 1, v_a_953_);
v___x_955_ = v_reuseFailAlloc_959_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
size_t v___x_956_; size_t v___x_957_; lean_object* v___x_958_; 
v___x_956_ = ((size_t)1ULL);
v___x_957_ = lean_usize_add(v_i_938_, v___x_956_);
v___x_958_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___redArg(v_as_936_, v_sz_937_, v___x_957_, v___x_955_);
return v___x_958_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3___boxed(lean_object* v_as_967_, lean_object* v_sz_968_, lean_object* v_i_969_, lean_object* v_b_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
size_t v_sz_boxed_976_; size_t v_i_boxed_977_; lean_object* v_res_978_; 
v_sz_boxed_976_ = lean_unbox_usize(v_sz_968_);
lean_dec(v_sz_968_);
v_i_boxed_977_ = lean_unbox_usize(v_i_969_);
lean_dec(v_i_969_);
v_res_978_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3(v_as_967_, v_sz_boxed_976_, v_i_boxed_977_, v_b_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
lean_dec_ref(v_as_967_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1(lean_object* v_t_979_, lean_object* v_init_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
lean_object* v_root_986_; lean_object* v_tail_987_; lean_object* v___x_988_; 
v_root_986_ = lean_ctor_get(v_t_979_, 0);
v_tail_987_ = lean_ctor_get(v_t_979_, 1);
lean_inc_ref(v_init_980_);
v___x_988_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2(v_init_980_, v_root_986_, v_init_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_);
lean_dec_ref(v_init_980_);
if (lean_obj_tag(v___x_988_) == 0)
{
lean_object* v_a_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_1025_; 
v_a_989_ = lean_ctor_get(v___x_988_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_991_ = v___x_988_;
v_isShared_992_ = v_isSharedCheck_1025_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_a_989_);
lean_dec(v___x_988_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_1025_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
if (lean_obj_tag(v_a_989_) == 0)
{
lean_object* v_a_993_; lean_object* v___x_995_; 
v_a_993_ = lean_ctor_get(v_a_989_, 0);
lean_inc(v_a_993_);
lean_dec_ref_known(v_a_989_, 1);
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 0, v_a_993_);
v___x_995_ = v___x_991_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_a_993_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
else
{
lean_object* v_a_997_; lean_object* v___x_998_; lean_object* v___x_999_; size_t v_sz_1000_; size_t v___x_1001_; lean_object* v___x_1002_; 
lean_del_object(v___x_991_);
v_a_997_ = lean_ctor_get(v_a_989_, 0);
lean_inc(v_a_997_);
lean_dec_ref_known(v_a_989_, 1);
v___x_998_ = lean_box(0);
v___x_999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_998_);
lean_ctor_set(v___x_999_, 1, v_a_997_);
v_sz_1000_ = lean_array_size(v_tail_987_);
v___x_1001_ = ((size_t)0ULL);
v___x_1002_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3(v_tail_987_, v_sz_1000_, v___x_1001_, v___x_999_, v___y_981_, v___y_982_, v___y_983_, v___y_984_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1016_; 
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_1005_ = v___x_1002_;
v_isShared_1006_ = v_isSharedCheck_1016_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_1002_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1016_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v_fst_1007_; 
v_fst_1007_ = lean_ctor_get(v_a_1003_, 0);
if (lean_obj_tag(v_fst_1007_) == 0)
{
lean_object* v_snd_1008_; lean_object* v___x_1010_; 
v_snd_1008_ = lean_ctor_get(v_a_1003_, 1);
lean_inc(v_snd_1008_);
lean_dec(v_a_1003_);
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 0, v_snd_1008_);
v___x_1010_ = v___x_1005_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v_snd_1008_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
else
{
lean_object* v_val_1012_; lean_object* v___x_1014_; 
lean_inc_ref(v_fst_1007_);
lean_dec(v_a_1003_);
v_val_1012_ = lean_ctor_get(v_fst_1007_, 0);
lean_inc(v_val_1012_);
lean_dec_ref_known(v_fst_1007_, 1);
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 0, v_val_1012_);
v___x_1014_ = v___x_1005_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_val_1012_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
}
}
else
{
lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1024_; 
v_a_1017_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1019_ = v___x_1002_;
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_a_1017_);
lean_dec(v___x_1002_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1022_; 
if (v_isShared_1020_ == 0)
{
v___x_1022_ = v___x_1019_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_a_1017_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
}
}
else
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1033_; 
v_a_1026_ = lean_ctor_get(v___x_988_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1028_ = v___x_988_;
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_988_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1031_; 
if (v_isShared_1029_ == 0)
{
v___x_1031_ = v___x_1028_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_a_1026_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1___boxed(lean_object* v_t_1034_, lean_object* v_init_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1(v_t_1034_, v_init_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
lean_dec(v___y_1037_);
lean_dec_ref(v___y_1036_);
lean_dec_ref(v_t_1034_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1(lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_){
_start:
{
lean_object* v_lctx_1049_; lean_object* v_decls_1050_; lean_object* v_hs_1051_; lean_object* v___x_1052_; 
v_lctx_1049_ = lean_ctor_get(v___y_1044_, 2);
v_decls_1050_ = lean_ctor_get(v_lctx_1049_, 1);
v_hs_1051_ = ((lean_object*)(l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1___closed__0));
v___x_1052_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1(v_decls_1050_, v_hs_1051_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1___boxed(lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1(v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_);
lean_dec(v___y_1056_);
lean_dec_ref(v___y_1055_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_localHypotheses(lean_object* v_except_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_){
_start:
{
lean_object* v___x_1067_; 
v___x_1067_ = l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1(v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_);
if (lean_obj_tag(v___x_1067_) == 0)
{
lean_object* v_a_1068_; lean_object* v___x_1069_; size_t v_sz_1070_; size_t v___x_1071_; lean_object* v___x_1072_; 
v_a_1068_ = lean_ctor_get(v___x_1067_, 0);
lean_inc(v_a_1068_);
lean_dec_ref_known(v___x_1067_, 1);
v___x_1069_ = ((lean_object*)(l_Lean_Meta_Rewrites_localHypotheses___closed__0));
v_sz_1070_ = lean_array_size(v_a_1068_);
v___x_1071_ = ((size_t)0ULL);
v___x_1072_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_localHypotheses_spec__2(v_except_1061_, v_a_1068_, v_sz_1070_, v___x_1071_, v___x_1069_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_);
lean_dec(v_a_1068_);
return v___x_1072_;
}
else
{
lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1080_; 
v_a_1073_ = lean_ctor_get(v___x_1067_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1075_ = v___x_1067_;
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_1067_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_localHypotheses___boxed(lean_object* v_except_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l_Lean_Meta_Rewrites_localHypotheses(v_except_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_);
lean_dec(v_a_1085_);
lean_dec_ref(v_a_1084_);
lean_dec(v_a_1083_);
lean_dec_ref(v_a_1082_);
lean_dec(v_except_1081_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7(lean_object* v_as_1088_, size_t v_sz_1089_, size_t v_i_1090_, lean_object* v_b_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_){
_start:
{
lean_object* v___x_1097_; 
v___x_1097_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___redArg(v_as_1088_, v_sz_1089_, v_i_1090_, v_b_1091_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___boxed(lean_object* v_as_1098_, lean_object* v_sz_1099_, lean_object* v_i_1100_, lean_object* v_b_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_){
_start:
{
size_t v_sz_boxed_1107_; size_t v_i_boxed_1108_; lean_object* v_res_1109_; 
v_sz_boxed_1107_ = lean_unbox_usize(v_sz_1099_);
lean_dec(v_sz_1099_);
v_i_boxed_1108_ = lean_unbox_usize(v_i_1100_);
lean_dec(v_i_1100_);
v_res_1109_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7(v_as_1098_, v_sz_boxed_1107_, v_i_boxed_1108_, v_b_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
lean_dec_ref(v_as_1098_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6(lean_object* v_as_1110_, size_t v_sz_1111_, size_t v_i_1112_, lean_object* v_b_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
lean_object* v___x_1119_; 
v___x_1119_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(v_as_1110_, v_sz_1111_, v_i_1112_, v_b_1113_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___boxed(lean_object* v_as_1120_, lean_object* v_sz_1121_, lean_object* v_i_1122_, lean_object* v_b_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_){
_start:
{
size_t v_sz_boxed_1129_; size_t v_i_boxed_1130_; lean_object* v_res_1131_; 
v_sz_boxed_1129_ = lean_unbox_usize(v_sz_1121_);
lean_dec(v_sz_1121_);
v_i_boxed_1130_ = lean_unbox_usize(v_i_1122_);
lean_dec(v_i_1122_);
v_res_1131_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6(v_as_1120_, v_sz_boxed_1129_, v_i_boxed_1130_, v_b_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec_ref(v_as_1120_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_createModuleTreeRef(lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_){
_start:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1162_ = ((lean_object*)(l_Lean_Meta_Rewrites_createModuleTreeRef___closed__0));
v___x_1163_ = ((lean_object*)(l_Lean_Meta_Rewrites_droppedKeys));
v___x_1164_ = lean_box(0);
v___x_1165_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v___x_1162_, v___x_1163_, v___x_1164_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_createModuleTreeRef___boxed(lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_Lean_Meta_Rewrites_createModuleTreeRef(v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
lean_dec(v_a_1169_);
lean_dec_ref(v_a_1168_);
lean_dec(v_a_1167_);
lean_dec_ref(v_a_1166_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_1824551397____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1173_ = lean_box(0);
v___x_1174_ = lean_st_mk_ref(v___x_1173_);
v___x_1175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1174_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_1824551397____hygCtx___hyg_2____boxed(lean_object* v_a_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_1824551397____hygCtx___hyg_2_();
return v_res_1177_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_constantsPerImportTask(void){
_start:
{
lean_object* v___x_1178_; 
v___x_1178_ = lean_unsigned_to_nat(6500u);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_incPrio(lean_object* v_x_1179_, lean_object* v_x_1180_){
_start:
{
lean_object* v_snd_1181_; uint8_t v___x_1182_; 
v_snd_1181_ = lean_ctor_get(v_x_1180_, 1);
v___x_1182_ = lean_unbox(v_snd_1181_);
if (v___x_1182_ == 0)
{
lean_object* v_fst_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1195_; 
v_fst_1183_ = lean_ctor_get(v_x_1180_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v_x_1180_);
if (v_isSharedCheck_1195_ == 0)
{
lean_object* v_unused_1196_; 
v_unused_1196_ = lean_ctor_get(v_x_1180_, 1);
lean_dec(v_unused_1196_);
v___x_1185_ = v_x_1180_;
v_isShared_1186_ = v_isSharedCheck_1195_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_fst_1183_);
lean_dec(v_x_1180_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1195_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
uint8_t v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1192_; 
v___x_1187_ = 0;
v___x_1188_ = lean_unsigned_to_nat(2u);
v___x_1189_ = lean_nat_mul(v___x_1188_, v_x_1179_);
lean_dec(v_x_1179_);
v___x_1190_ = lean_box(v___x_1187_);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 1, v___x_1189_);
lean_ctor_set(v___x_1185_, 0, v___x_1190_);
v___x_1192_ = v___x_1185_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v___x_1190_);
lean_ctor_set(v_reuseFailAlloc_1194_, 1, v___x_1189_);
v___x_1192_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
lean_object* v___x_1193_; 
v___x_1193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1193_, 0, v_fst_1183_);
lean_ctor_set(v___x_1193_, 1, v___x_1192_);
return v___x_1193_;
}
}
}
else
{
lean_object* v_fst_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1207_; 
v_fst_1197_ = lean_ctor_get(v_x_1180_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v_x_1180_);
if (v_isSharedCheck_1207_ == 0)
{
lean_object* v_unused_1208_; 
v_unused_1208_ = lean_ctor_get(v_x_1180_, 1);
lean_dec(v_unused_1208_);
v___x_1199_ = v_x_1180_;
v_isShared_1200_ = v_isSharedCheck_1207_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_fst_1197_);
lean_dec(v_x_1180_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1207_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
uint8_t v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1204_; 
v___x_1201_ = 1;
v___x_1202_ = lean_box(v___x_1201_);
if (v_isShared_1200_ == 0)
{
lean_ctor_set(v___x_1199_, 1, v_x_1179_);
lean_ctor_set(v___x_1199_, 0, v___x_1202_);
v___x_1204_ = v___x_1199_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v___x_1202_);
lean_ctor_set(v_reuseFailAlloc_1206_, 1, v_x_1179_);
v___x_1204_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
lean_object* v___x_1205_; 
v___x_1205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1205_, 0, v_fst_1197_);
lean_ctor_set(v___x_1205_, 1, v___x_1204_);
return v___x_1205_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwFindDecls(lean_object* v_moduleRef_1210_, lean_object* v_ty_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1217_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_ext;
v___x_1218_ = ((lean_object*)(l_Lean_Meta_Rewrites_createModuleTreeRef___closed__0));
v___x_1219_ = ((lean_object*)(l_Lean_Meta_Rewrites_droppedKeys));
v___x_1220_ = lean_unsigned_to_nat(6500u);
v___x_1221_ = lean_box(0);
v___x_1222_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwFindDecls___closed__0));
v___x_1223_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_moduleRef_1210_, v___x_1217_, v___x_1218_, v___x_1219_, v___x_1220_, v___x_1221_, v___x_1222_, v_ty_1211_, v_a_1212_, v_a_1213_, v_a_1214_, v_a_1215_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwFindDecls___boxed(lean_object* v_moduleRef_1224_, lean_object* v_ty_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l_Lean_Meta_Rewrites_rwFindDecls(v_moduleRef_1224_, v_ty_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_);
lean_dec(v_a_1229_);
lean_dec_ref(v_a_1228_);
lean_dec(v_a_1227_);
lean_dec_ref(v_a_1226_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg(lean_object* v_mctx_1232_, lean_object* v_x_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
lean_object* v___x_1239_; 
v___x_1239_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp(lean_box(0), v_mctx_1232_, v_x_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_);
if (lean_obj_tag(v___x_1239_) == 0)
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1247_; 
v_a_1240_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1242_ = v___x_1239_;
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1239_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1245_; 
if (v_isShared_1243_ == 0)
{
v___x_1245_ = v___x_1242_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_a_1240_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
else
{
lean_object* v_a_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1255_; 
v_a_1248_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1250_ = v___x_1239_;
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_a_1248_);
lean_dec(v___x_1239_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1253_; 
if (v_isShared_1251_ == 0)
{
v___x_1253_ = v___x_1250_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_a_1248_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg___boxed(lean_object* v_mctx_1256_, lean_object* v_x_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg(v_mctx_1256_, v_x_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_);
lean_dec(v___y_1261_);
lean_dec_ref(v___y_1260_);
lean_dec(v___y_1259_);
lean_dec_ref(v___y_1258_);
return v_res_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0(lean_object* v_00_u03b1_1264_, lean_object* v_mctx_1265_, lean_object* v_x_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
lean_object* v___x_1272_; 
v___x_1272_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg(v_mctx_1265_, v_x_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___boxed(lean_object* v_00_u03b1_1273_, lean_object* v_mctx_1274_, lean_object* v_x_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0(v_00_u03b1_1273_, v_mctx_1274_, v_x_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(lean_object* v_x_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_){
_start:
{
lean_object* v___x_1288_; 
v___x_1288_ = l_Lean_Meta_saveState___redArg(v___y_1284_, v___y_1286_);
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_object* v_a_1289_; lean_object* v_r_1290_; 
v_a_1289_ = lean_ctor_get(v___x_1288_, 0);
lean_inc(v_a_1289_);
lean_dec_ref_known(v___x_1288_, 1);
lean_inc(v___y_1286_);
lean_inc_ref(v___y_1285_);
lean_inc(v___y_1284_);
lean_inc_ref(v___y_1283_);
v_r_1290_ = lean_apply_5(v_x_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, lean_box(0));
if (lean_obj_tag(v_r_1290_) == 0)
{
lean_object* v_a_1291_; lean_object* v___x_1292_; 
v_a_1291_ = lean_ctor_get(v_r_1290_, 0);
lean_inc(v_a_1291_);
lean_dec_ref_known(v_r_1290_, 1);
v___x_1292_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1289_, v___y_1284_, v___y_1286_);
lean_dec(v_a_1289_);
if (lean_obj_tag(v___x_1292_) == 0)
{
lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1299_; 
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1299_ == 0)
{
lean_object* v_unused_1300_; 
v_unused_1300_ = lean_ctor_get(v___x_1292_, 0);
lean_dec(v_unused_1300_);
v___x_1294_ = v___x_1292_;
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
else
{
lean_dec(v___x_1292_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1297_; 
if (v_isShared_1295_ == 0)
{
lean_ctor_set(v___x_1294_, 0, v_a_1291_);
v___x_1297_ = v___x_1294_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_a_1291_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
else
{
lean_object* v_a_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1308_; 
lean_dec(v_a_1291_);
v_a_1301_ = lean_ctor_get(v___x_1292_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1303_ = v___x_1292_;
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_a_1301_);
lean_dec(v___x_1292_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v___x_1306_; 
if (v_isShared_1304_ == 0)
{
v___x_1306_ = v___x_1303_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_a_1301_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
}
}
}
}
else
{
lean_object* v_a_1309_; lean_object* v___x_1310_; 
v_a_1309_ = lean_ctor_get(v_r_1290_, 0);
lean_inc(v_a_1309_);
lean_dec_ref_known(v_r_1290_, 1);
v___x_1310_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1289_, v___y_1284_, v___y_1286_);
lean_dec(v_a_1289_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1317_; 
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1317_ == 0)
{
lean_object* v_unused_1318_; 
v_unused_1318_ = lean_ctor_get(v___x_1310_, 0);
lean_dec(v_unused_1318_);
v___x_1312_ = v___x_1310_;
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
else
{
lean_dec(v___x_1310_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1315_; 
if (v_isShared_1313_ == 0)
{
lean_ctor_set_tag(v___x_1312_, 1);
lean_ctor_set(v___x_1312_, 0, v_a_1309_);
v___x_1315_ = v___x_1312_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_a_1309_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
}
else
{
lean_object* v_a_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1326_; 
lean_dec(v_a_1309_);
v_a_1319_ = lean_ctor_get(v___x_1310_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1321_ = v___x_1310_;
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_a_1319_);
lean_dec(v___x_1310_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1324_; 
if (v_isShared_1322_ == 0)
{
v___x_1324_ = v___x_1321_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_a_1319_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
}
}
else
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1334_; 
lean_dec_ref(v_x_1282_);
v_a_1327_ = lean_ctor_get(v___x_1288_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1288_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1329_ = v___x_1288_;
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1288_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1332_; 
if (v_isShared_1330_ == 0)
{
v___x_1332_ = v___x_1329_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_a_1327_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg___boxed(lean_object* v_x_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v_x_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1(lean_object* v_00_u03b1_1342_, lean_object* v_x_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_){
_start:
{
lean_object* v___x_1349_; 
v___x_1349_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v_x_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___boxed(lean_object* v_00_u03b1_1350_, lean_object* v_x_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_){
_start:
{
lean_object* v_res_1357_; 
v_res_1357_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1(v_00_u03b1_1350_, v_x_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
lean_dec(v___y_1355_);
lean_dec_ref(v___y_1354_);
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0(lean_object* v___x_1358_, uint8_t v___x_1359_, lean_object* v___x_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_){
_start:
{
lean_object* v___x_1366_; 
v___x_1366_ = l_Lean_Meta_mkFreshExprMVar(v___x_1358_, v___x_1359_, v___x_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_);
if (lean_obj_tag(v___x_1366_) == 0)
{
lean_object* v_a_1367_; lean_object* v_keyedConfig_1368_; uint8_t v_trackZetaDelta_1369_; lean_object* v_zetaDeltaSet_1370_; lean_object* v_lctx_1371_; lean_object* v_localInstances_1372_; lean_object* v_defEqCtx_x3f_1373_; lean_object* v_synthPendingDepth_1374_; lean_object* v_customCanUnfoldPredicate_x3f_1375_; uint8_t v_univApprox_1376_; uint8_t v_inTypeClassResolution_1377_; uint8_t v_cacheInferType_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1407_; 
v_a_1367_ = lean_ctor_get(v___x_1366_, 0);
lean_inc(v_a_1367_);
lean_dec_ref_known(v___x_1366_, 1);
v_keyedConfig_1368_ = lean_ctor_get(v___y_1361_, 0);
v_trackZetaDelta_1369_ = lean_ctor_get_uint8(v___y_1361_, sizeof(void*)*7);
v_zetaDeltaSet_1370_ = lean_ctor_get(v___y_1361_, 1);
v_lctx_1371_ = lean_ctor_get(v___y_1361_, 2);
v_localInstances_1372_ = lean_ctor_get(v___y_1361_, 3);
v_defEqCtx_x3f_1373_ = lean_ctor_get(v___y_1361_, 4);
v_synthPendingDepth_1374_ = lean_ctor_get(v___y_1361_, 5);
v_customCanUnfoldPredicate_x3f_1375_ = lean_ctor_get(v___y_1361_, 6);
v_univApprox_1376_ = lean_ctor_get_uint8(v___y_1361_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1377_ = lean_ctor_get_uint8(v___y_1361_, sizeof(void*)*7 + 2);
v_cacheInferType_1378_ = lean_ctor_get_uint8(v___y_1361_, sizeof(void*)*7 + 3);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___y_1361_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1380_ = v___y_1361_;
v_isShared_1381_ = v_isSharedCheck_1407_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_1375_);
lean_inc(v_synthPendingDepth_1374_);
lean_inc(v_defEqCtx_x3f_1373_);
lean_inc(v_localInstances_1372_);
lean_inc(v_lctx_1371_);
lean_inc(v_zetaDeltaSet_1370_);
lean_inc(v_keyedConfig_1368_);
lean_dec(v___y_1361_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1407_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1382_; uint8_t v___x_1383_; uint8_t v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1387_; 
v___x_1382_ = l_Lean_Expr_mvarId_x21(v_a_1367_);
lean_dec(v_a_1367_);
v___x_1383_ = 1;
v___x_1384_ = 2;
v___x_1385_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1384_, v_keyedConfig_1368_);
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 0, v___x_1385_);
v___x_1387_ = v___x_1380_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v___x_1385_);
lean_ctor_set(v_reuseFailAlloc_1406_, 1, v_zetaDeltaSet_1370_);
lean_ctor_set(v_reuseFailAlloc_1406_, 2, v_lctx_1371_);
lean_ctor_set(v_reuseFailAlloc_1406_, 3, v_localInstances_1372_);
lean_ctor_set(v_reuseFailAlloc_1406_, 4, v_defEqCtx_x3f_1373_);
lean_ctor_set(v_reuseFailAlloc_1406_, 5, v_synthPendingDepth_1374_);
lean_ctor_set(v_reuseFailAlloc_1406_, 6, v_customCanUnfoldPredicate_x3f_1375_);
lean_ctor_set_uint8(v_reuseFailAlloc_1406_, sizeof(void*)*7, v_trackZetaDelta_1369_);
lean_ctor_set_uint8(v_reuseFailAlloc_1406_, sizeof(void*)*7 + 1, v_univApprox_1376_);
lean_ctor_set_uint8(v_reuseFailAlloc_1406_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1377_);
lean_ctor_set_uint8(v_reuseFailAlloc_1406_, sizeof(void*)*7 + 3, v_cacheInferType_1378_);
v___x_1387_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
lean_object* v___x_1388_; 
v___x_1388_ = l_Lean_MVarId_refl(v___x_1382_, v___x_1383_, v___x_1387_, v___y_1362_, v___y_1363_, v___y_1364_);
lean_dec_ref(v___x_1387_);
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1396_; 
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1396_ == 0)
{
lean_object* v_unused_1397_; 
v_unused_1397_ = lean_ctor_get(v___x_1388_, 0);
lean_dec(v_unused_1397_);
v___x_1390_ = v___x_1388_;
v_isShared_1391_ = v_isSharedCheck_1396_;
goto v_resetjp_1389_;
}
else
{
lean_dec(v___x_1388_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1396_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1392_; lean_object* v___x_1394_; 
v___x_1392_ = lean_box(v___x_1383_);
if (v_isShared_1391_ == 0)
{
lean_ctor_set(v___x_1390_, 0, v___x_1392_);
v___x_1394_ = v___x_1390_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v___x_1392_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
}
else
{
lean_object* v_a_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1405_; 
v_a_1398_ = lean_ctor_get(v___x_1388_, 0);
v_isSharedCheck_1405_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1400_ = v___x_1388_;
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_a_1398_);
lean_dec(v___x_1388_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1403_; 
if (v_isShared_1401_ == 0)
{
v___x_1403_ = v___x_1400_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v_a_1398_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
}
}
}
}
else
{
lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1415_; 
lean_dec_ref(v___y_1361_);
v_a_1408_ = lean_ctor_get(v___x_1366_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1410_ = v___x_1366_;
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_a_1408_);
lean_dec(v___x_1366_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1413_; 
if (v_isShared_1411_ == 0)
{
v___x_1413_ = v___x_1410_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_a_1408_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___boxed(lean_object* v___x_1416_, lean_object* v___x_1417_, lean_object* v___x_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
uint8_t v___x_2168__boxed_1424_; lean_object* v_res_1425_; 
v___x_2168__boxed_1424_ = lean_unbox(v___x_1417_);
v_res_1425_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0(v___x_1416_, v___x_2168__boxed_1424_, v___x_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v___y_1420_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(lean_object* v_mctx_1426_, lean_object* v_e_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_){
_start:
{
lean_object* v___x_1433_; uint8_t v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___f_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; 
v___x_1433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1433_, 0, v_e_1427_);
v___x_1434_ = 0;
v___x_1435_ = lean_box(0);
v___x_1436_ = lean_box(v___x_1434_);
v___f_1437_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1437_, 0, v___x_1433_);
lean_closure_set(v___f_1437_, 1, v___x_1436_);
lean_closure_set(v___f_1437_, 2, v___x_1435_);
v___x_1438_ = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___boxed), 8, 3);
lean_closure_set(v___x_1438_, 0, lean_box(0));
lean_closure_set(v___x_1438_, 1, v_mctx_1426_);
lean_closure_set(v___x_1438_, 2, v___f_1437_);
v___x_1439_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v___x_1438_, v_a_1428_, v_a_1429_, v_a_1430_, v_a_1431_);
if (lean_obj_tag(v___x_1439_) == 0)
{
return v___x_1439_;
}
else
{
lean_object* v_a_1440_; uint8_t v___y_1442_; uint8_t v___x_1452_; 
v_a_1440_ = lean_ctor_get(v___x_1439_, 0);
lean_inc(v_a_1440_);
v___x_1452_ = l_Lean_Exception_isInterrupt(v_a_1440_);
if (v___x_1452_ == 0)
{
uint8_t v___x_1453_; 
v___x_1453_ = l_Lean_Exception_isRuntime(v_a_1440_);
v___y_1442_ = v___x_1453_;
goto v___jp_1441_;
}
else
{
lean_dec(v_a_1440_);
v___y_1442_ = v___x_1452_;
goto v___jp_1441_;
}
v___jp_1441_:
{
if (v___y_1442_ == 0)
{
lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1450_; 
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1439_);
if (v_isSharedCheck_1450_ == 0)
{
lean_object* v_unused_1451_; 
v_unused_1451_ = lean_ctor_get(v___x_1439_, 0);
lean_dec(v_unused_1451_);
v___x_1444_ = v___x_1439_;
v_isShared_1445_ = v_isSharedCheck_1450_;
goto v_resetjp_1443_;
}
else
{
lean_dec(v___x_1439_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1450_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1446_; lean_object* v___x_1448_; 
v___x_1446_ = lean_box(v___y_1442_);
if (v_isShared_1445_ == 0)
{
lean_ctor_set_tag(v___x_1444_, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1446_);
v___x_1448_ = v___x_1444_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v___x_1446_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
else
{
return v___x_1439_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___boxed(lean_object* v_mctx_1454_, lean_object* v_e_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_){
_start:
{
lean_object* v_res_1461_; 
v_res_1461_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(v_mctx_1454_, v_e_1455_, v_a_1456_, v_a_1457_, v_a_1458_, v_a_1459_);
lean_dec(v_a_1459_);
lean_dec_ref(v_a_1458_);
lean_dec(v_a_1457_);
lean_dec_ref(v_a_1456_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult(lean_object* v_r_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_){
_start:
{
lean_object* v_result_1468_; lean_object* v_eNew_1469_; lean_object* v___x_1470_; 
v_result_1468_ = lean_ctor_get(v_r_1462_, 2);
lean_inc_ref(v_result_1468_);
lean_dec_ref(v_r_1462_);
v_eNew_1469_ = lean_ctor_get(v_result_1468_, 0);
lean_inc_ref(v_eNew_1469_);
lean_dec_ref(v_result_1468_);
v___x_1470_ = l_Lean_Meta_ppExpr(v_eNew_1469_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1481_; 
v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1473_ = v___x_1470_;
v_isShared_1474_ = v_isSharedCheck_1481_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1470_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1481_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1479_; 
v___x_1475_ = l_Std_Format_defWidth;
v___x_1476_ = lean_unsigned_to_nat(0u);
v___x_1477_ = l_Std_Format_pretty(v_a_1471_, v___x_1475_, v___x_1476_, v___x_1476_);
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 0, v___x_1477_);
v___x_1479_ = v___x_1473_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v___x_1477_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
}
else
{
lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1489_; 
v_a_1482_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1484_ = v___x_1470_;
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v___x_1470_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1487_; 
if (v_isShared_1485_ == 0)
{
v___x_1487_ = v___x_1484_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_a_1482_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult___boxed(lean_object* v_r_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_){
_start:
{
lean_object* v_res_1496_; 
v_res_1496_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult(v_r_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_);
lean_dec(v_a_1494_);
lean_dec_ref(v_a_1493_);
lean_dec(v_a_1492_);
lean_dec_ref(v_a_1491_);
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorIdx(uint8_t v_x_1497_){
_start:
{
switch(v_x_1497_)
{
case 0:
{
lean_object* v___x_1498_; 
v___x_1498_ = lean_unsigned_to_nat(0u);
return v___x_1498_;
}
case 1:
{
lean_object* v___x_1499_; 
v___x_1499_ = lean_unsigned_to_nat(1u);
return v___x_1499_;
}
default: 
{
lean_object* v___x_1500_; 
v___x_1500_ = lean_unsigned_to_nat(2u);
return v___x_1500_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorIdx___boxed(lean_object* v_x_1501_){
_start:
{
uint8_t v_x_boxed_1502_; lean_object* v_res_1503_; 
v_x_boxed_1502_ = lean_unbox(v_x_1501_);
v_res_1503_ = l_Lean_Meta_Rewrites_SideConditions_ctorIdx(v_x_boxed_1502_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorElim___redArg(lean_object* v_k_1504_){
_start:
{
lean_inc(v_k_1504_);
return v_k_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorElim___redArg___boxed(lean_object* v_k_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l_Lean_Meta_Rewrites_SideConditions_ctorElim___redArg(v_k_1505_);
lean_dec(v_k_1505_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorElim(lean_object* v_motive_1507_, lean_object* v_ctorIdx_1508_, uint8_t v_t_1509_, lean_object* v_h_1510_, lean_object* v_k_1511_){
_start:
{
lean_inc(v_k_1511_);
return v_k_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorElim___boxed(lean_object* v_motive_1512_, lean_object* v_ctorIdx_1513_, lean_object* v_t_1514_, lean_object* v_h_1515_, lean_object* v_k_1516_){
_start:
{
uint8_t v_t_boxed_1517_; lean_object* v_res_1518_; 
v_t_boxed_1517_ = lean_unbox(v_t_1514_);
v_res_1518_ = l_Lean_Meta_Rewrites_SideConditions_ctorElim(v_motive_1512_, v_ctorIdx_1513_, v_t_boxed_1517_, v_h_1515_, v_k_1516_);
lean_dec(v_k_1516_);
lean_dec(v_ctorIdx_1513_);
return v_res_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_none_elim___redArg(lean_object* v_none_1519_){
_start:
{
lean_inc(v_none_1519_);
return v_none_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_none_elim___redArg___boxed(lean_object* v_none_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l_Lean_Meta_Rewrites_SideConditions_none_elim___redArg(v_none_1520_);
lean_dec(v_none_1520_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_none_elim(lean_object* v_motive_1522_, uint8_t v_t_1523_, lean_object* v_h_1524_, lean_object* v_none_1525_){
_start:
{
lean_inc(v_none_1525_);
return v_none_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_none_elim___boxed(lean_object* v_motive_1526_, lean_object* v_t_1527_, lean_object* v_h_1528_, lean_object* v_none_1529_){
_start:
{
uint8_t v_t_boxed_1530_; lean_object* v_res_1531_; 
v_t_boxed_1530_ = lean_unbox(v_t_1527_);
v_res_1531_ = l_Lean_Meta_Rewrites_SideConditions_none_elim(v_motive_1526_, v_t_boxed_1530_, v_h_1528_, v_none_1529_);
lean_dec(v_none_1529_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_assumption_elim___redArg(lean_object* v_assumption_1532_){
_start:
{
lean_inc(v_assumption_1532_);
return v_assumption_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_assumption_elim___redArg___boxed(lean_object* v_assumption_1533_){
_start:
{
lean_object* v_res_1534_; 
v_res_1534_ = l_Lean_Meta_Rewrites_SideConditions_assumption_elim___redArg(v_assumption_1533_);
lean_dec(v_assumption_1533_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_assumption_elim(lean_object* v_motive_1535_, uint8_t v_t_1536_, lean_object* v_h_1537_, lean_object* v_assumption_1538_){
_start:
{
lean_inc(v_assumption_1538_);
return v_assumption_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_assumption_elim___boxed(lean_object* v_motive_1539_, lean_object* v_t_1540_, lean_object* v_h_1541_, lean_object* v_assumption_1542_){
_start:
{
uint8_t v_t_boxed_1543_; lean_object* v_res_1544_; 
v_t_boxed_1543_ = lean_unbox(v_t_1540_);
v_res_1544_ = l_Lean_Meta_Rewrites_SideConditions_assumption_elim(v_motive_1539_, v_t_boxed_1543_, v_h_1541_, v_assumption_1542_);
lean_dec(v_assumption_1542_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim___redArg(lean_object* v_solveByElim_1545_){
_start:
{
lean_inc(v_solveByElim_1545_);
return v_solveByElim_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim___redArg___boxed(lean_object* v_solveByElim_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim___redArg(v_solveByElim_1546_);
lean_dec(v_solveByElim_1546_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim(lean_object* v_motive_1548_, uint8_t v_t_1549_, lean_object* v_h_1550_, lean_object* v_solveByElim_1551_){
_start:
{
lean_inc(v_solveByElim_1551_);
return v_solveByElim_1551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim___boxed(lean_object* v_motive_1552_, lean_object* v_t_1553_, lean_object* v_h_1554_, lean_object* v_solveByElim_1555_){
_start:
{
uint8_t v_t_boxed_1556_; lean_object* v_res_1557_; 
v_t_boxed_1556_ = lean_unbox(v_t_1553_);
v_res_1557_ = l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim(v_motive_1552_, v_t_boxed_1556_, v_h_1554_, v_solveByElim_1555_);
lean_dec(v_solveByElim_1555_);
return v_res_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__0(lean_object* v_x_1558_, lean_object* v_x_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_){
_start:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1565_ = lean_box(0);
v___x_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1565_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__0___boxed(lean_object* v_x_1567_, lean_object* v_x_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_){
_start:
{
lean_object* v_res_1574_; 
v_res_1574_ = l_Lean_Meta_Rewrites_solveByElim___lam__0(v_x_1567_, v_x_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
lean_dec(v___y_1572_);
lean_dec_ref(v___y_1571_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v_x_1568_);
lean_dec(v_x_1567_);
return v_res_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__1(lean_object* v_x_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_){
_start:
{
uint8_t v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1581_ = 0;
v___x_1582_ = lean_box(v___x_1581_);
v___x_1583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1582_);
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__1___boxed(lean_object* v_x_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_){
_start:
{
lean_object* v_res_1590_; 
v_res_1590_ = l_Lean_Meta_Rewrites_solveByElim___lam__1(v_x_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
lean_dec(v_x_1584_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0(lean_object* v_msgData_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_){
_start:
{
lean_object* v___x_1597_; lean_object* v_env_1598_; lean_object* v___x_1599_; lean_object* v_mctx_1600_; lean_object* v_lctx_1601_; lean_object* v_options_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; 
v___x_1597_ = lean_st_ref_get(v___y_1595_);
v_env_1598_ = lean_ctor_get(v___x_1597_, 0);
lean_inc_ref(v_env_1598_);
lean_dec(v___x_1597_);
v___x_1599_ = lean_st_ref_get(v___y_1593_);
v_mctx_1600_ = lean_ctor_get(v___x_1599_, 0);
lean_inc_ref(v_mctx_1600_);
lean_dec(v___x_1599_);
v_lctx_1601_ = lean_ctor_get(v___y_1592_, 2);
v_options_1602_ = lean_ctor_get(v___y_1594_, 2);
lean_inc_ref(v_options_1602_);
lean_inc_ref(v_lctx_1601_);
v___x_1603_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1603_, 0, v_env_1598_);
lean_ctor_set(v___x_1603_, 1, v_mctx_1600_);
lean_ctor_set(v___x_1603_, 2, v_lctx_1601_);
lean_ctor_set(v___x_1603_, 3, v_options_1602_);
v___x_1604_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1603_);
lean_ctor_set(v___x_1604_, 1, v_msgData_1591_);
v___x_1605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1604_);
return v___x_1605_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0___boxed(lean_object* v_msgData_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_){
_start:
{
lean_object* v_res_1612_; 
v_res_1612_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0(v_msgData_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_);
lean_dec(v___y_1610_);
lean_dec_ref(v___y_1609_);
lean_dec(v___y_1608_);
lean_dec_ref(v___y_1607_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(lean_object* v_msg_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
lean_object* v_ref_1619_; lean_object* v___x_1620_; lean_object* v_a_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1629_; 
v_ref_1619_ = lean_ctor_get(v___y_1616_, 5);
v___x_1620_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0(v_msg_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
v_a_1621_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1623_ = v___x_1620_;
v_isShared_1624_ = v_isSharedCheck_1629_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_a_1621_);
lean_dec(v___x_1620_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1629_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1625_; lean_object* v___x_1627_; 
lean_inc(v_ref_1619_);
v___x_1625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1625_, 0, v_ref_1619_);
lean_ctor_set(v___x_1625_, 1, v_a_1621_);
if (v_isShared_1624_ == 0)
{
lean_ctor_set_tag(v___x_1623_, 1);
lean_ctor_set(v___x_1623_, 0, v___x_1625_);
v___x_1627_ = v___x_1623_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v___x_1625_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg___boxed(lean_object* v_msg_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(v_msg_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
lean_dec(v___y_1634_);
lean_dec_ref(v___y_1633_);
lean_dec(v___y_1632_);
lean_dec_ref(v___y_1631_);
return v_res_1636_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1638_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__0));
v___x_1639_ = l_Lean_stringToMessageData(v___x_1638_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__2(lean_object* v_x_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_){
_start:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1646_ = lean_obj_once(&l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1, &l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1_once, _init_l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1);
v___x_1647_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(v___x_1646_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__2___boxed(lean_object* v_x_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_){
_start:
{
lean_object* v_res_1654_; 
v_res_1654_ = l_Lean_Meta_Rewrites_solveByElim___lam__2(v_x_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
lean_dec(v___y_1650_);
lean_dec_ref(v___y_1649_);
lean_dec(v_x_1648_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim(lean_object* v_goals_1664_, lean_object* v_depth_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_){
_start:
{
lean_object* v___f_1671_; lean_object* v___f_1672_; lean_object* v___f_1673_; uint8_t v___x_1674_; lean_object* v___x_1675_; uint8_t v___x_1676_; lean_object* v___x_1677_; uint8_t v___x_1678_; lean_object* v___x_1679_; lean_object* v_cfg_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___f_1671_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___closed__0));
v___f_1672_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___closed__1));
v___f_1673_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___closed__2));
v___x_1674_ = 0;
v___x_1675_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1675_, 0, v_depth_1665_);
lean_ctor_set(v___x_1675_, 1, v___f_1671_);
lean_ctor_set(v___x_1675_, 2, v___f_1672_);
lean_ctor_set(v___x_1675_, 3, v___f_1673_);
lean_ctor_set_uint8(v___x_1675_, sizeof(void*)*4, v___x_1674_);
v___x_1676_ = 1;
v___x_1677_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___closed__3));
v___x_1678_ = 1;
v___x_1679_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_1679_, 0, v___x_1675_);
lean_ctor_set(v___x_1679_, 1, v___x_1677_);
lean_ctor_set_uint8(v___x_1679_, sizeof(void*)*2, v___x_1678_);
lean_ctor_set_uint8(v___x_1679_, sizeof(void*)*2 + 1, v___x_1676_);
lean_ctor_set_uint8(v___x_1679_, sizeof(void*)*2 + 2, v___x_1674_);
v_cfg_1680_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_cfg_1680_, 0, v___x_1679_);
lean_ctor_set_uint8(v_cfg_1680_, sizeof(void*)*1, v___x_1676_);
lean_ctor_set_uint8(v_cfg_1680_, sizeof(void*)*1 + 1, v___x_1676_);
lean_ctor_set_uint8(v_cfg_1680_, sizeof(void*)*1 + 2, v___x_1676_);
lean_ctor_set_uint8(v_cfg_1680_, sizeof(void*)*1 + 3, v___x_1674_);
v___x_1681_ = lean_box(0);
v___x_1682_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___closed__4));
v___x_1683_ = l_Lean_Meta_SolveByElim_mkAssumptionSet(v___x_1674_, v___x_1674_, v___x_1681_, v___x_1681_, v___x_1682_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_);
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_object* v_a_1684_; lean_object* v_fst_1685_; lean_object* v_snd_1686_; lean_object* v___x_1687_; 
v_a_1684_ = lean_ctor_get(v___x_1683_, 0);
lean_inc(v_a_1684_);
lean_dec_ref_known(v___x_1683_, 1);
v_fst_1685_ = lean_ctor_get(v_a_1684_, 0);
lean_inc(v_fst_1685_);
v_snd_1686_ = lean_ctor_get(v_a_1684_, 1);
lean_inc(v_snd_1686_);
lean_dec(v_a_1684_);
v___x_1687_ = l_Lean_Meta_SolveByElim_solveByElim(v_cfg_1680_, v_fst_1685_, v_snd_1686_, v_goals_1664_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_);
if (lean_obj_tag(v___x_1687_) == 0)
{
lean_object* v_a_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1698_; 
v_a_1688_ = lean_ctor_get(v___x_1687_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1687_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1690_ = v___x_1687_;
v_isShared_1691_ = v_isSharedCheck_1698_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_a_1688_);
lean_dec(v___x_1687_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1698_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
if (lean_obj_tag(v_a_1688_) == 0)
{
lean_object* v___x_1692_; lean_object* v___x_1694_; 
v___x_1692_ = lean_box(0);
if (v_isShared_1691_ == 0)
{
lean_ctor_set(v___x_1690_, 0, v___x_1692_);
v___x_1694_ = v___x_1690_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v___x_1692_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
else
{
lean_object* v___x_1696_; lean_object* v___x_1697_; 
lean_del_object(v___x_1690_);
lean_dec(v_a_1688_);
v___x_1696_ = lean_obj_once(&l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1, &l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1_once, _init_l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1);
v___x_1697_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(v___x_1696_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_);
return v___x_1697_;
}
}
}
else
{
lean_object* v_a_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1706_; 
v_a_1699_ = lean_ctor_get(v___x_1687_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v___x_1687_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1701_ = v___x_1687_;
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_a_1699_);
lean_dec(v___x_1687_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1704_; 
if (v_isShared_1702_ == 0)
{
v___x_1704_ = v___x_1701_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_a_1699_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
}
}
else
{
lean_object* v_a_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1714_; 
lean_dec_ref_known(v_cfg_1680_, 1);
lean_dec(v_goals_1664_);
v_a_1707_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1709_ = v___x_1683_;
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_dec(v___x_1683_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1712_; 
if (v_isShared_1710_ == 0)
{
v___x_1712_ = v___x_1709_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_a_1707_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___boxed(lean_object* v_goals_1715_, lean_object* v_depth_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_){
_start:
{
lean_object* v_res_1722_; 
v_res_1722_ = l_Lean_Meta_Rewrites_solveByElim(v_goals_1715_, v_depth_1716_, v_a_1717_, v_a_1718_, v_a_1719_, v_a_1720_);
lean_dec(v_a_1720_);
lean_dec_ref(v_a_1719_);
lean_dec(v_a_1718_);
lean_dec_ref(v_a_1717_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0(lean_object* v_00_u03b1_1723_, lean_object* v_msg_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
lean_object* v___x_1730_; 
v___x_1730_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(v_msg_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_);
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___boxed(lean_object* v_00_u03b1_1731_, lean_object* v_msg_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0(v_00_u03b1_1731_, v_msg_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
lean_dec(v___y_1736_);
lean_dec_ref(v___y_1735_);
lean_dec(v___y_1734_);
lean_dec_ref(v___y_1733_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg(lean_object* v_e_1739_, lean_object* v___y_1740_){
_start:
{
uint8_t v___x_1742_; 
v___x_1742_ = l_Lean_Expr_hasMVar(v_e_1739_);
if (v___x_1742_ == 0)
{
lean_object* v___x_1743_; 
v___x_1743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1743_, 0, v_e_1739_);
return v___x_1743_;
}
else
{
lean_object* v___x_1744_; lean_object* v_mctx_1745_; lean_object* v___x_1746_; lean_object* v_fst_1747_; lean_object* v_snd_1748_; lean_object* v___x_1749_; lean_object* v_cache_1750_; lean_object* v_zetaDeltaFVarIds_1751_; lean_object* v_postponed_1752_; lean_object* v_diag_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1762_; 
v___x_1744_ = lean_st_ref_get(v___y_1740_);
v_mctx_1745_ = lean_ctor_get(v___x_1744_, 0);
lean_inc_ref(v_mctx_1745_);
lean_dec(v___x_1744_);
v___x_1746_ = l_Lean_instantiateMVarsCore(v_mctx_1745_, v_e_1739_);
v_fst_1747_ = lean_ctor_get(v___x_1746_, 0);
lean_inc(v_fst_1747_);
v_snd_1748_ = lean_ctor_get(v___x_1746_, 1);
lean_inc(v_snd_1748_);
lean_dec_ref(v___x_1746_);
v___x_1749_ = lean_st_ref_take(v___y_1740_);
v_cache_1750_ = lean_ctor_get(v___x_1749_, 1);
v_zetaDeltaFVarIds_1751_ = lean_ctor_get(v___x_1749_, 2);
v_postponed_1752_ = lean_ctor_get(v___x_1749_, 3);
v_diag_1753_ = lean_ctor_get(v___x_1749_, 4);
v_isSharedCheck_1762_ = !lean_is_exclusive(v___x_1749_);
if (v_isSharedCheck_1762_ == 0)
{
lean_object* v_unused_1763_; 
v_unused_1763_ = lean_ctor_get(v___x_1749_, 0);
lean_dec(v_unused_1763_);
v___x_1755_ = v___x_1749_;
v_isShared_1756_ = v_isSharedCheck_1762_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_diag_1753_);
lean_inc(v_postponed_1752_);
lean_inc(v_zetaDeltaFVarIds_1751_);
lean_inc(v_cache_1750_);
lean_dec(v___x_1749_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1762_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1758_; 
if (v_isShared_1756_ == 0)
{
lean_ctor_set(v___x_1755_, 0, v_snd_1748_);
v___x_1758_ = v___x_1755_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v_snd_1748_);
lean_ctor_set(v_reuseFailAlloc_1761_, 1, v_cache_1750_);
lean_ctor_set(v_reuseFailAlloc_1761_, 2, v_zetaDeltaFVarIds_1751_);
lean_ctor_set(v_reuseFailAlloc_1761_, 3, v_postponed_1752_);
lean_ctor_set(v_reuseFailAlloc_1761_, 4, v_diag_1753_);
v___x_1758_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1759_ = lean_st_ref_set(v___y_1740_, v___x_1758_);
v___x_1760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1760_, 0, v_fst_1747_);
return v___x_1760_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg___boxed(lean_object* v_e_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_){
_start:
{
lean_object* v_res_1767_; 
v_res_1767_ = l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg(v_e_1764_, v___y_1765_);
lean_dec(v___y_1765_);
return v_res_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0(lean_object* v_e_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_){
_start:
{
lean_object* v___x_1774_; 
v___x_1774_ = l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg(v_e_1768_, v___y_1770_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___boxed(lean_object* v_e_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0(v_e_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
lean_dec(v___y_1777_);
lean_dec_ref(v___y_1776_);
return v_res_1781_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1782_; double v___x_1783_; 
v___x_1782_ = lean_unsigned_to_nat(0u);
v___x_1783_ = lean_float_of_nat(v___x_1782_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2(lean_object* v_cls_1787_, lean_object* v_msg_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
lean_object* v_ref_1794_; lean_object* v___x_1795_; lean_object* v_a_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1840_; 
v_ref_1794_ = lean_ctor_get(v___y_1791_, 5);
v___x_1795_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0(v_msg_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
v_a_1796_ = lean_ctor_get(v___x_1795_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1795_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1798_ = v___x_1795_;
v_isShared_1799_ = v_isSharedCheck_1840_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_a_1796_);
lean_dec(v___x_1795_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1840_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1800_; lean_object* v_traceState_1801_; lean_object* v_env_1802_; lean_object* v_nextMacroScope_1803_; lean_object* v_ngen_1804_; lean_object* v_auxDeclNGen_1805_; lean_object* v_cache_1806_; lean_object* v_messages_1807_; lean_object* v_infoState_1808_; lean_object* v_snapshotTasks_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1839_; 
v___x_1800_ = lean_st_ref_take(v___y_1792_);
v_traceState_1801_ = lean_ctor_get(v___x_1800_, 4);
v_env_1802_ = lean_ctor_get(v___x_1800_, 0);
v_nextMacroScope_1803_ = lean_ctor_get(v___x_1800_, 1);
v_ngen_1804_ = lean_ctor_get(v___x_1800_, 2);
v_auxDeclNGen_1805_ = lean_ctor_get(v___x_1800_, 3);
v_cache_1806_ = lean_ctor_get(v___x_1800_, 5);
v_messages_1807_ = lean_ctor_get(v___x_1800_, 6);
v_infoState_1808_ = lean_ctor_get(v___x_1800_, 7);
v_snapshotTasks_1809_ = lean_ctor_get(v___x_1800_, 8);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1811_ = v___x_1800_;
v_isShared_1812_ = v_isSharedCheck_1839_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_snapshotTasks_1809_);
lean_inc(v_infoState_1808_);
lean_inc(v_messages_1807_);
lean_inc(v_cache_1806_);
lean_inc(v_traceState_1801_);
lean_inc(v_auxDeclNGen_1805_);
lean_inc(v_ngen_1804_);
lean_inc(v_nextMacroScope_1803_);
lean_inc(v_env_1802_);
lean_dec(v___x_1800_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1839_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
uint64_t v_tid_1813_; lean_object* v_traces_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1838_; 
v_tid_1813_ = lean_ctor_get_uint64(v_traceState_1801_, sizeof(void*)*1);
v_traces_1814_ = lean_ctor_get(v_traceState_1801_, 0);
v_isSharedCheck_1838_ = !lean_is_exclusive(v_traceState_1801_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1816_ = v_traceState_1801_;
v_isShared_1817_ = v_isSharedCheck_1838_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_traces_1814_);
lean_dec(v_traceState_1801_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1838_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1818_; double v___x_1819_; uint8_t v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1828_; 
v___x_1818_ = lean_box(0);
v___x_1819_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__0);
v___x_1820_ = 0;
v___x_1821_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__1));
v___x_1822_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1822_, 0, v_cls_1787_);
lean_ctor_set(v___x_1822_, 1, v___x_1818_);
lean_ctor_set(v___x_1822_, 2, v___x_1821_);
lean_ctor_set_float(v___x_1822_, sizeof(void*)*3, v___x_1819_);
lean_ctor_set_float(v___x_1822_, sizeof(void*)*3 + 8, v___x_1819_);
lean_ctor_set_uint8(v___x_1822_, sizeof(void*)*3 + 16, v___x_1820_);
v___x_1823_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__2));
v___x_1824_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1822_);
lean_ctor_set(v___x_1824_, 1, v_a_1796_);
lean_ctor_set(v___x_1824_, 2, v___x_1823_);
lean_inc(v_ref_1794_);
v___x_1825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1825_, 0, v_ref_1794_);
lean_ctor_set(v___x_1825_, 1, v___x_1824_);
v___x_1826_ = l_Lean_PersistentArray_push___redArg(v_traces_1814_, v___x_1825_);
if (v_isShared_1817_ == 0)
{
lean_ctor_set(v___x_1816_, 0, v___x_1826_);
v___x_1828_ = v___x_1816_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v___x_1826_);
lean_ctor_set_uint64(v_reuseFailAlloc_1837_, sizeof(void*)*1, v_tid_1813_);
v___x_1828_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
lean_object* v___x_1830_; 
if (v_isShared_1812_ == 0)
{
lean_ctor_set(v___x_1811_, 4, v___x_1828_);
v___x_1830_ = v___x_1811_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v_env_1802_);
lean_ctor_set(v_reuseFailAlloc_1836_, 1, v_nextMacroScope_1803_);
lean_ctor_set(v_reuseFailAlloc_1836_, 2, v_ngen_1804_);
lean_ctor_set(v_reuseFailAlloc_1836_, 3, v_auxDeclNGen_1805_);
lean_ctor_set(v_reuseFailAlloc_1836_, 4, v___x_1828_);
lean_ctor_set(v_reuseFailAlloc_1836_, 5, v_cache_1806_);
lean_ctor_set(v_reuseFailAlloc_1836_, 6, v_messages_1807_);
lean_ctor_set(v_reuseFailAlloc_1836_, 7, v_infoState_1808_);
lean_ctor_set(v_reuseFailAlloc_1836_, 8, v_snapshotTasks_1809_);
v___x_1830_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1834_; 
v___x_1831_ = lean_st_ref_set(v___y_1792_, v___x_1830_);
v___x_1832_ = lean_box(0);
if (v_isShared_1799_ == 0)
{
lean_ctor_set(v___x_1798_, 0, v___x_1832_);
v___x_1834_ = v___x_1798_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v___x_1832_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___boxed(lean_object* v_cls_1841_, lean_object* v_msg_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_){
_start:
{
lean_object* v_res_1848_; 
v_res_1848_ = l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2(v_cls_1841_, v_msg_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_);
lean_dec(v___y_1846_);
lean_dec_ref(v___y_1845_);
lean_dec(v___y_1844_);
lean_dec_ref(v___y_1843_);
return v_res_1848_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Rewrites_rwLemma_spec__1(lean_object* v_x_1849_, lean_object* v_x_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_){
_start:
{
if (lean_obj_tag(v_x_1849_) == 0)
{
lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1856_ = l_List_reverse___redArg(v_x_1850_);
v___x_1857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1856_);
return v___x_1857_;
}
else
{
lean_object* v_head_1858_; lean_object* v_tail_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1877_; 
v_head_1858_ = lean_ctor_get(v_x_1849_, 0);
v_tail_1859_ = lean_ctor_get(v_x_1849_, 1);
v_isSharedCheck_1877_ = !lean_is_exclusive(v_x_1849_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1861_ = v_x_1849_;
v_isShared_1862_ = v_isSharedCheck_1877_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_tail_1859_);
lean_inc(v_head_1858_);
lean_dec(v_x_1849_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1877_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1863_; 
v___x_1863_ = l_Lean_MVarId_assumption(v_head_1858_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_);
if (lean_obj_tag(v___x_1863_) == 0)
{
lean_object* v_a_1864_; lean_object* v___x_1866_; 
v_a_1864_ = lean_ctor_get(v___x_1863_, 0);
lean_inc(v_a_1864_);
lean_dec_ref_known(v___x_1863_, 1);
if (v_isShared_1862_ == 0)
{
lean_ctor_set(v___x_1861_, 1, v_x_1850_);
lean_ctor_set(v___x_1861_, 0, v_a_1864_);
v___x_1866_ = v___x_1861_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_a_1864_);
lean_ctor_set(v_reuseFailAlloc_1868_, 1, v_x_1850_);
v___x_1866_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
v_x_1849_ = v_tail_1859_;
v_x_1850_ = v___x_1866_;
goto _start;
}
}
else
{
lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1876_; 
lean_del_object(v___x_1861_);
lean_dec(v_tail_1859_);
lean_dec(v_x_1850_);
v_a_1869_ = lean_ctor_get(v___x_1863_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1863_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1871_ = v___x_1863_;
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v___x_1863_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1874_; 
if (v_isShared_1872_ == 0)
{
v___x_1874_ = v___x_1871_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_a_1869_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Rewrites_rwLemma_spec__1___boxed(lean_object* v_x_1878_, lean_object* v_x_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l_List_mapM_loop___at___00Lean_Meta_Rewrites_rwLemma_spec__1(v_x_1878_, v_x_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_);
lean_dec(v___y_1883_);
lean_dec_ref(v___y_1882_);
lean_dec(v___y_1881_);
lean_dec_ref(v___y_1880_);
return v_res_1885_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5(void){
_start:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1898_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_));
v___x_1899_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__4));
v___x_1900_ = l_Lean_Name_append(v___x_1899_, v___x_1898_);
return v___x_1900_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__7(void){
_start:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1902_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__6));
v___x_1903_ = l_Lean_stringToMessageData(v___x_1902_);
return v___x_1903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0(lean_object* v_weight_1905_, lean_object* v_goal_1906_, lean_object* v_target_1907_, uint8_t v_symm_1908_, uint8_t v_side_1909_, lean_object* v_lem_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_){
_start:
{
lean_object* v___y_1917_; lean_object* v___y_1918_; lean_object* v___y_1919_; lean_object* v___y_1920_; uint8_t v___y_1921_; lean_object* v___y_1942_; lean_object* v___y_1943_; lean_object* v___y_1944_; lean_object* v___y_1945_; lean_object* v___y_1946_; lean_object* v___y_1947_; lean_object* v_fst_1948_; uint8_t v_snd_1949_; uint8_t v___y_1973_; uint8_t v___y_1974_; lean_object* v___y_1975_; lean_object* v___y_1976_; lean_object* v___y_1977_; lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1980_; lean_object* v___y_2000_; lean_object* v___y_2001_; lean_object* v___y_2002_; lean_object* v___y_2003_; uint8_t v___y_2004_; lean_object* v___y_2016_; lean_object* v___y_2017_; lean_object* v___y_2018_; lean_object* v___y_2019_; uint8_t v___y_2020_; lean_object* v___y_2032_; lean_object* v___y_2112_; lean_object* v___y_2113_; lean_object* v___y_2114_; lean_object* v___y_2115_; lean_object* v_val_2130_; 
if (lean_obj_tag(v_lem_1910_) == 0)
{
lean_object* v_val_2140_; 
v_val_2140_ = lean_ctor_get(v_lem_1910_, 0);
lean_inc(v_val_2140_);
lean_dec_ref_known(v_lem_1910_, 1);
v_val_2130_ = v_val_2140_;
goto v___jp_2129_;
}
else
{
lean_object* v_val_2141_; lean_object* v___x_2142_; 
v_val_2141_ = lean_ctor_get(v_lem_1910_, 0);
lean_inc(v_val_2141_);
lean_dec_ref_known(v_lem_1910_, 1);
v___x_2142_ = l_Lean_Meta_saveState___redArg(v___y_1912_, v___y_1914_);
if (lean_obj_tag(v___x_2142_) == 0)
{
lean_object* v_a_2143_; lean_object* v___x_2144_; 
v_a_2143_ = lean_ctor_get(v___x_2142_, 0);
lean_inc(v_a_2143_);
lean_dec_ref_known(v___x_2142_, 1);
v___x_2144_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_val_2141_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_a_2145_; 
lean_dec(v_a_2143_);
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_a_2145_);
lean_dec_ref_known(v___x_2144_, 1);
v_val_2130_ = v_a_2145_;
goto v___jp_2129_;
}
else
{
lean_object* v_a_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2175_; 
lean_dec_ref(v_target_1907_);
lean_dec(v_goal_1906_);
lean_dec(v_weight_1905_);
v_a_2146_ = lean_ctor_get(v___x_2144_, 0);
v_isSharedCheck_2175_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2148_ = v___x_2144_;
v_isShared_2149_ = v_isSharedCheck_2175_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_a_2146_);
lean_dec(v___x_2144_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2175_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
uint8_t v___y_2151_; uint8_t v___x_2173_; 
v___x_2173_ = l_Lean_Exception_isInterrupt(v_a_2146_);
if (v___x_2173_ == 0)
{
uint8_t v___x_2174_; 
lean_inc(v_a_2146_);
v___x_2174_ = l_Lean_Exception_isRuntime(v_a_2146_);
v___y_2151_ = v___x_2174_;
goto v___jp_2150_;
}
else
{
v___y_2151_ = v___x_2173_;
goto v___jp_2150_;
}
v___jp_2150_:
{
if (v___y_2151_ == 0)
{
lean_object* v___x_2152_; 
lean_del_object(v___x_2148_);
lean_dec(v_a_2146_);
v___x_2152_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2143_, v___y_1912_, v___y_1914_);
lean_dec(v_a_2143_);
if (lean_obj_tag(v___x_2152_) == 0)
{
lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2160_; 
v_isSharedCheck_2160_ = !lean_is_exclusive(v___x_2152_);
if (v_isSharedCheck_2160_ == 0)
{
lean_object* v_unused_2161_; 
v_unused_2161_ = lean_ctor_get(v___x_2152_, 0);
lean_dec(v_unused_2161_);
v___x_2154_ = v___x_2152_;
v_isShared_2155_ = v_isSharedCheck_2160_;
goto v_resetjp_2153_;
}
else
{
lean_dec(v___x_2152_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2160_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v___x_2156_; lean_object* v___x_2158_; 
v___x_2156_ = lean_box(0);
if (v_isShared_2155_ == 0)
{
lean_ctor_set(v___x_2154_, 0, v___x_2156_);
v___x_2158_ = v___x_2154_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v___x_2156_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
return v___x_2158_;
}
}
}
else
{
lean_object* v_a_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2169_; 
v_a_2162_ = lean_ctor_get(v___x_2152_, 0);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2152_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2164_ = v___x_2152_;
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_a_2162_);
lean_dec(v___x_2152_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2167_; 
if (v_isShared_2165_ == 0)
{
v___x_2167_ = v___x_2164_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_a_2162_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
}
}
else
{
lean_object* v___x_2171_; 
lean_dec(v_a_2143_);
if (v_isShared_2149_ == 0)
{
v___x_2171_ = v___x_2148_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_a_2146_);
v___x_2171_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
return v___x_2171_;
}
}
}
}
}
}
else
{
lean_object* v_a_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2183_; 
lean_dec(v_val_2141_);
lean_dec_ref(v_target_1907_);
lean_dec(v_goal_1906_);
lean_dec(v_weight_1905_);
v_a_2176_ = lean_ctor_get(v___x_2142_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2142_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2178_ = v___x_2142_;
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_a_2176_);
lean_dec(v___x_2142_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2181_; 
if (v_isShared_2179_ == 0)
{
v___x_2181_ = v___x_2178_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_a_2176_);
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
v___jp_1916_:
{
if (v___y_1921_ == 0)
{
lean_object* v___x_1922_; 
lean_dec_ref(v___y_1917_);
v___x_1922_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1918_, v___y_1920_, v___y_1919_);
lean_dec_ref(v___y_1918_);
if (lean_obj_tag(v___x_1922_) == 0)
{
lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1930_; 
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1922_);
if (v_isSharedCheck_1930_ == 0)
{
lean_object* v_unused_1931_; 
v_unused_1931_ = lean_ctor_get(v___x_1922_, 0);
lean_dec(v_unused_1931_);
v___x_1924_ = v___x_1922_;
v_isShared_1925_ = v_isSharedCheck_1930_;
goto v_resetjp_1923_;
}
else
{
lean_dec(v___x_1922_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1930_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1926_; lean_object* v___x_1928_; 
v___x_1926_ = lean_box(0);
if (v_isShared_1925_ == 0)
{
lean_ctor_set(v___x_1924_, 0, v___x_1926_);
v___x_1928_ = v___x_1924_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v___x_1926_);
v___x_1928_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
return v___x_1928_;
}
}
}
else
{
lean_object* v_a_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1939_; 
v_a_1932_ = lean_ctor_get(v___x_1922_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1922_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1934_ = v___x_1922_;
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_a_1932_);
lean_dec(v___x_1922_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1937_; 
if (v_isShared_1935_ == 0)
{
v___x_1937_ = v___x_1934_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_a_1932_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
}
}
else
{
lean_object* v___x_1940_; 
lean_dec_ref(v___y_1918_);
v___x_1940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1940_, 0, v___y_1917_);
return v___x_1940_;
}
}
v___jp_1941_:
{
lean_object* v___x_1950_; lean_object* v_mctx_1951_; lean_object* v___x_1952_; 
v___x_1950_ = lean_st_ref_get(v___y_1946_);
v_mctx_1951_ = lean_ctor_get(v___x_1950_, 0);
lean_inc_ref_n(v_mctx_1951_, 2);
lean_dec(v___x_1950_);
v___x_1952_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(v_mctx_1951_, v___y_1943_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1942_);
if (lean_obj_tag(v___x_1952_) == 0)
{
lean_object* v_a_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1963_; 
v_a_1953_ = lean_ctor_get(v___x_1952_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1952_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1955_ = v___x_1952_;
v_isShared_1956_ = v_isSharedCheck_1963_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_a_1953_);
lean_dec(v___x_1952_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1963_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v___x_1957_; uint8_t v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1961_; 
v___x_1957_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1957_, 0, v_fst_1948_);
lean_ctor_set(v___x_1957_, 1, v_weight_1905_);
lean_ctor_set(v___x_1957_, 2, v___y_1944_);
lean_ctor_set(v___x_1957_, 3, v_mctx_1951_);
lean_ctor_set_uint8(v___x_1957_, sizeof(void*)*4, v_snd_1949_);
v___x_1958_ = lean_unbox(v_a_1953_);
lean_dec(v_a_1953_);
lean_ctor_set_uint8(v___x_1957_, sizeof(void*)*4 + 1, v___x_1958_);
v___x_1959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1959_, 0, v___x_1957_);
if (v_isShared_1956_ == 0)
{
lean_ctor_set(v___x_1955_, 0, v___x_1959_);
v___x_1961_ = v___x_1955_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v___x_1959_);
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
lean_dec_ref(v_mctx_1951_);
lean_dec_ref(v_fst_1948_);
lean_dec_ref(v___y_1944_);
lean_dec(v_weight_1905_);
v_a_1964_ = lean_ctor_get(v___x_1952_, 0);
v_isSharedCheck_1971_ = !lean_is_exclusive(v___x_1952_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1966_ = v___x_1952_;
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_a_1964_);
lean_dec(v___x_1952_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1969_; 
if (v_isShared_1967_ == 0)
{
v___x_1969_ = v___x_1966_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(1, 1, 0);
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
v___jp_1972_:
{
lean_object* v___x_1981_; 
v___x_1981_ = l_Lean_Meta_Rewrites_rewriteResultLemma(v___y_1976_);
if (lean_obj_tag(v___x_1981_) == 1)
{
lean_object* v_val_1982_; lean_object* v___x_1983_; lean_object* v_a_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; uint8_t v___x_1987_; 
v_val_1982_ = lean_ctor_get(v___x_1981_, 0);
lean_inc(v_val_1982_);
lean_dec_ref_known(v___x_1981_, 1);
v___x_1983_ = l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg(v_val_1982_, v___y_1978_);
v_a_1984_ = lean_ctor_get(v___x_1983_, 0);
lean_inc(v_a_1984_);
lean_dec_ref(v___x_1983_);
v___x_1985_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__1));
v___x_1986_ = lean_unsigned_to_nat(4u);
v___x_1987_ = l_Lean_Expr_isAppOfArity(v_a_1984_, v___x_1985_, v___x_1986_);
if (v___x_1987_ == 0)
{
v___y_1942_ = v___y_1980_;
v___y_1943_ = v___y_1975_;
v___y_1944_ = v___y_1976_;
v___y_1945_ = v___y_1977_;
v___y_1946_ = v___y_1978_;
v___y_1947_ = v___y_1979_;
v_fst_1948_ = v_a_1984_;
v_snd_1949_ = v___y_1974_;
goto v___jp_1941_;
}
else
{
lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1988_ = lean_unsigned_to_nat(3u);
v___x_1989_ = l_Lean_Expr_getAppNumArgs(v_a_1984_);
v___x_1990_ = lean_nat_sub(v___x_1989_, v___x_1988_);
lean_dec(v___x_1989_);
v___x_1991_ = lean_unsigned_to_nat(1u);
v___x_1992_ = lean_nat_sub(v___x_1990_, v___x_1991_);
lean_dec(v___x_1990_);
v___x_1993_ = l_Lean_Expr_getRevArg_x21(v_a_1984_, v___x_1992_);
lean_dec(v_a_1984_);
v___y_1942_ = v___y_1980_;
v___y_1943_ = v___y_1975_;
v___y_1944_ = v___y_1976_;
v___y_1945_ = v___y_1977_;
v___y_1946_ = v___y_1978_;
v___y_1947_ = v___y_1979_;
v_fst_1948_ = v___x_1993_;
v_snd_1949_ = v___y_1973_;
goto v___jp_1941_;
}
}
else
{
lean_object* v___x_1994_; lean_object* v___x_1995_; 
lean_dec(v___x_1981_);
lean_dec_ref(v___y_1976_);
lean_dec_ref(v___y_1975_);
lean_dec(v_weight_1905_);
v___x_1994_ = lean_box(0);
v___x_1995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1995_, 0, v___x_1994_);
return v___x_1995_;
}
}
v___jp_1996_:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1997_ = lean_box(0);
v___x_1998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1998_, 0, v___x_1997_);
return v___x_1998_;
}
v___jp_1999_:
{
if (v___y_2004_ == 0)
{
lean_object* v___x_2005_; 
lean_dec_ref(v___y_2001_);
v___x_2005_ = l_Lean_Meta_SavedState_restore___redArg(v___y_2000_, v___y_2003_, v___y_2002_);
lean_dec_ref(v___y_2000_);
if (lean_obj_tag(v___x_2005_) == 0)
{
lean_dec_ref_known(v___x_2005_, 1);
goto v___jp_1996_;
}
else
{
lean_object* v_a_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2013_; 
v_a_2006_ = lean_ctor_get(v___x_2005_, 0);
v_isSharedCheck_2013_ = !lean_is_exclusive(v___x_2005_);
if (v_isSharedCheck_2013_ == 0)
{
v___x_2008_ = v___x_2005_;
v_isShared_2009_ = v_isSharedCheck_2013_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_a_2006_);
lean_dec(v___x_2005_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2013_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v___x_2011_; 
if (v_isShared_2009_ == 0)
{
v___x_2011_ = v___x_2008_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v_a_2006_);
v___x_2011_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
return v___x_2011_;
}
}
}
}
else
{
lean_object* v___x_2014_; 
lean_dec_ref(v___y_2000_);
v___x_2014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2014_, 0, v___y_2001_);
return v___x_2014_;
}
}
v___jp_2015_:
{
if (v___y_2020_ == 0)
{
lean_object* v___x_2021_; 
lean_dec_ref(v___y_2016_);
v___x_2021_ = l_Lean_Meta_SavedState_restore___redArg(v___y_2018_, v___y_2019_, v___y_2017_);
lean_dec_ref(v___y_2018_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_dec_ref_known(v___x_2021_, 1);
goto v___jp_1996_;
}
else
{
lean_object* v_a_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2029_; 
v_a_2022_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2024_ = v___x_2021_;
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_a_2022_);
lean_dec(v___x_2021_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v___x_2027_; 
if (v_isShared_2025_ == 0)
{
v___x_2027_ = v___x_2024_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_a_2022_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
}
else
{
lean_object* v___x_2030_; 
lean_dec_ref(v___y_2018_);
v___x_2030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2030_, 0, v___y_2016_);
return v___x_2030_;
}
}
v___jp_2031_:
{
lean_object* v___x_2033_; 
v___x_2033_ = l_Lean_Meta_saveState___redArg(v___y_1912_, v___y_1914_);
if (lean_obj_tag(v___x_2033_) == 0)
{
lean_object* v_a_2034_; uint8_t v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
v_a_2034_ = lean_ctor_get(v___x_2033_, 0);
lean_inc(v_a_2034_);
lean_dec_ref_known(v___x_2033_, 1);
v___x_2035_ = 1;
v___x_2036_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__2));
lean_inc_ref(v___y_2032_);
v___x_2037_ = l_Lean_MVarId_rewrite(v_goal_1906_, v_target_1907_, v___y_2032_, v_symm_1908_, v___x_2036_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_);
if (lean_obj_tag(v___x_2037_) == 0)
{
lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2099_; 
lean_dec(v_a_2034_);
v_a_2038_ = lean_ctor_get(v___x_2037_, 0);
v_isSharedCheck_2099_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2040_ = v___x_2037_;
v_isShared_2041_ = v_isSharedCheck_2099_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_2037_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2099_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v_eNew_2042_; lean_object* v_mvarIds_2043_; uint8_t v___x_2044_; 
v_eNew_2042_ = lean_ctor_get(v_a_2038_, 0);
v_mvarIds_2043_ = lean_ctor_get(v_a_2038_, 2);
v___x_2044_ = l_List_isEmpty___redArg(v_mvarIds_2043_);
if (v___x_2044_ == 0)
{
lean_inc_ref(v_eNew_2042_);
lean_del_object(v___x_2040_);
lean_dec_ref(v___y_2032_);
switch(v_side_1909_)
{
case 0:
{
if (v___x_2044_ == 0)
{
lean_dec_ref(v_eNew_2042_);
lean_dec(v_a_2038_);
lean_dec(v_weight_1905_);
goto v___jp_1996_;
}
else
{
v___y_1973_ = v___x_2035_;
v___y_1974_ = v___x_2044_;
v___y_1975_ = v_eNew_2042_;
v___y_1976_ = v_a_2038_;
v___y_1977_ = v___y_1911_;
v___y_1978_ = v___y_1912_;
v___y_1979_ = v___y_1913_;
v___y_1980_ = v___y_1914_;
goto v___jp_1972_;
}
}
case 1:
{
lean_object* v___x_2045_; 
v___x_2045_ = l_Lean_Meta_saveState___redArg(v___y_1912_, v___y_1914_);
if (lean_obj_tag(v___x_2045_) == 0)
{
lean_object* v_a_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; 
v_a_2046_ = lean_ctor_get(v___x_2045_, 0);
lean_inc(v_a_2046_);
lean_dec_ref_known(v___x_2045_, 1);
v___x_2047_ = lean_box(0);
lean_inc(v_mvarIds_2043_);
v___x_2048_ = l_List_mapM_loop___at___00Lean_Meta_Rewrites_rwLemma_spec__1(v_mvarIds_2043_, v___x_2047_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_);
if (lean_obj_tag(v___x_2048_) == 0)
{
lean_dec_ref_known(v___x_2048_, 1);
lean_dec(v_a_2046_);
v___y_1973_ = v___x_2035_;
v___y_1974_ = v___x_2044_;
v___y_1975_ = v_eNew_2042_;
v___y_1976_ = v_a_2038_;
v___y_1977_ = v___y_1911_;
v___y_1978_ = v___y_1912_;
v___y_1979_ = v___y_1913_;
v___y_1980_ = v___y_1914_;
goto v___jp_1972_;
}
else
{
lean_object* v_a_2049_; uint8_t v___x_2050_; 
lean_dec_ref(v_eNew_2042_);
lean_dec(v_a_2038_);
lean_dec(v_weight_1905_);
v_a_2049_ = lean_ctor_get(v___x_2048_, 0);
lean_inc(v_a_2049_);
lean_dec_ref_known(v___x_2048_, 1);
v___x_2050_ = l_Lean_Exception_isInterrupt(v_a_2049_);
if (v___x_2050_ == 0)
{
uint8_t v___x_2051_; 
lean_inc(v_a_2049_);
v___x_2051_ = l_Lean_Exception_isRuntime(v_a_2049_);
v___y_2016_ = v_a_2049_;
v___y_2017_ = v___y_1914_;
v___y_2018_ = v_a_2046_;
v___y_2019_ = v___y_1912_;
v___y_2020_ = v___x_2051_;
goto v___jp_2015_;
}
else
{
v___y_2016_ = v_a_2049_;
v___y_2017_ = v___y_1914_;
v___y_2018_ = v_a_2046_;
v___y_2019_ = v___y_1912_;
v___y_2020_ = v___x_2050_;
goto v___jp_2015_;
}
}
}
else
{
lean_object* v_a_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2059_; 
lean_dec_ref(v_eNew_2042_);
lean_dec(v_a_2038_);
lean_dec(v_weight_1905_);
v_a_2052_ = lean_ctor_get(v___x_2045_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2054_ = v___x_2045_;
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_a_2052_);
lean_dec(v___x_2045_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v___x_2057_; 
if (v_isShared_2055_ == 0)
{
v___x_2057_ = v___x_2054_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_a_2052_);
v___x_2057_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
return v___x_2057_;
}
}
}
}
default: 
{
lean_object* v___x_2060_; 
v___x_2060_ = l_Lean_Meta_saveState___redArg(v___y_1912_, v___y_1914_);
if (lean_obj_tag(v___x_2060_) == 0)
{
lean_object* v_a_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; 
v_a_2061_ = lean_ctor_get(v___x_2060_, 0);
lean_inc(v_a_2061_);
lean_dec_ref_known(v___x_2060_, 1);
v___x_2062_ = lean_unsigned_to_nat(6u);
lean_inc(v_mvarIds_2043_);
v___x_2063_ = l_Lean_Meta_Rewrites_solveByElim(v_mvarIds_2043_, v___x_2062_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_);
if (lean_obj_tag(v___x_2063_) == 0)
{
lean_dec_ref_known(v___x_2063_, 1);
lean_dec(v_a_2061_);
v___y_1973_ = v___x_2035_;
v___y_1974_ = v___x_2044_;
v___y_1975_ = v_eNew_2042_;
v___y_1976_ = v_a_2038_;
v___y_1977_ = v___y_1911_;
v___y_1978_ = v___y_1912_;
v___y_1979_ = v___y_1913_;
v___y_1980_ = v___y_1914_;
goto v___jp_1972_;
}
else
{
lean_object* v_a_2064_; uint8_t v___x_2065_; 
lean_dec_ref(v_eNew_2042_);
lean_dec(v_a_2038_);
lean_dec(v_weight_1905_);
v_a_2064_ = lean_ctor_get(v___x_2063_, 0);
lean_inc(v_a_2064_);
lean_dec_ref_known(v___x_2063_, 1);
v___x_2065_ = l_Lean_Exception_isInterrupt(v_a_2064_);
if (v___x_2065_ == 0)
{
uint8_t v___x_2066_; 
lean_inc(v_a_2064_);
v___x_2066_ = l_Lean_Exception_isRuntime(v_a_2064_);
v___y_2000_ = v_a_2061_;
v___y_2001_ = v_a_2064_;
v___y_2002_ = v___y_1914_;
v___y_2003_ = v___y_1912_;
v___y_2004_ = v___x_2066_;
goto v___jp_1999_;
}
else
{
v___y_2000_ = v_a_2061_;
v___y_2001_ = v_a_2064_;
v___y_2002_ = v___y_1914_;
v___y_2003_ = v___y_1912_;
v___y_2004_ = v___x_2065_;
goto v___jp_1999_;
}
}
}
else
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2074_; 
lean_dec_ref(v_eNew_2042_);
lean_dec(v_a_2038_);
lean_dec(v_weight_1905_);
v_a_2067_ = lean_ctor_get(v___x_2060_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2069_ = v___x_2060_;
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2060_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2072_; 
if (v_isShared_2070_ == 0)
{
v___x_2072_ = v___x_2069_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_a_2067_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
}
}
}
else
{
lean_object* v___x_2075_; lean_object* v_mctx_2076_; lean_object* v___x_2077_; 
v___x_2075_ = lean_st_ref_get(v___y_1912_);
v_mctx_2076_ = lean_ctor_get(v___x_2075_, 0);
lean_inc_ref_n(v_mctx_2076_, 2);
lean_dec(v___x_2075_);
lean_inc_ref(v_eNew_2042_);
v___x_2077_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(v_mctx_2076_, v_eNew_2042_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v_a_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2090_; 
v_a_2078_ = lean_ctor_get(v___x_2077_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2080_ = v___x_2077_;
v_isShared_2081_ = v_isSharedCheck_2090_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_a_2078_);
lean_dec(v___x_2077_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2090_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2082_; uint8_t v___x_2083_; lean_object* v___x_2085_; 
v___x_2082_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2082_, 0, v___y_2032_);
lean_ctor_set(v___x_2082_, 1, v_weight_1905_);
lean_ctor_set(v___x_2082_, 2, v_a_2038_);
lean_ctor_set(v___x_2082_, 3, v_mctx_2076_);
lean_ctor_set_uint8(v___x_2082_, sizeof(void*)*4, v_symm_1908_);
v___x_2083_ = lean_unbox(v_a_2078_);
lean_dec(v_a_2078_);
lean_ctor_set_uint8(v___x_2082_, sizeof(void*)*4 + 1, v___x_2083_);
if (v_isShared_2041_ == 0)
{
lean_ctor_set_tag(v___x_2040_, 1);
lean_ctor_set(v___x_2040_, 0, v___x_2082_);
v___x_2085_ = v___x_2040_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v___x_2082_);
v___x_2085_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
lean_object* v___x_2087_; 
if (v_isShared_2081_ == 0)
{
lean_ctor_set(v___x_2080_, 0, v___x_2085_);
v___x_2087_ = v___x_2080_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v___x_2085_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
}
else
{
lean_object* v_a_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2098_; 
lean_dec_ref(v_mctx_2076_);
lean_del_object(v___x_2040_);
lean_dec(v_a_2038_);
lean_dec_ref(v___y_2032_);
lean_dec(v_weight_1905_);
v_a_2091_ = lean_ctor_get(v___x_2077_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2093_ = v___x_2077_;
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_a_2091_);
lean_dec(v___x_2077_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v___x_2096_; 
if (v_isShared_2094_ == 0)
{
v___x_2096_ = v___x_2093_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_a_2091_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
}
}
}
}
else
{
lean_object* v_a_2100_; uint8_t v___x_2101_; 
lean_dec_ref(v___y_2032_);
lean_dec(v_weight_1905_);
v_a_2100_ = lean_ctor_get(v___x_2037_, 0);
lean_inc(v_a_2100_);
lean_dec_ref_known(v___x_2037_, 1);
v___x_2101_ = l_Lean_Exception_isInterrupt(v_a_2100_);
if (v___x_2101_ == 0)
{
uint8_t v___x_2102_; 
lean_inc(v_a_2100_);
v___x_2102_ = l_Lean_Exception_isRuntime(v_a_2100_);
v___y_1917_ = v_a_2100_;
v___y_1918_ = v_a_2034_;
v___y_1919_ = v___y_1914_;
v___y_1920_ = v___y_1912_;
v___y_1921_ = v___x_2102_;
goto v___jp_1916_;
}
else
{
v___y_1917_ = v_a_2100_;
v___y_1918_ = v_a_2034_;
v___y_1919_ = v___y_1914_;
v___y_1920_ = v___y_1912_;
v___y_1921_ = v___x_2101_;
goto v___jp_1916_;
}
}
}
else
{
lean_object* v_a_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2110_; 
lean_dec_ref(v___y_2032_);
lean_dec_ref(v_target_1907_);
lean_dec(v_goal_1906_);
lean_dec(v_weight_1905_);
v_a_2103_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2105_ = v___x_2033_;
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_a_2103_);
lean_dec(v___x_2033_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v___x_2108_; 
if (v_isShared_2106_ == 0)
{
v___x_2108_ = v___x_2105_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_a_2103_);
v___x_2108_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
return v___x_2108_;
}
}
}
}
v___jp_2111_:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
lean_inc_ref(v___y_2115_);
v___x_2116_ = l_Lean_stringToMessageData(v___y_2115_);
lean_inc_ref(v___y_2113_);
v___x_2117_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2117_, 0, v___y_2113_);
lean_ctor_set(v___x_2117_, 1, v___x_2116_);
lean_inc_ref(v___y_2114_);
v___x_2118_ = l_Lean_MessageData_ofExpr(v___y_2114_);
v___x_2119_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2117_);
lean_ctor_set(v___x_2119_, 1, v___x_2118_);
lean_inc(v___y_2112_);
v___x_2120_ = l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2(v___y_2112_, v___x_2119_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_dec_ref_known(v___x_2120_, 1);
v___y_2032_ = v___y_2114_;
goto v___jp_2031_;
}
else
{
lean_object* v_a_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2128_; 
lean_dec_ref(v___y_2114_);
lean_dec_ref(v_target_1907_);
lean_dec(v_goal_1906_);
lean_dec(v_weight_1905_);
v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2123_ = v___x_2120_;
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_dec(v___x_2120_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2126_; 
if (v_isShared_2124_ == 0)
{
v___x_2126_ = v___x_2123_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_a_2121_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
}
}
v___jp_2129_:
{
lean_object* v_options_2131_; uint8_t v_hasTrace_2132_; 
v_options_2131_ = lean_ctor_get(v___y_1913_, 2);
v_hasTrace_2132_ = lean_ctor_get_uint8(v_options_2131_, sizeof(void*)*1);
if (v_hasTrace_2132_ == 0)
{
v___y_2032_ = v_val_2130_;
goto v___jp_2031_;
}
else
{
lean_object* v_inheritedTraceOptions_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; uint8_t v___x_2136_; 
v_inheritedTraceOptions_2133_ = lean_ctor_get(v___y_1913_, 13);
v___x_2134_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_));
v___x_2135_ = lean_obj_once(&l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5, &l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5_once, _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5);
v___x_2136_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2133_, v_options_2131_, v___x_2135_);
if (v___x_2136_ == 0)
{
v___y_2032_ = v_val_2130_;
goto v___jp_2031_;
}
else
{
lean_object* v___x_2137_; 
v___x_2137_ = lean_obj_once(&l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__7, &l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__7_once, _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__7);
if (v_symm_1908_ == 0)
{
lean_object* v___x_2138_; 
v___x_2138_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__1));
v___y_2112_ = v___x_2134_;
v___y_2113_ = v___x_2137_;
v___y_2114_ = v_val_2130_;
v___y_2115_ = v___x_2138_;
goto v___jp_2111_;
}
else
{
lean_object* v___x_2139_; 
v___x_2139_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__8));
v___y_2112_ = v___x_2134_;
v___y_2113_ = v___x_2137_;
v___y_2114_ = v_val_2130_;
v___y_2115_ = v___x_2139_;
goto v___jp_2111_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0___boxed(lean_object* v_weight_2184_, lean_object* v_goal_2185_, lean_object* v_target_2186_, lean_object* v_symm_2187_, lean_object* v_side_2188_, lean_object* v_lem_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_){
_start:
{
uint8_t v_symm_boxed_2195_; uint8_t v_side_boxed_2196_; lean_object* v_res_2197_; 
v_symm_boxed_2195_ = lean_unbox(v_symm_2187_);
v_side_boxed_2196_ = lean_unbox(v_side_2188_);
v_res_2197_ = l_Lean_Meta_Rewrites_rwLemma___lam__0(v_weight_2184_, v_goal_2185_, v_target_2186_, v_symm_boxed_2195_, v_side_boxed_2196_, v_lem_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
lean_dec(v___y_2193_);
lean_dec_ref(v___y_2192_);
lean_dec(v___y_2191_);
lean_dec_ref(v___y_2190_);
return v_res_2197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma(lean_object* v_ctx_2198_, lean_object* v_goal_2199_, lean_object* v_target_2200_, uint8_t v_side_2201_, lean_object* v_lem_2202_, uint8_t v_symm_2203_, lean_object* v_weight_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_){
_start:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___f_2212_; lean_object* v___x_2213_; 
v___x_2210_ = lean_box(v_symm_2203_);
v___x_2211_ = lean_box(v_side_2201_);
v___f_2212_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___boxed), 11, 6);
lean_closure_set(v___f_2212_, 0, v_weight_2204_);
lean_closure_set(v___f_2212_, 1, v_goal_2199_);
lean_closure_set(v___f_2212_, 2, v_target_2200_);
lean_closure_set(v___f_2212_, 3, v___x_2210_);
lean_closure_set(v___f_2212_, 4, v___x_2211_);
lean_closure_set(v___f_2212_, 5, v_lem_2202_);
v___x_2213_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg(v_ctx_2198_, v___f_2212_, v_a_2205_, v_a_2206_, v_a_2207_, v_a_2208_);
return v___x_2213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___boxed(lean_object* v_ctx_2214_, lean_object* v_goal_2215_, lean_object* v_target_2216_, lean_object* v_side_2217_, lean_object* v_lem_2218_, lean_object* v_symm_2219_, lean_object* v_weight_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_){
_start:
{
uint8_t v_side_boxed_2226_; uint8_t v_symm_boxed_2227_; lean_object* v_res_2228_; 
v_side_boxed_2226_ = lean_unbox(v_side_2217_);
v_symm_boxed_2227_ = lean_unbox(v_symm_2219_);
v_res_2228_ = l_Lean_Meta_Rewrites_rwLemma(v_ctx_2214_, v_goal_2215_, v_target_2216_, v_side_boxed_2226_, v_lem_2218_, v_symm_boxed_2227_, v_weight_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_);
lean_dec(v_a_2224_);
lean_dec_ref(v_a_2223_);
lean_dec(v_a_2222_);
lean_dec_ref(v_a_2221_);
return v_res_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(lean_object* v_type_2229_, lean_object* v_k_2230_, uint8_t v_cleanupAnnotations_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_){
_start:
{
lean_object* v___f_2237_; uint8_t v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___f_2237_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2237_, 0, v_k_2230_);
v___x_2238_ = 0;
v___x_2239_ = lean_box(0);
v___x_2240_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_2238_, v___x_2239_, v_type_2229_, v___f_2237_, v_cleanupAnnotations_2231_, v___x_2238_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
if (lean_obj_tag(v___x_2240_) == 0)
{
lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2248_; 
v_a_2241_ = lean_ctor_get(v___x_2240_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2243_ = v___x_2240_;
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_dec(v___x_2240_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2246_; 
if (v_isShared_2244_ == 0)
{
v___x_2246_ = v___x_2243_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_a_2241_);
v___x_2246_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
return v___x_2246_;
}
}
}
else
{
lean_object* v_a_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2256_; 
v_a_2249_ = lean_ctor_get(v___x_2240_, 0);
v_isSharedCheck_2256_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2251_ = v___x_2240_;
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_a_2249_);
lean_dec(v___x_2240_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
lean_object* v___x_2254_; 
if (v_isShared_2252_ == 0)
{
v___x_2254_ = v___x_2251_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v_a_2249_);
v___x_2254_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
return v___x_2254_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg___boxed(lean_object* v_type_2257_, lean_object* v_k_2258_, lean_object* v_cleanupAnnotations_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2265_; lean_object* v_res_2266_; 
v_cleanupAnnotations_boxed_2265_ = lean_unbox(v_cleanupAnnotations_2259_);
v_res_2266_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(v_type_2257_, v_k_2258_, v_cleanupAnnotations_boxed_2265_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
return v_res_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1(lean_object* v_00_u03b1_2267_, lean_object* v_type_2268_, lean_object* v_k_2269_, uint8_t v_cleanupAnnotations_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_){
_start:
{
lean_object* v___x_2276_; 
v___x_2276_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(v_type_2268_, v_k_2269_, v_cleanupAnnotations_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_);
return v___x_2276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___boxed(lean_object* v_00_u03b1_2277_, lean_object* v_type_2278_, lean_object* v_k_2279_, lean_object* v_cleanupAnnotations_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2286_; lean_object* v_res_2287_; 
v_cleanupAnnotations_boxed_2286_ = lean_unbox(v_cleanupAnnotations_2280_);
v_res_2287_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1(v_00_u03b1_2277_, v_type_2278_, v_k_2279_, v_cleanupAnnotations_boxed_2286_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
return v_res_2287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(lean_object* v_e_2288_, lean_object* v_k_2289_, uint8_t v_cleanupAnnotations_2290_, uint8_t v_preserveNondepLet_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_){
_start:
{
lean_object* v___f_2297_; uint8_t v___x_2298_; uint8_t v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
v___f_2297_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2297_, 0, v_k_2289_);
v___x_2298_ = 1;
v___x_2299_ = 0;
v___x_2300_ = lean_box(0);
v___x_2301_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2288_, v___x_2298_, v___x_2298_, v_preserveNondepLet_2291_, v___x_2299_, v___x_2300_, v___f_2297_, v_cleanupAnnotations_2290_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_);
if (lean_obj_tag(v___x_2301_) == 0)
{
lean_object* v_a_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2309_; 
v_a_2302_ = lean_ctor_get(v___x_2301_, 0);
v_isSharedCheck_2309_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2304_ = v___x_2301_;
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_a_2302_);
lean_dec(v___x_2301_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2307_; 
if (v_isShared_2305_ == 0)
{
v___x_2307_ = v___x_2304_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_a_2302_);
v___x_2307_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
return v___x_2307_;
}
}
}
else
{
lean_object* v_a_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2317_; 
v_a_2310_ = lean_ctor_get(v___x_2301_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2312_ = v___x_2301_;
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_a_2310_);
lean_dec(v___x_2301_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2315_; 
if (v_isShared_2313_ == 0)
{
v___x_2315_ = v___x_2312_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_a_2310_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
return v___x_2315_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg___boxed(lean_object* v_e_2318_, lean_object* v_k_2319_, lean_object* v_cleanupAnnotations_2320_, lean_object* v_preserveNondepLet_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2327_; uint8_t v_preserveNondepLet_boxed_2328_; lean_object* v_res_2329_; 
v_cleanupAnnotations_boxed_2327_ = lean_unbox(v_cleanupAnnotations_2320_);
v_preserveNondepLet_boxed_2328_ = lean_unbox(v_preserveNondepLet_2321_);
v_res_2329_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(v_e_2318_, v_k_2319_, v_cleanupAnnotations_boxed_2327_, v_preserveNondepLet_boxed_2328_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
return v_res_2329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2(lean_object* v_00_u03b1_2330_, lean_object* v_e_2331_, lean_object* v_k_2332_, uint8_t v_cleanupAnnotations_2333_, uint8_t v_preserveNondepLet_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_){
_start:
{
lean_object* v___x_2340_; 
v___x_2340_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(v_e_2331_, v_k_2332_, v_cleanupAnnotations_2333_, v_preserveNondepLet_2334_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_);
return v___x_2340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___boxed(lean_object* v_00_u03b1_2341_, lean_object* v_e_2342_, lean_object* v_k_2343_, lean_object* v_cleanupAnnotations_2344_, lean_object* v_preserveNondepLet_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2351_; uint8_t v_preserveNondepLet_boxed_2352_; lean_object* v_res_2353_; 
v_cleanupAnnotations_boxed_2351_ = lean_unbox(v_cleanupAnnotations_2344_);
v_preserveNondepLet_boxed_2352_ = lean_unbox(v_preserveNondepLet_2345_);
v_res_2353_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2(v_00_u03b1_2341_, v_e_2342_, v_k_2343_, v_cleanupAnnotations_boxed_2351_, v_preserveNondepLet_boxed_2352_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_);
lean_dec(v___y_2349_);
lean_dec_ref(v___y_2348_);
lean_dec(v___y_2347_);
lean_dec_ref(v___y_2346_);
return v_res_2353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(lean_object* v_f_2354_, lean_object* v_e_x27_2355_, lean_object* v_a_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_){
_start:
{
lean_object* v___x_2362_; 
lean_inc(v___y_2360_);
lean_inc_ref(v___y_2359_);
lean_inc(v___y_2358_);
lean_inc_ref(v___y_2357_);
lean_inc_ref(v_e_x27_2355_);
v___x_2362_ = lean_apply_7(v_f_2354_, v_a_2356_, v_e_x27_2355_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, lean_box(0));
if (lean_obj_tag(v___x_2362_) == 0)
{
lean_object* v_a_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2371_; 
v_a_2363_ = lean_ctor_get(v___x_2362_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2365_ = v___x_2362_;
v_isShared_2366_ = v_isSharedCheck_2371_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_a_2363_);
lean_dec(v___x_2362_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2371_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v___x_2367_; lean_object* v___x_2369_; 
v___x_2367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2367_, 0, v_e_x27_2355_);
lean_ctor_set(v___x_2367_, 1, v_a_2363_);
if (v_isShared_2366_ == 0)
{
lean_ctor_set(v___x_2365_, 0, v___x_2367_);
v___x_2369_ = v___x_2365_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v___x_2367_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
}
}
}
else
{
lean_object* v_a_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2379_; 
lean_dec_ref(v_e_x27_2355_);
v_a_2372_ = lean_ctor_get(v___x_2362_, 0);
v_isSharedCheck_2379_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2379_ == 0)
{
v___x_2374_ = v___x_2362_;
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_a_2372_);
lean_dec(v___x_2362_);
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
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0___boxed(lean_object* v_f_2380_, lean_object* v_e_x27_2381_, lean_object* v_a_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_){
_start:
{
lean_object* v_res_2388_; 
v_res_2388_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2380_, v_e_x27_2381_, v_a_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
return v_res_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg(lean_object* v_f_2389_, lean_object* v_x_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_){
_start:
{
switch(lean_obj_tag(v_x_2390_))
{
case 7:
{
lean_object* v_binderName_2397_; lean_object* v_binderType_2398_; lean_object* v_body_2399_; uint8_t v_binderInfo_2400_; lean_object* v___x_2401_; 
v_binderName_2397_ = lean_ctor_get(v_x_2390_, 0);
v_binderType_2398_ = lean_ctor_get(v_x_2390_, 1);
v_body_2399_ = lean_ctor_get(v_x_2390_, 2);
v_binderInfo_2400_ = lean_ctor_get_uint8(v_x_2390_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2398_);
lean_inc_ref(v_f_2389_);
v___x_2401_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2389_, v_binderType_2398_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_);
if (lean_obj_tag(v___x_2401_) == 0)
{
lean_object* v_a_2402_; lean_object* v_fst_2403_; lean_object* v_snd_2404_; lean_object* v___x_2405_; 
v_a_2402_ = lean_ctor_get(v___x_2401_, 0);
lean_inc(v_a_2402_);
lean_dec_ref_known(v___x_2401_, 1);
v_fst_2403_ = lean_ctor_get(v_a_2402_, 0);
lean_inc(v_fst_2403_);
v_snd_2404_ = lean_ctor_get(v_a_2402_, 1);
lean_inc(v_snd_2404_);
lean_dec(v_a_2402_);
lean_inc_ref(v_body_2399_);
v___x_2405_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2389_, v_body_2399_, v_snd_2404_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_);
if (lean_obj_tag(v___x_2405_) == 0)
{
lean_object* v_a_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2435_; 
v_a_2406_ = lean_ctor_get(v___x_2405_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___x_2405_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2408_ = v___x_2405_;
v_isShared_2409_ = v_isSharedCheck_2435_;
goto v_resetjp_2407_;
}
else
{
lean_inc(v_a_2406_);
lean_dec(v___x_2405_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2435_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
lean_object* v_fst_2410_; lean_object* v_snd_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2434_; 
v_fst_2410_ = lean_ctor_get(v_a_2406_, 0);
v_snd_2411_ = lean_ctor_get(v_a_2406_, 1);
v_isSharedCheck_2434_ = !lean_is_exclusive(v_a_2406_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2413_ = v_a_2406_;
v_isShared_2414_ = v_isSharedCheck_2434_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_snd_2411_);
lean_inc(v_fst_2410_);
lean_dec(v_a_2406_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2434_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v___y_2416_; uint8_t v___y_2424_; size_t v___x_2428_; size_t v___x_2429_; uint8_t v___x_2430_; 
v___x_2428_ = lean_ptr_addr(v_binderType_2398_);
v___x_2429_ = lean_ptr_addr(v_fst_2403_);
v___x_2430_ = lean_usize_dec_eq(v___x_2428_, v___x_2429_);
if (v___x_2430_ == 0)
{
v___y_2424_ = v___x_2430_;
goto v___jp_2423_;
}
else
{
size_t v___x_2431_; size_t v___x_2432_; uint8_t v___x_2433_; 
v___x_2431_ = lean_ptr_addr(v_body_2399_);
v___x_2432_ = lean_ptr_addr(v_fst_2410_);
v___x_2433_ = lean_usize_dec_eq(v___x_2431_, v___x_2432_);
v___y_2424_ = v___x_2433_;
goto v___jp_2423_;
}
v___jp_2415_:
{
lean_object* v___x_2418_; 
if (v_isShared_2414_ == 0)
{
lean_ctor_set(v___x_2413_, 0, v___y_2416_);
v___x_2418_ = v___x_2413_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v___y_2416_);
lean_ctor_set(v_reuseFailAlloc_2422_, 1, v_snd_2411_);
v___x_2418_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
lean_object* v___x_2420_; 
if (v_isShared_2409_ == 0)
{
lean_ctor_set(v___x_2408_, 0, v___x_2418_);
v___x_2420_ = v___x_2408_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v___x_2418_);
v___x_2420_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2419_;
}
v_reusejp_2419_:
{
return v___x_2420_;
}
}
}
v___jp_2423_:
{
if (v___y_2424_ == 0)
{
lean_object* v___x_2425_; 
lean_inc(v_binderName_2397_);
lean_dec_ref_known(v_x_2390_, 3);
v___x_2425_ = l_Lean_Expr_forallE___override(v_binderName_2397_, v_fst_2403_, v_fst_2410_, v_binderInfo_2400_);
v___y_2416_ = v___x_2425_;
goto v___jp_2415_;
}
else
{
uint8_t v___x_2426_; 
v___x_2426_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2400_, v_binderInfo_2400_);
if (v___x_2426_ == 0)
{
lean_object* v___x_2427_; 
lean_inc(v_binderName_2397_);
lean_dec_ref_known(v_x_2390_, 3);
v___x_2427_ = l_Lean_Expr_forallE___override(v_binderName_2397_, v_fst_2403_, v_fst_2410_, v_binderInfo_2400_);
v___y_2416_ = v___x_2427_;
goto v___jp_2415_;
}
else
{
lean_dec(v_fst_2410_);
lean_dec(v_fst_2403_);
v___y_2416_ = v_x_2390_;
goto v___jp_2415_;
}
}
}
}
}
}
else
{
lean_dec(v_fst_2403_);
lean_dec_ref_known(v_x_2390_, 3);
return v___x_2405_;
}
}
else
{
lean_dec_ref_known(v_x_2390_, 3);
lean_dec_ref(v_f_2389_);
return v___x_2401_;
}
}
case 6:
{
lean_object* v_binderName_2436_; lean_object* v_binderType_2437_; lean_object* v_body_2438_; uint8_t v_binderInfo_2439_; lean_object* v___x_2440_; 
v_binderName_2436_ = lean_ctor_get(v_x_2390_, 0);
v_binderType_2437_ = lean_ctor_get(v_x_2390_, 1);
v_body_2438_ = lean_ctor_get(v_x_2390_, 2);
v_binderInfo_2439_ = lean_ctor_get_uint8(v_x_2390_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2437_);
lean_inc_ref(v_f_2389_);
v___x_2440_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2389_, v_binderType_2437_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_);
if (lean_obj_tag(v___x_2440_) == 0)
{
lean_object* v_a_2441_; lean_object* v_fst_2442_; lean_object* v_snd_2443_; lean_object* v___x_2444_; 
v_a_2441_ = lean_ctor_get(v___x_2440_, 0);
lean_inc(v_a_2441_);
lean_dec_ref_known(v___x_2440_, 1);
v_fst_2442_ = lean_ctor_get(v_a_2441_, 0);
lean_inc(v_fst_2442_);
v_snd_2443_ = lean_ctor_get(v_a_2441_, 1);
lean_inc(v_snd_2443_);
lean_dec(v_a_2441_);
lean_inc_ref(v_body_2438_);
v___x_2444_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2389_, v_body_2438_, v_snd_2443_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_);
if (lean_obj_tag(v___x_2444_) == 0)
{
lean_object* v_a_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2474_; 
v_a_2445_ = lean_ctor_get(v___x_2444_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2444_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2447_ = v___x_2444_;
v_isShared_2448_ = v_isSharedCheck_2474_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_a_2445_);
lean_dec(v___x_2444_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2474_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
lean_object* v_fst_2449_; lean_object* v_snd_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2473_; 
v_fst_2449_ = lean_ctor_get(v_a_2445_, 0);
v_snd_2450_ = lean_ctor_get(v_a_2445_, 1);
v_isSharedCheck_2473_ = !lean_is_exclusive(v_a_2445_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2452_ = v_a_2445_;
v_isShared_2453_ = v_isSharedCheck_2473_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_snd_2450_);
lean_inc(v_fst_2449_);
lean_dec(v_a_2445_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2473_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v___y_2455_; uint8_t v___y_2463_; size_t v___x_2467_; size_t v___x_2468_; uint8_t v___x_2469_; 
v___x_2467_ = lean_ptr_addr(v_binderType_2437_);
v___x_2468_ = lean_ptr_addr(v_fst_2442_);
v___x_2469_ = lean_usize_dec_eq(v___x_2467_, v___x_2468_);
if (v___x_2469_ == 0)
{
v___y_2463_ = v___x_2469_;
goto v___jp_2462_;
}
else
{
size_t v___x_2470_; size_t v___x_2471_; uint8_t v___x_2472_; 
v___x_2470_ = lean_ptr_addr(v_body_2438_);
v___x_2471_ = lean_ptr_addr(v_fst_2449_);
v___x_2472_ = lean_usize_dec_eq(v___x_2470_, v___x_2471_);
v___y_2463_ = v___x_2472_;
goto v___jp_2462_;
}
v___jp_2454_:
{
lean_object* v___x_2457_; 
if (v_isShared_2453_ == 0)
{
lean_ctor_set(v___x_2452_, 0, v___y_2455_);
v___x_2457_ = v___x_2452_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v___y_2455_);
lean_ctor_set(v_reuseFailAlloc_2461_, 1, v_snd_2450_);
v___x_2457_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
lean_object* v___x_2459_; 
if (v_isShared_2448_ == 0)
{
lean_ctor_set(v___x_2447_, 0, v___x_2457_);
v___x_2459_ = v___x_2447_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v___x_2457_);
v___x_2459_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
return v___x_2459_;
}
}
}
v___jp_2462_:
{
if (v___y_2463_ == 0)
{
lean_object* v___x_2464_; 
lean_inc(v_binderName_2436_);
lean_dec_ref_known(v_x_2390_, 3);
v___x_2464_ = l_Lean_Expr_lam___override(v_binderName_2436_, v_fst_2442_, v_fst_2449_, v_binderInfo_2439_);
v___y_2455_ = v___x_2464_;
goto v___jp_2454_;
}
else
{
uint8_t v___x_2465_; 
v___x_2465_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2439_, v_binderInfo_2439_);
if (v___x_2465_ == 0)
{
lean_object* v___x_2466_; 
lean_inc(v_binderName_2436_);
lean_dec_ref_known(v_x_2390_, 3);
v___x_2466_ = l_Lean_Expr_lam___override(v_binderName_2436_, v_fst_2442_, v_fst_2449_, v_binderInfo_2439_);
v___y_2455_ = v___x_2466_;
goto v___jp_2454_;
}
else
{
lean_dec(v_fst_2449_);
lean_dec(v_fst_2442_);
v___y_2455_ = v_x_2390_;
goto v___jp_2454_;
}
}
}
}
}
}
else
{
lean_dec(v_fst_2442_);
lean_dec_ref_known(v_x_2390_, 3);
return v___x_2444_;
}
}
else
{
lean_dec_ref_known(v_x_2390_, 3);
lean_dec_ref(v_f_2389_);
return v___x_2440_;
}
}
case 10:
{
lean_object* v_data_2475_; lean_object* v_expr_2476_; lean_object* v___x_2477_; 
v_data_2475_ = lean_ctor_get(v_x_2390_, 0);
v_expr_2476_ = lean_ctor_get(v_x_2390_, 1);
lean_inc_ref(v_expr_2476_);
v___x_2477_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2389_, v_expr_2476_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_);
if (lean_obj_tag(v___x_2477_) == 0)
{
lean_object* v_a_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2500_; 
v_a_2478_ = lean_ctor_get(v___x_2477_, 0);
v_isSharedCheck_2500_ = !lean_is_exclusive(v___x_2477_);
if (v_isSharedCheck_2500_ == 0)
{
v___x_2480_ = v___x_2477_;
v_isShared_2481_ = v_isSharedCheck_2500_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_a_2478_);
lean_dec(v___x_2477_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2500_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v_fst_2482_; lean_object* v_snd_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2499_; 
v_fst_2482_ = lean_ctor_get(v_a_2478_, 0);
v_snd_2483_ = lean_ctor_get(v_a_2478_, 1);
v_isSharedCheck_2499_ = !lean_is_exclusive(v_a_2478_);
if (v_isSharedCheck_2499_ == 0)
{
v___x_2485_ = v_a_2478_;
v_isShared_2486_ = v_isSharedCheck_2499_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_snd_2483_);
lean_inc(v_fst_2482_);
lean_dec(v_a_2478_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2499_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___y_2488_; size_t v___x_2495_; size_t v___x_2496_; uint8_t v___x_2497_; 
v___x_2495_ = lean_ptr_addr(v_expr_2476_);
v___x_2496_ = lean_ptr_addr(v_fst_2482_);
v___x_2497_ = lean_usize_dec_eq(v___x_2495_, v___x_2496_);
if (v___x_2497_ == 0)
{
lean_object* v___x_2498_; 
lean_inc(v_data_2475_);
lean_dec_ref_known(v_x_2390_, 2);
v___x_2498_ = l_Lean_Expr_mdata___override(v_data_2475_, v_fst_2482_);
v___y_2488_ = v___x_2498_;
goto v___jp_2487_;
}
else
{
lean_dec(v_fst_2482_);
v___y_2488_ = v_x_2390_;
goto v___jp_2487_;
}
v___jp_2487_:
{
lean_object* v___x_2490_; 
if (v_isShared_2486_ == 0)
{
lean_ctor_set(v___x_2485_, 0, v___y_2488_);
v___x_2490_ = v___x_2485_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v___y_2488_);
lean_ctor_set(v_reuseFailAlloc_2494_, 1, v_snd_2483_);
v___x_2490_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
lean_object* v___x_2492_; 
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 0, v___x_2490_);
v___x_2492_ = v___x_2480_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v___x_2490_);
v___x_2492_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
return v___x_2492_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_x_2390_, 2);
return v___x_2477_;
}
}
case 8:
{
lean_object* v_declName_2501_; lean_object* v_type_2502_; lean_object* v_value_2503_; lean_object* v_body_2504_; uint8_t v_nondep_2505_; lean_object* v___x_2506_; 
v_declName_2501_ = lean_ctor_get(v_x_2390_, 0);
v_type_2502_ = lean_ctor_get(v_x_2390_, 1);
v_value_2503_ = lean_ctor_get(v_x_2390_, 2);
v_body_2504_ = lean_ctor_get(v_x_2390_, 3);
v_nondep_2505_ = lean_ctor_get_uint8(v_x_2390_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_2502_);
lean_inc_ref(v_f_2389_);
v___x_2506_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2389_, v_type_2502_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_);
if (lean_obj_tag(v___x_2506_) == 0)
{
lean_object* v_a_2507_; lean_object* v_fst_2508_; lean_object* v_snd_2509_; lean_object* v___x_2510_; 
v_a_2507_ = lean_ctor_get(v___x_2506_, 0);
lean_inc(v_a_2507_);
lean_dec_ref_known(v___x_2506_, 1);
v_fst_2508_ = lean_ctor_get(v_a_2507_, 0);
lean_inc(v_fst_2508_);
v_snd_2509_ = lean_ctor_get(v_a_2507_, 1);
lean_inc(v_snd_2509_);
lean_dec(v_a_2507_);
lean_inc_ref(v_value_2503_);
lean_inc_ref(v_f_2389_);
v___x_2510_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2389_, v_value_2503_, v_snd_2509_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_);
if (lean_obj_tag(v___x_2510_) == 0)
{
lean_object* v_a_2511_; lean_object* v_fst_2512_; lean_object* v_snd_2513_; lean_object* v___x_2514_; 
v_a_2511_ = lean_ctor_get(v___x_2510_, 0);
lean_inc(v_a_2511_);
lean_dec_ref_known(v___x_2510_, 1);
v_fst_2512_ = lean_ctor_get(v_a_2511_, 0);
lean_inc(v_fst_2512_);
v_snd_2513_ = lean_ctor_get(v_a_2511_, 1);
lean_inc(v_snd_2513_);
lean_dec(v_a_2511_);
lean_inc_ref(v_body_2504_);
v___x_2514_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2389_, v_body_2504_, v_snd_2513_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_);
if (lean_obj_tag(v___x_2514_) == 0)
{
lean_object* v_a_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2546_; 
v_a_2515_ = lean_ctor_get(v___x_2514_, 0);
v_isSharedCheck_2546_ = !lean_is_exclusive(v___x_2514_);
if (v_isSharedCheck_2546_ == 0)
{
v___x_2517_ = v___x_2514_;
v_isShared_2518_ = v_isSharedCheck_2546_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_a_2515_);
lean_dec(v___x_2514_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2546_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
lean_object* v_fst_2519_; lean_object* v_snd_2520_; lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2545_; 
v_fst_2519_ = lean_ctor_get(v_a_2515_, 0);
v_snd_2520_ = lean_ctor_get(v_a_2515_, 1);
v_isSharedCheck_2545_ = !lean_is_exclusive(v_a_2515_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2522_ = v_a_2515_;
v_isShared_2523_ = v_isSharedCheck_2545_;
goto v_resetjp_2521_;
}
else
{
lean_inc(v_snd_2520_);
lean_inc(v_fst_2519_);
lean_dec(v_a_2515_);
v___x_2522_ = lean_box(0);
v_isShared_2523_ = v_isSharedCheck_2545_;
goto v_resetjp_2521_;
}
v_resetjp_2521_:
{
lean_object* v___y_2525_; uint8_t v___y_2533_; size_t v___x_2539_; size_t v___x_2540_; uint8_t v___x_2541_; 
v___x_2539_ = lean_ptr_addr(v_type_2502_);
v___x_2540_ = lean_ptr_addr(v_fst_2508_);
v___x_2541_ = lean_usize_dec_eq(v___x_2539_, v___x_2540_);
if (v___x_2541_ == 0)
{
v___y_2533_ = v___x_2541_;
goto v___jp_2532_;
}
else
{
size_t v___x_2542_; size_t v___x_2543_; uint8_t v___x_2544_; 
v___x_2542_ = lean_ptr_addr(v_value_2503_);
v___x_2543_ = lean_ptr_addr(v_fst_2512_);
v___x_2544_ = lean_usize_dec_eq(v___x_2542_, v___x_2543_);
v___y_2533_ = v___x_2544_;
goto v___jp_2532_;
}
v___jp_2524_:
{
lean_object* v___x_2527_; 
if (v_isShared_2523_ == 0)
{
lean_ctor_set(v___x_2522_, 0, v___y_2525_);
v___x_2527_ = v___x_2522_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v___y_2525_);
lean_ctor_set(v_reuseFailAlloc_2531_, 1, v_snd_2520_);
v___x_2527_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
lean_object* v___x_2529_; 
if (v_isShared_2518_ == 0)
{
lean_ctor_set(v___x_2517_, 0, v___x_2527_);
v___x_2529_ = v___x_2517_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v___x_2527_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
v___jp_2532_:
{
if (v___y_2533_ == 0)
{
lean_object* v___x_2534_; 
lean_inc(v_declName_2501_);
lean_dec_ref_known(v_x_2390_, 4);
v___x_2534_ = l_Lean_Expr_letE___override(v_declName_2501_, v_fst_2508_, v_fst_2512_, v_fst_2519_, v_nondep_2505_);
v___y_2525_ = v___x_2534_;
goto v___jp_2524_;
}
else
{
size_t v___x_2535_; size_t v___x_2536_; uint8_t v___x_2537_; 
v___x_2535_ = lean_ptr_addr(v_body_2504_);
v___x_2536_ = lean_ptr_addr(v_fst_2519_);
v___x_2537_ = lean_usize_dec_eq(v___x_2535_, v___x_2536_);
if (v___x_2537_ == 0)
{
lean_object* v___x_2538_; 
lean_inc(v_declName_2501_);
lean_dec_ref_known(v_x_2390_, 4);
v___x_2538_ = l_Lean_Expr_letE___override(v_declName_2501_, v_fst_2508_, v_fst_2512_, v_fst_2519_, v_nondep_2505_);
v___y_2525_ = v___x_2538_;
goto v___jp_2524_;
}
else
{
lean_dec(v_fst_2519_);
lean_dec(v_fst_2512_);
lean_dec(v_fst_2508_);
v___y_2525_ = v_x_2390_;
goto v___jp_2524_;
}
}
}
}
}
}
else
{
lean_dec(v_fst_2512_);
lean_dec(v_fst_2508_);
lean_dec_ref_known(v_x_2390_, 4);
return v___x_2514_;
}
}
else
{
lean_dec(v_fst_2508_);
lean_dec_ref_known(v_x_2390_, 4);
lean_dec_ref(v_f_2389_);
return v___x_2510_;
}
}
else
{
lean_dec_ref_known(v_x_2390_, 4);
lean_dec_ref(v_f_2389_);
return v___x_2506_;
}
}
case 5:
{
lean_object* v_fn_2547_; lean_object* v_arg_2548_; lean_object* v___x_2549_; 
v_fn_2547_ = lean_ctor_get(v_x_2390_, 0);
v_arg_2548_ = lean_ctor_get(v_x_2390_, 1);
lean_inc_ref(v_fn_2547_);
lean_inc_ref(v_f_2389_);
v___x_2549_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2389_, v_fn_2547_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_);
if (lean_obj_tag(v___x_2549_) == 0)
{
lean_object* v_a_2550_; lean_object* v_fst_2551_; lean_object* v_snd_2552_; lean_object* v___x_2553_; 
v_a_2550_ = lean_ctor_get(v___x_2549_, 0);
lean_inc(v_a_2550_);
lean_dec_ref_known(v___x_2549_, 1);
v_fst_2551_ = lean_ctor_get(v_a_2550_, 0);
lean_inc(v_fst_2551_);
v_snd_2552_ = lean_ctor_get(v_a_2550_, 1);
lean_inc(v_snd_2552_);
lean_dec(v_a_2550_);
lean_inc_ref(v_arg_2548_);
v___x_2553_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2389_, v_arg_2548_, v_snd_2552_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_);
if (lean_obj_tag(v___x_2553_) == 0)
{
lean_object* v_a_2554_; lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2581_; 
v_a_2554_ = lean_ctor_get(v___x_2553_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2556_ = v___x_2553_;
v_isShared_2557_ = v_isSharedCheck_2581_;
goto v_resetjp_2555_;
}
else
{
lean_inc(v_a_2554_);
lean_dec(v___x_2553_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2581_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
lean_object* v_fst_2558_; lean_object* v_snd_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2580_; 
v_fst_2558_ = lean_ctor_get(v_a_2554_, 0);
v_snd_2559_ = lean_ctor_get(v_a_2554_, 1);
v_isSharedCheck_2580_ = !lean_is_exclusive(v_a_2554_);
if (v_isSharedCheck_2580_ == 0)
{
v___x_2561_ = v_a_2554_;
v_isShared_2562_ = v_isSharedCheck_2580_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_snd_2559_);
lean_inc(v_fst_2558_);
lean_dec(v_a_2554_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2580_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v___y_2564_; uint8_t v___y_2572_; size_t v___x_2574_; size_t v___x_2575_; uint8_t v___x_2576_; 
v___x_2574_ = lean_ptr_addr(v_fn_2547_);
v___x_2575_ = lean_ptr_addr(v_fst_2551_);
v___x_2576_ = lean_usize_dec_eq(v___x_2574_, v___x_2575_);
if (v___x_2576_ == 0)
{
v___y_2572_ = v___x_2576_;
goto v___jp_2571_;
}
else
{
size_t v___x_2577_; size_t v___x_2578_; uint8_t v___x_2579_; 
v___x_2577_ = lean_ptr_addr(v_arg_2548_);
v___x_2578_ = lean_ptr_addr(v_fst_2558_);
v___x_2579_ = lean_usize_dec_eq(v___x_2577_, v___x_2578_);
v___y_2572_ = v___x_2579_;
goto v___jp_2571_;
}
v___jp_2563_:
{
lean_object* v___x_2566_; 
if (v_isShared_2562_ == 0)
{
lean_ctor_set(v___x_2561_, 0, v___y_2564_);
v___x_2566_ = v___x_2561_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v___y_2564_);
lean_ctor_set(v_reuseFailAlloc_2570_, 1, v_snd_2559_);
v___x_2566_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
lean_object* v___x_2568_; 
if (v_isShared_2557_ == 0)
{
lean_ctor_set(v___x_2556_, 0, v___x_2566_);
v___x_2568_ = v___x_2556_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v___x_2566_);
v___x_2568_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
return v___x_2568_;
}
}
}
v___jp_2571_:
{
if (v___y_2572_ == 0)
{
lean_object* v___x_2573_; 
lean_dec_ref_known(v_x_2390_, 2);
v___x_2573_ = l_Lean_Expr_app___override(v_fst_2551_, v_fst_2558_);
v___y_2564_ = v___x_2573_;
goto v___jp_2563_;
}
else
{
lean_dec(v_fst_2558_);
lean_dec(v_fst_2551_);
v___y_2564_ = v_x_2390_;
goto v___jp_2563_;
}
}
}
}
}
else
{
lean_dec(v_fst_2551_);
lean_dec_ref_known(v_x_2390_, 2);
return v___x_2553_;
}
}
else
{
lean_dec_ref_known(v_x_2390_, 2);
lean_dec_ref(v_f_2389_);
return v___x_2549_;
}
}
case 11:
{
lean_object* v_typeName_2582_; lean_object* v_idx_2583_; lean_object* v_struct_2584_; lean_object* v___x_2585_; 
v_typeName_2582_ = lean_ctor_get(v_x_2390_, 0);
v_idx_2583_ = lean_ctor_get(v_x_2390_, 1);
v_struct_2584_ = lean_ctor_get(v_x_2390_, 2);
lean_inc_ref(v_struct_2584_);
v___x_2585_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2389_, v_struct_2584_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_);
if (lean_obj_tag(v___x_2585_) == 0)
{
lean_object* v_a_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2608_; 
v_a_2586_ = lean_ctor_get(v___x_2585_, 0);
v_isSharedCheck_2608_ = !lean_is_exclusive(v___x_2585_);
if (v_isSharedCheck_2608_ == 0)
{
v___x_2588_ = v___x_2585_;
v_isShared_2589_ = v_isSharedCheck_2608_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_a_2586_);
lean_dec(v___x_2585_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2608_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
lean_object* v_fst_2590_; lean_object* v_snd_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2607_; 
v_fst_2590_ = lean_ctor_get(v_a_2586_, 0);
v_snd_2591_ = lean_ctor_get(v_a_2586_, 1);
v_isSharedCheck_2607_ = !lean_is_exclusive(v_a_2586_);
if (v_isSharedCheck_2607_ == 0)
{
v___x_2593_ = v_a_2586_;
v_isShared_2594_ = v_isSharedCheck_2607_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_snd_2591_);
lean_inc(v_fst_2590_);
lean_dec(v_a_2586_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2607_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___y_2596_; size_t v___x_2603_; size_t v___x_2604_; uint8_t v___x_2605_; 
v___x_2603_ = lean_ptr_addr(v_struct_2584_);
v___x_2604_ = lean_ptr_addr(v_fst_2590_);
v___x_2605_ = lean_usize_dec_eq(v___x_2603_, v___x_2604_);
if (v___x_2605_ == 0)
{
lean_object* v___x_2606_; 
lean_inc(v_idx_2583_);
lean_inc(v_typeName_2582_);
lean_dec_ref_known(v_x_2390_, 3);
v___x_2606_ = l_Lean_Expr_proj___override(v_typeName_2582_, v_idx_2583_, v_fst_2590_);
v___y_2596_ = v___x_2606_;
goto v___jp_2595_;
}
else
{
lean_dec(v_fst_2590_);
v___y_2596_ = v_x_2390_;
goto v___jp_2595_;
}
v___jp_2595_:
{
lean_object* v___x_2598_; 
if (v_isShared_2594_ == 0)
{
lean_ctor_set(v___x_2593_, 0, v___y_2596_);
v___x_2598_ = v___x_2593_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v___y_2596_);
lean_ctor_set(v_reuseFailAlloc_2602_, 1, v_snd_2591_);
v___x_2598_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
lean_object* v___x_2600_; 
if (v_isShared_2589_ == 0)
{
lean_ctor_set(v___x_2588_, 0, v___x_2598_);
v___x_2600_ = v___x_2588_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v___x_2598_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
return v___x_2600_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_x_2390_, 3);
return v___x_2585_;
}
}
default: 
{
lean_object* v___x_2609_; lean_object* v___x_2610_; 
lean_dec_ref(v_f_2389_);
v___x_2609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2609_, 0, v_x_2390_);
lean_ctor_set(v___x_2609_, 1, v___y_2391_);
v___x_2610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2610_, 0, v___x_2609_);
return v___x_2610_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___boxed(lean_object* v_f_2611_, lean_object* v_x_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_){
_start:
{
lean_object* v_res_2619_; 
v_res_2619_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg(v_f_2611_, v_x_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_);
lean_dec(v___y_2617_);
lean_dec_ref(v___y_2616_);
lean_dec(v___y_2615_);
lean_dec_ref(v___y_2614_);
return v_res_2619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg(lean_object* v_f_2620_, lean_object* v_init_2621_, lean_object* v_e_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_){
_start:
{
lean_object* v___x_2628_; 
v___x_2628_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg(v_f_2620_, v_e_2622_, v_init_2621_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_);
if (lean_obj_tag(v___x_2628_) == 0)
{
lean_object* v_a_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2637_; 
v_a_2629_ = lean_ctor_get(v___x_2628_, 0);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2628_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2631_ = v___x_2628_;
v_isShared_2632_ = v_isSharedCheck_2637_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_a_2629_);
lean_dec(v___x_2628_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2637_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v_snd_2633_; lean_object* v___x_2635_; 
v_snd_2633_ = lean_ctor_get(v_a_2629_, 1);
lean_inc(v_snd_2633_);
lean_dec(v_a_2629_);
if (v_isShared_2632_ == 0)
{
lean_ctor_set(v___x_2631_, 0, v_snd_2633_);
v___x_2635_ = v___x_2631_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v_snd_2633_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
return v___x_2635_;
}
}
}
else
{
lean_object* v_a_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2645_; 
v_a_2638_ = lean_ctor_get(v___x_2628_, 0);
v_isSharedCheck_2645_ = !lean_is_exclusive(v___x_2628_);
if (v_isSharedCheck_2645_ == 0)
{
v___x_2640_ = v___x_2628_;
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_a_2638_);
lean_dec(v___x_2628_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v___x_2643_; 
if (v_isShared_2641_ == 0)
{
v___x_2643_ = v___x_2640_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v_a_2638_);
v___x_2643_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
return v___x_2643_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg___boxed(lean_object* v_f_2646_, lean_object* v_init_2647_, lean_object* v_e_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_){
_start:
{
lean_object* v_res_2654_; 
v_res_2654_ = l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg(v_f_2646_, v_init_2647_, v_e_2648_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_);
lean_dec(v___y_2652_);
lean_dec_ref(v___y_2651_);
lean_dec(v___y_2650_);
lean_dec_ref(v___y_2649_);
return v_res_2654_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(lean_object* v_op_2657_, lean_object* v_as_2658_, size_t v_i_2659_, size_t v_stop_2660_, lean_object* v_b_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_){
_start:
{
lean_object* v_a_2668_; uint8_t v___x_2672_; 
v___x_2672_ = lean_usize_dec_eq(v_i_2659_, v_stop_2660_);
if (v___x_2672_ == 0)
{
lean_object* v___x_2673_; lean_object* v___x_2674_; 
v___x_2673_ = lean_array_uget_borrowed(v_as_2658_, v_i_2659_);
lean_inc(v___y_2665_);
lean_inc_ref(v___y_2664_);
lean_inc(v___y_2663_);
lean_inc_ref(v___y_2662_);
lean_inc(v___x_2673_);
v___x_2674_ = lean_infer_type(v___x_2673_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_);
if (lean_obj_tag(v___x_2674_) == 0)
{
lean_object* v_a_2675_; lean_object* v___x_2676_; 
v_a_2675_ = lean_ctor_get(v___x_2674_, 0);
lean_inc(v_a_2675_);
lean_dec_ref_known(v___x_2674_, 1);
lean_inc_ref(v_op_2657_);
v___x_2676_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v_op_2657_, v_a_2675_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_);
if (lean_obj_tag(v___x_2676_) == 0)
{
lean_object* v_a_2677_; lean_object* v___x_2678_; 
v_a_2677_ = lean_ctor_get(v___x_2676_, 0);
lean_inc(v_a_2677_);
lean_dec_ref_known(v___x_2676_, 1);
v___x_2678_ = l_Array_append___redArg(v_b_2661_, v_a_2677_);
lean_dec(v_a_2677_);
v_a_2668_ = v___x_2678_;
goto v___jp_2667_;
}
else
{
lean_dec_ref(v_b_2661_);
if (lean_obj_tag(v___x_2676_) == 0)
{
lean_object* v_a_2679_; 
v_a_2679_ = lean_ctor_get(v___x_2676_, 0);
lean_inc(v_a_2679_);
lean_dec_ref_known(v___x_2676_, 1);
v_a_2668_ = v_a_2679_;
goto v___jp_2667_;
}
else
{
lean_dec_ref(v_op_2657_);
return v___x_2676_;
}
}
}
else
{
lean_object* v_a_2680_; lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2687_; 
lean_dec_ref(v_b_2661_);
lean_dec_ref(v_op_2657_);
v_a_2680_ = lean_ctor_get(v___x_2674_, 0);
v_isSharedCheck_2687_ = !lean_is_exclusive(v___x_2674_);
if (v_isSharedCheck_2687_ == 0)
{
v___x_2682_ = v___x_2674_;
v_isShared_2683_ = v_isSharedCheck_2687_;
goto v_resetjp_2681_;
}
else
{
lean_inc(v_a_2680_);
lean_dec(v___x_2674_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2687_;
goto v_resetjp_2681_;
}
v_resetjp_2681_:
{
lean_object* v___x_2685_; 
if (v_isShared_2683_ == 0)
{
v___x_2685_ = v___x_2682_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v_a_2680_);
v___x_2685_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
return v___x_2685_;
}
}
}
}
else
{
lean_object* v___x_2688_; 
lean_dec_ref(v_op_2657_);
v___x_2688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2688_, 0, v_b_2661_);
return v___x_2688_;
}
v___jp_2667_:
{
size_t v___x_2669_; size_t v___x_2670_; 
v___x_2669_ = ((size_t)1ULL);
v___x_2670_ = lean_usize_add(v_i_2659_, v___x_2669_);
v_i_2659_ = v___x_2670_;
v_b_2661_ = v_a_2668_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0(lean_object* v_op_2689_, lean_object* v_args_2690_, lean_object* v_body_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_){
_start:
{
lean_object* v___x_2697_; 
lean_inc_ref(v_op_2689_);
v___x_2697_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v_op_2689_, v_body_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_);
if (lean_obj_tag(v___x_2697_) == 0)
{
lean_object* v_a_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2719_; 
v_a_2698_ = lean_ctor_get(v___x_2697_, 0);
v_isSharedCheck_2719_ = !lean_is_exclusive(v___x_2697_);
if (v_isSharedCheck_2719_ == 0)
{
v___x_2700_ = v___x_2697_;
v_isShared_2701_ = v_isSharedCheck_2719_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_a_2698_);
lean_dec(v___x_2697_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2719_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; uint8_t v___x_2705_; 
v___x_2702_ = l_Array_reverse___redArg(v_a_2698_);
v___x_2703_ = lean_unsigned_to_nat(0u);
v___x_2704_ = lean_array_get_size(v_args_2690_);
v___x_2705_ = lean_nat_dec_lt(v___x_2703_, v___x_2704_);
if (v___x_2705_ == 0)
{
lean_object* v___x_2707_; 
lean_dec_ref(v_op_2689_);
if (v_isShared_2701_ == 0)
{
lean_ctor_set(v___x_2700_, 0, v___x_2702_);
v___x_2707_ = v___x_2700_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v___x_2702_);
v___x_2707_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
return v___x_2707_;
}
}
else
{
uint8_t v___x_2709_; 
v___x_2709_ = lean_nat_dec_le(v___x_2704_, v___x_2704_);
if (v___x_2709_ == 0)
{
if (v___x_2705_ == 0)
{
lean_object* v___x_2711_; 
lean_dec_ref(v_op_2689_);
if (v_isShared_2701_ == 0)
{
lean_ctor_set(v___x_2700_, 0, v___x_2702_);
v___x_2711_ = v___x_2700_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v___x_2702_);
v___x_2711_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2710_;
}
v_reusejp_2710_:
{
return v___x_2711_;
}
}
else
{
size_t v___x_2713_; size_t v___x_2714_; lean_object* v___x_2715_; 
lean_del_object(v___x_2700_);
v___x_2713_ = ((size_t)0ULL);
v___x_2714_ = lean_usize_of_nat(v___x_2704_);
v___x_2715_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(v_op_2689_, v_args_2690_, v___x_2713_, v___x_2714_, v___x_2702_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_);
return v___x_2715_;
}
}
else
{
size_t v___x_2716_; size_t v___x_2717_; lean_object* v___x_2718_; 
lean_del_object(v___x_2700_);
v___x_2716_ = ((size_t)0ULL);
v___x_2717_ = lean_usize_of_nat(v___x_2704_);
v___x_2718_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(v_op_2689_, v_args_2690_, v___x_2716_, v___x_2717_, v___x_2702_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_);
return v___x_2718_;
}
}
}
}
else
{
lean_dec_ref(v_op_2689_);
return v___x_2697_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed(lean_object* v_op_2720_, lean_object* v_args_2721_, lean_object* v_body_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_){
_start:
{
lean_object* v_res_2728_; 
v_res_2728_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0(v_op_2720_, v_args_2721_, v_body_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_);
lean_dec(v___y_2726_);
lean_dec_ref(v___y_2725_);
lean_dec(v___y_2724_);
lean_dec_ref(v___y_2723_);
lean_dec_ref(v_args_2721_);
return v_res_2728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3___boxed(lean_object* v_op_2729_, lean_object* v_a_2730_, lean_object* v_f_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_){
_start:
{
lean_object* v_res_2737_; 
v_res_2737_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3(v_op_2729_, v_a_2730_, v_f_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
return v_res_2737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(lean_object* v_op_2738_, lean_object* v_e_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_){
_start:
{
switch(lean_obj_tag(v_e_2739_))
{
case 0:
{
lean_object* v___x_2745_; lean_object* v___x_2746_; 
lean_dec_ref_known(v_e_2739_, 1);
lean_dec_ref(v_op_2738_);
v___x_2745_ = ((lean_object*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___closed__0));
v___x_2746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2746_, 0, v___x_2745_);
return v___x_2746_;
}
case 7:
{
lean_object* v___f_2747_; uint8_t v___x_2748_; lean_object* v___x_2749_; 
v___f_2747_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2747_, 0, v_op_2738_);
v___x_2748_ = 0;
v___x_2749_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(v_e_2739_, v___f_2747_, v___x_2748_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_);
return v___x_2749_;
}
case 6:
{
lean_object* v___f_2750_; uint8_t v___x_2751_; uint8_t v___x_2752_; lean_object* v___x_2753_; 
v___f_2750_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2750_, 0, v_op_2738_);
v___x_2751_ = 0;
v___x_2752_ = 1;
v___x_2753_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(v_e_2739_, v___f_2750_, v___x_2751_, v___x_2752_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_);
return v___x_2753_;
}
case 8:
{
lean_object* v___f_2754_; uint8_t v___x_2755_; uint8_t v___x_2756_; lean_object* v___x_2757_; 
v___f_2754_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2754_, 0, v_op_2738_);
v___x_2755_ = 0;
v___x_2756_ = 1;
v___x_2757_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(v_e_2739_, v___f_2754_, v___x_2755_, v___x_2756_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_);
return v___x_2757_;
}
default: 
{
lean_object* v___x_2758_; 
lean_inc_ref(v_op_2738_);
lean_inc(v_a_2743_);
lean_inc_ref(v_a_2742_);
lean_inc(v_a_2741_);
lean_inc_ref(v_a_2740_);
lean_inc_ref(v_e_2739_);
v___x_2758_ = lean_apply_6(v_op_2738_, v_e_2739_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_, lean_box(0));
if (lean_obj_tag(v___x_2758_) == 0)
{
lean_object* v_a_2759_; lean_object* v___f_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; 
v_a_2759_ = lean_ctor_get(v___x_2758_, 0);
lean_inc(v_a_2759_);
lean_dec_ref_known(v___x_2758_, 1);
v___f_2760_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3___boxed), 8, 1);
lean_closure_set(v___f_2760_, 0, v_op_2738_);
v___x_2761_ = l_Array_reverse___redArg(v_a_2759_);
v___x_2762_ = l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg(v___f_2760_, v___x_2761_, v_e_2739_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_);
return v___x_2762_;
}
else
{
lean_dec_ref(v_e_2739_);
lean_dec_ref(v_op_2738_);
return v___x_2758_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3(lean_object* v_op_2763_, lean_object* v_a_2764_, lean_object* v_f_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_){
_start:
{
lean_object* v___x_2771_; 
v___x_2771_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v_op_2763_, v_f_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_);
if (lean_obj_tag(v___x_2771_) == 0)
{
lean_object* v_a_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2780_; 
v_a_2772_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2780_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2780_ == 0)
{
v___x_2774_ = v___x_2771_;
v_isShared_2775_ = v_isSharedCheck_2780_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_a_2772_);
lean_dec(v___x_2771_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2780_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v___x_2776_; lean_object* v___x_2778_; 
v___x_2776_ = l_Array_append___redArg(v_a_2764_, v_a_2772_);
lean_dec(v_a_2772_);
if (v_isShared_2775_ == 0)
{
lean_ctor_set(v___x_2774_, 0, v___x_2776_);
v___x_2778_ = v___x_2774_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v___x_2776_);
v___x_2778_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
return v___x_2778_;
}
}
}
else
{
lean_dec_ref(v_a_2764_);
return v___x_2771_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg___boxed(lean_object* v_op_2781_, lean_object* v_as_2782_, lean_object* v_i_2783_, lean_object* v_stop_2784_, lean_object* v_b_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_){
_start:
{
size_t v_i_boxed_2791_; size_t v_stop_boxed_2792_; lean_object* v_res_2793_; 
v_i_boxed_2791_ = lean_unbox_usize(v_i_2783_);
lean_dec(v_i_2783_);
v_stop_boxed_2792_ = lean_unbox_usize(v_stop_2784_);
lean_dec(v_stop_2784_);
v_res_2793_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(v_op_2781_, v_as_2782_, v_i_boxed_2791_, v_stop_boxed_2792_, v_b_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_);
lean_dec(v___y_2789_);
lean_dec_ref(v___y_2788_);
lean_dec(v___y_2787_);
lean_dec_ref(v___y_2786_);
lean_dec_ref(v_as_2782_);
return v_res_2793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___boxed(lean_object* v_op_2794_, lean_object* v_e_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_){
_start:
{
lean_object* v_res_2801_; 
v_res_2801_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v_op_2794_, v_e_2795_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_);
lean_dec(v_a_2799_);
lean_dec_ref(v_a_2798_);
lean_dec(v_a_2797_);
lean_dec_ref(v_a_2796_);
return v_res_2801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches(lean_object* v_00_u03b1_2802_, lean_object* v_op_2803_, lean_object* v_e_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_){
_start:
{
lean_object* v___x_2810_; 
v___x_2810_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v_op_2803_, v_e_2804_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_);
return v___x_2810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___boxed(lean_object* v_00_u03b1_2811_, lean_object* v_op_2812_, lean_object* v_e_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_){
_start:
{
lean_object* v_res_2819_; 
v_res_2819_ = l_Lean_Meta_Rewrites_getSubexpressionMatches(v_00_u03b1_2811_, v_op_2812_, v_e_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_);
lean_dec(v_a_2817_);
lean_dec_ref(v_a_2816_);
lean_dec(v_a_2815_);
lean_dec_ref(v_a_2814_);
return v_res_2819_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0(lean_object* v_00_u03b1_2820_, lean_object* v_op_2821_, lean_object* v_as_2822_, size_t v_i_2823_, size_t v_stop_2824_, lean_object* v_b_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_){
_start:
{
lean_object* v___x_2831_; 
v___x_2831_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(v_op_2821_, v_as_2822_, v_i_2823_, v_stop_2824_, v_b_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_);
return v___x_2831_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___boxed(lean_object* v_00_u03b1_2832_, lean_object* v_op_2833_, lean_object* v_as_2834_, lean_object* v_i_2835_, lean_object* v_stop_2836_, lean_object* v_b_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_){
_start:
{
size_t v_i_boxed_2843_; size_t v_stop_boxed_2844_; lean_object* v_res_2845_; 
v_i_boxed_2843_ = lean_unbox_usize(v_i_2835_);
lean_dec(v_i_2835_);
v_stop_boxed_2844_ = lean_unbox_usize(v_stop_2836_);
lean_dec(v_stop_2836_);
v_res_2845_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0(v_00_u03b1_2832_, v_op_2833_, v_as_2834_, v_i_boxed_2843_, v_stop_boxed_2844_, v_b_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_);
lean_dec(v___y_2841_);
lean_dec_ref(v___y_2840_);
lean_dec(v___y_2839_);
lean_dec_ref(v___y_2838_);
lean_dec_ref(v_as_2834_);
return v_res_2845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3(lean_object* v_00_u03b1_2846_, lean_object* v_f_2847_, lean_object* v_x_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_){
_start:
{
lean_object* v___x_2855_; 
v___x_2855_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg(v_f_2847_, v_x_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_);
return v___x_2855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___boxed(lean_object* v_00_u03b1_2856_, lean_object* v_f_2857_, lean_object* v_x_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_){
_start:
{
lean_object* v_res_2865_; 
v_res_2865_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3(v_00_u03b1_2856_, v_f_2857_, v_x_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
lean_dec(v___y_2863_);
lean_dec_ref(v___y_2862_);
lean_dec(v___y_2861_);
lean_dec_ref(v___y_2860_);
return v_res_2865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3(lean_object* v_00_u03b1_2866_, lean_object* v_f_2867_, lean_object* v_init_2868_, lean_object* v_e_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_){
_start:
{
lean_object* v___x_2875_; 
v___x_2875_ = l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg(v_f_2867_, v_init_2868_, v_e_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_);
return v___x_2875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___boxed(lean_object* v_00_u03b1_2876_, lean_object* v_f_2877_, lean_object* v_init_2878_, lean_object* v_e_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_){
_start:
{
lean_object* v_res_2885_; 
v_res_2885_ = l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3(v_00_u03b1_2876_, v_f_2877_, v_init_2878_, v_e_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2882_);
lean_dec(v___y_2881_);
lean_dec_ref(v___y_2880_);
return v_res_2885_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__3(size_t v_sz_2886_, size_t v_i_2887_, lean_object* v_bs_2888_){
_start:
{
uint8_t v___x_2889_; 
v___x_2889_ = lean_usize_dec_lt(v_i_2887_, v_sz_2886_);
if (v___x_2889_ == 0)
{
return v_bs_2888_;
}
else
{
lean_object* v_v_2890_; lean_object* v_fst_2891_; lean_object* v_snd_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2906_; 
v_v_2890_ = lean_array_uget(v_bs_2888_, v_i_2887_);
v_fst_2891_ = lean_ctor_get(v_v_2890_, 0);
v_snd_2892_ = lean_ctor_get(v_v_2890_, 1);
v_isSharedCheck_2906_ = !lean_is_exclusive(v_v_2890_);
if (v_isSharedCheck_2906_ == 0)
{
v___x_2894_ = v_v_2890_;
v_isShared_2895_ = v_isSharedCheck_2906_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_snd_2892_);
lean_inc(v_fst_2891_);
lean_dec(v_v_2890_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2906_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v___x_2896_; lean_object* v_bs_x27_2897_; lean_object* v___x_2898_; lean_object* v___x_2900_; 
v___x_2896_ = lean_unsigned_to_nat(0u);
v_bs_x27_2897_ = lean_array_uset(v_bs_2888_, v_i_2887_, v___x_2896_);
v___x_2898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2898_, 0, v_fst_2891_);
if (v_isShared_2895_ == 0)
{
lean_ctor_set(v___x_2894_, 0, v___x_2898_);
v___x_2900_ = v___x_2894_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v___x_2898_);
lean_ctor_set(v_reuseFailAlloc_2905_, 1, v_snd_2892_);
v___x_2900_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
size_t v___x_2901_; size_t v___x_2902_; lean_object* v___x_2903_; 
v___x_2901_ = ((size_t)1ULL);
v___x_2902_ = lean_usize_add(v_i_2887_, v___x_2901_);
v___x_2903_ = lean_array_uset(v_bs_x27_2897_, v_i_2887_, v___x_2900_);
v_i_2887_ = v___x_2902_;
v_bs_2888_ = v___x_2903_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__3___boxed(lean_object* v_sz_2907_, lean_object* v_i_2908_, lean_object* v_bs_2909_){
_start:
{
size_t v_sz_boxed_2910_; size_t v_i_boxed_2911_; lean_object* v_res_2912_; 
v_sz_boxed_2910_ = lean_unbox_usize(v_sz_2907_);
lean_dec(v_sz_2907_);
v_i_boxed_2911_ = lean_unbox_usize(v_i_2908_);
lean_dec(v_i_2908_);
v_res_2912_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__3(v_sz_boxed_2910_, v_i_boxed_2911_, v_bs_2909_);
return v_res_2912_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0___redArg(lean_object* v_xs_2913_, lean_object* v_j_2914_){
_start:
{
lean_object* v_zero_2915_; uint8_t v_isZero_2916_; 
v_zero_2915_ = lean_unsigned_to_nat(0u);
v_isZero_2916_ = lean_nat_dec_eq(v_j_2914_, v_zero_2915_);
if (v_isZero_2916_ == 1)
{
lean_dec(v_j_2914_);
return v_xs_2913_;
}
else
{
lean_object* v___x_2917_; lean_object* v_snd_2918_; lean_object* v_snd_2919_; lean_object* v_one_2920_; lean_object* v_n_2921_; lean_object* v___x_2922_; lean_object* v_snd_2923_; lean_object* v_snd_2924_; uint8_t v___x_2925_; 
v___x_2917_ = lean_array_fget_borrowed(v_xs_2913_, v_j_2914_);
v_snd_2918_ = lean_ctor_get(v___x_2917_, 1);
v_snd_2919_ = lean_ctor_get(v_snd_2918_, 1);
v_one_2920_ = lean_unsigned_to_nat(1u);
v_n_2921_ = lean_nat_sub(v_j_2914_, v_one_2920_);
v___x_2922_ = lean_array_fget_borrowed(v_xs_2913_, v_n_2921_);
v_snd_2923_ = lean_ctor_get(v___x_2922_, 1);
v_snd_2924_ = lean_ctor_get(v_snd_2923_, 1);
v___x_2925_ = lean_nat_dec_lt(v_snd_2924_, v_snd_2919_);
if (v___x_2925_ == 0)
{
lean_dec(v_n_2921_);
lean_dec(v_j_2914_);
return v_xs_2913_;
}
else
{
lean_object* v___x_2926_; 
v___x_2926_ = lean_array_fswap(v_xs_2913_, v_j_2914_, v_n_2921_);
lean_dec(v_j_2914_);
v_xs_2913_ = v___x_2926_;
v_j_2914_ = v_n_2921_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0(lean_object* v_xs_2928_, lean_object* v_i_2929_, lean_object* v_fuel_2930_){
_start:
{
lean_object* v_zero_2931_; uint8_t v_isZero_2932_; 
v_zero_2931_ = lean_unsigned_to_nat(0u);
v_isZero_2932_ = lean_nat_dec_eq(v_fuel_2930_, v_zero_2931_);
if (v_isZero_2932_ == 1)
{
lean_dec(v_fuel_2930_);
lean_dec(v_i_2929_);
return v_xs_2928_;
}
else
{
lean_object* v___x_2933_; uint8_t v___x_2934_; 
v___x_2933_ = lean_array_get_size(v_xs_2928_);
v___x_2934_ = lean_nat_dec_lt(v_i_2929_, v___x_2933_);
if (v___x_2934_ == 0)
{
lean_dec(v_fuel_2930_);
lean_dec(v_i_2929_);
return v_xs_2928_;
}
else
{
lean_object* v_one_2935_; lean_object* v_n_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; 
v_one_2935_ = lean_unsigned_to_nat(1u);
v_n_2936_ = lean_nat_sub(v_fuel_2930_, v_one_2935_);
lean_dec(v_fuel_2930_);
lean_inc(v_i_2929_);
v___x_2937_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0___redArg(v_xs_2928_, v_i_2929_);
v___x_2938_ = lean_nat_add(v_i_2929_, v_one_2935_);
lean_dec(v_i_2929_);
v_xs_2928_ = v___x_2937_;
v_i_2929_ = v___x_2938_;
v_fuel_2930_ = v_n_2936_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__2(size_t v_sz_2940_, size_t v_i_2941_, lean_object* v_bs_2942_){
_start:
{
uint8_t v___x_2943_; 
v___x_2943_ = lean_usize_dec_lt(v_i_2941_, v_sz_2940_);
if (v___x_2943_ == 0)
{
return v_bs_2942_;
}
else
{
lean_object* v_v_2944_; lean_object* v_fst_2945_; lean_object* v_snd_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_2960_; 
v_v_2944_ = lean_array_uget(v_bs_2942_, v_i_2941_);
v_fst_2945_ = lean_ctor_get(v_v_2944_, 0);
v_snd_2946_ = lean_ctor_get(v_v_2944_, 1);
v_isSharedCheck_2960_ = !lean_is_exclusive(v_v_2944_);
if (v_isSharedCheck_2960_ == 0)
{
v___x_2948_ = v_v_2944_;
v_isShared_2949_ = v_isSharedCheck_2960_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_snd_2946_);
lean_inc(v_fst_2945_);
lean_dec(v_v_2944_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_2960_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
lean_object* v___x_2950_; lean_object* v_bs_x27_2951_; lean_object* v___x_2952_; lean_object* v___x_2954_; 
v___x_2950_ = lean_unsigned_to_nat(0u);
v_bs_x27_2951_ = lean_array_uset(v_bs_2942_, v_i_2941_, v___x_2950_);
v___x_2952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2952_, 0, v_fst_2945_);
if (v_isShared_2949_ == 0)
{
lean_ctor_set(v___x_2948_, 0, v___x_2952_);
v___x_2954_ = v___x_2948_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v___x_2952_);
lean_ctor_set(v_reuseFailAlloc_2959_, 1, v_snd_2946_);
v___x_2954_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
size_t v___x_2955_; size_t v___x_2956_; lean_object* v___x_2957_; 
v___x_2955_ = ((size_t)1ULL);
v___x_2956_ = lean_usize_add(v_i_2941_, v___x_2955_);
v___x_2957_ = lean_array_uset(v_bs_x27_2951_, v_i_2941_, v___x_2954_);
v_i_2941_ = v___x_2956_;
v_bs_2942_ = v___x_2957_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__2___boxed(lean_object* v_sz_2961_, lean_object* v_i_2962_, lean_object* v_bs_2963_){
_start:
{
size_t v_sz_boxed_2964_; size_t v_i_boxed_2965_; lean_object* v_res_2966_; 
v_sz_boxed_2964_ = lean_unbox_usize(v_sz_2961_);
lean_dec(v_sz_2961_);
v_i_boxed_2965_ = lean_unbox_usize(v_i_2962_);
lean_dec(v_i_2962_);
v_res_2966_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__2(v_sz_boxed_2964_, v_i_boxed_2965_, v_bs_2963_);
return v_res_2966_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg(lean_object* v_forbidden_2967_, lean_object* v_as_2968_, size_t v_sz_2969_, size_t v_i_2970_, lean_object* v_b_2971_){
_start:
{
lean_object* v_a_2974_; uint8_t v___x_2978_; 
v___x_2978_ = lean_usize_dec_lt(v_i_2970_, v_sz_2969_);
if (v___x_2978_ == 0)
{
lean_object* v___x_2979_; 
v___x_2979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2979_, 0, v_b_2971_);
return v___x_2979_;
}
else
{
lean_object* v_a_2980_; lean_object* v_snd_2981_; lean_object* v_snd_2982_; lean_object* v_fst_2983_; lean_object* v_fst_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_3034_; 
v_a_2980_ = lean_array_uget(v_as_2968_, v_i_2970_);
v_snd_2981_ = lean_ctor_get(v_a_2980_, 1);
lean_inc(v_snd_2981_);
v_snd_2982_ = lean_ctor_get(v_b_2971_, 1);
lean_inc(v_snd_2982_);
v_fst_2983_ = lean_ctor_get(v_a_2980_, 0);
v_fst_2984_ = lean_ctor_get(v_snd_2981_, 0);
v_isSharedCheck_3034_ = !lean_is_exclusive(v_snd_2981_);
if (v_isSharedCheck_3034_ == 0)
{
lean_object* v_unused_3035_; 
v_unused_3035_ = lean_ctor_get(v_snd_2981_, 1);
lean_dec(v_unused_3035_);
v___x_2986_ = v_snd_2981_;
v_isShared_2987_ = v_isSharedCheck_3034_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_fst_2984_);
lean_dec(v_snd_2981_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_3034_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
lean_object* v_fst_2988_; lean_object* v___x_2990_; uint8_t v_isShared_2991_; uint8_t v_isSharedCheck_3032_; 
v_fst_2988_ = lean_ctor_get(v_b_2971_, 0);
v_isSharedCheck_3032_ = !lean_is_exclusive(v_b_2971_);
if (v_isSharedCheck_3032_ == 0)
{
lean_object* v_unused_3033_; 
v_unused_3033_ = lean_ctor_get(v_b_2971_, 1);
lean_dec(v_unused_3033_);
v___x_2990_ = v_b_2971_;
v_isShared_2991_ = v_isSharedCheck_3032_;
goto v_resetjp_2989_;
}
else
{
lean_inc(v_fst_2988_);
lean_dec(v_b_2971_);
v___x_2990_ = lean_box(0);
v_isShared_2991_ = v_isSharedCheck_3032_;
goto v_resetjp_2989_;
}
v_resetjp_2989_:
{
lean_object* v_fst_2992_; lean_object* v_snd_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3031_; 
v_fst_2992_ = lean_ctor_get(v_snd_2982_, 0);
v_snd_2993_ = lean_ctor_get(v_snd_2982_, 1);
v_isSharedCheck_3031_ = !lean_is_exclusive(v_snd_2982_);
if (v_isSharedCheck_3031_ == 0)
{
v___x_2995_ = v_snd_2982_;
v_isShared_2996_ = v_isSharedCheck_3031_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_snd_2993_);
lean_inc(v_fst_2992_);
lean_dec(v_snd_2982_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3031_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
uint8_t v___x_3009_; 
v___x_3009_ = l_Lean_NameSet_contains(v_forbidden_2967_, v_fst_2983_);
if (v___x_3009_ == 0)
{
uint8_t v___x_3010_; 
lean_inc(v_fst_2983_);
v___x_3010_ = lean_unbox(v_fst_2984_);
lean_dec(v_fst_2984_);
if (v___x_3010_ == 0)
{
uint8_t v___x_3011_; 
lean_del_object(v___x_2995_);
lean_del_object(v___x_2990_);
v___x_3011_ = l_Lean_NameSet_contains(v_fst_2988_, v_fst_2983_);
if (v___x_3011_ == 0)
{
if (v___x_2978_ == 0)
{
lean_dec(v_fst_2983_);
lean_dec(v_a_2980_);
goto v___jp_3004_;
}
else
{
lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; 
lean_del_object(v___x_2986_);
v___x_3012_ = lean_array_push(v_snd_2993_, v_a_2980_);
v___x_3013_ = l_Lean_NameSet_insert(v_fst_2988_, v_fst_2983_);
v___x_3014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3014_, 0, v_fst_2992_);
lean_ctor_set(v___x_3014_, 1, v___x_3012_);
v___x_3015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3015_, 0, v___x_3013_);
lean_ctor_set(v___x_3015_, 1, v___x_3014_);
v_a_2974_ = v___x_3015_;
goto v___jp_2973_;
}
}
else
{
lean_dec(v_fst_2983_);
lean_dec(v_a_2980_);
goto v___jp_3004_;
}
}
else
{
uint8_t v___x_3016_; 
lean_del_object(v___x_2986_);
v___x_3016_ = l_Lean_NameSet_contains(v_fst_2992_, v_fst_2983_);
if (v___x_3016_ == 0)
{
if (v___x_2978_ == 0)
{
lean_dec(v_fst_2983_);
lean_dec(v_a_2980_);
goto v___jp_2997_;
}
else
{
lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; 
lean_del_object(v___x_2995_);
lean_del_object(v___x_2990_);
v___x_3017_ = lean_array_push(v_snd_2993_, v_a_2980_);
v___x_3018_ = l_Lean_NameSet_insert(v_fst_2992_, v_fst_2983_);
v___x_3019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3019_, 0, v___x_3018_);
lean_ctor_set(v___x_3019_, 1, v___x_3017_);
v___x_3020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3020_, 0, v_fst_2988_);
lean_ctor_set(v___x_3020_, 1, v___x_3019_);
v_a_2974_ = v___x_3020_;
goto v___jp_2973_;
}
}
else
{
lean_dec(v_fst_2983_);
lean_dec(v_a_2980_);
goto v___jp_2997_;
}
}
}
else
{
lean_object* v___x_3022_; uint8_t v_isShared_3023_; uint8_t v_isSharedCheck_3028_; 
lean_del_object(v___x_2995_);
lean_del_object(v___x_2990_);
lean_del_object(v___x_2986_);
lean_dec(v_fst_2984_);
v_isSharedCheck_3028_ = !lean_is_exclusive(v_a_2980_);
if (v_isSharedCheck_3028_ == 0)
{
lean_object* v_unused_3029_; lean_object* v_unused_3030_; 
v_unused_3029_ = lean_ctor_get(v_a_2980_, 1);
lean_dec(v_unused_3029_);
v_unused_3030_ = lean_ctor_get(v_a_2980_, 0);
lean_dec(v_unused_3030_);
v___x_3022_ = v_a_2980_;
v_isShared_3023_ = v_isSharedCheck_3028_;
goto v_resetjp_3021_;
}
else
{
lean_dec(v_a_2980_);
v___x_3022_ = lean_box(0);
v_isShared_3023_ = v_isSharedCheck_3028_;
goto v_resetjp_3021_;
}
v_resetjp_3021_:
{
lean_object* v___x_3025_; 
if (v_isShared_3023_ == 0)
{
lean_ctor_set(v___x_3022_, 1, v_snd_2993_);
lean_ctor_set(v___x_3022_, 0, v_fst_2992_);
v___x_3025_ = v___x_3022_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v_fst_2992_);
lean_ctor_set(v_reuseFailAlloc_3027_, 1, v_snd_2993_);
v___x_3025_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
lean_object* v___x_3026_; 
v___x_3026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3026_, 0, v_fst_2988_);
lean_ctor_set(v___x_3026_, 1, v___x_3025_);
v_a_2974_ = v___x_3026_;
goto v___jp_2973_;
}
}
}
v___jp_2997_:
{
lean_object* v___x_2999_; 
if (v_isShared_2996_ == 0)
{
v___x_2999_ = v___x_2995_;
goto v_reusejp_2998_;
}
else
{
lean_object* v_reuseFailAlloc_3003_; 
v_reuseFailAlloc_3003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3003_, 0, v_fst_2992_);
lean_ctor_set(v_reuseFailAlloc_3003_, 1, v_snd_2993_);
v___x_2999_ = v_reuseFailAlloc_3003_;
goto v_reusejp_2998_;
}
v_reusejp_2998_:
{
lean_object* v___x_3001_; 
if (v_isShared_2991_ == 0)
{
lean_ctor_set(v___x_2990_, 1, v___x_2999_);
v___x_3001_ = v___x_2990_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v_fst_2988_);
lean_ctor_set(v_reuseFailAlloc_3002_, 1, v___x_2999_);
v___x_3001_ = v_reuseFailAlloc_3002_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
v_a_2974_ = v___x_3001_;
goto v___jp_2973_;
}
}
}
v___jp_3004_:
{
lean_object* v___x_3006_; 
if (v_isShared_2987_ == 0)
{
lean_ctor_set(v___x_2986_, 1, v_snd_2993_);
lean_ctor_set(v___x_2986_, 0, v_fst_2992_);
v___x_3006_ = v___x_2986_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v_fst_2992_);
lean_ctor_set(v_reuseFailAlloc_3008_, 1, v_snd_2993_);
v___x_3006_ = v_reuseFailAlloc_3008_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
lean_object* v___x_3007_; 
v___x_3007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3007_, 0, v_fst_2988_);
lean_ctor_set(v___x_3007_, 1, v___x_3006_);
v_a_2974_ = v___x_3007_;
goto v___jp_2973_;
}
}
}
}
}
}
v___jp_2973_:
{
size_t v___x_2975_; size_t v___x_2976_; 
v___x_2975_ = ((size_t)1ULL);
v___x_2976_ = lean_usize_add(v_i_2970_, v___x_2975_);
v_i_2970_ = v___x_2976_;
v_b_2971_ = v_a_2974_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg___boxed(lean_object* v_forbidden_3036_, lean_object* v_as_3037_, lean_object* v_sz_3038_, lean_object* v_i_3039_, lean_object* v_b_3040_, lean_object* v___y_3041_){
_start:
{
size_t v_sz_boxed_3042_; size_t v_i_boxed_3043_; lean_object* v_res_3044_; 
v_sz_boxed_3042_ = lean_unbox_usize(v_sz_3038_);
lean_dec(v_sz_3038_);
v_i_boxed_3043_ = lean_unbox_usize(v_i_3039_);
lean_dec(v_i_3039_);
v_res_3044_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg(v_forbidden_3036_, v_as_3037_, v_sz_boxed_3042_, v_i_boxed_3043_, v_b_3040_);
lean_dec_ref(v_as_3037_);
lean_dec(v_forbidden_3036_);
return v_res_3044_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__2(void){
_start:
{
lean_object* v___x_3048_; lean_object* v___x_3049_; 
v___x_3048_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__1));
v___x_3049_ = l_Lean_MessageData_ofFormat(v___x_3048_);
return v___x_3049_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__3(void){
_start:
{
lean_object* v___x_3050_; lean_object* v___x_3051_; 
v___x_3050_ = lean_box(1);
v___x_3051_ = l_Lean_MessageData_ofFormat(v___x_3050_);
return v___x_3051_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4(lean_object* v_a_3054_, lean_object* v_a_3055_){
_start:
{
if (lean_obj_tag(v_a_3054_) == 0)
{
lean_object* v___x_3056_; 
v___x_3056_ = l_List_reverse___redArg(v_a_3055_);
return v___x_3056_;
}
else
{
lean_object* v_head_3057_; lean_object* v_snd_3058_; lean_object* v_tail_3059_; lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3104_; 
v_head_3057_ = lean_ctor_get(v_a_3054_, 0);
lean_inc(v_head_3057_);
v_snd_3058_ = lean_ctor_get(v_head_3057_, 1);
lean_inc(v_snd_3058_);
v_tail_3059_ = lean_ctor_get(v_a_3054_, 1);
v_isSharedCheck_3104_ = !lean_is_exclusive(v_a_3054_);
if (v_isSharedCheck_3104_ == 0)
{
lean_object* v_unused_3105_; 
v_unused_3105_ = lean_ctor_get(v_a_3054_, 0);
lean_dec(v_unused_3105_);
v___x_3061_ = v_a_3054_;
v_isShared_3062_ = v_isSharedCheck_3104_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_tail_3059_);
lean_dec(v_a_3054_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3104_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
lean_object* v_fst_3063_; lean_object* v___x_3065_; uint8_t v_isShared_3066_; uint8_t v_isSharedCheck_3102_; 
v_fst_3063_ = lean_ctor_get(v_head_3057_, 0);
v_isSharedCheck_3102_ = !lean_is_exclusive(v_head_3057_);
if (v_isSharedCheck_3102_ == 0)
{
lean_object* v_unused_3103_; 
v_unused_3103_ = lean_ctor_get(v_head_3057_, 1);
lean_dec(v_unused_3103_);
v___x_3065_ = v_head_3057_;
v_isShared_3066_ = v_isSharedCheck_3102_;
goto v_resetjp_3064_;
}
else
{
lean_inc(v_fst_3063_);
lean_dec(v_head_3057_);
v___x_3065_ = lean_box(0);
v_isShared_3066_ = v_isSharedCheck_3102_;
goto v_resetjp_3064_;
}
v_resetjp_3064_:
{
lean_object* v_fst_3067_; lean_object* v_snd_3068_; lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3101_; 
v_fst_3067_ = lean_ctor_get(v_snd_3058_, 0);
v_snd_3068_ = lean_ctor_get(v_snd_3058_, 1);
v_isSharedCheck_3101_ = !lean_is_exclusive(v_snd_3058_);
if (v_isSharedCheck_3101_ == 0)
{
v___x_3070_ = v_snd_3058_;
v_isShared_3071_ = v_isSharedCheck_3101_;
goto v_resetjp_3069_;
}
else
{
lean_inc(v_snd_3068_);
lean_inc(v_fst_3067_);
lean_dec(v_snd_3058_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3101_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3075_; 
v___x_3072_ = l_Lean_MessageData_ofName(v_fst_3063_);
v___x_3073_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__2, &l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__2_once, _init_l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__2);
if (v_isShared_3071_ == 0)
{
lean_ctor_set_tag(v___x_3070_, 7);
lean_ctor_set(v___x_3070_, 1, v___x_3073_);
lean_ctor_set(v___x_3070_, 0, v___x_3072_);
v___x_3075_ = v___x_3070_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v___x_3072_);
lean_ctor_set(v_reuseFailAlloc_3100_, 1, v___x_3073_);
v___x_3075_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
lean_object* v___x_3076_; lean_object* v___x_3078_; 
v___x_3076_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__3, &l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__3_once, _init_l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__3);
if (v_isShared_3066_ == 0)
{
lean_ctor_set_tag(v___x_3065_, 7);
lean_ctor_set(v___x_3065_, 1, v___x_3076_);
lean_ctor_set(v___x_3065_, 0, v___x_3075_);
v___x_3078_ = v___x_3065_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v___x_3075_);
lean_ctor_set(v_reuseFailAlloc_3099_, 1, v___x_3076_);
v___x_3078_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3077_;
}
v_reusejp_3077_:
{
lean_object* v___y_3080_; uint8_t v___x_3096_; 
v___x_3096_ = lean_unbox(v_fst_3067_);
lean_dec(v_fst_3067_);
if (v___x_3096_ == 0)
{
lean_object* v___x_3097_; 
v___x_3097_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__4));
v___y_3080_ = v___x_3097_;
goto v___jp_3079_;
}
else
{
lean_object* v___x_3098_; 
v___x_3098_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__5));
v___y_3080_ = v___x_3098_;
goto v___jp_3079_;
}
v___jp_3079_:
{
lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3093_; 
lean_inc_ref(v___y_3080_);
v___x_3081_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3081_, 0, v___y_3080_);
v___x_3082_ = l_Lean_MessageData_ofFormat(v___x_3081_);
v___x_3083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3083_, 0, v___x_3082_);
lean_ctor_set(v___x_3083_, 1, v___x_3073_);
v___x_3084_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3084_, 0, v___x_3083_);
lean_ctor_set(v___x_3084_, 1, v___x_3076_);
v___x_3085_ = l_Nat_reprFast(v_snd_3068_);
v___x_3086_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3086_, 0, v___x_3085_);
v___x_3087_ = l_Lean_MessageData_ofFormat(v___x_3086_);
v___x_3088_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3088_, 0, v___x_3084_);
lean_ctor_set(v___x_3088_, 1, v___x_3087_);
v___x_3089_ = l_Lean_MessageData_paren(v___x_3088_);
v___x_3090_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3090_, 0, v___x_3078_);
lean_ctor_set(v___x_3090_, 1, v___x_3089_);
v___x_3091_ = l_Lean_MessageData_paren(v___x_3090_);
if (v_isShared_3062_ == 0)
{
lean_ctor_set(v___x_3061_, 1, v_a_3055_);
lean_ctor_set(v___x_3061_, 0, v___x_3091_);
v___x_3093_ = v___x_3061_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v___x_3091_);
lean_ctor_set(v_reuseFailAlloc_3095_, 1, v_a_3055_);
v___x_3093_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
v_a_3054_ = v_tail_3059_;
v_a_3055_ = v___x_3093_;
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
lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; 
v___x_3108_ = ((lean_object*)(l_Lean_Meta_Rewrites_rewriteCandidates___closed__0));
v___x_3109_ = l_Lean_NameSet_empty;
v___x_3110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3110_, 0, v___x_3109_);
lean_ctor_set(v___x_3110_, 1, v___x_3108_);
return v___x_3110_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__2(void){
_start:
{
lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; 
v___x_3111_ = lean_obj_once(&l_Lean_Meta_Rewrites_rewriteCandidates___closed__1, &l_Lean_Meta_Rewrites_rewriteCandidates___closed__1_once, _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__1);
v___x_3112_ = l_Lean_NameSet_empty;
v___x_3113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3113_, 0, v___x_3112_);
lean_ctor_set(v___x_3113_, 1, v___x_3111_);
return v___x_3113_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__3(void){
_start:
{
lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; 
v___x_3114_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_));
v___x_3115_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__4));
v___x_3116_ = l_Lean_Name_append(v___x_3115_, v___x_3114_);
return v___x_3116_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__5(void){
_start:
{
lean_object* v___x_3118_; lean_object* v___x_3119_; 
v___x_3118_ = ((lean_object*)(l_Lean_Meta_Rewrites_rewriteCandidates___closed__4));
v___x_3119_ = l_Lean_stringToMessageData(v___x_3118_);
return v___x_3119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rewriteCandidates(lean_object* v_hyps_3120_, lean_object* v_moduleRef_3121_, lean_object* v_target_3122_, lean_object* v_forbidden_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_, lean_object* v_a_3127_){
_start:
{
lean_object* v___x_3129_; lean_object* v___x_3130_; 
v___x_3129_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_rwFindDecls___boxed), 7, 1);
lean_closure_set(v___x_3129_, 0, v_moduleRef_3121_);
v___x_3130_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v___x_3129_, v_target_3122_, v_a_3124_, v_a_3125_, v_a_3126_, v_a_3127_);
if (lean_obj_tag(v___x_3130_) == 0)
{
lean_object* v_a_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; size_t v_sz_3136_; size_t v___x_3137_; lean_object* v___x_3138_; 
v_a_3131_ = lean_ctor_get(v___x_3130_, 0);
lean_inc(v_a_3131_);
lean_dec_ref_known(v___x_3130_, 1);
v___x_3132_ = lean_unsigned_to_nat(0u);
v___x_3133_ = lean_array_get_size(v_a_3131_);
v___x_3134_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0(v_a_3131_, v___x_3132_, v___x_3133_);
v___x_3135_ = lean_obj_once(&l_Lean_Meta_Rewrites_rewriteCandidates___closed__2, &l_Lean_Meta_Rewrites_rewriteCandidates___closed__2_once, _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__2);
v_sz_3136_ = lean_array_size(v___x_3134_);
v___x_3137_ = ((size_t)0ULL);
v___x_3138_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg(v_forbidden_3123_, v___x_3134_, v_sz_3136_, v___x_3137_, v___x_3135_);
lean_dec_ref(v___x_3134_);
if (lean_obj_tag(v___x_3138_) == 0)
{
lean_object* v_a_3139_; lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3182_; 
v_a_3139_ = lean_ctor_get(v___x_3138_, 0);
v_isSharedCheck_3182_ = !lean_is_exclusive(v___x_3138_);
if (v_isSharedCheck_3182_ == 0)
{
v___x_3141_ = v___x_3138_;
v_isShared_3142_ = v_isSharedCheck_3182_;
goto v_resetjp_3140_;
}
else
{
lean_inc(v_a_3139_);
lean_dec(v___x_3138_);
v___x_3141_ = lean_box(0);
v_isShared_3142_ = v_isSharedCheck_3182_;
goto v_resetjp_3140_;
}
v_resetjp_3140_:
{
lean_object* v_snd_3143_; lean_object* v_snd_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3180_; 
v_snd_3143_ = lean_ctor_get(v_a_3139_, 1);
lean_inc(v_snd_3143_);
lean_dec(v_a_3139_);
v_snd_3144_ = lean_ctor_get(v_snd_3143_, 1);
v_isSharedCheck_3180_ = !lean_is_exclusive(v_snd_3143_);
if (v_isSharedCheck_3180_ == 0)
{
lean_object* v_unused_3181_; 
v_unused_3181_ = lean_ctor_get(v_snd_3143_, 0);
lean_dec(v_unused_3181_);
v___x_3146_ = v_snd_3143_;
v_isShared_3147_ = v_isSharedCheck_3180_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_snd_3144_);
lean_dec(v_snd_3143_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3180_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v_options_3157_; uint8_t v_hasTrace_3158_; 
v_options_3157_ = lean_ctor_get(v_a_3126_, 2);
v_hasTrace_3158_ = lean_ctor_get_uint8(v_options_3157_, sizeof(void*)*1);
if (v_hasTrace_3158_ == 0)
{
lean_del_object(v___x_3146_);
goto v___jp_3148_;
}
else
{
lean_object* v_inheritedTraceOptions_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; uint8_t v___x_3162_; 
v_inheritedTraceOptions_3159_ = lean_ctor_get(v_a_3126_, 13);
v___x_3160_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_));
v___x_3161_ = lean_obj_once(&l_Lean_Meta_Rewrites_rewriteCandidates___closed__3, &l_Lean_Meta_Rewrites_rewriteCandidates___closed__3_once, _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__3);
v___x_3162_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3159_, v_options_3157_, v___x_3161_);
if (v___x_3162_ == 0)
{
lean_del_object(v___x_3146_);
goto v___jp_3148_;
}
else
{
lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3169_; 
v___x_3163_ = lean_obj_once(&l_Lean_Meta_Rewrites_rewriteCandidates___closed__5, &l_Lean_Meta_Rewrites_rewriteCandidates___closed__5_once, _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__5);
lean_inc(v_snd_3144_);
v___x_3164_ = lean_array_to_list(v_snd_3144_);
v___x_3165_ = lean_box(0);
v___x_3166_ = l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4(v___x_3164_, v___x_3165_);
v___x_3167_ = l_Lean_MessageData_ofList(v___x_3166_);
if (v_isShared_3147_ == 0)
{
lean_ctor_set_tag(v___x_3146_, 7);
lean_ctor_set(v___x_3146_, 1, v___x_3167_);
lean_ctor_set(v___x_3146_, 0, v___x_3163_);
v___x_3169_ = v___x_3146_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v___x_3163_);
lean_ctor_set(v_reuseFailAlloc_3179_, 1, v___x_3167_);
v___x_3169_ = v_reuseFailAlloc_3179_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
lean_object* v___x_3170_; 
v___x_3170_ = l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2(v___x_3160_, v___x_3169_, v_a_3124_, v_a_3125_, v_a_3126_, v_a_3127_);
if (lean_obj_tag(v___x_3170_) == 0)
{
lean_dec_ref_known(v___x_3170_, 1);
goto v___jp_3148_;
}
else
{
lean_object* v_a_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3178_; 
lean_dec(v_snd_3144_);
lean_del_object(v___x_3141_);
lean_dec_ref(v_hyps_3120_);
v_a_3171_ = lean_ctor_get(v___x_3170_, 0);
v_isSharedCheck_3178_ = !lean_is_exclusive(v___x_3170_);
if (v_isSharedCheck_3178_ == 0)
{
v___x_3173_ = v___x_3170_;
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
else
{
lean_inc(v_a_3171_);
lean_dec(v___x_3170_);
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
}
}
v___jp_3148_:
{
size_t v_sz_3149_; lean_object* v___x_3150_; size_t v_sz_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3155_; 
v_sz_3149_ = lean_array_size(v_hyps_3120_);
v___x_3150_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__2(v_sz_3149_, v___x_3137_, v_hyps_3120_);
v_sz_3151_ = lean_array_size(v_snd_3144_);
v___x_3152_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__3(v_sz_3151_, v___x_3137_, v_snd_3144_);
v___x_3153_ = l_Array_append___redArg(v___x_3150_, v___x_3152_);
lean_dec_ref(v___x_3152_);
if (v_isShared_3142_ == 0)
{
lean_ctor_set(v___x_3141_, 0, v___x_3153_);
v___x_3155_ = v___x_3141_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v___x_3153_);
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
else
{
lean_object* v_a_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3190_; 
lean_dec_ref(v_hyps_3120_);
v_a_3183_ = lean_ctor_get(v___x_3138_, 0);
v_isSharedCheck_3190_ = !lean_is_exclusive(v___x_3138_);
if (v_isSharedCheck_3190_ == 0)
{
v___x_3185_ = v___x_3138_;
v_isShared_3186_ = v_isSharedCheck_3190_;
goto v_resetjp_3184_;
}
else
{
lean_inc(v_a_3183_);
lean_dec(v___x_3138_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3190_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
lean_object* v___x_3188_; 
if (v_isShared_3186_ == 0)
{
v___x_3188_ = v___x_3185_;
goto v_reusejp_3187_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v_a_3183_);
v___x_3188_ = v_reuseFailAlloc_3189_;
goto v_reusejp_3187_;
}
v_reusejp_3187_:
{
return v___x_3188_;
}
}
}
}
else
{
lean_object* v_a_3191_; lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3198_; 
lean_dec_ref(v_hyps_3120_);
v_a_3191_ = lean_ctor_get(v___x_3130_, 0);
v_isSharedCheck_3198_ = !lean_is_exclusive(v___x_3130_);
if (v_isSharedCheck_3198_ == 0)
{
v___x_3193_ = v___x_3130_;
v_isShared_3194_ = v_isSharedCheck_3198_;
goto v_resetjp_3192_;
}
else
{
lean_inc(v_a_3191_);
lean_dec(v___x_3130_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3198_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
lean_object* v___x_3196_; 
if (v_isShared_3194_ == 0)
{
v___x_3196_ = v___x_3193_;
goto v_reusejp_3195_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v_a_3191_);
v___x_3196_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3195_;
}
v_reusejp_3195_:
{
return v___x_3196_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rewriteCandidates___boxed(lean_object* v_hyps_3199_, lean_object* v_moduleRef_3200_, lean_object* v_target_3201_, lean_object* v_forbidden_3202_, lean_object* v_a_3203_, lean_object* v_a_3204_, lean_object* v_a_3205_, lean_object* v_a_3206_, lean_object* v_a_3207_){
_start:
{
lean_object* v_res_3208_; 
v_res_3208_ = l_Lean_Meta_Rewrites_rewriteCandidates(v_hyps_3199_, v_moduleRef_3200_, v_target_3201_, v_forbidden_3202_, v_a_3203_, v_a_3204_, v_a_3205_, v_a_3206_);
lean_dec(v_a_3206_);
lean_dec_ref(v_a_3205_);
lean_dec(v_a_3204_);
lean_dec_ref(v_a_3203_);
lean_dec(v_forbidden_3202_);
return v_res_3208_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1(lean_object* v_forbidden_3209_, lean_object* v_as_3210_, size_t v_sz_3211_, size_t v_i_3212_, lean_object* v_b_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_){
_start:
{
lean_object* v___x_3219_; 
v___x_3219_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg(v_forbidden_3209_, v_as_3210_, v_sz_3211_, v_i_3212_, v_b_3213_);
return v___x_3219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___boxed(lean_object* v_forbidden_3220_, lean_object* v_as_3221_, lean_object* v_sz_3222_, lean_object* v_i_3223_, lean_object* v_b_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_){
_start:
{
size_t v_sz_boxed_3230_; size_t v_i_boxed_3231_; lean_object* v_res_3232_; 
v_sz_boxed_3230_ = lean_unbox_usize(v_sz_3222_);
lean_dec(v_sz_3222_);
v_i_boxed_3231_ = lean_unbox_usize(v_i_3223_);
lean_dec(v_i_3223_);
v_res_3232_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1(v_forbidden_3220_, v_as_3221_, v_sz_boxed_3230_, v_i_boxed_3231_, v_b_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_);
lean_dec(v___y_3228_);
lean_dec_ref(v___y_3227_);
lean_dec(v___y_3226_);
lean_dec_ref(v___y_3225_);
lean_dec_ref(v_as_3221_);
lean_dec(v_forbidden_3220_);
return v_res_3232_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0(lean_object* v_xs_3233_, lean_object* v_j_3234_, lean_object* v_h_3235_){
_start:
{
lean_object* v___x_3236_; 
v___x_3236_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0___redArg(v_xs_3233_, v_j_3234_);
return v___x_3236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_newGoal(lean_object* v_r_3237_){
_start:
{
uint8_t v_rfl_x3f_3238_; 
v_rfl_x3f_3238_ = lean_ctor_get_uint8(v_r_3237_, sizeof(void*)*4 + 1);
if (v_rfl_x3f_3238_ == 0)
{
lean_object* v_result_3239_; lean_object* v_eNew_3240_; lean_object* v___x_3241_; 
v_result_3239_ = lean_ctor_get(v_r_3237_, 2);
v_eNew_3240_ = lean_ctor_get(v_result_3239_, 0);
lean_inc_ref(v_eNew_3240_);
v___x_3241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3241_, 0, v_eNew_3240_);
return v___x_3241_;
}
else
{
lean_object* v___x_3242_; 
v___x_3242_ = lean_box(0);
return v___x_3242_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_newGoal___boxed(lean_object* v_r_3243_){
_start:
{
lean_object* v_res_3244_; 
v_res_3244_ = l_Lean_Meta_Rewrites_RewriteResult_newGoal(v_r_3243_);
lean_dec_ref(v_r_3243_);
return v_res_3244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0(lean_object* v_x_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_){
_start:
{
lean_object* v___x_3255_; 
lean_inc(v___y_3249_);
lean_inc_ref(v___y_3248_);
lean_inc(v___y_3247_);
lean_inc_ref(v___y_3246_);
v___x_3255_ = lean_apply_9(v_x_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_, lean_box(0));
return v___x_3255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0___boxed(lean_object* v_x_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_){
_start:
{
lean_object* v_res_3266_; 
v_res_3266_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0(v_x_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_);
lean_dec(v___y_3260_);
lean_dec_ref(v___y_3259_);
lean_dec(v___y_3258_);
lean_dec_ref(v___y_3257_);
return v_res_3266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg(lean_object* v_mctx_3267_, lean_object* v_x_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_){
_start:
{
lean_object* v___f_3278_; lean_object* v___x_3279_; 
lean_inc(v___y_3272_);
lean_inc_ref(v___y_3271_);
lean_inc(v___y_3270_);
lean_inc_ref(v___y_3269_);
v___f_3278_ = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3278_, 0, v_x_3268_);
lean_closure_set(v___f_3278_, 1, v___y_3269_);
lean_closure_set(v___f_3278_, 2, v___y_3270_);
lean_closure_set(v___f_3278_, 3, v___y_3271_);
lean_closure_set(v___f_3278_, 4, v___y_3272_);
v___x_3279_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp(lean_box(0), v_mctx_3267_, v___f_3278_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_);
if (lean_obj_tag(v___x_3279_) == 0)
{
return v___x_3279_;
}
else
{
lean_object* v_a_3280_; lean_object* v___x_3282_; uint8_t v_isShared_3283_; uint8_t v_isSharedCheck_3287_; 
v_a_3280_ = lean_ctor_get(v___x_3279_, 0);
v_isSharedCheck_3287_ = !lean_is_exclusive(v___x_3279_);
if (v_isSharedCheck_3287_ == 0)
{
v___x_3282_ = v___x_3279_;
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
else
{
lean_inc(v_a_3280_);
lean_dec(v___x_3279_);
v___x_3282_ = lean_box(0);
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
v_resetjp_3281_:
{
lean_object* v___x_3285_; 
if (v_isShared_3283_ == 0)
{
v___x_3285_ = v___x_3282_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v_a_3280_);
v___x_3285_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3284_;
}
v_reusejp_3284_:
{
return v___x_3285_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___boxed(lean_object* v_mctx_3288_, lean_object* v_x_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_){
_start:
{
lean_object* v_res_3299_; 
v_res_3299_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg(v_mctx_3288_, v_x_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
lean_dec(v___y_3297_);
lean_dec_ref(v___y_3296_);
lean_dec(v___y_3295_);
lean_dec_ref(v___y_3294_);
lean_dec(v___y_3293_);
lean_dec_ref(v___y_3292_);
lean_dec(v___y_3291_);
lean_dec_ref(v___y_3290_);
return v_res_3299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0(lean_object* v_00_u03b1_3300_, lean_object* v_mctx_3301_, lean_object* v_x_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_){
_start:
{
lean_object* v___x_3312_; 
v___x_3312_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg(v_mctx_3301_, v_x_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_);
return v___x_3312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___boxed(lean_object* v_00_u03b1_3313_, lean_object* v_mctx_3314_, lean_object* v_x_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_){
_start:
{
lean_object* v_res_3325_; 
v_res_3325_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0(v_00_u03b1_3313_, v_mctx_3314_, v_x_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_);
lean_dec(v___y_3323_);
lean_dec_ref(v___y_3322_);
lean_dec(v___y_3321_);
lean_dec_ref(v___y_3320_);
lean_dec(v___y_3319_);
lean_dec_ref(v___y_3318_);
lean_dec(v___y_3317_);
lean_dec_ref(v___y_3316_);
return v_res_3325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0(lean_object* v_expr_3326_, uint8_t v_symm_3327_, lean_object* v_r_3328_, lean_object* v_ref_3329_, lean_object* v_checkState_x3f_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_){
_start:
{
lean_object* v___x_3340_; 
v___x_3340_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_3332_, v___y_3334_, v___y_3336_, v___y_3338_);
if (lean_obj_tag(v___x_3340_) == 0)
{
lean_object* v_a_3341_; lean_object* v_ref_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___y_3352_; 
v_a_3341_ = lean_ctor_get(v___x_3340_, 0);
lean_inc(v_a_3341_);
lean_dec_ref_known(v___x_3340_, 1);
v_ref_3342_ = lean_ctor_get(v___y_3337_, 5);
v___x_3343_ = lean_box(v_symm_3327_);
v___x_3344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3344_, 0, v_expr_3326_);
lean_ctor_set(v___x_3344_, 1, v___x_3343_);
v___x_3345_ = lean_box(0);
v___x_3346_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3346_, 0, v___x_3344_);
lean_ctor_set(v___x_3346_, 1, v___x_3345_);
v___x_3347_ = l_Lean_Meta_Rewrites_RewriteResult_newGoal(v_r_3328_);
v___x_3348_ = l_Lean_Option_toLOption___redArg(v___x_3347_);
v___x_3349_ = lean_box(0);
lean_inc(v_ref_3342_);
v___x_3350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3350_, 0, v_ref_3342_);
if (lean_obj_tag(v_checkState_x3f_3330_) == 0)
{
v___y_3352_ = v_a_3341_;
goto v___jp_3351_;
}
else
{
lean_object* v_val_3355_; 
lean_dec(v_a_3341_);
v_val_3355_ = lean_ctor_get(v_checkState_x3f_3330_, 0);
lean_inc(v_val_3355_);
lean_dec_ref_known(v_checkState_x3f_3330_, 1);
v___y_3352_ = v_val_3355_;
goto v___jp_3351_;
}
v___jp_3351_:
{
lean_object* v___x_3353_; lean_object* v___x_3354_; 
v___x_3353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3353_, 0, v___y_3352_);
v___x_3354_ = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion(v_ref_3329_, v___x_3346_, v___x_3348_, v___x_3349_, v___x_3350_, v___x_3353_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_);
return v___x_3354_;
}
}
else
{
lean_object* v_a_3356_; lean_object* v___x_3358_; uint8_t v_isShared_3359_; uint8_t v_isSharedCheck_3363_; 
lean_dec(v_checkState_x3f_3330_);
lean_dec(v_ref_3329_);
lean_dec_ref(v_expr_3326_);
v_a_3356_ = lean_ctor_get(v___x_3340_, 0);
v_isSharedCheck_3363_ = !lean_is_exclusive(v___x_3340_);
if (v_isSharedCheck_3363_ == 0)
{
v___x_3358_ = v___x_3340_;
v_isShared_3359_ = v_isSharedCheck_3363_;
goto v_resetjp_3357_;
}
else
{
lean_inc(v_a_3356_);
lean_dec(v___x_3340_);
v___x_3358_ = lean_box(0);
v_isShared_3359_ = v_isSharedCheck_3363_;
goto v_resetjp_3357_;
}
v_resetjp_3357_:
{
lean_object* v___x_3361_; 
if (v_isShared_3359_ == 0)
{
v___x_3361_ = v___x_3358_;
goto v_reusejp_3360_;
}
else
{
lean_object* v_reuseFailAlloc_3362_; 
v_reuseFailAlloc_3362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3362_, 0, v_a_3356_);
v___x_3361_ = v_reuseFailAlloc_3362_;
goto v_reusejp_3360_;
}
v_reusejp_3360_:
{
return v___x_3361_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0___boxed(lean_object* v_expr_3364_, lean_object* v_symm_3365_, lean_object* v_r_3366_, lean_object* v_ref_3367_, lean_object* v_checkState_x3f_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_){
_start:
{
uint8_t v_symm_boxed_3378_; lean_object* v_res_3379_; 
v_symm_boxed_3378_ = lean_unbox(v_symm_3365_);
v_res_3379_ = l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0(v_expr_3364_, v_symm_boxed_3378_, v_r_3366_, v_ref_3367_, v_checkState_x3f_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_);
lean_dec(v___y_3376_);
lean_dec_ref(v___y_3375_);
lean_dec(v___y_3374_);
lean_dec_ref(v___y_3373_);
lean_dec(v___y_3372_);
lean_dec_ref(v___y_3371_);
lean_dec(v___y_3370_);
lean_dec_ref(v___y_3369_);
lean_dec_ref(v_r_3366_);
return v_res_3379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion(lean_object* v_ref_3380_, lean_object* v_r_3381_, lean_object* v_checkState_x3f_3382_, lean_object* v_a_3383_, lean_object* v_a_3384_, lean_object* v_a_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_){
_start:
{
lean_object* v_expr_3392_; uint8_t v_symm_3393_; lean_object* v_mctx_3394_; lean_object* v___x_3395_; lean_object* v___f_3396_; lean_object* v___x_3397_; 
v_expr_3392_ = lean_ctor_get(v_r_3381_, 0);
lean_inc_ref(v_expr_3392_);
v_symm_3393_ = lean_ctor_get_uint8(v_r_3381_, sizeof(void*)*4);
v_mctx_3394_ = lean_ctor_get(v_r_3381_, 3);
lean_inc_ref(v_mctx_3394_);
v___x_3395_ = lean_box(v_symm_3393_);
v___f_3396_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0___boxed), 14, 5);
lean_closure_set(v___f_3396_, 0, v_expr_3392_);
lean_closure_set(v___f_3396_, 1, v___x_3395_);
lean_closure_set(v___f_3396_, 2, v_r_3381_);
lean_closure_set(v___f_3396_, 3, v_ref_3380_);
lean_closure_set(v___f_3396_, 4, v_checkState_x3f_3382_);
v___x_3397_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg(v_mctx_3394_, v___f_3396_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_, v_a_3390_);
return v___x_3397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___boxed(lean_object* v_ref_3398_, lean_object* v_r_3399_, lean_object* v_checkState_x3f_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_, lean_object* v_a_3406_, lean_object* v_a_3407_, lean_object* v_a_3408_, lean_object* v_a_3409_){
_start:
{
lean_object* v_res_3410_; 
v_res_3410_ = l_Lean_Meta_Rewrites_RewriteResult_addSuggestion(v_ref_3398_, v_r_3399_, v_checkState_x3f_3400_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_);
lean_dec(v_a_3408_);
lean_dec_ref(v_a_3407_);
lean_dec(v_a_3406_);
lean_dec_ref(v_a_3405_);
lean_dec(v_a_3404_);
lean_dec_ref(v_a_3403_);
lean_dec(v_a_3402_);
lean_dec_ref(v_a_3401_);
return v_res_3410_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3___redArg(lean_object* v_a_3411_, lean_object* v_b_3412_, lean_object* v_x_3413_){
_start:
{
if (lean_obj_tag(v_x_3413_) == 0)
{
lean_dec(v_b_3412_);
lean_dec_ref(v_a_3411_);
return v_x_3413_;
}
else
{
lean_object* v_key_3414_; lean_object* v_value_3415_; lean_object* v_tail_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3428_; 
v_key_3414_ = lean_ctor_get(v_x_3413_, 0);
v_value_3415_ = lean_ctor_get(v_x_3413_, 1);
v_tail_3416_ = lean_ctor_get(v_x_3413_, 2);
v_isSharedCheck_3428_ = !lean_is_exclusive(v_x_3413_);
if (v_isSharedCheck_3428_ == 0)
{
v___x_3418_ = v_x_3413_;
v_isShared_3419_ = v_isSharedCheck_3428_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_tail_3416_);
lean_inc(v_value_3415_);
lean_inc(v_key_3414_);
lean_dec(v_x_3413_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3428_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
uint8_t v___x_3420_; 
v___x_3420_ = lean_string_dec_eq(v_key_3414_, v_a_3411_);
if (v___x_3420_ == 0)
{
lean_object* v___x_3421_; lean_object* v___x_3423_; 
v___x_3421_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3___redArg(v_a_3411_, v_b_3412_, v_tail_3416_);
if (v_isShared_3419_ == 0)
{
lean_ctor_set(v___x_3418_, 2, v___x_3421_);
v___x_3423_ = v___x_3418_;
goto v_reusejp_3422_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v_key_3414_);
lean_ctor_set(v_reuseFailAlloc_3424_, 1, v_value_3415_);
lean_ctor_set(v_reuseFailAlloc_3424_, 2, v___x_3421_);
v___x_3423_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3422_;
}
v_reusejp_3422_:
{
return v___x_3423_;
}
}
else
{
lean_object* v___x_3426_; 
lean_dec(v_value_3415_);
lean_dec(v_key_3414_);
if (v_isShared_3419_ == 0)
{
lean_ctor_set(v___x_3418_, 1, v_b_3412_);
lean_ctor_set(v___x_3418_, 0, v_a_3411_);
v___x_3426_ = v___x_3418_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3427_; 
v_reuseFailAlloc_3427_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3427_, 0, v_a_3411_);
lean_ctor_set(v_reuseFailAlloc_3427_, 1, v_b_3412_);
lean_ctor_set(v_reuseFailAlloc_3427_, 2, v_tail_3416_);
v___x_3426_ = v_reuseFailAlloc_3427_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
return v___x_3426_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_x_3429_, lean_object* v_x_3430_){
_start:
{
if (lean_obj_tag(v_x_3430_) == 0)
{
return v_x_3429_;
}
else
{
lean_object* v_key_3431_; lean_object* v_value_3432_; lean_object* v_tail_3433_; lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3456_; 
v_key_3431_ = lean_ctor_get(v_x_3430_, 0);
v_value_3432_ = lean_ctor_get(v_x_3430_, 1);
v_tail_3433_ = lean_ctor_get(v_x_3430_, 2);
v_isSharedCheck_3456_ = !lean_is_exclusive(v_x_3430_);
if (v_isSharedCheck_3456_ == 0)
{
v___x_3435_ = v_x_3430_;
v_isShared_3436_ = v_isSharedCheck_3456_;
goto v_resetjp_3434_;
}
else
{
lean_inc(v_tail_3433_);
lean_inc(v_value_3432_);
lean_inc(v_key_3431_);
lean_dec(v_x_3430_);
v___x_3435_ = lean_box(0);
v_isShared_3436_ = v_isSharedCheck_3456_;
goto v_resetjp_3434_;
}
v_resetjp_3434_:
{
lean_object* v___x_3437_; uint64_t v___x_3438_; uint64_t v___x_3439_; uint64_t v___x_3440_; uint64_t v_fold_3441_; uint64_t v___x_3442_; uint64_t v___x_3443_; uint64_t v___x_3444_; size_t v___x_3445_; size_t v___x_3446_; size_t v___x_3447_; size_t v___x_3448_; size_t v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3452_; 
v___x_3437_ = lean_array_get_size(v_x_3429_);
v___x_3438_ = lean_string_hash(v_key_3431_);
v___x_3439_ = 32ULL;
v___x_3440_ = lean_uint64_shift_right(v___x_3438_, v___x_3439_);
v_fold_3441_ = lean_uint64_xor(v___x_3438_, v___x_3440_);
v___x_3442_ = 16ULL;
v___x_3443_ = lean_uint64_shift_right(v_fold_3441_, v___x_3442_);
v___x_3444_ = lean_uint64_xor(v_fold_3441_, v___x_3443_);
v___x_3445_ = lean_uint64_to_usize(v___x_3444_);
v___x_3446_ = lean_usize_of_nat(v___x_3437_);
v___x_3447_ = ((size_t)1ULL);
v___x_3448_ = lean_usize_sub(v___x_3446_, v___x_3447_);
v___x_3449_ = lean_usize_land(v___x_3445_, v___x_3448_);
v___x_3450_ = lean_array_uget_borrowed(v_x_3429_, v___x_3449_);
lean_inc(v___x_3450_);
if (v_isShared_3436_ == 0)
{
lean_ctor_set(v___x_3435_, 2, v___x_3450_);
v___x_3452_ = v___x_3435_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v_key_3431_);
lean_ctor_set(v_reuseFailAlloc_3455_, 1, v_value_3432_);
lean_ctor_set(v_reuseFailAlloc_3455_, 2, v___x_3450_);
v___x_3452_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
lean_object* v___x_3453_; 
v___x_3453_ = lean_array_uset(v_x_3429_, v___x_3449_, v___x_3452_);
v_x_3429_ = v___x_3453_;
v_x_3430_ = v_tail_3433_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3___redArg(lean_object* v_i_3457_, lean_object* v_source_3458_, lean_object* v_target_3459_){
_start:
{
lean_object* v___x_3460_; uint8_t v___x_3461_; 
v___x_3460_ = lean_array_get_size(v_source_3458_);
v___x_3461_ = lean_nat_dec_lt(v_i_3457_, v___x_3460_);
if (v___x_3461_ == 0)
{
lean_dec_ref(v_source_3458_);
lean_dec(v_i_3457_);
return v_target_3459_;
}
else
{
lean_object* v_es_3462_; lean_object* v___x_3463_; lean_object* v_source_3464_; lean_object* v_target_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; 
v_es_3462_ = lean_array_fget(v_source_3458_, v_i_3457_);
v___x_3463_ = lean_box(0);
v_source_3464_ = lean_array_fset(v_source_3458_, v_i_3457_, v___x_3463_);
v_target_3465_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3_spec__5___redArg(v_target_3459_, v_es_3462_);
v___x_3466_ = lean_unsigned_to_nat(1u);
v___x_3467_ = lean_nat_add(v_i_3457_, v___x_3466_);
lean_dec(v_i_3457_);
v_i_3457_ = v___x_3467_;
v_source_3458_ = v_source_3464_;
v_target_3459_ = v_target_3465_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2___redArg(lean_object* v_data_3469_){
_start:
{
lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v_nbuckets_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; 
v___x_3470_ = lean_array_get_size(v_data_3469_);
v___x_3471_ = lean_unsigned_to_nat(2u);
v_nbuckets_3472_ = lean_nat_mul(v___x_3470_, v___x_3471_);
v___x_3473_ = lean_unsigned_to_nat(0u);
v___x_3474_ = lean_box(0);
v___x_3475_ = lean_mk_array(v_nbuckets_3472_, v___x_3474_);
v___x_3476_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3___redArg(v___x_3473_, v_data_3469_, v___x_3475_);
return v___x_3476_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(lean_object* v_a_3477_, lean_object* v_x_3478_){
_start:
{
if (lean_obj_tag(v_x_3478_) == 0)
{
uint8_t v___x_3479_; 
v___x_3479_ = 0;
return v___x_3479_;
}
else
{
lean_object* v_key_3480_; lean_object* v_tail_3481_; uint8_t v___x_3482_; 
v_key_3480_ = lean_ctor_get(v_x_3478_, 0);
v_tail_3481_ = lean_ctor_get(v_x_3478_, 2);
v___x_3482_ = lean_string_dec_eq(v_key_3480_, v_a_3477_);
if (v___x_3482_ == 0)
{
v_x_3478_ = v_tail_3481_;
goto _start;
}
else
{
return v___x_3482_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg___boxed(lean_object* v_a_3484_, lean_object* v_x_3485_){
_start:
{
uint8_t v_res_3486_; lean_object* v_r_3487_; 
v_res_3486_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(v_a_3484_, v_x_3485_);
lean_dec(v_x_3485_);
lean_dec_ref(v_a_3484_);
v_r_3487_ = lean_box(v_res_3486_);
return v_r_3487_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1___redArg(lean_object* v_m_3488_, lean_object* v_a_3489_, lean_object* v_b_3490_){
_start:
{
lean_object* v_size_3491_; lean_object* v_buckets_3492_; lean_object* v___x_3494_; uint8_t v_isShared_3495_; uint8_t v_isSharedCheck_3535_; 
v_size_3491_ = lean_ctor_get(v_m_3488_, 0);
v_buckets_3492_ = lean_ctor_get(v_m_3488_, 1);
v_isSharedCheck_3535_ = !lean_is_exclusive(v_m_3488_);
if (v_isSharedCheck_3535_ == 0)
{
v___x_3494_ = v_m_3488_;
v_isShared_3495_ = v_isSharedCheck_3535_;
goto v_resetjp_3493_;
}
else
{
lean_inc(v_buckets_3492_);
lean_inc(v_size_3491_);
lean_dec(v_m_3488_);
v___x_3494_ = lean_box(0);
v_isShared_3495_ = v_isSharedCheck_3535_;
goto v_resetjp_3493_;
}
v_resetjp_3493_:
{
lean_object* v___x_3496_; uint64_t v___x_3497_; uint64_t v___x_3498_; uint64_t v___x_3499_; uint64_t v_fold_3500_; uint64_t v___x_3501_; uint64_t v___x_3502_; uint64_t v___x_3503_; size_t v___x_3504_; size_t v___x_3505_; size_t v___x_3506_; size_t v___x_3507_; size_t v___x_3508_; lean_object* v_bkt_3509_; uint8_t v___x_3510_; 
v___x_3496_ = lean_array_get_size(v_buckets_3492_);
v___x_3497_ = lean_string_hash(v_a_3489_);
v___x_3498_ = 32ULL;
v___x_3499_ = lean_uint64_shift_right(v___x_3497_, v___x_3498_);
v_fold_3500_ = lean_uint64_xor(v___x_3497_, v___x_3499_);
v___x_3501_ = 16ULL;
v___x_3502_ = lean_uint64_shift_right(v_fold_3500_, v___x_3501_);
v___x_3503_ = lean_uint64_xor(v_fold_3500_, v___x_3502_);
v___x_3504_ = lean_uint64_to_usize(v___x_3503_);
v___x_3505_ = lean_usize_of_nat(v___x_3496_);
v___x_3506_ = ((size_t)1ULL);
v___x_3507_ = lean_usize_sub(v___x_3505_, v___x_3506_);
v___x_3508_ = lean_usize_land(v___x_3504_, v___x_3507_);
v_bkt_3509_ = lean_array_uget_borrowed(v_buckets_3492_, v___x_3508_);
v___x_3510_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(v_a_3489_, v_bkt_3509_);
if (v___x_3510_ == 0)
{
lean_object* v___x_3511_; lean_object* v_size_x27_3512_; lean_object* v___x_3513_; lean_object* v_buckets_x27_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; uint8_t v___x_3520_; 
v___x_3511_ = lean_unsigned_to_nat(1u);
v_size_x27_3512_ = lean_nat_add(v_size_3491_, v___x_3511_);
lean_dec(v_size_3491_);
lean_inc(v_bkt_3509_);
v___x_3513_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3513_, 0, v_a_3489_);
lean_ctor_set(v___x_3513_, 1, v_b_3490_);
lean_ctor_set(v___x_3513_, 2, v_bkt_3509_);
v_buckets_x27_3514_ = lean_array_uset(v_buckets_3492_, v___x_3508_, v___x_3513_);
v___x_3515_ = lean_unsigned_to_nat(4u);
v___x_3516_ = lean_nat_mul(v_size_x27_3512_, v___x_3515_);
v___x_3517_ = lean_unsigned_to_nat(3u);
v___x_3518_ = lean_nat_div(v___x_3516_, v___x_3517_);
lean_dec(v___x_3516_);
v___x_3519_ = lean_array_get_size(v_buckets_x27_3514_);
v___x_3520_ = lean_nat_dec_le(v___x_3518_, v___x_3519_);
lean_dec(v___x_3518_);
if (v___x_3520_ == 0)
{
lean_object* v_val_3521_; lean_object* v___x_3523_; 
v_val_3521_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2___redArg(v_buckets_x27_3514_);
if (v_isShared_3495_ == 0)
{
lean_ctor_set(v___x_3494_, 1, v_val_3521_);
lean_ctor_set(v___x_3494_, 0, v_size_x27_3512_);
v___x_3523_ = v___x_3494_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v_size_x27_3512_);
lean_ctor_set(v_reuseFailAlloc_3524_, 1, v_val_3521_);
v___x_3523_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
return v___x_3523_;
}
}
else
{
lean_object* v___x_3526_; 
if (v_isShared_3495_ == 0)
{
lean_ctor_set(v___x_3494_, 1, v_buckets_x27_3514_);
lean_ctor_set(v___x_3494_, 0, v_size_x27_3512_);
v___x_3526_ = v___x_3494_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v_size_x27_3512_);
lean_ctor_set(v_reuseFailAlloc_3527_, 1, v_buckets_x27_3514_);
v___x_3526_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
return v___x_3526_;
}
}
}
else
{
lean_object* v___x_3528_; lean_object* v_buckets_x27_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3533_; 
lean_inc(v_bkt_3509_);
v___x_3528_ = lean_box(0);
v_buckets_x27_3529_ = lean_array_uset(v_buckets_3492_, v___x_3508_, v___x_3528_);
v___x_3530_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3___redArg(v_a_3489_, v_b_3490_, v_bkt_3509_);
v___x_3531_ = lean_array_uset(v_buckets_x27_3529_, v___x_3508_, v___x_3530_);
if (v_isShared_3495_ == 0)
{
lean_ctor_set(v___x_3494_, 1, v___x_3531_);
v___x_3533_ = v___x_3494_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v_size_3491_);
lean_ctor_set(v_reuseFailAlloc_3534_, 1, v___x_3531_);
v___x_3533_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3532_;
}
v_reusejp_3532_:
{
return v___x_3533_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg(lean_object* v_m_3536_, lean_object* v_a_3537_){
_start:
{
lean_object* v_buckets_3538_; lean_object* v___x_3539_; uint64_t v___x_3540_; uint64_t v___x_3541_; uint64_t v___x_3542_; uint64_t v_fold_3543_; uint64_t v___x_3544_; uint64_t v___x_3545_; uint64_t v___x_3546_; size_t v___x_3547_; size_t v___x_3548_; size_t v___x_3549_; size_t v___x_3550_; size_t v___x_3551_; lean_object* v___x_3552_; uint8_t v___x_3553_; 
v_buckets_3538_ = lean_ctor_get(v_m_3536_, 1);
v___x_3539_ = lean_array_get_size(v_buckets_3538_);
v___x_3540_ = lean_string_hash(v_a_3537_);
v___x_3541_ = 32ULL;
v___x_3542_ = lean_uint64_shift_right(v___x_3540_, v___x_3541_);
v_fold_3543_ = lean_uint64_xor(v___x_3540_, v___x_3542_);
v___x_3544_ = 16ULL;
v___x_3545_ = lean_uint64_shift_right(v_fold_3543_, v___x_3544_);
v___x_3546_ = lean_uint64_xor(v_fold_3543_, v___x_3545_);
v___x_3547_ = lean_uint64_to_usize(v___x_3546_);
v___x_3548_ = lean_usize_of_nat(v___x_3539_);
v___x_3549_ = ((size_t)1ULL);
v___x_3550_ = lean_usize_sub(v___x_3548_, v___x_3549_);
v___x_3551_ = lean_usize_land(v___x_3547_, v___x_3550_);
v___x_3552_ = lean_array_uget_borrowed(v_buckets_3538_, v___x_3551_);
v___x_3553_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(v_a_3537_, v___x_3552_);
return v___x_3553_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg___boxed(lean_object* v_m_3554_, lean_object* v_a_3555_){
_start:
{
uint8_t v_res_3556_; lean_object* v_r_3557_; 
v_res_3556_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg(v_m_3554_, v_a_3555_);
lean_dec_ref(v_a_3555_);
lean_dec_ref(v_m_3554_);
v_r_3557_ = lean_box(v_res_3556_);
return v_r_3557_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg(lean_object* v_cfg_3558_, lean_object* v_as_x27_3559_, lean_object* v_b_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_){
_start:
{
if (lean_obj_tag(v_as_x27_3559_) == 0)
{
lean_object* v___x_3566_; 
lean_dec_ref(v_cfg_3558_);
v___x_3566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3566_, 0, v_b_3560_);
return v___x_3566_;
}
else
{
lean_object* v_head_3567_; lean_object* v_snd_3568_; lean_object* v_tail_3569_; lean_object* v_fst_3570_; lean_object* v_fst_3571_; lean_object* v_snd_3572_; lean_object* v___x_3573_; 
v_head_3567_ = lean_ctor_get(v_as_x27_3559_, 0);
v_snd_3568_ = lean_ctor_get(v_head_3567_, 1);
v_tail_3569_ = lean_ctor_get(v_as_x27_3559_, 1);
v_fst_3570_ = lean_ctor_get(v_head_3567_, 0);
v_fst_3571_ = lean_ctor_get(v_snd_3568_, 0);
v_snd_3572_ = lean_ctor_get(v_snd_3568_, 1);
v___x_3573_ = l_Lean_getRemainingHeartbeats___redArg(v___y_3563_);
if (lean_obj_tag(v___x_3573_) == 0)
{
lean_object* v_snd_3574_; lean_object* v___x_3576_; uint8_t v_isShared_3577_; uint8_t v_isSharedCheck_3718_; 
v_snd_3574_ = lean_ctor_get(v_b_3560_, 1);
v_isSharedCheck_3718_ = !lean_is_exclusive(v_b_3560_);
if (v_isSharedCheck_3718_ == 0)
{
lean_object* v_unused_3719_; 
v_unused_3719_ = lean_ctor_get(v_b_3560_, 0);
lean_dec(v_unused_3719_);
v___x_3576_ = v_b_3560_;
v_isShared_3577_ = v_isSharedCheck_3718_;
goto v_resetjp_3575_;
}
else
{
lean_inc(v_snd_3574_);
lean_dec(v_b_3560_);
v___x_3576_ = lean_box(0);
v_isShared_3577_ = v_isSharedCheck_3718_;
goto v_resetjp_3575_;
}
v_resetjp_3575_:
{
lean_object* v_a_3578_; lean_object* v___x_3580_; uint8_t v_isShared_3581_; uint8_t v_isSharedCheck_3717_; 
v_a_3578_ = lean_ctor_get(v___x_3573_, 0);
v_isSharedCheck_3717_ = !lean_is_exclusive(v___x_3573_);
if (v_isSharedCheck_3717_ == 0)
{
v___x_3580_ = v___x_3573_;
v_isShared_3581_ = v_isSharedCheck_3717_;
goto v_resetjp_3579_;
}
else
{
lean_inc(v_a_3578_);
lean_dec(v___x_3573_);
v___x_3580_ = lean_box(0);
v_isShared_3581_ = v_isSharedCheck_3717_;
goto v_resetjp_3579_;
}
v_resetjp_3579_:
{
lean_object* v_fst_3582_; lean_object* v_snd_3583_; lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3716_; 
v_fst_3582_ = lean_ctor_get(v_snd_3574_, 0);
v_snd_3583_ = lean_ctor_get(v_snd_3574_, 1);
v_isSharedCheck_3716_ = !lean_is_exclusive(v_snd_3574_);
if (v_isSharedCheck_3716_ == 0)
{
v___x_3585_ = v_snd_3574_;
v_isShared_3586_ = v_isSharedCheck_3716_;
goto v_resetjp_3584_;
}
else
{
lean_inc(v_snd_3583_);
lean_inc(v_fst_3582_);
lean_dec(v_snd_3574_);
v___x_3585_ = lean_box(0);
v_isShared_3586_ = v_isSharedCheck_3716_;
goto v_resetjp_3584_;
}
v_resetjp_3584_:
{
uint8_t v_stopAtRfl_3587_; lean_object* v_max_3588_; lean_object* v_minHeartbeats_3589_; lean_object* v_goal_3590_; lean_object* v_target_3591_; uint8_t v_side_3592_; lean_object* v_mctx_3593_; uint8_t v___x_3594_; 
v_stopAtRfl_3587_ = lean_ctor_get_uint8(v_cfg_3558_, sizeof(void*)*5);
v_max_3588_ = lean_ctor_get(v_cfg_3558_, 0);
v_minHeartbeats_3589_ = lean_ctor_get(v_cfg_3558_, 1);
v_goal_3590_ = lean_ctor_get(v_cfg_3558_, 2);
v_target_3591_ = lean_ctor_get(v_cfg_3558_, 3);
v_side_3592_ = lean_ctor_get_uint8(v_cfg_3558_, sizeof(void*)*5 + 1);
v_mctx_3593_ = lean_ctor_get(v_cfg_3558_, 4);
v___x_3594_ = lean_nat_dec_lt(v_a_3578_, v_minHeartbeats_3589_);
lean_dec(v_a_3578_);
if (v___x_3594_ == 0)
{
lean_object* v___x_3595_; uint8_t v___x_3596_; 
v___x_3595_ = lean_array_get_size(v_snd_3583_);
v___x_3596_ = lean_nat_dec_le(v_max_3588_, v___x_3595_);
if (v___x_3596_ == 0)
{
lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; 
lean_del_object(v___x_3580_);
v___x_3597_ = lean_box(v_side_3592_);
lean_inc(v_snd_3572_);
lean_inc(v_fst_3571_);
lean_inc(v_fst_3570_);
lean_inc_ref(v_target_3591_);
lean_inc(v_goal_3590_);
lean_inc_ref_n(v_mctx_3593_, 2);
v___x_3598_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_rwLemma___boxed), 12, 7);
lean_closure_set(v___x_3598_, 0, v_mctx_3593_);
lean_closure_set(v___x_3598_, 1, v_goal_3590_);
lean_closure_set(v___x_3598_, 2, v_target_3591_);
lean_closure_set(v___x_3598_, 3, v___x_3597_);
lean_closure_set(v___x_3598_, 4, v_fst_3570_);
lean_closure_set(v___x_3598_, 5, v_fst_3571_);
lean_closure_set(v___x_3598_, 6, v_snd_3572_);
v___x_3599_ = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___boxed), 8, 3);
lean_closure_set(v___x_3599_, 0, lean_box(0));
lean_closure_set(v___x_3599_, 1, v_mctx_3593_);
lean_closure_set(v___x_3599_, 2, v___x_3598_);
v___x_3600_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v___x_3599_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_);
if (lean_obj_tag(v___x_3600_) == 0)
{
lean_object* v_a_3601_; lean_object* v___x_3602_; 
v_a_3601_ = lean_ctor_get(v___x_3600_, 0);
lean_inc(v_a_3601_);
lean_dec_ref_known(v___x_3600_, 1);
v___x_3602_ = lean_box(0);
if (lean_obj_tag(v_a_3601_) == 0)
{
lean_object* v___x_3604_; 
if (v_isShared_3586_ == 0)
{
v___x_3604_ = v___x_3585_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v_fst_3582_);
lean_ctor_set(v_reuseFailAlloc_3609_, 1, v_snd_3583_);
v___x_3604_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
lean_object* v___x_3606_; 
if (v_isShared_3577_ == 0)
{
lean_ctor_set(v___x_3576_, 1, v___x_3604_);
lean_ctor_set(v___x_3576_, 0, v___x_3602_);
v___x_3606_ = v___x_3576_;
goto v_reusejp_3605_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v___x_3602_);
lean_ctor_set(v_reuseFailAlloc_3608_, 1, v___x_3604_);
v___x_3606_ = v_reuseFailAlloc_3608_;
goto v_reusejp_3605_;
}
v_reusejp_3605_:
{
v_as_x27_3559_ = v_tail_3569_;
v_b_3560_ = v___x_3606_;
goto _start;
}
}
}
else
{
lean_object* v_val_3610_; lean_object* v___x_3612_; uint8_t v_isShared_3613_; uint8_t v_isSharedCheck_3687_; 
v_val_3610_ = lean_ctor_get(v_a_3601_, 0);
v_isSharedCheck_3687_ = !lean_is_exclusive(v_a_3601_);
if (v_isSharedCheck_3687_ == 0)
{
v___x_3612_ = v_a_3601_;
v_isShared_3613_ = v_isSharedCheck_3687_;
goto v_resetjp_3611_;
}
else
{
lean_inc(v_val_3610_);
lean_dec(v_a_3601_);
v___x_3612_ = lean_box(0);
v_isShared_3613_ = v_isSharedCheck_3687_;
goto v_resetjp_3611_;
}
v_resetjp_3611_:
{
lean_object* v_result_3614_; lean_object* v_mctx_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; 
v_result_3614_ = lean_ctor_get(v_val_3610_, 2);
v_mctx_3615_ = lean_ctor_get(v_val_3610_, 3);
lean_inc(v_val_3610_);
v___x_3616_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult___boxed), 6, 1);
lean_closure_set(v___x_3616_, 0, v_val_3610_);
lean_inc_ref(v_mctx_3615_);
v___x_3617_ = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___boxed), 8, 3);
lean_closure_set(v___x_3617_, 0, lean_box(0));
lean_closure_set(v___x_3617_, 1, v_mctx_3615_);
lean_closure_set(v___x_3617_, 2, v___x_3616_);
v___x_3618_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v___x_3617_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_);
if (lean_obj_tag(v___x_3618_) == 0)
{
lean_object* v_a_3619_; uint8_t v___x_3620_; 
v_a_3619_ = lean_ctor_get(v___x_3618_, 0);
lean_inc(v_a_3619_);
lean_dec_ref_known(v___x_3618_, 1);
v___x_3620_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg(v_fst_3582_, v_a_3619_);
if (v___x_3620_ == 0)
{
lean_object* v_eNew_3621_; lean_object* v___x_3622_; 
v_eNew_3621_ = lean_ctor_get(v_result_3614_, 0);
lean_inc_ref(v_eNew_3621_);
lean_inc_ref(v_mctx_3615_);
v___x_3622_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(v_mctx_3615_, v_eNew_3621_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_);
if (lean_obj_tag(v___x_3622_) == 0)
{
if (v_stopAtRfl_3587_ == 0)
{
lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3627_; 
lean_dec_ref_known(v___x_3622_, 1);
lean_del_object(v___x_3612_);
v___x_3623_ = lean_box(0);
v___x_3624_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1___redArg(v_fst_3582_, v_a_3619_, v___x_3623_);
v___x_3625_ = lean_array_push(v_snd_3583_, v_val_3610_);
if (v_isShared_3586_ == 0)
{
lean_ctor_set(v___x_3585_, 1, v___x_3625_);
lean_ctor_set(v___x_3585_, 0, v___x_3624_);
v___x_3627_ = v___x_3585_;
goto v_reusejp_3626_;
}
else
{
lean_object* v_reuseFailAlloc_3632_; 
v_reuseFailAlloc_3632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3632_, 0, v___x_3624_);
lean_ctor_set(v_reuseFailAlloc_3632_, 1, v___x_3625_);
v___x_3627_ = v_reuseFailAlloc_3632_;
goto v_reusejp_3626_;
}
v_reusejp_3626_:
{
lean_object* v___x_3629_; 
if (v_isShared_3577_ == 0)
{
lean_ctor_set(v___x_3576_, 1, v___x_3627_);
lean_ctor_set(v___x_3576_, 0, v___x_3602_);
v___x_3629_ = v___x_3576_;
goto v_reusejp_3628_;
}
else
{
lean_object* v_reuseFailAlloc_3631_; 
v_reuseFailAlloc_3631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3631_, 0, v___x_3602_);
lean_ctor_set(v_reuseFailAlloc_3631_, 1, v___x_3627_);
v___x_3629_ = v_reuseFailAlloc_3631_;
goto v_reusejp_3628_;
}
v_reusejp_3628_:
{
v_as_x27_3559_ = v_tail_3569_;
v_b_3560_ = v___x_3629_;
goto _start;
}
}
}
else
{
lean_object* v_a_3633_; lean_object* v___x_3635_; uint8_t v_isShared_3636_; uint8_t v_isSharedCheck_3663_; 
v_a_3633_ = lean_ctor_get(v___x_3622_, 0);
v_isSharedCheck_3663_ = !lean_is_exclusive(v___x_3622_);
if (v_isSharedCheck_3663_ == 0)
{
v___x_3635_ = v___x_3622_;
v_isShared_3636_ = v_isSharedCheck_3663_;
goto v_resetjp_3634_;
}
else
{
lean_inc(v_a_3633_);
lean_dec(v___x_3622_);
v___x_3635_ = lean_box(0);
v_isShared_3636_ = v_isSharedCheck_3663_;
goto v_resetjp_3634_;
}
v_resetjp_3634_:
{
uint8_t v___x_3637_; 
v___x_3637_ = lean_unbox(v_a_3633_);
lean_dec(v_a_3633_);
if (v___x_3637_ == 0)
{
lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3642_; 
lean_del_object(v___x_3635_);
lean_del_object(v___x_3612_);
v___x_3638_ = lean_box(0);
v___x_3639_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1___redArg(v_fst_3582_, v_a_3619_, v___x_3638_);
v___x_3640_ = lean_array_push(v_snd_3583_, v_val_3610_);
if (v_isShared_3586_ == 0)
{
lean_ctor_set(v___x_3585_, 1, v___x_3640_);
lean_ctor_set(v___x_3585_, 0, v___x_3639_);
v___x_3642_ = v___x_3585_;
goto v_reusejp_3641_;
}
else
{
lean_object* v_reuseFailAlloc_3647_; 
v_reuseFailAlloc_3647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3647_, 0, v___x_3639_);
lean_ctor_set(v_reuseFailAlloc_3647_, 1, v___x_3640_);
v___x_3642_ = v_reuseFailAlloc_3647_;
goto v_reusejp_3641_;
}
v_reusejp_3641_:
{
lean_object* v___x_3644_; 
if (v_isShared_3577_ == 0)
{
lean_ctor_set(v___x_3576_, 1, v___x_3642_);
lean_ctor_set(v___x_3576_, 0, v___x_3602_);
v___x_3644_ = v___x_3576_;
goto v_reusejp_3643_;
}
else
{
lean_object* v_reuseFailAlloc_3646_; 
v_reuseFailAlloc_3646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3646_, 0, v___x_3602_);
lean_ctor_set(v_reuseFailAlloc_3646_, 1, v___x_3642_);
v___x_3644_ = v_reuseFailAlloc_3646_;
goto v_reusejp_3643_;
}
v_reusejp_3643_:
{
v_as_x27_3559_ = v_tail_3569_;
v_b_3560_ = v___x_3644_;
goto _start;
}
}
}
else
{
lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3652_; 
lean_dec(v_a_3619_);
lean_dec_ref(v_cfg_3558_);
v___x_3648_ = lean_unsigned_to_nat(1u);
v___x_3649_ = lean_mk_empty_array_with_capacity(v___x_3648_);
v___x_3650_ = lean_array_push(v___x_3649_, v_val_3610_);
if (v_isShared_3613_ == 0)
{
lean_ctor_set(v___x_3612_, 0, v___x_3650_);
v___x_3652_ = v___x_3612_;
goto v_reusejp_3651_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v___x_3650_);
v___x_3652_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3651_;
}
v_reusejp_3651_:
{
lean_object* v___x_3654_; 
if (v_isShared_3586_ == 0)
{
v___x_3654_ = v___x_3585_;
goto v_reusejp_3653_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v_fst_3582_);
lean_ctor_set(v_reuseFailAlloc_3661_, 1, v_snd_3583_);
v___x_3654_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3653_;
}
v_reusejp_3653_:
{
lean_object* v___x_3656_; 
if (v_isShared_3577_ == 0)
{
lean_ctor_set(v___x_3576_, 1, v___x_3654_);
lean_ctor_set(v___x_3576_, 0, v___x_3652_);
v___x_3656_ = v___x_3576_;
goto v_reusejp_3655_;
}
else
{
lean_object* v_reuseFailAlloc_3660_; 
v_reuseFailAlloc_3660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3660_, 0, v___x_3652_);
lean_ctor_set(v_reuseFailAlloc_3660_, 1, v___x_3654_);
v___x_3656_ = v_reuseFailAlloc_3660_;
goto v_reusejp_3655_;
}
v_reusejp_3655_:
{
lean_object* v___x_3658_; 
if (v_isShared_3636_ == 0)
{
lean_ctor_set(v___x_3635_, 0, v___x_3656_);
v___x_3658_ = v___x_3635_;
goto v_reusejp_3657_;
}
else
{
lean_object* v_reuseFailAlloc_3659_; 
v_reuseFailAlloc_3659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3659_, 0, v___x_3656_);
v___x_3658_ = v_reuseFailAlloc_3659_;
goto v_reusejp_3657_;
}
v_reusejp_3657_:
{
return v___x_3658_;
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
lean_object* v_a_3664_; lean_object* v___x_3666_; uint8_t v_isShared_3667_; uint8_t v_isSharedCheck_3671_; 
lean_dec(v_a_3619_);
lean_del_object(v___x_3612_);
lean_dec(v_val_3610_);
lean_del_object(v___x_3585_);
lean_dec(v_snd_3583_);
lean_dec(v_fst_3582_);
lean_del_object(v___x_3576_);
lean_dec_ref(v_cfg_3558_);
v_a_3664_ = lean_ctor_get(v___x_3622_, 0);
v_isSharedCheck_3671_ = !lean_is_exclusive(v___x_3622_);
if (v_isSharedCheck_3671_ == 0)
{
v___x_3666_ = v___x_3622_;
v_isShared_3667_ = v_isSharedCheck_3671_;
goto v_resetjp_3665_;
}
else
{
lean_inc(v_a_3664_);
lean_dec(v___x_3622_);
v___x_3666_ = lean_box(0);
v_isShared_3667_ = v_isSharedCheck_3671_;
goto v_resetjp_3665_;
}
v_resetjp_3665_:
{
lean_object* v___x_3669_; 
if (v_isShared_3667_ == 0)
{
v___x_3669_ = v___x_3666_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v_a_3664_);
v___x_3669_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
return v___x_3669_;
}
}
}
}
else
{
lean_object* v___x_3673_; 
lean_dec(v_a_3619_);
lean_del_object(v___x_3612_);
lean_dec(v_val_3610_);
if (v_isShared_3586_ == 0)
{
v___x_3673_ = v___x_3585_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3678_; 
v_reuseFailAlloc_3678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3678_, 0, v_fst_3582_);
lean_ctor_set(v_reuseFailAlloc_3678_, 1, v_snd_3583_);
v___x_3673_ = v_reuseFailAlloc_3678_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
lean_object* v___x_3675_; 
if (v_isShared_3577_ == 0)
{
lean_ctor_set(v___x_3576_, 1, v___x_3673_);
lean_ctor_set(v___x_3576_, 0, v___x_3602_);
v___x_3675_ = v___x_3576_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3677_; 
v_reuseFailAlloc_3677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3677_, 0, v___x_3602_);
lean_ctor_set(v_reuseFailAlloc_3677_, 1, v___x_3673_);
v___x_3675_ = v_reuseFailAlloc_3677_;
goto v_reusejp_3674_;
}
v_reusejp_3674_:
{
v_as_x27_3559_ = v_tail_3569_;
v_b_3560_ = v___x_3675_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3679_; lean_object* v___x_3681_; uint8_t v_isShared_3682_; uint8_t v_isSharedCheck_3686_; 
lean_del_object(v___x_3612_);
lean_dec(v_val_3610_);
lean_del_object(v___x_3585_);
lean_dec(v_snd_3583_);
lean_dec(v_fst_3582_);
lean_del_object(v___x_3576_);
lean_dec_ref(v_cfg_3558_);
v_a_3679_ = lean_ctor_get(v___x_3618_, 0);
v_isSharedCheck_3686_ = !lean_is_exclusive(v___x_3618_);
if (v_isSharedCheck_3686_ == 0)
{
v___x_3681_ = v___x_3618_;
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
else
{
lean_inc(v_a_3679_);
lean_dec(v___x_3618_);
v___x_3681_ = lean_box(0);
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
v_resetjp_3680_:
{
lean_object* v___x_3684_; 
if (v_isShared_3682_ == 0)
{
v___x_3684_ = v___x_3681_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3685_; 
v_reuseFailAlloc_3685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3685_, 0, v_a_3679_);
v___x_3684_ = v_reuseFailAlloc_3685_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
return v___x_3684_;
}
}
}
}
}
}
else
{
lean_object* v_a_3688_; lean_object* v___x_3690_; uint8_t v_isShared_3691_; uint8_t v_isSharedCheck_3695_; 
lean_del_object(v___x_3585_);
lean_dec(v_snd_3583_);
lean_dec(v_fst_3582_);
lean_del_object(v___x_3576_);
lean_dec_ref(v_cfg_3558_);
v_a_3688_ = lean_ctor_get(v___x_3600_, 0);
v_isSharedCheck_3695_ = !lean_is_exclusive(v___x_3600_);
if (v_isSharedCheck_3695_ == 0)
{
v___x_3690_ = v___x_3600_;
v_isShared_3691_ = v_isSharedCheck_3695_;
goto v_resetjp_3689_;
}
else
{
lean_inc(v_a_3688_);
lean_dec(v___x_3600_);
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
else
{
lean_object* v___x_3696_; lean_object* v___x_3698_; 
lean_dec_ref(v_cfg_3558_);
lean_inc(v_snd_3583_);
v___x_3696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3696_, 0, v_snd_3583_);
if (v_isShared_3586_ == 0)
{
v___x_3698_ = v___x_3585_;
goto v_reusejp_3697_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v_fst_3582_);
lean_ctor_set(v_reuseFailAlloc_3705_, 1, v_snd_3583_);
v___x_3698_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3697_;
}
v_reusejp_3697_:
{
lean_object* v___x_3700_; 
if (v_isShared_3577_ == 0)
{
lean_ctor_set(v___x_3576_, 1, v___x_3698_);
lean_ctor_set(v___x_3576_, 0, v___x_3696_);
v___x_3700_ = v___x_3576_;
goto v_reusejp_3699_;
}
else
{
lean_object* v_reuseFailAlloc_3704_; 
v_reuseFailAlloc_3704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3704_, 0, v___x_3696_);
lean_ctor_set(v_reuseFailAlloc_3704_, 1, v___x_3698_);
v___x_3700_ = v_reuseFailAlloc_3704_;
goto v_reusejp_3699_;
}
v_reusejp_3699_:
{
lean_object* v___x_3702_; 
if (v_isShared_3581_ == 0)
{
lean_ctor_set(v___x_3580_, 0, v___x_3700_);
v___x_3702_ = v___x_3580_;
goto v_reusejp_3701_;
}
else
{
lean_object* v_reuseFailAlloc_3703_; 
v_reuseFailAlloc_3703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3703_, 0, v___x_3700_);
v___x_3702_ = v_reuseFailAlloc_3703_;
goto v_reusejp_3701_;
}
v_reusejp_3701_:
{
return v___x_3702_;
}
}
}
}
}
else
{
lean_object* v___x_3706_; lean_object* v___x_3708_; 
lean_dec_ref(v_cfg_3558_);
lean_inc(v_snd_3583_);
v___x_3706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3706_, 0, v_snd_3583_);
if (v_isShared_3586_ == 0)
{
v___x_3708_ = v___x_3585_;
goto v_reusejp_3707_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v_fst_3582_);
lean_ctor_set(v_reuseFailAlloc_3715_, 1, v_snd_3583_);
v___x_3708_ = v_reuseFailAlloc_3715_;
goto v_reusejp_3707_;
}
v_reusejp_3707_:
{
lean_object* v___x_3710_; 
if (v_isShared_3577_ == 0)
{
lean_ctor_set(v___x_3576_, 1, v___x_3708_);
lean_ctor_set(v___x_3576_, 0, v___x_3706_);
v___x_3710_ = v___x_3576_;
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
if (v_isShared_3581_ == 0)
{
lean_ctor_set(v___x_3580_, 0, v___x_3710_);
v___x_3712_ = v___x_3580_;
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
}
}
}
else
{
lean_object* v_a_3720_; lean_object* v___x_3722_; uint8_t v_isShared_3723_; uint8_t v_isSharedCheck_3727_; 
lean_dec_ref(v_b_3560_);
lean_dec_ref(v_cfg_3558_);
v_a_3720_ = lean_ctor_get(v___x_3573_, 0);
v_isSharedCheck_3727_ = !lean_is_exclusive(v___x_3573_);
if (v_isSharedCheck_3727_ == 0)
{
v___x_3722_ = v___x_3573_;
v_isShared_3723_ = v_isSharedCheck_3727_;
goto v_resetjp_3721_;
}
else
{
lean_inc(v_a_3720_);
lean_dec(v___x_3573_);
v___x_3722_ = lean_box(0);
v_isShared_3723_ = v_isSharedCheck_3727_;
goto v_resetjp_3721_;
}
v_resetjp_3721_:
{
lean_object* v___x_3725_; 
if (v_isShared_3723_ == 0)
{
v___x_3725_ = v___x_3722_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v_a_3720_);
v___x_3725_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
return v___x_3725_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg___boxed(lean_object* v_cfg_3728_, lean_object* v_as_x27_3729_, lean_object* v_b_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_){
_start:
{
lean_object* v_res_3736_; 
v_res_3736_ = l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg(v_cfg_3728_, v_as_x27_3729_, v_b_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_);
lean_dec(v___y_3734_);
lean_dec_ref(v___y_3733_);
lean_dec(v___y_3732_);
lean_dec_ref(v___y_3731_);
lean_dec(v_as_x27_3729_);
return v_res_3736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_takeListAux(lean_object* v_cfg_3737_, lean_object* v_seen_3738_, lean_object* v_acc_3739_, lean_object* v_xs_3740_, lean_object* v_a_3741_, lean_object* v_a_3742_, lean_object* v_a_3743_, lean_object* v_a_3744_){
_start:
{
lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; 
v___x_3746_ = lean_box(0);
v___x_3747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3747_, 0, v_seen_3738_);
lean_ctor_set(v___x_3747_, 1, v_acc_3739_);
v___x_3748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3748_, 0, v___x_3746_);
lean_ctor_set(v___x_3748_, 1, v___x_3747_);
v___x_3749_ = l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg(v_cfg_3737_, v_xs_3740_, v___x_3748_, v_a_3741_, v_a_3742_, v_a_3743_, v_a_3744_);
if (lean_obj_tag(v___x_3749_) == 0)
{
lean_object* v_a_3750_; lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3764_; 
v_a_3750_ = lean_ctor_get(v___x_3749_, 0);
v_isSharedCheck_3764_ = !lean_is_exclusive(v___x_3749_);
if (v_isSharedCheck_3764_ == 0)
{
v___x_3752_ = v___x_3749_;
v_isShared_3753_ = v_isSharedCheck_3764_;
goto v_resetjp_3751_;
}
else
{
lean_inc(v_a_3750_);
lean_dec(v___x_3749_);
v___x_3752_ = lean_box(0);
v_isShared_3753_ = v_isSharedCheck_3764_;
goto v_resetjp_3751_;
}
v_resetjp_3751_:
{
lean_object* v_fst_3754_; 
v_fst_3754_ = lean_ctor_get(v_a_3750_, 0);
if (lean_obj_tag(v_fst_3754_) == 0)
{
lean_object* v_snd_3755_; lean_object* v_snd_3756_; lean_object* v___x_3758_; 
v_snd_3755_ = lean_ctor_get(v_a_3750_, 1);
lean_inc(v_snd_3755_);
lean_dec(v_a_3750_);
v_snd_3756_ = lean_ctor_get(v_snd_3755_, 1);
lean_inc(v_snd_3756_);
lean_dec(v_snd_3755_);
if (v_isShared_3753_ == 0)
{
lean_ctor_set(v___x_3752_, 0, v_snd_3756_);
v___x_3758_ = v___x_3752_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3759_; 
v_reuseFailAlloc_3759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3759_, 0, v_snd_3756_);
v___x_3758_ = v_reuseFailAlloc_3759_;
goto v_reusejp_3757_;
}
v_reusejp_3757_:
{
return v___x_3758_;
}
}
else
{
lean_object* v_val_3760_; lean_object* v___x_3762_; 
lean_inc_ref(v_fst_3754_);
lean_dec(v_a_3750_);
v_val_3760_ = lean_ctor_get(v_fst_3754_, 0);
lean_inc(v_val_3760_);
lean_dec_ref_known(v_fst_3754_, 1);
if (v_isShared_3753_ == 0)
{
lean_ctor_set(v___x_3752_, 0, v_val_3760_);
v___x_3762_ = v___x_3752_;
goto v_reusejp_3761_;
}
else
{
lean_object* v_reuseFailAlloc_3763_; 
v_reuseFailAlloc_3763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3763_, 0, v_val_3760_);
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
lean_object* v_a_3765_; lean_object* v___x_3767_; uint8_t v_isShared_3768_; uint8_t v_isSharedCheck_3772_; 
v_a_3765_ = lean_ctor_get(v___x_3749_, 0);
v_isSharedCheck_3772_ = !lean_is_exclusive(v___x_3749_);
if (v_isSharedCheck_3772_ == 0)
{
v___x_3767_ = v___x_3749_;
v_isShared_3768_ = v_isSharedCheck_3772_;
goto v_resetjp_3766_;
}
else
{
lean_inc(v_a_3765_);
lean_dec(v___x_3749_);
v___x_3767_ = lean_box(0);
v_isShared_3768_ = v_isSharedCheck_3772_;
goto v_resetjp_3766_;
}
v_resetjp_3766_:
{
lean_object* v___x_3770_; 
if (v_isShared_3768_ == 0)
{
v___x_3770_ = v___x_3767_;
goto v_reusejp_3769_;
}
else
{
lean_object* v_reuseFailAlloc_3771_; 
v_reuseFailAlloc_3771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3771_, 0, v_a_3765_);
v___x_3770_ = v_reuseFailAlloc_3771_;
goto v_reusejp_3769_;
}
v_reusejp_3769_:
{
return v___x_3770_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_takeListAux___boxed(lean_object* v_cfg_3773_, lean_object* v_seen_3774_, lean_object* v_acc_3775_, lean_object* v_xs_3776_, lean_object* v_a_3777_, lean_object* v_a_3778_, lean_object* v_a_3779_, lean_object* v_a_3780_, lean_object* v_a_3781_){
_start:
{
lean_object* v_res_3782_; 
v_res_3782_ = l_Lean_Meta_Rewrites_takeListAux(v_cfg_3773_, v_seen_3774_, v_acc_3775_, v_xs_3776_, v_a_3777_, v_a_3778_, v_a_3779_, v_a_3780_);
lean_dec(v_a_3780_);
lean_dec_ref(v_a_3779_);
lean_dec(v_a_3778_);
lean_dec_ref(v_a_3777_);
lean_dec(v_xs_3776_);
return v_res_3782_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0(lean_object* v_00_u03b2_3783_, lean_object* v_m_3784_, lean_object* v_a_3785_){
_start:
{
uint8_t v___x_3786_; 
v___x_3786_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg(v_m_3784_, v_a_3785_);
return v___x_3786_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___boxed(lean_object* v_00_u03b2_3787_, lean_object* v_m_3788_, lean_object* v_a_3789_){
_start:
{
uint8_t v_res_3790_; lean_object* v_r_3791_; 
v_res_3790_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0(v_00_u03b2_3787_, v_m_3788_, v_a_3789_);
lean_dec_ref(v_a_3789_);
lean_dec_ref(v_m_3788_);
v_r_3791_ = lean_box(v_res_3790_);
return v_r_3791_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1(lean_object* v_00_u03b2_3792_, lean_object* v_m_3793_, lean_object* v_a_3794_, lean_object* v_b_3795_){
_start:
{
lean_object* v___x_3796_; 
v___x_3796_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1___redArg(v_m_3793_, v_a_3794_, v_b_3795_);
return v___x_3796_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2(lean_object* v_cfg_3797_, lean_object* v_as_3798_, lean_object* v_as_x27_3799_, lean_object* v_b_3800_, lean_object* v_a_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_){
_start:
{
lean_object* v___x_3807_; 
v___x_3807_ = l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg(v_cfg_3797_, v_as_x27_3799_, v_b_3800_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_);
return v___x_3807_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___boxed(lean_object* v_cfg_3808_, lean_object* v_as_3809_, lean_object* v_as_x27_3810_, lean_object* v_b_3811_, lean_object* v_a_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_){
_start:
{
lean_object* v_res_3818_; 
v_res_3818_ = l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2(v_cfg_3808_, v_as_3809_, v_as_x27_3810_, v_b_3811_, v_a_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_);
lean_dec(v___y_3816_);
lean_dec_ref(v___y_3815_);
lean_dec(v___y_3814_);
lean_dec_ref(v___y_3813_);
lean_dec(v_as_x27_3810_);
lean_dec(v_as_3809_);
return v_res_3818_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0(lean_object* v_00_u03b2_3819_, lean_object* v_a_3820_, lean_object* v_x_3821_){
_start:
{
uint8_t v___x_3822_; 
v___x_3822_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(v_a_3820_, v_x_3821_);
return v___x_3822_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3823_, lean_object* v_a_3824_, lean_object* v_x_3825_){
_start:
{
uint8_t v_res_3826_; lean_object* v_r_3827_; 
v_res_3826_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0(v_00_u03b2_3823_, v_a_3824_, v_x_3825_);
lean_dec(v_x_3825_);
lean_dec_ref(v_a_3824_);
v_r_3827_ = lean_box(v_res_3826_);
return v_r_3827_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2(lean_object* v_00_u03b2_3828_, lean_object* v_data_3829_){
_start:
{
lean_object* v___x_3830_; 
v___x_3830_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2___redArg(v_data_3829_);
return v___x_3830_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3(lean_object* v_00_u03b2_3831_, lean_object* v_a_3832_, lean_object* v_b_3833_, lean_object* v_x_3834_){
_start:
{
lean_object* v___x_3835_; 
v___x_3835_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3___redArg(v_a_3832_, v_b_3833_, v_x_3834_);
return v___x_3835_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_3836_, lean_object* v_i_3837_, lean_object* v_source_3838_, lean_object* v_target_3839_){
_start:
{
lean_object* v___x_3840_; 
v___x_3840_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3___redArg(v_i_3837_, v_source_3838_, v_target_3839_);
return v___x_3840_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_3841_, lean_object* v_x_3842_, lean_object* v_x_3843_){
_start:
{
lean_object* v___x_3844_; 
v___x_3844_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3_spec__5___redArg(v_x_3842_, v_x_3843_);
return v___x_3844_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_findRewrites___closed__0(void){
_start:
{
lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; 
v___x_3845_ = lean_box(0);
v___x_3846_ = lean_unsigned_to_nat(16u);
v___x_3847_ = lean_mk_array(v___x_3846_, v___x_3845_);
return v___x_3847_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_findRewrites___closed__1(void){
_start:
{
lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; 
v___x_3848_ = lean_obj_once(&l_Lean_Meta_Rewrites_findRewrites___closed__0, &l_Lean_Meta_Rewrites_findRewrites___closed__0_once, _init_l_Lean_Meta_Rewrites_findRewrites___closed__0);
v___x_3849_ = lean_unsigned_to_nat(0u);
v___x_3850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3850_, 0, v___x_3849_);
lean_ctor_set(v___x_3850_, 1, v___x_3848_);
return v___x_3850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_findRewrites(lean_object* v_hyps_3851_, lean_object* v_moduleRef_3852_, lean_object* v_goal_3853_, lean_object* v_target_3854_, lean_object* v_forbidden_3855_, uint8_t v_side_3856_, uint8_t v_stopAtRfl_3857_, lean_object* v_max_3858_, lean_object* v_leavePercentHeartbeats_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_){
_start:
{
lean_object* v___x_3865_; lean_object* v___x_3866_; 
v___x_3865_ = lean_st_ref_get(v_a_3861_);
lean_inc_ref(v_target_3854_);
v___x_3866_ = l_Lean_Meta_Rewrites_rewriteCandidates(v_hyps_3851_, v_moduleRef_3852_, v_target_3854_, v_forbidden_3855_, v_a_3860_, v_a_3861_, v_a_3862_, v_a_3863_);
if (lean_obj_tag(v___x_3866_) == 0)
{
lean_object* v_a_3867_; lean_object* v___x_3868_; 
v_a_3867_ = lean_ctor_get(v___x_3866_, 0);
lean_inc(v_a_3867_);
lean_dec_ref_known(v___x_3866_, 1);
v___x_3868_ = l_Lean_getMaxHeartbeats___redArg(v_a_3862_);
if (lean_obj_tag(v___x_3868_) == 0)
{
lean_object* v_a_3869_; lean_object* v_mctx_3870_; lean_object* v_minHeartbeats_3872_; lean_object* v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3875_; lean_object* v___y_3876_; lean_object* v___x_3899_; uint8_t v___x_3900_; 
v_a_3869_ = lean_ctor_get(v___x_3868_, 0);
lean_inc(v_a_3869_);
lean_dec_ref_known(v___x_3868_, 1);
v_mctx_3870_ = lean_ctor_get(v___x_3865_, 0);
lean_inc_ref(v_mctx_3870_);
lean_dec(v___x_3865_);
v___x_3899_ = lean_unsigned_to_nat(0u);
v___x_3900_ = lean_nat_dec_eq(v_a_3869_, v___x_3899_);
lean_dec(v_a_3869_);
if (v___x_3900_ == 0)
{
lean_object* v___x_3901_; 
v___x_3901_ = l_Lean_getRemainingHeartbeats___redArg(v_a_3862_);
if (lean_obj_tag(v___x_3901_) == 0)
{
lean_object* v_a_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; 
v_a_3902_ = lean_ctor_get(v___x_3901_, 0);
lean_inc(v_a_3902_);
lean_dec_ref_known(v___x_3901_, 1);
v___x_3903_ = lean_nat_mul(v_leavePercentHeartbeats_3859_, v_a_3902_);
lean_dec(v_a_3902_);
v___x_3904_ = lean_unsigned_to_nat(100u);
v___x_3905_ = lean_nat_div(v___x_3903_, v___x_3904_);
lean_dec(v___x_3903_);
v_minHeartbeats_3872_ = v___x_3905_;
v___y_3873_ = v_a_3860_;
v___y_3874_ = v_a_3861_;
v___y_3875_ = v_a_3862_;
v___y_3876_ = v_a_3863_;
goto v___jp_3871_;
}
else
{
lean_object* v_a_3906_; lean_object* v___x_3908_; uint8_t v_isShared_3909_; uint8_t v_isSharedCheck_3913_; 
lean_dec_ref(v_mctx_3870_);
lean_dec(v_a_3867_);
lean_dec(v_max_3858_);
lean_dec_ref(v_target_3854_);
lean_dec(v_goal_3853_);
v_a_3906_ = lean_ctor_get(v___x_3901_, 0);
v_isSharedCheck_3913_ = !lean_is_exclusive(v___x_3901_);
if (v_isSharedCheck_3913_ == 0)
{
v___x_3908_ = v___x_3901_;
v_isShared_3909_ = v_isSharedCheck_3913_;
goto v_resetjp_3907_;
}
else
{
lean_inc(v_a_3906_);
lean_dec(v___x_3901_);
v___x_3908_ = lean_box(0);
v_isShared_3909_ = v_isSharedCheck_3913_;
goto v_resetjp_3907_;
}
v_resetjp_3907_:
{
lean_object* v___x_3911_; 
if (v_isShared_3909_ == 0)
{
v___x_3911_ = v___x_3908_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3912_; 
v_reuseFailAlloc_3912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3912_, 0, v_a_3906_);
v___x_3911_ = v_reuseFailAlloc_3912_;
goto v_reusejp_3910_;
}
v_reusejp_3910_:
{
return v___x_3911_;
}
}
}
}
else
{
v_minHeartbeats_3872_ = v___x_3899_;
v___y_3873_ = v_a_3860_;
v___y_3874_ = v_a_3861_;
v___y_3875_ = v_a_3862_;
v___y_3876_ = v_a_3863_;
goto v___jp_3871_;
}
v___jp_3871_:
{
lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; 
lean_inc(v_max_3858_);
v___x_3877_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_3877_, 0, v_max_3858_);
lean_ctor_set(v___x_3877_, 1, v_minHeartbeats_3872_);
lean_ctor_set(v___x_3877_, 2, v_goal_3853_);
lean_ctor_set(v___x_3877_, 3, v_target_3854_);
lean_ctor_set(v___x_3877_, 4, v_mctx_3870_);
lean_ctor_set_uint8(v___x_3877_, sizeof(void*)*5, v_stopAtRfl_3857_);
lean_ctor_set_uint8(v___x_3877_, sizeof(void*)*5 + 1, v_side_3856_);
v___x_3878_ = lean_obj_once(&l_Lean_Meta_Rewrites_findRewrites___closed__1, &l_Lean_Meta_Rewrites_findRewrites___closed__1_once, _init_l_Lean_Meta_Rewrites_findRewrites___closed__1);
v___x_3879_ = lean_mk_empty_array_with_capacity(v_max_3858_);
lean_dec(v_max_3858_);
v___x_3880_ = lean_array_to_list(v_a_3867_);
v___x_3881_ = l_Lean_Meta_Rewrites_takeListAux(v___x_3877_, v___x_3878_, v___x_3879_, v___x_3880_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_);
lean_dec(v___x_3880_);
if (lean_obj_tag(v___x_3881_) == 0)
{
lean_object* v_a_3882_; lean_object* v___x_3884_; uint8_t v_isShared_3885_; uint8_t v_isSharedCheck_3890_; 
v_a_3882_ = lean_ctor_get(v___x_3881_, 0);
v_isSharedCheck_3890_ = !lean_is_exclusive(v___x_3881_);
if (v_isSharedCheck_3890_ == 0)
{
v___x_3884_ = v___x_3881_;
v_isShared_3885_ = v_isSharedCheck_3890_;
goto v_resetjp_3883_;
}
else
{
lean_inc(v_a_3882_);
lean_dec(v___x_3881_);
v___x_3884_ = lean_box(0);
v_isShared_3885_ = v_isSharedCheck_3890_;
goto v_resetjp_3883_;
}
v_resetjp_3883_:
{
lean_object* v___x_3886_; lean_object* v___x_3888_; 
v___x_3886_ = lean_array_to_list(v_a_3882_);
if (v_isShared_3885_ == 0)
{
lean_ctor_set(v___x_3884_, 0, v___x_3886_);
v___x_3888_ = v___x_3884_;
goto v_reusejp_3887_;
}
else
{
lean_object* v_reuseFailAlloc_3889_; 
v_reuseFailAlloc_3889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3889_, 0, v___x_3886_);
v___x_3888_ = v_reuseFailAlloc_3889_;
goto v_reusejp_3887_;
}
v_reusejp_3887_:
{
return v___x_3888_;
}
}
}
else
{
lean_object* v_a_3891_; lean_object* v___x_3893_; uint8_t v_isShared_3894_; uint8_t v_isSharedCheck_3898_; 
v_a_3891_ = lean_ctor_get(v___x_3881_, 0);
v_isSharedCheck_3898_ = !lean_is_exclusive(v___x_3881_);
if (v_isSharedCheck_3898_ == 0)
{
v___x_3893_ = v___x_3881_;
v_isShared_3894_ = v_isSharedCheck_3898_;
goto v_resetjp_3892_;
}
else
{
lean_inc(v_a_3891_);
lean_dec(v___x_3881_);
v___x_3893_ = lean_box(0);
v_isShared_3894_ = v_isSharedCheck_3898_;
goto v_resetjp_3892_;
}
v_resetjp_3892_:
{
lean_object* v___x_3896_; 
if (v_isShared_3894_ == 0)
{
v___x_3896_ = v___x_3893_;
goto v_reusejp_3895_;
}
else
{
lean_object* v_reuseFailAlloc_3897_; 
v_reuseFailAlloc_3897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3897_, 0, v_a_3891_);
v___x_3896_ = v_reuseFailAlloc_3897_;
goto v_reusejp_3895_;
}
v_reusejp_3895_:
{
return v___x_3896_;
}
}
}
}
}
else
{
lean_object* v_a_3914_; lean_object* v___x_3916_; uint8_t v_isShared_3917_; uint8_t v_isSharedCheck_3921_; 
lean_dec(v_a_3867_);
lean_dec(v___x_3865_);
lean_dec(v_max_3858_);
lean_dec_ref(v_target_3854_);
lean_dec(v_goal_3853_);
v_a_3914_ = lean_ctor_get(v___x_3868_, 0);
v_isSharedCheck_3921_ = !lean_is_exclusive(v___x_3868_);
if (v_isSharedCheck_3921_ == 0)
{
v___x_3916_ = v___x_3868_;
v_isShared_3917_ = v_isSharedCheck_3921_;
goto v_resetjp_3915_;
}
else
{
lean_inc(v_a_3914_);
lean_dec(v___x_3868_);
v___x_3916_ = lean_box(0);
v_isShared_3917_ = v_isSharedCheck_3921_;
goto v_resetjp_3915_;
}
v_resetjp_3915_:
{
lean_object* v___x_3919_; 
if (v_isShared_3917_ == 0)
{
v___x_3919_ = v___x_3916_;
goto v_reusejp_3918_;
}
else
{
lean_object* v_reuseFailAlloc_3920_; 
v_reuseFailAlloc_3920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3920_, 0, v_a_3914_);
v___x_3919_ = v_reuseFailAlloc_3920_;
goto v_reusejp_3918_;
}
v_reusejp_3918_:
{
return v___x_3919_;
}
}
}
}
else
{
lean_object* v_a_3922_; lean_object* v___x_3924_; uint8_t v_isShared_3925_; uint8_t v_isSharedCheck_3929_; 
lean_dec(v___x_3865_);
lean_dec(v_max_3858_);
lean_dec_ref(v_target_3854_);
lean_dec(v_goal_3853_);
v_a_3922_ = lean_ctor_get(v___x_3866_, 0);
v_isSharedCheck_3929_ = !lean_is_exclusive(v___x_3866_);
if (v_isSharedCheck_3929_ == 0)
{
v___x_3924_ = v___x_3866_;
v_isShared_3925_ = v_isSharedCheck_3929_;
goto v_resetjp_3923_;
}
else
{
lean_inc(v_a_3922_);
lean_dec(v___x_3866_);
v___x_3924_ = lean_box(0);
v_isShared_3925_ = v_isSharedCheck_3929_;
goto v_resetjp_3923_;
}
v_resetjp_3923_:
{
lean_object* v___x_3927_; 
if (v_isShared_3925_ == 0)
{
v___x_3927_ = v___x_3924_;
goto v_reusejp_3926_;
}
else
{
lean_object* v_reuseFailAlloc_3928_; 
v_reuseFailAlloc_3928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3928_, 0, v_a_3922_);
v___x_3927_ = v_reuseFailAlloc_3928_;
goto v_reusejp_3926_;
}
v_reusejp_3926_:
{
return v___x_3927_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_findRewrites___boxed(lean_object* v_hyps_3930_, lean_object* v_moduleRef_3931_, lean_object* v_goal_3932_, lean_object* v_target_3933_, lean_object* v_forbidden_3934_, lean_object* v_side_3935_, lean_object* v_stopAtRfl_3936_, lean_object* v_max_3937_, lean_object* v_leavePercentHeartbeats_3938_, lean_object* v_a_3939_, lean_object* v_a_3940_, lean_object* v_a_3941_, lean_object* v_a_3942_, lean_object* v_a_3943_){
_start:
{
uint8_t v_side_boxed_3944_; uint8_t v_stopAtRfl_boxed_3945_; lean_object* v_res_3946_; 
v_side_boxed_3944_ = lean_unbox(v_side_3935_);
v_stopAtRfl_boxed_3945_ = lean_unbox(v_stopAtRfl_3936_);
v_res_3946_ = l_Lean_Meta_Rewrites_findRewrites(v_hyps_3930_, v_moduleRef_3931_, v_goal_3932_, v_target_3933_, v_forbidden_3934_, v_side_boxed_3944_, v_stopAtRfl_boxed_3945_, v_max_3937_, v_leavePercentHeartbeats_3938_, v_a_3939_, v_a_3940_, v_a_3941_, v_a_3942_);
lean_dec(v_a_3942_);
lean_dec_ref(v_a_3941_);
lean_dec(v_a_3940_);
lean_dec_ref(v_a_3939_);
lean_dec(v_leavePercentHeartbeats_3938_);
lean_dec(v_forbidden_3934_);
return v_res_3946_;
}
}
lean_object* runtime_initialize_Lean_Meta_LazyDiscrTree(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Rewrite(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Refl(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_SolveByElim(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_Heartbeats(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Rewrites(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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

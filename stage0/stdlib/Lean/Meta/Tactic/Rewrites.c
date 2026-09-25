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
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
uint8_t l_Lean_AsyncConstantInfo_isUnsafe(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isMetaprogramming(lean_object*);
lean_object* l_Lean_AsyncConstantInfo_toConstantVal(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_allowCompletion(lean_object*, lean_object*);
uint8_t l_Lean_Linter_isDeprecated(lean_object*, lean_object*);
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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "injEq"};
static const lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "sizeOf_spec"};
static const lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_inj'"};
static const lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__3;
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
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; uint8_t v___x_337_; lean_object* v___x_338_; lean_object* v___x_340_; 
v___x_332_ = lean_unsigned_to_nat(0u);
v___x_333_ = lean_array_fget(v_snd_320_, v___x_332_);
v___x_334_ = lean_unsigned_to_nat(1u);
v___x_335_ = lean_array_fget(v_snd_320_, v___x_334_);
lean_dec(v_snd_320_);
v___x_336_ = lean_mk_empty_array_with_capacity(v___x_330_);
v___x_337_ = 0;
v___x_338_ = lean_box(v___x_337_);
lean_inc(v_name_306_);
if (v_isShared_323_ == 0)
{
lean_ctor_set(v___x_322_, 1, v___x_338_);
lean_ctor_set(v___x_322_, 0, v_name_306_);
v___x_340_ = v___x_322_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_name_306_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v___x_338_);
v___x_340_ = v_reuseFailAlloc_373_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
lean_object* v___x_341_; 
v___x_341_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(v___x_333_, v___x_340_, v___y_309_, v___y_310_, v___y_311_, v___y_312_);
if (lean_obj_tag(v___x_341_) == 0)
{
lean_object* v_a_342_; lean_object* v___x_343_; uint8_t v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v_a_342_ = lean_ctor_get(v___x_341_, 0);
lean_inc(v_a_342_);
lean_dec_ref_known(v___x_341_, 1);
v___x_343_ = lean_array_push(v___x_336_, v_a_342_);
v___x_344_ = 1;
v___x_345_ = lean_box(v___x_344_);
v___x_346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_346_, 0, v_name_306_);
lean_ctor_set(v___x_346_, 1, v___x_345_);
v___x_347_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(v___x_335_, v___x_346_, v___y_309_, v___y_310_, v___y_311_, v___y_312_);
if (lean_obj_tag(v___x_347_) == 0)
{
lean_object* v_a_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_356_; 
v_a_348_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_356_ == 0)
{
v___x_350_ = v___x_347_;
v_isShared_351_ = v_isSharedCheck_356_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_a_348_);
lean_dec(v___x_347_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_356_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_352_; lean_object* v___x_354_; 
v___x_352_ = lean_array_push(v___x_343_, v_a_348_);
if (v_isShared_351_ == 0)
{
lean_ctor_set(v___x_350_, 0, v___x_352_);
v___x_354_ = v___x_350_;
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
lean_dec_ref(v___x_343_);
v_a_357_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_364_ == 0)
{
v___x_359_ = v___x_347_;
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_a_357_);
lean_dec(v___x_347_);
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
lean_dec_ref(v___x_336_);
lean_dec(v___x_335_);
lean_dec(v_name_306_);
v_a_365_ = lean_ctor_get(v___x_341_, 0);
v_isSharedCheck_372_ = !lean_is_exclusive(v___x_341_);
if (v_isSharedCheck_372_ == 0)
{
v___x_367_ = v___x_341_;
v_isShared_368_ = v_isSharedCheck_372_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_a_365_);
lean_dec(v___x_341_);
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
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; uint8_t v___x_382_; lean_object* v___x_383_; lean_object* v___x_385_; 
v___x_377_ = lean_unsigned_to_nat(1u);
v___x_378_ = lean_array_fget(v_snd_320_, v___x_377_);
v___x_379_ = lean_unsigned_to_nat(2u);
v___x_380_ = lean_array_fget(v_snd_320_, v___x_379_);
lean_dec(v_snd_320_);
v___x_381_ = lean_mk_empty_array_with_capacity(v___x_379_);
v___x_382_ = 0;
v___x_383_ = lean_box(v___x_382_);
lean_inc(v_name_306_);
if (v_isShared_323_ == 0)
{
lean_ctor_set(v___x_322_, 1, v___x_383_);
lean_ctor_set(v___x_322_, 0, v_name_306_);
v___x_385_ = v___x_322_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_name_306_);
lean_ctor_set(v_reuseFailAlloc_418_, 1, v___x_383_);
v___x_385_ = v_reuseFailAlloc_418_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
lean_object* v___x_386_; 
v___x_386_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(v___x_378_, v___x_385_, v___y_309_, v___y_310_, v___y_311_, v___y_312_);
if (lean_obj_tag(v___x_386_) == 0)
{
lean_object* v_a_387_; lean_object* v___x_388_; uint8_t v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v_a_387_ = lean_ctor_get(v___x_386_, 0);
lean_inc(v_a_387_);
lean_dec_ref_known(v___x_386_, 1);
v___x_388_ = lean_array_push(v___x_381_, v_a_387_);
v___x_389_ = 1;
v___x_390_ = lean_box(v___x_389_);
v___x_391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_391_, 0, v_name_306_);
lean_ctor_set(v___x_391_, 1, v___x_390_);
v___x_392_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(v___x_380_, v___x_391_, v___y_309_, v___y_310_, v___y_311_, v___y_312_);
if (lean_obj_tag(v___x_392_) == 0)
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_401_; 
v_a_393_ = lean_ctor_get(v___x_392_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_401_ == 0)
{
v___x_395_ = v___x_392_;
v_isShared_396_ = v_isSharedCheck_401_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___x_392_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_401_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_397_; lean_object* v___x_399_; 
v___x_397_ = lean_array_push(v___x_388_, v_a_393_);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 0, v___x_397_);
v___x_399_ = v___x_395_;
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
lean_dec_ref(v___x_388_);
v_a_402_ = lean_ctor_get(v___x_392_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_409_ == 0)
{
v___x_404_ = v___x_392_;
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_a_402_);
lean_dec(v___x_392_);
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
lean_dec_ref(v___x_381_);
lean_dec(v___x_380_);
lean_dec(v_name_306_);
v_a_410_ = lean_ctor_get(v___x_386_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_417_ == 0)
{
v___x_412_ = v___x_386_;
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_a_410_);
lean_dec(v___x_386_);
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
lean_object* v___y_440_; lean_object* v___x_457_; uint8_t v_transparency_458_; uint8_t v___x_459_; 
v___x_457_ = l_Lean_Meta_Context_config(v___y_434_);
v_transparency_458_ = lean_ctor_get_uint8(v___x_457_, 9);
lean_dec_ref(v___x_457_);
v___x_459_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_458_, v___x_430_);
if (v___x_459_ == 0)
{
lean_object* v_keyedConfig_460_; uint8_t v_trackZetaDelta_461_; lean_object* v_zetaDeltaSet_462_; lean_object* v_lctx_463_; lean_object* v_localInstances_464_; lean_object* v_defEqCtx_x3f_465_; lean_object* v_synthPendingDepth_466_; lean_object* v_customCanUnfoldPredicate_x3f_467_; uint8_t v_univApprox_468_; uint8_t v_inTypeClassResolution_469_; uint8_t v_cacheInferType_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_479_; 
v_keyedConfig_460_ = lean_ctor_get(v___y_434_, 0);
v_trackZetaDelta_461_ = lean_ctor_get_uint8(v___y_434_, sizeof(void*)*7);
v_zetaDeltaSet_462_ = lean_ctor_get(v___y_434_, 1);
v_lctx_463_ = lean_ctor_get(v___y_434_, 2);
v_localInstances_464_ = lean_ctor_get(v___y_434_, 3);
v_defEqCtx_x3f_465_ = lean_ctor_get(v___y_434_, 4);
v_synthPendingDepth_466_ = lean_ctor_get(v___y_434_, 5);
v_customCanUnfoldPredicate_x3f_467_ = lean_ctor_get(v___y_434_, 6);
v_univApprox_468_ = lean_ctor_get_uint8(v___y_434_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_469_ = lean_ctor_get_uint8(v___y_434_, sizeof(void*)*7 + 2);
v_cacheInferType_470_ = lean_ctor_get_uint8(v___y_434_, sizeof(void*)*7 + 3);
v_isSharedCheck_479_ = !lean_is_exclusive(v___y_434_);
if (v_isSharedCheck_479_ == 0)
{
v___x_472_ = v___y_434_;
v_isShared_473_ = v_isSharedCheck_479_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_467_);
lean_inc(v_synthPendingDepth_466_);
lean_inc(v_defEqCtx_x3f_465_);
lean_inc(v_localInstances_464_);
lean_inc(v_lctx_463_);
lean_inc(v_zetaDeltaSet_462_);
lean_inc(v_keyedConfig_460_);
lean_dec(v___y_434_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_479_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_474_; lean_object* v___x_476_; 
v___x_474_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_430_, v_keyedConfig_460_);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 0, v___x_474_);
v___x_476_ = v___x_472_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v___x_474_);
lean_ctor_set(v_reuseFailAlloc_478_, 1, v_zetaDeltaSet_462_);
lean_ctor_set(v_reuseFailAlloc_478_, 2, v_lctx_463_);
lean_ctor_set(v_reuseFailAlloc_478_, 3, v_localInstances_464_);
lean_ctor_set(v_reuseFailAlloc_478_, 4, v_defEqCtx_x3f_465_);
lean_ctor_set(v_reuseFailAlloc_478_, 5, v_synthPendingDepth_466_);
lean_ctor_set(v_reuseFailAlloc_478_, 6, v_customCanUnfoldPredicate_x3f_467_);
lean_ctor_set_uint8(v_reuseFailAlloc_478_, sizeof(void*)*7, v_trackZetaDelta_461_);
lean_ctor_set_uint8(v_reuseFailAlloc_478_, sizeof(void*)*7 + 1, v_univApprox_468_);
lean_ctor_set_uint8(v_reuseFailAlloc_478_, sizeof(void*)*7 + 2, v_inTypeClassResolution_469_);
lean_ctor_set_uint8(v_reuseFailAlloc_478_, sizeof(void*)*7 + 3, v_cacheInferType_470_);
v___x_476_ = v_reuseFailAlloc_478_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
lean_object* v___x_477_; 
v___x_477_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg(v_type_431_, v___f_432_, v___x_433_, v___x_433_, v___x_476_, v___y_435_, v___y_436_, v___y_437_);
lean_dec_ref(v___x_476_);
v___y_440_ = v___x_477_;
goto v___jp_439_;
}
}
}
else
{
lean_object* v___x_480_; 
v___x_480_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg(v_type_431_, v___f_432_, v___x_433_, v___x_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
lean_dec_ref(v___y_434_);
v___y_440_ = v___x_480_;
goto v___jp_439_;
}
v___jp_439_:
{
if (lean_obj_tag(v___y_440_) == 0)
{
lean_object* v_a_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_448_; 
v_a_441_ = lean_ctor_get(v___y_440_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v___y_440_);
if (v_isSharedCheck_448_ == 0)
{
v___x_443_ = v___y_440_;
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_a_441_);
lean_dec(v___y_440_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_448_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_446_; 
if (v_isShared_444_ == 0)
{
v___x_446_ = v___x_443_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_a_441_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
else
{
lean_object* v_a_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_456_; 
v_a_449_ = lean_ctor_get(v___y_440_, 0);
v_isSharedCheck_456_ = !lean_is_exclusive(v___y_440_);
if (v_isSharedCheck_456_ == 0)
{
v___x_451_ = v___y_440_;
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_a_449_);
lean_dec(v___y_440_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_454_; 
if (v_isShared_452_ == 0)
{
v___x_454_ = v___x_451_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_a_449_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__1___boxed(lean_object* v___x_481_, lean_object* v_type_482_, lean_object* v___f_483_, lean_object* v___x_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
uint8_t v___x_4629__boxed_490_; uint8_t v___x_4631__boxed_491_; lean_object* v_res_492_; 
v___x_4629__boxed_490_ = lean_unbox(v___x_481_);
v___x_4631__boxed_491_ = lean_unbox(v___x_484_);
v_res_492_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__1(v___x_4629__boxed_490_, v_type_482_, v___f_483_, v___x_4631__boxed_491_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec(v___y_486_);
return v_res_492_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__3(void){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__2));
v___x_497_ = lean_string_utf8_byte_size(v___x_496_);
return v___x_497_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__5(void){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__4));
v___x_500_ = lean_string_utf8_byte_size(v___x_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport(lean_object* v_name_501_, lean_object* v_c_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_){
_start:
{
uint8_t v___x_508_; 
lean_inc_ref(v_c_502_);
v___x_508_ = l_Lean_AsyncConstantInfo_isUnsafe(v_c_502_);
if (v___x_508_ == 0)
{
lean_object* v___f_509_; lean_object* v___y_511_; lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v___y_514_; lean_object* v___x_525_; lean_object* v_env_529_; uint8_t v___x_530_; 
lean_inc_n(v_name_501_, 2);
v___f_509_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___boxed), 8, 1);
lean_closure_set(v___f_509_, 0, v_name_501_);
v___x_525_ = lean_st_ref_get(v_a_506_);
v_env_529_ = lean_ctor_get(v___x_525_, 0);
lean_inc_ref(v_env_529_);
lean_dec(v___x_525_);
v___x_530_ = l_Lean_Meta_allowCompletion(v_env_529_, v_name_501_);
if (v___x_530_ == 0)
{
lean_dec_ref(v___f_509_);
lean_dec_ref(v_c_502_);
lean_dec(v_name_501_);
goto v___jp_526_;
}
else
{
if (v___x_508_ == 0)
{
lean_object* v___x_531_; uint8_t v___y_533_; lean_object* v_env_536_; uint8_t v___x_537_; 
v___x_531_ = lean_st_ref_get(v_a_506_);
v_env_536_ = lean_ctor_get(v___x_531_, 0);
lean_inc_ref(v_env_536_);
lean_dec(v___x_531_);
lean_inc(v_name_501_);
v___x_537_ = l_Lean_Linter_isDeprecated(v_env_536_, v_name_501_);
if (v___x_537_ == 0)
{
if (lean_obj_tag(v_name_501_) == 1)
{
lean_object* v_str_538_; lean_object* v___x_539_; uint8_t v___x_540_; uint8_t v___y_542_; lean_object* v___x_543_; uint8_t v___x_544_; uint8_t v___y_546_; uint8_t v___y_548_; uint8_t v___y_549_; uint8_t v___y_551_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; uint8_t v___x_562_; 
v_str_538_ = lean_ctor_get(v_name_501_, 1);
v___x_539_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__0));
v___x_540_ = lean_string_dec_eq(v_str_538_, v___x_539_);
v___x_543_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__1));
v___x_544_ = lean_string_dec_eq(v_str_538_, v___x_543_);
v___x_559_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__4));
v___x_560_ = lean_string_utf8_byte_size(v_str_538_);
v___x_561_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__5, &l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__5_once, _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__5);
v___x_562_ = lean_nat_dec_le(v___x_561_, v___x_560_);
if (v___x_562_ == 0)
{
v___y_551_ = v___x_562_;
goto v___jp_550_;
}
else
{
lean_object* v___x_563_; lean_object* v___x_564_; uint8_t v___x_565_; 
v___x_563_ = lean_unsigned_to_nat(0u);
v___x_564_ = lean_nat_sub(v___x_560_, v___x_561_);
v___x_565_ = lean_string_memcmp(v_str_538_, v___x_559_, v___x_564_, v___x_563_, v___x_561_);
lean_dec(v___x_564_);
v___y_551_ = v___x_565_;
goto v___jp_550_;
}
v___jp_541_:
{
if (v___x_540_ == 0)
{
v___y_533_ = v___y_542_;
goto v___jp_532_;
}
else
{
v___y_533_ = v___x_540_;
goto v___jp_532_;
}
}
v___jp_545_:
{
if (v___x_544_ == 0)
{
v___y_542_ = v___y_546_;
goto v___jp_541_;
}
else
{
v___y_542_ = v___x_544_;
goto v___jp_541_;
}
}
v___jp_547_:
{
if (v___y_548_ == 0)
{
v___y_546_ = v___y_549_;
goto v___jp_545_;
}
else
{
v___y_546_ = v___y_548_;
goto v___jp_545_;
}
}
v___jp_550_:
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; uint8_t v___x_555_; 
v___x_552_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__2));
v___x_553_ = lean_string_utf8_byte_size(v_str_538_);
v___x_554_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__3, &l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__3_once, _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__3);
v___x_555_ = lean_nat_dec_le(v___x_554_, v___x_553_);
if (v___x_555_ == 0)
{
v___y_548_ = v___y_551_;
v___y_549_ = v___x_555_;
goto v___jp_547_;
}
else
{
lean_object* v___x_556_; lean_object* v___x_557_; uint8_t v___x_558_; 
v___x_556_ = lean_unsigned_to_nat(0u);
v___x_557_ = lean_nat_sub(v___x_553_, v___x_554_);
v___x_558_ = lean_string_memcmp(v_str_538_, v___x_552_, v___x_557_, v___x_556_, v___x_554_);
lean_dec(v___x_557_);
v___y_548_ = v___y_551_;
v___y_549_ = v___x_558_;
goto v___jp_547_;
}
}
}
else
{
v___y_511_ = v_a_503_;
v___y_512_ = v_a_504_;
v___y_513_ = v_a_505_;
v___y_514_ = v_a_506_;
goto v___jp_510_;
}
}
else
{
lean_object* v___x_566_; lean_object* v___x_567_; 
lean_dec_ref(v___f_509_);
lean_dec_ref(v_c_502_);
lean_dec(v_name_501_);
v___x_566_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0));
v___x_567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
return v___x_567_;
}
v___jp_532_:
{
if (v___y_533_ == 0)
{
v___y_511_ = v_a_503_;
v___y_512_ = v_a_504_;
v___y_513_ = v_a_505_;
v___y_514_ = v_a_506_;
goto v___jp_510_;
}
else
{
lean_object* v___x_534_; lean_object* v___x_535_; 
lean_dec_ref(v___f_509_);
lean_dec_ref(v_c_502_);
lean_dec(v_name_501_);
v___x_534_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0));
v___x_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
return v___x_535_;
}
}
}
else
{
lean_dec_ref(v___f_509_);
lean_dec_ref(v_c_502_);
lean_dec(v_name_501_);
goto v___jp_526_;
}
}
v___jp_510_:
{
uint8_t v___x_515_; 
v___x_515_ = l_Lean_Name_isMetaprogramming(v_name_501_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; lean_object* v_type_517_; uint8_t v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___f_521_; lean_object* v___x_522_; 
v___x_516_ = l_Lean_AsyncConstantInfo_toConstantVal(v_c_502_);
v_type_517_ = lean_ctor_get(v___x_516_, 2);
lean_inc_ref(v_type_517_);
lean_dec_ref(v___x_516_);
v___x_518_ = 2;
v___x_519_ = lean_box(v___x_518_);
v___x_520_ = lean_box(v___x_515_);
v___f_521_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__1___boxed), 9, 4);
lean_closure_set(v___f_521_, 0, v___x_519_);
lean_closure_set(v___f_521_, 1, v_type_517_);
lean_closure_set(v___f_521_, 2, v___f_509_);
lean_closure_set(v___f_521_, 3, v___x_520_);
v___x_522_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1___redArg(v___f_521_, v___x_515_, v___y_511_, v___y_512_, v___y_513_, v___y_514_);
return v___x_522_;
}
else
{
lean_object* v___x_523_; lean_object* v___x_524_; 
lean_dec_ref(v___f_509_);
lean_dec_ref(v_c_502_);
v___x_523_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0));
v___x_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_524_, 0, v___x_523_);
return v___x_524_;
}
}
v___jp_526_:
{
lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_527_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0));
v___x_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
return v___x_528_;
}
}
else
{
lean_object* v___x_568_; lean_object* v___x_569_; 
lean_dec_ref(v_c_502_);
lean_dec(v_name_501_);
v___x_568_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0));
v___x_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
return v___x_569_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___boxed(lean_object* v_name_570_, lean_object* v_c_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport(v_name_570_, v_c_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_);
lean_dec(v_a_575_);
lean_dec_ref(v_a_574_);
lean_dec(v_a_573_);
lean_dec_ref(v_a_572_);
return v_res_577_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_Rewrites_localHypotheses_spec__0(lean_object* v_a_578_, lean_object* v_x_579_){
_start:
{
if (lean_obj_tag(v_x_579_) == 0)
{
uint8_t v___x_580_; 
v___x_580_ = 0;
return v___x_580_;
}
else
{
lean_object* v_head_581_; lean_object* v_tail_582_; uint8_t v___x_583_; 
v_head_581_ = lean_ctor_get(v_x_579_, 0);
v_tail_582_ = lean_ctor_get(v_x_579_, 1);
v___x_583_ = l_Lean_instBEqFVarId_beq(v_a_578_, v_head_581_);
if (v___x_583_ == 0)
{
v_x_579_ = v_tail_582_;
goto _start;
}
else
{
return v___x_583_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_Rewrites_localHypotheses_spec__0___boxed(lean_object* v_a_585_, lean_object* v_x_586_){
_start:
{
uint8_t v_res_587_; lean_object* v_r_588_; 
v_res_587_ = l_List_elem___at___00Lean_Meta_Rewrites_localHypotheses_spec__0(v_a_585_, v_x_586_);
lean_dec(v_x_586_);
lean_dec(v_a_585_);
v_r_588_ = lean_box(v_res_587_);
return v_r_588_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_localHypotheses_spec__2(lean_object* v_except_589_, lean_object* v_as_590_, size_t v_sz_591_, size_t v_i_592_, lean_object* v_b_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
lean_object* v_a_600_; uint8_t v___x_604_; 
v___x_604_ = lean_usize_dec_lt(v_i_592_, v_sz_591_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; 
v___x_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_605_, 0, v_b_593_);
return v___x_605_;
}
else
{
lean_object* v_a_606_; lean_object* v___x_607_; uint8_t v___x_608_; 
v_a_606_ = lean_array_uget_borrowed(v_as_590_, v_i_592_);
v___x_607_ = l_Lean_Expr_fvarId_x21(v_a_606_);
v___x_608_ = l_List_elem___at___00Lean_Meta_Rewrites_localHypotheses_spec__0(v___x_607_, v_except_589_);
lean_dec(v___x_607_);
if (v___x_608_ == 0)
{
lean_object* v___x_609_; 
lean_inc(v___y_597_);
lean_inc_ref(v___y_596_);
lean_inc(v___y_595_);
lean_inc_ref(v___y_594_);
lean_inc(v_a_606_);
v___x_609_ = lean_infer_type(v_a_606_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
if (lean_obj_tag(v___x_609_) == 0)
{
lean_object* v_a_610_; lean_object* v___x_611_; uint8_t v___x_612_; lean_object* v___x_613_; 
v_a_610_ = lean_ctor_get(v___x_609_, 0);
lean_inc(v_a_610_);
lean_dec_ref_known(v___x_609_, 1);
v___x_611_ = lean_box(0);
v___x_612_ = 0;
v___x_613_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_610_, v___x_611_, v___x_612_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
if (lean_obj_tag(v___x_613_) == 0)
{
lean_object* v_a_614_; lean_object* v_snd_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_686_; 
v_a_614_ = lean_ctor_get(v___x_613_, 0);
lean_inc(v_a_614_);
lean_dec_ref_known(v___x_613_, 1);
v_snd_615_ = lean_ctor_get(v_a_614_, 1);
v_isSharedCheck_686_ = !lean_is_exclusive(v_a_614_);
if (v_isSharedCheck_686_ == 0)
{
lean_object* v_unused_687_; 
v_unused_687_ = lean_ctor_get(v_a_614_, 0);
lean_dec(v_unused_687_);
v___x_617_ = v_a_614_;
v_isShared_618_ = v_isSharedCheck_686_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_snd_615_);
lean_dec(v_a_614_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_686_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v_snd_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_684_; 
v_snd_619_ = lean_ctor_get(v_snd_615_, 1);
v_isSharedCheck_684_ = !lean_is_exclusive(v_snd_615_);
if (v_isSharedCheck_684_ == 0)
{
lean_object* v_unused_685_; 
v_unused_685_ = lean_ctor_get(v_snd_615_, 0);
lean_dec(v_unused_685_);
v___x_621_ = v_snd_615_;
v_isShared_622_ = v_isSharedCheck_684_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_snd_619_);
lean_dec(v_snd_615_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_684_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_623_; 
v___x_623_ = l_Lean_Meta_whnfR(v_snd_619_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
if (lean_obj_tag(v___x_623_) == 0)
{
lean_object* v_a_624_; lean_object* v___x_625_; lean_object* v_fst_626_; 
v_a_624_ = lean_ctor_get(v___x_623_, 0);
lean_inc(v_a_624_);
lean_dec_ref_known(v___x_623_, 1);
v___x_625_ = l_Lean_Expr_getAppFnArgs(v_a_624_);
v_fst_626_ = lean_ctor_get(v___x_625_, 0);
lean_inc(v_fst_626_);
if (lean_obj_tag(v_fst_626_) == 1)
{
lean_object* v_pre_627_; 
v_pre_627_ = lean_ctor_get(v_fst_626_, 0);
if (lean_obj_tag(v_pre_627_) == 0)
{
lean_object* v_snd_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_674_; 
v_snd_628_ = lean_ctor_get(v___x_625_, 1);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_625_);
if (v_isSharedCheck_674_ == 0)
{
lean_object* v_unused_675_; 
v_unused_675_ = lean_ctor_get(v___x_625_, 0);
lean_dec(v_unused_675_);
v___x_630_ = v___x_625_;
v_isShared_631_ = v_isSharedCheck_674_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_snd_628_);
lean_dec(v___x_625_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_674_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v_str_632_; lean_object* v___x_633_; uint8_t v___x_634_; 
v_str_632_ = lean_ctor_get(v_fst_626_, 1);
lean_inc_ref(v_str_632_);
lean_dec_ref_known(v_fst_626_, 2);
v___x_633_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__1));
v___x_634_ = lean_string_dec_eq(v_str_632_, v___x_633_);
if (v___x_634_ == 0)
{
lean_object* v___x_635_; uint8_t v___x_636_; 
v___x_635_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__2));
v___x_636_ = lean_string_dec_eq(v_str_632_, v___x_635_);
lean_dec_ref(v_str_632_);
if (v___x_636_ == 0)
{
lean_del_object(v___x_630_);
lean_dec(v_snd_628_);
lean_del_object(v___x_621_);
lean_del_object(v___x_617_);
v_a_600_ = v_b_593_;
goto v___jp_599_;
}
else
{
lean_object* v___x_637_; lean_object* v___x_638_; uint8_t v___x_639_; 
v___x_637_ = lean_array_get_size(v_snd_628_);
lean_dec(v_snd_628_);
v___x_638_ = lean_unsigned_to_nat(2u);
v___x_639_ = lean_nat_dec_eq(v___x_637_, v___x_638_);
if (v___x_639_ == 0)
{
lean_del_object(v___x_630_);
lean_del_object(v___x_621_);
lean_del_object(v___x_617_);
v_a_600_ = v_b_593_;
goto v___jp_599_;
}
else
{
lean_object* v___x_640_; lean_object* v___x_642_; 
v___x_640_ = lean_box(v___x_608_);
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 1, v___x_638_);
lean_ctor_set(v___x_630_, 0, v___x_640_);
v___x_642_ = v___x_630_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v___x_640_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v___x_638_);
v___x_642_ = v_reuseFailAlloc_654_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
lean_object* v___x_644_; 
lean_inc(v_a_606_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 1, v___x_642_);
lean_ctor_set(v___x_621_, 0, v_a_606_);
v___x_644_ = v___x_621_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_a_606_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v___x_642_);
v___x_644_ = v_reuseFailAlloc_653_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_649_; 
v___x_645_ = lean_array_push(v_b_593_, v___x_644_);
v___x_646_ = lean_unsigned_to_nat(1u);
v___x_647_ = lean_box(v___x_604_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 1, v___x_646_);
lean_ctor_set(v___x_617_, 0, v___x_647_);
v___x_649_ = v___x_617_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_647_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v___x_646_);
v___x_649_ = v_reuseFailAlloc_652_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
lean_object* v___x_650_; lean_object* v___x_651_; 
lean_inc(v_a_606_);
v___x_650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_650_, 0, v_a_606_);
lean_ctor_set(v___x_650_, 1, v___x_649_);
v___x_651_ = lean_array_push(v___x_645_, v___x_650_);
v_a_600_ = v___x_651_;
goto v___jp_599_;
}
}
}
}
}
}
else
{
lean_object* v___x_655_; lean_object* v___x_656_; uint8_t v___x_657_; 
lean_dec_ref(v_str_632_);
v___x_655_ = lean_array_get_size(v_snd_628_);
lean_dec(v_snd_628_);
v___x_656_ = lean_unsigned_to_nat(3u);
v___x_657_ = lean_nat_dec_eq(v___x_655_, v___x_656_);
if (v___x_657_ == 0)
{
lean_del_object(v___x_630_);
lean_del_object(v___x_621_);
lean_del_object(v___x_617_);
v_a_600_ = v_b_593_;
goto v___jp_599_;
}
else
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_661_; 
v___x_658_ = lean_unsigned_to_nat(2u);
v___x_659_ = lean_box(v___x_608_);
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 1, v___x_658_);
lean_ctor_set(v___x_630_, 0, v___x_659_);
v___x_661_ = v___x_630_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v___x_659_);
lean_ctor_set(v_reuseFailAlloc_673_, 1, v___x_658_);
v___x_661_ = v_reuseFailAlloc_673_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
lean_object* v___x_663_; 
lean_inc(v_a_606_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 1, v___x_661_);
lean_ctor_set(v___x_621_, 0, v_a_606_);
v___x_663_ = v___x_621_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_a_606_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v___x_661_);
v___x_663_ = v_reuseFailAlloc_672_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_668_; 
v___x_664_ = lean_array_push(v_b_593_, v___x_663_);
v___x_665_ = lean_unsigned_to_nat(1u);
v___x_666_ = lean_box(v___x_604_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 1, v___x_665_);
lean_ctor_set(v___x_617_, 0, v___x_666_);
v___x_668_ = v___x_617_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v___x_666_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v___x_665_);
v___x_668_ = v_reuseFailAlloc_671_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
lean_object* v___x_669_; lean_object* v___x_670_; 
lean_inc(v_a_606_);
v___x_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_669_, 0, v_a_606_);
lean_ctor_set(v___x_669_, 1, v___x_668_);
v___x_670_ = lean_array_push(v___x_664_, v___x_669_);
v_a_600_ = v___x_670_;
goto v___jp_599_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_fst_626_, 2);
lean_dec_ref(v___x_625_);
lean_del_object(v___x_621_);
lean_del_object(v___x_617_);
v_a_600_ = v_b_593_;
goto v___jp_599_;
}
}
else
{
lean_dec(v_fst_626_);
lean_dec_ref(v___x_625_);
lean_del_object(v___x_621_);
lean_del_object(v___x_617_);
v_a_600_ = v_b_593_;
goto v___jp_599_;
}
}
else
{
lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_683_; 
lean_del_object(v___x_621_);
lean_del_object(v___x_617_);
lean_dec_ref(v_b_593_);
v_a_676_ = lean_ctor_get(v___x_623_, 0);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_683_ == 0)
{
v___x_678_ = v___x_623_;
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_dec(v___x_623_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_681_; 
if (v_isShared_679_ == 0)
{
v___x_681_ = v___x_678_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_a_676_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
}
}
}
else
{
lean_object* v_a_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_695_; 
lean_dec_ref(v_b_593_);
v_a_688_ = lean_ctor_get(v___x_613_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_613_);
if (v_isSharedCheck_695_ == 0)
{
v___x_690_ = v___x_613_;
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_a_688_);
lean_dec(v___x_613_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_693_; 
if (v_isShared_691_ == 0)
{
v___x_693_ = v___x_690_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_a_688_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
}
else
{
lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_703_; 
lean_dec_ref(v_b_593_);
v_a_696_ = lean_ctor_get(v___x_609_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_703_ == 0)
{
v___x_698_ = v___x_609_;
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_609_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_701_; 
if (v_isShared_699_ == 0)
{
v___x_701_ = v___x_698_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_a_696_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
}
else
{
v_a_600_ = v_b_593_;
goto v___jp_599_;
}
}
v___jp_599_:
{
size_t v___x_601_; size_t v___x_602_; 
v___x_601_ = ((size_t)1ULL);
v___x_602_ = lean_usize_add(v_i_592_, v___x_601_);
v_i_592_ = v___x_602_;
v_b_593_ = v_a_600_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_localHypotheses_spec__2___boxed(lean_object* v_except_704_, lean_object* v_as_705_, lean_object* v_sz_706_, lean_object* v_i_707_, lean_object* v_b_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_){
_start:
{
size_t v_sz_boxed_714_; size_t v_i_boxed_715_; lean_object* v_res_716_; 
v_sz_boxed_714_ = lean_unbox_usize(v_sz_706_);
lean_dec(v_sz_706_);
v_i_boxed_715_ = lean_unbox_usize(v_i_707_);
lean_dec(v_i_707_);
v_res_716_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_localHypotheses_spec__2(v_except_704_, v_as_705_, v_sz_boxed_714_, v_i_boxed_715_, v_b_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
lean_dec(v___y_712_);
lean_dec_ref(v___y_711_);
lean_dec(v___y_710_);
lean_dec_ref(v___y_709_);
lean_dec_ref(v_as_705_);
lean_dec(v_except_704_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(lean_object* v_as_717_, size_t v_sz_718_, size_t v_i_719_, lean_object* v_b_720_){
_start:
{
uint8_t v___x_722_; 
v___x_722_ = lean_usize_dec_lt(v_i_719_, v_sz_718_);
if (v___x_722_ == 0)
{
lean_object* v___x_723_; 
v___x_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_723_, 0, v_b_720_);
return v___x_723_;
}
else
{
lean_object* v_snd_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_742_; 
v_snd_724_ = lean_ctor_get(v_b_720_, 1);
v_isSharedCheck_742_ = !lean_is_exclusive(v_b_720_);
if (v_isSharedCheck_742_ == 0)
{
lean_object* v_unused_743_; 
v_unused_743_ = lean_ctor_get(v_b_720_, 0);
lean_dec(v_unused_743_);
v___x_726_ = v_b_720_;
v_isShared_727_ = v_isSharedCheck_742_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_snd_724_);
lean_dec(v_b_720_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_742_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_728_; lean_object* v_a_730_; lean_object* v_a_737_; 
v___x_728_ = lean_box(0);
v_a_737_ = lean_array_uget_borrowed(v_as_717_, v_i_719_);
if (lean_obj_tag(v_a_737_) == 0)
{
v_a_730_ = v_snd_724_;
goto v___jp_729_;
}
else
{
lean_object* v_val_738_; uint8_t v___x_739_; 
v_val_738_ = lean_ctor_get(v_a_737_, 0);
v___x_739_ = l_Lean_LocalDecl_isImplementationDetail(v_val_738_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; lean_object* v___x_741_; 
lean_inc(v_val_738_);
v___x_740_ = l_Lean_LocalDecl_toExpr(v_val_738_);
v___x_741_ = lean_array_push(v_snd_724_, v___x_740_);
v_a_730_ = v___x_741_;
goto v___jp_729_;
}
else
{
v_a_730_ = v_snd_724_;
goto v___jp_729_;
}
}
v___jp_729_:
{
lean_object* v___x_732_; 
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 1, v_a_730_);
lean_ctor_set(v___x_726_, 0, v___x_728_);
v___x_732_ = v___x_726_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v___x_728_);
lean_ctor_set(v_reuseFailAlloc_736_, 1, v_a_730_);
v___x_732_ = v_reuseFailAlloc_736_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
size_t v___x_733_; size_t v___x_734_; 
v___x_733_ = ((size_t)1ULL);
v___x_734_ = lean_usize_add(v_i_719_, v___x_733_);
v_i_719_ = v___x_734_;
v_b_720_ = v___x_732_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___redArg___boxed(lean_object* v_as_744_, lean_object* v_sz_745_, lean_object* v_i_746_, lean_object* v_b_747_, lean_object* v___y_748_){
_start:
{
size_t v_sz_boxed_749_; size_t v_i_boxed_750_; lean_object* v_res_751_; 
v_sz_boxed_749_ = lean_unbox_usize(v_sz_745_);
lean_dec(v_sz_745_);
v_i_boxed_750_ = lean_unbox_usize(v_i_746_);
lean_dec(v_i_746_);
v_res_751_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(v_as_744_, v_sz_boxed_749_, v_i_boxed_750_, v_b_747_);
lean_dec_ref(v_as_744_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5(lean_object* v_as_752_, size_t v_sz_753_, size_t v_i_754_, lean_object* v_b_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_){
_start:
{
uint8_t v___x_761_; 
v___x_761_ = lean_usize_dec_lt(v_i_754_, v_sz_753_);
if (v___x_761_ == 0)
{
lean_object* v___x_762_; 
v___x_762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_762_, 0, v_b_755_);
return v___x_762_;
}
else
{
lean_object* v_snd_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_781_; 
v_snd_763_ = lean_ctor_get(v_b_755_, 1);
v_isSharedCheck_781_ = !lean_is_exclusive(v_b_755_);
if (v_isSharedCheck_781_ == 0)
{
lean_object* v_unused_782_; 
v_unused_782_ = lean_ctor_get(v_b_755_, 0);
lean_dec(v_unused_782_);
v___x_765_ = v_b_755_;
v_isShared_766_ = v_isSharedCheck_781_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_snd_763_);
lean_dec(v_b_755_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_781_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_767_; lean_object* v_a_769_; lean_object* v_a_776_; 
v___x_767_ = lean_box(0);
v_a_776_ = lean_array_uget_borrowed(v_as_752_, v_i_754_);
if (lean_obj_tag(v_a_776_) == 0)
{
v_a_769_ = v_snd_763_;
goto v___jp_768_;
}
else
{
lean_object* v_val_777_; uint8_t v___x_778_; 
v_val_777_ = lean_ctor_get(v_a_776_, 0);
v___x_778_ = l_Lean_LocalDecl_isImplementationDetail(v_val_777_);
if (v___x_778_ == 0)
{
lean_object* v___x_779_; lean_object* v___x_780_; 
lean_inc(v_val_777_);
v___x_779_ = l_Lean_LocalDecl_toExpr(v_val_777_);
v___x_780_ = lean_array_push(v_snd_763_, v___x_779_);
v_a_769_ = v___x_780_;
goto v___jp_768_;
}
else
{
v_a_769_ = v_snd_763_;
goto v___jp_768_;
}
}
v___jp_768_:
{
lean_object* v___x_771_; 
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 1, v_a_769_);
lean_ctor_set(v___x_765_, 0, v___x_767_);
v___x_771_ = v___x_765_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v___x_767_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v_a_769_);
v___x_771_ = v_reuseFailAlloc_775_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
size_t v___x_772_; size_t v___x_773_; lean_object* v___x_774_; 
v___x_772_ = ((size_t)1ULL);
v___x_773_ = lean_usize_add(v_i_754_, v___x_772_);
v___x_774_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(v_as_752_, v_sz_753_, v___x_773_, v___x_771_);
return v___x_774_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5___boxed(lean_object* v_as_783_, lean_object* v_sz_784_, lean_object* v_i_785_, lean_object* v_b_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
size_t v_sz_boxed_792_; size_t v_i_boxed_793_; lean_object* v_res_794_; 
v_sz_boxed_792_ = lean_unbox_usize(v_sz_784_);
lean_dec(v_sz_784_);
v_i_boxed_793_ = lean_unbox_usize(v_i_785_);
lean_dec(v_i_785_);
v_res_794_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5(v_as_783_, v_sz_boxed_792_, v_i_boxed_793_, v_b_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
lean_dec_ref(v_as_783_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2(lean_object* v_init_795_, lean_object* v_n_796_, lean_object* v_b_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_){
_start:
{
if (lean_obj_tag(v_n_796_) == 0)
{
lean_object* v_cs_803_; lean_object* v___x_804_; lean_object* v___x_805_; size_t v_sz_806_; size_t v___x_807_; lean_object* v___x_808_; 
v_cs_803_ = lean_ctor_get(v_n_796_, 0);
v___x_804_ = lean_box(0);
v___x_805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_805_, 0, v___x_804_);
lean_ctor_set(v___x_805_, 1, v_b_797_);
v_sz_806_ = lean_array_size(v_cs_803_);
v___x_807_ = ((size_t)0ULL);
v___x_808_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__4(v_init_795_, v_cs_803_, v_sz_806_, v___x_807_, v___x_805_, v___y_798_, v___y_799_, v___y_800_, v___y_801_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_823_; 
v_a_809_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_823_ == 0)
{
v___x_811_ = v___x_808_;
v_isShared_812_ = v_isSharedCheck_823_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v___x_808_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_823_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v_fst_813_; 
v_fst_813_ = lean_ctor_get(v_a_809_, 0);
if (lean_obj_tag(v_fst_813_) == 0)
{
lean_object* v_snd_814_; lean_object* v___x_815_; lean_object* v___x_817_; 
v_snd_814_ = lean_ctor_get(v_a_809_, 1);
lean_inc(v_snd_814_);
lean_dec(v_a_809_);
v___x_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_815_, 0, v_snd_814_);
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 0, v___x_815_);
v___x_817_ = v___x_811_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_815_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
else
{
lean_object* v_val_819_; lean_object* v___x_821_; 
lean_inc_ref(v_fst_813_);
lean_dec(v_a_809_);
v_val_819_ = lean_ctor_get(v_fst_813_, 0);
lean_inc(v_val_819_);
lean_dec_ref_known(v_fst_813_, 1);
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 0, v_val_819_);
v___x_821_ = v___x_811_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_val_819_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
}
else
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_831_; 
v_a_824_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_831_ == 0)
{
v___x_826_ = v___x_808_;
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___x_808_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_829_; 
if (v_isShared_827_ == 0)
{
v___x_829_ = v___x_826_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_a_824_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
}
else
{
lean_object* v_vs_832_; lean_object* v___x_833_; lean_object* v___x_834_; size_t v_sz_835_; size_t v___x_836_; lean_object* v___x_837_; 
v_vs_832_ = lean_ctor_get(v_n_796_, 0);
v___x_833_ = lean_box(0);
v___x_834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_834_, 0, v___x_833_);
lean_ctor_set(v___x_834_, 1, v_b_797_);
v_sz_835_ = lean_array_size(v_vs_832_);
v___x_836_ = ((size_t)0ULL);
v___x_837_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5(v_vs_832_, v_sz_835_, v___x_836_, v___x_834_, v___y_798_, v___y_799_, v___y_800_, v___y_801_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v_a_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_852_; 
v_a_838_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_852_ == 0)
{
v___x_840_ = v___x_837_;
v_isShared_841_ = v_isSharedCheck_852_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_a_838_);
lean_dec(v___x_837_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_852_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v_fst_842_; 
v_fst_842_ = lean_ctor_get(v_a_838_, 0);
if (lean_obj_tag(v_fst_842_) == 0)
{
lean_object* v_snd_843_; lean_object* v___x_844_; lean_object* v___x_846_; 
v_snd_843_ = lean_ctor_get(v_a_838_, 1);
lean_inc(v_snd_843_);
lean_dec(v_a_838_);
v___x_844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_844_, 0, v_snd_843_);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 0, v___x_844_);
v___x_846_ = v___x_840_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v___x_844_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
else
{
lean_object* v_val_848_; lean_object* v___x_850_; 
lean_inc_ref(v_fst_842_);
lean_dec(v_a_838_);
v_val_848_ = lean_ctor_get(v_fst_842_, 0);
lean_inc(v_val_848_);
lean_dec_ref_known(v_fst_842_, 1);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 0, v_val_848_);
v___x_850_ = v___x_840_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_val_848_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
}
else
{
lean_object* v_a_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_860_; 
v_a_853_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_860_ == 0)
{
v___x_855_ = v___x_837_;
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_a_853_);
lean_dec(v___x_837_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_858_; 
if (v_isShared_856_ == 0)
{
v___x_858_ = v___x_855_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_a_853_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__4(lean_object* v_init_861_, lean_object* v_as_862_, size_t v_sz_863_, size_t v_i_864_, lean_object* v_b_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
uint8_t v___x_871_; 
v___x_871_ = lean_usize_dec_lt(v_i_864_, v_sz_863_);
if (v___x_871_ == 0)
{
lean_object* v___x_872_; 
v___x_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_872_, 0, v_b_865_);
return v___x_872_;
}
else
{
lean_object* v_snd_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_907_; 
v_snd_873_ = lean_ctor_get(v_b_865_, 1);
v_isSharedCheck_907_ = !lean_is_exclusive(v_b_865_);
if (v_isSharedCheck_907_ == 0)
{
lean_object* v_unused_908_; 
v_unused_908_ = lean_ctor_get(v_b_865_, 0);
lean_dec(v_unused_908_);
v___x_875_ = v_b_865_;
v_isShared_876_ = v_isSharedCheck_907_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_snd_873_);
lean_dec(v_b_865_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_907_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_877_; lean_object* v_a_878_; lean_object* v___x_879_; 
v___x_877_ = lean_box(0);
v_a_878_ = lean_array_uget_borrowed(v_as_862_, v_i_864_);
lean_inc(v_snd_873_);
v___x_879_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2(v_init_861_, v_a_878_, v_snd_873_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
if (lean_obj_tag(v___x_879_) == 0)
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_898_; 
v_a_880_ = lean_ctor_get(v___x_879_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_898_ == 0)
{
v___x_882_ = v___x_879_;
v_isShared_883_ = v_isSharedCheck_898_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_879_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_898_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
if (lean_obj_tag(v_a_880_) == 0)
{
lean_object* v___x_884_; lean_object* v___x_886_; 
v___x_884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_884_, 0, v_a_880_);
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 0, v___x_884_);
v___x_886_ = v___x_875_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_884_);
lean_ctor_set(v_reuseFailAlloc_890_, 1, v_snd_873_);
v___x_886_ = v_reuseFailAlloc_890_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
lean_object* v___x_888_; 
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 0, v___x_886_);
v___x_888_ = v___x_882_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_886_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
else
{
lean_object* v_a_891_; lean_object* v___x_893_; 
lean_del_object(v___x_882_);
lean_dec(v_snd_873_);
v_a_891_ = lean_ctor_get(v_a_880_, 0);
lean_inc(v_a_891_);
lean_dec_ref_known(v_a_880_, 1);
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 1, v_a_891_);
lean_ctor_set(v___x_875_, 0, v___x_877_);
v___x_893_ = v___x_875_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v___x_877_);
lean_ctor_set(v_reuseFailAlloc_897_, 1, v_a_891_);
v___x_893_ = v_reuseFailAlloc_897_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
size_t v___x_894_; size_t v___x_895_; 
v___x_894_ = ((size_t)1ULL);
v___x_895_ = lean_usize_add(v_i_864_, v___x_894_);
v_i_864_ = v___x_895_;
v_b_865_ = v___x_893_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_906_; 
lean_del_object(v___x_875_);
lean_dec(v_snd_873_);
v_a_899_ = lean_ctor_get(v___x_879_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_906_ == 0)
{
v___x_901_ = v___x_879_;
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_dec(v___x_879_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_904_; 
if (v_isShared_902_ == 0)
{
v___x_904_ = v___x_901_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_a_899_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_init_909_, lean_object* v_as_910_, lean_object* v_sz_911_, lean_object* v_i_912_, lean_object* v_b_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
size_t v_sz_boxed_919_; size_t v_i_boxed_920_; lean_object* v_res_921_; 
v_sz_boxed_919_ = lean_unbox_usize(v_sz_911_);
lean_dec(v_sz_911_);
v_i_boxed_920_ = lean_unbox_usize(v_i_912_);
lean_dec(v_i_912_);
v_res_921_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__4(v_init_909_, v_as_910_, v_sz_boxed_919_, v_i_boxed_920_, v_b_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec_ref(v_as_910_);
lean_dec_ref(v_init_909_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2___boxed(lean_object* v_init_922_, lean_object* v_n_923_, lean_object* v_b_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
lean_object* v_res_930_; 
v_res_930_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2(v_init_922_, v_n_923_, v_b_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec_ref(v_n_923_);
lean_dec_ref(v_init_922_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___redArg(lean_object* v_as_931_, size_t v_sz_932_, size_t v_i_933_, lean_object* v_b_934_){
_start:
{
uint8_t v___x_936_; 
v___x_936_ = lean_usize_dec_lt(v_i_933_, v_sz_932_);
if (v___x_936_ == 0)
{
lean_object* v___x_937_; 
v___x_937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_937_, 0, v_b_934_);
return v___x_937_;
}
else
{
lean_object* v_snd_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_956_; 
v_snd_938_ = lean_ctor_get(v_b_934_, 1);
v_isSharedCheck_956_ = !lean_is_exclusive(v_b_934_);
if (v_isSharedCheck_956_ == 0)
{
lean_object* v_unused_957_; 
v_unused_957_ = lean_ctor_get(v_b_934_, 0);
lean_dec(v_unused_957_);
v___x_940_ = v_b_934_;
v_isShared_941_ = v_isSharedCheck_956_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_snd_938_);
lean_dec(v_b_934_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_956_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_942_; lean_object* v_a_944_; lean_object* v_a_951_; 
v___x_942_ = lean_box(0);
v_a_951_ = lean_array_uget_borrowed(v_as_931_, v_i_933_);
if (lean_obj_tag(v_a_951_) == 0)
{
v_a_944_ = v_snd_938_;
goto v___jp_943_;
}
else
{
lean_object* v_val_952_; uint8_t v___x_953_; 
v_val_952_ = lean_ctor_get(v_a_951_, 0);
v___x_953_ = l_Lean_LocalDecl_isImplementationDetail(v_val_952_);
if (v___x_953_ == 0)
{
lean_object* v___x_954_; lean_object* v___x_955_; 
lean_inc(v_val_952_);
v___x_954_ = l_Lean_LocalDecl_toExpr(v_val_952_);
v___x_955_ = lean_array_push(v_snd_938_, v___x_954_);
v_a_944_ = v___x_955_;
goto v___jp_943_;
}
else
{
v_a_944_ = v_snd_938_;
goto v___jp_943_;
}
}
v___jp_943_:
{
lean_object* v___x_946_; 
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 1, v_a_944_);
lean_ctor_set(v___x_940_, 0, v___x_942_);
v___x_946_ = v___x_940_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_942_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v_a_944_);
v___x_946_ = v_reuseFailAlloc_950_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
size_t v___x_947_; size_t v___x_948_; 
v___x_947_ = ((size_t)1ULL);
v___x_948_ = lean_usize_add(v_i_933_, v___x_947_);
v_i_933_ = v___x_948_;
v_b_934_ = v___x_946_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_as_958_, lean_object* v_sz_959_, lean_object* v_i_960_, lean_object* v_b_961_, lean_object* v___y_962_){
_start:
{
size_t v_sz_boxed_963_; size_t v_i_boxed_964_; lean_object* v_res_965_; 
v_sz_boxed_963_ = lean_unbox_usize(v_sz_959_);
lean_dec(v_sz_959_);
v_i_boxed_964_ = lean_unbox_usize(v_i_960_);
lean_dec(v_i_960_);
v_res_965_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___redArg(v_as_958_, v_sz_boxed_963_, v_i_boxed_964_, v_b_961_);
lean_dec_ref(v_as_958_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3(lean_object* v_as_966_, size_t v_sz_967_, size_t v_i_968_, lean_object* v_b_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
uint8_t v___x_975_; 
v___x_975_ = lean_usize_dec_lt(v_i_968_, v_sz_967_);
if (v___x_975_ == 0)
{
lean_object* v___x_976_; 
v___x_976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_976_, 0, v_b_969_);
return v___x_976_;
}
else
{
lean_object* v_snd_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_995_; 
v_snd_977_ = lean_ctor_get(v_b_969_, 1);
v_isSharedCheck_995_ = !lean_is_exclusive(v_b_969_);
if (v_isSharedCheck_995_ == 0)
{
lean_object* v_unused_996_; 
v_unused_996_ = lean_ctor_get(v_b_969_, 0);
lean_dec(v_unused_996_);
v___x_979_ = v_b_969_;
v_isShared_980_ = v_isSharedCheck_995_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_snd_977_);
lean_dec(v_b_969_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_995_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_981_; lean_object* v_a_983_; lean_object* v_a_990_; 
v___x_981_ = lean_box(0);
v_a_990_ = lean_array_uget_borrowed(v_as_966_, v_i_968_);
if (lean_obj_tag(v_a_990_) == 0)
{
v_a_983_ = v_snd_977_;
goto v___jp_982_;
}
else
{
lean_object* v_val_991_; uint8_t v___x_992_; 
v_val_991_ = lean_ctor_get(v_a_990_, 0);
v___x_992_ = l_Lean_LocalDecl_isImplementationDetail(v_val_991_);
if (v___x_992_ == 0)
{
lean_object* v___x_993_; lean_object* v___x_994_; 
lean_inc(v_val_991_);
v___x_993_ = l_Lean_LocalDecl_toExpr(v_val_991_);
v___x_994_ = lean_array_push(v_snd_977_, v___x_993_);
v_a_983_ = v___x_994_;
goto v___jp_982_;
}
else
{
v_a_983_ = v_snd_977_;
goto v___jp_982_;
}
}
v___jp_982_:
{
lean_object* v___x_985_; 
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 1, v_a_983_);
lean_ctor_set(v___x_979_, 0, v___x_981_);
v___x_985_ = v___x_979_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v___x_981_);
lean_ctor_set(v_reuseFailAlloc_989_, 1, v_a_983_);
v___x_985_ = v_reuseFailAlloc_989_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
size_t v___x_986_; size_t v___x_987_; lean_object* v___x_988_; 
v___x_986_ = ((size_t)1ULL);
v___x_987_ = lean_usize_add(v_i_968_, v___x_986_);
v___x_988_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___redArg(v_as_966_, v_sz_967_, v___x_987_, v___x_985_);
return v___x_988_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3___boxed(lean_object* v_as_997_, lean_object* v_sz_998_, lean_object* v_i_999_, lean_object* v_b_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
size_t v_sz_boxed_1006_; size_t v_i_boxed_1007_; lean_object* v_res_1008_; 
v_sz_boxed_1006_ = lean_unbox_usize(v_sz_998_);
lean_dec(v_sz_998_);
v_i_boxed_1007_ = lean_unbox_usize(v_i_999_);
lean_dec(v_i_999_);
v_res_1008_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3(v_as_997_, v_sz_boxed_1006_, v_i_boxed_1007_, v_b_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_);
lean_dec(v___y_1004_);
lean_dec_ref(v___y_1003_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec_ref(v_as_997_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1(lean_object* v_t_1009_, lean_object* v_init_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_){
_start:
{
lean_object* v_root_1016_; lean_object* v_tail_1017_; lean_object* v___x_1018_; 
v_root_1016_ = lean_ctor_get(v_t_1009_, 0);
v_tail_1017_ = lean_ctor_get(v_t_1009_, 1);
lean_inc_ref(v_init_1010_);
v___x_1018_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2(v_init_1010_, v_root_1016_, v_init_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
lean_dec_ref(v_init_1010_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1055_; 
v_a_1019_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1021_ = v___x_1018_;
v_isShared_1022_ = v_isSharedCheck_1055_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_1018_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1055_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
if (lean_obj_tag(v_a_1019_) == 0)
{
lean_object* v_a_1023_; lean_object* v___x_1025_; 
v_a_1023_ = lean_ctor_get(v_a_1019_, 0);
lean_inc(v_a_1023_);
lean_dec_ref_known(v_a_1019_, 1);
if (v_isShared_1022_ == 0)
{
lean_ctor_set(v___x_1021_, 0, v_a_1023_);
v___x_1025_ = v___x_1021_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v_a_1023_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
return v___x_1025_;
}
}
else
{
lean_object* v_a_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; size_t v_sz_1030_; size_t v___x_1031_; lean_object* v___x_1032_; 
lean_del_object(v___x_1021_);
v_a_1027_ = lean_ctor_get(v_a_1019_, 0);
lean_inc(v_a_1027_);
lean_dec_ref_known(v_a_1019_, 1);
v___x_1028_ = lean_box(0);
v___x_1029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1028_);
lean_ctor_set(v___x_1029_, 1, v_a_1027_);
v_sz_1030_ = lean_array_size(v_tail_1017_);
v___x_1031_ = ((size_t)0ULL);
v___x_1032_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3(v_tail_1017_, v_sz_1030_, v___x_1031_, v___x_1029_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
if (lean_obj_tag(v___x_1032_) == 0)
{
lean_object* v_a_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1046_; 
v_a_1033_ = lean_ctor_get(v___x_1032_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1035_ = v___x_1032_;
v_isShared_1036_ = v_isSharedCheck_1046_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_a_1033_);
lean_dec(v___x_1032_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1046_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v_fst_1037_; 
v_fst_1037_ = lean_ctor_get(v_a_1033_, 0);
if (lean_obj_tag(v_fst_1037_) == 0)
{
lean_object* v_snd_1038_; lean_object* v___x_1040_; 
v_snd_1038_ = lean_ctor_get(v_a_1033_, 1);
lean_inc(v_snd_1038_);
lean_dec(v_a_1033_);
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 0, v_snd_1038_);
v___x_1040_ = v___x_1035_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_snd_1038_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
else
{
lean_object* v_val_1042_; lean_object* v___x_1044_; 
lean_inc_ref(v_fst_1037_);
lean_dec(v_a_1033_);
v_val_1042_ = lean_ctor_get(v_fst_1037_, 0);
lean_inc(v_val_1042_);
lean_dec_ref_known(v_fst_1037_, 1);
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 0, v_val_1042_);
v___x_1044_ = v___x_1035_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_val_1042_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
else
{
lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1054_; 
v_a_1047_ = lean_ctor_get(v___x_1032_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1049_ = v___x_1032_;
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_1032_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1052_; 
if (v_isShared_1050_ == 0)
{
v___x_1052_ = v___x_1049_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_a_1047_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
}
}
}
else
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
v_a_1056_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1058_ = v___x_1018_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___x_1018_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_a_1056_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1___boxed(lean_object* v_t_1064_, lean_object* v_init_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1(v_t_1064_, v_init_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
lean_dec(v___y_1067_);
lean_dec_ref(v___y_1066_);
lean_dec_ref(v_t_1064_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1(lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_){
_start:
{
lean_object* v_lctx_1079_; lean_object* v_decls_1080_; lean_object* v_hs_1081_; lean_object* v___x_1082_; 
v_lctx_1079_ = lean_ctor_get(v___y_1074_, 2);
v_decls_1080_ = lean_ctor_get(v_lctx_1079_, 1);
v_hs_1081_ = ((lean_object*)(l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1___closed__0));
v___x_1082_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1(v_decls_1080_, v_hs_1081_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1___boxed(lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1(v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_localHypotheses(lean_object* v_except_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_){
_start:
{
lean_object* v___x_1097_; 
v___x_1097_ = l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1(v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_);
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_object* v_a_1098_; lean_object* v___x_1099_; size_t v_sz_1100_; size_t v___x_1101_; lean_object* v___x_1102_; 
v_a_1098_ = lean_ctor_get(v___x_1097_, 0);
lean_inc(v_a_1098_);
lean_dec_ref_known(v___x_1097_, 1);
v___x_1099_ = ((lean_object*)(l_Lean_Meta_Rewrites_localHypotheses___closed__0));
v_sz_1100_ = lean_array_size(v_a_1098_);
v___x_1101_ = ((size_t)0ULL);
v___x_1102_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_localHypotheses_spec__2(v_except_1091_, v_a_1098_, v_sz_1100_, v___x_1101_, v___x_1099_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_);
lean_dec(v_a_1098_);
return v___x_1102_;
}
else
{
lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1110_; 
v_a_1103_ = lean_ctor_get(v___x_1097_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1105_ = v___x_1097_;
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_dec(v___x_1097_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1108_; 
if (v_isShared_1106_ == 0)
{
v___x_1108_ = v___x_1105_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_a_1103_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_localHypotheses___boxed(lean_object* v_except_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Lean_Meta_Rewrites_localHypotheses(v_except_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_);
lean_dec(v_a_1115_);
lean_dec_ref(v_a_1114_);
lean_dec(v_a_1113_);
lean_dec_ref(v_a_1112_);
lean_dec(v_except_1111_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7(lean_object* v_as_1118_, size_t v_sz_1119_, size_t v_i_1120_, lean_object* v_b_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
lean_object* v___x_1127_; 
v___x_1127_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___redArg(v_as_1118_, v_sz_1119_, v_i_1120_, v_b_1121_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___boxed(lean_object* v_as_1128_, lean_object* v_sz_1129_, lean_object* v_i_1130_, lean_object* v_b_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
size_t v_sz_boxed_1137_; size_t v_i_boxed_1138_; lean_object* v_res_1139_; 
v_sz_boxed_1137_ = lean_unbox_usize(v_sz_1129_);
lean_dec(v_sz_1129_);
v_i_boxed_1138_ = lean_unbox_usize(v_i_1130_);
lean_dec(v_i_1130_);
v_res_1139_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7(v_as_1128_, v_sz_boxed_1137_, v_i_boxed_1138_, v_b_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec_ref(v_as_1128_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6(lean_object* v_as_1140_, size_t v_sz_1141_, size_t v_i_1142_, lean_object* v_b_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_){
_start:
{
lean_object* v___x_1149_; 
v___x_1149_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(v_as_1140_, v_sz_1141_, v_i_1142_, v_b_1143_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___boxed(lean_object* v_as_1150_, lean_object* v_sz_1151_, lean_object* v_i_1152_, lean_object* v_b_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_){
_start:
{
size_t v_sz_boxed_1159_; size_t v_i_boxed_1160_; lean_object* v_res_1161_; 
v_sz_boxed_1159_ = lean_unbox_usize(v_sz_1151_);
lean_dec(v_sz_1151_);
v_i_boxed_1160_ = lean_unbox_usize(v_i_1152_);
lean_dec(v_i_1152_);
v_res_1161_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6(v_as_1150_, v_sz_boxed_1159_, v_i_boxed_1160_, v_b_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
lean_dec_ref(v_as_1150_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_createModuleTreeRef(lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_){
_start:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1192_ = ((lean_object*)(l_Lean_Meta_Rewrites_createModuleTreeRef___closed__0));
v___x_1193_ = ((lean_object*)(l_Lean_Meta_Rewrites_droppedKeys));
v___x_1194_ = lean_box(0);
v___x_1195_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v___x_1192_, v___x_1193_, v___x_1194_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_createModuleTreeRef___boxed(lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l_Lean_Meta_Rewrites_createModuleTreeRef(v_a_1196_, v_a_1197_, v_a_1198_, v_a_1199_);
lean_dec(v_a_1199_);
lean_dec_ref(v_a_1198_);
lean_dec(v_a_1197_);
lean_dec_ref(v_a_1196_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_1824551397____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1203_ = lean_box(0);
v___x_1204_ = lean_st_mk_ref(v___x_1203_);
v___x_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1204_);
return v___x_1205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_1824551397____hygCtx___hyg_2____boxed(lean_object* v_a_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_1824551397____hygCtx___hyg_2_();
return v_res_1207_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_constantsPerImportTask(void){
_start:
{
lean_object* v___x_1208_; 
v___x_1208_ = lean_unsigned_to_nat(6500u);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_incPrio(lean_object* v_x_1209_, lean_object* v_x_1210_){
_start:
{
lean_object* v_snd_1211_; uint8_t v___x_1212_; 
v_snd_1211_ = lean_ctor_get(v_x_1210_, 1);
v___x_1212_ = lean_unbox(v_snd_1211_);
if (v___x_1212_ == 0)
{
lean_object* v_fst_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1225_; 
v_fst_1213_ = lean_ctor_get(v_x_1210_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v_x_1210_);
if (v_isSharedCheck_1225_ == 0)
{
lean_object* v_unused_1226_; 
v_unused_1226_ = lean_ctor_get(v_x_1210_, 1);
lean_dec(v_unused_1226_);
v___x_1215_ = v_x_1210_;
v_isShared_1216_ = v_isSharedCheck_1225_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_fst_1213_);
lean_dec(v_x_1210_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1225_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
uint8_t v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1222_; 
v___x_1217_ = 0;
v___x_1218_ = lean_unsigned_to_nat(2u);
v___x_1219_ = lean_nat_mul(v___x_1218_, v_x_1209_);
lean_dec(v_x_1209_);
v___x_1220_ = lean_box(v___x_1217_);
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 1, v___x_1219_);
lean_ctor_set(v___x_1215_, 0, v___x_1220_);
v___x_1222_ = v___x_1215_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v___x_1220_);
lean_ctor_set(v_reuseFailAlloc_1224_, 1, v___x_1219_);
v___x_1222_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
lean_object* v___x_1223_; 
v___x_1223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1223_, 0, v_fst_1213_);
lean_ctor_set(v___x_1223_, 1, v___x_1222_);
return v___x_1223_;
}
}
}
else
{
lean_object* v_fst_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1237_; 
v_fst_1227_ = lean_ctor_get(v_x_1210_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v_x_1210_);
if (v_isSharedCheck_1237_ == 0)
{
lean_object* v_unused_1238_; 
v_unused_1238_ = lean_ctor_get(v_x_1210_, 1);
lean_dec(v_unused_1238_);
v___x_1229_ = v_x_1210_;
v_isShared_1230_ = v_isSharedCheck_1237_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_fst_1227_);
lean_dec(v_x_1210_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1237_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
uint8_t v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1234_; 
v___x_1231_ = 1;
v___x_1232_ = lean_box(v___x_1231_);
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 1, v_x_1209_);
lean_ctor_set(v___x_1229_, 0, v___x_1232_);
v___x_1234_ = v___x_1229_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v___x_1232_);
lean_ctor_set(v_reuseFailAlloc_1236_, 1, v_x_1209_);
v___x_1234_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
lean_object* v___x_1235_; 
v___x_1235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1235_, 0, v_fst_1227_);
lean_ctor_set(v___x_1235_, 1, v___x_1234_);
return v___x_1235_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwFindDecls(lean_object* v_moduleRef_1240_, lean_object* v_ty_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_){
_start:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1247_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_ext;
v___x_1248_ = ((lean_object*)(l_Lean_Meta_Rewrites_createModuleTreeRef___closed__0));
v___x_1249_ = ((lean_object*)(l_Lean_Meta_Rewrites_droppedKeys));
v___x_1250_ = lean_unsigned_to_nat(6500u);
v___x_1251_ = lean_box(0);
v___x_1252_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwFindDecls___closed__0));
v___x_1253_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_moduleRef_1240_, v___x_1247_, v___x_1248_, v___x_1249_, v___x_1250_, v___x_1251_, v___x_1252_, v_ty_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_);
return v___x_1253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwFindDecls___boxed(lean_object* v_moduleRef_1254_, lean_object* v_ty_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l_Lean_Meta_Rewrites_rwFindDecls(v_moduleRef_1254_, v_ty_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
lean_dec(v_a_1259_);
lean_dec_ref(v_a_1258_);
lean_dec(v_a_1257_);
lean_dec_ref(v_a_1256_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg(lean_object* v_mctx_1262_, lean_object* v_x_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
lean_object* v___x_1269_; 
v___x_1269_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp(lean_box(0), v_mctx_1262_, v_x_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_object* v_a_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1277_; 
v_a_1270_ = lean_ctor_get(v___x_1269_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1272_ = v___x_1269_;
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_a_1270_);
lean_dec(v___x_1269_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1275_; 
if (v_isShared_1273_ == 0)
{
v___x_1275_ = v___x_1272_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_a_1270_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
else
{
lean_object* v_a_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1285_; 
v_a_1278_ = lean_ctor_get(v___x_1269_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1280_ = v___x_1269_;
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_a_1278_);
lean_dec(v___x_1269_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1283_; 
if (v_isShared_1281_ == 0)
{
v___x_1283_ = v___x_1280_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_a_1278_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg___boxed(lean_object* v_mctx_1286_, lean_object* v_x_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_){
_start:
{
lean_object* v_res_1293_; 
v_res_1293_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg(v_mctx_1286_, v_x_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
lean_dec(v___y_1289_);
lean_dec_ref(v___y_1288_);
return v_res_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0(lean_object* v_00_u03b1_1294_, lean_object* v_mctx_1295_, lean_object* v_x_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_){
_start:
{
lean_object* v___x_1302_; 
v___x_1302_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg(v_mctx_1295_, v_x_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_);
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___boxed(lean_object* v_00_u03b1_1303_, lean_object* v_mctx_1304_, lean_object* v_x_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0(v_00_u03b1_1303_, v_mctx_1304_, v_x_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(lean_object* v_x_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
lean_object* v___x_1318_; 
v___x_1318_ = l_Lean_Meta_saveState___redArg(v___y_1314_, v___y_1316_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_object* v_a_1319_; lean_object* v_r_1320_; 
v_a_1319_ = lean_ctor_get(v___x_1318_, 0);
lean_inc(v_a_1319_);
lean_dec_ref_known(v___x_1318_, 1);
lean_inc(v___y_1316_);
lean_inc_ref(v___y_1315_);
lean_inc(v___y_1314_);
lean_inc_ref(v___y_1313_);
v_r_1320_ = lean_apply_5(v_x_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, lean_box(0));
if (lean_obj_tag(v_r_1320_) == 0)
{
lean_object* v_a_1321_; lean_object* v___x_1322_; 
v_a_1321_ = lean_ctor_get(v_r_1320_, 0);
lean_inc(v_a_1321_);
lean_dec_ref_known(v_r_1320_, 1);
v___x_1322_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1319_, v___y_1314_, v___y_1316_);
lean_dec(v_a_1319_);
if (lean_obj_tag(v___x_1322_) == 0)
{
lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1329_; 
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1329_ == 0)
{
lean_object* v_unused_1330_; 
v_unused_1330_ = lean_ctor_get(v___x_1322_, 0);
lean_dec(v_unused_1330_);
v___x_1324_ = v___x_1322_;
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
else
{
lean_dec(v___x_1322_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1327_; 
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 0, v_a_1321_);
v___x_1327_ = v___x_1324_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_a_1321_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
}
else
{
lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1338_; 
lean_dec(v_a_1321_);
v_a_1331_ = lean_ctor_get(v___x_1322_, 0);
v_isSharedCheck_1338_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1333_ = v___x_1322_;
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_dec(v___x_1322_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1336_; 
if (v_isShared_1334_ == 0)
{
v___x_1336_ = v___x_1333_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v_a_1331_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
return v___x_1336_;
}
}
}
}
else
{
lean_object* v_a_1339_; lean_object* v___x_1340_; 
v_a_1339_ = lean_ctor_get(v_r_1320_, 0);
lean_inc(v_a_1339_);
lean_dec_ref_known(v_r_1320_, 1);
v___x_1340_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1319_, v___y_1314_, v___y_1316_);
lean_dec(v_a_1319_);
if (lean_obj_tag(v___x_1340_) == 0)
{
lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1347_; 
v_isSharedCheck_1347_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1347_ == 0)
{
lean_object* v_unused_1348_; 
v_unused_1348_ = lean_ctor_get(v___x_1340_, 0);
lean_dec(v_unused_1348_);
v___x_1342_ = v___x_1340_;
v_isShared_1343_ = v_isSharedCheck_1347_;
goto v_resetjp_1341_;
}
else
{
lean_dec(v___x_1340_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1347_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v___x_1345_; 
if (v_isShared_1343_ == 0)
{
lean_ctor_set_tag(v___x_1342_, 1);
lean_ctor_set(v___x_1342_, 0, v_a_1339_);
v___x_1345_ = v___x_1342_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_a_1339_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
return v___x_1345_;
}
}
}
else
{
lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1356_; 
lean_dec(v_a_1339_);
v_a_1349_ = lean_ctor_get(v___x_1340_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1351_ = v___x_1340_;
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v___x_1340_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1354_; 
if (v_isShared_1352_ == 0)
{
v___x_1354_ = v___x_1351_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_a_1349_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
}
}
else
{
lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1364_; 
lean_dec_ref(v_x_1312_);
v_a_1357_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1359_ = v___x_1318_;
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v___x_1318_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
if (v_isShared_1360_ == 0)
{
v___x_1362_ = v___x_1359_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_a_1357_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg___boxed(lean_object* v_x_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_){
_start:
{
lean_object* v_res_1371_; 
v_res_1371_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v_x_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_);
lean_dec(v___y_1369_);
lean_dec_ref(v___y_1368_);
lean_dec(v___y_1367_);
lean_dec_ref(v___y_1366_);
return v_res_1371_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1(lean_object* v_00_u03b1_1372_, lean_object* v_x_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_){
_start:
{
lean_object* v___x_1379_; 
v___x_1379_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v_x_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
return v___x_1379_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___boxed(lean_object* v_00_u03b1_1380_, lean_object* v_x_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1(v_00_u03b1_1380_, v_x_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0(lean_object* v___x_1388_, uint8_t v___x_1389_, lean_object* v___x_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
lean_object* v___x_1396_; 
v___x_1396_ = l_Lean_Meta_mkFreshExprMVar(v___x_1388_, v___x_1389_, v___x_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_);
if (lean_obj_tag(v___x_1396_) == 0)
{
lean_object* v_a_1397_; lean_object* v___x_1398_; uint8_t v_transparency_1399_; lean_object* v___x_1400_; uint8_t v___x_1401_; lean_object* v___y_1403_; uint8_t v___x_1421_; uint8_t v___x_1422_; 
v_a_1397_ = lean_ctor_get(v___x_1396_, 0);
lean_inc(v_a_1397_);
lean_dec_ref_known(v___x_1396_, 1);
v___x_1398_ = l_Lean_Meta_Context_config(v___y_1391_);
v_transparency_1399_ = lean_ctor_get_uint8(v___x_1398_, 9);
lean_dec_ref(v___x_1398_);
v___x_1400_ = l_Lean_Expr_mvarId_x21(v_a_1397_);
lean_dec(v_a_1397_);
v___x_1401_ = 1;
v___x_1421_ = 2;
v___x_1422_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_1399_, v___x_1421_);
if (v___x_1422_ == 0)
{
lean_object* v_keyedConfig_1423_; uint8_t v_trackZetaDelta_1424_; lean_object* v_zetaDeltaSet_1425_; lean_object* v_lctx_1426_; lean_object* v_localInstances_1427_; lean_object* v_defEqCtx_x3f_1428_; lean_object* v_synthPendingDepth_1429_; lean_object* v_customCanUnfoldPredicate_x3f_1430_; uint8_t v_univApprox_1431_; uint8_t v_inTypeClassResolution_1432_; uint8_t v_cacheInferType_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1442_; 
v_keyedConfig_1423_ = lean_ctor_get(v___y_1391_, 0);
v_trackZetaDelta_1424_ = lean_ctor_get_uint8(v___y_1391_, sizeof(void*)*7);
v_zetaDeltaSet_1425_ = lean_ctor_get(v___y_1391_, 1);
v_lctx_1426_ = lean_ctor_get(v___y_1391_, 2);
v_localInstances_1427_ = lean_ctor_get(v___y_1391_, 3);
v_defEqCtx_x3f_1428_ = lean_ctor_get(v___y_1391_, 4);
v_synthPendingDepth_1429_ = lean_ctor_get(v___y_1391_, 5);
v_customCanUnfoldPredicate_x3f_1430_ = lean_ctor_get(v___y_1391_, 6);
v_univApprox_1431_ = lean_ctor_get_uint8(v___y_1391_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1432_ = lean_ctor_get_uint8(v___y_1391_, sizeof(void*)*7 + 2);
v_cacheInferType_1433_ = lean_ctor_get_uint8(v___y_1391_, sizeof(void*)*7 + 3);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___y_1391_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1435_ = v___y_1391_;
v_isShared_1436_ = v_isSharedCheck_1442_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_1430_);
lean_inc(v_synthPendingDepth_1429_);
lean_inc(v_defEqCtx_x3f_1428_);
lean_inc(v_localInstances_1427_);
lean_inc(v_lctx_1426_);
lean_inc(v_zetaDeltaSet_1425_);
lean_inc(v_keyedConfig_1423_);
lean_dec(v___y_1391_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1442_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1437_; lean_object* v___x_1439_; 
v___x_1437_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1421_, v_keyedConfig_1423_);
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 0, v___x_1437_);
v___x_1439_ = v___x_1435_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v___x_1437_);
lean_ctor_set(v_reuseFailAlloc_1441_, 1, v_zetaDeltaSet_1425_);
lean_ctor_set(v_reuseFailAlloc_1441_, 2, v_lctx_1426_);
lean_ctor_set(v_reuseFailAlloc_1441_, 3, v_localInstances_1427_);
lean_ctor_set(v_reuseFailAlloc_1441_, 4, v_defEqCtx_x3f_1428_);
lean_ctor_set(v_reuseFailAlloc_1441_, 5, v_synthPendingDepth_1429_);
lean_ctor_set(v_reuseFailAlloc_1441_, 6, v_customCanUnfoldPredicate_x3f_1430_);
lean_ctor_set_uint8(v_reuseFailAlloc_1441_, sizeof(void*)*7, v_trackZetaDelta_1424_);
lean_ctor_set_uint8(v_reuseFailAlloc_1441_, sizeof(void*)*7 + 1, v_univApprox_1431_);
lean_ctor_set_uint8(v_reuseFailAlloc_1441_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1432_);
lean_ctor_set_uint8(v_reuseFailAlloc_1441_, sizeof(void*)*7 + 3, v_cacheInferType_1433_);
v___x_1439_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
lean_object* v___x_1440_; 
v___x_1440_ = l_Lean_MVarId_refl(v___x_1400_, v___x_1401_, v___x_1439_, v___y_1392_, v___y_1393_, v___y_1394_);
lean_dec_ref(v___x_1439_);
v___y_1403_ = v___x_1440_;
goto v___jp_1402_;
}
}
}
else
{
lean_object* v___x_1443_; 
v___x_1443_ = l_Lean_MVarId_refl(v___x_1400_, v___x_1401_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_);
lean_dec_ref(v___y_1391_);
v___y_1403_ = v___x_1443_;
goto v___jp_1402_;
}
v___jp_1402_:
{
if (lean_obj_tag(v___y_1403_) == 0)
{
lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1411_; 
v_isSharedCheck_1411_ = !lean_is_exclusive(v___y_1403_);
if (v_isSharedCheck_1411_ == 0)
{
lean_object* v_unused_1412_; 
v_unused_1412_ = lean_ctor_get(v___y_1403_, 0);
lean_dec(v_unused_1412_);
v___x_1405_ = v___y_1403_;
v_isShared_1406_ = v_isSharedCheck_1411_;
goto v_resetjp_1404_;
}
else
{
lean_dec(v___y_1403_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1411_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1407_; lean_object* v___x_1409_; 
v___x_1407_ = lean_box(v___x_1401_);
if (v_isShared_1406_ == 0)
{
lean_ctor_set(v___x_1405_, 0, v___x_1407_);
v___x_1409_ = v___x_1405_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v___x_1407_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
}
else
{
lean_object* v_a_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1420_; 
v_a_1413_ = lean_ctor_get(v___y_1403_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___y_1403_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1415_ = v___y_1403_;
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_a_1413_);
lean_dec(v___y_1403_);
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
else
{
lean_object* v_a_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1451_; 
lean_dec_ref(v___y_1391_);
v_a_1444_ = lean_ctor_get(v___x_1396_, 0);
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1446_ = v___x_1396_;
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_a_1444_);
lean_dec(v___x_1396_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1449_; 
if (v_isShared_1447_ == 0)
{
v___x_1449_ = v___x_1446_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v_a_1444_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
return v___x_1449_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___boxed(lean_object* v___x_1452_, lean_object* v___x_1453_, lean_object* v___x_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_){
_start:
{
uint8_t v___x_2261__boxed_1460_; lean_object* v_res_1461_; 
v___x_2261__boxed_1460_ = lean_unbox(v___x_1453_);
v_res_1461_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0(v___x_1452_, v___x_2261__boxed_1460_, v___x_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_);
lean_dec(v___y_1458_);
lean_dec_ref(v___y_1457_);
lean_dec(v___y_1456_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(lean_object* v_mctx_1462_, lean_object* v_e_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_){
_start:
{
lean_object* v___x_1469_; uint8_t v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___f_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; 
v___x_1469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1469_, 0, v_e_1463_);
v___x_1470_ = 0;
v___x_1471_ = lean_box(0);
v___x_1472_ = lean_box(v___x_1470_);
v___f_1473_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1473_, 0, v___x_1469_);
lean_closure_set(v___f_1473_, 1, v___x_1472_);
lean_closure_set(v___f_1473_, 2, v___x_1471_);
v___x_1474_ = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___boxed), 8, 3);
lean_closure_set(v___x_1474_, 0, lean_box(0));
lean_closure_set(v___x_1474_, 1, v_mctx_1462_);
lean_closure_set(v___x_1474_, 2, v___f_1473_);
v___x_1475_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v___x_1474_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_);
if (lean_obj_tag(v___x_1475_) == 0)
{
return v___x_1475_;
}
else
{
lean_object* v_a_1476_; uint8_t v___y_1478_; uint8_t v___x_1488_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
lean_inc(v_a_1476_);
v___x_1488_ = l_Lean_Exception_isInterrupt(v_a_1476_);
if (v___x_1488_ == 0)
{
uint8_t v___x_1489_; 
v___x_1489_ = l_Lean_Exception_isRuntime(v_a_1476_);
v___y_1478_ = v___x_1489_;
goto v___jp_1477_;
}
else
{
lean_dec(v_a_1476_);
v___y_1478_ = v___x_1488_;
goto v___jp_1477_;
}
v___jp_1477_:
{
if (v___y_1478_ == 0)
{
lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1486_; 
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1486_ == 0)
{
lean_object* v_unused_1487_; 
v_unused_1487_ = lean_ctor_get(v___x_1475_, 0);
lean_dec(v_unused_1487_);
v___x_1480_ = v___x_1475_;
v_isShared_1481_ = v_isSharedCheck_1486_;
goto v_resetjp_1479_;
}
else
{
lean_dec(v___x_1475_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1486_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1482_; lean_object* v___x_1484_; 
v___x_1482_ = lean_box(v___y_1478_);
if (v_isShared_1481_ == 0)
{
lean_ctor_set_tag(v___x_1480_, 0);
lean_ctor_set(v___x_1480_, 0, v___x_1482_);
v___x_1484_ = v___x_1480_;
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
return v___x_1475_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___boxed(lean_object* v_mctx_1490_, lean_object* v_e_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_){
_start:
{
lean_object* v_res_1497_; 
v_res_1497_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(v_mctx_1490_, v_e_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_);
lean_dec(v_a_1495_);
lean_dec_ref(v_a_1494_);
lean_dec(v_a_1493_);
lean_dec_ref(v_a_1492_);
return v_res_1497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult(lean_object* v_r_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_){
_start:
{
lean_object* v_result_1504_; lean_object* v_eNew_1505_; lean_object* v___x_1506_; 
v_result_1504_ = lean_ctor_get(v_r_1498_, 2);
lean_inc_ref(v_result_1504_);
lean_dec_ref(v_r_1498_);
v_eNew_1505_ = lean_ctor_get(v_result_1504_, 0);
lean_inc_ref(v_eNew_1505_);
lean_dec_ref(v_result_1504_);
v___x_1506_ = l_Lean_Meta_ppExpr(v_eNew_1505_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_);
if (lean_obj_tag(v___x_1506_) == 0)
{
lean_object* v_a_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1517_; 
v_a_1507_ = lean_ctor_get(v___x_1506_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1506_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1509_ = v___x_1506_;
v_isShared_1510_ = v_isSharedCheck_1517_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_a_1507_);
lean_dec(v___x_1506_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1517_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1515_; 
v___x_1511_ = l_Std_Format_defWidth;
v___x_1512_ = lean_unsigned_to_nat(0u);
v___x_1513_ = l_Std_Format_pretty(v_a_1507_, v___x_1511_, v___x_1512_, v___x_1512_);
if (v_isShared_1510_ == 0)
{
lean_ctor_set(v___x_1509_, 0, v___x_1513_);
v___x_1515_ = v___x_1509_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1513_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
else
{
lean_object* v_a_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1525_; 
v_a_1518_ = lean_ctor_get(v___x_1506_, 0);
v_isSharedCheck_1525_ = !lean_is_exclusive(v___x_1506_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1520_ = v___x_1506_;
v_isShared_1521_ = v_isSharedCheck_1525_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_a_1518_);
lean_dec(v___x_1506_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1525_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v___x_1523_; 
if (v_isShared_1521_ == 0)
{
v___x_1523_ = v___x_1520_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_a_1518_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult___boxed(lean_object* v_r_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_){
_start:
{
lean_object* v_res_1532_; 
v_res_1532_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult(v_r_1526_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_);
lean_dec(v_a_1530_);
lean_dec_ref(v_a_1529_);
lean_dec(v_a_1528_);
lean_dec_ref(v_a_1527_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorIdx(uint8_t v_x_1533_){
_start:
{
switch(v_x_1533_)
{
case 0:
{
lean_object* v___x_1534_; 
v___x_1534_ = lean_unsigned_to_nat(0u);
return v___x_1534_;
}
case 1:
{
lean_object* v___x_1535_; 
v___x_1535_ = lean_unsigned_to_nat(1u);
return v___x_1535_;
}
default: 
{
lean_object* v___x_1536_; 
v___x_1536_ = lean_unsigned_to_nat(2u);
return v___x_1536_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorIdx___boxed(lean_object* v_x_1537_){
_start:
{
uint8_t v_x_boxed_1538_; lean_object* v_res_1539_; 
v_x_boxed_1538_ = lean_unbox(v_x_1537_);
v_res_1539_ = l_Lean_Meta_Rewrites_SideConditions_ctorIdx(v_x_boxed_1538_);
return v_res_1539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorElim___redArg(lean_object* v_k_1540_){
_start:
{
lean_inc(v_k_1540_);
return v_k_1540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorElim___redArg___boxed(lean_object* v_k_1541_){
_start:
{
lean_object* v_res_1542_; 
v_res_1542_ = l_Lean_Meta_Rewrites_SideConditions_ctorElim___redArg(v_k_1541_);
lean_dec(v_k_1541_);
return v_res_1542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorElim(lean_object* v_motive_1543_, lean_object* v_ctorIdx_1544_, uint8_t v_t_1545_, lean_object* v_h_1546_, lean_object* v_k_1547_){
_start:
{
lean_inc(v_k_1547_);
return v_k_1547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorElim___boxed(lean_object* v_motive_1548_, lean_object* v_ctorIdx_1549_, lean_object* v_t_1550_, lean_object* v_h_1551_, lean_object* v_k_1552_){
_start:
{
uint8_t v_t_boxed_1553_; lean_object* v_res_1554_; 
v_t_boxed_1553_ = lean_unbox(v_t_1550_);
v_res_1554_ = l_Lean_Meta_Rewrites_SideConditions_ctorElim(v_motive_1548_, v_ctorIdx_1549_, v_t_boxed_1553_, v_h_1551_, v_k_1552_);
lean_dec(v_k_1552_);
lean_dec(v_ctorIdx_1549_);
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_none_elim___redArg(lean_object* v_none_1555_){
_start:
{
lean_inc(v_none_1555_);
return v_none_1555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_none_elim___redArg___boxed(lean_object* v_none_1556_){
_start:
{
lean_object* v_res_1557_; 
v_res_1557_ = l_Lean_Meta_Rewrites_SideConditions_none_elim___redArg(v_none_1556_);
lean_dec(v_none_1556_);
return v_res_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_none_elim(lean_object* v_motive_1558_, uint8_t v_t_1559_, lean_object* v_h_1560_, lean_object* v_none_1561_){
_start:
{
lean_inc(v_none_1561_);
return v_none_1561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_none_elim___boxed(lean_object* v_motive_1562_, lean_object* v_t_1563_, lean_object* v_h_1564_, lean_object* v_none_1565_){
_start:
{
uint8_t v_t_boxed_1566_; lean_object* v_res_1567_; 
v_t_boxed_1566_ = lean_unbox(v_t_1563_);
v_res_1567_ = l_Lean_Meta_Rewrites_SideConditions_none_elim(v_motive_1562_, v_t_boxed_1566_, v_h_1564_, v_none_1565_);
lean_dec(v_none_1565_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_assumption_elim___redArg(lean_object* v_assumption_1568_){
_start:
{
lean_inc(v_assumption_1568_);
return v_assumption_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_assumption_elim___redArg___boxed(lean_object* v_assumption_1569_){
_start:
{
lean_object* v_res_1570_; 
v_res_1570_ = l_Lean_Meta_Rewrites_SideConditions_assumption_elim___redArg(v_assumption_1569_);
lean_dec(v_assumption_1569_);
return v_res_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_assumption_elim(lean_object* v_motive_1571_, uint8_t v_t_1572_, lean_object* v_h_1573_, lean_object* v_assumption_1574_){
_start:
{
lean_inc(v_assumption_1574_);
return v_assumption_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_assumption_elim___boxed(lean_object* v_motive_1575_, lean_object* v_t_1576_, lean_object* v_h_1577_, lean_object* v_assumption_1578_){
_start:
{
uint8_t v_t_boxed_1579_; lean_object* v_res_1580_; 
v_t_boxed_1579_ = lean_unbox(v_t_1576_);
v_res_1580_ = l_Lean_Meta_Rewrites_SideConditions_assumption_elim(v_motive_1575_, v_t_boxed_1579_, v_h_1577_, v_assumption_1578_);
lean_dec(v_assumption_1578_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim___redArg(lean_object* v_solveByElim_1581_){
_start:
{
lean_inc(v_solveByElim_1581_);
return v_solveByElim_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim___redArg___boxed(lean_object* v_solveByElim_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim___redArg(v_solveByElim_1582_);
lean_dec(v_solveByElim_1582_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim(lean_object* v_motive_1584_, uint8_t v_t_1585_, lean_object* v_h_1586_, lean_object* v_solveByElim_1587_){
_start:
{
lean_inc(v_solveByElim_1587_);
return v_solveByElim_1587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim___boxed(lean_object* v_motive_1588_, lean_object* v_t_1589_, lean_object* v_h_1590_, lean_object* v_solveByElim_1591_){
_start:
{
uint8_t v_t_boxed_1592_; lean_object* v_res_1593_; 
v_t_boxed_1592_ = lean_unbox(v_t_1589_);
v_res_1593_ = l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim(v_motive_1588_, v_t_boxed_1592_, v_h_1590_, v_solveByElim_1591_);
lean_dec(v_solveByElim_1591_);
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__0(lean_object* v_x_1594_, lean_object* v_x_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_){
_start:
{
lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1601_ = lean_box(0);
v___x_1602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1602_, 0, v___x_1601_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__0___boxed(lean_object* v_x_1603_, lean_object* v_x_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l_Lean_Meta_Rewrites_solveByElim___lam__0(v_x_1603_, v_x_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_);
lean_dec(v___y_1608_);
lean_dec_ref(v___y_1607_);
lean_dec(v___y_1606_);
lean_dec_ref(v___y_1605_);
lean_dec(v_x_1604_);
lean_dec(v_x_1603_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__1(lean_object* v_x_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
uint8_t v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1617_ = 0;
v___x_1618_ = lean_box(v___x_1617_);
v___x_1619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1618_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__1___boxed(lean_object* v_x_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l_Lean_Meta_Rewrites_solveByElim___lam__1(v_x_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
lean_dec(v_x_1620_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0(lean_object* v_msgData_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v___x_1633_; lean_object* v_env_1634_; lean_object* v___x_1635_; lean_object* v_toCold_1636_; lean_object* v_mctx_1637_; lean_object* v_lctx_1638_; lean_object* v_options_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1633_ = lean_st_ref_get(v___y_1631_);
v_env_1634_ = lean_ctor_get(v___x_1633_, 0);
lean_inc_ref(v_env_1634_);
lean_dec(v___x_1633_);
v___x_1635_ = lean_st_ref_get(v___y_1629_);
v_toCold_1636_ = lean_ctor_get(v___y_1630_, 0);
v_mctx_1637_ = lean_ctor_get(v___x_1635_, 0);
lean_inc_ref(v_mctx_1637_);
lean_dec(v___x_1635_);
v_lctx_1638_ = lean_ctor_get(v___y_1628_, 2);
v_options_1639_ = lean_ctor_get(v_toCold_1636_, 2);
lean_inc_ref(v_options_1639_);
lean_inc_ref(v_lctx_1638_);
v___x_1640_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1640_, 0, v_env_1634_);
lean_ctor_set(v___x_1640_, 1, v_mctx_1637_);
lean_ctor_set(v___x_1640_, 2, v_lctx_1638_);
lean_ctor_set(v___x_1640_, 3, v_options_1639_);
v___x_1641_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1640_);
lean_ctor_set(v___x_1641_, 1, v_msgData_1627_);
v___x_1642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1641_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0___boxed(lean_object* v_msgData_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_){
_start:
{
lean_object* v_res_1649_; 
v_res_1649_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0(v_msgData_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_);
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(lean_object* v_msg_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_){
_start:
{
lean_object* v_ref_1656_; lean_object* v___x_1657_; lean_object* v_a_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1666_; 
v_ref_1656_ = lean_ctor_get(v___y_1653_, 2);
v___x_1657_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0(v_msg_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
v_a_1658_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1660_ = v___x_1657_;
v_isShared_1661_ = v_isSharedCheck_1666_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_a_1658_);
lean_dec(v___x_1657_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1666_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1662_; lean_object* v___x_1664_; 
lean_inc(v_ref_1656_);
v___x_1662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1662_, 0, v_ref_1656_);
lean_ctor_set(v___x_1662_, 1, v_a_1658_);
if (v_isShared_1661_ == 0)
{
lean_ctor_set_tag(v___x_1660_, 1);
lean_ctor_set(v___x_1660_, 0, v___x_1662_);
v___x_1664_ = v___x_1660_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v___x_1662_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg___boxed(lean_object* v_msg_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(v_msg_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
return v_res_1673_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1675_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__0));
v___x_1676_ = l_Lean_stringToMessageData(v___x_1675_);
return v___x_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__2(lean_object* v_x_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_){
_start:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1683_ = lean_obj_once(&l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1, &l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1_once, _init_l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1);
v___x_1684_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(v___x_1683_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_);
return v___x_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__2___boxed(lean_object* v_x_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
lean_object* v_res_1691_; 
v_res_1691_ = l_Lean_Meta_Rewrites_solveByElim___lam__2(v_x_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
lean_dec(v_x_1685_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim(lean_object* v_goals_1701_, lean_object* v_depth_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_){
_start:
{
lean_object* v___f_1708_; lean_object* v___f_1709_; lean_object* v___f_1710_; uint8_t v___x_1711_; lean_object* v___x_1712_; uint8_t v___x_1713_; lean_object* v___x_1714_; uint8_t v___x_1715_; lean_object* v___x_1716_; lean_object* v_cfg_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___f_1708_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___closed__0));
v___f_1709_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___closed__1));
v___f_1710_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___closed__2));
v___x_1711_ = 0;
v___x_1712_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1712_, 0, v_depth_1702_);
lean_ctor_set(v___x_1712_, 1, v___f_1708_);
lean_ctor_set(v___x_1712_, 2, v___f_1709_);
lean_ctor_set(v___x_1712_, 3, v___f_1710_);
lean_ctor_set_uint8(v___x_1712_, sizeof(void*)*4, v___x_1711_);
v___x_1713_ = 1;
v___x_1714_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___closed__3));
v___x_1715_ = 1;
v___x_1716_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_1716_, 0, v___x_1712_);
lean_ctor_set(v___x_1716_, 1, v___x_1714_);
lean_ctor_set_uint8(v___x_1716_, sizeof(void*)*2, v___x_1715_);
lean_ctor_set_uint8(v___x_1716_, sizeof(void*)*2 + 1, v___x_1713_);
lean_ctor_set_uint8(v___x_1716_, sizeof(void*)*2 + 2, v___x_1711_);
v_cfg_1717_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_cfg_1717_, 0, v___x_1716_);
lean_ctor_set_uint8(v_cfg_1717_, sizeof(void*)*1, v___x_1713_);
lean_ctor_set_uint8(v_cfg_1717_, sizeof(void*)*1 + 1, v___x_1713_);
lean_ctor_set_uint8(v_cfg_1717_, sizeof(void*)*1 + 2, v___x_1713_);
lean_ctor_set_uint8(v_cfg_1717_, sizeof(void*)*1 + 3, v___x_1711_);
v___x_1718_ = lean_box(0);
v___x_1719_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___closed__4));
v___x_1720_ = l_Lean_Meta_SolveByElim_mkAssumptionSet(v___x_1711_, v___x_1711_, v___x_1718_, v___x_1718_, v___x_1719_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_);
if (lean_obj_tag(v___x_1720_) == 0)
{
lean_object* v_a_1721_; lean_object* v_fst_1722_; lean_object* v_snd_1723_; lean_object* v___x_1724_; 
v_a_1721_ = lean_ctor_get(v___x_1720_, 0);
lean_inc(v_a_1721_);
lean_dec_ref_known(v___x_1720_, 1);
v_fst_1722_ = lean_ctor_get(v_a_1721_, 0);
lean_inc(v_fst_1722_);
v_snd_1723_ = lean_ctor_get(v_a_1721_, 1);
lean_inc(v_snd_1723_);
lean_dec(v_a_1721_);
v___x_1724_ = l_Lean_Meta_SolveByElim_solveByElim(v_cfg_1717_, v_fst_1722_, v_snd_1723_, v_goals_1701_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_);
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_object* v_a_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1735_; 
v_a_1725_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1735_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1727_ = v___x_1724_;
v_isShared_1728_ = v_isSharedCheck_1735_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_a_1725_);
lean_dec(v___x_1724_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1735_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
if (lean_obj_tag(v_a_1725_) == 0)
{
lean_object* v___x_1729_; lean_object* v___x_1731_; 
v___x_1729_ = lean_box(0);
if (v_isShared_1728_ == 0)
{
lean_ctor_set(v___x_1727_, 0, v___x_1729_);
v___x_1731_ = v___x_1727_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v___x_1729_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
else
{
lean_object* v___x_1733_; lean_object* v___x_1734_; 
lean_del_object(v___x_1727_);
lean_dec(v_a_1725_);
v___x_1733_ = lean_obj_once(&l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1, &l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1_once, _init_l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1);
v___x_1734_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(v___x_1733_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_);
return v___x_1734_;
}
}
}
else
{
lean_object* v_a_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1743_; 
v_a_1736_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1738_ = v___x_1724_;
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_a_1736_);
lean_dec(v___x_1724_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v___x_1741_; 
if (v_isShared_1739_ == 0)
{
v___x_1741_ = v___x_1738_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_a_1736_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
return v___x_1741_;
}
}
}
}
else
{
lean_object* v_a_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1751_; 
lean_dec_ref_known(v_cfg_1717_, 1);
lean_dec(v_goals_1701_);
v_a_1744_ = lean_ctor_get(v___x_1720_, 0);
v_isSharedCheck_1751_ = !lean_is_exclusive(v___x_1720_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1746_ = v___x_1720_;
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_a_1744_);
lean_dec(v___x_1720_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1749_; 
if (v_isShared_1747_ == 0)
{
v___x_1749_ = v___x_1746_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_a_1744_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
return v___x_1749_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___boxed(lean_object* v_goals_1752_, lean_object* v_depth_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_){
_start:
{
lean_object* v_res_1759_; 
v_res_1759_ = l_Lean_Meta_Rewrites_solveByElim(v_goals_1752_, v_depth_1753_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_);
lean_dec(v_a_1757_);
lean_dec_ref(v_a_1756_);
lean_dec(v_a_1755_);
lean_dec_ref(v_a_1754_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0(lean_object* v_00_u03b1_1760_, lean_object* v_msg_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_){
_start:
{
lean_object* v___x_1767_; 
v___x_1767_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(v_msg_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_);
return v___x_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___boxed(lean_object* v_00_u03b1_1768_, lean_object* v_msg_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_){
_start:
{
lean_object* v_res_1775_; 
v_res_1775_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0(v_00_u03b1_1768_, v_msg_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_);
lean_dec(v___y_1773_);
lean_dec_ref(v___y_1772_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
return v_res_1775_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg(lean_object* v_e_1776_, lean_object* v___y_1777_){
_start:
{
uint8_t v___x_1779_; 
v___x_1779_ = l_Lean_Expr_hasMVar(v_e_1776_);
if (v___x_1779_ == 0)
{
lean_object* v___x_1780_; 
v___x_1780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1780_, 0, v_e_1776_);
return v___x_1780_;
}
else
{
lean_object* v___x_1781_; lean_object* v_mctx_1782_; lean_object* v___x_1783_; lean_object* v_fst_1784_; lean_object* v_snd_1785_; lean_object* v___x_1786_; lean_object* v_cache_1787_; lean_object* v_zetaDeltaFVarIds_1788_; lean_object* v_postponed_1789_; lean_object* v_diag_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1799_; 
v___x_1781_ = lean_st_ref_get(v___y_1777_);
v_mctx_1782_ = lean_ctor_get(v___x_1781_, 0);
lean_inc_ref(v_mctx_1782_);
lean_dec(v___x_1781_);
v___x_1783_ = l_Lean_instantiateMVarsCore(v_mctx_1782_, v_e_1776_);
v_fst_1784_ = lean_ctor_get(v___x_1783_, 0);
lean_inc(v_fst_1784_);
v_snd_1785_ = lean_ctor_get(v___x_1783_, 1);
lean_inc(v_snd_1785_);
lean_dec_ref(v___x_1783_);
v___x_1786_ = lean_st_ref_take(v___y_1777_);
v_cache_1787_ = lean_ctor_get(v___x_1786_, 1);
v_zetaDeltaFVarIds_1788_ = lean_ctor_get(v___x_1786_, 2);
v_postponed_1789_ = lean_ctor_get(v___x_1786_, 3);
v_diag_1790_ = lean_ctor_get(v___x_1786_, 4);
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1786_);
if (v_isSharedCheck_1799_ == 0)
{
lean_object* v_unused_1800_; 
v_unused_1800_ = lean_ctor_get(v___x_1786_, 0);
lean_dec(v_unused_1800_);
v___x_1792_ = v___x_1786_;
v_isShared_1793_ = v_isSharedCheck_1799_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_diag_1790_);
lean_inc(v_postponed_1789_);
lean_inc(v_zetaDeltaFVarIds_1788_);
lean_inc(v_cache_1787_);
lean_dec(v___x_1786_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1799_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v___x_1795_; 
if (v_isShared_1793_ == 0)
{
lean_ctor_set(v___x_1792_, 0, v_snd_1785_);
v___x_1795_ = v___x_1792_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_snd_1785_);
lean_ctor_set(v_reuseFailAlloc_1798_, 1, v_cache_1787_);
lean_ctor_set(v_reuseFailAlloc_1798_, 2, v_zetaDeltaFVarIds_1788_);
lean_ctor_set(v_reuseFailAlloc_1798_, 3, v_postponed_1789_);
lean_ctor_set(v_reuseFailAlloc_1798_, 4, v_diag_1790_);
v___x_1795_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1796_ = lean_st_ref_put(v___y_1777_, v___x_1795_);
v___x_1797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1797_, 0, v_fst_1784_);
return v___x_1797_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg___boxed(lean_object* v_e_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_){
_start:
{
lean_object* v_res_1804_; 
v_res_1804_ = l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg(v_e_1801_, v___y_1802_);
lean_dec(v___y_1802_);
return v_res_1804_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0(lean_object* v_e_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_){
_start:
{
lean_object* v___x_1811_; 
v___x_1811_ = l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg(v_e_1805_, v___y_1807_);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___boxed(lean_object* v_e_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_){
_start:
{
lean_object* v_res_1818_; 
v_res_1818_ = l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0(v_e_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
return v_res_1818_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1819_; double v___x_1820_; 
v___x_1819_ = lean_unsigned_to_nat(0u);
v___x_1820_ = lean_float_of_nat(v___x_1819_);
return v___x_1820_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2(lean_object* v_cls_1824_, lean_object* v_msg_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_){
_start:
{
lean_object* v_ref_1831_; lean_object* v___x_1832_; lean_object* v_a_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1878_; 
v_ref_1831_ = lean_ctor_get(v___y_1828_, 2);
v___x_1832_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0(v_msg_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_);
v_a_1833_ = lean_ctor_get(v___x_1832_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1832_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1835_ = v___x_1832_;
v_isShared_1836_ = v_isSharedCheck_1878_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_a_1833_);
lean_dec(v___x_1832_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1878_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1837_; lean_object* v_traceState_1838_; lean_object* v_env_1839_; lean_object* v_nextMacroScope_1840_; lean_object* v_ngen_1841_; lean_object* v_auxDeclNGen_1842_; lean_object* v_cache_1843_; lean_object* v_recordedDeps_1844_; lean_object* v_messages_1845_; lean_object* v_infoState_1846_; lean_object* v_snapshotTasks_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1877_; 
v___x_1837_ = lean_st_ref_take(v___y_1829_);
v_traceState_1838_ = lean_ctor_get(v___x_1837_, 4);
v_env_1839_ = lean_ctor_get(v___x_1837_, 0);
v_nextMacroScope_1840_ = lean_ctor_get(v___x_1837_, 1);
v_ngen_1841_ = lean_ctor_get(v___x_1837_, 2);
v_auxDeclNGen_1842_ = lean_ctor_get(v___x_1837_, 3);
v_cache_1843_ = lean_ctor_get(v___x_1837_, 5);
v_recordedDeps_1844_ = lean_ctor_get(v___x_1837_, 6);
v_messages_1845_ = lean_ctor_get(v___x_1837_, 7);
v_infoState_1846_ = lean_ctor_get(v___x_1837_, 8);
v_snapshotTasks_1847_ = lean_ctor_get(v___x_1837_, 9);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1849_ = v___x_1837_;
v_isShared_1850_ = v_isSharedCheck_1877_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_snapshotTasks_1847_);
lean_inc(v_infoState_1846_);
lean_inc(v_messages_1845_);
lean_inc(v_recordedDeps_1844_);
lean_inc(v_cache_1843_);
lean_inc(v_traceState_1838_);
lean_inc(v_auxDeclNGen_1842_);
lean_inc(v_ngen_1841_);
lean_inc(v_nextMacroScope_1840_);
lean_inc(v_env_1839_);
lean_dec(v___x_1837_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1877_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
uint64_t v_tid_1851_; lean_object* v_traces_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1876_; 
v_tid_1851_ = lean_ctor_get_uint64(v_traceState_1838_, sizeof(void*)*1);
v_traces_1852_ = lean_ctor_get(v_traceState_1838_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v_traceState_1838_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1854_ = v_traceState_1838_;
v_isShared_1855_ = v_isSharedCheck_1876_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_traces_1852_);
lean_dec(v_traceState_1838_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1876_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; double v___x_1858_; uint8_t v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1867_; 
v___x_1856_ = lean_box(0);
v___x_1857_ = lean_box(0);
v___x_1858_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__0);
v___x_1859_ = 0;
v___x_1860_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__1));
v___x_1861_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1861_, 0, v_cls_1824_);
lean_ctor_set(v___x_1861_, 1, v___x_1857_);
lean_ctor_set(v___x_1861_, 2, v___x_1860_);
lean_ctor_set_float(v___x_1861_, sizeof(void*)*3, v___x_1858_);
lean_ctor_set_float(v___x_1861_, sizeof(void*)*3 + 8, v___x_1858_);
lean_ctor_set_uint8(v___x_1861_, sizeof(void*)*3 + 16, v___x_1859_);
v___x_1862_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__2));
v___x_1863_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1861_);
lean_ctor_set(v___x_1863_, 1, v_a_1833_);
lean_ctor_set(v___x_1863_, 2, v___x_1862_);
lean_inc(v_ref_1831_);
v___x_1864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1864_, 0, v_ref_1831_);
lean_ctor_set(v___x_1864_, 1, v___x_1863_);
v___x_1865_ = l_Lean_PersistentArray_push___redArg(v_traces_1852_, v___x_1864_);
if (v_isShared_1855_ == 0)
{
lean_ctor_set(v___x_1854_, 0, v___x_1865_);
v___x_1867_ = v___x_1854_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v___x_1865_);
lean_ctor_set_uint64(v_reuseFailAlloc_1875_, sizeof(void*)*1, v_tid_1851_);
v___x_1867_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
lean_object* v___x_1869_; 
if (v_isShared_1850_ == 0)
{
lean_ctor_set(v___x_1849_, 4, v___x_1867_);
v___x_1869_ = v___x_1849_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_env_1839_);
lean_ctor_set(v_reuseFailAlloc_1874_, 1, v_nextMacroScope_1840_);
lean_ctor_set(v_reuseFailAlloc_1874_, 2, v_ngen_1841_);
lean_ctor_set(v_reuseFailAlloc_1874_, 3, v_auxDeclNGen_1842_);
lean_ctor_set(v_reuseFailAlloc_1874_, 4, v___x_1867_);
lean_ctor_set(v_reuseFailAlloc_1874_, 5, v_cache_1843_);
lean_ctor_set(v_reuseFailAlloc_1874_, 6, v_recordedDeps_1844_);
lean_ctor_set(v_reuseFailAlloc_1874_, 7, v_messages_1845_);
lean_ctor_set(v_reuseFailAlloc_1874_, 8, v_infoState_1846_);
lean_ctor_set(v_reuseFailAlloc_1874_, 9, v_snapshotTasks_1847_);
v___x_1869_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
lean_object* v___x_1870_; lean_object* v___x_1872_; 
v___x_1870_ = lean_st_ref_put(v___y_1829_, v___x_1869_);
if (v_isShared_1836_ == 0)
{
lean_ctor_set(v___x_1835_, 0, v___x_1856_);
v___x_1872_ = v___x_1835_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v___x_1856_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
return v___x_1872_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___boxed(lean_object* v_cls_1879_, lean_object* v_msg_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_){
_start:
{
lean_object* v_res_1886_; 
v_res_1886_ = l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2(v_cls_1879_, v_msg_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Rewrites_rwLemma_spec__1(lean_object* v_x_1887_, lean_object* v_x_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_){
_start:
{
if (lean_obj_tag(v_x_1887_) == 0)
{
lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___x_1894_ = l_List_reverse___redArg(v_x_1888_);
v___x_1895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1894_);
return v___x_1895_;
}
else
{
lean_object* v_head_1896_; lean_object* v_tail_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1915_; 
v_head_1896_ = lean_ctor_get(v_x_1887_, 0);
v_tail_1897_ = lean_ctor_get(v_x_1887_, 1);
v_isSharedCheck_1915_ = !lean_is_exclusive(v_x_1887_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1899_ = v_x_1887_;
v_isShared_1900_ = v_isSharedCheck_1915_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_tail_1897_);
lean_inc(v_head_1896_);
lean_dec(v_x_1887_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1915_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1901_; 
v___x_1901_ = l_Lean_MVarId_assumption(v_head_1896_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v_a_1902_; lean_object* v___x_1904_; 
v_a_1902_ = lean_ctor_get(v___x_1901_, 0);
lean_inc(v_a_1902_);
lean_dec_ref_known(v___x_1901_, 1);
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 1, v_x_1888_);
lean_ctor_set(v___x_1899_, 0, v_a_1902_);
v___x_1904_ = v___x_1899_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v_a_1902_);
lean_ctor_set(v_reuseFailAlloc_1906_, 1, v_x_1888_);
v___x_1904_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
v_x_1887_ = v_tail_1897_;
v_x_1888_ = v___x_1904_;
goto _start;
}
}
else
{
lean_object* v_a_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1914_; 
lean_del_object(v___x_1899_);
lean_dec(v_tail_1897_);
lean_dec(v_x_1888_);
v_a_1907_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1909_ = v___x_1901_;
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_a_1907_);
lean_dec(v___x_1901_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1912_; 
if (v_isShared_1910_ == 0)
{
v___x_1912_ = v___x_1909_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_a_1907_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Rewrites_rwLemma_spec__1___boxed(lean_object* v_x_1916_, lean_object* v_x_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_){
_start:
{
lean_object* v_res_1923_; 
v_res_1923_ = l_List_mapM_loop___at___00Lean_Meta_Rewrites_rwLemma_spec__1(v_x_1916_, v_x_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_);
lean_dec(v___y_1921_);
lean_dec_ref(v___y_1920_);
lean_dec(v___y_1919_);
lean_dec_ref(v___y_1918_);
return v_res_1923_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5(void){
_start:
{
lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; 
v___x_1936_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_));
v___x_1937_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__4));
v___x_1938_ = l_Lean_Name_append(v___x_1937_, v___x_1936_);
return v___x_1938_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__7(void){
_start:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; 
v___x_1940_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__6));
v___x_1941_ = l_Lean_stringToMessageData(v___x_1940_);
return v___x_1941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0(lean_object* v_weight_1943_, lean_object* v_goal_1944_, lean_object* v_target_1945_, uint8_t v_symm_1946_, uint8_t v_side_1947_, lean_object* v_lem_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_){
_start:
{
lean_object* v___y_1955_; lean_object* v___y_1956_; lean_object* v___y_1957_; lean_object* v___y_1958_; uint8_t v___y_1959_; lean_object* v___y_1980_; lean_object* v___y_1981_; lean_object* v___y_1982_; lean_object* v___y_1983_; lean_object* v___y_1984_; lean_object* v_fst_1985_; uint8_t v_snd_1986_; uint8_t v___y_2011_; lean_object* v___y_2012_; lean_object* v___y_2013_; lean_object* v___y_2014_; lean_object* v___y_2015_; lean_object* v___y_2016_; uint8_t v___y_2033_; lean_object* v___y_2034_; uint8_t v_discharge_2035_; lean_object* v___y_2036_; lean_object* v___y_2037_; lean_object* v___y_2038_; lean_object* v___y_2039_; uint8_t v___y_2043_; lean_object* v___y_2044_; uint8_t v___y_2045_; lean_object* v___y_2046_; lean_object* v___y_2047_; lean_object* v___y_2048_; lean_object* v___y_2049_; lean_object* v___y_2050_; lean_object* v___y_2051_; uint8_t v___y_2052_; lean_object* v___y_2064_; uint8_t v___y_2065_; lean_object* v___y_2066_; uint8_t v___y_2067_; lean_object* v___y_2068_; lean_object* v___y_2069_; lean_object* v___y_2070_; lean_object* v___y_2071_; lean_object* v___y_2072_; uint8_t v___y_2073_; lean_object* v___y_2085_; lean_object* v___y_2165_; lean_object* v___y_2166_; lean_object* v___y_2167_; lean_object* v___y_2168_; lean_object* v_val_2183_; 
if (lean_obj_tag(v_lem_1948_) == 0)
{
lean_object* v_val_2194_; 
v_val_2194_ = lean_ctor_get(v_lem_1948_, 0);
lean_inc(v_val_2194_);
lean_dec_ref_known(v_lem_1948_, 1);
v_val_2183_ = v_val_2194_;
goto v___jp_2182_;
}
else
{
lean_object* v_val_2195_; lean_object* v___x_2196_; 
v_val_2195_ = lean_ctor_get(v_lem_1948_, 0);
lean_inc(v_val_2195_);
lean_dec_ref_known(v_lem_1948_, 1);
v___x_2196_ = l_Lean_Meta_saveState___redArg(v___y_1950_, v___y_1952_);
if (lean_obj_tag(v___x_2196_) == 0)
{
lean_object* v_a_2197_; lean_object* v___x_2198_; 
v_a_2197_ = lean_ctor_get(v___x_2196_, 0);
lean_inc(v_a_2197_);
lean_dec_ref_known(v___x_2196_, 1);
v___x_2198_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_val_2195_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_);
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_object* v_a_2199_; 
lean_dec(v_a_2197_);
v_a_2199_ = lean_ctor_get(v___x_2198_, 0);
lean_inc(v_a_2199_);
lean_dec_ref_known(v___x_2198_, 1);
v_val_2183_ = v_a_2199_;
goto v___jp_2182_;
}
else
{
lean_object* v_a_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2229_; 
lean_dec_ref(v_target_1945_);
lean_dec(v_goal_1944_);
lean_dec(v_weight_1943_);
v_a_2200_ = lean_ctor_get(v___x_2198_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2202_ = v___x_2198_;
v_isShared_2203_ = v_isSharedCheck_2229_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_a_2200_);
lean_dec(v___x_2198_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2229_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
uint8_t v___y_2205_; uint8_t v___x_2227_; 
v___x_2227_ = l_Lean_Exception_isInterrupt(v_a_2200_);
if (v___x_2227_ == 0)
{
uint8_t v___x_2228_; 
lean_inc(v_a_2200_);
v___x_2228_ = l_Lean_Exception_isRuntime(v_a_2200_);
v___y_2205_ = v___x_2228_;
goto v___jp_2204_;
}
else
{
v___y_2205_ = v___x_2227_;
goto v___jp_2204_;
}
v___jp_2204_:
{
if (v___y_2205_ == 0)
{
lean_object* v___x_2206_; 
lean_del_object(v___x_2202_);
lean_dec(v_a_2200_);
v___x_2206_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2197_, v___y_1950_, v___y_1952_);
lean_dec(v_a_2197_);
if (lean_obj_tag(v___x_2206_) == 0)
{
lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2214_; 
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2206_);
if (v_isSharedCheck_2214_ == 0)
{
lean_object* v_unused_2215_; 
v_unused_2215_ = lean_ctor_get(v___x_2206_, 0);
lean_dec(v_unused_2215_);
v___x_2208_ = v___x_2206_;
v_isShared_2209_ = v_isSharedCheck_2214_;
goto v_resetjp_2207_;
}
else
{
lean_dec(v___x_2206_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2214_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2210_; lean_object* v___x_2212_; 
v___x_2210_ = lean_box(0);
if (v_isShared_2209_ == 0)
{
lean_ctor_set(v___x_2208_, 0, v___x_2210_);
v___x_2212_ = v___x_2208_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v___x_2210_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
else
{
lean_object* v_a_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2223_; 
v_a_2216_ = lean_ctor_get(v___x_2206_, 0);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2206_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2218_ = v___x_2206_;
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_a_2216_);
lean_dec(v___x_2206_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2221_; 
if (v_isShared_2219_ == 0)
{
v___x_2221_ = v___x_2218_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_a_2216_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
}
}
}
}
else
{
lean_object* v___x_2225_; 
lean_dec(v_a_2197_);
if (v_isShared_2203_ == 0)
{
v___x_2225_ = v___x_2202_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_a_2200_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
}
}
}
}
else
{
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2237_; 
lean_dec(v_val_2195_);
lean_dec_ref(v_target_1945_);
lean_dec(v_goal_1944_);
lean_dec(v_weight_1943_);
v_a_2230_ = lean_ctor_get(v___x_2196_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___x_2196_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2232_ = v___x_2196_;
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___x_2196_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2235_; 
if (v_isShared_2233_ == 0)
{
v___x_2235_ = v___x_2232_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_a_2230_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
}
}
v___jp_1954_:
{
if (v___y_1959_ == 0)
{
lean_object* v___x_1960_; 
lean_dec_ref(v___y_1955_);
v___x_1960_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1956_, v___y_1958_, v___y_1957_);
lean_dec_ref(v___y_1956_);
if (lean_obj_tag(v___x_1960_) == 0)
{
lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1968_; 
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_1968_ == 0)
{
lean_object* v_unused_1969_; 
v_unused_1969_ = lean_ctor_get(v___x_1960_, 0);
lean_dec(v_unused_1969_);
v___x_1962_ = v___x_1960_;
v_isShared_1963_ = v_isSharedCheck_1968_;
goto v_resetjp_1961_;
}
else
{
lean_dec(v___x_1960_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1968_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v___x_1964_; lean_object* v___x_1966_; 
v___x_1964_ = lean_box(0);
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 0, v___x_1964_);
v___x_1966_ = v___x_1962_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v___x_1964_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
return v___x_1966_;
}
}
}
else
{
lean_object* v_a_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1977_; 
v_a_1970_ = lean_ctor_get(v___x_1960_, 0);
v_isSharedCheck_1977_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1972_ = v___x_1960_;
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_a_1970_);
lean_dec(v___x_1960_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1975_; 
if (v_isShared_1973_ == 0)
{
v___x_1975_ = v___x_1972_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_a_1970_);
v___x_1975_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
return v___x_1975_;
}
}
}
}
else
{
lean_object* v___x_1978_; 
lean_dec_ref(v___y_1956_);
v___x_1978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1978_, 0, v___y_1955_);
return v___x_1978_;
}
}
v___jp_1979_:
{
lean_object* v___x_1987_; lean_object* v_mctx_1988_; lean_object* v_eNew_1989_; lean_object* v___x_1990_; 
v___x_1987_ = lean_st_ref_get(v___y_1981_);
v_mctx_1988_ = lean_ctor_get(v___x_1987_, 0);
lean_inc_ref_n(v_mctx_1988_, 2);
lean_dec(v___x_1987_);
v_eNew_1989_ = lean_ctor_get(v___y_1984_, 0);
lean_inc_ref(v_eNew_1989_);
v___x_1990_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(v_mctx_1988_, v_eNew_1989_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_);
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_object* v_a_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_2001_; 
v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1993_ = v___x_1990_;
v_isShared_1994_ = v_isSharedCheck_2001_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_a_1991_);
lean_dec(v___x_1990_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_2001_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v___x_1995_; uint8_t v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1999_; 
v___x_1995_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1995_, 0, v_fst_1985_);
lean_ctor_set(v___x_1995_, 1, v_weight_1943_);
lean_ctor_set(v___x_1995_, 2, v___y_1984_);
lean_ctor_set(v___x_1995_, 3, v_mctx_1988_);
lean_ctor_set_uint8(v___x_1995_, sizeof(void*)*4, v_snd_1986_);
v___x_1996_ = lean_unbox(v_a_1991_);
lean_dec(v_a_1991_);
lean_ctor_set_uint8(v___x_1995_, sizeof(void*)*4 + 1, v___x_1996_);
v___x_1997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1997_, 0, v___x_1995_);
if (v_isShared_1994_ == 0)
{
lean_ctor_set(v___x_1993_, 0, v___x_1997_);
v___x_1999_ = v___x_1993_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v___x_1997_);
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
lean_dec_ref(v_mctx_1988_);
lean_dec_ref(v_fst_1985_);
lean_dec_ref(v___y_1984_);
lean_dec(v_weight_1943_);
v_a_2002_ = lean_ctor_get(v___x_1990_, 0);
v_isSharedCheck_2009_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_2004_ = v___x_1990_;
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_a_2002_);
lean_dec(v___x_1990_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v___x_2007_; 
if (v_isShared_2005_ == 0)
{
v___x_2007_ = v___x_2004_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(1, 1, 0);
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
v___jp_2010_:
{
lean_object* v___x_2017_; 
v___x_2017_ = l_Lean_Meta_Rewrites_rewriteResultLemma(v___y_2012_);
if (lean_obj_tag(v___x_2017_) == 1)
{
lean_object* v_val_2018_; lean_object* v___x_2019_; lean_object* v_a_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; uint8_t v___x_2023_; 
v_val_2018_ = lean_ctor_get(v___x_2017_, 0);
lean_inc(v_val_2018_);
lean_dec_ref_known(v___x_2017_, 1);
v___x_2019_ = l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg(v_val_2018_, v___y_2014_);
v_a_2020_ = lean_ctor_get(v___x_2019_, 0);
lean_inc(v_a_2020_);
lean_dec_ref(v___x_2019_);
v___x_2021_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__1));
v___x_2022_ = lean_unsigned_to_nat(4u);
v___x_2023_ = l_Lean_Expr_isAppOfArity(v_a_2020_, v___x_2021_, v___x_2022_);
if (v___x_2023_ == 0)
{
v___y_1980_ = v___y_2013_;
v___y_1981_ = v___y_2014_;
v___y_1982_ = v___y_2015_;
v___y_1983_ = v___y_2016_;
v___y_1984_ = v___y_2012_;
v_fst_1985_ = v_a_2020_;
v_snd_1986_ = v___x_2023_;
goto v___jp_1979_;
}
else
{
lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; 
v___x_2024_ = lean_unsigned_to_nat(3u);
v___x_2025_ = l_Lean_Expr_getAppNumArgs(v_a_2020_);
v___x_2026_ = lean_nat_sub(v___x_2025_, v___x_2024_);
lean_dec(v___x_2025_);
v___x_2027_ = lean_unsigned_to_nat(1u);
v___x_2028_ = lean_nat_sub(v___x_2026_, v___x_2027_);
lean_dec(v___x_2026_);
v___x_2029_ = l_Lean_Expr_getRevArg_x21(v_a_2020_, v___x_2028_);
lean_dec(v_a_2020_);
v___y_1980_ = v___y_2013_;
v___y_1981_ = v___y_2014_;
v___y_1982_ = v___y_2015_;
v___y_1983_ = v___y_2016_;
v___y_1984_ = v___y_2012_;
v_fst_1985_ = v___x_2029_;
v_snd_1986_ = v___y_2011_;
goto v___jp_1979_;
}
}
else
{
lean_object* v___x_2030_; lean_object* v___x_2031_; 
lean_dec(v___x_2017_);
lean_dec_ref(v___y_2012_);
lean_dec(v_weight_1943_);
v___x_2030_ = lean_box(0);
v___x_2031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2031_, 0, v___x_2030_);
return v___x_2031_;
}
}
v___jp_2032_:
{
if (v_discharge_2035_ == 0)
{
lean_object* v___x_2040_; lean_object* v___x_2041_; 
lean_dec_ref(v___y_2034_);
lean_dec(v_weight_1943_);
v___x_2040_ = lean_box(0);
v___x_2041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2041_, 0, v___x_2040_);
return v___x_2041_;
}
else
{
v___y_2011_ = v___y_2033_;
v___y_2012_ = v___y_2034_;
v___y_2013_ = v___y_2036_;
v___y_2014_ = v___y_2037_;
v___y_2015_ = v___y_2038_;
v___y_2016_ = v___y_2039_;
goto v___jp_2010_;
}
}
v___jp_2042_:
{
if (v___y_2052_ == 0)
{
lean_object* v___x_2053_; 
lean_dec_ref(v___y_2051_);
v___x_2053_ = l_Lean_Meta_SavedState_restore___redArg(v___y_2050_, v___y_2049_, v___y_2047_);
lean_dec_ref(v___y_2050_);
if (lean_obj_tag(v___x_2053_) == 0)
{
lean_dec_ref_known(v___x_2053_, 1);
v___y_2033_ = v___y_2043_;
v___y_2034_ = v___y_2046_;
v_discharge_2035_ = v___y_2045_;
v___y_2036_ = v___y_2048_;
v___y_2037_ = v___y_2049_;
v___y_2038_ = v___y_2044_;
v___y_2039_ = v___y_2047_;
goto v___jp_2032_;
}
else
{
lean_object* v_a_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2061_; 
lean_dec_ref(v___y_2046_);
lean_dec(v_weight_1943_);
v_a_2054_ = lean_ctor_get(v___x_2053_, 0);
v_isSharedCheck_2061_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2061_ == 0)
{
v___x_2056_ = v___x_2053_;
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_a_2054_);
lean_dec(v___x_2053_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v___x_2059_; 
if (v_isShared_2057_ == 0)
{
v___x_2059_ = v___x_2056_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v_a_2054_);
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
else
{
lean_object* v___x_2062_; 
lean_dec_ref(v___y_2050_);
lean_dec_ref(v___y_2046_);
lean_dec(v_weight_1943_);
v___x_2062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2062_, 0, v___y_2051_);
return v___x_2062_;
}
}
v___jp_2063_:
{
if (v___y_2073_ == 0)
{
lean_object* v___x_2074_; 
lean_dec_ref(v___y_2072_);
v___x_2074_ = l_Lean_Meta_SavedState_restore___redArg(v___y_2064_, v___y_2071_, v___y_2069_);
lean_dec_ref(v___y_2064_);
if (lean_obj_tag(v___x_2074_) == 0)
{
lean_dec_ref_known(v___x_2074_, 1);
v___y_2033_ = v___y_2065_;
v___y_2034_ = v___y_2068_;
v_discharge_2035_ = v___y_2067_;
v___y_2036_ = v___y_2070_;
v___y_2037_ = v___y_2071_;
v___y_2038_ = v___y_2066_;
v___y_2039_ = v___y_2069_;
goto v___jp_2032_;
}
else
{
lean_object* v_a_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2082_; 
lean_dec_ref(v___y_2068_);
lean_dec(v_weight_1943_);
v_a_2075_ = lean_ctor_get(v___x_2074_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_2074_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2077_ = v___x_2074_;
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_a_2075_);
lean_dec(v___x_2074_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2080_; 
if (v_isShared_2078_ == 0)
{
v___x_2080_ = v___x_2077_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_a_2075_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
}
}
else
{
lean_object* v___x_2083_; 
lean_dec_ref(v___y_2068_);
lean_dec_ref(v___y_2064_);
lean_dec(v_weight_1943_);
v___x_2083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2083_, 0, v___y_2072_);
return v___x_2083_;
}
}
v___jp_2084_:
{
uint8_t v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2086_ = 1;
v___x_2087_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__2));
v___x_2088_ = l_Lean_Meta_saveState___redArg(v___y_1950_, v___y_1952_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v_a_2089_; lean_object* v___x_2090_; 
v_a_2089_ = lean_ctor_get(v___x_2088_, 0);
lean_inc(v_a_2089_);
lean_dec_ref_known(v___x_2088_, 1);
lean_inc_ref(v___y_2085_);
v___x_2090_ = l_Lean_MVarId_rewrite(v_goal_1944_, v_target_1945_, v___y_2085_, v_symm_1946_, v___x_2087_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_);
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_object* v_a_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2152_; 
lean_dec(v_a_2089_);
v_a_2091_ = lean_ctor_get(v___x_2090_, 0);
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2093_ = v___x_2090_;
v_isShared_2094_ = v_isSharedCheck_2152_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_a_2091_);
lean_dec(v___x_2090_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2152_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v_eNew_2095_; lean_object* v_mvarIds_2096_; uint8_t v___x_2097_; 
v_eNew_2095_ = lean_ctor_get(v_a_2091_, 0);
v_mvarIds_2096_ = lean_ctor_get(v_a_2091_, 2);
v___x_2097_ = l_List_isEmpty___redArg(v_mvarIds_2096_);
if (v___x_2097_ == 0)
{
lean_del_object(v___x_2093_);
lean_dec_ref(v___y_2085_);
switch(v_side_1947_)
{
case 0:
{
v___y_2033_ = v___x_2086_;
v___y_2034_ = v_a_2091_;
v_discharge_2035_ = v___x_2097_;
v___y_2036_ = v___y_1949_;
v___y_2037_ = v___y_1950_;
v___y_2038_ = v___y_1951_;
v___y_2039_ = v___y_1952_;
goto v___jp_2032_;
}
case 1:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2098_ = lean_box(0);
v___x_2099_ = l_Lean_Meta_saveState___redArg(v___y_1950_, v___y_1952_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_object* v_a_2100_; lean_object* v___x_2101_; 
v_a_2100_ = lean_ctor_get(v___x_2099_, 0);
lean_inc(v_a_2100_);
lean_dec_ref_known(v___x_2099_, 1);
lean_inc(v_mvarIds_2096_);
v___x_2101_ = l_List_mapM_loop___at___00Lean_Meta_Rewrites_rwLemma_spec__1(v_mvarIds_2096_, v___x_2098_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_);
if (lean_obj_tag(v___x_2101_) == 0)
{
lean_dec_ref_known(v___x_2101_, 1);
lean_dec(v_a_2100_);
v___y_2011_ = v___x_2086_;
v___y_2012_ = v_a_2091_;
v___y_2013_ = v___y_1949_;
v___y_2014_ = v___y_1950_;
v___y_2015_ = v___y_1951_;
v___y_2016_ = v___y_1952_;
goto v___jp_2010_;
}
else
{
lean_object* v_a_2102_; uint8_t v___x_2103_; 
v_a_2102_ = lean_ctor_get(v___x_2101_, 0);
lean_inc(v_a_2102_);
lean_dec_ref_known(v___x_2101_, 1);
v___x_2103_ = l_Lean_Exception_isInterrupt(v_a_2102_);
if (v___x_2103_ == 0)
{
uint8_t v___x_2104_; 
lean_inc(v_a_2102_);
v___x_2104_ = l_Lean_Exception_isRuntime(v_a_2102_);
v___y_2064_ = v_a_2100_;
v___y_2065_ = v___x_2086_;
v___y_2066_ = v___y_1951_;
v___y_2067_ = v___x_2097_;
v___y_2068_ = v_a_2091_;
v___y_2069_ = v___y_1952_;
v___y_2070_ = v___y_1949_;
v___y_2071_ = v___y_1950_;
v___y_2072_ = v_a_2102_;
v___y_2073_ = v___x_2104_;
goto v___jp_2063_;
}
else
{
v___y_2064_ = v_a_2100_;
v___y_2065_ = v___x_2086_;
v___y_2066_ = v___y_1951_;
v___y_2067_ = v___x_2097_;
v___y_2068_ = v_a_2091_;
v___y_2069_ = v___y_1952_;
v___y_2070_ = v___y_1949_;
v___y_2071_ = v___y_1950_;
v___y_2072_ = v_a_2102_;
v___y_2073_ = v___x_2103_;
goto v___jp_2063_;
}
}
}
else
{
lean_object* v_a_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2112_; 
lean_dec(v_a_2091_);
lean_dec(v_weight_1943_);
v_a_2105_ = lean_ctor_get(v___x_2099_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2107_ = v___x_2099_;
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_a_2105_);
lean_dec(v___x_2099_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2110_; 
if (v_isShared_2108_ == 0)
{
v___x_2110_ = v___x_2107_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_a_2105_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
}
}
default: 
{
lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2113_ = lean_unsigned_to_nat(6u);
v___x_2114_ = l_Lean_Meta_saveState___redArg(v___y_1950_, v___y_1952_);
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_object* v_a_2115_; lean_object* v___x_2116_; 
v_a_2115_ = lean_ctor_get(v___x_2114_, 0);
lean_inc(v_a_2115_);
lean_dec_ref_known(v___x_2114_, 1);
lean_inc(v_mvarIds_2096_);
v___x_2116_ = l_Lean_Meta_Rewrites_solveByElim(v_mvarIds_2096_, v___x_2113_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_dec_ref_known(v___x_2116_, 1);
lean_dec(v_a_2115_);
v___y_2011_ = v___x_2086_;
v___y_2012_ = v_a_2091_;
v___y_2013_ = v___y_1949_;
v___y_2014_ = v___y_1950_;
v___y_2015_ = v___y_1951_;
v___y_2016_ = v___y_1952_;
goto v___jp_2010_;
}
else
{
lean_object* v_a_2117_; uint8_t v___x_2118_; 
v_a_2117_ = lean_ctor_get(v___x_2116_, 0);
lean_inc(v_a_2117_);
lean_dec_ref_known(v___x_2116_, 1);
v___x_2118_ = l_Lean_Exception_isInterrupt(v_a_2117_);
if (v___x_2118_ == 0)
{
uint8_t v___x_2119_; 
lean_inc(v_a_2117_);
v___x_2119_ = l_Lean_Exception_isRuntime(v_a_2117_);
v___y_2043_ = v___x_2086_;
v___y_2044_ = v___y_1951_;
v___y_2045_ = v___x_2097_;
v___y_2046_ = v_a_2091_;
v___y_2047_ = v___y_1952_;
v___y_2048_ = v___y_1949_;
v___y_2049_ = v___y_1950_;
v___y_2050_ = v_a_2115_;
v___y_2051_ = v_a_2117_;
v___y_2052_ = v___x_2119_;
goto v___jp_2042_;
}
else
{
v___y_2043_ = v___x_2086_;
v___y_2044_ = v___y_1951_;
v___y_2045_ = v___x_2097_;
v___y_2046_ = v_a_2091_;
v___y_2047_ = v___y_1952_;
v___y_2048_ = v___y_1949_;
v___y_2049_ = v___y_1950_;
v___y_2050_ = v_a_2115_;
v___y_2051_ = v_a_2117_;
v___y_2052_ = v___x_2118_;
goto v___jp_2042_;
}
}
}
else
{
lean_object* v_a_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2127_; 
lean_dec(v_a_2091_);
lean_dec(v_weight_1943_);
v_a_2120_ = lean_ctor_get(v___x_2114_, 0);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2122_ = v___x_2114_;
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_a_2120_);
lean_dec(v___x_2114_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2125_; 
if (v_isShared_2123_ == 0)
{
v___x_2125_ = v___x_2122_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_a_2120_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
}
}
}
else
{
lean_object* v___x_2128_; lean_object* v_mctx_2129_; lean_object* v___x_2130_; 
v___x_2128_ = lean_st_ref_get(v___y_1950_);
v_mctx_2129_ = lean_ctor_get(v___x_2128_, 0);
lean_inc_ref_n(v_mctx_2129_, 2);
lean_dec(v___x_2128_);
lean_inc_ref(v_eNew_2095_);
v___x_2130_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(v_mctx_2129_, v_eNew_2095_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v_a_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2143_; 
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2133_ = v___x_2130_;
v_isShared_2134_ = v_isSharedCheck_2143_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_a_2131_);
lean_dec(v___x_2130_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2143_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v___x_2135_; uint8_t v___x_2136_; lean_object* v___x_2138_; 
v___x_2135_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2135_, 0, v___y_2085_);
lean_ctor_set(v___x_2135_, 1, v_weight_1943_);
lean_ctor_set(v___x_2135_, 2, v_a_2091_);
lean_ctor_set(v___x_2135_, 3, v_mctx_2129_);
lean_ctor_set_uint8(v___x_2135_, sizeof(void*)*4, v_symm_1946_);
v___x_2136_ = lean_unbox(v_a_2131_);
lean_dec(v_a_2131_);
lean_ctor_set_uint8(v___x_2135_, sizeof(void*)*4 + 1, v___x_2136_);
if (v_isShared_2094_ == 0)
{
lean_ctor_set_tag(v___x_2093_, 1);
lean_ctor_set(v___x_2093_, 0, v___x_2135_);
v___x_2138_ = v___x_2093_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v___x_2135_);
v___x_2138_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
lean_object* v___x_2140_; 
if (v_isShared_2134_ == 0)
{
lean_ctor_set(v___x_2133_, 0, v___x_2138_);
v___x_2140_ = v___x_2133_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v___x_2138_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
}
}
else
{
lean_object* v_a_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2151_; 
lean_dec_ref(v_mctx_2129_);
lean_del_object(v___x_2093_);
lean_dec(v_a_2091_);
lean_dec_ref(v___y_2085_);
lean_dec(v_weight_1943_);
v_a_2144_ = lean_ctor_get(v___x_2130_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2146_ = v___x_2130_;
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_a_2144_);
lean_dec(v___x_2130_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2149_; 
if (v_isShared_2147_ == 0)
{
v___x_2149_ = v___x_2146_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v_a_2144_);
v___x_2149_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
return v___x_2149_;
}
}
}
}
}
}
else
{
lean_object* v_a_2153_; uint8_t v___x_2154_; 
lean_dec_ref(v___y_2085_);
lean_dec(v_weight_1943_);
v_a_2153_ = lean_ctor_get(v___x_2090_, 0);
lean_inc(v_a_2153_);
lean_dec_ref_known(v___x_2090_, 1);
v___x_2154_ = l_Lean_Exception_isInterrupt(v_a_2153_);
if (v___x_2154_ == 0)
{
uint8_t v___x_2155_; 
lean_inc(v_a_2153_);
v___x_2155_ = l_Lean_Exception_isRuntime(v_a_2153_);
v___y_1955_ = v_a_2153_;
v___y_1956_ = v_a_2089_;
v___y_1957_ = v___y_1952_;
v___y_1958_ = v___y_1950_;
v___y_1959_ = v___x_2155_;
goto v___jp_1954_;
}
else
{
v___y_1955_ = v_a_2153_;
v___y_1956_ = v_a_2089_;
v___y_1957_ = v___y_1952_;
v___y_1958_ = v___y_1950_;
v___y_1959_ = v___x_2154_;
goto v___jp_1954_;
}
}
}
else
{
lean_object* v_a_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2163_; 
lean_dec_ref(v___y_2085_);
lean_dec_ref(v_target_1945_);
lean_dec(v_goal_1944_);
lean_dec(v_weight_1943_);
v_a_2156_ = lean_ctor_get(v___x_2088_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2158_ = v___x_2088_;
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_a_2156_);
lean_dec(v___x_2088_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v___x_2161_; 
if (v_isShared_2159_ == 0)
{
v___x_2161_ = v___x_2158_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v_a_2156_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
}
v___jp_2164_:
{
lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; 
lean_inc_ref(v___y_2168_);
v___x_2169_ = l_Lean_stringToMessageData(v___y_2168_);
lean_inc_ref(v___y_2167_);
v___x_2170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2170_, 0, v___y_2167_);
lean_ctor_set(v___x_2170_, 1, v___x_2169_);
lean_inc_ref(v___y_2166_);
v___x_2171_ = l_Lean_MessageData_ofExpr(v___y_2166_);
v___x_2172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2172_, 0, v___x_2170_);
lean_ctor_set(v___x_2172_, 1, v___x_2171_);
lean_inc(v___y_2165_);
v___x_2173_ = l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2(v___y_2165_, v___x_2172_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_);
if (lean_obj_tag(v___x_2173_) == 0)
{
lean_dec_ref_known(v___x_2173_, 1);
v___y_2085_ = v___y_2166_;
goto v___jp_2084_;
}
else
{
lean_object* v_a_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2181_; 
lean_dec_ref(v___y_2166_);
lean_dec_ref(v_target_1945_);
lean_dec(v_goal_1944_);
lean_dec(v_weight_1943_);
v_a_2174_ = lean_ctor_get(v___x_2173_, 0);
v_isSharedCheck_2181_ = !lean_is_exclusive(v___x_2173_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2176_ = v___x_2173_;
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_a_2174_);
lean_dec(v___x_2173_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2179_; 
if (v_isShared_2177_ == 0)
{
v___x_2179_ = v___x_2176_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_a_2174_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
return v___x_2179_;
}
}
}
}
v___jp_2182_:
{
lean_object* v_toCold_2184_; lean_object* v_options_2185_; uint8_t v_hasTrace_2186_; 
v_toCold_2184_ = lean_ctor_get(v___y_1951_, 0);
v_options_2185_ = lean_ctor_get(v_toCold_2184_, 2);
v_hasTrace_2186_ = lean_ctor_get_uint8(v_options_2185_, sizeof(void*)*1);
if (v_hasTrace_2186_ == 0)
{
v___y_2085_ = v_val_2183_;
goto v___jp_2084_;
}
else
{
lean_object* v_inheritedTraceOptions_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; uint8_t v___x_2190_; 
v_inheritedTraceOptions_2187_ = lean_ctor_get(v_toCold_2184_, 11);
v___x_2188_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_));
v___x_2189_ = lean_obj_once(&l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5, &l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5_once, _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5);
v___x_2190_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2187_, v_options_2185_, v___x_2189_);
if (v___x_2190_ == 0)
{
v___y_2085_ = v_val_2183_;
goto v___jp_2084_;
}
else
{
lean_object* v___x_2191_; 
v___x_2191_ = lean_obj_once(&l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__7, &l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__7_once, _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__7);
if (v_symm_1946_ == 0)
{
lean_object* v___x_2192_; 
v___x_2192_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__1));
v___y_2165_ = v___x_2188_;
v___y_2166_ = v_val_2183_;
v___y_2167_ = v___x_2191_;
v___y_2168_ = v___x_2192_;
goto v___jp_2164_;
}
else
{
lean_object* v___x_2193_; 
v___x_2193_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__8));
v___y_2165_ = v___x_2188_;
v___y_2166_ = v_val_2183_;
v___y_2167_ = v___x_2191_;
v___y_2168_ = v___x_2193_;
goto v___jp_2164_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0___boxed(lean_object* v_weight_2238_, lean_object* v_goal_2239_, lean_object* v_target_2240_, lean_object* v_symm_2241_, lean_object* v_side_2242_, lean_object* v_lem_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
uint8_t v_symm_boxed_2249_; uint8_t v_side_boxed_2250_; lean_object* v_res_2251_; 
v_symm_boxed_2249_ = lean_unbox(v_symm_2241_);
v_side_boxed_2250_ = lean_unbox(v_side_2242_);
v_res_2251_ = l_Lean_Meta_Rewrites_rwLemma___lam__0(v_weight_2238_, v_goal_2239_, v_target_2240_, v_symm_boxed_2249_, v_side_boxed_2250_, v_lem_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
return v_res_2251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma(lean_object* v_ctx_2252_, lean_object* v_goal_2253_, lean_object* v_target_2254_, uint8_t v_side_2255_, lean_object* v_lem_2256_, uint8_t v_symm_2257_, lean_object* v_weight_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_){
_start:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___f_2266_; lean_object* v___x_2267_; 
v___x_2264_ = lean_box(v_symm_2257_);
v___x_2265_ = lean_box(v_side_2255_);
v___f_2266_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___boxed), 11, 6);
lean_closure_set(v___f_2266_, 0, v_weight_2258_);
lean_closure_set(v___f_2266_, 1, v_goal_2253_);
lean_closure_set(v___f_2266_, 2, v_target_2254_);
lean_closure_set(v___f_2266_, 3, v___x_2264_);
lean_closure_set(v___f_2266_, 4, v___x_2265_);
lean_closure_set(v___f_2266_, 5, v_lem_2256_);
v___x_2267_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg(v_ctx_2252_, v___f_2266_, v_a_2259_, v_a_2260_, v_a_2261_, v_a_2262_);
return v___x_2267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___boxed(lean_object* v_ctx_2268_, lean_object* v_goal_2269_, lean_object* v_target_2270_, lean_object* v_side_2271_, lean_object* v_lem_2272_, lean_object* v_symm_2273_, lean_object* v_weight_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_){
_start:
{
uint8_t v_side_boxed_2280_; uint8_t v_symm_boxed_2281_; lean_object* v_res_2282_; 
v_side_boxed_2280_ = lean_unbox(v_side_2271_);
v_symm_boxed_2281_ = lean_unbox(v_symm_2273_);
v_res_2282_ = l_Lean_Meta_Rewrites_rwLemma(v_ctx_2268_, v_goal_2269_, v_target_2270_, v_side_boxed_2280_, v_lem_2272_, v_symm_boxed_2281_, v_weight_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_);
lean_dec(v_a_2278_);
lean_dec_ref(v_a_2277_);
lean_dec(v_a_2276_);
lean_dec_ref(v_a_2275_);
return v_res_2282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(lean_object* v_type_2283_, lean_object* v_k_2284_, uint8_t v_cleanupAnnotations_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_){
_start:
{
lean_object* v___f_2291_; uint8_t v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___f_2291_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2291_, 0, v_k_2284_);
v___x_2292_ = 0;
v___x_2293_ = lean_box(0);
v___x_2294_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_2292_, v___x_2293_, v_type_2283_, v___f_2291_, v_cleanupAnnotations_2285_, v___x_2292_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_object* v_a_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2302_; 
v_a_2295_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2302_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2297_ = v___x_2294_;
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_a_2295_);
lean_dec(v___x_2294_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2302_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2300_; 
if (v_isShared_2298_ == 0)
{
v___x_2300_ = v___x_2297_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_a_2295_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
return v___x_2300_;
}
}
}
else
{
lean_object* v_a_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2310_; 
v_a_2303_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2310_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2310_ == 0)
{
v___x_2305_ = v___x_2294_;
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_a_2303_);
lean_dec(v___x_2294_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v___x_2308_; 
if (v_isShared_2306_ == 0)
{
v___x_2308_ = v___x_2305_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_a_2303_);
v___x_2308_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
return v___x_2308_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg___boxed(lean_object* v_type_2311_, lean_object* v_k_2312_, lean_object* v_cleanupAnnotations_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2319_; lean_object* v_res_2320_; 
v_cleanupAnnotations_boxed_2319_ = lean_unbox(v_cleanupAnnotations_2313_);
v_res_2320_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(v_type_2311_, v_k_2312_, v_cleanupAnnotations_boxed_2319_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
lean_dec(v___y_2317_);
lean_dec_ref(v___y_2316_);
lean_dec(v___y_2315_);
lean_dec_ref(v___y_2314_);
return v_res_2320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1(lean_object* v_00_u03b1_2321_, lean_object* v_type_2322_, lean_object* v_k_2323_, uint8_t v_cleanupAnnotations_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_){
_start:
{
lean_object* v___x_2330_; 
v___x_2330_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(v_type_2322_, v_k_2323_, v_cleanupAnnotations_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_);
return v___x_2330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___boxed(lean_object* v_00_u03b1_2331_, lean_object* v_type_2332_, lean_object* v_k_2333_, lean_object* v_cleanupAnnotations_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2340_; lean_object* v_res_2341_; 
v_cleanupAnnotations_boxed_2340_ = lean_unbox(v_cleanupAnnotations_2334_);
v_res_2341_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1(v_00_u03b1_2331_, v_type_2332_, v_k_2333_, v_cleanupAnnotations_boxed_2340_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_);
lean_dec(v___y_2338_);
lean_dec_ref(v___y_2337_);
lean_dec(v___y_2336_);
lean_dec_ref(v___y_2335_);
return v_res_2341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(lean_object* v_e_2342_, lean_object* v_k_2343_, uint8_t v_cleanupAnnotations_2344_, uint8_t v_preserveNondepLet_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_){
_start:
{
lean_object* v___f_2351_; uint8_t v___x_2352_; uint8_t v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___f_2351_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2351_, 0, v_k_2343_);
v___x_2352_ = 1;
v___x_2353_ = 0;
v___x_2354_ = lean_box(0);
v___x_2355_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2342_, v___x_2352_, v___x_2352_, v_preserveNondepLet_2345_, v___x_2353_, v___x_2354_, v___f_2351_, v_cleanupAnnotations_2344_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_);
if (lean_obj_tag(v___x_2355_) == 0)
{
lean_object* v_a_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2363_; 
v_a_2356_ = lean_ctor_get(v___x_2355_, 0);
v_isSharedCheck_2363_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2358_ = v___x_2355_;
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_a_2356_);
lean_dec(v___x_2355_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v___x_2361_; 
if (v_isShared_2359_ == 0)
{
v___x_2361_ = v___x_2358_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_a_2356_);
v___x_2361_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
return v___x_2361_;
}
}
}
else
{
lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2371_; 
v_a_2364_ = lean_ctor_get(v___x_2355_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2366_ = v___x_2355_;
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v___x_2355_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg___boxed(lean_object* v_e_2372_, lean_object* v_k_2373_, lean_object* v_cleanupAnnotations_2374_, lean_object* v_preserveNondepLet_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2381_; uint8_t v_preserveNondepLet_boxed_2382_; lean_object* v_res_2383_; 
v_cleanupAnnotations_boxed_2381_ = lean_unbox(v_cleanupAnnotations_2374_);
v_preserveNondepLet_boxed_2382_ = lean_unbox(v_preserveNondepLet_2375_);
v_res_2383_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(v_e_2372_, v_k_2373_, v_cleanupAnnotations_boxed_2381_, v_preserveNondepLet_boxed_2382_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_);
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
return v_res_2383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2(lean_object* v_00_u03b1_2384_, lean_object* v_e_2385_, lean_object* v_k_2386_, uint8_t v_cleanupAnnotations_2387_, uint8_t v_preserveNondepLet_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_){
_start:
{
lean_object* v___x_2394_; 
v___x_2394_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(v_e_2385_, v_k_2386_, v_cleanupAnnotations_2387_, v_preserveNondepLet_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_);
return v___x_2394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___boxed(lean_object* v_00_u03b1_2395_, lean_object* v_e_2396_, lean_object* v_k_2397_, lean_object* v_cleanupAnnotations_2398_, lean_object* v_preserveNondepLet_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2405_; uint8_t v_preserveNondepLet_boxed_2406_; lean_object* v_res_2407_; 
v_cleanupAnnotations_boxed_2405_ = lean_unbox(v_cleanupAnnotations_2398_);
v_preserveNondepLet_boxed_2406_ = lean_unbox(v_preserveNondepLet_2399_);
v_res_2407_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2(v_00_u03b1_2395_, v_e_2396_, v_k_2397_, v_cleanupAnnotations_boxed_2405_, v_preserveNondepLet_boxed_2406_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_);
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
return v_res_2407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(lean_object* v_f_2408_, lean_object* v_e_x27_2409_, lean_object* v_a_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_){
_start:
{
lean_object* v___x_2416_; 
lean_inc(v___y_2414_);
lean_inc_ref(v___y_2413_);
lean_inc(v___y_2412_);
lean_inc_ref(v___y_2411_);
lean_inc_ref(v_e_x27_2409_);
v___x_2416_ = lean_apply_7(v_f_2408_, v_a_2410_, v_e_x27_2409_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, lean_box(0));
if (lean_obj_tag(v___x_2416_) == 0)
{
lean_object* v_a_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2425_; 
v_a_2417_ = lean_ctor_get(v___x_2416_, 0);
v_isSharedCheck_2425_ = !lean_is_exclusive(v___x_2416_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2419_ = v___x_2416_;
v_isShared_2420_ = v_isSharedCheck_2425_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_a_2417_);
lean_dec(v___x_2416_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2425_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
lean_object* v___x_2421_; lean_object* v___x_2423_; 
v___x_2421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2421_, 0, v_e_x27_2409_);
lean_ctor_set(v___x_2421_, 1, v_a_2417_);
if (v_isShared_2420_ == 0)
{
lean_ctor_set(v___x_2419_, 0, v___x_2421_);
v___x_2423_ = v___x_2419_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v___x_2421_);
v___x_2423_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
return v___x_2423_;
}
}
}
else
{
lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2433_; 
lean_dec_ref(v_e_x27_2409_);
v_a_2426_ = lean_ctor_get(v___x_2416_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2416_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2428_ = v___x_2416_;
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_dec(v___x_2416_);
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
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0___boxed(lean_object* v_f_2434_, lean_object* v_e_x27_2435_, lean_object* v_a_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_){
_start:
{
lean_object* v_res_2442_; 
v_res_2442_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2434_, v_e_x27_2435_, v_a_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_);
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
lean_dec(v___y_2438_);
lean_dec_ref(v___y_2437_);
return v_res_2442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg(lean_object* v_f_2443_, lean_object* v_x_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_){
_start:
{
switch(lean_obj_tag(v_x_2444_))
{
case 7:
{
lean_object* v_binderName_2451_; lean_object* v_binderType_2452_; lean_object* v_body_2453_; uint8_t v_binderInfo_2454_; lean_object* v___x_2455_; 
v_binderName_2451_ = lean_ctor_get(v_x_2444_, 0);
v_binderType_2452_ = lean_ctor_get(v_x_2444_, 1);
v_body_2453_ = lean_ctor_get(v_x_2444_, 2);
v_binderInfo_2454_ = lean_ctor_get_uint8(v_x_2444_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2452_);
lean_inc_ref(v_f_2443_);
v___x_2455_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2443_, v_binderType_2452_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
if (lean_obj_tag(v___x_2455_) == 0)
{
lean_object* v_a_2456_; lean_object* v_fst_2457_; lean_object* v_snd_2458_; lean_object* v___x_2459_; 
v_a_2456_ = lean_ctor_get(v___x_2455_, 0);
lean_inc(v_a_2456_);
lean_dec_ref_known(v___x_2455_, 1);
v_fst_2457_ = lean_ctor_get(v_a_2456_, 0);
lean_inc(v_fst_2457_);
v_snd_2458_ = lean_ctor_get(v_a_2456_, 1);
lean_inc(v_snd_2458_);
lean_dec(v_a_2456_);
lean_inc_ref(v_body_2453_);
v___x_2459_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2443_, v_body_2453_, v_snd_2458_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
if (lean_obj_tag(v___x_2459_) == 0)
{
lean_object* v_a_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2488_; 
v_a_2460_ = lean_ctor_get(v___x_2459_, 0);
v_isSharedCheck_2488_ = !lean_is_exclusive(v___x_2459_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2462_ = v___x_2459_;
v_isShared_2463_ = v_isSharedCheck_2488_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_a_2460_);
lean_dec(v___x_2459_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2488_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v_fst_2464_; lean_object* v_snd_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2487_; 
v_fst_2464_ = lean_ctor_get(v_a_2460_, 0);
v_snd_2465_ = lean_ctor_get(v_a_2460_, 1);
v_isSharedCheck_2487_ = !lean_is_exclusive(v_a_2460_);
if (v_isSharedCheck_2487_ == 0)
{
v___x_2467_ = v_a_2460_;
v_isShared_2468_ = v_isSharedCheck_2487_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_snd_2465_);
lean_inc(v_fst_2464_);
lean_dec(v_a_2460_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2487_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v___y_2470_; size_t v___x_2477_; size_t v___x_2478_; uint8_t v___x_2479_; 
v___x_2477_ = lean_ptr_addr(v_binderType_2452_);
v___x_2478_ = lean_ptr_addr(v_fst_2457_);
v___x_2479_ = lean_usize_dec_eq(v___x_2477_, v___x_2478_);
if (v___x_2479_ == 0)
{
lean_object* v___x_2480_; 
lean_inc(v_binderName_2451_);
lean_dec_ref_known(v_x_2444_, 3);
v___x_2480_ = l_Lean_Expr_forallE___override(v_binderName_2451_, v_fst_2457_, v_fst_2464_, v_binderInfo_2454_);
v___y_2470_ = v___x_2480_;
goto v___jp_2469_;
}
else
{
size_t v___x_2481_; size_t v___x_2482_; uint8_t v___x_2483_; 
v___x_2481_ = lean_ptr_addr(v_body_2453_);
v___x_2482_ = lean_ptr_addr(v_fst_2464_);
v___x_2483_ = lean_usize_dec_eq(v___x_2481_, v___x_2482_);
if (v___x_2483_ == 0)
{
lean_object* v___x_2484_; 
lean_inc(v_binderName_2451_);
lean_dec_ref_known(v_x_2444_, 3);
v___x_2484_ = l_Lean_Expr_forallE___override(v_binderName_2451_, v_fst_2457_, v_fst_2464_, v_binderInfo_2454_);
v___y_2470_ = v___x_2484_;
goto v___jp_2469_;
}
else
{
uint8_t v___x_2485_; 
v___x_2485_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2454_, v_binderInfo_2454_);
if (v___x_2485_ == 0)
{
lean_object* v___x_2486_; 
lean_inc(v_binderName_2451_);
lean_dec_ref_known(v_x_2444_, 3);
v___x_2486_ = l_Lean_Expr_forallE___override(v_binderName_2451_, v_fst_2457_, v_fst_2464_, v_binderInfo_2454_);
v___y_2470_ = v___x_2486_;
goto v___jp_2469_;
}
else
{
lean_dec(v_fst_2464_);
lean_dec(v_fst_2457_);
v___y_2470_ = v_x_2444_;
goto v___jp_2469_;
}
}
}
v___jp_2469_:
{
lean_object* v___x_2472_; 
if (v_isShared_2468_ == 0)
{
lean_ctor_set(v___x_2467_, 0, v___y_2470_);
v___x_2472_ = v___x_2467_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v___y_2470_);
lean_ctor_set(v_reuseFailAlloc_2476_, 1, v_snd_2465_);
v___x_2472_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
lean_object* v___x_2474_; 
if (v_isShared_2463_ == 0)
{
lean_ctor_set(v___x_2462_, 0, v___x_2472_);
v___x_2474_ = v___x_2462_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v___x_2472_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
}
}
}
}
else
{
lean_dec(v_fst_2457_);
lean_dec_ref_known(v_x_2444_, 3);
return v___x_2459_;
}
}
else
{
lean_dec_ref_known(v_x_2444_, 3);
lean_dec_ref(v_f_2443_);
return v___x_2455_;
}
}
case 6:
{
lean_object* v_binderName_2489_; lean_object* v_binderType_2490_; lean_object* v_body_2491_; uint8_t v_binderInfo_2492_; lean_object* v___x_2493_; 
v_binderName_2489_ = lean_ctor_get(v_x_2444_, 0);
v_binderType_2490_ = lean_ctor_get(v_x_2444_, 1);
v_body_2491_ = lean_ctor_get(v_x_2444_, 2);
v_binderInfo_2492_ = lean_ctor_get_uint8(v_x_2444_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2490_);
lean_inc_ref(v_f_2443_);
v___x_2493_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2443_, v_binderType_2490_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
if (lean_obj_tag(v___x_2493_) == 0)
{
lean_object* v_a_2494_; lean_object* v_fst_2495_; lean_object* v_snd_2496_; lean_object* v___x_2497_; 
v_a_2494_ = lean_ctor_get(v___x_2493_, 0);
lean_inc(v_a_2494_);
lean_dec_ref_known(v___x_2493_, 1);
v_fst_2495_ = lean_ctor_get(v_a_2494_, 0);
lean_inc(v_fst_2495_);
v_snd_2496_ = lean_ctor_get(v_a_2494_, 1);
lean_inc(v_snd_2496_);
lean_dec(v_a_2494_);
lean_inc_ref(v_body_2491_);
v___x_2497_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2443_, v_body_2491_, v_snd_2496_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
if (lean_obj_tag(v___x_2497_) == 0)
{
lean_object* v_a_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2526_; 
v_a_2498_ = lean_ctor_get(v___x_2497_, 0);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2497_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2500_ = v___x_2497_;
v_isShared_2501_ = v_isSharedCheck_2526_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_a_2498_);
lean_dec(v___x_2497_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2526_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v_fst_2502_; lean_object* v_snd_2503_; lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2525_; 
v_fst_2502_ = lean_ctor_get(v_a_2498_, 0);
v_snd_2503_ = lean_ctor_get(v_a_2498_, 1);
v_isSharedCheck_2525_ = !lean_is_exclusive(v_a_2498_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2505_ = v_a_2498_;
v_isShared_2506_ = v_isSharedCheck_2525_;
goto v_resetjp_2504_;
}
else
{
lean_inc(v_snd_2503_);
lean_inc(v_fst_2502_);
lean_dec(v_a_2498_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_2525_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
lean_object* v___y_2508_; size_t v___x_2515_; size_t v___x_2516_; uint8_t v___x_2517_; 
v___x_2515_ = lean_ptr_addr(v_binderType_2490_);
v___x_2516_ = lean_ptr_addr(v_fst_2495_);
v___x_2517_ = lean_usize_dec_eq(v___x_2515_, v___x_2516_);
if (v___x_2517_ == 0)
{
lean_object* v___x_2518_; 
lean_inc(v_binderName_2489_);
lean_dec_ref_known(v_x_2444_, 3);
v___x_2518_ = l_Lean_Expr_lam___override(v_binderName_2489_, v_fst_2495_, v_fst_2502_, v_binderInfo_2492_);
v___y_2508_ = v___x_2518_;
goto v___jp_2507_;
}
else
{
size_t v___x_2519_; size_t v___x_2520_; uint8_t v___x_2521_; 
v___x_2519_ = lean_ptr_addr(v_body_2491_);
v___x_2520_ = lean_ptr_addr(v_fst_2502_);
v___x_2521_ = lean_usize_dec_eq(v___x_2519_, v___x_2520_);
if (v___x_2521_ == 0)
{
lean_object* v___x_2522_; 
lean_inc(v_binderName_2489_);
lean_dec_ref_known(v_x_2444_, 3);
v___x_2522_ = l_Lean_Expr_lam___override(v_binderName_2489_, v_fst_2495_, v_fst_2502_, v_binderInfo_2492_);
v___y_2508_ = v___x_2522_;
goto v___jp_2507_;
}
else
{
uint8_t v___x_2523_; 
v___x_2523_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2492_, v_binderInfo_2492_);
if (v___x_2523_ == 0)
{
lean_object* v___x_2524_; 
lean_inc(v_binderName_2489_);
lean_dec_ref_known(v_x_2444_, 3);
v___x_2524_ = l_Lean_Expr_lam___override(v_binderName_2489_, v_fst_2495_, v_fst_2502_, v_binderInfo_2492_);
v___y_2508_ = v___x_2524_;
goto v___jp_2507_;
}
else
{
lean_dec(v_fst_2502_);
lean_dec(v_fst_2495_);
v___y_2508_ = v_x_2444_;
goto v___jp_2507_;
}
}
}
v___jp_2507_:
{
lean_object* v___x_2510_; 
if (v_isShared_2506_ == 0)
{
lean_ctor_set(v___x_2505_, 0, v___y_2508_);
v___x_2510_ = v___x_2505_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v___y_2508_);
lean_ctor_set(v_reuseFailAlloc_2514_, 1, v_snd_2503_);
v___x_2510_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
lean_object* v___x_2512_; 
if (v_isShared_2501_ == 0)
{
lean_ctor_set(v___x_2500_, 0, v___x_2510_);
v___x_2512_ = v___x_2500_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v___x_2510_);
v___x_2512_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
return v___x_2512_;
}
}
}
}
}
}
else
{
lean_dec(v_fst_2495_);
lean_dec_ref_known(v_x_2444_, 3);
return v___x_2497_;
}
}
else
{
lean_dec_ref_known(v_x_2444_, 3);
lean_dec_ref(v_f_2443_);
return v___x_2493_;
}
}
case 10:
{
lean_object* v_data_2527_; lean_object* v_expr_2528_; lean_object* v___x_2529_; 
v_data_2527_ = lean_ctor_get(v_x_2444_, 0);
v_expr_2528_ = lean_ctor_get(v_x_2444_, 1);
lean_inc_ref(v_expr_2528_);
v___x_2529_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2443_, v_expr_2528_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
if (lean_obj_tag(v___x_2529_) == 0)
{
lean_object* v_a_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2552_; 
v_a_2530_ = lean_ctor_get(v___x_2529_, 0);
v_isSharedCheck_2552_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2532_ = v___x_2529_;
v_isShared_2533_ = v_isSharedCheck_2552_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_a_2530_);
lean_dec(v___x_2529_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2552_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v_fst_2534_; lean_object* v_snd_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2551_; 
v_fst_2534_ = lean_ctor_get(v_a_2530_, 0);
v_snd_2535_ = lean_ctor_get(v_a_2530_, 1);
v_isSharedCheck_2551_ = !lean_is_exclusive(v_a_2530_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2537_ = v_a_2530_;
v_isShared_2538_ = v_isSharedCheck_2551_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_snd_2535_);
lean_inc(v_fst_2534_);
lean_dec(v_a_2530_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2551_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
lean_object* v___y_2540_; size_t v___x_2547_; size_t v___x_2548_; uint8_t v___x_2549_; 
v___x_2547_ = lean_ptr_addr(v_expr_2528_);
v___x_2548_ = lean_ptr_addr(v_fst_2534_);
v___x_2549_ = lean_usize_dec_eq(v___x_2547_, v___x_2548_);
if (v___x_2549_ == 0)
{
lean_object* v___x_2550_; 
lean_inc(v_data_2527_);
lean_dec_ref_known(v_x_2444_, 2);
v___x_2550_ = l_Lean_Expr_mdata___override(v_data_2527_, v_fst_2534_);
v___y_2540_ = v___x_2550_;
goto v___jp_2539_;
}
else
{
lean_dec(v_fst_2534_);
v___y_2540_ = v_x_2444_;
goto v___jp_2539_;
}
v___jp_2539_:
{
lean_object* v___x_2542_; 
if (v_isShared_2538_ == 0)
{
lean_ctor_set(v___x_2537_, 0, v___y_2540_);
v___x_2542_ = v___x_2537_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v___y_2540_);
lean_ctor_set(v_reuseFailAlloc_2546_, 1, v_snd_2535_);
v___x_2542_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
lean_object* v___x_2544_; 
if (v_isShared_2533_ == 0)
{
lean_ctor_set(v___x_2532_, 0, v___x_2542_);
v___x_2544_ = v___x_2532_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v___x_2542_);
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
}
}
else
{
lean_dec_ref_known(v_x_2444_, 2);
return v___x_2529_;
}
}
case 8:
{
lean_object* v_declName_2553_; lean_object* v_type_2554_; lean_object* v_value_2555_; lean_object* v_body_2556_; uint8_t v_nondep_2557_; lean_object* v___x_2558_; 
v_declName_2553_ = lean_ctor_get(v_x_2444_, 0);
v_type_2554_ = lean_ctor_get(v_x_2444_, 1);
v_value_2555_ = lean_ctor_get(v_x_2444_, 2);
v_body_2556_ = lean_ctor_get(v_x_2444_, 3);
v_nondep_2557_ = lean_ctor_get_uint8(v_x_2444_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_2554_);
lean_inc_ref(v_f_2443_);
v___x_2558_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2443_, v_type_2554_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
if (lean_obj_tag(v___x_2558_) == 0)
{
lean_object* v_a_2559_; lean_object* v_fst_2560_; lean_object* v_snd_2561_; lean_object* v___x_2562_; 
v_a_2559_ = lean_ctor_get(v___x_2558_, 0);
lean_inc(v_a_2559_);
lean_dec_ref_known(v___x_2558_, 1);
v_fst_2560_ = lean_ctor_get(v_a_2559_, 0);
lean_inc(v_fst_2560_);
v_snd_2561_ = lean_ctor_get(v_a_2559_, 1);
lean_inc(v_snd_2561_);
lean_dec(v_a_2559_);
lean_inc_ref(v_value_2555_);
lean_inc_ref(v_f_2443_);
v___x_2562_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2443_, v_value_2555_, v_snd_2561_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
if (lean_obj_tag(v___x_2562_) == 0)
{
lean_object* v_a_2563_; lean_object* v_fst_2564_; lean_object* v_snd_2565_; lean_object* v___x_2566_; 
v_a_2563_ = lean_ctor_get(v___x_2562_, 0);
lean_inc(v_a_2563_);
lean_dec_ref_known(v___x_2562_, 1);
v_fst_2564_ = lean_ctor_get(v_a_2563_, 0);
lean_inc(v_fst_2564_);
v_snd_2565_ = lean_ctor_get(v_a_2563_, 1);
lean_inc(v_snd_2565_);
lean_dec(v_a_2563_);
lean_inc_ref(v_body_2556_);
v___x_2566_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2443_, v_body_2556_, v_snd_2565_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v_a_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2597_; 
v_a_2567_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2569_ = v___x_2566_;
v_isShared_2570_ = v_isSharedCheck_2597_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_a_2567_);
lean_dec(v___x_2566_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2597_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v_fst_2571_; lean_object* v_snd_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2596_; 
v_fst_2571_ = lean_ctor_get(v_a_2567_, 0);
v_snd_2572_ = lean_ctor_get(v_a_2567_, 1);
v_isSharedCheck_2596_ = !lean_is_exclusive(v_a_2567_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2574_ = v_a_2567_;
v_isShared_2575_ = v_isSharedCheck_2596_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_snd_2572_);
lean_inc(v_fst_2571_);
lean_dec(v_a_2567_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2596_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v___y_2577_; size_t v___x_2584_; size_t v___x_2585_; uint8_t v___x_2586_; 
v___x_2584_ = lean_ptr_addr(v_type_2554_);
v___x_2585_ = lean_ptr_addr(v_fst_2560_);
v___x_2586_ = lean_usize_dec_eq(v___x_2584_, v___x_2585_);
if (v___x_2586_ == 0)
{
lean_object* v___x_2587_; 
lean_inc(v_declName_2553_);
lean_dec_ref_known(v_x_2444_, 4);
v___x_2587_ = l_Lean_Expr_letE___override(v_declName_2553_, v_fst_2560_, v_fst_2564_, v_fst_2571_, v_nondep_2557_);
v___y_2577_ = v___x_2587_;
goto v___jp_2576_;
}
else
{
size_t v___x_2588_; size_t v___x_2589_; uint8_t v___x_2590_; 
v___x_2588_ = lean_ptr_addr(v_value_2555_);
v___x_2589_ = lean_ptr_addr(v_fst_2564_);
v___x_2590_ = lean_usize_dec_eq(v___x_2588_, v___x_2589_);
if (v___x_2590_ == 0)
{
lean_object* v___x_2591_; 
lean_inc(v_declName_2553_);
lean_dec_ref_known(v_x_2444_, 4);
v___x_2591_ = l_Lean_Expr_letE___override(v_declName_2553_, v_fst_2560_, v_fst_2564_, v_fst_2571_, v_nondep_2557_);
v___y_2577_ = v___x_2591_;
goto v___jp_2576_;
}
else
{
size_t v___x_2592_; size_t v___x_2593_; uint8_t v___x_2594_; 
v___x_2592_ = lean_ptr_addr(v_body_2556_);
v___x_2593_ = lean_ptr_addr(v_fst_2571_);
v___x_2594_ = lean_usize_dec_eq(v___x_2592_, v___x_2593_);
if (v___x_2594_ == 0)
{
lean_object* v___x_2595_; 
lean_inc(v_declName_2553_);
lean_dec_ref_known(v_x_2444_, 4);
v___x_2595_ = l_Lean_Expr_letE___override(v_declName_2553_, v_fst_2560_, v_fst_2564_, v_fst_2571_, v_nondep_2557_);
v___y_2577_ = v___x_2595_;
goto v___jp_2576_;
}
else
{
lean_dec(v_fst_2571_);
lean_dec(v_fst_2564_);
lean_dec(v_fst_2560_);
v___y_2577_ = v_x_2444_;
goto v___jp_2576_;
}
}
}
v___jp_2576_:
{
lean_object* v___x_2579_; 
if (v_isShared_2575_ == 0)
{
lean_ctor_set(v___x_2574_, 0, v___y_2577_);
v___x_2579_ = v___x_2574_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v___y_2577_);
lean_ctor_set(v_reuseFailAlloc_2583_, 1, v_snd_2572_);
v___x_2579_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
lean_object* v___x_2581_; 
if (v_isShared_2570_ == 0)
{
lean_ctor_set(v___x_2569_, 0, v___x_2579_);
v___x_2581_ = v___x_2569_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v___x_2579_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
}
}
}
}
}
}
else
{
lean_dec(v_fst_2564_);
lean_dec(v_fst_2560_);
lean_dec_ref_known(v_x_2444_, 4);
return v___x_2566_;
}
}
else
{
lean_dec(v_fst_2560_);
lean_dec_ref_known(v_x_2444_, 4);
lean_dec_ref(v_f_2443_);
return v___x_2562_;
}
}
else
{
lean_dec_ref_known(v_x_2444_, 4);
lean_dec_ref(v_f_2443_);
return v___x_2558_;
}
}
case 5:
{
lean_object* v_fn_2598_; lean_object* v_arg_2599_; lean_object* v___x_2600_; 
v_fn_2598_ = lean_ctor_get(v_x_2444_, 0);
v_arg_2599_ = lean_ctor_get(v_x_2444_, 1);
lean_inc_ref(v_fn_2598_);
lean_inc_ref(v_f_2443_);
v___x_2600_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2443_, v_fn_2598_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
if (lean_obj_tag(v___x_2600_) == 0)
{
lean_object* v_a_2601_; lean_object* v_fst_2602_; lean_object* v_snd_2603_; lean_object* v___x_2604_; 
v_a_2601_ = lean_ctor_get(v___x_2600_, 0);
lean_inc(v_a_2601_);
lean_dec_ref_known(v___x_2600_, 1);
v_fst_2602_ = lean_ctor_get(v_a_2601_, 0);
lean_inc(v_fst_2602_);
v_snd_2603_ = lean_ctor_get(v_a_2601_, 1);
lean_inc(v_snd_2603_);
lean_dec(v_a_2601_);
lean_inc_ref(v_arg_2599_);
v___x_2604_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2443_, v_arg_2599_, v_snd_2603_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
if (lean_obj_tag(v___x_2604_) == 0)
{
lean_object* v_a_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2631_; 
v_a_2605_ = lean_ctor_get(v___x_2604_, 0);
v_isSharedCheck_2631_ = !lean_is_exclusive(v___x_2604_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2607_ = v___x_2604_;
v_isShared_2608_ = v_isSharedCheck_2631_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_a_2605_);
lean_dec(v___x_2604_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2631_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v_fst_2609_; lean_object* v_snd_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2630_; 
v_fst_2609_ = lean_ctor_get(v_a_2605_, 0);
v_snd_2610_ = lean_ctor_get(v_a_2605_, 1);
v_isSharedCheck_2630_ = !lean_is_exclusive(v_a_2605_);
if (v_isSharedCheck_2630_ == 0)
{
v___x_2612_ = v_a_2605_;
v_isShared_2613_ = v_isSharedCheck_2630_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_snd_2610_);
lean_inc(v_fst_2609_);
lean_dec(v_a_2605_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2630_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
lean_object* v___y_2615_; size_t v___x_2622_; size_t v___x_2623_; uint8_t v___x_2624_; 
v___x_2622_ = lean_ptr_addr(v_fn_2598_);
v___x_2623_ = lean_ptr_addr(v_fst_2602_);
v___x_2624_ = lean_usize_dec_eq(v___x_2622_, v___x_2623_);
if (v___x_2624_ == 0)
{
lean_object* v___x_2625_; 
lean_dec_ref_known(v_x_2444_, 2);
v___x_2625_ = l_Lean_Expr_app___override(v_fst_2602_, v_fst_2609_);
v___y_2615_ = v___x_2625_;
goto v___jp_2614_;
}
else
{
size_t v___x_2626_; size_t v___x_2627_; uint8_t v___x_2628_; 
v___x_2626_ = lean_ptr_addr(v_arg_2599_);
v___x_2627_ = lean_ptr_addr(v_fst_2609_);
v___x_2628_ = lean_usize_dec_eq(v___x_2626_, v___x_2627_);
if (v___x_2628_ == 0)
{
lean_object* v___x_2629_; 
lean_dec_ref_known(v_x_2444_, 2);
v___x_2629_ = l_Lean_Expr_app___override(v_fst_2602_, v_fst_2609_);
v___y_2615_ = v___x_2629_;
goto v___jp_2614_;
}
else
{
lean_dec(v_fst_2609_);
lean_dec(v_fst_2602_);
v___y_2615_ = v_x_2444_;
goto v___jp_2614_;
}
}
v___jp_2614_:
{
lean_object* v___x_2617_; 
if (v_isShared_2613_ == 0)
{
lean_ctor_set(v___x_2612_, 0, v___y_2615_);
v___x_2617_ = v___x_2612_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v___y_2615_);
lean_ctor_set(v_reuseFailAlloc_2621_, 1, v_snd_2610_);
v___x_2617_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
lean_object* v___x_2619_; 
if (v_isShared_2608_ == 0)
{
lean_ctor_set(v___x_2607_, 0, v___x_2617_);
v___x_2619_ = v___x_2607_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v___x_2617_);
v___x_2619_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
return v___x_2619_;
}
}
}
}
}
}
else
{
lean_dec(v_fst_2602_);
lean_dec_ref_known(v_x_2444_, 2);
return v___x_2604_;
}
}
else
{
lean_dec_ref_known(v_x_2444_, 2);
lean_dec_ref(v_f_2443_);
return v___x_2600_;
}
}
case 11:
{
lean_object* v_typeName_2632_; lean_object* v_idx_2633_; lean_object* v_struct_2634_; lean_object* v___x_2635_; 
v_typeName_2632_ = lean_ctor_get(v_x_2444_, 0);
v_idx_2633_ = lean_ctor_get(v_x_2444_, 1);
v_struct_2634_ = lean_ctor_get(v_x_2444_, 2);
lean_inc_ref(v_struct_2634_);
v___x_2635_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2443_, v_struct_2634_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
if (lean_obj_tag(v___x_2635_) == 0)
{
lean_object* v_a_2636_; lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2658_; 
v_a_2636_ = lean_ctor_get(v___x_2635_, 0);
v_isSharedCheck_2658_ = !lean_is_exclusive(v___x_2635_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2638_ = v___x_2635_;
v_isShared_2639_ = v_isSharedCheck_2658_;
goto v_resetjp_2637_;
}
else
{
lean_inc(v_a_2636_);
lean_dec(v___x_2635_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2658_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
lean_object* v_fst_2640_; lean_object* v_snd_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2657_; 
v_fst_2640_ = lean_ctor_get(v_a_2636_, 0);
v_snd_2641_ = lean_ctor_get(v_a_2636_, 1);
v_isSharedCheck_2657_ = !lean_is_exclusive(v_a_2636_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2643_ = v_a_2636_;
v_isShared_2644_ = v_isSharedCheck_2657_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_snd_2641_);
lean_inc(v_fst_2640_);
lean_dec(v_a_2636_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2657_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v___y_2646_; size_t v___x_2653_; size_t v___x_2654_; uint8_t v___x_2655_; 
v___x_2653_ = lean_ptr_addr(v_struct_2634_);
v___x_2654_ = lean_ptr_addr(v_fst_2640_);
v___x_2655_ = lean_usize_dec_eq(v___x_2653_, v___x_2654_);
if (v___x_2655_ == 0)
{
lean_object* v___x_2656_; 
lean_inc(v_idx_2633_);
lean_inc(v_typeName_2632_);
lean_dec_ref_known(v_x_2444_, 3);
v___x_2656_ = l_Lean_Expr_proj___override(v_typeName_2632_, v_idx_2633_, v_fst_2640_);
v___y_2646_ = v___x_2656_;
goto v___jp_2645_;
}
else
{
lean_dec(v_fst_2640_);
v___y_2646_ = v_x_2444_;
goto v___jp_2645_;
}
v___jp_2645_:
{
lean_object* v___x_2648_; 
if (v_isShared_2644_ == 0)
{
lean_ctor_set(v___x_2643_, 0, v___y_2646_);
v___x_2648_ = v___x_2643_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v___y_2646_);
lean_ctor_set(v_reuseFailAlloc_2652_, 1, v_snd_2641_);
v___x_2648_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
lean_object* v___x_2650_; 
if (v_isShared_2639_ == 0)
{
lean_ctor_set(v___x_2638_, 0, v___x_2648_);
v___x_2650_ = v___x_2638_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v___x_2648_);
v___x_2650_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
return v___x_2650_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_x_2444_, 3);
return v___x_2635_;
}
}
default: 
{
lean_object* v___x_2659_; lean_object* v___x_2660_; 
lean_dec_ref(v_f_2443_);
v___x_2659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2659_, 0, v_x_2444_);
lean_ctor_set(v___x_2659_, 1, v___y_2445_);
v___x_2660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2660_, 0, v___x_2659_);
return v___x_2660_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___boxed(lean_object* v_f_2661_, lean_object* v_x_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_){
_start:
{
lean_object* v_res_2669_; 
v_res_2669_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg(v_f_2661_, v_x_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_);
lean_dec(v___y_2667_);
lean_dec_ref(v___y_2666_);
lean_dec(v___y_2665_);
lean_dec_ref(v___y_2664_);
return v_res_2669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg(lean_object* v_f_2670_, lean_object* v_init_2671_, lean_object* v_e_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_){
_start:
{
lean_object* v___x_2678_; 
v___x_2678_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg(v_f_2670_, v_e_2672_, v_init_2671_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_);
if (lean_obj_tag(v___x_2678_) == 0)
{
lean_object* v_a_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2687_; 
v_a_2679_ = lean_ctor_get(v___x_2678_, 0);
v_isSharedCheck_2687_ = !lean_is_exclusive(v___x_2678_);
if (v_isSharedCheck_2687_ == 0)
{
v___x_2681_ = v___x_2678_;
v_isShared_2682_ = v_isSharedCheck_2687_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_a_2679_);
lean_dec(v___x_2678_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2687_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v_snd_2683_; lean_object* v___x_2685_; 
v_snd_2683_ = lean_ctor_get(v_a_2679_, 1);
lean_inc(v_snd_2683_);
lean_dec(v_a_2679_);
if (v_isShared_2682_ == 0)
{
lean_ctor_set(v___x_2681_, 0, v_snd_2683_);
v___x_2685_ = v___x_2681_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v_snd_2683_);
v___x_2685_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
return v___x_2685_;
}
}
}
else
{
lean_object* v_a_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2695_; 
v_a_2688_ = lean_ctor_get(v___x_2678_, 0);
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2678_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2690_ = v___x_2678_;
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_a_2688_);
lean_dec(v___x_2678_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v___x_2693_; 
if (v_isShared_2691_ == 0)
{
v___x_2693_ = v___x_2690_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v_a_2688_);
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
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg___boxed(lean_object* v_f_2696_, lean_object* v_init_2697_, lean_object* v_e_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_){
_start:
{
lean_object* v_res_2704_; 
v_res_2704_ = l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg(v_f_2696_, v_init_2697_, v_e_2698_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_);
lean_dec(v___y_2702_);
lean_dec_ref(v___y_2701_);
lean_dec(v___y_2700_);
lean_dec_ref(v___y_2699_);
return v_res_2704_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(lean_object* v_op_2707_, lean_object* v_as_2708_, size_t v_i_2709_, size_t v_stop_2710_, lean_object* v_b_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_){
_start:
{
lean_object* v_a_2718_; uint8_t v___x_2722_; 
v___x_2722_ = lean_usize_dec_eq(v_i_2709_, v_stop_2710_);
if (v___x_2722_ == 0)
{
lean_object* v___x_2723_; lean_object* v___x_2724_; 
v___x_2723_ = lean_array_uget_borrowed(v_as_2708_, v_i_2709_);
lean_inc(v___y_2715_);
lean_inc_ref(v___y_2714_);
lean_inc(v___y_2713_);
lean_inc_ref(v___y_2712_);
lean_inc(v___x_2723_);
v___x_2724_ = lean_infer_type(v___x_2723_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_);
if (lean_obj_tag(v___x_2724_) == 0)
{
lean_object* v_a_2725_; lean_object* v___x_2726_; 
v_a_2725_ = lean_ctor_get(v___x_2724_, 0);
lean_inc(v_a_2725_);
lean_dec_ref_known(v___x_2724_, 1);
lean_inc_ref(v_op_2707_);
v___x_2726_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v_op_2707_, v_a_2725_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_);
if (lean_obj_tag(v___x_2726_) == 0)
{
lean_object* v_a_2727_; lean_object* v___x_2728_; 
v_a_2727_ = lean_ctor_get(v___x_2726_, 0);
lean_inc(v_a_2727_);
lean_dec_ref_known(v___x_2726_, 1);
v___x_2728_ = l_Array_append___redArg(v_b_2711_, v_a_2727_);
lean_dec(v_a_2727_);
v_a_2718_ = v___x_2728_;
goto v___jp_2717_;
}
else
{
lean_dec_ref(v_b_2711_);
if (lean_obj_tag(v___x_2726_) == 0)
{
lean_object* v_a_2729_; 
v_a_2729_ = lean_ctor_get(v___x_2726_, 0);
lean_inc(v_a_2729_);
lean_dec_ref_known(v___x_2726_, 1);
v_a_2718_ = v_a_2729_;
goto v___jp_2717_;
}
else
{
lean_dec_ref(v_op_2707_);
return v___x_2726_;
}
}
}
else
{
lean_object* v_a_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2737_; 
lean_dec_ref(v_b_2711_);
lean_dec_ref(v_op_2707_);
v_a_2730_ = lean_ctor_get(v___x_2724_, 0);
v_isSharedCheck_2737_ = !lean_is_exclusive(v___x_2724_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2732_ = v___x_2724_;
v_isShared_2733_ = v_isSharedCheck_2737_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_a_2730_);
lean_dec(v___x_2724_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2737_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v___x_2735_; 
if (v_isShared_2733_ == 0)
{
v___x_2735_ = v___x_2732_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v_a_2730_);
v___x_2735_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
return v___x_2735_;
}
}
}
}
else
{
lean_object* v___x_2738_; 
lean_dec_ref(v_op_2707_);
v___x_2738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2738_, 0, v_b_2711_);
return v___x_2738_;
}
v___jp_2717_:
{
size_t v___x_2719_; size_t v___x_2720_; 
v___x_2719_ = ((size_t)1ULL);
v___x_2720_ = lean_usize_add(v_i_2709_, v___x_2719_);
v_i_2709_ = v___x_2720_;
v_b_2711_ = v_a_2718_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0(lean_object* v_op_2739_, lean_object* v_args_2740_, lean_object* v_body_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_){
_start:
{
lean_object* v___x_2747_; 
lean_inc_ref(v_op_2739_);
v___x_2747_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v_op_2739_, v_body_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_);
if (lean_obj_tag(v___x_2747_) == 0)
{
lean_object* v_a_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2769_; 
v_a_2748_ = lean_ctor_get(v___x_2747_, 0);
v_isSharedCheck_2769_ = !lean_is_exclusive(v___x_2747_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2750_ = v___x_2747_;
v_isShared_2751_ = v_isSharedCheck_2769_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_a_2748_);
lean_dec(v___x_2747_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2769_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; uint8_t v___x_2755_; 
v___x_2752_ = l_Array_reverse___redArg(v_a_2748_);
v___x_2753_ = lean_unsigned_to_nat(0u);
v___x_2754_ = lean_array_get_size(v_args_2740_);
v___x_2755_ = lean_nat_dec_lt(v___x_2753_, v___x_2754_);
if (v___x_2755_ == 0)
{
lean_object* v___x_2757_; 
lean_dec_ref(v_op_2739_);
if (v_isShared_2751_ == 0)
{
lean_ctor_set(v___x_2750_, 0, v___x_2752_);
v___x_2757_ = v___x_2750_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v___x_2752_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
return v___x_2757_;
}
}
else
{
uint8_t v___x_2759_; 
v___x_2759_ = lean_nat_dec_le(v___x_2754_, v___x_2754_);
if (v___x_2759_ == 0)
{
if (v___x_2755_ == 0)
{
lean_object* v___x_2761_; 
lean_dec_ref(v_op_2739_);
if (v_isShared_2751_ == 0)
{
lean_ctor_set(v___x_2750_, 0, v___x_2752_);
v___x_2761_ = v___x_2750_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v___x_2752_);
v___x_2761_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
return v___x_2761_;
}
}
else
{
size_t v___x_2763_; size_t v___x_2764_; lean_object* v___x_2765_; 
lean_del_object(v___x_2750_);
v___x_2763_ = ((size_t)0ULL);
v___x_2764_ = lean_usize_of_nat(v___x_2754_);
v___x_2765_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(v_op_2739_, v_args_2740_, v___x_2763_, v___x_2764_, v___x_2752_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_);
return v___x_2765_;
}
}
else
{
size_t v___x_2766_; size_t v___x_2767_; lean_object* v___x_2768_; 
lean_del_object(v___x_2750_);
v___x_2766_ = ((size_t)0ULL);
v___x_2767_ = lean_usize_of_nat(v___x_2754_);
v___x_2768_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(v_op_2739_, v_args_2740_, v___x_2766_, v___x_2767_, v___x_2752_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_);
return v___x_2768_;
}
}
}
}
else
{
lean_dec_ref(v_op_2739_);
return v___x_2747_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed(lean_object* v_op_2770_, lean_object* v_args_2771_, lean_object* v_body_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_){
_start:
{
lean_object* v_res_2778_; 
v_res_2778_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0(v_op_2770_, v_args_2771_, v_body_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_);
lean_dec(v___y_2776_);
lean_dec_ref(v___y_2775_);
lean_dec(v___y_2774_);
lean_dec_ref(v___y_2773_);
lean_dec_ref(v_args_2771_);
return v_res_2778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3___boxed(lean_object* v_op_2779_, lean_object* v_a_2780_, lean_object* v_f_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_){
_start:
{
lean_object* v_res_2787_; 
v_res_2787_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3(v_op_2779_, v_a_2780_, v_f_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_);
lean_dec(v___y_2785_);
lean_dec_ref(v___y_2784_);
lean_dec(v___y_2783_);
lean_dec_ref(v___y_2782_);
return v_res_2787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(lean_object* v_op_2788_, lean_object* v_e_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_){
_start:
{
switch(lean_obj_tag(v_e_2789_))
{
case 0:
{
lean_object* v___x_2795_; lean_object* v___x_2796_; 
lean_dec_ref_known(v_e_2789_, 1);
lean_dec_ref(v_op_2788_);
v___x_2795_ = ((lean_object*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___closed__0));
v___x_2796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2796_, 0, v___x_2795_);
return v___x_2796_;
}
case 7:
{
lean_object* v___f_2797_; uint8_t v___x_2798_; lean_object* v___x_2799_; 
v___f_2797_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2797_, 0, v_op_2788_);
v___x_2798_ = 0;
v___x_2799_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(v_e_2789_, v___f_2797_, v___x_2798_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_);
return v___x_2799_;
}
case 6:
{
lean_object* v___f_2800_; uint8_t v___x_2801_; uint8_t v___x_2802_; lean_object* v___x_2803_; 
v___f_2800_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2800_, 0, v_op_2788_);
v___x_2801_ = 0;
v___x_2802_ = 1;
v___x_2803_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(v_e_2789_, v___f_2800_, v___x_2801_, v___x_2802_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_);
return v___x_2803_;
}
case 8:
{
lean_object* v___f_2804_; uint8_t v___x_2805_; uint8_t v___x_2806_; lean_object* v___x_2807_; 
v___f_2804_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2804_, 0, v_op_2788_);
v___x_2805_ = 0;
v___x_2806_ = 1;
v___x_2807_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(v_e_2789_, v___f_2804_, v___x_2805_, v___x_2806_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_);
return v___x_2807_;
}
default: 
{
lean_object* v___f_2808_; lean_object* v___x_2809_; 
lean_inc_ref(v_op_2788_);
v___f_2808_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3___boxed), 8, 1);
lean_closure_set(v___f_2808_, 0, v_op_2788_);
lean_inc(v_a_2793_);
lean_inc_ref(v_a_2792_);
lean_inc(v_a_2791_);
lean_inc_ref(v_a_2790_);
lean_inc_ref(v_e_2789_);
v___x_2809_ = lean_apply_6(v_op_2788_, v_e_2789_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_, lean_box(0));
if (lean_obj_tag(v___x_2809_) == 0)
{
lean_object* v_a_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; 
v_a_2810_ = lean_ctor_get(v___x_2809_, 0);
lean_inc(v_a_2810_);
lean_dec_ref_known(v___x_2809_, 1);
v___x_2811_ = l_Array_reverse___redArg(v_a_2810_);
v___x_2812_ = l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg(v___f_2808_, v___x_2811_, v_e_2789_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_);
return v___x_2812_;
}
else
{
lean_dec_ref(v___f_2808_);
lean_dec_ref(v_e_2789_);
return v___x_2809_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3(lean_object* v_op_2813_, lean_object* v_a_2814_, lean_object* v_f_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_){
_start:
{
lean_object* v___x_2821_; 
v___x_2821_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v_op_2813_, v_f_2815_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_);
if (lean_obj_tag(v___x_2821_) == 0)
{
lean_object* v_a_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2830_; 
v_a_2822_ = lean_ctor_get(v___x_2821_, 0);
v_isSharedCheck_2830_ = !lean_is_exclusive(v___x_2821_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2824_ = v___x_2821_;
v_isShared_2825_ = v_isSharedCheck_2830_;
goto v_resetjp_2823_;
}
else
{
lean_inc(v_a_2822_);
lean_dec(v___x_2821_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_2830_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
lean_object* v___x_2826_; lean_object* v___x_2828_; 
v___x_2826_ = l_Array_append___redArg(v_a_2814_, v_a_2822_);
lean_dec(v_a_2822_);
if (v_isShared_2825_ == 0)
{
lean_ctor_set(v___x_2824_, 0, v___x_2826_);
v___x_2828_ = v___x_2824_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v___x_2826_);
v___x_2828_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
return v___x_2828_;
}
}
}
else
{
lean_dec_ref(v_a_2814_);
return v___x_2821_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg___boxed(lean_object* v_op_2831_, lean_object* v_as_2832_, lean_object* v_i_2833_, lean_object* v_stop_2834_, lean_object* v_b_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_){
_start:
{
size_t v_i_boxed_2841_; size_t v_stop_boxed_2842_; lean_object* v_res_2843_; 
v_i_boxed_2841_ = lean_unbox_usize(v_i_2833_);
lean_dec(v_i_2833_);
v_stop_boxed_2842_ = lean_unbox_usize(v_stop_2834_);
lean_dec(v_stop_2834_);
v_res_2843_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(v_op_2831_, v_as_2832_, v_i_boxed_2841_, v_stop_boxed_2842_, v_b_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
lean_dec(v___y_2839_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2837_);
lean_dec_ref(v___y_2836_);
lean_dec_ref(v_as_2832_);
return v_res_2843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___boxed(lean_object* v_op_2844_, lean_object* v_e_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_){
_start:
{
lean_object* v_res_2851_; 
v_res_2851_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v_op_2844_, v_e_2845_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_);
lean_dec(v_a_2849_);
lean_dec_ref(v_a_2848_);
lean_dec(v_a_2847_);
lean_dec_ref(v_a_2846_);
return v_res_2851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches(lean_object* v_00_u03b1_2852_, lean_object* v_op_2853_, lean_object* v_e_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_){
_start:
{
lean_object* v___x_2860_; 
v___x_2860_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v_op_2853_, v_e_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_);
return v___x_2860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___boxed(lean_object* v_00_u03b1_2861_, lean_object* v_op_2862_, lean_object* v_e_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_){
_start:
{
lean_object* v_res_2869_; 
v_res_2869_ = l_Lean_Meta_Rewrites_getSubexpressionMatches(v_00_u03b1_2861_, v_op_2862_, v_e_2863_, v_a_2864_, v_a_2865_, v_a_2866_, v_a_2867_);
lean_dec(v_a_2867_);
lean_dec_ref(v_a_2866_);
lean_dec(v_a_2865_);
lean_dec_ref(v_a_2864_);
return v_res_2869_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0(lean_object* v_00_u03b1_2870_, lean_object* v_op_2871_, lean_object* v_as_2872_, size_t v_i_2873_, size_t v_stop_2874_, lean_object* v_b_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_){
_start:
{
lean_object* v___x_2881_; 
v___x_2881_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(v_op_2871_, v_as_2872_, v_i_2873_, v_stop_2874_, v_b_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_);
return v___x_2881_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___boxed(lean_object* v_00_u03b1_2882_, lean_object* v_op_2883_, lean_object* v_as_2884_, lean_object* v_i_2885_, lean_object* v_stop_2886_, lean_object* v_b_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_){
_start:
{
size_t v_i_boxed_2893_; size_t v_stop_boxed_2894_; lean_object* v_res_2895_; 
v_i_boxed_2893_ = lean_unbox_usize(v_i_2885_);
lean_dec(v_i_2885_);
v_stop_boxed_2894_ = lean_unbox_usize(v_stop_2886_);
lean_dec(v_stop_2886_);
v_res_2895_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0(v_00_u03b1_2882_, v_op_2883_, v_as_2884_, v_i_boxed_2893_, v_stop_boxed_2894_, v_b_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_);
lean_dec(v___y_2891_);
lean_dec_ref(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec_ref(v_as_2884_);
return v_res_2895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3(lean_object* v_00_u03b1_2896_, lean_object* v_f_2897_, lean_object* v_x_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_){
_start:
{
lean_object* v___x_2905_; 
v___x_2905_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg(v_f_2897_, v_x_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
return v___x_2905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___boxed(lean_object* v_00_u03b1_2906_, lean_object* v_f_2907_, lean_object* v_x_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_){
_start:
{
lean_object* v_res_2915_; 
v_res_2915_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3(v_00_u03b1_2906_, v_f_2907_, v_x_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_);
lean_dec(v___y_2913_);
lean_dec_ref(v___y_2912_);
lean_dec(v___y_2911_);
lean_dec_ref(v___y_2910_);
return v_res_2915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3(lean_object* v_00_u03b1_2916_, lean_object* v_f_2917_, lean_object* v_init_2918_, lean_object* v_e_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_){
_start:
{
lean_object* v___x_2925_; 
v___x_2925_ = l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg(v_f_2917_, v_init_2918_, v_e_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_);
return v___x_2925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___boxed(lean_object* v_00_u03b1_2926_, lean_object* v_f_2927_, lean_object* v_init_2928_, lean_object* v_e_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_){
_start:
{
lean_object* v_res_2935_; 
v_res_2935_ = l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3(v_00_u03b1_2926_, v_f_2927_, v_init_2928_, v_e_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
lean_dec(v___y_2931_);
lean_dec_ref(v___y_2930_);
return v_res_2935_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__3(size_t v_sz_2936_, size_t v_i_2937_, lean_object* v_bs_2938_){
_start:
{
uint8_t v___x_2939_; 
v___x_2939_ = lean_usize_dec_lt(v_i_2937_, v_sz_2936_);
if (v___x_2939_ == 0)
{
return v_bs_2938_;
}
else
{
lean_object* v_v_2940_; lean_object* v_fst_2941_; lean_object* v_snd_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2956_; 
v_v_2940_ = lean_array_uget(v_bs_2938_, v_i_2937_);
v_fst_2941_ = lean_ctor_get(v_v_2940_, 0);
v_snd_2942_ = lean_ctor_get(v_v_2940_, 1);
v_isSharedCheck_2956_ = !lean_is_exclusive(v_v_2940_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2944_ = v_v_2940_;
v_isShared_2945_ = v_isSharedCheck_2956_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_snd_2942_);
lean_inc(v_fst_2941_);
lean_dec(v_v_2940_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2956_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v___x_2946_; lean_object* v_bs_x27_2947_; lean_object* v___x_2948_; lean_object* v___x_2950_; 
v___x_2946_ = lean_unsigned_to_nat(0u);
v_bs_x27_2947_ = lean_array_uset(v_bs_2938_, v_i_2937_, v___x_2946_);
v___x_2948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2948_, 0, v_fst_2941_);
if (v_isShared_2945_ == 0)
{
lean_ctor_set(v___x_2944_, 0, v___x_2948_);
v___x_2950_ = v___x_2944_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v___x_2948_);
lean_ctor_set(v_reuseFailAlloc_2955_, 1, v_snd_2942_);
v___x_2950_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
size_t v___x_2951_; size_t v___x_2952_; lean_object* v___x_2953_; 
v___x_2951_ = ((size_t)1ULL);
v___x_2952_ = lean_usize_add(v_i_2937_, v___x_2951_);
v___x_2953_ = lean_array_uset(v_bs_x27_2947_, v_i_2937_, v___x_2950_);
v_i_2937_ = v___x_2952_;
v_bs_2938_ = v___x_2953_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__3___boxed(lean_object* v_sz_2957_, lean_object* v_i_2958_, lean_object* v_bs_2959_){
_start:
{
size_t v_sz_boxed_2960_; size_t v_i_boxed_2961_; lean_object* v_res_2962_; 
v_sz_boxed_2960_ = lean_unbox_usize(v_sz_2957_);
lean_dec(v_sz_2957_);
v_i_boxed_2961_ = lean_unbox_usize(v_i_2958_);
lean_dec(v_i_2958_);
v_res_2962_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__3(v_sz_boxed_2960_, v_i_boxed_2961_, v_bs_2959_);
return v_res_2962_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0___redArg(lean_object* v_xs_2963_, lean_object* v_j_2964_){
_start:
{
lean_object* v_zero_2965_; uint8_t v_isZero_2966_; 
v_zero_2965_ = lean_unsigned_to_nat(0u);
v_isZero_2966_ = lean_nat_dec_eq(v_j_2964_, v_zero_2965_);
if (v_isZero_2966_ == 1)
{
lean_dec(v_j_2964_);
return v_xs_2963_;
}
else
{
lean_object* v___x_2967_; lean_object* v_snd_2968_; lean_object* v_snd_2969_; lean_object* v_one_2970_; lean_object* v_n_2971_; lean_object* v___x_2972_; lean_object* v_snd_2973_; lean_object* v_snd_2974_; uint8_t v___x_2975_; 
v___x_2967_ = lean_array_fget_borrowed(v_xs_2963_, v_j_2964_);
v_snd_2968_ = lean_ctor_get(v___x_2967_, 1);
v_snd_2969_ = lean_ctor_get(v_snd_2968_, 1);
v_one_2970_ = lean_unsigned_to_nat(1u);
v_n_2971_ = lean_nat_sub(v_j_2964_, v_one_2970_);
v___x_2972_ = lean_array_fget_borrowed(v_xs_2963_, v_n_2971_);
v_snd_2973_ = lean_ctor_get(v___x_2972_, 1);
v_snd_2974_ = lean_ctor_get(v_snd_2973_, 1);
v___x_2975_ = lean_nat_dec_lt(v_snd_2974_, v_snd_2969_);
if (v___x_2975_ == 0)
{
lean_dec(v_n_2971_);
lean_dec(v_j_2964_);
return v_xs_2963_;
}
else
{
lean_object* v___x_2976_; 
v___x_2976_ = lean_array_fswap(v_xs_2963_, v_j_2964_, v_n_2971_);
lean_dec(v_j_2964_);
v_xs_2963_ = v___x_2976_;
v_j_2964_ = v_n_2971_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0(lean_object* v_xs_2978_, lean_object* v_i_2979_, lean_object* v_fuel_2980_){
_start:
{
lean_object* v_zero_2981_; uint8_t v_isZero_2982_; 
v_zero_2981_ = lean_unsigned_to_nat(0u);
v_isZero_2982_ = lean_nat_dec_eq(v_fuel_2980_, v_zero_2981_);
if (v_isZero_2982_ == 1)
{
lean_dec(v_fuel_2980_);
lean_dec(v_i_2979_);
return v_xs_2978_;
}
else
{
lean_object* v___x_2983_; uint8_t v___x_2984_; 
v___x_2983_ = lean_array_get_size(v_xs_2978_);
v___x_2984_ = lean_nat_dec_lt(v_i_2979_, v___x_2983_);
if (v___x_2984_ == 0)
{
lean_dec(v_fuel_2980_);
lean_dec(v_i_2979_);
return v_xs_2978_;
}
else
{
lean_object* v_one_2985_; lean_object* v_n_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; 
v_one_2985_ = lean_unsigned_to_nat(1u);
v_n_2986_ = lean_nat_sub(v_fuel_2980_, v_one_2985_);
lean_dec(v_fuel_2980_);
lean_inc(v_i_2979_);
v___x_2987_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0___redArg(v_xs_2978_, v_i_2979_);
v___x_2988_ = lean_nat_add(v_i_2979_, v_one_2985_);
lean_dec(v_i_2979_);
v_xs_2978_ = v___x_2987_;
v_i_2979_ = v___x_2988_;
v_fuel_2980_ = v_n_2986_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__2(size_t v_sz_2990_, size_t v_i_2991_, lean_object* v_bs_2992_){
_start:
{
uint8_t v___x_2993_; 
v___x_2993_ = lean_usize_dec_lt(v_i_2991_, v_sz_2990_);
if (v___x_2993_ == 0)
{
return v_bs_2992_;
}
else
{
lean_object* v_v_2994_; lean_object* v_fst_2995_; lean_object* v_snd_2996_; lean_object* v___x_2998_; uint8_t v_isShared_2999_; uint8_t v_isSharedCheck_3010_; 
v_v_2994_ = lean_array_uget(v_bs_2992_, v_i_2991_);
v_fst_2995_ = lean_ctor_get(v_v_2994_, 0);
v_snd_2996_ = lean_ctor_get(v_v_2994_, 1);
v_isSharedCheck_3010_ = !lean_is_exclusive(v_v_2994_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_2998_ = v_v_2994_;
v_isShared_2999_ = v_isSharedCheck_3010_;
goto v_resetjp_2997_;
}
else
{
lean_inc(v_snd_2996_);
lean_inc(v_fst_2995_);
lean_dec(v_v_2994_);
v___x_2998_ = lean_box(0);
v_isShared_2999_ = v_isSharedCheck_3010_;
goto v_resetjp_2997_;
}
v_resetjp_2997_:
{
lean_object* v___x_3000_; lean_object* v_bs_x27_3001_; lean_object* v___x_3002_; lean_object* v___x_3004_; 
v___x_3000_ = lean_unsigned_to_nat(0u);
v_bs_x27_3001_ = lean_array_uset(v_bs_2992_, v_i_2991_, v___x_3000_);
v___x_3002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3002_, 0, v_fst_2995_);
if (v_isShared_2999_ == 0)
{
lean_ctor_set(v___x_2998_, 0, v___x_3002_);
v___x_3004_ = v___x_2998_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v___x_3002_);
lean_ctor_set(v_reuseFailAlloc_3009_, 1, v_snd_2996_);
v___x_3004_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
size_t v___x_3005_; size_t v___x_3006_; lean_object* v___x_3007_; 
v___x_3005_ = ((size_t)1ULL);
v___x_3006_ = lean_usize_add(v_i_2991_, v___x_3005_);
v___x_3007_ = lean_array_uset(v_bs_x27_3001_, v_i_2991_, v___x_3004_);
v_i_2991_ = v___x_3006_;
v_bs_2992_ = v___x_3007_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__2___boxed(lean_object* v_sz_3011_, lean_object* v_i_3012_, lean_object* v_bs_3013_){
_start:
{
size_t v_sz_boxed_3014_; size_t v_i_boxed_3015_; lean_object* v_res_3016_; 
v_sz_boxed_3014_ = lean_unbox_usize(v_sz_3011_);
lean_dec(v_sz_3011_);
v_i_boxed_3015_ = lean_unbox_usize(v_i_3012_);
lean_dec(v_i_3012_);
v_res_3016_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__2(v_sz_boxed_3014_, v_i_boxed_3015_, v_bs_3013_);
return v_res_3016_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg(lean_object* v_forbidden_3017_, lean_object* v_as_3018_, size_t v_sz_3019_, size_t v_i_3020_, lean_object* v_b_3021_){
_start:
{
lean_object* v_a_3024_; uint8_t v___x_3028_; 
v___x_3028_ = lean_usize_dec_lt(v_i_3020_, v_sz_3019_);
if (v___x_3028_ == 0)
{
lean_object* v___x_3029_; 
v___x_3029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3029_, 0, v_b_3021_);
return v___x_3029_;
}
else
{
lean_object* v_a_3030_; lean_object* v_snd_3031_; lean_object* v_snd_3032_; lean_object* v_fst_3033_; lean_object* v_fst_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3092_; 
v_a_3030_ = lean_array_uget(v_as_3018_, v_i_3020_);
v_snd_3031_ = lean_ctor_get(v_a_3030_, 1);
lean_inc(v_snd_3031_);
v_snd_3032_ = lean_ctor_get(v_b_3021_, 1);
lean_inc(v_snd_3032_);
v_fst_3033_ = lean_ctor_get(v_a_3030_, 0);
v_fst_3034_ = lean_ctor_get(v_snd_3031_, 0);
v_isSharedCheck_3092_ = !lean_is_exclusive(v_snd_3031_);
if (v_isSharedCheck_3092_ == 0)
{
lean_object* v_unused_3093_; 
v_unused_3093_ = lean_ctor_get(v_snd_3031_, 1);
lean_dec(v_unused_3093_);
v___x_3036_ = v_snd_3031_;
v_isShared_3037_ = v_isSharedCheck_3092_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_fst_3034_);
lean_dec(v_snd_3031_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3092_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v_fst_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3090_; 
v_fst_3038_ = lean_ctor_get(v_b_3021_, 0);
v_isSharedCheck_3090_ = !lean_is_exclusive(v_b_3021_);
if (v_isSharedCheck_3090_ == 0)
{
lean_object* v_unused_3091_; 
v_unused_3091_ = lean_ctor_get(v_b_3021_, 1);
lean_dec(v_unused_3091_);
v___x_3040_ = v_b_3021_;
v_isShared_3041_ = v_isSharedCheck_3090_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_fst_3038_);
lean_dec(v_b_3021_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3090_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v_fst_3042_; lean_object* v_snd_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3089_; 
v_fst_3042_ = lean_ctor_get(v_snd_3032_, 0);
v_snd_3043_ = lean_ctor_get(v_snd_3032_, 1);
v_isSharedCheck_3089_ = !lean_is_exclusive(v_snd_3032_);
if (v_isSharedCheck_3089_ == 0)
{
v___x_3045_ = v_snd_3032_;
v_isShared_3046_ = v_isSharedCheck_3089_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_snd_3043_);
lean_inc(v_fst_3042_);
lean_dec(v_snd_3032_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3089_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
uint8_t v___x_3061_; 
v___x_3061_ = l_Lean_NameSet_contains(v_forbidden_3017_, v_fst_3033_);
if (v___x_3061_ == 0)
{
uint8_t v___x_3062_; 
v___x_3062_ = lean_unbox(v_fst_3034_);
lean_dec(v_fst_3034_);
if (v___x_3062_ == 0)
{
uint8_t v___x_3063_; 
lean_inc(v_fst_3033_);
lean_del_object(v___x_3045_);
lean_del_object(v___x_3040_);
v___x_3063_ = l_Lean_NameSet_contains(v_fst_3038_, v_fst_3033_);
if (v___x_3063_ == 0)
{
if (v___x_3028_ == 0)
{
lean_dec(v_fst_3033_);
lean_dec(v_a_3030_);
goto v___jp_3056_;
}
else
{
lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; 
lean_del_object(v___x_3036_);
v___x_3064_ = lean_array_push(v_snd_3043_, v_a_3030_);
v___x_3065_ = l_Lean_NameSet_insert(v_fst_3038_, v_fst_3033_);
v___x_3066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3066_, 0, v_fst_3042_);
lean_ctor_set(v___x_3066_, 1, v___x_3064_);
v___x_3067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3067_, 0, v___x_3065_);
lean_ctor_set(v___x_3067_, 1, v___x_3066_);
v_a_3024_ = v___x_3067_;
goto v___jp_3023_;
}
}
else
{
lean_dec(v_fst_3033_);
lean_dec(v_a_3030_);
goto v___jp_3056_;
}
}
else
{
uint8_t v___x_3068_; 
lean_del_object(v___x_3036_);
v___x_3068_ = l_Lean_NameSet_contains(v_fst_3042_, v_fst_3033_);
if (v___x_3068_ == 0)
{
lean_inc(v_fst_3033_);
goto v___jp_3047_;
}
else
{
if (v___x_3061_ == 0)
{
lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3076_; 
lean_del_object(v___x_3045_);
lean_del_object(v___x_3040_);
v_isSharedCheck_3076_ = !lean_is_exclusive(v_a_3030_);
if (v_isSharedCheck_3076_ == 0)
{
lean_object* v_unused_3077_; lean_object* v_unused_3078_; 
v_unused_3077_ = lean_ctor_get(v_a_3030_, 1);
lean_dec(v_unused_3077_);
v_unused_3078_ = lean_ctor_get(v_a_3030_, 0);
lean_dec(v_unused_3078_);
v___x_3070_ = v_a_3030_;
v_isShared_3071_ = v_isSharedCheck_3076_;
goto v_resetjp_3069_;
}
else
{
lean_dec(v_a_3030_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3076_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
lean_object* v___x_3073_; 
if (v_isShared_3071_ == 0)
{
lean_ctor_set(v___x_3070_, 1, v_snd_3043_);
lean_ctor_set(v___x_3070_, 0, v_fst_3042_);
v___x_3073_ = v___x_3070_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v_fst_3042_);
lean_ctor_set(v_reuseFailAlloc_3075_, 1, v_snd_3043_);
v___x_3073_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
lean_object* v___x_3074_; 
v___x_3074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3074_, 0, v_fst_3038_);
lean_ctor_set(v___x_3074_, 1, v___x_3073_);
v_a_3024_ = v___x_3074_;
goto v___jp_3023_;
}
}
}
else
{
lean_inc(v_fst_3033_);
goto v___jp_3047_;
}
}
}
}
else
{
lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3086_; 
lean_del_object(v___x_3045_);
lean_del_object(v___x_3040_);
lean_del_object(v___x_3036_);
lean_dec(v_fst_3034_);
v_isSharedCheck_3086_ = !lean_is_exclusive(v_a_3030_);
if (v_isSharedCheck_3086_ == 0)
{
lean_object* v_unused_3087_; lean_object* v_unused_3088_; 
v_unused_3087_ = lean_ctor_get(v_a_3030_, 1);
lean_dec(v_unused_3087_);
v_unused_3088_ = lean_ctor_get(v_a_3030_, 0);
lean_dec(v_unused_3088_);
v___x_3080_ = v_a_3030_;
v_isShared_3081_ = v_isSharedCheck_3086_;
goto v_resetjp_3079_;
}
else
{
lean_dec(v_a_3030_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3086_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
lean_object* v___x_3083_; 
if (v_isShared_3081_ == 0)
{
lean_ctor_set(v___x_3080_, 1, v_snd_3043_);
lean_ctor_set(v___x_3080_, 0, v_fst_3042_);
v___x_3083_ = v___x_3080_;
goto v_reusejp_3082_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v_fst_3042_);
lean_ctor_set(v_reuseFailAlloc_3085_, 1, v_snd_3043_);
v___x_3083_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3082_;
}
v_reusejp_3082_:
{
lean_object* v___x_3084_; 
v___x_3084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3084_, 0, v_fst_3038_);
lean_ctor_set(v___x_3084_, 1, v___x_3083_);
v_a_3024_ = v___x_3084_;
goto v___jp_3023_;
}
}
}
v___jp_3047_:
{
lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3051_; 
v___x_3048_ = lean_array_push(v_snd_3043_, v_a_3030_);
v___x_3049_ = l_Lean_NameSet_insert(v_fst_3042_, v_fst_3033_);
if (v_isShared_3046_ == 0)
{
lean_ctor_set(v___x_3045_, 1, v___x_3048_);
lean_ctor_set(v___x_3045_, 0, v___x_3049_);
v___x_3051_ = v___x_3045_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v___x_3049_);
lean_ctor_set(v_reuseFailAlloc_3055_, 1, v___x_3048_);
v___x_3051_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
lean_object* v___x_3053_; 
if (v_isShared_3041_ == 0)
{
lean_ctor_set(v___x_3040_, 1, v___x_3051_);
v___x_3053_ = v___x_3040_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v_fst_3038_);
lean_ctor_set(v_reuseFailAlloc_3054_, 1, v___x_3051_);
v___x_3053_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
v_a_3024_ = v___x_3053_;
goto v___jp_3023_;
}
}
}
v___jp_3056_:
{
lean_object* v___x_3058_; 
if (v_isShared_3037_ == 0)
{
lean_ctor_set(v___x_3036_, 1, v_snd_3043_);
lean_ctor_set(v___x_3036_, 0, v_fst_3042_);
v___x_3058_ = v___x_3036_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3060_, 0, v_fst_3042_);
lean_ctor_set(v_reuseFailAlloc_3060_, 1, v_snd_3043_);
v___x_3058_ = v_reuseFailAlloc_3060_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
lean_object* v___x_3059_; 
v___x_3059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3059_, 0, v_fst_3038_);
lean_ctor_set(v___x_3059_, 1, v___x_3058_);
v_a_3024_ = v___x_3059_;
goto v___jp_3023_;
}
}
}
}
}
}
v___jp_3023_:
{
size_t v___x_3025_; size_t v___x_3026_; 
v___x_3025_ = ((size_t)1ULL);
v___x_3026_ = lean_usize_add(v_i_3020_, v___x_3025_);
v_i_3020_ = v___x_3026_;
v_b_3021_ = v_a_3024_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg___boxed(lean_object* v_forbidden_3094_, lean_object* v_as_3095_, lean_object* v_sz_3096_, lean_object* v_i_3097_, lean_object* v_b_3098_, lean_object* v___y_3099_){
_start:
{
size_t v_sz_boxed_3100_; size_t v_i_boxed_3101_; lean_object* v_res_3102_; 
v_sz_boxed_3100_ = lean_unbox_usize(v_sz_3096_);
lean_dec(v_sz_3096_);
v_i_boxed_3101_ = lean_unbox_usize(v_i_3097_);
lean_dec(v_i_3097_);
v_res_3102_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg(v_forbidden_3094_, v_as_3095_, v_sz_boxed_3100_, v_i_boxed_3101_, v_b_3098_);
lean_dec_ref(v_as_3095_);
lean_dec(v_forbidden_3094_);
return v_res_3102_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__2(void){
_start:
{
lean_object* v___x_3106_; lean_object* v___x_3107_; 
v___x_3106_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__1));
v___x_3107_ = l_Lean_MessageData_ofFormat(v___x_3106_);
return v___x_3107_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__3(void){
_start:
{
lean_object* v___x_3108_; lean_object* v___x_3109_; 
v___x_3108_ = lean_box(1);
v___x_3109_ = l_Lean_MessageData_ofFormat(v___x_3108_);
return v___x_3109_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4(lean_object* v_a_3112_, lean_object* v_a_3113_){
_start:
{
if (lean_obj_tag(v_a_3112_) == 0)
{
lean_object* v___x_3114_; 
v___x_3114_ = l_List_reverse___redArg(v_a_3113_);
return v___x_3114_;
}
else
{
lean_object* v_head_3115_; lean_object* v_snd_3116_; lean_object* v_tail_3117_; lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3162_; 
v_head_3115_ = lean_ctor_get(v_a_3112_, 0);
lean_inc(v_head_3115_);
v_snd_3116_ = lean_ctor_get(v_head_3115_, 1);
lean_inc(v_snd_3116_);
v_tail_3117_ = lean_ctor_get(v_a_3112_, 1);
v_isSharedCheck_3162_ = !lean_is_exclusive(v_a_3112_);
if (v_isSharedCheck_3162_ == 0)
{
lean_object* v_unused_3163_; 
v_unused_3163_ = lean_ctor_get(v_a_3112_, 0);
lean_dec(v_unused_3163_);
v___x_3119_ = v_a_3112_;
v_isShared_3120_ = v_isSharedCheck_3162_;
goto v_resetjp_3118_;
}
else
{
lean_inc(v_tail_3117_);
lean_dec(v_a_3112_);
v___x_3119_ = lean_box(0);
v_isShared_3120_ = v_isSharedCheck_3162_;
goto v_resetjp_3118_;
}
v_resetjp_3118_:
{
lean_object* v_fst_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3160_; 
v_fst_3121_ = lean_ctor_get(v_head_3115_, 0);
v_isSharedCheck_3160_ = !lean_is_exclusive(v_head_3115_);
if (v_isSharedCheck_3160_ == 0)
{
lean_object* v_unused_3161_; 
v_unused_3161_ = lean_ctor_get(v_head_3115_, 1);
lean_dec(v_unused_3161_);
v___x_3123_ = v_head_3115_;
v_isShared_3124_ = v_isSharedCheck_3160_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_fst_3121_);
lean_dec(v_head_3115_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3160_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v_fst_3125_; lean_object* v_snd_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3159_; 
v_fst_3125_ = lean_ctor_get(v_snd_3116_, 0);
v_snd_3126_ = lean_ctor_get(v_snd_3116_, 1);
v_isSharedCheck_3159_ = !lean_is_exclusive(v_snd_3116_);
if (v_isSharedCheck_3159_ == 0)
{
v___x_3128_ = v_snd_3116_;
v_isShared_3129_ = v_isSharedCheck_3159_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_snd_3126_);
lean_inc(v_fst_3125_);
lean_dec(v_snd_3116_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3159_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3133_; 
v___x_3130_ = l_Lean_MessageData_ofName(v_fst_3121_);
v___x_3131_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__2, &l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__2_once, _init_l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__2);
if (v_isShared_3129_ == 0)
{
lean_ctor_set_tag(v___x_3128_, 7);
lean_ctor_set(v___x_3128_, 1, v___x_3131_);
lean_ctor_set(v___x_3128_, 0, v___x_3130_);
v___x_3133_ = v___x_3128_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v___x_3130_);
lean_ctor_set(v_reuseFailAlloc_3158_, 1, v___x_3131_);
v___x_3133_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
lean_object* v___x_3134_; lean_object* v___x_3136_; 
v___x_3134_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__3, &l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__3_once, _init_l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__3);
if (v_isShared_3124_ == 0)
{
lean_ctor_set_tag(v___x_3123_, 7);
lean_ctor_set(v___x_3123_, 1, v___x_3134_);
lean_ctor_set(v___x_3123_, 0, v___x_3133_);
v___x_3136_ = v___x_3123_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3157_; 
v_reuseFailAlloc_3157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3157_, 0, v___x_3133_);
lean_ctor_set(v_reuseFailAlloc_3157_, 1, v___x_3134_);
v___x_3136_ = v_reuseFailAlloc_3157_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
lean_object* v___y_3138_; uint8_t v___x_3154_; 
v___x_3154_ = lean_unbox(v_fst_3125_);
lean_dec(v_fst_3125_);
if (v___x_3154_ == 0)
{
lean_object* v___x_3155_; 
v___x_3155_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__4));
v___y_3138_ = v___x_3155_;
goto v___jp_3137_;
}
else
{
lean_object* v___x_3156_; 
v___x_3156_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__5));
v___y_3138_ = v___x_3156_;
goto v___jp_3137_;
}
v___jp_3137_:
{
lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3151_; 
lean_inc_ref(v___y_3138_);
v___x_3139_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3139_, 0, v___y_3138_);
v___x_3140_ = l_Lean_MessageData_ofFormat(v___x_3139_);
v___x_3141_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3141_, 0, v___x_3140_);
lean_ctor_set(v___x_3141_, 1, v___x_3131_);
v___x_3142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3142_, 0, v___x_3141_);
lean_ctor_set(v___x_3142_, 1, v___x_3134_);
v___x_3143_ = l_Nat_reprFast(v_snd_3126_);
v___x_3144_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3144_, 0, v___x_3143_);
v___x_3145_ = l_Lean_MessageData_ofFormat(v___x_3144_);
v___x_3146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3146_, 0, v___x_3142_);
lean_ctor_set(v___x_3146_, 1, v___x_3145_);
v___x_3147_ = l_Lean_MessageData_paren(v___x_3146_);
v___x_3148_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3148_, 0, v___x_3136_);
lean_ctor_set(v___x_3148_, 1, v___x_3147_);
v___x_3149_ = l_Lean_MessageData_paren(v___x_3148_);
if (v_isShared_3120_ == 0)
{
lean_ctor_set(v___x_3119_, 1, v_a_3113_);
lean_ctor_set(v___x_3119_, 0, v___x_3149_);
v___x_3151_ = v___x_3119_;
goto v_reusejp_3150_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v___x_3149_);
lean_ctor_set(v_reuseFailAlloc_3153_, 1, v_a_3113_);
v___x_3151_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3150_;
}
v_reusejp_3150_:
{
v_a_3112_ = v_tail_3117_;
v_a_3113_ = v___x_3151_;
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
lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; 
v___x_3166_ = ((lean_object*)(l_Lean_Meta_Rewrites_rewriteCandidates___closed__0));
v___x_3167_ = l_Lean_NameSet_empty;
v___x_3168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3168_, 0, v___x_3167_);
lean_ctor_set(v___x_3168_, 1, v___x_3166_);
return v___x_3168_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__2(void){
_start:
{
lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; 
v___x_3169_ = lean_obj_once(&l_Lean_Meta_Rewrites_rewriteCandidates___closed__1, &l_Lean_Meta_Rewrites_rewriteCandidates___closed__1_once, _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__1);
v___x_3170_ = l_Lean_NameSet_empty;
v___x_3171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3171_, 0, v___x_3170_);
lean_ctor_set(v___x_3171_, 1, v___x_3169_);
return v___x_3171_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__3(void){
_start:
{
lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; 
v___x_3172_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_));
v___x_3173_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__4));
v___x_3174_ = l_Lean_Name_append(v___x_3173_, v___x_3172_);
return v___x_3174_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__5(void){
_start:
{
lean_object* v___x_3176_; lean_object* v___x_3177_; 
v___x_3176_ = ((lean_object*)(l_Lean_Meta_Rewrites_rewriteCandidates___closed__4));
v___x_3177_ = l_Lean_stringToMessageData(v___x_3176_);
return v___x_3177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rewriteCandidates(lean_object* v_hyps_3178_, lean_object* v_moduleRef_3179_, lean_object* v_target_3180_, lean_object* v_forbidden_3181_, lean_object* v_a_3182_, lean_object* v_a_3183_, lean_object* v_a_3184_, lean_object* v_a_3185_){
_start:
{
lean_object* v___x_3187_; lean_object* v___x_3188_; 
v___x_3187_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_rwFindDecls___boxed), 7, 1);
lean_closure_set(v___x_3187_, 0, v_moduleRef_3179_);
v___x_3188_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v___x_3187_, v_target_3180_, v_a_3182_, v_a_3183_, v_a_3184_, v_a_3185_);
if (lean_obj_tag(v___x_3188_) == 0)
{
lean_object* v_a_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; size_t v_sz_3194_; size_t v___x_3195_; lean_object* v___x_3196_; 
v_a_3189_ = lean_ctor_get(v___x_3188_, 0);
lean_inc(v_a_3189_);
lean_dec_ref_known(v___x_3188_, 1);
v___x_3190_ = lean_unsigned_to_nat(0u);
v___x_3191_ = lean_array_get_size(v_a_3189_);
v___x_3192_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0(v_a_3189_, v___x_3190_, v___x_3191_);
v___x_3193_ = lean_obj_once(&l_Lean_Meta_Rewrites_rewriteCandidates___closed__2, &l_Lean_Meta_Rewrites_rewriteCandidates___closed__2_once, _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__2);
v_sz_3194_ = lean_array_size(v___x_3192_);
v___x_3195_ = ((size_t)0ULL);
v___x_3196_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg(v_forbidden_3181_, v___x_3192_, v_sz_3194_, v___x_3195_, v___x_3193_);
lean_dec_ref(v___x_3192_);
if (lean_obj_tag(v___x_3196_) == 0)
{
lean_object* v_a_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3241_; 
v_a_3197_ = lean_ctor_get(v___x_3196_, 0);
v_isSharedCheck_3241_ = !lean_is_exclusive(v___x_3196_);
if (v_isSharedCheck_3241_ == 0)
{
v___x_3199_ = v___x_3196_;
v_isShared_3200_ = v_isSharedCheck_3241_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_a_3197_);
lean_dec(v___x_3196_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3241_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
lean_object* v_snd_3201_; lean_object* v_snd_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3239_; 
v_snd_3201_ = lean_ctor_get(v_a_3197_, 1);
lean_inc(v_snd_3201_);
lean_dec(v_a_3197_);
v_snd_3202_ = lean_ctor_get(v_snd_3201_, 1);
v_isSharedCheck_3239_ = !lean_is_exclusive(v_snd_3201_);
if (v_isSharedCheck_3239_ == 0)
{
lean_object* v_unused_3240_; 
v_unused_3240_ = lean_ctor_get(v_snd_3201_, 0);
lean_dec(v_unused_3240_);
v___x_3204_ = v_snd_3201_;
v_isShared_3205_ = v_isSharedCheck_3239_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_snd_3202_);
lean_dec(v_snd_3201_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3239_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v_toCold_3215_; lean_object* v_options_3216_; uint8_t v_hasTrace_3217_; 
v_toCold_3215_ = lean_ctor_get(v_a_3184_, 0);
v_options_3216_ = lean_ctor_get(v_toCold_3215_, 2);
v_hasTrace_3217_ = lean_ctor_get_uint8(v_options_3216_, sizeof(void*)*1);
if (v_hasTrace_3217_ == 0)
{
lean_del_object(v___x_3204_);
goto v___jp_3206_;
}
else
{
lean_object* v_inheritedTraceOptions_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; uint8_t v___x_3221_; 
v_inheritedTraceOptions_3218_ = lean_ctor_get(v_toCold_3215_, 11);
v___x_3219_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_));
v___x_3220_ = lean_obj_once(&l_Lean_Meta_Rewrites_rewriteCandidates___closed__3, &l_Lean_Meta_Rewrites_rewriteCandidates___closed__3_once, _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__3);
v___x_3221_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3218_, v_options_3216_, v___x_3220_);
if (v___x_3221_ == 0)
{
lean_del_object(v___x_3204_);
goto v___jp_3206_;
}
else
{
lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3228_; 
v___x_3222_ = lean_obj_once(&l_Lean_Meta_Rewrites_rewriteCandidates___closed__5, &l_Lean_Meta_Rewrites_rewriteCandidates___closed__5_once, _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__5);
lean_inc(v_snd_3202_);
v___x_3223_ = lean_array_to_list(v_snd_3202_);
v___x_3224_ = lean_box(0);
v___x_3225_ = l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4(v___x_3223_, v___x_3224_);
v___x_3226_ = l_Lean_MessageData_ofList(v___x_3225_);
if (v_isShared_3205_ == 0)
{
lean_ctor_set_tag(v___x_3204_, 7);
lean_ctor_set(v___x_3204_, 1, v___x_3226_);
lean_ctor_set(v___x_3204_, 0, v___x_3222_);
v___x_3228_ = v___x_3204_;
goto v_reusejp_3227_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v___x_3222_);
lean_ctor_set(v_reuseFailAlloc_3238_, 1, v___x_3226_);
v___x_3228_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3227_;
}
v_reusejp_3227_:
{
lean_object* v___x_3229_; 
v___x_3229_ = l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2(v___x_3219_, v___x_3228_, v_a_3182_, v_a_3183_, v_a_3184_, v_a_3185_);
if (lean_obj_tag(v___x_3229_) == 0)
{
lean_dec_ref_known(v___x_3229_, 1);
goto v___jp_3206_;
}
else
{
lean_object* v_a_3230_; lean_object* v___x_3232_; uint8_t v_isShared_3233_; uint8_t v_isSharedCheck_3237_; 
lean_dec(v_snd_3202_);
lean_del_object(v___x_3199_);
lean_dec_ref(v_hyps_3178_);
v_a_3230_ = lean_ctor_get(v___x_3229_, 0);
v_isSharedCheck_3237_ = !lean_is_exclusive(v___x_3229_);
if (v_isSharedCheck_3237_ == 0)
{
v___x_3232_ = v___x_3229_;
v_isShared_3233_ = v_isSharedCheck_3237_;
goto v_resetjp_3231_;
}
else
{
lean_inc(v_a_3230_);
lean_dec(v___x_3229_);
v___x_3232_ = lean_box(0);
v_isShared_3233_ = v_isSharedCheck_3237_;
goto v_resetjp_3231_;
}
v_resetjp_3231_:
{
lean_object* v___x_3235_; 
if (v_isShared_3233_ == 0)
{
v___x_3235_ = v___x_3232_;
goto v_reusejp_3234_;
}
else
{
lean_object* v_reuseFailAlloc_3236_; 
v_reuseFailAlloc_3236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3236_, 0, v_a_3230_);
v___x_3235_ = v_reuseFailAlloc_3236_;
goto v_reusejp_3234_;
}
v_reusejp_3234_:
{
return v___x_3235_;
}
}
}
}
}
}
v___jp_3206_:
{
size_t v_sz_3207_; lean_object* v___x_3208_; size_t v_sz_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3213_; 
v_sz_3207_ = lean_array_size(v_hyps_3178_);
v___x_3208_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__2(v_sz_3207_, v___x_3195_, v_hyps_3178_);
v_sz_3209_ = lean_array_size(v_snd_3202_);
v___x_3210_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__3(v_sz_3209_, v___x_3195_, v_snd_3202_);
v___x_3211_ = l_Array_append___redArg(v___x_3208_, v___x_3210_);
lean_dec_ref(v___x_3210_);
if (v_isShared_3200_ == 0)
{
lean_ctor_set(v___x_3199_, 0, v___x_3211_);
v___x_3213_ = v___x_3199_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v___x_3211_);
v___x_3213_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
return v___x_3213_;
}
}
}
}
}
else
{
lean_object* v_a_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3249_; 
lean_dec_ref(v_hyps_3178_);
v_a_3242_ = lean_ctor_get(v___x_3196_, 0);
v_isSharedCheck_3249_ = !lean_is_exclusive(v___x_3196_);
if (v_isSharedCheck_3249_ == 0)
{
v___x_3244_ = v___x_3196_;
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_a_3242_);
lean_dec(v___x_3196_);
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
lean_dec_ref(v_hyps_3178_);
v_a_3250_ = lean_ctor_get(v___x_3188_, 0);
v_isSharedCheck_3257_ = !lean_is_exclusive(v___x_3188_);
if (v_isSharedCheck_3257_ == 0)
{
v___x_3252_ = v___x_3188_;
v_isShared_3253_ = v_isSharedCheck_3257_;
goto v_resetjp_3251_;
}
else
{
lean_inc(v_a_3250_);
lean_dec(v___x_3188_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rewriteCandidates___boxed(lean_object* v_hyps_3258_, lean_object* v_moduleRef_3259_, lean_object* v_target_3260_, lean_object* v_forbidden_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_, lean_object* v_a_3265_, lean_object* v_a_3266_){
_start:
{
lean_object* v_res_3267_; 
v_res_3267_ = l_Lean_Meta_Rewrites_rewriteCandidates(v_hyps_3258_, v_moduleRef_3259_, v_target_3260_, v_forbidden_3261_, v_a_3262_, v_a_3263_, v_a_3264_, v_a_3265_);
lean_dec(v_a_3265_);
lean_dec_ref(v_a_3264_);
lean_dec(v_a_3263_);
lean_dec_ref(v_a_3262_);
lean_dec(v_forbidden_3261_);
return v_res_3267_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1(lean_object* v_forbidden_3268_, lean_object* v_as_3269_, size_t v_sz_3270_, size_t v_i_3271_, lean_object* v_b_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_){
_start:
{
lean_object* v___x_3278_; 
v___x_3278_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg(v_forbidden_3268_, v_as_3269_, v_sz_3270_, v_i_3271_, v_b_3272_);
return v___x_3278_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___boxed(lean_object* v_forbidden_3279_, lean_object* v_as_3280_, lean_object* v_sz_3281_, lean_object* v_i_3282_, lean_object* v_b_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_){
_start:
{
size_t v_sz_boxed_3289_; size_t v_i_boxed_3290_; lean_object* v_res_3291_; 
v_sz_boxed_3289_ = lean_unbox_usize(v_sz_3281_);
lean_dec(v_sz_3281_);
v_i_boxed_3290_ = lean_unbox_usize(v_i_3282_);
lean_dec(v_i_3282_);
v_res_3291_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1(v_forbidden_3279_, v_as_3280_, v_sz_boxed_3289_, v_i_boxed_3290_, v_b_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_);
lean_dec(v___y_3287_);
lean_dec_ref(v___y_3286_);
lean_dec(v___y_3285_);
lean_dec_ref(v___y_3284_);
lean_dec_ref(v_as_3280_);
lean_dec(v_forbidden_3279_);
return v_res_3291_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0(lean_object* v_xs_3292_, lean_object* v_j_3293_, lean_object* v_h_3294_){
_start:
{
lean_object* v___x_3295_; 
v___x_3295_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0___redArg(v_xs_3292_, v_j_3293_);
return v___x_3295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_newGoal(lean_object* v_r_3296_){
_start:
{
uint8_t v_rfl_x3f_3297_; 
v_rfl_x3f_3297_ = lean_ctor_get_uint8(v_r_3296_, sizeof(void*)*4 + 1);
if (v_rfl_x3f_3297_ == 0)
{
lean_object* v_result_3298_; lean_object* v_eNew_3299_; lean_object* v___x_3300_; 
v_result_3298_ = lean_ctor_get(v_r_3296_, 2);
v_eNew_3299_ = lean_ctor_get(v_result_3298_, 0);
lean_inc_ref(v_eNew_3299_);
v___x_3300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3300_, 0, v_eNew_3299_);
return v___x_3300_;
}
else
{
lean_object* v___x_3301_; 
v___x_3301_ = lean_box(0);
return v___x_3301_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_newGoal___boxed(lean_object* v_r_3302_){
_start:
{
lean_object* v_res_3303_; 
v_res_3303_ = l_Lean_Meta_Rewrites_RewriteResult_newGoal(v_r_3302_);
lean_dec_ref(v_r_3302_);
return v_res_3303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0(lean_object* v_x_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_){
_start:
{
lean_object* v___x_3314_; 
lean_inc(v___y_3308_);
lean_inc_ref(v___y_3307_);
lean_inc(v___y_3306_);
lean_inc_ref(v___y_3305_);
v___x_3314_ = lean_apply_9(v_x_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_, lean_box(0));
return v___x_3314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0___boxed(lean_object* v_x_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_){
_start:
{
lean_object* v_res_3325_; 
v_res_3325_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0(v_x_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_);
lean_dec(v___y_3319_);
lean_dec_ref(v___y_3318_);
lean_dec(v___y_3317_);
lean_dec_ref(v___y_3316_);
return v_res_3325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg(lean_object* v_mctx_3326_, lean_object* v_x_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_){
_start:
{
lean_object* v___f_3337_; lean_object* v___x_3338_; 
lean_inc(v___y_3331_);
lean_inc_ref(v___y_3330_);
lean_inc(v___y_3329_);
lean_inc_ref(v___y_3328_);
v___f_3337_ = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3337_, 0, v_x_3327_);
lean_closure_set(v___f_3337_, 1, v___y_3328_);
lean_closure_set(v___f_3337_, 2, v___y_3329_);
lean_closure_set(v___f_3337_, 3, v___y_3330_);
lean_closure_set(v___f_3337_, 4, v___y_3331_);
v___x_3338_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp(lean_box(0), v_mctx_3326_, v___f_3337_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_);
if (lean_obj_tag(v___x_3338_) == 0)
{
return v___x_3338_;
}
else
{
lean_object* v_a_3339_; lean_object* v___x_3341_; uint8_t v_isShared_3342_; uint8_t v_isSharedCheck_3346_; 
v_a_3339_ = lean_ctor_get(v___x_3338_, 0);
v_isSharedCheck_3346_ = !lean_is_exclusive(v___x_3338_);
if (v_isSharedCheck_3346_ == 0)
{
v___x_3341_ = v___x_3338_;
v_isShared_3342_ = v_isSharedCheck_3346_;
goto v_resetjp_3340_;
}
else
{
lean_inc(v_a_3339_);
lean_dec(v___x_3338_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___boxed(lean_object* v_mctx_3347_, lean_object* v_x_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_){
_start:
{
lean_object* v_res_3358_; 
v_res_3358_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg(v_mctx_3347_, v_x_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_);
lean_dec(v___y_3356_);
lean_dec_ref(v___y_3355_);
lean_dec(v___y_3354_);
lean_dec_ref(v___y_3353_);
lean_dec(v___y_3352_);
lean_dec_ref(v___y_3351_);
lean_dec(v___y_3350_);
lean_dec_ref(v___y_3349_);
return v_res_3358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0(lean_object* v_00_u03b1_3359_, lean_object* v_mctx_3360_, lean_object* v_x_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_){
_start:
{
lean_object* v___x_3371_; 
v___x_3371_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg(v_mctx_3360_, v_x_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_);
return v___x_3371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___boxed(lean_object* v_00_u03b1_3372_, lean_object* v_mctx_3373_, lean_object* v_x_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_){
_start:
{
lean_object* v_res_3384_; 
v_res_3384_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0(v_00_u03b1_3372_, v_mctx_3373_, v_x_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_);
lean_dec(v___y_3382_);
lean_dec_ref(v___y_3381_);
lean_dec(v___y_3380_);
lean_dec_ref(v___y_3379_);
lean_dec(v___y_3378_);
lean_dec_ref(v___y_3377_);
lean_dec(v___y_3376_);
lean_dec_ref(v___y_3375_);
return v_res_3384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0(lean_object* v_expr_3385_, uint8_t v_symm_3386_, lean_object* v_r_3387_, lean_object* v_ref_3388_, lean_object* v_checkState_x3f_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_){
_start:
{
lean_object* v_ref_3399_; lean_object* v___x_3400_; 
v_ref_3399_ = lean_ctor_get(v___y_3396_, 2);
v___x_3400_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_3391_, v___y_3393_, v___y_3395_, v___y_3397_);
if (lean_obj_tag(v___x_3400_) == 0)
{
lean_object* v_a_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___y_3411_; 
v_a_3401_ = lean_ctor_get(v___x_3400_, 0);
lean_inc(v_a_3401_);
lean_dec_ref_known(v___x_3400_, 1);
v___x_3402_ = lean_box(v_symm_3386_);
v___x_3403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3403_, 0, v_expr_3385_);
lean_ctor_set(v___x_3403_, 1, v___x_3402_);
v___x_3404_ = lean_box(0);
v___x_3405_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3405_, 0, v___x_3403_);
lean_ctor_set(v___x_3405_, 1, v___x_3404_);
v___x_3406_ = l_Lean_Meta_Rewrites_RewriteResult_newGoal(v_r_3387_);
v___x_3407_ = l_Lean_Option_toLOption___redArg(v___x_3406_);
v___x_3408_ = lean_box(0);
lean_inc(v_ref_3399_);
v___x_3409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3409_, 0, v_ref_3399_);
if (lean_obj_tag(v_checkState_x3f_3389_) == 0)
{
v___y_3411_ = v_a_3401_;
goto v___jp_3410_;
}
else
{
lean_object* v_val_3414_; 
lean_dec(v_a_3401_);
v_val_3414_ = lean_ctor_get(v_checkState_x3f_3389_, 0);
lean_inc(v_val_3414_);
lean_dec_ref_known(v_checkState_x3f_3389_, 1);
v___y_3411_ = v_val_3414_;
goto v___jp_3410_;
}
v___jp_3410_:
{
lean_object* v___x_3412_; lean_object* v___x_3413_; 
v___x_3412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3412_, 0, v___y_3411_);
v___x_3413_ = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion(v_ref_3388_, v___x_3405_, v___x_3407_, v___x_3408_, v___x_3409_, v___x_3412_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_);
return v___x_3413_;
}
}
else
{
lean_object* v_a_3415_; lean_object* v___x_3417_; uint8_t v_isShared_3418_; uint8_t v_isSharedCheck_3422_; 
lean_dec(v_checkState_x3f_3389_);
lean_dec(v_ref_3388_);
lean_dec_ref(v_expr_3385_);
v_a_3415_ = lean_ctor_get(v___x_3400_, 0);
v_isSharedCheck_3422_ = !lean_is_exclusive(v___x_3400_);
if (v_isSharedCheck_3422_ == 0)
{
v___x_3417_ = v___x_3400_;
v_isShared_3418_ = v_isSharedCheck_3422_;
goto v_resetjp_3416_;
}
else
{
lean_inc(v_a_3415_);
lean_dec(v___x_3400_);
v___x_3417_ = lean_box(0);
v_isShared_3418_ = v_isSharedCheck_3422_;
goto v_resetjp_3416_;
}
v_resetjp_3416_:
{
lean_object* v___x_3420_; 
if (v_isShared_3418_ == 0)
{
v___x_3420_ = v___x_3417_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v_a_3415_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0___boxed(lean_object* v_expr_3423_, lean_object* v_symm_3424_, lean_object* v_r_3425_, lean_object* v_ref_3426_, lean_object* v_checkState_x3f_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_){
_start:
{
uint8_t v_symm_boxed_3437_; lean_object* v_res_3438_; 
v_symm_boxed_3437_ = lean_unbox(v_symm_3424_);
v_res_3438_ = l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0(v_expr_3423_, v_symm_boxed_3437_, v_r_3425_, v_ref_3426_, v_checkState_x3f_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_);
lean_dec(v___y_3435_);
lean_dec_ref(v___y_3434_);
lean_dec(v___y_3433_);
lean_dec_ref(v___y_3432_);
lean_dec(v___y_3431_);
lean_dec_ref(v___y_3430_);
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
lean_dec_ref(v_r_3425_);
return v_res_3438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion(lean_object* v_ref_3439_, lean_object* v_r_3440_, lean_object* v_checkState_x3f_3441_, lean_object* v_a_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_){
_start:
{
lean_object* v_expr_3451_; uint8_t v_symm_3452_; lean_object* v_mctx_3453_; lean_object* v___x_3454_; lean_object* v___f_3455_; lean_object* v___x_3456_; 
v_expr_3451_ = lean_ctor_get(v_r_3440_, 0);
lean_inc_ref(v_expr_3451_);
v_symm_3452_ = lean_ctor_get_uint8(v_r_3440_, sizeof(void*)*4);
v_mctx_3453_ = lean_ctor_get(v_r_3440_, 3);
lean_inc_ref(v_mctx_3453_);
v___x_3454_ = lean_box(v_symm_3452_);
v___f_3455_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0___boxed), 14, 5);
lean_closure_set(v___f_3455_, 0, v_expr_3451_);
lean_closure_set(v___f_3455_, 1, v___x_3454_);
lean_closure_set(v___f_3455_, 2, v_r_3440_);
lean_closure_set(v___f_3455_, 3, v_ref_3439_);
lean_closure_set(v___f_3455_, 4, v_checkState_x3f_3441_);
v___x_3456_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg(v_mctx_3453_, v___f_3455_, v_a_3442_, v_a_3443_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
return v___x_3456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___boxed(lean_object* v_ref_3457_, lean_object* v_r_3458_, lean_object* v_checkState_x3f_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_, lean_object* v_a_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_, lean_object* v_a_3465_, lean_object* v_a_3466_, lean_object* v_a_3467_, lean_object* v_a_3468_){
_start:
{
lean_object* v_res_3469_; 
v_res_3469_ = l_Lean_Meta_Rewrites_RewriteResult_addSuggestion(v_ref_3457_, v_r_3458_, v_checkState_x3f_3459_, v_a_3460_, v_a_3461_, v_a_3462_, v_a_3463_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_);
lean_dec(v_a_3467_);
lean_dec_ref(v_a_3466_);
lean_dec(v_a_3465_);
lean_dec_ref(v_a_3464_);
lean_dec(v_a_3463_);
lean_dec_ref(v_a_3462_);
lean_dec(v_a_3461_);
lean_dec_ref(v_a_3460_);
return v_res_3469_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3___redArg(lean_object* v_a_3470_, lean_object* v_b_3471_, lean_object* v_x_3472_){
_start:
{
if (lean_obj_tag(v_x_3472_) == 0)
{
lean_dec(v_b_3471_);
lean_dec_ref(v_a_3470_);
return v_x_3472_;
}
else
{
lean_object* v_key_3473_; lean_object* v_value_3474_; lean_object* v_tail_3475_; lean_object* v___x_3477_; uint8_t v_isShared_3478_; uint8_t v_isSharedCheck_3487_; 
v_key_3473_ = lean_ctor_get(v_x_3472_, 0);
v_value_3474_ = lean_ctor_get(v_x_3472_, 1);
v_tail_3475_ = lean_ctor_get(v_x_3472_, 2);
v_isSharedCheck_3487_ = !lean_is_exclusive(v_x_3472_);
if (v_isSharedCheck_3487_ == 0)
{
v___x_3477_ = v_x_3472_;
v_isShared_3478_ = v_isSharedCheck_3487_;
goto v_resetjp_3476_;
}
else
{
lean_inc(v_tail_3475_);
lean_inc(v_value_3474_);
lean_inc(v_key_3473_);
lean_dec(v_x_3472_);
v___x_3477_ = lean_box(0);
v_isShared_3478_ = v_isSharedCheck_3487_;
goto v_resetjp_3476_;
}
v_resetjp_3476_:
{
uint8_t v___x_3479_; 
v___x_3479_ = lean_string_dec_eq(v_key_3473_, v_a_3470_);
if (v___x_3479_ == 0)
{
lean_object* v___x_3480_; lean_object* v___x_3482_; 
v___x_3480_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3___redArg(v_a_3470_, v_b_3471_, v_tail_3475_);
if (v_isShared_3478_ == 0)
{
lean_ctor_set(v___x_3477_, 2, v___x_3480_);
v___x_3482_ = v___x_3477_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v_key_3473_);
lean_ctor_set(v_reuseFailAlloc_3483_, 1, v_value_3474_);
lean_ctor_set(v_reuseFailAlloc_3483_, 2, v___x_3480_);
v___x_3482_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
return v___x_3482_;
}
}
else
{
lean_object* v___x_3485_; 
lean_dec(v_value_3474_);
lean_dec(v_key_3473_);
if (v_isShared_3478_ == 0)
{
lean_ctor_set(v___x_3477_, 1, v_b_3471_);
lean_ctor_set(v___x_3477_, 0, v_a_3470_);
v___x_3485_ = v___x_3477_;
goto v_reusejp_3484_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v_a_3470_);
lean_ctor_set(v_reuseFailAlloc_3486_, 1, v_b_3471_);
lean_ctor_set(v_reuseFailAlloc_3486_, 2, v_tail_3475_);
v___x_3485_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3484_;
}
v_reusejp_3484_:
{
return v___x_3485_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_x_3488_, lean_object* v_x_3489_){
_start:
{
if (lean_obj_tag(v_x_3489_) == 0)
{
return v_x_3488_;
}
else
{
lean_object* v_key_3490_; lean_object* v_value_3491_; lean_object* v_tail_3492_; lean_object* v___x_3494_; uint8_t v_isShared_3495_; uint8_t v_isSharedCheck_3515_; 
v_key_3490_ = lean_ctor_get(v_x_3489_, 0);
v_value_3491_ = lean_ctor_get(v_x_3489_, 1);
v_tail_3492_ = lean_ctor_get(v_x_3489_, 2);
v_isSharedCheck_3515_ = !lean_is_exclusive(v_x_3489_);
if (v_isSharedCheck_3515_ == 0)
{
v___x_3494_ = v_x_3489_;
v_isShared_3495_ = v_isSharedCheck_3515_;
goto v_resetjp_3493_;
}
else
{
lean_inc(v_tail_3492_);
lean_inc(v_value_3491_);
lean_inc(v_key_3490_);
lean_dec(v_x_3489_);
v___x_3494_ = lean_box(0);
v_isShared_3495_ = v_isSharedCheck_3515_;
goto v_resetjp_3493_;
}
v_resetjp_3493_:
{
lean_object* v___x_3496_; uint64_t v___x_3497_; uint64_t v___x_3498_; uint64_t v___x_3499_; uint64_t v_fold_3500_; uint64_t v___x_3501_; uint64_t v___x_3502_; uint64_t v___x_3503_; size_t v___x_3504_; size_t v___x_3505_; size_t v___x_3506_; size_t v___x_3507_; size_t v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3511_; 
v___x_3496_ = lean_array_get_size(v_x_3488_);
v___x_3497_ = lean_string_hash(v_key_3490_);
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
v___x_3509_ = lean_array_uget_borrowed(v_x_3488_, v___x_3508_);
lean_inc(v___x_3509_);
if (v_isShared_3495_ == 0)
{
lean_ctor_set(v___x_3494_, 2, v___x_3509_);
v___x_3511_ = v___x_3494_;
goto v_reusejp_3510_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v_key_3490_);
lean_ctor_set(v_reuseFailAlloc_3514_, 1, v_value_3491_);
lean_ctor_set(v_reuseFailAlloc_3514_, 2, v___x_3509_);
v___x_3511_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3510_;
}
v_reusejp_3510_:
{
lean_object* v___x_3512_; 
v___x_3512_ = lean_array_uset(v_x_3488_, v___x_3508_, v___x_3511_);
v_x_3488_ = v___x_3512_;
v_x_3489_ = v_tail_3492_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3___redArg(lean_object* v_i_3516_, lean_object* v_source_3517_, lean_object* v_target_3518_){
_start:
{
lean_object* v___x_3519_; uint8_t v___x_3520_; 
v___x_3519_ = lean_array_get_size(v_source_3517_);
v___x_3520_ = lean_nat_dec_lt(v_i_3516_, v___x_3519_);
if (v___x_3520_ == 0)
{
lean_dec_ref(v_source_3517_);
lean_dec(v_i_3516_);
return v_target_3518_;
}
else
{
lean_object* v_es_3521_; lean_object* v___x_3522_; lean_object* v_source_3523_; lean_object* v_target_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; 
v_es_3521_ = lean_array_fget(v_source_3517_, v_i_3516_);
v___x_3522_ = lean_box(0);
v_source_3523_ = lean_array_fset(v_source_3517_, v_i_3516_, v___x_3522_);
v_target_3524_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3_spec__5___redArg(v_target_3518_, v_es_3521_);
v___x_3525_ = lean_unsigned_to_nat(1u);
v___x_3526_ = lean_nat_add(v_i_3516_, v___x_3525_);
lean_dec(v_i_3516_);
v_i_3516_ = v___x_3526_;
v_source_3517_ = v_source_3523_;
v_target_3518_ = v_target_3524_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2___redArg(lean_object* v_data_3528_){
_start:
{
lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v_nbuckets_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; 
v___x_3529_ = lean_array_get_size(v_data_3528_);
v___x_3530_ = lean_unsigned_to_nat(2u);
v_nbuckets_3531_ = lean_nat_mul(v___x_3529_, v___x_3530_);
v___x_3532_ = lean_unsigned_to_nat(0u);
v___x_3533_ = lean_box(0);
v___x_3534_ = lean_mk_array(v_nbuckets_3531_, v___x_3533_);
v___x_3535_ = lean_array_propagate_mark(v_data_3528_, v___x_3534_);
v___x_3536_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3___redArg(v___x_3532_, v_data_3528_, v___x_3535_);
return v___x_3536_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(lean_object* v_a_3537_, lean_object* v_x_3538_){
_start:
{
if (lean_obj_tag(v_x_3538_) == 0)
{
uint8_t v___x_3539_; 
v___x_3539_ = 0;
return v___x_3539_;
}
else
{
lean_object* v_key_3540_; lean_object* v_tail_3541_; uint8_t v___x_3542_; 
v_key_3540_ = lean_ctor_get(v_x_3538_, 0);
v_tail_3541_ = lean_ctor_get(v_x_3538_, 2);
v___x_3542_ = lean_string_dec_eq(v_key_3540_, v_a_3537_);
if (v___x_3542_ == 0)
{
v_x_3538_ = v_tail_3541_;
goto _start;
}
else
{
return v___x_3542_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg___boxed(lean_object* v_a_3544_, lean_object* v_x_3545_){
_start:
{
uint8_t v_res_3546_; lean_object* v_r_3547_; 
v_res_3546_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(v_a_3544_, v_x_3545_);
lean_dec(v_x_3545_);
lean_dec_ref(v_a_3544_);
v_r_3547_ = lean_box(v_res_3546_);
return v_r_3547_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1___redArg(lean_object* v_m_3548_, lean_object* v_a_3549_, lean_object* v_b_3550_){
_start:
{
lean_object* v_size_3551_; lean_object* v_buckets_3552_; lean_object* v___x_3554_; uint8_t v_isShared_3555_; uint8_t v_isSharedCheck_3595_; 
v_size_3551_ = lean_ctor_get(v_m_3548_, 0);
v_buckets_3552_ = lean_ctor_get(v_m_3548_, 1);
v_isSharedCheck_3595_ = !lean_is_exclusive(v_m_3548_);
if (v_isSharedCheck_3595_ == 0)
{
v___x_3554_ = v_m_3548_;
v_isShared_3555_ = v_isSharedCheck_3595_;
goto v_resetjp_3553_;
}
else
{
lean_inc(v_buckets_3552_);
lean_inc(v_size_3551_);
lean_dec(v_m_3548_);
v___x_3554_ = lean_box(0);
v_isShared_3555_ = v_isSharedCheck_3595_;
goto v_resetjp_3553_;
}
v_resetjp_3553_:
{
lean_object* v___x_3556_; uint64_t v___x_3557_; uint64_t v___x_3558_; uint64_t v___x_3559_; uint64_t v_fold_3560_; uint64_t v___x_3561_; uint64_t v___x_3562_; uint64_t v___x_3563_; size_t v___x_3564_; size_t v___x_3565_; size_t v___x_3566_; size_t v___x_3567_; size_t v___x_3568_; lean_object* v_bkt_3569_; uint8_t v___x_3570_; 
v___x_3556_ = lean_array_get_size(v_buckets_3552_);
v___x_3557_ = lean_string_hash(v_a_3549_);
v___x_3558_ = 32ULL;
v___x_3559_ = lean_uint64_shift_right(v___x_3557_, v___x_3558_);
v_fold_3560_ = lean_uint64_xor(v___x_3557_, v___x_3559_);
v___x_3561_ = 16ULL;
v___x_3562_ = lean_uint64_shift_right(v_fold_3560_, v___x_3561_);
v___x_3563_ = lean_uint64_xor(v_fold_3560_, v___x_3562_);
v___x_3564_ = lean_uint64_to_usize(v___x_3563_);
v___x_3565_ = lean_usize_of_nat(v___x_3556_);
v___x_3566_ = ((size_t)1ULL);
v___x_3567_ = lean_usize_sub(v___x_3565_, v___x_3566_);
v___x_3568_ = lean_usize_land(v___x_3564_, v___x_3567_);
v_bkt_3569_ = lean_array_uget_borrowed(v_buckets_3552_, v___x_3568_);
v___x_3570_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(v_a_3549_, v_bkt_3569_);
if (v___x_3570_ == 0)
{
lean_object* v___x_3571_; lean_object* v_size_x27_3572_; lean_object* v___x_3573_; lean_object* v_buckets_x27_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; uint8_t v___x_3580_; 
v___x_3571_ = lean_unsigned_to_nat(1u);
v_size_x27_3572_ = lean_nat_add(v_size_3551_, v___x_3571_);
lean_dec(v_size_3551_);
lean_inc(v_bkt_3569_);
v___x_3573_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3573_, 0, v_a_3549_);
lean_ctor_set(v___x_3573_, 1, v_b_3550_);
lean_ctor_set(v___x_3573_, 2, v_bkt_3569_);
v_buckets_x27_3574_ = lean_array_uset(v_buckets_3552_, v___x_3568_, v___x_3573_);
v___x_3575_ = lean_unsigned_to_nat(4u);
v___x_3576_ = lean_nat_mul(v_size_x27_3572_, v___x_3575_);
v___x_3577_ = lean_unsigned_to_nat(3u);
v___x_3578_ = lean_nat_div(v___x_3576_, v___x_3577_);
lean_dec(v___x_3576_);
v___x_3579_ = lean_array_get_size(v_buckets_x27_3574_);
v___x_3580_ = lean_nat_dec_le(v___x_3578_, v___x_3579_);
lean_dec(v___x_3578_);
if (v___x_3580_ == 0)
{
lean_object* v_val_3581_; lean_object* v___x_3583_; 
v_val_3581_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2___redArg(v_buckets_x27_3574_);
if (v_isShared_3555_ == 0)
{
lean_ctor_set(v___x_3554_, 1, v_val_3581_);
lean_ctor_set(v___x_3554_, 0, v_size_x27_3572_);
v___x_3583_ = v___x_3554_;
goto v_reusejp_3582_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v_size_x27_3572_);
lean_ctor_set(v_reuseFailAlloc_3584_, 1, v_val_3581_);
v___x_3583_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3582_;
}
v_reusejp_3582_:
{
return v___x_3583_;
}
}
else
{
lean_object* v___x_3586_; 
if (v_isShared_3555_ == 0)
{
lean_ctor_set(v___x_3554_, 1, v_buckets_x27_3574_);
lean_ctor_set(v___x_3554_, 0, v_size_x27_3572_);
v___x_3586_ = v___x_3554_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3587_; 
v_reuseFailAlloc_3587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3587_, 0, v_size_x27_3572_);
lean_ctor_set(v_reuseFailAlloc_3587_, 1, v_buckets_x27_3574_);
v___x_3586_ = v_reuseFailAlloc_3587_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
return v___x_3586_;
}
}
}
else
{
lean_object* v___x_3588_; lean_object* v_buckets_x27_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3593_; 
lean_inc(v_bkt_3569_);
v___x_3588_ = lean_box(0);
v_buckets_x27_3589_ = lean_array_uset(v_buckets_3552_, v___x_3568_, v___x_3588_);
v___x_3590_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3___redArg(v_a_3549_, v_b_3550_, v_bkt_3569_);
v___x_3591_ = lean_array_uset(v_buckets_x27_3589_, v___x_3568_, v___x_3590_);
if (v_isShared_3555_ == 0)
{
lean_ctor_set(v___x_3554_, 1, v___x_3591_);
v___x_3593_ = v___x_3554_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v_size_3551_);
lean_ctor_set(v_reuseFailAlloc_3594_, 1, v___x_3591_);
v___x_3593_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
return v___x_3593_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg(lean_object* v_m_3596_, lean_object* v_a_3597_){
_start:
{
lean_object* v_buckets_3598_; lean_object* v___x_3599_; uint64_t v___x_3600_; uint64_t v___x_3601_; uint64_t v___x_3602_; uint64_t v_fold_3603_; uint64_t v___x_3604_; uint64_t v___x_3605_; uint64_t v___x_3606_; size_t v___x_3607_; size_t v___x_3608_; size_t v___x_3609_; size_t v___x_3610_; size_t v___x_3611_; lean_object* v___x_3612_; uint8_t v___x_3613_; 
v_buckets_3598_ = lean_ctor_get(v_m_3596_, 1);
v___x_3599_ = lean_array_get_size(v_buckets_3598_);
v___x_3600_ = lean_string_hash(v_a_3597_);
v___x_3601_ = 32ULL;
v___x_3602_ = lean_uint64_shift_right(v___x_3600_, v___x_3601_);
v_fold_3603_ = lean_uint64_xor(v___x_3600_, v___x_3602_);
v___x_3604_ = 16ULL;
v___x_3605_ = lean_uint64_shift_right(v_fold_3603_, v___x_3604_);
v___x_3606_ = lean_uint64_xor(v_fold_3603_, v___x_3605_);
v___x_3607_ = lean_uint64_to_usize(v___x_3606_);
v___x_3608_ = lean_usize_of_nat(v___x_3599_);
v___x_3609_ = ((size_t)1ULL);
v___x_3610_ = lean_usize_sub(v___x_3608_, v___x_3609_);
v___x_3611_ = lean_usize_land(v___x_3607_, v___x_3610_);
v___x_3612_ = lean_array_uget_borrowed(v_buckets_3598_, v___x_3611_);
v___x_3613_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(v_a_3597_, v___x_3612_);
return v___x_3613_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg___boxed(lean_object* v_m_3614_, lean_object* v_a_3615_){
_start:
{
uint8_t v_res_3616_; lean_object* v_r_3617_; 
v_res_3616_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg(v_m_3614_, v_a_3615_);
lean_dec_ref(v_a_3615_);
lean_dec_ref(v_m_3614_);
v_r_3617_ = lean_box(v_res_3616_);
return v_r_3617_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg(lean_object* v_cfg_3618_, lean_object* v_as_x27_3619_, lean_object* v_b_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_){
_start:
{
if (lean_obj_tag(v_as_x27_3619_) == 0)
{
lean_object* v___x_3626_; 
lean_dec_ref(v_cfg_3618_);
v___x_3626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3626_, 0, v_b_3620_);
return v___x_3626_;
}
else
{
lean_object* v_head_3627_; lean_object* v_snd_3628_; lean_object* v_snd_3629_; lean_object* v___x_3631_; uint8_t v_isShared_3632_; uint8_t v_isSharedCheck_3786_; 
v_head_3627_ = lean_ctor_get(v_as_x27_3619_, 0);
v_snd_3628_ = lean_ctor_get(v_head_3627_, 1);
v_snd_3629_ = lean_ctor_get(v_b_3620_, 1);
v_isSharedCheck_3786_ = !lean_is_exclusive(v_b_3620_);
if (v_isSharedCheck_3786_ == 0)
{
lean_object* v_unused_3787_; 
v_unused_3787_ = lean_ctor_get(v_b_3620_, 0);
lean_dec(v_unused_3787_);
v___x_3631_ = v_b_3620_;
v_isShared_3632_ = v_isSharedCheck_3786_;
goto v_resetjp_3630_;
}
else
{
lean_inc(v_snd_3629_);
lean_dec(v_b_3620_);
v___x_3631_ = lean_box(0);
v_isShared_3632_ = v_isSharedCheck_3786_;
goto v_resetjp_3630_;
}
v_resetjp_3630_:
{
lean_object* v_tail_3633_; lean_object* v_fst_3634_; lean_object* v_fst_3635_; lean_object* v_snd_3636_; lean_object* v_fst_3637_; lean_object* v_snd_3638_; lean_object* v___x_3640_; uint8_t v_isShared_3641_; uint8_t v_isSharedCheck_3785_; 
v_tail_3633_ = lean_ctor_get(v_as_x27_3619_, 1);
v_fst_3634_ = lean_ctor_get(v_head_3627_, 0);
v_fst_3635_ = lean_ctor_get(v_snd_3628_, 0);
v_snd_3636_ = lean_ctor_get(v_snd_3628_, 1);
v_fst_3637_ = lean_ctor_get(v_snd_3629_, 0);
v_snd_3638_ = lean_ctor_get(v_snd_3629_, 1);
v_isSharedCheck_3785_ = !lean_is_exclusive(v_snd_3629_);
if (v_isSharedCheck_3785_ == 0)
{
v___x_3640_ = v_snd_3629_;
v_isShared_3641_ = v_isSharedCheck_3785_;
goto v_resetjp_3639_;
}
else
{
lean_inc(v_snd_3638_);
lean_inc(v_fst_3637_);
lean_dec(v_snd_3629_);
v___x_3640_ = lean_box(0);
v_isShared_3641_ = v_isSharedCheck_3785_;
goto v_resetjp_3639_;
}
v_resetjp_3639_:
{
lean_object* v___x_3642_; lean_object* v___x_3643_; 
v___x_3642_ = lean_box(0);
v___x_3643_ = l_Lean_getRemainingHeartbeats___redArg(v___y_3623_);
if (lean_obj_tag(v___x_3643_) == 0)
{
lean_object* v_a_3644_; lean_object* v___x_3646_; uint8_t v_isShared_3647_; uint8_t v_isSharedCheck_3776_; 
v_a_3644_ = lean_ctor_get(v___x_3643_, 0);
v_isSharedCheck_3776_ = !lean_is_exclusive(v___x_3643_);
if (v_isSharedCheck_3776_ == 0)
{
v___x_3646_ = v___x_3643_;
v_isShared_3647_ = v_isSharedCheck_3776_;
goto v_resetjp_3645_;
}
else
{
lean_inc(v_a_3644_);
lean_dec(v___x_3643_);
v___x_3646_ = lean_box(0);
v_isShared_3647_ = v_isSharedCheck_3776_;
goto v_resetjp_3645_;
}
v_resetjp_3645_:
{
uint8_t v_stopAtRfl_3648_; lean_object* v_max_3649_; lean_object* v_minHeartbeats_3650_; lean_object* v_goal_3651_; lean_object* v_target_3652_; uint8_t v_side_3653_; lean_object* v_mctx_3654_; uint8_t v___x_3655_; 
v_stopAtRfl_3648_ = lean_ctor_get_uint8(v_cfg_3618_, sizeof(void*)*5);
v_max_3649_ = lean_ctor_get(v_cfg_3618_, 0);
v_minHeartbeats_3650_ = lean_ctor_get(v_cfg_3618_, 1);
v_goal_3651_ = lean_ctor_get(v_cfg_3618_, 2);
v_target_3652_ = lean_ctor_get(v_cfg_3618_, 3);
v_side_3653_ = lean_ctor_get_uint8(v_cfg_3618_, sizeof(void*)*5 + 1);
v_mctx_3654_ = lean_ctor_get(v_cfg_3618_, 4);
v___x_3655_ = lean_nat_dec_lt(v_a_3644_, v_minHeartbeats_3650_);
lean_dec(v_a_3644_);
if (v___x_3655_ == 0)
{
lean_object* v___x_3656_; uint8_t v___x_3657_; 
v___x_3656_ = lean_array_get_size(v_snd_3638_);
v___x_3657_ = lean_nat_dec_le(v_max_3649_, v___x_3656_);
if (v___x_3657_ == 0)
{
lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; 
lean_del_object(v___x_3646_);
v___x_3658_ = lean_box(v_side_3653_);
lean_inc(v_snd_3636_);
lean_inc(v_fst_3635_);
lean_inc(v_fst_3634_);
lean_inc_ref(v_target_3652_);
lean_inc(v_goal_3651_);
lean_inc_ref_n(v_mctx_3654_, 2);
v___x_3659_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_rwLemma___boxed), 12, 7);
lean_closure_set(v___x_3659_, 0, v_mctx_3654_);
lean_closure_set(v___x_3659_, 1, v_goal_3651_);
lean_closure_set(v___x_3659_, 2, v_target_3652_);
lean_closure_set(v___x_3659_, 3, v___x_3658_);
lean_closure_set(v___x_3659_, 4, v_fst_3634_);
lean_closure_set(v___x_3659_, 5, v_fst_3635_);
lean_closure_set(v___x_3659_, 6, v_snd_3636_);
v___x_3660_ = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___boxed), 8, 3);
lean_closure_set(v___x_3660_, 0, lean_box(0));
lean_closure_set(v___x_3660_, 1, v_mctx_3654_);
lean_closure_set(v___x_3660_, 2, v___x_3659_);
v___x_3661_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v___x_3660_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_);
if (lean_obj_tag(v___x_3661_) == 0)
{
lean_object* v_a_3662_; 
v_a_3662_ = lean_ctor_get(v___x_3661_, 0);
lean_inc(v_a_3662_);
lean_dec_ref_known(v___x_3661_, 1);
if (lean_obj_tag(v_a_3662_) == 0)
{
lean_object* v___x_3664_; 
if (v_isShared_3641_ == 0)
{
v___x_3664_ = v___x_3640_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v_fst_3637_);
lean_ctor_set(v_reuseFailAlloc_3669_, 1, v_snd_3638_);
v___x_3664_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
lean_object* v___x_3666_; 
if (v_isShared_3632_ == 0)
{
lean_ctor_set(v___x_3631_, 1, v___x_3664_);
lean_ctor_set(v___x_3631_, 0, v___x_3642_);
v___x_3666_ = v___x_3631_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v___x_3642_);
lean_ctor_set(v_reuseFailAlloc_3668_, 1, v___x_3664_);
v___x_3666_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
v_as_x27_3619_ = v_tail_3633_;
v_b_3620_ = v___x_3666_;
goto _start;
}
}
}
else
{
lean_object* v_val_3670_; lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3747_; 
v_val_3670_ = lean_ctor_get(v_a_3662_, 0);
v_isSharedCheck_3747_ = !lean_is_exclusive(v_a_3662_);
if (v_isSharedCheck_3747_ == 0)
{
v___x_3672_ = v_a_3662_;
v_isShared_3673_ = v_isSharedCheck_3747_;
goto v_resetjp_3671_;
}
else
{
lean_inc(v_val_3670_);
lean_dec(v_a_3662_);
v___x_3672_ = lean_box(0);
v_isShared_3673_ = v_isSharedCheck_3747_;
goto v_resetjp_3671_;
}
v_resetjp_3671_:
{
lean_object* v_result_3674_; lean_object* v_mctx_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; 
v_result_3674_ = lean_ctor_get(v_val_3670_, 2);
v_mctx_3675_ = lean_ctor_get(v_val_3670_, 3);
lean_inc(v_val_3670_);
v___x_3676_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult___boxed), 6, 1);
lean_closure_set(v___x_3676_, 0, v_val_3670_);
lean_inc_ref(v_mctx_3675_);
v___x_3677_ = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___boxed), 8, 3);
lean_closure_set(v___x_3677_, 0, lean_box(0));
lean_closure_set(v___x_3677_, 1, v_mctx_3675_);
lean_closure_set(v___x_3677_, 2, v___x_3676_);
v___x_3678_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v___x_3677_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_);
if (lean_obj_tag(v___x_3678_) == 0)
{
lean_object* v_a_3679_; uint8_t v___x_3680_; 
v_a_3679_ = lean_ctor_get(v___x_3678_, 0);
lean_inc(v_a_3679_);
lean_dec_ref_known(v___x_3678_, 1);
v___x_3680_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg(v_fst_3637_, v_a_3679_);
if (v___x_3680_ == 0)
{
lean_object* v_eNew_3681_; lean_object* v___x_3682_; 
v_eNew_3681_ = lean_ctor_get(v_result_3674_, 0);
lean_inc_ref(v_eNew_3681_);
lean_inc_ref(v_mctx_3675_);
v___x_3682_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(v_mctx_3675_, v_eNew_3681_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_);
if (lean_obj_tag(v___x_3682_) == 0)
{
if (v_stopAtRfl_3648_ == 0)
{
lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3687_; 
lean_dec_ref_known(v___x_3682_, 1);
lean_del_object(v___x_3672_);
v___x_3683_ = lean_box(0);
v___x_3684_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1___redArg(v_fst_3637_, v_a_3679_, v___x_3683_);
v___x_3685_ = lean_array_push(v_snd_3638_, v_val_3670_);
if (v_isShared_3641_ == 0)
{
lean_ctor_set(v___x_3640_, 1, v___x_3685_);
lean_ctor_set(v___x_3640_, 0, v___x_3684_);
v___x_3687_ = v___x_3640_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v___x_3684_);
lean_ctor_set(v_reuseFailAlloc_3692_, 1, v___x_3685_);
v___x_3687_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
lean_object* v___x_3689_; 
if (v_isShared_3632_ == 0)
{
lean_ctor_set(v___x_3631_, 1, v___x_3687_);
lean_ctor_set(v___x_3631_, 0, v___x_3642_);
v___x_3689_ = v___x_3631_;
goto v_reusejp_3688_;
}
else
{
lean_object* v_reuseFailAlloc_3691_; 
v_reuseFailAlloc_3691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3691_, 0, v___x_3642_);
lean_ctor_set(v_reuseFailAlloc_3691_, 1, v___x_3687_);
v___x_3689_ = v_reuseFailAlloc_3691_;
goto v_reusejp_3688_;
}
v_reusejp_3688_:
{
v_as_x27_3619_ = v_tail_3633_;
v_b_3620_ = v___x_3689_;
goto _start;
}
}
}
else
{
lean_object* v_a_3693_; lean_object* v___x_3695_; uint8_t v_isShared_3696_; uint8_t v_isSharedCheck_3723_; 
v_a_3693_ = lean_ctor_get(v___x_3682_, 0);
v_isSharedCheck_3723_ = !lean_is_exclusive(v___x_3682_);
if (v_isSharedCheck_3723_ == 0)
{
v___x_3695_ = v___x_3682_;
v_isShared_3696_ = v_isSharedCheck_3723_;
goto v_resetjp_3694_;
}
else
{
lean_inc(v_a_3693_);
lean_dec(v___x_3682_);
v___x_3695_ = lean_box(0);
v_isShared_3696_ = v_isSharedCheck_3723_;
goto v_resetjp_3694_;
}
v_resetjp_3694_:
{
uint8_t v___x_3697_; 
v___x_3697_ = lean_unbox(v_a_3693_);
lean_dec(v_a_3693_);
if (v___x_3697_ == 0)
{
lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3702_; 
lean_del_object(v___x_3695_);
lean_del_object(v___x_3672_);
v___x_3698_ = lean_box(0);
v___x_3699_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1___redArg(v_fst_3637_, v_a_3679_, v___x_3698_);
v___x_3700_ = lean_array_push(v_snd_3638_, v_val_3670_);
if (v_isShared_3641_ == 0)
{
lean_ctor_set(v___x_3640_, 1, v___x_3700_);
lean_ctor_set(v___x_3640_, 0, v___x_3699_);
v___x_3702_ = v___x_3640_;
goto v_reusejp_3701_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v___x_3699_);
lean_ctor_set(v_reuseFailAlloc_3707_, 1, v___x_3700_);
v___x_3702_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3701_;
}
v_reusejp_3701_:
{
lean_object* v___x_3704_; 
if (v_isShared_3632_ == 0)
{
lean_ctor_set(v___x_3631_, 1, v___x_3702_);
lean_ctor_set(v___x_3631_, 0, v___x_3642_);
v___x_3704_ = v___x_3631_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3706_; 
v_reuseFailAlloc_3706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3706_, 0, v___x_3642_);
lean_ctor_set(v_reuseFailAlloc_3706_, 1, v___x_3702_);
v___x_3704_ = v_reuseFailAlloc_3706_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
v_as_x27_3619_ = v_tail_3633_;
v_b_3620_ = v___x_3704_;
goto _start;
}
}
}
else
{
lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3712_; 
lean_dec(v_a_3679_);
lean_dec_ref(v_cfg_3618_);
v___x_3708_ = lean_unsigned_to_nat(1u);
v___x_3709_ = lean_mk_empty_array_with_capacity(v___x_3708_);
v___x_3710_ = lean_array_push(v___x_3709_, v_val_3670_);
if (v_isShared_3673_ == 0)
{
lean_ctor_set(v___x_3672_, 0, v___x_3710_);
v___x_3712_ = v___x_3672_;
goto v_reusejp_3711_;
}
else
{
lean_object* v_reuseFailAlloc_3722_; 
v_reuseFailAlloc_3722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3722_, 0, v___x_3710_);
v___x_3712_ = v_reuseFailAlloc_3722_;
goto v_reusejp_3711_;
}
v_reusejp_3711_:
{
lean_object* v___x_3714_; 
if (v_isShared_3641_ == 0)
{
v___x_3714_ = v___x_3640_;
goto v_reusejp_3713_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v_fst_3637_);
lean_ctor_set(v_reuseFailAlloc_3721_, 1, v_snd_3638_);
v___x_3714_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3713_;
}
v_reusejp_3713_:
{
lean_object* v___x_3716_; 
if (v_isShared_3632_ == 0)
{
lean_ctor_set(v___x_3631_, 1, v___x_3714_);
lean_ctor_set(v___x_3631_, 0, v___x_3712_);
v___x_3716_ = v___x_3631_;
goto v_reusejp_3715_;
}
else
{
lean_object* v_reuseFailAlloc_3720_; 
v_reuseFailAlloc_3720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3720_, 0, v___x_3712_);
lean_ctor_set(v_reuseFailAlloc_3720_, 1, v___x_3714_);
v___x_3716_ = v_reuseFailAlloc_3720_;
goto v_reusejp_3715_;
}
v_reusejp_3715_:
{
lean_object* v___x_3718_; 
if (v_isShared_3696_ == 0)
{
lean_ctor_set(v___x_3695_, 0, v___x_3716_);
v___x_3718_ = v___x_3695_;
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
return v___x_3718_;
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
lean_object* v_a_3724_; lean_object* v___x_3726_; uint8_t v_isShared_3727_; uint8_t v_isSharedCheck_3731_; 
lean_dec(v_a_3679_);
lean_del_object(v___x_3672_);
lean_dec(v_val_3670_);
lean_del_object(v___x_3640_);
lean_dec(v_snd_3638_);
lean_dec(v_fst_3637_);
lean_del_object(v___x_3631_);
lean_dec_ref(v_cfg_3618_);
v_a_3724_ = lean_ctor_get(v___x_3682_, 0);
v_isSharedCheck_3731_ = !lean_is_exclusive(v___x_3682_);
if (v_isSharedCheck_3731_ == 0)
{
v___x_3726_ = v___x_3682_;
v_isShared_3727_ = v_isSharedCheck_3731_;
goto v_resetjp_3725_;
}
else
{
lean_inc(v_a_3724_);
lean_dec(v___x_3682_);
v___x_3726_ = lean_box(0);
v_isShared_3727_ = v_isSharedCheck_3731_;
goto v_resetjp_3725_;
}
v_resetjp_3725_:
{
lean_object* v___x_3729_; 
if (v_isShared_3727_ == 0)
{
v___x_3729_ = v___x_3726_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v_a_3724_);
v___x_3729_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
return v___x_3729_;
}
}
}
}
else
{
lean_object* v___x_3733_; 
lean_dec(v_a_3679_);
lean_del_object(v___x_3672_);
lean_dec(v_val_3670_);
if (v_isShared_3641_ == 0)
{
v___x_3733_ = v___x_3640_;
goto v_reusejp_3732_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v_fst_3637_);
lean_ctor_set(v_reuseFailAlloc_3738_, 1, v_snd_3638_);
v___x_3733_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3732_;
}
v_reusejp_3732_:
{
lean_object* v___x_3735_; 
if (v_isShared_3632_ == 0)
{
lean_ctor_set(v___x_3631_, 1, v___x_3733_);
lean_ctor_set(v___x_3631_, 0, v___x_3642_);
v___x_3735_ = v___x_3631_;
goto v_reusejp_3734_;
}
else
{
lean_object* v_reuseFailAlloc_3737_; 
v_reuseFailAlloc_3737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3737_, 0, v___x_3642_);
lean_ctor_set(v_reuseFailAlloc_3737_, 1, v___x_3733_);
v___x_3735_ = v_reuseFailAlloc_3737_;
goto v_reusejp_3734_;
}
v_reusejp_3734_:
{
v_as_x27_3619_ = v_tail_3633_;
v_b_3620_ = v___x_3735_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3739_; lean_object* v___x_3741_; uint8_t v_isShared_3742_; uint8_t v_isSharedCheck_3746_; 
lean_del_object(v___x_3672_);
lean_dec(v_val_3670_);
lean_del_object(v___x_3640_);
lean_dec(v_snd_3638_);
lean_dec(v_fst_3637_);
lean_del_object(v___x_3631_);
lean_dec_ref(v_cfg_3618_);
v_a_3739_ = lean_ctor_get(v___x_3678_, 0);
v_isSharedCheck_3746_ = !lean_is_exclusive(v___x_3678_);
if (v_isSharedCheck_3746_ == 0)
{
v___x_3741_ = v___x_3678_;
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
else
{
lean_inc(v_a_3739_);
lean_dec(v___x_3678_);
v___x_3741_ = lean_box(0);
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
v_resetjp_3740_:
{
lean_object* v___x_3744_; 
if (v_isShared_3742_ == 0)
{
v___x_3744_ = v___x_3741_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v_a_3739_);
v___x_3744_ = v_reuseFailAlloc_3745_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
return v___x_3744_;
}
}
}
}
}
}
else
{
lean_object* v_a_3748_; lean_object* v___x_3750_; uint8_t v_isShared_3751_; uint8_t v_isSharedCheck_3755_; 
lean_del_object(v___x_3640_);
lean_dec(v_snd_3638_);
lean_dec(v_fst_3637_);
lean_del_object(v___x_3631_);
lean_dec_ref(v_cfg_3618_);
v_a_3748_ = lean_ctor_get(v___x_3661_, 0);
v_isSharedCheck_3755_ = !lean_is_exclusive(v___x_3661_);
if (v_isSharedCheck_3755_ == 0)
{
v___x_3750_ = v___x_3661_;
v_isShared_3751_ = v_isSharedCheck_3755_;
goto v_resetjp_3749_;
}
else
{
lean_inc(v_a_3748_);
lean_dec(v___x_3661_);
v___x_3750_ = lean_box(0);
v_isShared_3751_ = v_isSharedCheck_3755_;
goto v_resetjp_3749_;
}
v_resetjp_3749_:
{
lean_object* v___x_3753_; 
if (v_isShared_3751_ == 0)
{
v___x_3753_ = v___x_3750_;
goto v_reusejp_3752_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v_a_3748_);
v___x_3753_ = v_reuseFailAlloc_3754_;
goto v_reusejp_3752_;
}
v_reusejp_3752_:
{
return v___x_3753_;
}
}
}
}
else
{
lean_object* v___x_3756_; lean_object* v___x_3758_; 
lean_dec_ref(v_cfg_3618_);
lean_inc(v_snd_3638_);
v___x_3756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3756_, 0, v_snd_3638_);
if (v_isShared_3641_ == 0)
{
v___x_3758_ = v___x_3640_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3765_; 
v_reuseFailAlloc_3765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3765_, 0, v_fst_3637_);
lean_ctor_set(v_reuseFailAlloc_3765_, 1, v_snd_3638_);
v___x_3758_ = v_reuseFailAlloc_3765_;
goto v_reusejp_3757_;
}
v_reusejp_3757_:
{
lean_object* v___x_3760_; 
if (v_isShared_3632_ == 0)
{
lean_ctor_set(v___x_3631_, 1, v___x_3758_);
lean_ctor_set(v___x_3631_, 0, v___x_3756_);
v___x_3760_ = v___x_3631_;
goto v_reusejp_3759_;
}
else
{
lean_object* v_reuseFailAlloc_3764_; 
v_reuseFailAlloc_3764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3764_, 0, v___x_3756_);
lean_ctor_set(v_reuseFailAlloc_3764_, 1, v___x_3758_);
v___x_3760_ = v_reuseFailAlloc_3764_;
goto v_reusejp_3759_;
}
v_reusejp_3759_:
{
lean_object* v___x_3762_; 
if (v_isShared_3647_ == 0)
{
lean_ctor_set(v___x_3646_, 0, v___x_3760_);
v___x_3762_ = v___x_3646_;
goto v_reusejp_3761_;
}
else
{
lean_object* v_reuseFailAlloc_3763_; 
v_reuseFailAlloc_3763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3763_, 0, v___x_3760_);
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
}
else
{
lean_object* v___x_3766_; lean_object* v___x_3768_; 
lean_dec_ref(v_cfg_3618_);
lean_inc(v_snd_3638_);
v___x_3766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3766_, 0, v_snd_3638_);
if (v_isShared_3641_ == 0)
{
v___x_3768_ = v___x_3640_;
goto v_reusejp_3767_;
}
else
{
lean_object* v_reuseFailAlloc_3775_; 
v_reuseFailAlloc_3775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3775_, 0, v_fst_3637_);
lean_ctor_set(v_reuseFailAlloc_3775_, 1, v_snd_3638_);
v___x_3768_ = v_reuseFailAlloc_3775_;
goto v_reusejp_3767_;
}
v_reusejp_3767_:
{
lean_object* v___x_3770_; 
if (v_isShared_3632_ == 0)
{
lean_ctor_set(v___x_3631_, 1, v___x_3768_);
lean_ctor_set(v___x_3631_, 0, v___x_3766_);
v___x_3770_ = v___x_3631_;
goto v_reusejp_3769_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v___x_3766_);
lean_ctor_set(v_reuseFailAlloc_3774_, 1, v___x_3768_);
v___x_3770_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3769_;
}
v_reusejp_3769_:
{
lean_object* v___x_3772_; 
if (v_isShared_3647_ == 0)
{
lean_ctor_set(v___x_3646_, 0, v___x_3770_);
v___x_3772_ = v___x_3646_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3773_; 
v_reuseFailAlloc_3773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3773_, 0, v___x_3770_);
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
}
}
else
{
lean_object* v_a_3777_; lean_object* v___x_3779_; uint8_t v_isShared_3780_; uint8_t v_isSharedCheck_3784_; 
lean_del_object(v___x_3640_);
lean_dec(v_snd_3638_);
lean_dec(v_fst_3637_);
lean_del_object(v___x_3631_);
lean_dec_ref(v_cfg_3618_);
v_a_3777_ = lean_ctor_get(v___x_3643_, 0);
v_isSharedCheck_3784_ = !lean_is_exclusive(v___x_3643_);
if (v_isSharedCheck_3784_ == 0)
{
v___x_3779_ = v___x_3643_;
v_isShared_3780_ = v_isSharedCheck_3784_;
goto v_resetjp_3778_;
}
else
{
lean_inc(v_a_3777_);
lean_dec(v___x_3643_);
v___x_3779_ = lean_box(0);
v_isShared_3780_ = v_isSharedCheck_3784_;
goto v_resetjp_3778_;
}
v_resetjp_3778_:
{
lean_object* v___x_3782_; 
if (v_isShared_3780_ == 0)
{
v___x_3782_ = v___x_3779_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3783_; 
v_reuseFailAlloc_3783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3783_, 0, v_a_3777_);
v___x_3782_ = v_reuseFailAlloc_3783_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
return v___x_3782_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg___boxed(lean_object* v_cfg_3788_, lean_object* v_as_x27_3789_, lean_object* v_b_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_){
_start:
{
lean_object* v_res_3796_; 
v_res_3796_ = l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg(v_cfg_3788_, v_as_x27_3789_, v_b_3790_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_);
lean_dec(v___y_3794_);
lean_dec_ref(v___y_3793_);
lean_dec(v___y_3792_);
lean_dec_ref(v___y_3791_);
lean_dec(v_as_x27_3789_);
return v_res_3796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_takeListAux(lean_object* v_cfg_3797_, lean_object* v_seen_3798_, lean_object* v_acc_3799_, lean_object* v_xs_3800_, lean_object* v_a_3801_, lean_object* v_a_3802_, lean_object* v_a_3803_, lean_object* v_a_3804_){
_start:
{
lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; 
v___x_3806_ = lean_box(0);
v___x_3807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3807_, 0, v_seen_3798_);
lean_ctor_set(v___x_3807_, 1, v_acc_3799_);
v___x_3808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3808_, 0, v___x_3806_);
lean_ctor_set(v___x_3808_, 1, v___x_3807_);
v___x_3809_ = l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg(v_cfg_3797_, v_xs_3800_, v___x_3808_, v_a_3801_, v_a_3802_, v_a_3803_, v_a_3804_);
if (lean_obj_tag(v___x_3809_) == 0)
{
lean_object* v_a_3810_; lean_object* v___x_3812_; uint8_t v_isShared_3813_; uint8_t v_isSharedCheck_3824_; 
v_a_3810_ = lean_ctor_get(v___x_3809_, 0);
v_isSharedCheck_3824_ = !lean_is_exclusive(v___x_3809_);
if (v_isSharedCheck_3824_ == 0)
{
v___x_3812_ = v___x_3809_;
v_isShared_3813_ = v_isSharedCheck_3824_;
goto v_resetjp_3811_;
}
else
{
lean_inc(v_a_3810_);
lean_dec(v___x_3809_);
v___x_3812_ = lean_box(0);
v_isShared_3813_ = v_isSharedCheck_3824_;
goto v_resetjp_3811_;
}
v_resetjp_3811_:
{
lean_object* v_fst_3814_; 
v_fst_3814_ = lean_ctor_get(v_a_3810_, 0);
if (lean_obj_tag(v_fst_3814_) == 0)
{
lean_object* v_snd_3815_; lean_object* v_snd_3816_; lean_object* v___x_3818_; 
v_snd_3815_ = lean_ctor_get(v_a_3810_, 1);
lean_inc(v_snd_3815_);
lean_dec(v_a_3810_);
v_snd_3816_ = lean_ctor_get(v_snd_3815_, 1);
lean_inc(v_snd_3816_);
lean_dec(v_snd_3815_);
if (v_isShared_3813_ == 0)
{
lean_ctor_set(v___x_3812_, 0, v_snd_3816_);
v___x_3818_ = v___x_3812_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v_snd_3816_);
v___x_3818_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3817_;
}
v_reusejp_3817_:
{
return v___x_3818_;
}
}
else
{
lean_object* v_val_3820_; lean_object* v___x_3822_; 
lean_inc_ref(v_fst_3814_);
lean_dec(v_a_3810_);
v_val_3820_ = lean_ctor_get(v_fst_3814_, 0);
lean_inc(v_val_3820_);
lean_dec_ref_known(v_fst_3814_, 1);
if (v_isShared_3813_ == 0)
{
lean_ctor_set(v___x_3812_, 0, v_val_3820_);
v___x_3822_ = v___x_3812_;
goto v_reusejp_3821_;
}
else
{
lean_object* v_reuseFailAlloc_3823_; 
v_reuseFailAlloc_3823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3823_, 0, v_val_3820_);
v___x_3822_ = v_reuseFailAlloc_3823_;
goto v_reusejp_3821_;
}
v_reusejp_3821_:
{
return v___x_3822_;
}
}
}
}
else
{
lean_object* v_a_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3832_; 
v_a_3825_ = lean_ctor_get(v___x_3809_, 0);
v_isSharedCheck_3832_ = !lean_is_exclusive(v___x_3809_);
if (v_isSharedCheck_3832_ == 0)
{
v___x_3827_ = v___x_3809_;
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_a_3825_);
lean_dec(v___x_3809_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
lean_object* v___x_3830_; 
if (v_isShared_3828_ == 0)
{
v___x_3830_ = v___x_3827_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v_a_3825_);
v___x_3830_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
return v___x_3830_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_takeListAux___boxed(lean_object* v_cfg_3833_, lean_object* v_seen_3834_, lean_object* v_acc_3835_, lean_object* v_xs_3836_, lean_object* v_a_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_, lean_object* v_a_3840_, lean_object* v_a_3841_){
_start:
{
lean_object* v_res_3842_; 
v_res_3842_ = l_Lean_Meta_Rewrites_takeListAux(v_cfg_3833_, v_seen_3834_, v_acc_3835_, v_xs_3836_, v_a_3837_, v_a_3838_, v_a_3839_, v_a_3840_);
lean_dec(v_a_3840_);
lean_dec_ref(v_a_3839_);
lean_dec(v_a_3838_);
lean_dec_ref(v_a_3837_);
lean_dec(v_xs_3836_);
return v_res_3842_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0(lean_object* v_00_u03b2_3843_, lean_object* v_m_3844_, lean_object* v_a_3845_){
_start:
{
uint8_t v___x_3846_; 
v___x_3846_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg(v_m_3844_, v_a_3845_);
return v___x_3846_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___boxed(lean_object* v_00_u03b2_3847_, lean_object* v_m_3848_, lean_object* v_a_3849_){
_start:
{
uint8_t v_res_3850_; lean_object* v_r_3851_; 
v_res_3850_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0(v_00_u03b2_3847_, v_m_3848_, v_a_3849_);
lean_dec_ref(v_a_3849_);
lean_dec_ref(v_m_3848_);
v_r_3851_ = lean_box(v_res_3850_);
return v_r_3851_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1(lean_object* v_00_u03b2_3852_, lean_object* v_m_3853_, lean_object* v_a_3854_, lean_object* v_b_3855_){
_start:
{
lean_object* v___x_3856_; 
v___x_3856_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1___redArg(v_m_3853_, v_a_3854_, v_b_3855_);
return v___x_3856_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2(lean_object* v_cfg_3857_, lean_object* v_as_3858_, lean_object* v_as_x27_3859_, lean_object* v_b_3860_, lean_object* v_a_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_){
_start:
{
lean_object* v___x_3867_; 
v___x_3867_ = l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg(v_cfg_3857_, v_as_x27_3859_, v_b_3860_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_);
return v___x_3867_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___boxed(lean_object* v_cfg_3868_, lean_object* v_as_3869_, lean_object* v_as_x27_3870_, lean_object* v_b_3871_, lean_object* v_a_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_){
_start:
{
lean_object* v_res_3878_; 
v_res_3878_ = l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2(v_cfg_3868_, v_as_3869_, v_as_x27_3870_, v_b_3871_, v_a_3872_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_);
lean_dec(v___y_3876_);
lean_dec_ref(v___y_3875_);
lean_dec(v___y_3874_);
lean_dec_ref(v___y_3873_);
lean_dec(v_as_x27_3870_);
lean_dec(v_as_3869_);
return v_res_3878_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0(lean_object* v_00_u03b2_3879_, lean_object* v_a_3880_, lean_object* v_x_3881_){
_start:
{
uint8_t v___x_3882_; 
v___x_3882_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(v_a_3880_, v_x_3881_);
return v___x_3882_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3883_, lean_object* v_a_3884_, lean_object* v_x_3885_){
_start:
{
uint8_t v_res_3886_; lean_object* v_r_3887_; 
v_res_3886_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0(v_00_u03b2_3883_, v_a_3884_, v_x_3885_);
lean_dec(v_x_3885_);
lean_dec_ref(v_a_3884_);
v_r_3887_ = lean_box(v_res_3886_);
return v_r_3887_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2(lean_object* v_00_u03b2_3888_, lean_object* v_data_3889_){
_start:
{
lean_object* v___x_3890_; 
v___x_3890_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2___redArg(v_data_3889_);
return v___x_3890_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3(lean_object* v_00_u03b2_3891_, lean_object* v_a_3892_, lean_object* v_b_3893_, lean_object* v_x_3894_){
_start:
{
lean_object* v___x_3895_; 
v___x_3895_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3___redArg(v_a_3892_, v_b_3893_, v_x_3894_);
return v___x_3895_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_3896_, lean_object* v_i_3897_, lean_object* v_source_3898_, lean_object* v_target_3899_){
_start:
{
lean_object* v___x_3900_; 
v___x_3900_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3___redArg(v_i_3897_, v_source_3898_, v_target_3899_);
return v___x_3900_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_3901_, lean_object* v_x_3902_, lean_object* v_x_3903_){
_start:
{
lean_object* v___x_3904_; 
v___x_3904_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3_spec__5___redArg(v_x_3902_, v_x_3903_);
return v___x_3904_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_findRewrites___closed__0(void){
_start:
{
lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; 
v___x_3905_ = lean_box(0);
v___x_3906_ = lean_unsigned_to_nat(16u);
v___x_3907_ = lean_mk_array(v___x_3906_, v___x_3905_);
return v___x_3907_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_findRewrites___closed__1(void){
_start:
{
lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; 
v___x_3908_ = lean_obj_once(&l_Lean_Meta_Rewrites_findRewrites___closed__0, &l_Lean_Meta_Rewrites_findRewrites___closed__0_once, _init_l_Lean_Meta_Rewrites_findRewrites___closed__0);
v___x_3909_ = lean_unsigned_to_nat(0u);
v___x_3910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3910_, 0, v___x_3909_);
lean_ctor_set(v___x_3910_, 1, v___x_3908_);
return v___x_3910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_findRewrites(lean_object* v_hyps_3911_, lean_object* v_moduleRef_3912_, lean_object* v_goal_3913_, lean_object* v_target_3914_, lean_object* v_forbidden_3915_, uint8_t v_side_3916_, uint8_t v_stopAtRfl_3917_, lean_object* v_max_3918_, lean_object* v_leavePercentHeartbeats_3919_, lean_object* v_a_3920_, lean_object* v_a_3921_, lean_object* v_a_3922_, lean_object* v_a_3923_){
_start:
{
lean_object* v___x_3925_; lean_object* v_mctx_3926_; lean_object* v___x_3927_; 
v___x_3925_ = lean_st_ref_get(v_a_3921_);
v_mctx_3926_ = lean_ctor_get(v___x_3925_, 0);
lean_inc_ref(v_mctx_3926_);
lean_dec(v___x_3925_);
lean_inc_ref(v_target_3914_);
v___x_3927_ = l_Lean_Meta_Rewrites_rewriteCandidates(v_hyps_3911_, v_moduleRef_3912_, v_target_3914_, v_forbidden_3915_, v_a_3920_, v_a_3921_, v_a_3922_, v_a_3923_);
if (lean_obj_tag(v___x_3927_) == 0)
{
lean_object* v_a_3928_; lean_object* v_minHeartbeats_3930_; lean_object* v___y_3931_; lean_object* v___y_3932_; lean_object* v___y_3933_; lean_object* v___y_3934_; lean_object* v___x_3957_; 
v_a_3928_ = lean_ctor_get(v___x_3927_, 0);
lean_inc(v_a_3928_);
lean_dec_ref_known(v___x_3927_, 1);
v___x_3957_ = l_Lean_getMaxHeartbeats___redArg(v_a_3922_);
if (lean_obj_tag(v___x_3957_) == 0)
{
lean_object* v_a_3958_; lean_object* v___x_3959_; uint8_t v___x_3960_; 
v_a_3958_ = lean_ctor_get(v___x_3957_, 0);
lean_inc(v_a_3958_);
lean_dec_ref_known(v___x_3957_, 1);
v___x_3959_ = lean_unsigned_to_nat(0u);
v___x_3960_ = lean_nat_dec_eq(v_a_3958_, v___x_3959_);
lean_dec(v_a_3958_);
if (v___x_3960_ == 0)
{
lean_object* v___x_3961_; 
v___x_3961_ = l_Lean_getRemainingHeartbeats___redArg(v_a_3922_);
if (lean_obj_tag(v___x_3961_) == 0)
{
lean_object* v_a_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; 
v_a_3962_ = lean_ctor_get(v___x_3961_, 0);
lean_inc(v_a_3962_);
lean_dec_ref_known(v___x_3961_, 1);
v___x_3963_ = lean_nat_mul(v_leavePercentHeartbeats_3919_, v_a_3962_);
lean_dec(v_a_3962_);
v___x_3964_ = lean_unsigned_to_nat(100u);
v___x_3965_ = lean_nat_div(v___x_3963_, v___x_3964_);
lean_dec(v___x_3963_);
v_minHeartbeats_3930_ = v___x_3965_;
v___y_3931_ = v_a_3920_;
v___y_3932_ = v_a_3921_;
v___y_3933_ = v_a_3922_;
v___y_3934_ = v_a_3923_;
goto v___jp_3929_;
}
else
{
lean_object* v_a_3966_; lean_object* v___x_3968_; uint8_t v_isShared_3969_; uint8_t v_isSharedCheck_3973_; 
lean_dec(v_a_3928_);
lean_dec_ref(v_mctx_3926_);
lean_dec(v_max_3918_);
lean_dec_ref(v_target_3914_);
lean_dec(v_goal_3913_);
v_a_3966_ = lean_ctor_get(v___x_3961_, 0);
v_isSharedCheck_3973_ = !lean_is_exclusive(v___x_3961_);
if (v_isSharedCheck_3973_ == 0)
{
v___x_3968_ = v___x_3961_;
v_isShared_3969_ = v_isSharedCheck_3973_;
goto v_resetjp_3967_;
}
else
{
lean_inc(v_a_3966_);
lean_dec(v___x_3961_);
v___x_3968_ = lean_box(0);
v_isShared_3969_ = v_isSharedCheck_3973_;
goto v_resetjp_3967_;
}
v_resetjp_3967_:
{
lean_object* v___x_3971_; 
if (v_isShared_3969_ == 0)
{
v___x_3971_ = v___x_3968_;
goto v_reusejp_3970_;
}
else
{
lean_object* v_reuseFailAlloc_3972_; 
v_reuseFailAlloc_3972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3972_, 0, v_a_3966_);
v___x_3971_ = v_reuseFailAlloc_3972_;
goto v_reusejp_3970_;
}
v_reusejp_3970_:
{
return v___x_3971_;
}
}
}
}
else
{
v_minHeartbeats_3930_ = v___x_3959_;
v___y_3931_ = v_a_3920_;
v___y_3932_ = v_a_3921_;
v___y_3933_ = v_a_3922_;
v___y_3934_ = v_a_3923_;
goto v___jp_3929_;
}
}
else
{
lean_object* v_a_3974_; lean_object* v___x_3976_; uint8_t v_isShared_3977_; uint8_t v_isSharedCheck_3981_; 
lean_dec(v_a_3928_);
lean_dec_ref(v_mctx_3926_);
lean_dec(v_max_3918_);
lean_dec_ref(v_target_3914_);
lean_dec(v_goal_3913_);
v_a_3974_ = lean_ctor_get(v___x_3957_, 0);
v_isSharedCheck_3981_ = !lean_is_exclusive(v___x_3957_);
if (v_isSharedCheck_3981_ == 0)
{
v___x_3976_ = v___x_3957_;
v_isShared_3977_ = v_isSharedCheck_3981_;
goto v_resetjp_3975_;
}
else
{
lean_inc(v_a_3974_);
lean_dec(v___x_3957_);
v___x_3976_ = lean_box(0);
v_isShared_3977_ = v_isSharedCheck_3981_;
goto v_resetjp_3975_;
}
v_resetjp_3975_:
{
lean_object* v___x_3979_; 
if (v_isShared_3977_ == 0)
{
v___x_3979_ = v___x_3976_;
goto v_reusejp_3978_;
}
else
{
lean_object* v_reuseFailAlloc_3980_; 
v_reuseFailAlloc_3980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3980_, 0, v_a_3974_);
v___x_3979_ = v_reuseFailAlloc_3980_;
goto v_reusejp_3978_;
}
v_reusejp_3978_:
{
return v___x_3979_;
}
}
}
v___jp_3929_:
{
lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; 
lean_inc(v_max_3918_);
v___x_3935_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_3935_, 0, v_max_3918_);
lean_ctor_set(v___x_3935_, 1, v_minHeartbeats_3930_);
lean_ctor_set(v___x_3935_, 2, v_goal_3913_);
lean_ctor_set(v___x_3935_, 3, v_target_3914_);
lean_ctor_set(v___x_3935_, 4, v_mctx_3926_);
lean_ctor_set_uint8(v___x_3935_, sizeof(void*)*5, v_stopAtRfl_3917_);
lean_ctor_set_uint8(v___x_3935_, sizeof(void*)*5 + 1, v_side_3916_);
v___x_3936_ = lean_obj_once(&l_Lean_Meta_Rewrites_findRewrites___closed__1, &l_Lean_Meta_Rewrites_findRewrites___closed__1_once, _init_l_Lean_Meta_Rewrites_findRewrites___closed__1);
v___x_3937_ = lean_mk_empty_array_with_capacity(v_max_3918_);
lean_dec(v_max_3918_);
v___x_3938_ = lean_array_to_list(v_a_3928_);
v___x_3939_ = l_Lean_Meta_Rewrites_takeListAux(v___x_3935_, v___x_3936_, v___x_3937_, v___x_3938_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_);
lean_dec(v___x_3938_);
if (lean_obj_tag(v___x_3939_) == 0)
{
lean_object* v_a_3940_; lean_object* v___x_3942_; uint8_t v_isShared_3943_; uint8_t v_isSharedCheck_3948_; 
v_a_3940_ = lean_ctor_get(v___x_3939_, 0);
v_isSharedCheck_3948_ = !lean_is_exclusive(v___x_3939_);
if (v_isSharedCheck_3948_ == 0)
{
v___x_3942_ = v___x_3939_;
v_isShared_3943_ = v_isSharedCheck_3948_;
goto v_resetjp_3941_;
}
else
{
lean_inc(v_a_3940_);
lean_dec(v___x_3939_);
v___x_3942_ = lean_box(0);
v_isShared_3943_ = v_isSharedCheck_3948_;
goto v_resetjp_3941_;
}
v_resetjp_3941_:
{
lean_object* v___x_3944_; lean_object* v___x_3946_; 
v___x_3944_ = lean_array_to_list(v_a_3940_);
if (v_isShared_3943_ == 0)
{
lean_ctor_set(v___x_3942_, 0, v___x_3944_);
v___x_3946_ = v___x_3942_;
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
lean_object* v_a_3949_; lean_object* v___x_3951_; uint8_t v_isShared_3952_; uint8_t v_isSharedCheck_3956_; 
v_a_3949_ = lean_ctor_get(v___x_3939_, 0);
v_isSharedCheck_3956_ = !lean_is_exclusive(v___x_3939_);
if (v_isSharedCheck_3956_ == 0)
{
v___x_3951_ = v___x_3939_;
v_isShared_3952_ = v_isSharedCheck_3956_;
goto v_resetjp_3950_;
}
else
{
lean_inc(v_a_3949_);
lean_dec(v___x_3939_);
v___x_3951_ = lean_box(0);
v_isShared_3952_ = v_isSharedCheck_3956_;
goto v_resetjp_3950_;
}
v_resetjp_3950_:
{
lean_object* v___x_3954_; 
if (v_isShared_3952_ == 0)
{
v___x_3954_ = v___x_3951_;
goto v_reusejp_3953_;
}
else
{
lean_object* v_reuseFailAlloc_3955_; 
v_reuseFailAlloc_3955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3955_, 0, v_a_3949_);
v___x_3954_ = v_reuseFailAlloc_3955_;
goto v_reusejp_3953_;
}
v_reusejp_3953_:
{
return v___x_3954_;
}
}
}
}
}
else
{
lean_object* v_a_3982_; lean_object* v___x_3984_; uint8_t v_isShared_3985_; uint8_t v_isSharedCheck_3989_; 
lean_dec_ref(v_mctx_3926_);
lean_dec(v_max_3918_);
lean_dec_ref(v_target_3914_);
lean_dec(v_goal_3913_);
v_a_3982_ = lean_ctor_get(v___x_3927_, 0);
v_isSharedCheck_3989_ = !lean_is_exclusive(v___x_3927_);
if (v_isSharedCheck_3989_ == 0)
{
v___x_3984_ = v___x_3927_;
v_isShared_3985_ = v_isSharedCheck_3989_;
goto v_resetjp_3983_;
}
else
{
lean_inc(v_a_3982_);
lean_dec(v___x_3927_);
v___x_3984_ = lean_box(0);
v_isShared_3985_ = v_isSharedCheck_3989_;
goto v_resetjp_3983_;
}
v_resetjp_3983_:
{
lean_object* v___x_3987_; 
if (v_isShared_3985_ == 0)
{
v___x_3987_ = v___x_3984_;
goto v_reusejp_3986_;
}
else
{
lean_object* v_reuseFailAlloc_3988_; 
v_reuseFailAlloc_3988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3988_, 0, v_a_3982_);
v___x_3987_ = v_reuseFailAlloc_3988_;
goto v_reusejp_3986_;
}
v_reusejp_3986_:
{
return v___x_3987_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_findRewrites___boxed(lean_object* v_hyps_3990_, lean_object* v_moduleRef_3991_, lean_object* v_goal_3992_, lean_object* v_target_3993_, lean_object* v_forbidden_3994_, lean_object* v_side_3995_, lean_object* v_stopAtRfl_3996_, lean_object* v_max_3997_, lean_object* v_leavePercentHeartbeats_3998_, lean_object* v_a_3999_, lean_object* v_a_4000_, lean_object* v_a_4001_, lean_object* v_a_4002_, lean_object* v_a_4003_){
_start:
{
uint8_t v_side_boxed_4004_; uint8_t v_stopAtRfl_boxed_4005_; lean_object* v_res_4006_; 
v_side_boxed_4004_ = lean_unbox(v_side_3995_);
v_stopAtRfl_boxed_4005_ = lean_unbox(v_stopAtRfl_3996_);
v_res_4006_ = l_Lean_Meta_Rewrites_findRewrites(v_hyps_3990_, v_moduleRef_3991_, v_goal_3992_, v_target_3993_, v_forbidden_3994_, v_side_boxed_4004_, v_stopAtRfl_boxed_4005_, v_max_3997_, v_leavePercentHeartbeats_3998_, v_a_3999_, v_a_4000_, v_a_4001_, v_a_4002_);
lean_dec(v_a_4002_);
lean_dec_ref(v_a_4001_);
lean_dec(v_a_4000_);
lean_dec_ref(v_a_3999_);
lean_dec(v_leavePercentHeartbeats_3998_);
lean_dec(v_forbidden_3994_);
return v_res_4006_;
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

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
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
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
uint8_t v___x_4624__boxed_490_; uint8_t v___x_4626__boxed_491_; lean_object* v_res_492_; 
v___x_4624__boxed_490_ = lean_unbox(v___x_481_);
v___x_4626__boxed_491_ = lean_unbox(v___x_484_);
v_res_492_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__1(v___x_4624__boxed_490_, v_type_482_, v___f_483_, v___x_4626__boxed_491_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
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
lean_object* v___x_509_; lean_object* v_env_513_; uint8_t v___x_514_; 
v___x_509_ = lean_st_ref_get(v_a_506_);
v_env_513_ = lean_ctor_get(v___x_509_, 0);
lean_inc_ref(v_env_513_);
lean_dec(v___x_509_);
lean_inc(v_name_501_);
v___x_514_ = l_Lean_Meta_allowCompletion(v_env_513_, v_name_501_);
if (v___x_514_ == 0)
{
lean_dec_ref(v_c_502_);
lean_dec(v_name_501_);
goto v___jp_510_;
}
else
{
if (v___x_508_ == 0)
{
lean_object* v___x_515_; lean_object* v_env_516_; uint8_t v___x_517_; 
v___x_515_ = lean_st_ref_get(v_a_506_);
v_env_516_ = lean_ctor_get(v___x_515_, 0);
lean_inc_ref(v_env_516_);
lean_dec(v___x_515_);
lean_inc(v_name_501_);
v___x_517_ = l_Lean_Linter_isDeprecated(v_env_516_, v_name_501_);
if (v___x_517_ == 0)
{
lean_object* v___f_518_; lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v___y_522_; lean_object* v___y_523_; uint8_t v___y_535_; 
lean_inc(v_name_501_);
v___f_518_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___boxed), 8, 1);
lean_closure_set(v___f_518_, 0, v_name_501_);
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
v___y_535_ = v___y_542_;
goto v___jp_534_;
}
else
{
v___y_535_ = v___x_540_;
goto v___jp_534_;
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
v___y_520_ = v_a_503_;
v___y_521_ = v_a_504_;
v___y_522_ = v_a_505_;
v___y_523_ = v_a_506_;
goto v___jp_519_;
}
v___jp_519_:
{
uint8_t v___x_524_; 
v___x_524_ = l_Lean_Name_isMetaprogramming(v_name_501_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; lean_object* v_type_526_; uint8_t v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___f_530_; lean_object* v___x_531_; 
v___x_525_ = l_Lean_AsyncConstantInfo_toConstantVal(v_c_502_);
v_type_526_ = lean_ctor_get(v___x_525_, 2);
lean_inc_ref(v_type_526_);
lean_dec_ref(v___x_525_);
v___x_527_ = 2;
v___x_528_ = lean_box(v___x_527_);
v___x_529_ = lean_box(v___x_524_);
v___f_530_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__1___boxed), 9, 4);
lean_closure_set(v___f_530_, 0, v___x_528_);
lean_closure_set(v___f_530_, 1, v_type_526_);
lean_closure_set(v___f_530_, 2, v___f_518_);
lean_closure_set(v___f_530_, 3, v___x_529_);
v___x_531_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1___redArg(v___f_530_, v___x_524_, v___y_520_, v___y_521_, v___y_522_, v___y_523_);
return v___x_531_;
}
else
{
lean_object* v___x_532_; lean_object* v___x_533_; 
lean_dec_ref(v___f_518_);
lean_dec_ref(v_c_502_);
v___x_532_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0));
v___x_533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_533_, 0, v___x_532_);
return v___x_533_;
}
}
v___jp_534_:
{
if (v___y_535_ == 0)
{
v___y_520_ = v_a_503_;
v___y_521_ = v_a_504_;
v___y_522_ = v_a_505_;
v___y_523_ = v_a_506_;
goto v___jp_519_;
}
else
{
lean_object* v___x_536_; lean_object* v___x_537_; 
lean_dec_ref(v___f_518_);
lean_dec_ref(v_c_502_);
lean_dec(v_name_501_);
v___x_536_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0));
v___x_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
return v___x_537_;
}
}
}
else
{
lean_object* v___x_566_; lean_object* v___x_567_; 
lean_dec_ref(v_c_502_);
lean_dec(v_name_501_);
v___x_566_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0));
v___x_567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
return v___x_567_;
}
}
else
{
lean_dec_ref(v_c_502_);
lean_dec(v_name_501_);
goto v___jp_510_;
}
}
v___jp_510_:
{
lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_511_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0));
v___x_512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_512_, 0, v___x_511_);
return v___x_512_;
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
lean_object* v_a_877_; lean_object* v___x_878_; 
v_a_877_ = lean_array_uget_borrowed(v_as_862_, v_i_864_);
lean_inc(v_snd_873_);
v___x_878_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2(v_init_861_, v_a_877_, v_snd_873_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_898_; 
v_a_879_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_898_ == 0)
{
v___x_881_ = v___x_878_;
v_isShared_882_ = v_isSharedCheck_898_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_878_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_898_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
if (lean_obj_tag(v_a_879_) == 0)
{
lean_object* v___x_883_; lean_object* v___x_885_; 
v___x_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_883_, 0, v_a_879_);
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 0, v___x_883_);
v___x_885_ = v___x_875_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_883_);
lean_ctor_set(v_reuseFailAlloc_889_, 1, v_snd_873_);
v___x_885_ = v_reuseFailAlloc_889_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
lean_object* v___x_887_; 
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 0, v___x_885_);
v___x_887_ = v___x_881_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_885_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
else
{
lean_object* v_a_890_; lean_object* v___x_891_; lean_object* v___x_893_; 
lean_del_object(v___x_881_);
lean_dec(v_snd_873_);
v_a_890_ = lean_ctor_get(v_a_879_, 0);
lean_inc(v_a_890_);
lean_dec_ref_known(v_a_879_, 1);
v___x_891_ = lean_box(0);
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 1, v_a_890_);
lean_ctor_set(v___x_875_, 0, v___x_891_);
v___x_893_ = v___x_875_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v___x_891_);
lean_ctor_set(v_reuseFailAlloc_897_, 1, v_a_890_);
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
v_a_899_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_906_ == 0)
{
v___x_901_ = v___x_878_;
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_dec(v___x_878_);
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
uint8_t v___x_2258__boxed_1460_; lean_object* v_res_1461_; 
v___x_2258__boxed_1460_ = lean_unbox(v___x_1453_);
v_res_1461_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0(v___x_1452_, v___x_2258__boxed_1460_, v___x_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_);
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
lean_object* v_ref_1831_; lean_object* v___x_1832_; lean_object* v_a_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1877_; 
v_ref_1831_ = lean_ctor_get(v___y_1828_, 2);
v___x_1832_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0(v_msg_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_);
v_a_1833_ = lean_ctor_get(v___x_1832_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1832_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1835_ = v___x_1832_;
v_isShared_1836_ = v_isSharedCheck_1877_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_a_1833_);
lean_dec(v___x_1832_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1877_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1837_; lean_object* v_traceState_1838_; lean_object* v_env_1839_; lean_object* v_nextMacroScope_1840_; lean_object* v_ngen_1841_; lean_object* v_auxDeclNGen_1842_; lean_object* v_cache_1843_; lean_object* v_messages_1844_; lean_object* v_infoState_1845_; lean_object* v_snapshotTasks_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1876_; 
v___x_1837_ = lean_st_ref_take(v___y_1829_);
v_traceState_1838_ = lean_ctor_get(v___x_1837_, 4);
v_env_1839_ = lean_ctor_get(v___x_1837_, 0);
v_nextMacroScope_1840_ = lean_ctor_get(v___x_1837_, 1);
v_ngen_1841_ = lean_ctor_get(v___x_1837_, 2);
v_auxDeclNGen_1842_ = lean_ctor_get(v___x_1837_, 3);
v_cache_1843_ = lean_ctor_get(v___x_1837_, 5);
v_messages_1844_ = lean_ctor_get(v___x_1837_, 6);
v_infoState_1845_ = lean_ctor_get(v___x_1837_, 7);
v_snapshotTasks_1846_ = lean_ctor_get(v___x_1837_, 8);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1848_ = v___x_1837_;
v_isShared_1849_ = v_isSharedCheck_1876_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_snapshotTasks_1846_);
lean_inc(v_infoState_1845_);
lean_inc(v_messages_1844_);
lean_inc(v_cache_1843_);
lean_inc(v_traceState_1838_);
lean_inc(v_auxDeclNGen_1842_);
lean_inc(v_ngen_1841_);
lean_inc(v_nextMacroScope_1840_);
lean_inc(v_env_1839_);
lean_dec(v___x_1837_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1876_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
uint64_t v_tid_1850_; lean_object* v_traces_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1875_; 
v_tid_1850_ = lean_ctor_get_uint64(v_traceState_1838_, sizeof(void*)*1);
v_traces_1851_ = lean_ctor_get(v_traceState_1838_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v_traceState_1838_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1853_ = v_traceState_1838_;
v_isShared_1854_ = v_isSharedCheck_1875_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_traces_1851_);
lean_dec(v_traceState_1838_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1875_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1855_; double v___x_1856_; uint8_t v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1865_; 
v___x_1855_ = lean_box(0);
v___x_1856_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__0);
v___x_1857_ = 0;
v___x_1858_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__1));
v___x_1859_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1859_, 0, v_cls_1824_);
lean_ctor_set(v___x_1859_, 1, v___x_1855_);
lean_ctor_set(v___x_1859_, 2, v___x_1858_);
lean_ctor_set_float(v___x_1859_, sizeof(void*)*3, v___x_1856_);
lean_ctor_set_float(v___x_1859_, sizeof(void*)*3 + 8, v___x_1856_);
lean_ctor_set_uint8(v___x_1859_, sizeof(void*)*3 + 16, v___x_1857_);
v___x_1860_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__2));
v___x_1861_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1859_);
lean_ctor_set(v___x_1861_, 1, v_a_1833_);
lean_ctor_set(v___x_1861_, 2, v___x_1860_);
lean_inc(v_ref_1831_);
v___x_1862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1862_, 0, v_ref_1831_);
lean_ctor_set(v___x_1862_, 1, v___x_1861_);
v___x_1863_ = l_Lean_PersistentArray_push___redArg(v_traces_1851_, v___x_1862_);
if (v_isShared_1854_ == 0)
{
lean_ctor_set(v___x_1853_, 0, v___x_1863_);
v___x_1865_ = v___x_1853_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v___x_1863_);
lean_ctor_set_uint64(v_reuseFailAlloc_1874_, sizeof(void*)*1, v_tid_1850_);
v___x_1865_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
lean_object* v___x_1867_; 
if (v_isShared_1849_ == 0)
{
lean_ctor_set(v___x_1848_, 4, v___x_1865_);
v___x_1867_ = v___x_1848_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_env_1839_);
lean_ctor_set(v_reuseFailAlloc_1873_, 1, v_nextMacroScope_1840_);
lean_ctor_set(v_reuseFailAlloc_1873_, 2, v_ngen_1841_);
lean_ctor_set(v_reuseFailAlloc_1873_, 3, v_auxDeclNGen_1842_);
lean_ctor_set(v_reuseFailAlloc_1873_, 4, v___x_1865_);
lean_ctor_set(v_reuseFailAlloc_1873_, 5, v_cache_1843_);
lean_ctor_set(v_reuseFailAlloc_1873_, 6, v_messages_1844_);
lean_ctor_set(v_reuseFailAlloc_1873_, 7, v_infoState_1845_);
lean_ctor_set(v_reuseFailAlloc_1873_, 8, v_snapshotTasks_1846_);
v___x_1867_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1871_; 
v___x_1868_ = lean_st_ref_put(v___y_1829_, v___x_1867_);
v___x_1869_ = lean_box(0);
if (v_isShared_1836_ == 0)
{
lean_ctor_set(v___x_1835_, 0, v___x_1869_);
v___x_1871_ = v___x_1835_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v___x_1869_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___boxed(lean_object* v_cls_1878_, lean_object* v_msg_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2(v_cls_1878_, v_msg_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_);
lean_dec(v___y_1883_);
lean_dec_ref(v___y_1882_);
lean_dec(v___y_1881_);
lean_dec_ref(v___y_1880_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Rewrites_rwLemma_spec__1(lean_object* v_x_1886_, lean_object* v_x_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_){
_start:
{
if (lean_obj_tag(v_x_1886_) == 0)
{
lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1893_ = l_List_reverse___redArg(v_x_1887_);
v___x_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1893_);
return v___x_1894_;
}
else
{
lean_object* v_head_1895_; lean_object* v_tail_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1914_; 
v_head_1895_ = lean_ctor_get(v_x_1886_, 0);
v_tail_1896_ = lean_ctor_get(v_x_1886_, 1);
v_isSharedCheck_1914_ = !lean_is_exclusive(v_x_1886_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1898_ = v_x_1886_;
v_isShared_1899_ = v_isSharedCheck_1914_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_tail_1896_);
lean_inc(v_head_1895_);
lean_dec(v_x_1886_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1914_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v___x_1900_; 
v___x_1900_ = l_Lean_MVarId_assumption(v_head_1895_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_);
if (lean_obj_tag(v___x_1900_) == 0)
{
lean_object* v_a_1901_; lean_object* v___x_1903_; 
v_a_1901_ = lean_ctor_get(v___x_1900_, 0);
lean_inc(v_a_1901_);
lean_dec_ref_known(v___x_1900_, 1);
if (v_isShared_1899_ == 0)
{
lean_ctor_set(v___x_1898_, 1, v_x_1887_);
lean_ctor_set(v___x_1898_, 0, v_a_1901_);
v___x_1903_ = v___x_1898_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_a_1901_);
lean_ctor_set(v_reuseFailAlloc_1905_, 1, v_x_1887_);
v___x_1903_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
v_x_1886_ = v_tail_1896_;
v_x_1887_ = v___x_1903_;
goto _start;
}
}
else
{
lean_object* v_a_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1913_; 
lean_del_object(v___x_1898_);
lean_dec(v_tail_1896_);
lean_dec(v_x_1887_);
v_a_1906_ = lean_ctor_get(v___x_1900_, 0);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1908_ = v___x_1900_;
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_dec(v___x_1900_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___x_1911_; 
if (v_isShared_1909_ == 0)
{
v___x_1911_ = v___x_1908_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_a_1906_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Rewrites_rwLemma_spec__1___boxed(lean_object* v_x_1915_, lean_object* v_x_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_){
_start:
{
lean_object* v_res_1922_; 
v_res_1922_ = l_List_mapM_loop___at___00Lean_Meta_Rewrites_rwLemma_spec__1(v_x_1915_, v_x_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_);
lean_dec(v___y_1920_);
lean_dec_ref(v___y_1919_);
lean_dec(v___y_1918_);
lean_dec_ref(v___y_1917_);
return v_res_1922_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5(void){
_start:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1935_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_));
v___x_1936_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__4));
v___x_1937_ = l_Lean_Name_append(v___x_1936_, v___x_1935_);
return v___x_1937_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__7(void){
_start:
{
lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1939_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__6));
v___x_1940_ = l_Lean_stringToMessageData(v___x_1939_);
return v___x_1940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0(lean_object* v_weight_1942_, lean_object* v_goal_1943_, lean_object* v_target_1944_, uint8_t v_symm_1945_, uint8_t v_side_1946_, lean_object* v_lem_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_){
_start:
{
lean_object* v___y_1954_; lean_object* v___y_1955_; lean_object* v___y_1956_; lean_object* v___y_1957_; uint8_t v___y_1958_; lean_object* v___y_1979_; lean_object* v___y_1980_; lean_object* v___y_1981_; lean_object* v___y_1982_; lean_object* v___y_1983_; lean_object* v_fst_1984_; uint8_t v_snd_1985_; lean_object* v___y_2010_; uint8_t v___y_2011_; lean_object* v___y_2012_; lean_object* v___y_2013_; lean_object* v___y_2014_; lean_object* v___y_2015_; lean_object* v___y_2032_; uint8_t v___y_2033_; uint8_t v_discharge_2034_; lean_object* v___y_2035_; lean_object* v___y_2036_; lean_object* v___y_2037_; lean_object* v___y_2038_; lean_object* v___y_2042_; uint8_t v___y_2043_; lean_object* v___y_2044_; lean_object* v___y_2045_; lean_object* v___y_2046_; lean_object* v___y_2047_; lean_object* v___y_2048_; lean_object* v___y_2049_; uint8_t v___y_2050_; uint8_t v___y_2051_; lean_object* v___y_2063_; uint8_t v___y_2064_; lean_object* v___y_2065_; lean_object* v___y_2066_; lean_object* v___y_2067_; lean_object* v___y_2068_; lean_object* v___y_2069_; lean_object* v___y_2070_; uint8_t v___y_2071_; uint8_t v___y_2072_; lean_object* v___y_2084_; lean_object* v___y_2164_; lean_object* v___y_2165_; lean_object* v___y_2166_; lean_object* v___y_2167_; lean_object* v_val_2182_; 
if (lean_obj_tag(v_lem_1947_) == 0)
{
lean_object* v_val_2193_; 
v_val_2193_ = lean_ctor_get(v_lem_1947_, 0);
lean_inc(v_val_2193_);
lean_dec_ref_known(v_lem_1947_, 1);
v_val_2182_ = v_val_2193_;
goto v___jp_2181_;
}
else
{
lean_object* v_val_2194_; lean_object* v___x_2195_; 
v_val_2194_ = lean_ctor_get(v_lem_1947_, 0);
lean_inc(v_val_2194_);
lean_dec_ref_known(v_lem_1947_, 1);
v___x_2195_ = l_Lean_Meta_saveState___redArg(v___y_1949_, v___y_1951_);
if (lean_obj_tag(v___x_2195_) == 0)
{
lean_object* v_a_2196_; lean_object* v___x_2197_; 
v_a_2196_ = lean_ctor_get(v___x_2195_, 0);
lean_inc(v_a_2196_);
lean_dec_ref_known(v___x_2195_, 1);
v___x_2197_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_val_2194_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_);
if (lean_obj_tag(v___x_2197_) == 0)
{
lean_object* v_a_2198_; 
lean_dec(v_a_2196_);
v_a_2198_ = lean_ctor_get(v___x_2197_, 0);
lean_inc(v_a_2198_);
lean_dec_ref_known(v___x_2197_, 1);
v_val_2182_ = v_a_2198_;
goto v___jp_2181_;
}
else
{
lean_object* v_a_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2228_; 
lean_dec_ref(v_target_1944_);
lean_dec(v_goal_1943_);
lean_dec(v_weight_1942_);
v_a_2199_ = lean_ctor_get(v___x_2197_, 0);
v_isSharedCheck_2228_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2201_ = v___x_2197_;
v_isShared_2202_ = v_isSharedCheck_2228_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_a_2199_);
lean_dec(v___x_2197_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2228_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
uint8_t v___y_2204_; uint8_t v___x_2226_; 
v___x_2226_ = l_Lean_Exception_isInterrupt(v_a_2199_);
if (v___x_2226_ == 0)
{
uint8_t v___x_2227_; 
lean_inc(v_a_2199_);
v___x_2227_ = l_Lean_Exception_isRuntime(v_a_2199_);
v___y_2204_ = v___x_2227_;
goto v___jp_2203_;
}
else
{
v___y_2204_ = v___x_2226_;
goto v___jp_2203_;
}
v___jp_2203_:
{
if (v___y_2204_ == 0)
{
lean_object* v___x_2205_; 
lean_del_object(v___x_2201_);
lean_dec(v_a_2199_);
v___x_2205_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2196_, v___y_1949_, v___y_1951_);
lean_dec(v_a_2196_);
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2213_; 
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2213_ == 0)
{
lean_object* v_unused_2214_; 
v_unused_2214_ = lean_ctor_get(v___x_2205_, 0);
lean_dec(v_unused_2214_);
v___x_2207_ = v___x_2205_;
v_isShared_2208_ = v_isSharedCheck_2213_;
goto v_resetjp_2206_;
}
else
{
lean_dec(v___x_2205_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2213_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2209_; lean_object* v___x_2211_; 
v___x_2209_ = lean_box(0);
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 0, v___x_2209_);
v___x_2211_ = v___x_2207_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v___x_2209_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
}
else
{
lean_object* v_a_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2222_; 
v_a_2215_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2217_ = v___x_2205_;
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_a_2215_);
lean_dec(v___x_2205_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___x_2220_; 
if (v_isShared_2218_ == 0)
{
v___x_2220_ = v___x_2217_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v_a_2215_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
}
}
}
}
else
{
lean_object* v___x_2224_; 
lean_dec(v_a_2196_);
if (v_isShared_2202_ == 0)
{
v___x_2224_ = v___x_2201_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v_a_2199_);
v___x_2224_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
return v___x_2224_;
}
}
}
}
}
}
else
{
lean_object* v_a_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2236_; 
lean_dec(v_val_2194_);
lean_dec_ref(v_target_1944_);
lean_dec(v_goal_1943_);
lean_dec(v_weight_1942_);
v_a_2229_ = lean_ctor_get(v___x_2195_, 0);
v_isSharedCheck_2236_ = !lean_is_exclusive(v___x_2195_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2231_ = v___x_2195_;
v_isShared_2232_ = v_isSharedCheck_2236_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_a_2229_);
lean_dec(v___x_2195_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2236_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v___x_2234_; 
if (v_isShared_2232_ == 0)
{
v___x_2234_ = v___x_2231_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v_a_2229_);
v___x_2234_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
return v___x_2234_;
}
}
}
}
v___jp_1953_:
{
if (v___y_1958_ == 0)
{
lean_object* v___x_1959_; 
lean_dec_ref(v___y_1955_);
v___x_1959_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1954_, v___y_1957_, v___y_1956_);
lean_dec_ref(v___y_1954_);
if (lean_obj_tag(v___x_1959_) == 0)
{
lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1967_; 
v_isSharedCheck_1967_ = !lean_is_exclusive(v___x_1959_);
if (v_isSharedCheck_1967_ == 0)
{
lean_object* v_unused_1968_; 
v_unused_1968_ = lean_ctor_get(v___x_1959_, 0);
lean_dec(v_unused_1968_);
v___x_1961_ = v___x_1959_;
v_isShared_1962_ = v_isSharedCheck_1967_;
goto v_resetjp_1960_;
}
else
{
lean_dec(v___x_1959_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1967_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1963_; lean_object* v___x_1965_; 
v___x_1963_ = lean_box(0);
if (v_isShared_1962_ == 0)
{
lean_ctor_set(v___x_1961_, 0, v___x_1963_);
v___x_1965_ = v___x_1961_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v___x_1963_);
v___x_1965_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
return v___x_1965_;
}
}
}
else
{
lean_object* v_a_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1976_; 
v_a_1969_ = lean_ctor_get(v___x_1959_, 0);
v_isSharedCheck_1976_ = !lean_is_exclusive(v___x_1959_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1971_ = v___x_1959_;
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_a_1969_);
lean_dec(v___x_1959_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1974_; 
if (v_isShared_1972_ == 0)
{
v___x_1974_ = v___x_1971_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v_a_1969_);
v___x_1974_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
return v___x_1974_;
}
}
}
}
else
{
lean_object* v___x_1977_; 
lean_dec_ref(v___y_1954_);
v___x_1977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1977_, 0, v___y_1955_);
return v___x_1977_;
}
}
v___jp_1978_:
{
lean_object* v___x_1986_; lean_object* v_mctx_1987_; lean_object* v_eNew_1988_; lean_object* v___x_1989_; 
v___x_1986_ = lean_st_ref_get(v___y_1983_);
v_mctx_1987_ = lean_ctor_get(v___x_1986_, 0);
lean_inc_ref_n(v_mctx_1987_, 2);
lean_dec(v___x_1986_);
v_eNew_1988_ = lean_ctor_get(v___y_1979_, 0);
lean_inc_ref(v_eNew_1988_);
v___x_1989_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(v_mctx_1987_, v_eNew_1988_, v___y_1982_, v___y_1983_, v___y_1980_, v___y_1981_);
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_object* v_a_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_2000_; 
v_a_1990_ = lean_ctor_get(v___x_1989_, 0);
v_isSharedCheck_2000_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1992_ = v___x_1989_;
v_isShared_1993_ = v_isSharedCheck_2000_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_a_1990_);
lean_dec(v___x_1989_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_2000_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1994_; uint8_t v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1998_; 
v___x_1994_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1994_, 0, v_fst_1984_);
lean_ctor_set(v___x_1994_, 1, v_weight_1942_);
lean_ctor_set(v___x_1994_, 2, v___y_1979_);
lean_ctor_set(v___x_1994_, 3, v_mctx_1987_);
lean_ctor_set_uint8(v___x_1994_, sizeof(void*)*4, v_snd_1985_);
v___x_1995_ = lean_unbox(v_a_1990_);
lean_dec(v_a_1990_);
lean_ctor_set_uint8(v___x_1994_, sizeof(void*)*4 + 1, v___x_1995_);
v___x_1996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1996_, 0, v___x_1994_);
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 0, v___x_1996_);
v___x_1998_ = v___x_1992_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v___x_1996_);
v___x_1998_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
return v___x_1998_;
}
}
}
else
{
lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2008_; 
lean_dec_ref(v_mctx_1987_);
lean_dec_ref(v_fst_1984_);
lean_dec_ref(v___y_1979_);
lean_dec(v_weight_1942_);
v_a_2001_ = lean_ctor_get(v___x_1989_, 0);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_2003_ = v___x_1989_;
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_dec(v___x_1989_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2006_; 
if (v_isShared_2004_ == 0)
{
v___x_2006_ = v___x_2003_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_a_2001_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
}
}
v___jp_2009_:
{
lean_object* v___x_2016_; 
v___x_2016_ = l_Lean_Meta_Rewrites_rewriteResultLemma(v___y_2010_);
if (lean_obj_tag(v___x_2016_) == 1)
{
lean_object* v_val_2017_; lean_object* v___x_2018_; lean_object* v_a_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; uint8_t v___x_2022_; 
v_val_2017_ = lean_ctor_get(v___x_2016_, 0);
lean_inc(v_val_2017_);
lean_dec_ref_known(v___x_2016_, 1);
v___x_2018_ = l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg(v_val_2017_, v___y_2013_);
v_a_2019_ = lean_ctor_get(v___x_2018_, 0);
lean_inc(v_a_2019_);
lean_dec_ref(v___x_2018_);
v___x_2020_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__1));
v___x_2021_ = lean_unsigned_to_nat(4u);
v___x_2022_ = l_Lean_Expr_isAppOfArity(v_a_2019_, v___x_2020_, v___x_2021_);
if (v___x_2022_ == 0)
{
v___y_1979_ = v___y_2010_;
v___y_1980_ = v___y_2014_;
v___y_1981_ = v___y_2015_;
v___y_1982_ = v___y_2012_;
v___y_1983_ = v___y_2013_;
v_fst_1984_ = v_a_2019_;
v_snd_1985_ = v___x_2022_;
goto v___jp_1978_;
}
else
{
lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; 
v___x_2023_ = lean_unsigned_to_nat(3u);
v___x_2024_ = l_Lean_Expr_getAppNumArgs(v_a_2019_);
v___x_2025_ = lean_nat_sub(v___x_2024_, v___x_2023_);
lean_dec(v___x_2024_);
v___x_2026_ = lean_unsigned_to_nat(1u);
v___x_2027_ = lean_nat_sub(v___x_2025_, v___x_2026_);
lean_dec(v___x_2025_);
v___x_2028_ = l_Lean_Expr_getRevArg_x21(v_a_2019_, v___x_2027_);
lean_dec(v_a_2019_);
v___y_1979_ = v___y_2010_;
v___y_1980_ = v___y_2014_;
v___y_1981_ = v___y_2015_;
v___y_1982_ = v___y_2012_;
v___y_1983_ = v___y_2013_;
v_fst_1984_ = v___x_2028_;
v_snd_1985_ = v___y_2011_;
goto v___jp_1978_;
}
}
else
{
lean_object* v___x_2029_; lean_object* v___x_2030_; 
lean_dec(v___x_2016_);
lean_dec_ref(v___y_2010_);
lean_dec(v_weight_1942_);
v___x_2029_ = lean_box(0);
v___x_2030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2029_);
return v___x_2030_;
}
}
v___jp_2031_:
{
if (v_discharge_2034_ == 0)
{
lean_object* v___x_2039_; lean_object* v___x_2040_; 
lean_dec_ref(v___y_2032_);
lean_dec(v_weight_1942_);
v___x_2039_ = lean_box(0);
v___x_2040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2040_, 0, v___x_2039_);
return v___x_2040_;
}
else
{
v___y_2010_ = v___y_2032_;
v___y_2011_ = v___y_2033_;
v___y_2012_ = v___y_2035_;
v___y_2013_ = v___y_2036_;
v___y_2014_ = v___y_2037_;
v___y_2015_ = v___y_2038_;
goto v___jp_2009_;
}
}
v___jp_2041_:
{
if (v___y_2051_ == 0)
{
lean_object* v___x_2052_; 
lean_dec_ref(v___y_2045_);
v___x_2052_ = l_Lean_Meta_SavedState_restore___redArg(v___y_2048_, v___y_2049_, v___y_2047_);
lean_dec_ref(v___y_2048_);
if (lean_obj_tag(v___x_2052_) == 0)
{
lean_dec_ref_known(v___x_2052_, 1);
v___y_2032_ = v___y_2042_;
v___y_2033_ = v___y_2043_;
v_discharge_2034_ = v___y_2050_;
v___y_2035_ = v___y_2044_;
v___y_2036_ = v___y_2049_;
v___y_2037_ = v___y_2046_;
v___y_2038_ = v___y_2047_;
goto v___jp_2031_;
}
else
{
lean_object* v_a_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2060_; 
lean_dec_ref(v___y_2042_);
lean_dec(v_weight_1942_);
v_a_2053_ = lean_ctor_get(v___x_2052_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2052_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2055_ = v___x_2052_;
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_a_2053_);
lean_dec(v___x_2052_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___x_2058_; 
if (v_isShared_2056_ == 0)
{
v___x_2058_ = v___x_2055_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_a_2053_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
}
}
else
{
lean_object* v___x_2061_; 
lean_dec_ref(v___y_2048_);
lean_dec_ref(v___y_2042_);
lean_dec(v_weight_1942_);
v___x_2061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2061_, 0, v___y_2045_);
return v___x_2061_;
}
}
v___jp_2062_:
{
if (v___y_2072_ == 0)
{
lean_object* v___x_2073_; 
lean_dec_ref(v___y_2067_);
v___x_2073_ = l_Lean_Meta_SavedState_restore___redArg(v___y_2069_, v___y_2070_, v___y_2068_);
lean_dec_ref(v___y_2069_);
if (lean_obj_tag(v___x_2073_) == 0)
{
lean_dec_ref_known(v___x_2073_, 1);
v___y_2032_ = v___y_2063_;
v___y_2033_ = v___y_2064_;
v_discharge_2034_ = v___y_2071_;
v___y_2035_ = v___y_2065_;
v___y_2036_ = v___y_2070_;
v___y_2037_ = v___y_2066_;
v___y_2038_ = v___y_2068_;
goto v___jp_2031_;
}
else
{
lean_object* v_a_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2081_; 
lean_dec_ref(v___y_2063_);
lean_dec(v_weight_1942_);
v_a_2074_ = lean_ctor_get(v___x_2073_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2073_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2076_ = v___x_2073_;
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_a_2074_);
lean_dec(v___x_2073_);
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
else
{
lean_object* v___x_2082_; 
lean_dec_ref(v___y_2069_);
lean_dec_ref(v___y_2063_);
lean_dec(v_weight_1942_);
v___x_2082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2082_, 0, v___y_2067_);
return v___x_2082_;
}
}
v___jp_2083_:
{
lean_object* v___x_2085_; 
v___x_2085_ = l_Lean_Meta_saveState___redArg(v___y_1949_, v___y_1951_);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_object* v_a_2086_; uint8_t v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; 
v_a_2086_ = lean_ctor_get(v___x_2085_, 0);
lean_inc(v_a_2086_);
lean_dec_ref_known(v___x_2085_, 1);
v___x_2087_ = 1;
v___x_2088_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__2));
lean_inc_ref(v___y_2084_);
v___x_2089_ = l_Lean_MVarId_rewrite(v_goal_1943_, v_target_1944_, v___y_2084_, v_symm_1945_, v___x_2088_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_);
if (lean_obj_tag(v___x_2089_) == 0)
{
lean_object* v_a_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2151_; 
lean_dec(v_a_2086_);
v_a_2090_ = lean_ctor_get(v___x_2089_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2092_ = v___x_2089_;
v_isShared_2093_ = v_isSharedCheck_2151_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_a_2090_);
lean_dec(v___x_2089_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2151_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v_eNew_2094_; lean_object* v_mvarIds_2095_; uint8_t v___x_2096_; 
v_eNew_2094_ = lean_ctor_get(v_a_2090_, 0);
v_mvarIds_2095_ = lean_ctor_get(v_a_2090_, 2);
v___x_2096_ = l_List_isEmpty___redArg(v_mvarIds_2095_);
if (v___x_2096_ == 0)
{
lean_del_object(v___x_2092_);
lean_dec_ref(v___y_2084_);
switch(v_side_1946_)
{
case 0:
{
v___y_2032_ = v_a_2090_;
v___y_2033_ = v___x_2087_;
v_discharge_2034_ = v___x_2096_;
v___y_2035_ = v___y_1948_;
v___y_2036_ = v___y_1949_;
v___y_2037_ = v___y_1950_;
v___y_2038_ = v___y_1951_;
goto v___jp_2031_;
}
case 1:
{
lean_object* v___x_2097_; 
v___x_2097_ = l_Lean_Meta_saveState___redArg(v___y_1949_, v___y_1951_);
if (lean_obj_tag(v___x_2097_) == 0)
{
lean_object* v_a_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; 
v_a_2098_ = lean_ctor_get(v___x_2097_, 0);
lean_inc(v_a_2098_);
lean_dec_ref_known(v___x_2097_, 1);
v___x_2099_ = lean_box(0);
lean_inc(v_mvarIds_2095_);
v___x_2100_ = l_List_mapM_loop___at___00Lean_Meta_Rewrites_rwLemma_spec__1(v_mvarIds_2095_, v___x_2099_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_);
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_dec_ref_known(v___x_2100_, 1);
lean_dec(v_a_2098_);
v___y_2010_ = v_a_2090_;
v___y_2011_ = v___x_2087_;
v___y_2012_ = v___y_1948_;
v___y_2013_ = v___y_1949_;
v___y_2014_ = v___y_1950_;
v___y_2015_ = v___y_1951_;
goto v___jp_2009_;
}
else
{
lean_object* v_a_2101_; uint8_t v___x_2102_; 
v_a_2101_ = lean_ctor_get(v___x_2100_, 0);
lean_inc(v_a_2101_);
lean_dec_ref_known(v___x_2100_, 1);
v___x_2102_ = l_Lean_Exception_isInterrupt(v_a_2101_);
if (v___x_2102_ == 0)
{
uint8_t v___x_2103_; 
lean_inc(v_a_2101_);
v___x_2103_ = l_Lean_Exception_isRuntime(v_a_2101_);
v___y_2063_ = v_a_2090_;
v___y_2064_ = v___x_2087_;
v___y_2065_ = v___y_1948_;
v___y_2066_ = v___y_1950_;
v___y_2067_ = v_a_2101_;
v___y_2068_ = v___y_1951_;
v___y_2069_ = v_a_2098_;
v___y_2070_ = v___y_1949_;
v___y_2071_ = v___x_2096_;
v___y_2072_ = v___x_2103_;
goto v___jp_2062_;
}
else
{
v___y_2063_ = v_a_2090_;
v___y_2064_ = v___x_2087_;
v___y_2065_ = v___y_1948_;
v___y_2066_ = v___y_1950_;
v___y_2067_ = v_a_2101_;
v___y_2068_ = v___y_1951_;
v___y_2069_ = v_a_2098_;
v___y_2070_ = v___y_1949_;
v___y_2071_ = v___x_2096_;
v___y_2072_ = v___x_2102_;
goto v___jp_2062_;
}
}
}
else
{
lean_object* v_a_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2111_; 
lean_dec(v_a_2090_);
lean_dec(v_weight_1942_);
v_a_2104_ = lean_ctor_get(v___x_2097_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2097_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2106_ = v___x_2097_;
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_a_2104_);
lean_dec(v___x_2097_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2109_; 
if (v_isShared_2107_ == 0)
{
v___x_2109_ = v___x_2106_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_a_2104_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
}
}
default: 
{
lean_object* v___x_2112_; 
v___x_2112_ = l_Lean_Meta_saveState___redArg(v___y_1949_, v___y_1951_);
if (lean_obj_tag(v___x_2112_) == 0)
{
lean_object* v_a_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; 
v_a_2113_ = lean_ctor_get(v___x_2112_, 0);
lean_inc(v_a_2113_);
lean_dec_ref_known(v___x_2112_, 1);
v___x_2114_ = lean_unsigned_to_nat(6u);
lean_inc(v_mvarIds_2095_);
v___x_2115_ = l_Lean_Meta_Rewrites_solveByElim(v_mvarIds_2095_, v___x_2114_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_);
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_dec_ref_known(v___x_2115_, 1);
lean_dec(v_a_2113_);
v___y_2010_ = v_a_2090_;
v___y_2011_ = v___x_2087_;
v___y_2012_ = v___y_1948_;
v___y_2013_ = v___y_1949_;
v___y_2014_ = v___y_1950_;
v___y_2015_ = v___y_1951_;
goto v___jp_2009_;
}
else
{
lean_object* v_a_2116_; uint8_t v___x_2117_; 
v_a_2116_ = lean_ctor_get(v___x_2115_, 0);
lean_inc(v_a_2116_);
lean_dec_ref_known(v___x_2115_, 1);
v___x_2117_ = l_Lean_Exception_isInterrupt(v_a_2116_);
if (v___x_2117_ == 0)
{
uint8_t v___x_2118_; 
lean_inc(v_a_2116_);
v___x_2118_ = l_Lean_Exception_isRuntime(v_a_2116_);
v___y_2042_ = v_a_2090_;
v___y_2043_ = v___x_2087_;
v___y_2044_ = v___y_1948_;
v___y_2045_ = v_a_2116_;
v___y_2046_ = v___y_1950_;
v___y_2047_ = v___y_1951_;
v___y_2048_ = v_a_2113_;
v___y_2049_ = v___y_1949_;
v___y_2050_ = v___x_2096_;
v___y_2051_ = v___x_2118_;
goto v___jp_2041_;
}
else
{
v___y_2042_ = v_a_2090_;
v___y_2043_ = v___x_2087_;
v___y_2044_ = v___y_1948_;
v___y_2045_ = v_a_2116_;
v___y_2046_ = v___y_1950_;
v___y_2047_ = v___y_1951_;
v___y_2048_ = v_a_2113_;
v___y_2049_ = v___y_1949_;
v___y_2050_ = v___x_2096_;
v___y_2051_ = v___x_2117_;
goto v___jp_2041_;
}
}
}
else
{
lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2126_; 
lean_dec(v_a_2090_);
lean_dec(v_weight_1942_);
v_a_2119_ = lean_ctor_get(v___x_2112_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2121_ = v___x_2112_;
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_2112_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2124_; 
if (v_isShared_2122_ == 0)
{
v___x_2124_ = v___x_2121_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_a_2119_);
v___x_2124_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
return v___x_2124_;
}
}
}
}
}
}
else
{
lean_object* v___x_2127_; lean_object* v_mctx_2128_; lean_object* v___x_2129_; 
v___x_2127_ = lean_st_ref_get(v___y_1949_);
v_mctx_2128_ = lean_ctor_get(v___x_2127_, 0);
lean_inc_ref_n(v_mctx_2128_, 2);
lean_dec(v___x_2127_);
lean_inc_ref(v_eNew_2094_);
v___x_2129_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(v_mctx_2128_, v_eNew_2094_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_);
if (lean_obj_tag(v___x_2129_) == 0)
{
lean_object* v_a_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2142_; 
v_a_2130_ = lean_ctor_get(v___x_2129_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_2129_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2132_ = v___x_2129_;
v_isShared_2133_ = v_isSharedCheck_2142_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_a_2130_);
lean_dec(v___x_2129_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2142_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2134_; uint8_t v___x_2135_; lean_object* v___x_2137_; 
v___x_2134_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2134_, 0, v___y_2084_);
lean_ctor_set(v___x_2134_, 1, v_weight_1942_);
lean_ctor_set(v___x_2134_, 2, v_a_2090_);
lean_ctor_set(v___x_2134_, 3, v_mctx_2128_);
lean_ctor_set_uint8(v___x_2134_, sizeof(void*)*4, v_symm_1945_);
v___x_2135_ = lean_unbox(v_a_2130_);
lean_dec(v_a_2130_);
lean_ctor_set_uint8(v___x_2134_, sizeof(void*)*4 + 1, v___x_2135_);
if (v_isShared_2093_ == 0)
{
lean_ctor_set_tag(v___x_2092_, 1);
lean_ctor_set(v___x_2092_, 0, v___x_2134_);
v___x_2137_ = v___x_2092_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v___x_2134_);
v___x_2137_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
lean_object* v___x_2139_; 
if (v_isShared_2133_ == 0)
{
lean_ctor_set(v___x_2132_, 0, v___x_2137_);
v___x_2139_ = v___x_2132_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v___x_2137_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
}
}
else
{
lean_object* v_a_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2150_; 
lean_dec_ref(v_mctx_2128_);
lean_del_object(v___x_2092_);
lean_dec(v_a_2090_);
lean_dec_ref(v___y_2084_);
lean_dec(v_weight_1942_);
v_a_2143_ = lean_ctor_get(v___x_2129_, 0);
v_isSharedCheck_2150_ = !lean_is_exclusive(v___x_2129_);
if (v_isSharedCheck_2150_ == 0)
{
v___x_2145_ = v___x_2129_;
v_isShared_2146_ = v_isSharedCheck_2150_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_a_2143_);
lean_dec(v___x_2129_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2150_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v___x_2148_; 
if (v_isShared_2146_ == 0)
{
v___x_2148_ = v___x_2145_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_a_2143_);
v___x_2148_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
return v___x_2148_;
}
}
}
}
}
}
else
{
lean_object* v_a_2152_; uint8_t v___x_2153_; 
lean_dec_ref(v___y_2084_);
lean_dec(v_weight_1942_);
v_a_2152_ = lean_ctor_get(v___x_2089_, 0);
lean_inc(v_a_2152_);
lean_dec_ref_known(v___x_2089_, 1);
v___x_2153_ = l_Lean_Exception_isInterrupt(v_a_2152_);
if (v___x_2153_ == 0)
{
uint8_t v___x_2154_; 
lean_inc(v_a_2152_);
v___x_2154_ = l_Lean_Exception_isRuntime(v_a_2152_);
v___y_1954_ = v_a_2086_;
v___y_1955_ = v_a_2152_;
v___y_1956_ = v___y_1951_;
v___y_1957_ = v___y_1949_;
v___y_1958_ = v___x_2154_;
goto v___jp_1953_;
}
else
{
v___y_1954_ = v_a_2086_;
v___y_1955_ = v_a_2152_;
v___y_1956_ = v___y_1951_;
v___y_1957_ = v___y_1949_;
v___y_1958_ = v___x_2153_;
goto v___jp_1953_;
}
}
}
else
{
lean_object* v_a_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2162_; 
lean_dec_ref(v___y_2084_);
lean_dec_ref(v_target_1944_);
lean_dec(v_goal_1943_);
lean_dec(v_weight_1942_);
v_a_2155_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2162_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2157_ = v___x_2085_;
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_a_2155_);
lean_dec(v___x_2085_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v___x_2160_; 
if (v_isShared_2158_ == 0)
{
v___x_2160_ = v___x_2157_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_a_2155_);
v___x_2160_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
return v___x_2160_;
}
}
}
}
v___jp_2163_:
{
lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
lean_inc_ref(v___y_2167_);
v___x_2168_ = l_Lean_stringToMessageData(v___y_2167_);
lean_inc_ref(v___y_2164_);
v___x_2169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2169_, 0, v___y_2164_);
lean_ctor_set(v___x_2169_, 1, v___x_2168_);
lean_inc_ref(v___y_2165_);
v___x_2170_ = l_Lean_MessageData_ofExpr(v___y_2165_);
v___x_2171_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2171_, 0, v___x_2169_);
lean_ctor_set(v___x_2171_, 1, v___x_2170_);
lean_inc(v___y_2166_);
v___x_2172_ = l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2(v___y_2166_, v___x_2171_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_);
if (lean_obj_tag(v___x_2172_) == 0)
{
lean_dec_ref_known(v___x_2172_, 1);
v___y_2084_ = v___y_2165_;
goto v___jp_2083_;
}
else
{
lean_object* v_a_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2180_; 
lean_dec_ref(v___y_2165_);
lean_dec_ref(v_target_1944_);
lean_dec(v_goal_1943_);
lean_dec(v_weight_1942_);
v_a_2173_ = lean_ctor_get(v___x_2172_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2172_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2175_ = v___x_2172_;
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_a_2173_);
lean_dec(v___x_2172_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2178_; 
if (v_isShared_2176_ == 0)
{
v___x_2178_ = v___x_2175_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v_a_2173_);
v___x_2178_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
return v___x_2178_;
}
}
}
}
v___jp_2181_:
{
lean_object* v_toCold_2183_; lean_object* v_options_2184_; uint8_t v_hasTrace_2185_; 
v_toCold_2183_ = lean_ctor_get(v___y_1950_, 0);
v_options_2184_ = lean_ctor_get(v_toCold_2183_, 2);
v_hasTrace_2185_ = lean_ctor_get_uint8(v_options_2184_, sizeof(void*)*1);
if (v_hasTrace_2185_ == 0)
{
v___y_2084_ = v_val_2182_;
goto v___jp_2083_;
}
else
{
lean_object* v_inheritedTraceOptions_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; uint8_t v___x_2189_; 
v_inheritedTraceOptions_2186_ = lean_ctor_get(v_toCold_2183_, 11);
v___x_2187_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_));
v___x_2188_ = lean_obj_once(&l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5, &l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5_once, _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5);
v___x_2189_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2186_, v_options_2184_, v___x_2188_);
if (v___x_2189_ == 0)
{
v___y_2084_ = v_val_2182_;
goto v___jp_2083_;
}
else
{
lean_object* v___x_2190_; 
v___x_2190_ = lean_obj_once(&l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__7, &l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__7_once, _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__7);
if (v_symm_1945_ == 0)
{
lean_object* v___x_2191_; 
v___x_2191_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__1));
v___y_2164_ = v___x_2190_;
v___y_2165_ = v_val_2182_;
v___y_2166_ = v___x_2187_;
v___y_2167_ = v___x_2191_;
goto v___jp_2163_;
}
else
{
lean_object* v___x_2192_; 
v___x_2192_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__8));
v___y_2164_ = v___x_2190_;
v___y_2165_ = v_val_2182_;
v___y_2166_ = v___x_2187_;
v___y_2167_ = v___x_2192_;
goto v___jp_2163_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0___boxed(lean_object* v_weight_2237_, lean_object* v_goal_2238_, lean_object* v_target_2239_, lean_object* v_symm_2240_, lean_object* v_side_2241_, lean_object* v_lem_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_){
_start:
{
uint8_t v_symm_boxed_2248_; uint8_t v_side_boxed_2249_; lean_object* v_res_2250_; 
v_symm_boxed_2248_ = lean_unbox(v_symm_2240_);
v_side_boxed_2249_ = lean_unbox(v_side_2241_);
v_res_2250_ = l_Lean_Meta_Rewrites_rwLemma___lam__0(v_weight_2237_, v_goal_2238_, v_target_2239_, v_symm_boxed_2248_, v_side_boxed_2249_, v_lem_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_);
lean_dec(v___y_2246_);
lean_dec_ref(v___y_2245_);
lean_dec(v___y_2244_);
lean_dec_ref(v___y_2243_);
return v_res_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma(lean_object* v_ctx_2251_, lean_object* v_goal_2252_, lean_object* v_target_2253_, uint8_t v_side_2254_, lean_object* v_lem_2255_, uint8_t v_symm_2256_, lean_object* v_weight_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_){
_start:
{
lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___f_2265_; lean_object* v___x_2266_; 
v___x_2263_ = lean_box(v_symm_2256_);
v___x_2264_ = lean_box(v_side_2254_);
v___f_2265_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___boxed), 11, 6);
lean_closure_set(v___f_2265_, 0, v_weight_2257_);
lean_closure_set(v___f_2265_, 1, v_goal_2252_);
lean_closure_set(v___f_2265_, 2, v_target_2253_);
lean_closure_set(v___f_2265_, 3, v___x_2263_);
lean_closure_set(v___f_2265_, 4, v___x_2264_);
lean_closure_set(v___f_2265_, 5, v_lem_2255_);
v___x_2266_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg(v_ctx_2251_, v___f_2265_, v_a_2258_, v_a_2259_, v_a_2260_, v_a_2261_);
return v___x_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___boxed(lean_object* v_ctx_2267_, lean_object* v_goal_2268_, lean_object* v_target_2269_, lean_object* v_side_2270_, lean_object* v_lem_2271_, lean_object* v_symm_2272_, lean_object* v_weight_2273_, lean_object* v_a_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_){
_start:
{
uint8_t v_side_boxed_2279_; uint8_t v_symm_boxed_2280_; lean_object* v_res_2281_; 
v_side_boxed_2279_ = lean_unbox(v_side_2270_);
v_symm_boxed_2280_ = lean_unbox(v_symm_2272_);
v_res_2281_ = l_Lean_Meta_Rewrites_rwLemma(v_ctx_2267_, v_goal_2268_, v_target_2269_, v_side_boxed_2279_, v_lem_2271_, v_symm_boxed_2280_, v_weight_2273_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_);
lean_dec(v_a_2277_);
lean_dec_ref(v_a_2276_);
lean_dec(v_a_2275_);
lean_dec_ref(v_a_2274_);
return v_res_2281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(lean_object* v_type_2282_, lean_object* v_k_2283_, uint8_t v_cleanupAnnotations_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_){
_start:
{
lean_object* v___f_2290_; uint8_t v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; 
v___f_2290_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2290_, 0, v_k_2283_);
v___x_2291_ = 0;
v___x_2292_ = lean_box(0);
v___x_2293_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_2291_, v___x_2292_, v_type_2282_, v___f_2290_, v_cleanupAnnotations_2284_, v___x_2291_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_);
if (lean_obj_tag(v___x_2293_) == 0)
{
lean_object* v_a_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2301_; 
v_a_2294_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2301_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2301_ == 0)
{
v___x_2296_ = v___x_2293_;
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_a_2294_);
lean_dec(v___x_2293_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2299_; 
if (v_isShared_2297_ == 0)
{
v___x_2299_ = v___x_2296_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v_a_2294_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
return v___x_2299_;
}
}
}
else
{
lean_object* v_a_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2309_; 
v_a_2302_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2309_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2304_ = v___x_2293_;
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_a_2302_);
lean_dec(v___x_2293_);
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
v_reuseFailAlloc_2308_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg___boxed(lean_object* v_type_2310_, lean_object* v_k_2311_, lean_object* v_cleanupAnnotations_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2318_; lean_object* v_res_2319_; 
v_cleanupAnnotations_boxed_2318_ = lean_unbox(v_cleanupAnnotations_2312_);
v_res_2319_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(v_type_2310_, v_k_2311_, v_cleanupAnnotations_boxed_2318_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
lean_dec(v___y_2316_);
lean_dec_ref(v___y_2315_);
lean_dec(v___y_2314_);
lean_dec_ref(v___y_2313_);
return v_res_2319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1(lean_object* v_00_u03b1_2320_, lean_object* v_type_2321_, lean_object* v_k_2322_, uint8_t v_cleanupAnnotations_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_){
_start:
{
lean_object* v___x_2329_; 
v___x_2329_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(v_type_2321_, v_k_2322_, v_cleanupAnnotations_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_);
return v___x_2329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___boxed(lean_object* v_00_u03b1_2330_, lean_object* v_type_2331_, lean_object* v_k_2332_, lean_object* v_cleanupAnnotations_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2339_; lean_object* v_res_2340_; 
v_cleanupAnnotations_boxed_2339_ = lean_unbox(v_cleanupAnnotations_2333_);
v_res_2340_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1(v_00_u03b1_2330_, v_type_2331_, v_k_2332_, v_cleanupAnnotations_boxed_2339_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_);
lean_dec(v___y_2337_);
lean_dec_ref(v___y_2336_);
lean_dec(v___y_2335_);
lean_dec_ref(v___y_2334_);
return v_res_2340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(lean_object* v_e_2341_, lean_object* v_k_2342_, uint8_t v_cleanupAnnotations_2343_, uint8_t v_preserveNondepLet_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_){
_start:
{
lean_object* v___f_2350_; uint8_t v___x_2351_; uint8_t v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; 
v___f_2350_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2350_, 0, v_k_2342_);
v___x_2351_ = 1;
v___x_2352_ = 0;
v___x_2353_ = lean_box(0);
v___x_2354_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2341_, v___x_2351_, v___x_2351_, v_preserveNondepLet_2344_, v___x_2352_, v___x_2353_, v___f_2350_, v_cleanupAnnotations_2343_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_);
if (lean_obj_tag(v___x_2354_) == 0)
{
lean_object* v_a_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2362_; 
v_a_2355_ = lean_ctor_get(v___x_2354_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___x_2354_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2357_ = v___x_2354_;
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_a_2355_);
lean_dec(v___x_2354_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2360_; 
if (v_isShared_2358_ == 0)
{
v___x_2360_ = v___x_2357_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_a_2355_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
else
{
lean_object* v_a_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2370_; 
v_a_2363_ = lean_ctor_get(v___x_2354_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2354_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2365_ = v___x_2354_;
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_a_2363_);
lean_dec(v___x_2354_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v___x_2368_; 
if (v_isShared_2366_ == 0)
{
v___x_2368_ = v___x_2365_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_a_2363_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
return v___x_2368_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg___boxed(lean_object* v_e_2371_, lean_object* v_k_2372_, lean_object* v_cleanupAnnotations_2373_, lean_object* v_preserveNondepLet_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2380_; uint8_t v_preserveNondepLet_boxed_2381_; lean_object* v_res_2382_; 
v_cleanupAnnotations_boxed_2380_ = lean_unbox(v_cleanupAnnotations_2373_);
v_preserveNondepLet_boxed_2381_ = lean_unbox(v_preserveNondepLet_2374_);
v_res_2382_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(v_e_2371_, v_k_2372_, v_cleanupAnnotations_boxed_2380_, v_preserveNondepLet_boxed_2381_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
return v_res_2382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2(lean_object* v_00_u03b1_2383_, lean_object* v_e_2384_, lean_object* v_k_2385_, uint8_t v_cleanupAnnotations_2386_, uint8_t v_preserveNondepLet_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_){
_start:
{
lean_object* v___x_2393_; 
v___x_2393_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(v_e_2384_, v_k_2385_, v_cleanupAnnotations_2386_, v_preserveNondepLet_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_);
return v___x_2393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___boxed(lean_object* v_00_u03b1_2394_, lean_object* v_e_2395_, lean_object* v_k_2396_, lean_object* v_cleanupAnnotations_2397_, lean_object* v_preserveNondepLet_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2404_; uint8_t v_preserveNondepLet_boxed_2405_; lean_object* v_res_2406_; 
v_cleanupAnnotations_boxed_2404_ = lean_unbox(v_cleanupAnnotations_2397_);
v_preserveNondepLet_boxed_2405_ = lean_unbox(v_preserveNondepLet_2398_);
v_res_2406_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2(v_00_u03b1_2394_, v_e_2395_, v_k_2396_, v_cleanupAnnotations_boxed_2404_, v_preserveNondepLet_boxed_2405_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_);
lean_dec(v___y_2402_);
lean_dec_ref(v___y_2401_);
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2399_);
return v_res_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(lean_object* v_f_2407_, lean_object* v_e_x27_2408_, lean_object* v_a_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_){
_start:
{
lean_object* v___x_2415_; 
lean_inc(v___y_2413_);
lean_inc_ref(v___y_2412_);
lean_inc(v___y_2411_);
lean_inc_ref(v___y_2410_);
lean_inc_ref(v_e_x27_2408_);
v___x_2415_ = lean_apply_7(v_f_2407_, v_a_2409_, v_e_x27_2408_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, lean_box(0));
if (lean_obj_tag(v___x_2415_) == 0)
{
lean_object* v_a_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2424_; 
v_a_2416_ = lean_ctor_get(v___x_2415_, 0);
v_isSharedCheck_2424_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2418_ = v___x_2415_;
v_isShared_2419_ = v_isSharedCheck_2424_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_a_2416_);
lean_dec(v___x_2415_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2424_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2420_; lean_object* v___x_2422_; 
v___x_2420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2420_, 0, v_e_x27_2408_);
lean_ctor_set(v___x_2420_, 1, v_a_2416_);
if (v_isShared_2419_ == 0)
{
lean_ctor_set(v___x_2418_, 0, v___x_2420_);
v___x_2422_ = v___x_2418_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v___x_2420_);
v___x_2422_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
return v___x_2422_;
}
}
}
else
{
lean_object* v_a_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2432_; 
lean_dec_ref(v_e_x27_2408_);
v_a_2425_ = lean_ctor_get(v___x_2415_, 0);
v_isSharedCheck_2432_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2427_ = v___x_2415_;
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_a_2425_);
lean_dec(v___x_2415_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___x_2430_; 
if (v_isShared_2428_ == 0)
{
v___x_2430_ = v___x_2427_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v_a_2425_);
v___x_2430_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
return v___x_2430_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0___boxed(lean_object* v_f_2433_, lean_object* v_e_x27_2434_, lean_object* v_a_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_){
_start:
{
lean_object* v_res_2441_; 
v_res_2441_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2433_, v_e_x27_2434_, v_a_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
lean_dec(v___y_2437_);
lean_dec_ref(v___y_2436_);
return v_res_2441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg(lean_object* v_f_2442_, lean_object* v_x_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_){
_start:
{
switch(lean_obj_tag(v_x_2443_))
{
case 7:
{
lean_object* v_binderName_2450_; lean_object* v_binderType_2451_; lean_object* v_body_2452_; uint8_t v_binderInfo_2453_; lean_object* v___x_2454_; 
v_binderName_2450_ = lean_ctor_get(v_x_2443_, 0);
v_binderType_2451_ = lean_ctor_get(v_x_2443_, 1);
v_body_2452_ = lean_ctor_get(v_x_2443_, 2);
v_binderInfo_2453_ = lean_ctor_get_uint8(v_x_2443_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2451_);
lean_inc_ref(v_f_2442_);
v___x_2454_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2442_, v_binderType_2451_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_object* v_a_2455_; lean_object* v_fst_2456_; lean_object* v_snd_2457_; lean_object* v___x_2458_; 
v_a_2455_ = lean_ctor_get(v___x_2454_, 0);
lean_inc(v_a_2455_);
lean_dec_ref_known(v___x_2454_, 1);
v_fst_2456_ = lean_ctor_get(v_a_2455_, 0);
lean_inc(v_fst_2456_);
v_snd_2457_ = lean_ctor_get(v_a_2455_, 1);
lean_inc(v_snd_2457_);
lean_dec(v_a_2455_);
lean_inc_ref(v_body_2452_);
v___x_2458_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2442_, v_body_2452_, v_snd_2457_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
if (lean_obj_tag(v___x_2458_) == 0)
{
lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2487_; 
v_a_2459_ = lean_ctor_get(v___x_2458_, 0);
v_isSharedCheck_2487_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2487_ == 0)
{
v___x_2461_ = v___x_2458_;
v_isShared_2462_ = v_isSharedCheck_2487_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_dec(v___x_2458_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2487_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v_fst_2463_; lean_object* v_snd_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2486_; 
v_fst_2463_ = lean_ctor_get(v_a_2459_, 0);
v_snd_2464_ = lean_ctor_get(v_a_2459_, 1);
v_isSharedCheck_2486_ = !lean_is_exclusive(v_a_2459_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2466_ = v_a_2459_;
v_isShared_2467_ = v_isSharedCheck_2486_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_snd_2464_);
lean_inc(v_fst_2463_);
lean_dec(v_a_2459_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2486_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___y_2469_; size_t v___x_2476_; size_t v___x_2477_; uint8_t v___x_2478_; 
v___x_2476_ = lean_ptr_addr(v_binderType_2451_);
v___x_2477_ = lean_ptr_addr(v_fst_2456_);
v___x_2478_ = lean_usize_dec_eq(v___x_2476_, v___x_2477_);
if (v___x_2478_ == 0)
{
lean_object* v___x_2479_; 
lean_inc(v_binderName_2450_);
lean_dec_ref_known(v_x_2443_, 3);
v___x_2479_ = l_Lean_Expr_forallE___override(v_binderName_2450_, v_fst_2456_, v_fst_2463_, v_binderInfo_2453_);
v___y_2469_ = v___x_2479_;
goto v___jp_2468_;
}
else
{
size_t v___x_2480_; size_t v___x_2481_; uint8_t v___x_2482_; 
v___x_2480_ = lean_ptr_addr(v_body_2452_);
v___x_2481_ = lean_ptr_addr(v_fst_2463_);
v___x_2482_ = lean_usize_dec_eq(v___x_2480_, v___x_2481_);
if (v___x_2482_ == 0)
{
lean_object* v___x_2483_; 
lean_inc(v_binderName_2450_);
lean_dec_ref_known(v_x_2443_, 3);
v___x_2483_ = l_Lean_Expr_forallE___override(v_binderName_2450_, v_fst_2456_, v_fst_2463_, v_binderInfo_2453_);
v___y_2469_ = v___x_2483_;
goto v___jp_2468_;
}
else
{
uint8_t v___x_2484_; 
v___x_2484_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2453_, v_binderInfo_2453_);
if (v___x_2484_ == 0)
{
lean_object* v___x_2485_; 
lean_inc(v_binderName_2450_);
lean_dec_ref_known(v_x_2443_, 3);
v___x_2485_ = l_Lean_Expr_forallE___override(v_binderName_2450_, v_fst_2456_, v_fst_2463_, v_binderInfo_2453_);
v___y_2469_ = v___x_2485_;
goto v___jp_2468_;
}
else
{
lean_dec(v_fst_2463_);
lean_dec(v_fst_2456_);
v___y_2469_ = v_x_2443_;
goto v___jp_2468_;
}
}
}
v___jp_2468_:
{
lean_object* v___x_2471_; 
if (v_isShared_2467_ == 0)
{
lean_ctor_set(v___x_2466_, 0, v___y_2469_);
v___x_2471_ = v___x_2466_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v___y_2469_);
lean_ctor_set(v_reuseFailAlloc_2475_, 1, v_snd_2464_);
v___x_2471_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
lean_object* v___x_2473_; 
if (v_isShared_2462_ == 0)
{
lean_ctor_set(v___x_2461_, 0, v___x_2471_);
v___x_2473_ = v___x_2461_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v___x_2471_);
v___x_2473_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
return v___x_2473_;
}
}
}
}
}
}
else
{
lean_dec(v_fst_2456_);
lean_dec_ref_known(v_x_2443_, 3);
return v___x_2458_;
}
}
else
{
lean_dec_ref_known(v_x_2443_, 3);
lean_dec_ref(v_f_2442_);
return v___x_2454_;
}
}
case 6:
{
lean_object* v_binderName_2488_; lean_object* v_binderType_2489_; lean_object* v_body_2490_; uint8_t v_binderInfo_2491_; lean_object* v___x_2492_; 
v_binderName_2488_ = lean_ctor_get(v_x_2443_, 0);
v_binderType_2489_ = lean_ctor_get(v_x_2443_, 1);
v_body_2490_ = lean_ctor_get(v_x_2443_, 2);
v_binderInfo_2491_ = lean_ctor_get_uint8(v_x_2443_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2489_);
lean_inc_ref(v_f_2442_);
v___x_2492_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2442_, v_binderType_2489_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
if (lean_obj_tag(v___x_2492_) == 0)
{
lean_object* v_a_2493_; lean_object* v_fst_2494_; lean_object* v_snd_2495_; lean_object* v___x_2496_; 
v_a_2493_ = lean_ctor_get(v___x_2492_, 0);
lean_inc(v_a_2493_);
lean_dec_ref_known(v___x_2492_, 1);
v_fst_2494_ = lean_ctor_get(v_a_2493_, 0);
lean_inc(v_fst_2494_);
v_snd_2495_ = lean_ctor_get(v_a_2493_, 1);
lean_inc(v_snd_2495_);
lean_dec(v_a_2493_);
lean_inc_ref(v_body_2490_);
v___x_2496_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2442_, v_body_2490_, v_snd_2495_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
if (lean_obj_tag(v___x_2496_) == 0)
{
lean_object* v_a_2497_; lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2525_; 
v_a_2497_ = lean_ctor_get(v___x_2496_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2496_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2499_ = v___x_2496_;
v_isShared_2500_ = v_isSharedCheck_2525_;
goto v_resetjp_2498_;
}
else
{
lean_inc(v_a_2497_);
lean_dec(v___x_2496_);
v___x_2499_ = lean_box(0);
v_isShared_2500_ = v_isSharedCheck_2525_;
goto v_resetjp_2498_;
}
v_resetjp_2498_:
{
lean_object* v_fst_2501_; lean_object* v_snd_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2524_; 
v_fst_2501_ = lean_ctor_get(v_a_2497_, 0);
v_snd_2502_ = lean_ctor_get(v_a_2497_, 1);
v_isSharedCheck_2524_ = !lean_is_exclusive(v_a_2497_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2504_ = v_a_2497_;
v_isShared_2505_ = v_isSharedCheck_2524_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_snd_2502_);
lean_inc(v_fst_2501_);
lean_dec(v_a_2497_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2524_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
lean_object* v___y_2507_; size_t v___x_2514_; size_t v___x_2515_; uint8_t v___x_2516_; 
v___x_2514_ = lean_ptr_addr(v_binderType_2489_);
v___x_2515_ = lean_ptr_addr(v_fst_2494_);
v___x_2516_ = lean_usize_dec_eq(v___x_2514_, v___x_2515_);
if (v___x_2516_ == 0)
{
lean_object* v___x_2517_; 
lean_inc(v_binderName_2488_);
lean_dec_ref_known(v_x_2443_, 3);
v___x_2517_ = l_Lean_Expr_lam___override(v_binderName_2488_, v_fst_2494_, v_fst_2501_, v_binderInfo_2491_);
v___y_2507_ = v___x_2517_;
goto v___jp_2506_;
}
else
{
size_t v___x_2518_; size_t v___x_2519_; uint8_t v___x_2520_; 
v___x_2518_ = lean_ptr_addr(v_body_2490_);
v___x_2519_ = lean_ptr_addr(v_fst_2501_);
v___x_2520_ = lean_usize_dec_eq(v___x_2518_, v___x_2519_);
if (v___x_2520_ == 0)
{
lean_object* v___x_2521_; 
lean_inc(v_binderName_2488_);
lean_dec_ref_known(v_x_2443_, 3);
v___x_2521_ = l_Lean_Expr_lam___override(v_binderName_2488_, v_fst_2494_, v_fst_2501_, v_binderInfo_2491_);
v___y_2507_ = v___x_2521_;
goto v___jp_2506_;
}
else
{
uint8_t v___x_2522_; 
v___x_2522_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2491_, v_binderInfo_2491_);
if (v___x_2522_ == 0)
{
lean_object* v___x_2523_; 
lean_inc(v_binderName_2488_);
lean_dec_ref_known(v_x_2443_, 3);
v___x_2523_ = l_Lean_Expr_lam___override(v_binderName_2488_, v_fst_2494_, v_fst_2501_, v_binderInfo_2491_);
v___y_2507_ = v___x_2523_;
goto v___jp_2506_;
}
else
{
lean_dec(v_fst_2501_);
lean_dec(v_fst_2494_);
v___y_2507_ = v_x_2443_;
goto v___jp_2506_;
}
}
}
v___jp_2506_:
{
lean_object* v___x_2509_; 
if (v_isShared_2505_ == 0)
{
lean_ctor_set(v___x_2504_, 0, v___y_2507_);
v___x_2509_ = v___x_2504_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v___y_2507_);
lean_ctor_set(v_reuseFailAlloc_2513_, 1, v_snd_2502_);
v___x_2509_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
lean_object* v___x_2511_; 
if (v_isShared_2500_ == 0)
{
lean_ctor_set(v___x_2499_, 0, v___x_2509_);
v___x_2511_ = v___x_2499_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v___x_2509_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
return v___x_2511_;
}
}
}
}
}
}
else
{
lean_dec(v_fst_2494_);
lean_dec_ref_known(v_x_2443_, 3);
return v___x_2496_;
}
}
else
{
lean_dec_ref_known(v_x_2443_, 3);
lean_dec_ref(v_f_2442_);
return v___x_2492_;
}
}
case 10:
{
lean_object* v_data_2526_; lean_object* v_expr_2527_; lean_object* v___x_2528_; 
v_data_2526_ = lean_ctor_get(v_x_2443_, 0);
v_expr_2527_ = lean_ctor_get(v_x_2443_, 1);
lean_inc_ref(v_expr_2527_);
v___x_2528_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2442_, v_expr_2527_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
if (lean_obj_tag(v___x_2528_) == 0)
{
lean_object* v_a_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2551_; 
v_a_2529_ = lean_ctor_get(v___x_2528_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2528_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2531_ = v___x_2528_;
v_isShared_2532_ = v_isSharedCheck_2551_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_a_2529_);
lean_dec(v___x_2528_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2551_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
lean_object* v_fst_2533_; lean_object* v_snd_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2550_; 
v_fst_2533_ = lean_ctor_get(v_a_2529_, 0);
v_snd_2534_ = lean_ctor_get(v_a_2529_, 1);
v_isSharedCheck_2550_ = !lean_is_exclusive(v_a_2529_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2536_ = v_a_2529_;
v_isShared_2537_ = v_isSharedCheck_2550_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_snd_2534_);
lean_inc(v_fst_2533_);
lean_dec(v_a_2529_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2550_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
lean_object* v___y_2539_; size_t v___x_2546_; size_t v___x_2547_; uint8_t v___x_2548_; 
v___x_2546_ = lean_ptr_addr(v_expr_2527_);
v___x_2547_ = lean_ptr_addr(v_fst_2533_);
v___x_2548_ = lean_usize_dec_eq(v___x_2546_, v___x_2547_);
if (v___x_2548_ == 0)
{
lean_object* v___x_2549_; 
lean_inc(v_data_2526_);
lean_dec_ref_known(v_x_2443_, 2);
v___x_2549_ = l_Lean_Expr_mdata___override(v_data_2526_, v_fst_2533_);
v___y_2539_ = v___x_2549_;
goto v___jp_2538_;
}
else
{
lean_dec(v_fst_2533_);
v___y_2539_ = v_x_2443_;
goto v___jp_2538_;
}
v___jp_2538_:
{
lean_object* v___x_2541_; 
if (v_isShared_2537_ == 0)
{
lean_ctor_set(v___x_2536_, 0, v___y_2539_);
v___x_2541_ = v___x_2536_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v___y_2539_);
lean_ctor_set(v_reuseFailAlloc_2545_, 1, v_snd_2534_);
v___x_2541_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
lean_object* v___x_2543_; 
if (v_isShared_2532_ == 0)
{
lean_ctor_set(v___x_2531_, 0, v___x_2541_);
v___x_2543_ = v___x_2531_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v___x_2541_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_x_2443_, 2);
return v___x_2528_;
}
}
case 8:
{
lean_object* v_declName_2552_; lean_object* v_type_2553_; lean_object* v_value_2554_; lean_object* v_body_2555_; uint8_t v_nondep_2556_; lean_object* v___x_2557_; 
v_declName_2552_ = lean_ctor_get(v_x_2443_, 0);
v_type_2553_ = lean_ctor_get(v_x_2443_, 1);
v_value_2554_ = lean_ctor_get(v_x_2443_, 2);
v_body_2555_ = lean_ctor_get(v_x_2443_, 3);
v_nondep_2556_ = lean_ctor_get_uint8(v_x_2443_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_2553_);
lean_inc_ref(v_f_2442_);
v___x_2557_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2442_, v_type_2553_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
if (lean_obj_tag(v___x_2557_) == 0)
{
lean_object* v_a_2558_; lean_object* v_fst_2559_; lean_object* v_snd_2560_; lean_object* v___x_2561_; 
v_a_2558_ = lean_ctor_get(v___x_2557_, 0);
lean_inc(v_a_2558_);
lean_dec_ref_known(v___x_2557_, 1);
v_fst_2559_ = lean_ctor_get(v_a_2558_, 0);
lean_inc(v_fst_2559_);
v_snd_2560_ = lean_ctor_get(v_a_2558_, 1);
lean_inc(v_snd_2560_);
lean_dec(v_a_2558_);
lean_inc_ref(v_value_2554_);
lean_inc_ref(v_f_2442_);
v___x_2561_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2442_, v_value_2554_, v_snd_2560_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
if (lean_obj_tag(v___x_2561_) == 0)
{
lean_object* v_a_2562_; lean_object* v_fst_2563_; lean_object* v_snd_2564_; lean_object* v___x_2565_; 
v_a_2562_ = lean_ctor_get(v___x_2561_, 0);
lean_inc(v_a_2562_);
lean_dec_ref_known(v___x_2561_, 1);
v_fst_2563_ = lean_ctor_get(v_a_2562_, 0);
lean_inc(v_fst_2563_);
v_snd_2564_ = lean_ctor_get(v_a_2562_, 1);
lean_inc(v_snd_2564_);
lean_dec(v_a_2562_);
lean_inc_ref(v_body_2555_);
v___x_2565_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2442_, v_body_2555_, v_snd_2564_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v_a_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2596_; 
v_a_2566_ = lean_ctor_get(v___x_2565_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2568_ = v___x_2565_;
v_isShared_2569_ = v_isSharedCheck_2596_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_a_2566_);
lean_dec(v___x_2565_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2596_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v_fst_2570_; lean_object* v_snd_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2595_; 
v_fst_2570_ = lean_ctor_get(v_a_2566_, 0);
v_snd_2571_ = lean_ctor_get(v_a_2566_, 1);
v_isSharedCheck_2595_ = !lean_is_exclusive(v_a_2566_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2573_ = v_a_2566_;
v_isShared_2574_ = v_isSharedCheck_2595_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_snd_2571_);
lean_inc(v_fst_2570_);
lean_dec(v_a_2566_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2595_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v___y_2576_; size_t v___x_2583_; size_t v___x_2584_; uint8_t v___x_2585_; 
v___x_2583_ = lean_ptr_addr(v_type_2553_);
v___x_2584_ = lean_ptr_addr(v_fst_2559_);
v___x_2585_ = lean_usize_dec_eq(v___x_2583_, v___x_2584_);
if (v___x_2585_ == 0)
{
lean_object* v___x_2586_; 
lean_inc(v_declName_2552_);
lean_dec_ref_known(v_x_2443_, 4);
v___x_2586_ = l_Lean_Expr_letE___override(v_declName_2552_, v_fst_2559_, v_fst_2563_, v_fst_2570_, v_nondep_2556_);
v___y_2576_ = v___x_2586_;
goto v___jp_2575_;
}
else
{
size_t v___x_2587_; size_t v___x_2588_; uint8_t v___x_2589_; 
v___x_2587_ = lean_ptr_addr(v_value_2554_);
v___x_2588_ = lean_ptr_addr(v_fst_2563_);
v___x_2589_ = lean_usize_dec_eq(v___x_2587_, v___x_2588_);
if (v___x_2589_ == 0)
{
lean_object* v___x_2590_; 
lean_inc(v_declName_2552_);
lean_dec_ref_known(v_x_2443_, 4);
v___x_2590_ = l_Lean_Expr_letE___override(v_declName_2552_, v_fst_2559_, v_fst_2563_, v_fst_2570_, v_nondep_2556_);
v___y_2576_ = v___x_2590_;
goto v___jp_2575_;
}
else
{
size_t v___x_2591_; size_t v___x_2592_; uint8_t v___x_2593_; 
v___x_2591_ = lean_ptr_addr(v_body_2555_);
v___x_2592_ = lean_ptr_addr(v_fst_2570_);
v___x_2593_ = lean_usize_dec_eq(v___x_2591_, v___x_2592_);
if (v___x_2593_ == 0)
{
lean_object* v___x_2594_; 
lean_inc(v_declName_2552_);
lean_dec_ref_known(v_x_2443_, 4);
v___x_2594_ = l_Lean_Expr_letE___override(v_declName_2552_, v_fst_2559_, v_fst_2563_, v_fst_2570_, v_nondep_2556_);
v___y_2576_ = v___x_2594_;
goto v___jp_2575_;
}
else
{
lean_dec(v_fst_2570_);
lean_dec(v_fst_2563_);
lean_dec(v_fst_2559_);
v___y_2576_ = v_x_2443_;
goto v___jp_2575_;
}
}
}
v___jp_2575_:
{
lean_object* v___x_2578_; 
if (v_isShared_2574_ == 0)
{
lean_ctor_set(v___x_2573_, 0, v___y_2576_);
v___x_2578_ = v___x_2573_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v___y_2576_);
lean_ctor_set(v_reuseFailAlloc_2582_, 1, v_snd_2571_);
v___x_2578_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
lean_object* v___x_2580_; 
if (v_isShared_2569_ == 0)
{
lean_ctor_set(v___x_2568_, 0, v___x_2578_);
v___x_2580_ = v___x_2568_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v___x_2578_);
v___x_2580_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
return v___x_2580_;
}
}
}
}
}
}
else
{
lean_dec(v_fst_2563_);
lean_dec(v_fst_2559_);
lean_dec_ref_known(v_x_2443_, 4);
return v___x_2565_;
}
}
else
{
lean_dec(v_fst_2559_);
lean_dec_ref_known(v_x_2443_, 4);
lean_dec_ref(v_f_2442_);
return v___x_2561_;
}
}
else
{
lean_dec_ref_known(v_x_2443_, 4);
lean_dec_ref(v_f_2442_);
return v___x_2557_;
}
}
case 5:
{
lean_object* v_fn_2597_; lean_object* v_arg_2598_; lean_object* v___x_2599_; 
v_fn_2597_ = lean_ctor_get(v_x_2443_, 0);
v_arg_2598_ = lean_ctor_get(v_x_2443_, 1);
lean_inc_ref(v_fn_2597_);
lean_inc_ref(v_f_2442_);
v___x_2599_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2442_, v_fn_2597_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
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
lean_inc_ref(v_arg_2598_);
v___x_2603_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2442_, v_arg_2598_, v_snd_2602_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
if (lean_obj_tag(v___x_2603_) == 0)
{
lean_object* v_a_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2630_; 
v_a_2604_ = lean_ctor_get(v___x_2603_, 0);
v_isSharedCheck_2630_ = !lean_is_exclusive(v___x_2603_);
if (v_isSharedCheck_2630_ == 0)
{
v___x_2606_ = v___x_2603_;
v_isShared_2607_ = v_isSharedCheck_2630_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_a_2604_);
lean_dec(v___x_2603_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2630_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v_fst_2608_; lean_object* v_snd_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2629_; 
v_fst_2608_ = lean_ctor_get(v_a_2604_, 0);
v_snd_2609_ = lean_ctor_get(v_a_2604_, 1);
v_isSharedCheck_2629_ = !lean_is_exclusive(v_a_2604_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2611_ = v_a_2604_;
v_isShared_2612_ = v_isSharedCheck_2629_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_snd_2609_);
lean_inc(v_fst_2608_);
lean_dec(v_a_2604_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2629_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___y_2614_; size_t v___x_2621_; size_t v___x_2622_; uint8_t v___x_2623_; 
v___x_2621_ = lean_ptr_addr(v_fn_2597_);
v___x_2622_ = lean_ptr_addr(v_fst_2601_);
v___x_2623_ = lean_usize_dec_eq(v___x_2621_, v___x_2622_);
if (v___x_2623_ == 0)
{
lean_object* v___x_2624_; 
lean_dec_ref_known(v_x_2443_, 2);
v___x_2624_ = l_Lean_Expr_app___override(v_fst_2601_, v_fst_2608_);
v___y_2614_ = v___x_2624_;
goto v___jp_2613_;
}
else
{
size_t v___x_2625_; size_t v___x_2626_; uint8_t v___x_2627_; 
v___x_2625_ = lean_ptr_addr(v_arg_2598_);
v___x_2626_ = lean_ptr_addr(v_fst_2608_);
v___x_2627_ = lean_usize_dec_eq(v___x_2625_, v___x_2626_);
if (v___x_2627_ == 0)
{
lean_object* v___x_2628_; 
lean_dec_ref_known(v_x_2443_, 2);
v___x_2628_ = l_Lean_Expr_app___override(v_fst_2601_, v_fst_2608_);
v___y_2614_ = v___x_2628_;
goto v___jp_2613_;
}
else
{
lean_dec(v_fst_2608_);
lean_dec(v_fst_2601_);
v___y_2614_ = v_x_2443_;
goto v___jp_2613_;
}
}
v___jp_2613_:
{
lean_object* v___x_2616_; 
if (v_isShared_2612_ == 0)
{
lean_ctor_set(v___x_2611_, 0, v___y_2614_);
v___x_2616_ = v___x_2611_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v___y_2614_);
lean_ctor_set(v_reuseFailAlloc_2620_, 1, v_snd_2609_);
v___x_2616_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
lean_object* v___x_2618_; 
if (v_isShared_2607_ == 0)
{
lean_ctor_set(v___x_2606_, 0, v___x_2616_);
v___x_2618_ = v___x_2606_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v___x_2616_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
}
}
}
}
else
{
lean_dec(v_fst_2601_);
lean_dec_ref_known(v_x_2443_, 2);
return v___x_2603_;
}
}
else
{
lean_dec_ref_known(v_x_2443_, 2);
lean_dec_ref(v_f_2442_);
return v___x_2599_;
}
}
case 11:
{
lean_object* v_typeName_2631_; lean_object* v_idx_2632_; lean_object* v_struct_2633_; lean_object* v___x_2634_; 
v_typeName_2631_ = lean_ctor_get(v_x_2443_, 0);
v_idx_2632_ = lean_ctor_get(v_x_2443_, 1);
v_struct_2633_ = lean_ctor_get(v_x_2443_, 2);
lean_inc_ref(v_struct_2633_);
v___x_2634_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2442_, v_struct_2633_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
if (lean_obj_tag(v___x_2634_) == 0)
{
lean_object* v_a_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2657_; 
v_a_2635_ = lean_ctor_get(v___x_2634_, 0);
v_isSharedCheck_2657_ = !lean_is_exclusive(v___x_2634_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2637_ = v___x_2634_;
v_isShared_2638_ = v_isSharedCheck_2657_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_a_2635_);
lean_dec(v___x_2634_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2657_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v_fst_2639_; lean_object* v_snd_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2656_; 
v_fst_2639_ = lean_ctor_get(v_a_2635_, 0);
v_snd_2640_ = lean_ctor_get(v_a_2635_, 1);
v_isSharedCheck_2656_ = !lean_is_exclusive(v_a_2635_);
if (v_isSharedCheck_2656_ == 0)
{
v___x_2642_ = v_a_2635_;
v_isShared_2643_ = v_isSharedCheck_2656_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_snd_2640_);
lean_inc(v_fst_2639_);
lean_dec(v_a_2635_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2656_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v___y_2645_; size_t v___x_2652_; size_t v___x_2653_; uint8_t v___x_2654_; 
v___x_2652_ = lean_ptr_addr(v_struct_2633_);
v___x_2653_ = lean_ptr_addr(v_fst_2639_);
v___x_2654_ = lean_usize_dec_eq(v___x_2652_, v___x_2653_);
if (v___x_2654_ == 0)
{
lean_object* v___x_2655_; 
lean_inc(v_idx_2632_);
lean_inc(v_typeName_2631_);
lean_dec_ref_known(v_x_2443_, 3);
v___x_2655_ = l_Lean_Expr_proj___override(v_typeName_2631_, v_idx_2632_, v_fst_2639_);
v___y_2645_ = v___x_2655_;
goto v___jp_2644_;
}
else
{
lean_dec(v_fst_2639_);
v___y_2645_ = v_x_2443_;
goto v___jp_2644_;
}
v___jp_2644_:
{
lean_object* v___x_2647_; 
if (v_isShared_2643_ == 0)
{
lean_ctor_set(v___x_2642_, 0, v___y_2645_);
v___x_2647_ = v___x_2642_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v___y_2645_);
lean_ctor_set(v_reuseFailAlloc_2651_, 1, v_snd_2640_);
v___x_2647_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
lean_object* v___x_2649_; 
if (v_isShared_2638_ == 0)
{
lean_ctor_set(v___x_2637_, 0, v___x_2647_);
v___x_2649_ = v___x_2637_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v___x_2647_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_x_2443_, 3);
return v___x_2634_;
}
}
default: 
{
lean_object* v___x_2658_; lean_object* v___x_2659_; 
lean_dec_ref(v_f_2442_);
v___x_2658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2658_, 0, v_x_2443_);
lean_ctor_set(v___x_2658_, 1, v___y_2444_);
v___x_2659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2659_, 0, v___x_2658_);
return v___x_2659_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___boxed(lean_object* v_f_2660_, lean_object* v_x_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_){
_start:
{
lean_object* v_res_2668_; 
v_res_2668_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg(v_f_2660_, v_x_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_);
lean_dec(v___y_2666_);
lean_dec_ref(v___y_2665_);
lean_dec(v___y_2664_);
lean_dec_ref(v___y_2663_);
return v_res_2668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg(lean_object* v_f_2669_, lean_object* v_init_2670_, lean_object* v_e_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_){
_start:
{
lean_object* v___x_2677_; 
v___x_2677_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg(v_f_2669_, v_e_2671_, v_init_2670_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_);
if (lean_obj_tag(v___x_2677_) == 0)
{
lean_object* v_a_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2686_; 
v_a_2678_ = lean_ctor_get(v___x_2677_, 0);
v_isSharedCheck_2686_ = !lean_is_exclusive(v___x_2677_);
if (v_isSharedCheck_2686_ == 0)
{
v___x_2680_ = v___x_2677_;
v_isShared_2681_ = v_isSharedCheck_2686_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_a_2678_);
lean_dec(v___x_2677_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2686_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v_snd_2682_; lean_object* v___x_2684_; 
v_snd_2682_ = lean_ctor_get(v_a_2678_, 1);
lean_inc(v_snd_2682_);
lean_dec(v_a_2678_);
if (v_isShared_2681_ == 0)
{
lean_ctor_set(v___x_2680_, 0, v_snd_2682_);
v___x_2684_ = v___x_2680_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v_snd_2682_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
return v___x_2684_;
}
}
}
else
{
lean_object* v_a_2687_; lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2694_; 
v_a_2687_ = lean_ctor_get(v___x_2677_, 0);
v_isSharedCheck_2694_ = !lean_is_exclusive(v___x_2677_);
if (v_isSharedCheck_2694_ == 0)
{
v___x_2689_ = v___x_2677_;
v_isShared_2690_ = v_isSharedCheck_2694_;
goto v_resetjp_2688_;
}
else
{
lean_inc(v_a_2687_);
lean_dec(v___x_2677_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2694_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
lean_object* v___x_2692_; 
if (v_isShared_2690_ == 0)
{
v___x_2692_ = v___x_2689_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v_a_2687_);
v___x_2692_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
return v___x_2692_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg___boxed(lean_object* v_f_2695_, lean_object* v_init_2696_, lean_object* v_e_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_){
_start:
{
lean_object* v_res_2703_; 
v_res_2703_ = l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg(v_f_2695_, v_init_2696_, v_e_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_);
lean_dec(v___y_2701_);
lean_dec_ref(v___y_2700_);
lean_dec(v___y_2699_);
lean_dec_ref(v___y_2698_);
return v_res_2703_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(lean_object* v_op_2706_, lean_object* v_as_2707_, size_t v_i_2708_, size_t v_stop_2709_, lean_object* v_b_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_){
_start:
{
lean_object* v_a_2717_; uint8_t v___x_2721_; 
v___x_2721_ = lean_usize_dec_eq(v_i_2708_, v_stop_2709_);
if (v___x_2721_ == 0)
{
lean_object* v___x_2722_; lean_object* v___x_2723_; 
v___x_2722_ = lean_array_uget_borrowed(v_as_2707_, v_i_2708_);
lean_inc(v___y_2714_);
lean_inc_ref(v___y_2713_);
lean_inc(v___y_2712_);
lean_inc_ref(v___y_2711_);
lean_inc(v___x_2722_);
v___x_2723_ = lean_infer_type(v___x_2722_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_);
if (lean_obj_tag(v___x_2723_) == 0)
{
lean_object* v_a_2724_; lean_object* v___x_2725_; 
v_a_2724_ = lean_ctor_get(v___x_2723_, 0);
lean_inc(v_a_2724_);
lean_dec_ref_known(v___x_2723_, 1);
lean_inc_ref(v_op_2706_);
v___x_2725_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v_op_2706_, v_a_2724_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_);
if (lean_obj_tag(v___x_2725_) == 0)
{
lean_object* v_a_2726_; lean_object* v___x_2727_; 
v_a_2726_ = lean_ctor_get(v___x_2725_, 0);
lean_inc(v_a_2726_);
lean_dec_ref_known(v___x_2725_, 1);
v___x_2727_ = l_Array_append___redArg(v_b_2710_, v_a_2726_);
lean_dec(v_a_2726_);
v_a_2717_ = v___x_2727_;
goto v___jp_2716_;
}
else
{
lean_dec_ref(v_b_2710_);
if (lean_obj_tag(v___x_2725_) == 0)
{
lean_object* v_a_2728_; 
v_a_2728_ = lean_ctor_get(v___x_2725_, 0);
lean_inc(v_a_2728_);
lean_dec_ref_known(v___x_2725_, 1);
v_a_2717_ = v_a_2728_;
goto v___jp_2716_;
}
else
{
lean_dec_ref(v_op_2706_);
return v___x_2725_;
}
}
}
else
{
lean_object* v_a_2729_; lean_object* v___x_2731_; uint8_t v_isShared_2732_; uint8_t v_isSharedCheck_2736_; 
lean_dec_ref(v_b_2710_);
lean_dec_ref(v_op_2706_);
v_a_2729_ = lean_ctor_get(v___x_2723_, 0);
v_isSharedCheck_2736_ = !lean_is_exclusive(v___x_2723_);
if (v_isSharedCheck_2736_ == 0)
{
v___x_2731_ = v___x_2723_;
v_isShared_2732_ = v_isSharedCheck_2736_;
goto v_resetjp_2730_;
}
else
{
lean_inc(v_a_2729_);
lean_dec(v___x_2723_);
v___x_2731_ = lean_box(0);
v_isShared_2732_ = v_isSharedCheck_2736_;
goto v_resetjp_2730_;
}
v_resetjp_2730_:
{
lean_object* v___x_2734_; 
if (v_isShared_2732_ == 0)
{
v___x_2734_ = v___x_2731_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v_a_2729_);
v___x_2734_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
return v___x_2734_;
}
}
}
}
else
{
lean_object* v___x_2737_; 
lean_dec_ref(v_op_2706_);
v___x_2737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2737_, 0, v_b_2710_);
return v___x_2737_;
}
v___jp_2716_:
{
size_t v___x_2718_; size_t v___x_2719_; 
v___x_2718_ = ((size_t)1ULL);
v___x_2719_ = lean_usize_add(v_i_2708_, v___x_2718_);
v_i_2708_ = v___x_2719_;
v_b_2710_ = v_a_2717_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0(lean_object* v_op_2738_, lean_object* v_args_2739_, lean_object* v_body_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_){
_start:
{
lean_object* v___x_2746_; 
lean_inc_ref(v_op_2738_);
v___x_2746_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v_op_2738_, v_body_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_);
if (lean_obj_tag(v___x_2746_) == 0)
{
lean_object* v_a_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2768_; 
v_a_2747_ = lean_ctor_get(v___x_2746_, 0);
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2749_ = v___x_2746_;
v_isShared_2750_ = v_isSharedCheck_2768_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_a_2747_);
lean_dec(v___x_2746_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2768_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; uint8_t v___x_2754_; 
v___x_2751_ = l_Array_reverse___redArg(v_a_2747_);
v___x_2752_ = lean_unsigned_to_nat(0u);
v___x_2753_ = lean_array_get_size(v_args_2739_);
v___x_2754_ = lean_nat_dec_lt(v___x_2752_, v___x_2753_);
if (v___x_2754_ == 0)
{
lean_object* v___x_2756_; 
lean_dec_ref(v_op_2738_);
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 0, v___x_2751_);
v___x_2756_ = v___x_2749_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v___x_2751_);
v___x_2756_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
return v___x_2756_;
}
}
else
{
uint8_t v___x_2758_; 
v___x_2758_ = lean_nat_dec_le(v___x_2753_, v___x_2753_);
if (v___x_2758_ == 0)
{
if (v___x_2754_ == 0)
{
lean_object* v___x_2760_; 
lean_dec_ref(v_op_2738_);
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 0, v___x_2751_);
v___x_2760_ = v___x_2749_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v___x_2751_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
return v___x_2760_;
}
}
else
{
size_t v___x_2762_; size_t v___x_2763_; lean_object* v___x_2764_; 
lean_del_object(v___x_2749_);
v___x_2762_ = ((size_t)0ULL);
v___x_2763_ = lean_usize_of_nat(v___x_2753_);
v___x_2764_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(v_op_2738_, v_args_2739_, v___x_2762_, v___x_2763_, v___x_2751_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_);
return v___x_2764_;
}
}
else
{
size_t v___x_2765_; size_t v___x_2766_; lean_object* v___x_2767_; 
lean_del_object(v___x_2749_);
v___x_2765_ = ((size_t)0ULL);
v___x_2766_ = lean_usize_of_nat(v___x_2753_);
v___x_2767_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(v_op_2738_, v_args_2739_, v___x_2765_, v___x_2766_, v___x_2751_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_);
return v___x_2767_;
}
}
}
}
else
{
lean_dec_ref(v_op_2738_);
return v___x_2746_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed(lean_object* v_op_2769_, lean_object* v_args_2770_, lean_object* v_body_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_){
_start:
{
lean_object* v_res_2777_; 
v_res_2777_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0(v_op_2769_, v_args_2770_, v_body_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_);
lean_dec(v___y_2775_);
lean_dec_ref(v___y_2774_);
lean_dec(v___y_2773_);
lean_dec_ref(v___y_2772_);
lean_dec_ref(v_args_2770_);
return v_res_2777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3___boxed(lean_object* v_op_2778_, lean_object* v_a_2779_, lean_object* v_f_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_){
_start:
{
lean_object* v_res_2786_; 
v_res_2786_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3(v_op_2778_, v_a_2779_, v_f_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_);
lean_dec(v___y_2784_);
lean_dec_ref(v___y_2783_);
lean_dec(v___y_2782_);
lean_dec_ref(v___y_2781_);
return v_res_2786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(lean_object* v_op_2787_, lean_object* v_e_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_){
_start:
{
switch(lean_obj_tag(v_e_2788_))
{
case 0:
{
lean_object* v___x_2794_; lean_object* v___x_2795_; 
lean_dec_ref_known(v_e_2788_, 1);
lean_dec_ref(v_op_2787_);
v___x_2794_ = ((lean_object*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___closed__0));
v___x_2795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2795_, 0, v___x_2794_);
return v___x_2795_;
}
case 7:
{
lean_object* v___f_2796_; uint8_t v___x_2797_; lean_object* v___x_2798_; 
v___f_2796_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2796_, 0, v_op_2787_);
v___x_2797_ = 0;
v___x_2798_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(v_e_2788_, v___f_2796_, v___x_2797_, v_a_2789_, v_a_2790_, v_a_2791_, v_a_2792_);
return v___x_2798_;
}
case 6:
{
lean_object* v___f_2799_; uint8_t v___x_2800_; uint8_t v___x_2801_; lean_object* v___x_2802_; 
v___f_2799_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2799_, 0, v_op_2787_);
v___x_2800_ = 0;
v___x_2801_ = 1;
v___x_2802_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(v_e_2788_, v___f_2799_, v___x_2800_, v___x_2801_, v_a_2789_, v_a_2790_, v_a_2791_, v_a_2792_);
return v___x_2802_;
}
case 8:
{
lean_object* v___f_2803_; uint8_t v___x_2804_; uint8_t v___x_2805_; lean_object* v___x_2806_; 
v___f_2803_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2803_, 0, v_op_2787_);
v___x_2804_ = 0;
v___x_2805_ = 1;
v___x_2806_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(v_e_2788_, v___f_2803_, v___x_2804_, v___x_2805_, v_a_2789_, v_a_2790_, v_a_2791_, v_a_2792_);
return v___x_2806_;
}
default: 
{
lean_object* v___x_2807_; 
lean_inc_ref(v_op_2787_);
lean_inc(v_a_2792_);
lean_inc_ref(v_a_2791_);
lean_inc(v_a_2790_);
lean_inc_ref(v_a_2789_);
lean_inc_ref(v_e_2788_);
v___x_2807_ = lean_apply_6(v_op_2787_, v_e_2788_, v_a_2789_, v_a_2790_, v_a_2791_, v_a_2792_, lean_box(0));
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_object* v_a_2808_; lean_object* v___f_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; 
v_a_2808_ = lean_ctor_get(v___x_2807_, 0);
lean_inc(v_a_2808_);
lean_dec_ref_known(v___x_2807_, 1);
v___f_2809_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3___boxed), 8, 1);
lean_closure_set(v___f_2809_, 0, v_op_2787_);
v___x_2810_ = l_Array_reverse___redArg(v_a_2808_);
v___x_2811_ = l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg(v___f_2809_, v___x_2810_, v_e_2788_, v_a_2789_, v_a_2790_, v_a_2791_, v_a_2792_);
return v___x_2811_;
}
else
{
lean_dec_ref(v_e_2788_);
lean_dec_ref(v_op_2787_);
return v___x_2807_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3(lean_object* v_op_2812_, lean_object* v_a_2813_, lean_object* v_f_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_){
_start:
{
lean_object* v___x_2820_; 
v___x_2820_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v_op_2812_, v_f_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_);
if (lean_obj_tag(v___x_2820_) == 0)
{
lean_object* v_a_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2829_; 
v_a_2821_ = lean_ctor_get(v___x_2820_, 0);
v_isSharedCheck_2829_ = !lean_is_exclusive(v___x_2820_);
if (v_isSharedCheck_2829_ == 0)
{
v___x_2823_ = v___x_2820_;
v_isShared_2824_ = v_isSharedCheck_2829_;
goto v_resetjp_2822_;
}
else
{
lean_inc(v_a_2821_);
lean_dec(v___x_2820_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2829_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
lean_object* v___x_2825_; lean_object* v___x_2827_; 
v___x_2825_ = l_Array_append___redArg(v_a_2813_, v_a_2821_);
lean_dec(v_a_2821_);
if (v_isShared_2824_ == 0)
{
lean_ctor_set(v___x_2823_, 0, v___x_2825_);
v___x_2827_ = v___x_2823_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v___x_2825_);
v___x_2827_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
return v___x_2827_;
}
}
}
else
{
lean_dec_ref(v_a_2813_);
return v___x_2820_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg___boxed(lean_object* v_op_2830_, lean_object* v_as_2831_, lean_object* v_i_2832_, lean_object* v_stop_2833_, lean_object* v_b_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_){
_start:
{
size_t v_i_boxed_2840_; size_t v_stop_boxed_2841_; lean_object* v_res_2842_; 
v_i_boxed_2840_ = lean_unbox_usize(v_i_2832_);
lean_dec(v_i_2832_);
v_stop_boxed_2841_ = lean_unbox_usize(v_stop_2833_);
lean_dec(v_stop_2833_);
v_res_2842_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(v_op_2830_, v_as_2831_, v_i_boxed_2840_, v_stop_boxed_2841_, v_b_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_);
lean_dec(v___y_2838_);
lean_dec_ref(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec_ref(v___y_2835_);
lean_dec_ref(v_as_2831_);
return v_res_2842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___boxed(lean_object* v_op_2843_, lean_object* v_e_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_){
_start:
{
lean_object* v_res_2850_; 
v_res_2850_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v_op_2843_, v_e_2844_, v_a_2845_, v_a_2846_, v_a_2847_, v_a_2848_);
lean_dec(v_a_2848_);
lean_dec_ref(v_a_2847_);
lean_dec(v_a_2846_);
lean_dec_ref(v_a_2845_);
return v_res_2850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches(lean_object* v_00_u03b1_2851_, lean_object* v_op_2852_, lean_object* v_e_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_){
_start:
{
lean_object* v___x_2859_; 
v___x_2859_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v_op_2852_, v_e_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_);
return v___x_2859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___boxed(lean_object* v_00_u03b1_2860_, lean_object* v_op_2861_, lean_object* v_e_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_){
_start:
{
lean_object* v_res_2868_; 
v_res_2868_ = l_Lean_Meta_Rewrites_getSubexpressionMatches(v_00_u03b1_2860_, v_op_2861_, v_e_2862_, v_a_2863_, v_a_2864_, v_a_2865_, v_a_2866_);
lean_dec(v_a_2866_);
lean_dec_ref(v_a_2865_);
lean_dec(v_a_2864_);
lean_dec_ref(v_a_2863_);
return v_res_2868_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0(lean_object* v_00_u03b1_2869_, lean_object* v_op_2870_, lean_object* v_as_2871_, size_t v_i_2872_, size_t v_stop_2873_, lean_object* v_b_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_){
_start:
{
lean_object* v___x_2880_; 
v___x_2880_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(v_op_2870_, v_as_2871_, v_i_2872_, v_stop_2873_, v_b_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_);
return v___x_2880_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___boxed(lean_object* v_00_u03b1_2881_, lean_object* v_op_2882_, lean_object* v_as_2883_, lean_object* v_i_2884_, lean_object* v_stop_2885_, lean_object* v_b_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_){
_start:
{
size_t v_i_boxed_2892_; size_t v_stop_boxed_2893_; lean_object* v_res_2894_; 
v_i_boxed_2892_ = lean_unbox_usize(v_i_2884_);
lean_dec(v_i_2884_);
v_stop_boxed_2893_ = lean_unbox_usize(v_stop_2885_);
lean_dec(v_stop_2885_);
v_res_2894_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0(v_00_u03b1_2881_, v_op_2882_, v_as_2883_, v_i_boxed_2892_, v_stop_boxed_2893_, v_b_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
lean_dec(v___y_2890_);
lean_dec_ref(v___y_2889_);
lean_dec(v___y_2888_);
lean_dec_ref(v___y_2887_);
lean_dec_ref(v_as_2883_);
return v_res_2894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3(lean_object* v_00_u03b1_2895_, lean_object* v_f_2896_, lean_object* v_x_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_){
_start:
{
lean_object* v___x_2904_; 
v___x_2904_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg(v_f_2896_, v_x_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_);
return v___x_2904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___boxed(lean_object* v_00_u03b1_2905_, lean_object* v_f_2906_, lean_object* v_x_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_){
_start:
{
lean_object* v_res_2914_; 
v_res_2914_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3(v_00_u03b1_2905_, v_f_2906_, v_x_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_);
lean_dec(v___y_2912_);
lean_dec_ref(v___y_2911_);
lean_dec(v___y_2910_);
lean_dec_ref(v___y_2909_);
return v_res_2914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3(lean_object* v_00_u03b1_2915_, lean_object* v_f_2916_, lean_object* v_init_2917_, lean_object* v_e_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_){
_start:
{
lean_object* v___x_2924_; 
v___x_2924_ = l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg(v_f_2916_, v_init_2917_, v_e_2918_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_);
return v___x_2924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___boxed(lean_object* v_00_u03b1_2925_, lean_object* v_f_2926_, lean_object* v_init_2927_, lean_object* v_e_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_){
_start:
{
lean_object* v_res_2934_; 
v_res_2934_ = l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3(v_00_u03b1_2925_, v_f_2926_, v_init_2927_, v_e_2928_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_);
lean_dec(v___y_2932_);
lean_dec_ref(v___y_2931_);
lean_dec(v___y_2930_);
lean_dec_ref(v___y_2929_);
return v_res_2934_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__3(size_t v_sz_2935_, size_t v_i_2936_, lean_object* v_bs_2937_){
_start:
{
uint8_t v___x_2938_; 
v___x_2938_ = lean_usize_dec_lt(v_i_2936_, v_sz_2935_);
if (v___x_2938_ == 0)
{
return v_bs_2937_;
}
else
{
lean_object* v_v_2939_; lean_object* v_fst_2940_; lean_object* v_snd_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2955_; 
v_v_2939_ = lean_array_uget(v_bs_2937_, v_i_2936_);
v_fst_2940_ = lean_ctor_get(v_v_2939_, 0);
v_snd_2941_ = lean_ctor_get(v_v_2939_, 1);
v_isSharedCheck_2955_ = !lean_is_exclusive(v_v_2939_);
if (v_isSharedCheck_2955_ == 0)
{
v___x_2943_ = v_v_2939_;
v_isShared_2944_ = v_isSharedCheck_2955_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_snd_2941_);
lean_inc(v_fst_2940_);
lean_dec(v_v_2939_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2955_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v___x_2945_; lean_object* v_bs_x27_2946_; lean_object* v___x_2947_; lean_object* v___x_2949_; 
v___x_2945_ = lean_unsigned_to_nat(0u);
v_bs_x27_2946_ = lean_array_uset(v_bs_2937_, v_i_2936_, v___x_2945_);
v___x_2947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2947_, 0, v_fst_2940_);
if (v_isShared_2944_ == 0)
{
lean_ctor_set(v___x_2943_, 0, v___x_2947_);
v___x_2949_ = v___x_2943_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v___x_2947_);
lean_ctor_set(v_reuseFailAlloc_2954_, 1, v_snd_2941_);
v___x_2949_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
size_t v___x_2950_; size_t v___x_2951_; lean_object* v___x_2952_; 
v___x_2950_ = ((size_t)1ULL);
v___x_2951_ = lean_usize_add(v_i_2936_, v___x_2950_);
v___x_2952_ = lean_array_uset(v_bs_x27_2946_, v_i_2936_, v___x_2949_);
v_i_2936_ = v___x_2951_;
v_bs_2937_ = v___x_2952_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__3___boxed(lean_object* v_sz_2956_, lean_object* v_i_2957_, lean_object* v_bs_2958_){
_start:
{
size_t v_sz_boxed_2959_; size_t v_i_boxed_2960_; lean_object* v_res_2961_; 
v_sz_boxed_2959_ = lean_unbox_usize(v_sz_2956_);
lean_dec(v_sz_2956_);
v_i_boxed_2960_ = lean_unbox_usize(v_i_2957_);
lean_dec(v_i_2957_);
v_res_2961_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__3(v_sz_boxed_2959_, v_i_boxed_2960_, v_bs_2958_);
return v_res_2961_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0___redArg(lean_object* v_xs_2962_, lean_object* v_j_2963_){
_start:
{
lean_object* v_zero_2964_; uint8_t v_isZero_2965_; 
v_zero_2964_ = lean_unsigned_to_nat(0u);
v_isZero_2965_ = lean_nat_dec_eq(v_j_2963_, v_zero_2964_);
if (v_isZero_2965_ == 1)
{
lean_dec(v_j_2963_);
return v_xs_2962_;
}
else
{
lean_object* v___x_2966_; lean_object* v_snd_2967_; lean_object* v_snd_2968_; lean_object* v_one_2969_; lean_object* v_n_2970_; lean_object* v___x_2971_; lean_object* v_snd_2972_; lean_object* v_snd_2973_; uint8_t v___x_2974_; 
v___x_2966_ = lean_array_fget_borrowed(v_xs_2962_, v_j_2963_);
v_snd_2967_ = lean_ctor_get(v___x_2966_, 1);
v_snd_2968_ = lean_ctor_get(v_snd_2967_, 1);
v_one_2969_ = lean_unsigned_to_nat(1u);
v_n_2970_ = lean_nat_sub(v_j_2963_, v_one_2969_);
v___x_2971_ = lean_array_fget_borrowed(v_xs_2962_, v_n_2970_);
v_snd_2972_ = lean_ctor_get(v___x_2971_, 1);
v_snd_2973_ = lean_ctor_get(v_snd_2972_, 1);
v___x_2974_ = lean_nat_dec_lt(v_snd_2973_, v_snd_2968_);
if (v___x_2974_ == 0)
{
lean_dec(v_n_2970_);
lean_dec(v_j_2963_);
return v_xs_2962_;
}
else
{
lean_object* v___x_2975_; 
v___x_2975_ = lean_array_fswap(v_xs_2962_, v_j_2963_, v_n_2970_);
lean_dec(v_j_2963_);
v_xs_2962_ = v___x_2975_;
v_j_2963_ = v_n_2970_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0(lean_object* v_xs_2977_, lean_object* v_i_2978_, lean_object* v_fuel_2979_){
_start:
{
lean_object* v_zero_2980_; uint8_t v_isZero_2981_; 
v_zero_2980_ = lean_unsigned_to_nat(0u);
v_isZero_2981_ = lean_nat_dec_eq(v_fuel_2979_, v_zero_2980_);
if (v_isZero_2981_ == 1)
{
lean_dec(v_fuel_2979_);
lean_dec(v_i_2978_);
return v_xs_2977_;
}
else
{
lean_object* v___x_2982_; uint8_t v___x_2983_; 
v___x_2982_ = lean_array_get_size(v_xs_2977_);
v___x_2983_ = lean_nat_dec_lt(v_i_2978_, v___x_2982_);
if (v___x_2983_ == 0)
{
lean_dec(v_fuel_2979_);
lean_dec(v_i_2978_);
return v_xs_2977_;
}
else
{
lean_object* v_one_2984_; lean_object* v_n_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; 
v_one_2984_ = lean_unsigned_to_nat(1u);
v_n_2985_ = lean_nat_sub(v_fuel_2979_, v_one_2984_);
lean_dec(v_fuel_2979_);
lean_inc(v_i_2978_);
v___x_2986_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0___redArg(v_xs_2977_, v_i_2978_);
v___x_2987_ = lean_nat_add(v_i_2978_, v_one_2984_);
lean_dec(v_i_2978_);
v_xs_2977_ = v___x_2986_;
v_i_2978_ = v___x_2987_;
v_fuel_2979_ = v_n_2985_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__2(size_t v_sz_2989_, size_t v_i_2990_, lean_object* v_bs_2991_){
_start:
{
uint8_t v___x_2992_; 
v___x_2992_ = lean_usize_dec_lt(v_i_2990_, v_sz_2989_);
if (v___x_2992_ == 0)
{
return v_bs_2991_;
}
else
{
lean_object* v_v_2993_; lean_object* v_fst_2994_; lean_object* v_snd_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3009_; 
v_v_2993_ = lean_array_uget(v_bs_2991_, v_i_2990_);
v_fst_2994_ = lean_ctor_get(v_v_2993_, 0);
v_snd_2995_ = lean_ctor_get(v_v_2993_, 1);
v_isSharedCheck_3009_ = !lean_is_exclusive(v_v_2993_);
if (v_isSharedCheck_3009_ == 0)
{
v___x_2997_ = v_v_2993_;
v_isShared_2998_ = v_isSharedCheck_3009_;
goto v_resetjp_2996_;
}
else
{
lean_inc(v_snd_2995_);
lean_inc(v_fst_2994_);
lean_dec(v_v_2993_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3009_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
lean_object* v___x_2999_; lean_object* v_bs_x27_3000_; lean_object* v___x_3001_; lean_object* v___x_3003_; 
v___x_2999_ = lean_unsigned_to_nat(0u);
v_bs_x27_3000_ = lean_array_uset(v_bs_2991_, v_i_2990_, v___x_2999_);
v___x_3001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3001_, 0, v_fst_2994_);
if (v_isShared_2998_ == 0)
{
lean_ctor_set(v___x_2997_, 0, v___x_3001_);
v___x_3003_ = v___x_2997_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v___x_3001_);
lean_ctor_set(v_reuseFailAlloc_3008_, 1, v_snd_2995_);
v___x_3003_ = v_reuseFailAlloc_3008_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
size_t v___x_3004_; size_t v___x_3005_; lean_object* v___x_3006_; 
v___x_3004_ = ((size_t)1ULL);
v___x_3005_ = lean_usize_add(v_i_2990_, v___x_3004_);
v___x_3006_ = lean_array_uset(v_bs_x27_3000_, v_i_2990_, v___x_3003_);
v_i_2990_ = v___x_3005_;
v_bs_2991_ = v___x_3006_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__2___boxed(lean_object* v_sz_3010_, lean_object* v_i_3011_, lean_object* v_bs_3012_){
_start:
{
size_t v_sz_boxed_3013_; size_t v_i_boxed_3014_; lean_object* v_res_3015_; 
v_sz_boxed_3013_ = lean_unbox_usize(v_sz_3010_);
lean_dec(v_sz_3010_);
v_i_boxed_3014_ = lean_unbox_usize(v_i_3011_);
lean_dec(v_i_3011_);
v_res_3015_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__2(v_sz_boxed_3013_, v_i_boxed_3014_, v_bs_3012_);
return v_res_3015_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg(lean_object* v_forbidden_3016_, lean_object* v_as_3017_, size_t v_sz_3018_, size_t v_i_3019_, lean_object* v_b_3020_){
_start:
{
lean_object* v_a_3023_; uint8_t v___x_3027_; 
v___x_3027_ = lean_usize_dec_lt(v_i_3019_, v_sz_3018_);
if (v___x_3027_ == 0)
{
lean_object* v___x_3028_; 
v___x_3028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3028_, 0, v_b_3020_);
return v___x_3028_;
}
else
{
lean_object* v_a_3029_; lean_object* v_snd_3030_; lean_object* v_snd_3031_; lean_object* v_fst_3032_; lean_object* v_fst_3033_; lean_object* v___x_3035_; uint8_t v_isShared_3036_; uint8_t v_isSharedCheck_3091_; 
v_a_3029_ = lean_array_uget(v_as_3017_, v_i_3019_);
v_snd_3030_ = lean_ctor_get(v_a_3029_, 1);
lean_inc(v_snd_3030_);
v_snd_3031_ = lean_ctor_get(v_b_3020_, 1);
lean_inc(v_snd_3031_);
v_fst_3032_ = lean_ctor_get(v_a_3029_, 0);
v_fst_3033_ = lean_ctor_get(v_snd_3030_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v_snd_3030_);
if (v_isSharedCheck_3091_ == 0)
{
lean_object* v_unused_3092_; 
v_unused_3092_ = lean_ctor_get(v_snd_3030_, 1);
lean_dec(v_unused_3092_);
v___x_3035_ = v_snd_3030_;
v_isShared_3036_ = v_isSharedCheck_3091_;
goto v_resetjp_3034_;
}
else
{
lean_inc(v_fst_3033_);
lean_dec(v_snd_3030_);
v___x_3035_ = lean_box(0);
v_isShared_3036_ = v_isSharedCheck_3091_;
goto v_resetjp_3034_;
}
v_resetjp_3034_:
{
lean_object* v_fst_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3089_; 
v_fst_3037_ = lean_ctor_get(v_b_3020_, 0);
v_isSharedCheck_3089_ = !lean_is_exclusive(v_b_3020_);
if (v_isSharedCheck_3089_ == 0)
{
lean_object* v_unused_3090_; 
v_unused_3090_ = lean_ctor_get(v_b_3020_, 1);
lean_dec(v_unused_3090_);
v___x_3039_ = v_b_3020_;
v_isShared_3040_ = v_isSharedCheck_3089_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_fst_3037_);
lean_dec(v_b_3020_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3089_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v_fst_3041_; lean_object* v_snd_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3088_; 
v_fst_3041_ = lean_ctor_get(v_snd_3031_, 0);
v_snd_3042_ = lean_ctor_get(v_snd_3031_, 1);
v_isSharedCheck_3088_ = !lean_is_exclusive(v_snd_3031_);
if (v_isSharedCheck_3088_ == 0)
{
v___x_3044_ = v_snd_3031_;
v_isShared_3045_ = v_isSharedCheck_3088_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_snd_3042_);
lean_inc(v_fst_3041_);
lean_dec(v_snd_3031_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3088_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
uint8_t v___x_3060_; 
v___x_3060_ = l_Lean_NameSet_contains(v_forbidden_3016_, v_fst_3032_);
if (v___x_3060_ == 0)
{
uint8_t v___x_3061_; 
v___x_3061_ = lean_unbox(v_fst_3033_);
lean_dec(v_fst_3033_);
if (v___x_3061_ == 0)
{
uint8_t v___x_3062_; 
lean_inc(v_fst_3032_);
lean_del_object(v___x_3044_);
lean_del_object(v___x_3039_);
v___x_3062_ = l_Lean_NameSet_contains(v_fst_3037_, v_fst_3032_);
if (v___x_3062_ == 0)
{
if (v___x_3027_ == 0)
{
lean_dec(v_fst_3032_);
lean_dec(v_a_3029_);
goto v___jp_3055_;
}
else
{
lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; 
lean_del_object(v___x_3035_);
v___x_3063_ = lean_array_push(v_snd_3042_, v_a_3029_);
v___x_3064_ = l_Lean_NameSet_insert(v_fst_3037_, v_fst_3032_);
v___x_3065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3065_, 0, v_fst_3041_);
lean_ctor_set(v___x_3065_, 1, v___x_3063_);
v___x_3066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3066_, 0, v___x_3064_);
lean_ctor_set(v___x_3066_, 1, v___x_3065_);
v_a_3023_ = v___x_3066_;
goto v___jp_3022_;
}
}
else
{
lean_dec(v_fst_3032_);
lean_dec(v_a_3029_);
goto v___jp_3055_;
}
}
else
{
uint8_t v___x_3067_; 
lean_del_object(v___x_3035_);
v___x_3067_ = l_Lean_NameSet_contains(v_fst_3041_, v_fst_3032_);
if (v___x_3067_ == 0)
{
lean_inc(v_fst_3032_);
goto v___jp_3046_;
}
else
{
if (v___x_3060_ == 0)
{
lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3075_; 
lean_del_object(v___x_3044_);
lean_del_object(v___x_3039_);
v_isSharedCheck_3075_ = !lean_is_exclusive(v_a_3029_);
if (v_isSharedCheck_3075_ == 0)
{
lean_object* v_unused_3076_; lean_object* v_unused_3077_; 
v_unused_3076_ = lean_ctor_get(v_a_3029_, 1);
lean_dec(v_unused_3076_);
v_unused_3077_ = lean_ctor_get(v_a_3029_, 0);
lean_dec(v_unused_3077_);
v___x_3069_ = v_a_3029_;
v_isShared_3070_ = v_isSharedCheck_3075_;
goto v_resetjp_3068_;
}
else
{
lean_dec(v_a_3029_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3075_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v___x_3072_; 
if (v_isShared_3070_ == 0)
{
lean_ctor_set(v___x_3069_, 1, v_snd_3042_);
lean_ctor_set(v___x_3069_, 0, v_fst_3041_);
v___x_3072_ = v___x_3069_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v_fst_3041_);
lean_ctor_set(v_reuseFailAlloc_3074_, 1, v_snd_3042_);
v___x_3072_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
lean_object* v___x_3073_; 
v___x_3073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3073_, 0, v_fst_3037_);
lean_ctor_set(v___x_3073_, 1, v___x_3072_);
v_a_3023_ = v___x_3073_;
goto v___jp_3022_;
}
}
}
else
{
lean_inc(v_fst_3032_);
goto v___jp_3046_;
}
}
}
}
else
{
lean_object* v___x_3079_; uint8_t v_isShared_3080_; uint8_t v_isSharedCheck_3085_; 
lean_del_object(v___x_3044_);
lean_del_object(v___x_3039_);
lean_del_object(v___x_3035_);
lean_dec(v_fst_3033_);
v_isSharedCheck_3085_ = !lean_is_exclusive(v_a_3029_);
if (v_isSharedCheck_3085_ == 0)
{
lean_object* v_unused_3086_; lean_object* v_unused_3087_; 
v_unused_3086_ = lean_ctor_get(v_a_3029_, 1);
lean_dec(v_unused_3086_);
v_unused_3087_ = lean_ctor_get(v_a_3029_, 0);
lean_dec(v_unused_3087_);
v___x_3079_ = v_a_3029_;
v_isShared_3080_ = v_isSharedCheck_3085_;
goto v_resetjp_3078_;
}
else
{
lean_dec(v_a_3029_);
v___x_3079_ = lean_box(0);
v_isShared_3080_ = v_isSharedCheck_3085_;
goto v_resetjp_3078_;
}
v_resetjp_3078_:
{
lean_object* v___x_3082_; 
if (v_isShared_3080_ == 0)
{
lean_ctor_set(v___x_3079_, 1, v_snd_3042_);
lean_ctor_set(v___x_3079_, 0, v_fst_3041_);
v___x_3082_ = v___x_3079_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_fst_3041_);
lean_ctor_set(v_reuseFailAlloc_3084_, 1, v_snd_3042_);
v___x_3082_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
lean_object* v___x_3083_; 
v___x_3083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3083_, 0, v_fst_3037_);
lean_ctor_set(v___x_3083_, 1, v___x_3082_);
v_a_3023_ = v___x_3083_;
goto v___jp_3022_;
}
}
}
v___jp_3046_:
{
lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3050_; 
v___x_3047_ = lean_array_push(v_snd_3042_, v_a_3029_);
v___x_3048_ = l_Lean_NameSet_insert(v_fst_3041_, v_fst_3032_);
if (v_isShared_3045_ == 0)
{
lean_ctor_set(v___x_3044_, 1, v___x_3047_);
lean_ctor_set(v___x_3044_, 0, v___x_3048_);
v___x_3050_ = v___x_3044_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v___x_3048_);
lean_ctor_set(v_reuseFailAlloc_3054_, 1, v___x_3047_);
v___x_3050_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
lean_object* v___x_3052_; 
if (v_isShared_3040_ == 0)
{
lean_ctor_set(v___x_3039_, 1, v___x_3050_);
v___x_3052_ = v___x_3039_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v_fst_3037_);
lean_ctor_set(v_reuseFailAlloc_3053_, 1, v___x_3050_);
v___x_3052_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
v_a_3023_ = v___x_3052_;
goto v___jp_3022_;
}
}
}
v___jp_3055_:
{
lean_object* v___x_3057_; 
if (v_isShared_3036_ == 0)
{
lean_ctor_set(v___x_3035_, 1, v_snd_3042_);
lean_ctor_set(v___x_3035_, 0, v_fst_3041_);
v___x_3057_ = v___x_3035_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v_fst_3041_);
lean_ctor_set(v_reuseFailAlloc_3059_, 1, v_snd_3042_);
v___x_3057_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
lean_object* v___x_3058_; 
v___x_3058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3058_, 0, v_fst_3037_);
lean_ctor_set(v___x_3058_, 1, v___x_3057_);
v_a_3023_ = v___x_3058_;
goto v___jp_3022_;
}
}
}
}
}
}
v___jp_3022_:
{
size_t v___x_3024_; size_t v___x_3025_; 
v___x_3024_ = ((size_t)1ULL);
v___x_3025_ = lean_usize_add(v_i_3019_, v___x_3024_);
v_i_3019_ = v___x_3025_;
v_b_3020_ = v_a_3023_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg___boxed(lean_object* v_forbidden_3093_, lean_object* v_as_3094_, lean_object* v_sz_3095_, lean_object* v_i_3096_, lean_object* v_b_3097_, lean_object* v___y_3098_){
_start:
{
size_t v_sz_boxed_3099_; size_t v_i_boxed_3100_; lean_object* v_res_3101_; 
v_sz_boxed_3099_ = lean_unbox_usize(v_sz_3095_);
lean_dec(v_sz_3095_);
v_i_boxed_3100_ = lean_unbox_usize(v_i_3096_);
lean_dec(v_i_3096_);
v_res_3101_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg(v_forbidden_3093_, v_as_3094_, v_sz_boxed_3099_, v_i_boxed_3100_, v_b_3097_);
lean_dec_ref(v_as_3094_);
lean_dec(v_forbidden_3093_);
return v_res_3101_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__2(void){
_start:
{
lean_object* v___x_3105_; lean_object* v___x_3106_; 
v___x_3105_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__1));
v___x_3106_ = l_Lean_MessageData_ofFormat(v___x_3105_);
return v___x_3106_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__3(void){
_start:
{
lean_object* v___x_3107_; lean_object* v___x_3108_; 
v___x_3107_ = lean_box(1);
v___x_3108_ = l_Lean_MessageData_ofFormat(v___x_3107_);
return v___x_3108_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4(lean_object* v_a_3111_, lean_object* v_a_3112_){
_start:
{
if (lean_obj_tag(v_a_3111_) == 0)
{
lean_object* v___x_3113_; 
v___x_3113_ = l_List_reverse___redArg(v_a_3112_);
return v___x_3113_;
}
else
{
lean_object* v_head_3114_; lean_object* v_snd_3115_; lean_object* v_tail_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3161_; 
v_head_3114_ = lean_ctor_get(v_a_3111_, 0);
lean_inc(v_head_3114_);
v_snd_3115_ = lean_ctor_get(v_head_3114_, 1);
lean_inc(v_snd_3115_);
v_tail_3116_ = lean_ctor_get(v_a_3111_, 1);
v_isSharedCheck_3161_ = !lean_is_exclusive(v_a_3111_);
if (v_isSharedCheck_3161_ == 0)
{
lean_object* v_unused_3162_; 
v_unused_3162_ = lean_ctor_get(v_a_3111_, 0);
lean_dec(v_unused_3162_);
v___x_3118_ = v_a_3111_;
v_isShared_3119_ = v_isSharedCheck_3161_;
goto v_resetjp_3117_;
}
else
{
lean_inc(v_tail_3116_);
lean_dec(v_a_3111_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3161_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
lean_object* v_fst_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3159_; 
v_fst_3120_ = lean_ctor_get(v_head_3114_, 0);
v_isSharedCheck_3159_ = !lean_is_exclusive(v_head_3114_);
if (v_isSharedCheck_3159_ == 0)
{
lean_object* v_unused_3160_; 
v_unused_3160_ = lean_ctor_get(v_head_3114_, 1);
lean_dec(v_unused_3160_);
v___x_3122_ = v_head_3114_;
v_isShared_3123_ = v_isSharedCheck_3159_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_fst_3120_);
lean_dec(v_head_3114_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3159_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
lean_object* v_fst_3124_; lean_object* v_snd_3125_; lean_object* v___x_3127_; uint8_t v_isShared_3128_; uint8_t v_isSharedCheck_3158_; 
v_fst_3124_ = lean_ctor_get(v_snd_3115_, 0);
v_snd_3125_ = lean_ctor_get(v_snd_3115_, 1);
v_isSharedCheck_3158_ = !lean_is_exclusive(v_snd_3115_);
if (v_isSharedCheck_3158_ == 0)
{
v___x_3127_ = v_snd_3115_;
v_isShared_3128_ = v_isSharedCheck_3158_;
goto v_resetjp_3126_;
}
else
{
lean_inc(v_snd_3125_);
lean_inc(v_fst_3124_);
lean_dec(v_snd_3115_);
v___x_3127_ = lean_box(0);
v_isShared_3128_ = v_isSharedCheck_3158_;
goto v_resetjp_3126_;
}
v_resetjp_3126_:
{
lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3132_; 
v___x_3129_ = l_Lean_MessageData_ofName(v_fst_3120_);
v___x_3130_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__2, &l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__2_once, _init_l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__2);
if (v_isShared_3128_ == 0)
{
lean_ctor_set_tag(v___x_3127_, 7);
lean_ctor_set(v___x_3127_, 1, v___x_3130_);
lean_ctor_set(v___x_3127_, 0, v___x_3129_);
v___x_3132_ = v___x_3127_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3157_; 
v_reuseFailAlloc_3157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3157_, 0, v___x_3129_);
lean_ctor_set(v_reuseFailAlloc_3157_, 1, v___x_3130_);
v___x_3132_ = v_reuseFailAlloc_3157_;
goto v_reusejp_3131_;
}
v_reusejp_3131_:
{
lean_object* v___x_3133_; lean_object* v___x_3135_; 
v___x_3133_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__3, &l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__3_once, _init_l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__3);
if (v_isShared_3123_ == 0)
{
lean_ctor_set_tag(v___x_3122_, 7);
lean_ctor_set(v___x_3122_, 1, v___x_3133_);
lean_ctor_set(v___x_3122_, 0, v___x_3132_);
v___x_3135_ = v___x_3122_;
goto v_reusejp_3134_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v___x_3132_);
lean_ctor_set(v_reuseFailAlloc_3156_, 1, v___x_3133_);
v___x_3135_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3134_;
}
v_reusejp_3134_:
{
lean_object* v___y_3137_; uint8_t v___x_3153_; 
v___x_3153_ = lean_unbox(v_fst_3124_);
lean_dec(v_fst_3124_);
if (v___x_3153_ == 0)
{
lean_object* v___x_3154_; 
v___x_3154_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__4));
v___y_3137_ = v___x_3154_;
goto v___jp_3136_;
}
else
{
lean_object* v___x_3155_; 
v___x_3155_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__5));
v___y_3137_ = v___x_3155_;
goto v___jp_3136_;
}
v___jp_3136_:
{
lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3150_; 
lean_inc_ref(v___y_3137_);
v___x_3138_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3138_, 0, v___y_3137_);
v___x_3139_ = l_Lean_MessageData_ofFormat(v___x_3138_);
v___x_3140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3140_, 0, v___x_3139_);
lean_ctor_set(v___x_3140_, 1, v___x_3130_);
v___x_3141_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3141_, 0, v___x_3140_);
lean_ctor_set(v___x_3141_, 1, v___x_3133_);
v___x_3142_ = l_Nat_reprFast(v_snd_3125_);
v___x_3143_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3143_, 0, v___x_3142_);
v___x_3144_ = l_Lean_MessageData_ofFormat(v___x_3143_);
v___x_3145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3145_, 0, v___x_3141_);
lean_ctor_set(v___x_3145_, 1, v___x_3144_);
v___x_3146_ = l_Lean_MessageData_paren(v___x_3145_);
v___x_3147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3147_, 0, v___x_3135_);
lean_ctor_set(v___x_3147_, 1, v___x_3146_);
v___x_3148_ = l_Lean_MessageData_paren(v___x_3147_);
if (v_isShared_3119_ == 0)
{
lean_ctor_set(v___x_3118_, 1, v_a_3112_);
lean_ctor_set(v___x_3118_, 0, v___x_3148_);
v___x_3150_ = v___x_3118_;
goto v_reusejp_3149_;
}
else
{
lean_object* v_reuseFailAlloc_3152_; 
v_reuseFailAlloc_3152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3152_, 0, v___x_3148_);
lean_ctor_set(v_reuseFailAlloc_3152_, 1, v_a_3112_);
v___x_3150_ = v_reuseFailAlloc_3152_;
goto v_reusejp_3149_;
}
v_reusejp_3149_:
{
v_a_3111_ = v_tail_3116_;
v_a_3112_ = v___x_3150_;
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
lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; 
v___x_3165_ = ((lean_object*)(l_Lean_Meta_Rewrites_rewriteCandidates___closed__0));
v___x_3166_ = l_Lean_NameSet_empty;
v___x_3167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3167_, 0, v___x_3166_);
lean_ctor_set(v___x_3167_, 1, v___x_3165_);
return v___x_3167_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__2(void){
_start:
{
lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; 
v___x_3168_ = lean_obj_once(&l_Lean_Meta_Rewrites_rewriteCandidates___closed__1, &l_Lean_Meta_Rewrites_rewriteCandidates___closed__1_once, _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__1);
v___x_3169_ = l_Lean_NameSet_empty;
v___x_3170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3170_, 0, v___x_3169_);
lean_ctor_set(v___x_3170_, 1, v___x_3168_);
return v___x_3170_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__3(void){
_start:
{
lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; 
v___x_3171_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_));
v___x_3172_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__4));
v___x_3173_ = l_Lean_Name_append(v___x_3172_, v___x_3171_);
return v___x_3173_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__5(void){
_start:
{
lean_object* v___x_3175_; lean_object* v___x_3176_; 
v___x_3175_ = ((lean_object*)(l_Lean_Meta_Rewrites_rewriteCandidates___closed__4));
v___x_3176_ = l_Lean_stringToMessageData(v___x_3175_);
return v___x_3176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rewriteCandidates(lean_object* v_hyps_3177_, lean_object* v_moduleRef_3178_, lean_object* v_target_3179_, lean_object* v_forbidden_3180_, lean_object* v_a_3181_, lean_object* v_a_3182_, lean_object* v_a_3183_, lean_object* v_a_3184_){
_start:
{
lean_object* v___x_3186_; lean_object* v___x_3187_; 
v___x_3186_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_rwFindDecls___boxed), 7, 1);
lean_closure_set(v___x_3186_, 0, v_moduleRef_3178_);
v___x_3187_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v___x_3186_, v_target_3179_, v_a_3181_, v_a_3182_, v_a_3183_, v_a_3184_);
if (lean_obj_tag(v___x_3187_) == 0)
{
lean_object* v_a_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; size_t v_sz_3193_; size_t v___x_3194_; lean_object* v___x_3195_; 
v_a_3188_ = lean_ctor_get(v___x_3187_, 0);
lean_inc(v_a_3188_);
lean_dec_ref_known(v___x_3187_, 1);
v___x_3189_ = lean_unsigned_to_nat(0u);
v___x_3190_ = lean_array_get_size(v_a_3188_);
v___x_3191_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0(v_a_3188_, v___x_3189_, v___x_3190_);
v___x_3192_ = lean_obj_once(&l_Lean_Meta_Rewrites_rewriteCandidates___closed__2, &l_Lean_Meta_Rewrites_rewriteCandidates___closed__2_once, _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__2);
v_sz_3193_ = lean_array_size(v___x_3191_);
v___x_3194_ = ((size_t)0ULL);
v___x_3195_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg(v_forbidden_3180_, v___x_3191_, v_sz_3193_, v___x_3194_, v___x_3192_);
lean_dec_ref(v___x_3191_);
if (lean_obj_tag(v___x_3195_) == 0)
{
lean_object* v_a_3196_; lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3240_; 
v_a_3196_ = lean_ctor_get(v___x_3195_, 0);
v_isSharedCheck_3240_ = !lean_is_exclusive(v___x_3195_);
if (v_isSharedCheck_3240_ == 0)
{
v___x_3198_ = v___x_3195_;
v_isShared_3199_ = v_isSharedCheck_3240_;
goto v_resetjp_3197_;
}
else
{
lean_inc(v_a_3196_);
lean_dec(v___x_3195_);
v___x_3198_ = lean_box(0);
v_isShared_3199_ = v_isSharedCheck_3240_;
goto v_resetjp_3197_;
}
v_resetjp_3197_:
{
lean_object* v_snd_3200_; lean_object* v_snd_3201_; lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3238_; 
v_snd_3200_ = lean_ctor_get(v_a_3196_, 1);
lean_inc(v_snd_3200_);
lean_dec(v_a_3196_);
v_snd_3201_ = lean_ctor_get(v_snd_3200_, 1);
v_isSharedCheck_3238_ = !lean_is_exclusive(v_snd_3200_);
if (v_isSharedCheck_3238_ == 0)
{
lean_object* v_unused_3239_; 
v_unused_3239_ = lean_ctor_get(v_snd_3200_, 0);
lean_dec(v_unused_3239_);
v___x_3203_ = v_snd_3200_;
v_isShared_3204_ = v_isSharedCheck_3238_;
goto v_resetjp_3202_;
}
else
{
lean_inc(v_snd_3201_);
lean_dec(v_snd_3200_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3238_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
lean_object* v_toCold_3214_; lean_object* v_options_3215_; uint8_t v_hasTrace_3216_; 
v_toCold_3214_ = lean_ctor_get(v_a_3183_, 0);
v_options_3215_ = lean_ctor_get(v_toCold_3214_, 2);
v_hasTrace_3216_ = lean_ctor_get_uint8(v_options_3215_, sizeof(void*)*1);
if (v_hasTrace_3216_ == 0)
{
lean_del_object(v___x_3203_);
goto v___jp_3205_;
}
else
{
lean_object* v_inheritedTraceOptions_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; uint8_t v___x_3220_; 
v_inheritedTraceOptions_3217_ = lean_ctor_get(v_toCold_3214_, 11);
v___x_3218_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_));
v___x_3219_ = lean_obj_once(&l_Lean_Meta_Rewrites_rewriteCandidates___closed__3, &l_Lean_Meta_Rewrites_rewriteCandidates___closed__3_once, _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__3);
v___x_3220_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3217_, v_options_3215_, v___x_3219_);
if (v___x_3220_ == 0)
{
lean_del_object(v___x_3203_);
goto v___jp_3205_;
}
else
{
lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3227_; 
v___x_3221_ = lean_obj_once(&l_Lean_Meta_Rewrites_rewriteCandidates___closed__5, &l_Lean_Meta_Rewrites_rewriteCandidates___closed__5_once, _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__5);
lean_inc(v_snd_3201_);
v___x_3222_ = lean_array_to_list(v_snd_3201_);
v___x_3223_ = lean_box(0);
v___x_3224_ = l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4(v___x_3222_, v___x_3223_);
v___x_3225_ = l_Lean_MessageData_ofList(v___x_3224_);
if (v_isShared_3204_ == 0)
{
lean_ctor_set_tag(v___x_3203_, 7);
lean_ctor_set(v___x_3203_, 1, v___x_3225_);
lean_ctor_set(v___x_3203_, 0, v___x_3221_);
v___x_3227_ = v___x_3203_;
goto v_reusejp_3226_;
}
else
{
lean_object* v_reuseFailAlloc_3237_; 
v_reuseFailAlloc_3237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3237_, 0, v___x_3221_);
lean_ctor_set(v_reuseFailAlloc_3237_, 1, v___x_3225_);
v___x_3227_ = v_reuseFailAlloc_3237_;
goto v_reusejp_3226_;
}
v_reusejp_3226_:
{
lean_object* v___x_3228_; 
v___x_3228_ = l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2(v___x_3218_, v___x_3227_, v_a_3181_, v_a_3182_, v_a_3183_, v_a_3184_);
if (lean_obj_tag(v___x_3228_) == 0)
{
lean_dec_ref_known(v___x_3228_, 1);
goto v___jp_3205_;
}
else
{
lean_object* v_a_3229_; lean_object* v___x_3231_; uint8_t v_isShared_3232_; uint8_t v_isSharedCheck_3236_; 
lean_dec(v_snd_3201_);
lean_del_object(v___x_3198_);
lean_dec_ref(v_hyps_3177_);
v_a_3229_ = lean_ctor_get(v___x_3228_, 0);
v_isSharedCheck_3236_ = !lean_is_exclusive(v___x_3228_);
if (v_isSharedCheck_3236_ == 0)
{
v___x_3231_ = v___x_3228_;
v_isShared_3232_ = v_isSharedCheck_3236_;
goto v_resetjp_3230_;
}
else
{
lean_inc(v_a_3229_);
lean_dec(v___x_3228_);
v___x_3231_ = lean_box(0);
v_isShared_3232_ = v_isSharedCheck_3236_;
goto v_resetjp_3230_;
}
v_resetjp_3230_:
{
lean_object* v___x_3234_; 
if (v_isShared_3232_ == 0)
{
v___x_3234_ = v___x_3231_;
goto v_reusejp_3233_;
}
else
{
lean_object* v_reuseFailAlloc_3235_; 
v_reuseFailAlloc_3235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3235_, 0, v_a_3229_);
v___x_3234_ = v_reuseFailAlloc_3235_;
goto v_reusejp_3233_;
}
v_reusejp_3233_:
{
return v___x_3234_;
}
}
}
}
}
}
v___jp_3205_:
{
size_t v_sz_3206_; lean_object* v___x_3207_; size_t v_sz_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3212_; 
v_sz_3206_ = lean_array_size(v_hyps_3177_);
v___x_3207_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__2(v_sz_3206_, v___x_3194_, v_hyps_3177_);
v_sz_3208_ = lean_array_size(v_snd_3201_);
v___x_3209_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__3(v_sz_3208_, v___x_3194_, v_snd_3201_);
v___x_3210_ = l_Array_append___redArg(v___x_3207_, v___x_3209_);
lean_dec_ref(v___x_3209_);
if (v_isShared_3199_ == 0)
{
lean_ctor_set(v___x_3198_, 0, v___x_3210_);
v___x_3212_ = v___x_3198_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3213_; 
v_reuseFailAlloc_3213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3213_, 0, v___x_3210_);
v___x_3212_ = v_reuseFailAlloc_3213_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
return v___x_3212_;
}
}
}
}
}
else
{
lean_object* v_a_3241_; lean_object* v___x_3243_; uint8_t v_isShared_3244_; uint8_t v_isSharedCheck_3248_; 
lean_dec_ref(v_hyps_3177_);
v_a_3241_ = lean_ctor_get(v___x_3195_, 0);
v_isSharedCheck_3248_ = !lean_is_exclusive(v___x_3195_);
if (v_isSharedCheck_3248_ == 0)
{
v___x_3243_ = v___x_3195_;
v_isShared_3244_ = v_isSharedCheck_3248_;
goto v_resetjp_3242_;
}
else
{
lean_inc(v_a_3241_);
lean_dec(v___x_3195_);
v___x_3243_ = lean_box(0);
v_isShared_3244_ = v_isSharedCheck_3248_;
goto v_resetjp_3242_;
}
v_resetjp_3242_:
{
lean_object* v___x_3246_; 
if (v_isShared_3244_ == 0)
{
v___x_3246_ = v___x_3243_;
goto v_reusejp_3245_;
}
else
{
lean_object* v_reuseFailAlloc_3247_; 
v_reuseFailAlloc_3247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3247_, 0, v_a_3241_);
v___x_3246_ = v_reuseFailAlloc_3247_;
goto v_reusejp_3245_;
}
v_reusejp_3245_:
{
return v___x_3246_;
}
}
}
}
else
{
lean_object* v_a_3249_; lean_object* v___x_3251_; uint8_t v_isShared_3252_; uint8_t v_isSharedCheck_3256_; 
lean_dec_ref(v_hyps_3177_);
v_a_3249_ = lean_ctor_get(v___x_3187_, 0);
v_isSharedCheck_3256_ = !lean_is_exclusive(v___x_3187_);
if (v_isSharedCheck_3256_ == 0)
{
v___x_3251_ = v___x_3187_;
v_isShared_3252_ = v_isSharedCheck_3256_;
goto v_resetjp_3250_;
}
else
{
lean_inc(v_a_3249_);
lean_dec(v___x_3187_);
v___x_3251_ = lean_box(0);
v_isShared_3252_ = v_isSharedCheck_3256_;
goto v_resetjp_3250_;
}
v_resetjp_3250_:
{
lean_object* v___x_3254_; 
if (v_isShared_3252_ == 0)
{
v___x_3254_ = v___x_3251_;
goto v_reusejp_3253_;
}
else
{
lean_object* v_reuseFailAlloc_3255_; 
v_reuseFailAlloc_3255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3255_, 0, v_a_3249_);
v___x_3254_ = v_reuseFailAlloc_3255_;
goto v_reusejp_3253_;
}
v_reusejp_3253_:
{
return v___x_3254_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rewriteCandidates___boxed(lean_object* v_hyps_3257_, lean_object* v_moduleRef_3258_, lean_object* v_target_3259_, lean_object* v_forbidden_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_, lean_object* v_a_3265_){
_start:
{
lean_object* v_res_3266_; 
v_res_3266_ = l_Lean_Meta_Rewrites_rewriteCandidates(v_hyps_3257_, v_moduleRef_3258_, v_target_3259_, v_forbidden_3260_, v_a_3261_, v_a_3262_, v_a_3263_, v_a_3264_);
lean_dec(v_a_3264_);
lean_dec_ref(v_a_3263_);
lean_dec(v_a_3262_);
lean_dec_ref(v_a_3261_);
lean_dec(v_forbidden_3260_);
return v_res_3266_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1(lean_object* v_forbidden_3267_, lean_object* v_as_3268_, size_t v_sz_3269_, size_t v_i_3270_, lean_object* v_b_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_){
_start:
{
lean_object* v___x_3277_; 
v___x_3277_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg(v_forbidden_3267_, v_as_3268_, v_sz_3269_, v_i_3270_, v_b_3271_);
return v___x_3277_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___boxed(lean_object* v_forbidden_3278_, lean_object* v_as_3279_, lean_object* v_sz_3280_, lean_object* v_i_3281_, lean_object* v_b_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_){
_start:
{
size_t v_sz_boxed_3288_; size_t v_i_boxed_3289_; lean_object* v_res_3290_; 
v_sz_boxed_3288_ = lean_unbox_usize(v_sz_3280_);
lean_dec(v_sz_3280_);
v_i_boxed_3289_ = lean_unbox_usize(v_i_3281_);
lean_dec(v_i_3281_);
v_res_3290_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1(v_forbidden_3278_, v_as_3279_, v_sz_boxed_3288_, v_i_boxed_3289_, v_b_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_);
lean_dec(v___y_3286_);
lean_dec_ref(v___y_3285_);
lean_dec(v___y_3284_);
lean_dec_ref(v___y_3283_);
lean_dec_ref(v_as_3279_);
lean_dec(v_forbidden_3278_);
return v_res_3290_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0(lean_object* v_xs_3291_, lean_object* v_j_3292_, lean_object* v_h_3293_){
_start:
{
lean_object* v___x_3294_; 
v___x_3294_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0___redArg(v_xs_3291_, v_j_3292_);
return v___x_3294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_newGoal(lean_object* v_r_3295_){
_start:
{
uint8_t v_rfl_x3f_3296_; 
v_rfl_x3f_3296_ = lean_ctor_get_uint8(v_r_3295_, sizeof(void*)*4 + 1);
if (v_rfl_x3f_3296_ == 0)
{
lean_object* v_result_3297_; lean_object* v_eNew_3298_; lean_object* v___x_3299_; 
v_result_3297_ = lean_ctor_get(v_r_3295_, 2);
v_eNew_3298_ = lean_ctor_get(v_result_3297_, 0);
lean_inc_ref(v_eNew_3298_);
v___x_3299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3299_, 0, v_eNew_3298_);
return v___x_3299_;
}
else
{
lean_object* v___x_3300_; 
v___x_3300_ = lean_box(0);
return v___x_3300_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_newGoal___boxed(lean_object* v_r_3301_){
_start:
{
lean_object* v_res_3302_; 
v_res_3302_ = l_Lean_Meta_Rewrites_RewriteResult_newGoal(v_r_3301_);
lean_dec_ref(v_r_3301_);
return v_res_3302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0(lean_object* v_x_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_){
_start:
{
lean_object* v___x_3313_; 
lean_inc(v___y_3307_);
lean_inc_ref(v___y_3306_);
lean_inc(v___y_3305_);
lean_inc_ref(v___y_3304_);
v___x_3313_ = lean_apply_9(v_x_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_, lean_box(0));
return v___x_3313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0___boxed(lean_object* v_x_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_){
_start:
{
lean_object* v_res_3324_; 
v_res_3324_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0(v_x_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_);
lean_dec(v___y_3318_);
lean_dec_ref(v___y_3317_);
lean_dec(v___y_3316_);
lean_dec_ref(v___y_3315_);
return v_res_3324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg(lean_object* v_mctx_3325_, lean_object* v_x_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_){
_start:
{
lean_object* v___f_3336_; lean_object* v___x_3337_; 
lean_inc(v___y_3330_);
lean_inc_ref(v___y_3329_);
lean_inc(v___y_3328_);
lean_inc_ref(v___y_3327_);
v___f_3336_ = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3336_, 0, v_x_3326_);
lean_closure_set(v___f_3336_, 1, v___y_3327_);
lean_closure_set(v___f_3336_, 2, v___y_3328_);
lean_closure_set(v___f_3336_, 3, v___y_3329_);
lean_closure_set(v___f_3336_, 4, v___y_3330_);
v___x_3337_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp(lean_box(0), v_mctx_3325_, v___f_3336_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_);
if (lean_obj_tag(v___x_3337_) == 0)
{
return v___x_3337_;
}
else
{
lean_object* v_a_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3345_; 
v_a_3338_ = lean_ctor_get(v___x_3337_, 0);
v_isSharedCheck_3345_ = !lean_is_exclusive(v___x_3337_);
if (v_isSharedCheck_3345_ == 0)
{
v___x_3340_ = v___x_3337_;
v_isShared_3341_ = v_isSharedCheck_3345_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_a_3338_);
lean_dec(v___x_3337_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3345_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
lean_object* v___x_3343_; 
if (v_isShared_3341_ == 0)
{
v___x_3343_ = v___x_3340_;
goto v_reusejp_3342_;
}
else
{
lean_object* v_reuseFailAlloc_3344_; 
v_reuseFailAlloc_3344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3344_, 0, v_a_3338_);
v___x_3343_ = v_reuseFailAlloc_3344_;
goto v_reusejp_3342_;
}
v_reusejp_3342_:
{
return v___x_3343_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___boxed(lean_object* v_mctx_3346_, lean_object* v_x_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_){
_start:
{
lean_object* v_res_3357_; 
v_res_3357_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg(v_mctx_3346_, v_x_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_);
lean_dec(v___y_3355_);
lean_dec_ref(v___y_3354_);
lean_dec(v___y_3353_);
lean_dec_ref(v___y_3352_);
lean_dec(v___y_3351_);
lean_dec_ref(v___y_3350_);
lean_dec(v___y_3349_);
lean_dec_ref(v___y_3348_);
return v_res_3357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0(lean_object* v_00_u03b1_3358_, lean_object* v_mctx_3359_, lean_object* v_x_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_){
_start:
{
lean_object* v___x_3370_; 
v___x_3370_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg(v_mctx_3359_, v_x_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_);
return v___x_3370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___boxed(lean_object* v_00_u03b1_3371_, lean_object* v_mctx_3372_, lean_object* v_x_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_){
_start:
{
lean_object* v_res_3383_; 
v_res_3383_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0(v_00_u03b1_3371_, v_mctx_3372_, v_x_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_);
lean_dec(v___y_3381_);
lean_dec_ref(v___y_3380_);
lean_dec(v___y_3379_);
lean_dec_ref(v___y_3378_);
lean_dec(v___y_3377_);
lean_dec_ref(v___y_3376_);
lean_dec(v___y_3375_);
lean_dec_ref(v___y_3374_);
return v_res_3383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0(lean_object* v_expr_3384_, uint8_t v_symm_3385_, lean_object* v_r_3386_, lean_object* v_ref_3387_, lean_object* v_checkState_x3f_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_){
_start:
{
lean_object* v___x_3398_; 
v___x_3398_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_3390_, v___y_3392_, v___y_3394_, v___y_3396_);
if (lean_obj_tag(v___x_3398_) == 0)
{
lean_object* v_a_3399_; lean_object* v_ref_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___y_3410_; 
v_a_3399_ = lean_ctor_get(v___x_3398_, 0);
lean_inc(v_a_3399_);
lean_dec_ref_known(v___x_3398_, 1);
v_ref_3400_ = lean_ctor_get(v___y_3395_, 2);
v___x_3401_ = lean_box(v_symm_3385_);
v___x_3402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3402_, 0, v_expr_3384_);
lean_ctor_set(v___x_3402_, 1, v___x_3401_);
v___x_3403_ = lean_box(0);
v___x_3404_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3404_, 0, v___x_3402_);
lean_ctor_set(v___x_3404_, 1, v___x_3403_);
v___x_3405_ = l_Lean_Meta_Rewrites_RewriteResult_newGoal(v_r_3386_);
v___x_3406_ = l_Lean_Option_toLOption___redArg(v___x_3405_);
v___x_3407_ = lean_box(0);
lean_inc(v_ref_3400_);
v___x_3408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3408_, 0, v_ref_3400_);
if (lean_obj_tag(v_checkState_x3f_3388_) == 0)
{
v___y_3410_ = v_a_3399_;
goto v___jp_3409_;
}
else
{
lean_object* v_val_3413_; 
lean_dec(v_a_3399_);
v_val_3413_ = lean_ctor_get(v_checkState_x3f_3388_, 0);
lean_inc(v_val_3413_);
lean_dec_ref_known(v_checkState_x3f_3388_, 1);
v___y_3410_ = v_val_3413_;
goto v___jp_3409_;
}
v___jp_3409_:
{
lean_object* v___x_3411_; lean_object* v___x_3412_; 
v___x_3411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3411_, 0, v___y_3410_);
v___x_3412_ = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion(v_ref_3387_, v___x_3404_, v___x_3406_, v___x_3407_, v___x_3408_, v___x_3411_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_);
return v___x_3412_;
}
}
else
{
lean_object* v_a_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3421_; 
lean_dec(v_checkState_x3f_3388_);
lean_dec(v_ref_3387_);
lean_dec_ref(v_expr_3384_);
v_a_3414_ = lean_ctor_get(v___x_3398_, 0);
v_isSharedCheck_3421_ = !lean_is_exclusive(v___x_3398_);
if (v_isSharedCheck_3421_ == 0)
{
v___x_3416_ = v___x_3398_;
v_isShared_3417_ = v_isSharedCheck_3421_;
goto v_resetjp_3415_;
}
else
{
lean_inc(v_a_3414_);
lean_dec(v___x_3398_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3421_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
lean_object* v___x_3419_; 
if (v_isShared_3417_ == 0)
{
v___x_3419_ = v___x_3416_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v_a_3414_);
v___x_3419_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
return v___x_3419_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0___boxed(lean_object* v_expr_3422_, lean_object* v_symm_3423_, lean_object* v_r_3424_, lean_object* v_ref_3425_, lean_object* v_checkState_x3f_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_){
_start:
{
uint8_t v_symm_boxed_3436_; lean_object* v_res_3437_; 
v_symm_boxed_3436_ = lean_unbox(v_symm_3423_);
v_res_3437_ = l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0(v_expr_3422_, v_symm_boxed_3436_, v_r_3424_, v_ref_3425_, v_checkState_x3f_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_);
lean_dec(v___y_3434_);
lean_dec_ref(v___y_3433_);
lean_dec(v___y_3432_);
lean_dec_ref(v___y_3431_);
lean_dec(v___y_3430_);
lean_dec_ref(v___y_3429_);
lean_dec(v___y_3428_);
lean_dec_ref(v___y_3427_);
lean_dec_ref(v_r_3424_);
return v_res_3437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion(lean_object* v_ref_3438_, lean_object* v_r_3439_, lean_object* v_checkState_x3f_3440_, lean_object* v_a_3441_, lean_object* v_a_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_){
_start:
{
lean_object* v_expr_3450_; uint8_t v_symm_3451_; lean_object* v_mctx_3452_; lean_object* v___x_3453_; lean_object* v___f_3454_; lean_object* v___x_3455_; 
v_expr_3450_ = lean_ctor_get(v_r_3439_, 0);
lean_inc_ref(v_expr_3450_);
v_symm_3451_ = lean_ctor_get_uint8(v_r_3439_, sizeof(void*)*4);
v_mctx_3452_ = lean_ctor_get(v_r_3439_, 3);
lean_inc_ref(v_mctx_3452_);
v___x_3453_ = lean_box(v_symm_3451_);
v___f_3454_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0___boxed), 14, 5);
lean_closure_set(v___f_3454_, 0, v_expr_3450_);
lean_closure_set(v___f_3454_, 1, v___x_3453_);
lean_closure_set(v___f_3454_, 2, v_r_3439_);
lean_closure_set(v___f_3454_, 3, v_ref_3438_);
lean_closure_set(v___f_3454_, 4, v_checkState_x3f_3440_);
v___x_3455_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg(v_mctx_3452_, v___f_3454_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_);
return v___x_3455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___boxed(lean_object* v_ref_3456_, lean_object* v_r_3457_, lean_object* v_checkState_x3f_3458_, lean_object* v_a_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_, lean_object* v_a_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_, lean_object* v_a_3465_, lean_object* v_a_3466_, lean_object* v_a_3467_){
_start:
{
lean_object* v_res_3468_; 
v_res_3468_ = l_Lean_Meta_Rewrites_RewriteResult_addSuggestion(v_ref_3456_, v_r_3457_, v_checkState_x3f_3458_, v_a_3459_, v_a_3460_, v_a_3461_, v_a_3462_, v_a_3463_, v_a_3464_, v_a_3465_, v_a_3466_);
lean_dec(v_a_3466_);
lean_dec_ref(v_a_3465_);
lean_dec(v_a_3464_);
lean_dec_ref(v_a_3463_);
lean_dec(v_a_3462_);
lean_dec_ref(v_a_3461_);
lean_dec(v_a_3460_);
lean_dec_ref(v_a_3459_);
return v_res_3468_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3___redArg(lean_object* v_a_3469_, lean_object* v_b_3470_, lean_object* v_x_3471_){
_start:
{
if (lean_obj_tag(v_x_3471_) == 0)
{
lean_dec(v_b_3470_);
lean_dec_ref(v_a_3469_);
return v_x_3471_;
}
else
{
lean_object* v_key_3472_; lean_object* v_value_3473_; lean_object* v_tail_3474_; lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3486_; 
v_key_3472_ = lean_ctor_get(v_x_3471_, 0);
v_value_3473_ = lean_ctor_get(v_x_3471_, 1);
v_tail_3474_ = lean_ctor_get(v_x_3471_, 2);
v_isSharedCheck_3486_ = !lean_is_exclusive(v_x_3471_);
if (v_isSharedCheck_3486_ == 0)
{
v___x_3476_ = v_x_3471_;
v_isShared_3477_ = v_isSharedCheck_3486_;
goto v_resetjp_3475_;
}
else
{
lean_inc(v_tail_3474_);
lean_inc(v_value_3473_);
lean_inc(v_key_3472_);
lean_dec(v_x_3471_);
v___x_3476_ = lean_box(0);
v_isShared_3477_ = v_isSharedCheck_3486_;
goto v_resetjp_3475_;
}
v_resetjp_3475_:
{
uint8_t v___x_3478_; 
v___x_3478_ = lean_string_dec_eq(v_key_3472_, v_a_3469_);
if (v___x_3478_ == 0)
{
lean_object* v___x_3479_; lean_object* v___x_3481_; 
v___x_3479_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3___redArg(v_a_3469_, v_b_3470_, v_tail_3474_);
if (v_isShared_3477_ == 0)
{
lean_ctor_set(v___x_3476_, 2, v___x_3479_);
v___x_3481_ = v___x_3476_;
goto v_reusejp_3480_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v_key_3472_);
lean_ctor_set(v_reuseFailAlloc_3482_, 1, v_value_3473_);
lean_ctor_set(v_reuseFailAlloc_3482_, 2, v___x_3479_);
v___x_3481_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3480_;
}
v_reusejp_3480_:
{
return v___x_3481_;
}
}
else
{
lean_object* v___x_3484_; 
lean_dec(v_value_3473_);
lean_dec(v_key_3472_);
if (v_isShared_3477_ == 0)
{
lean_ctor_set(v___x_3476_, 1, v_b_3470_);
lean_ctor_set(v___x_3476_, 0, v_a_3469_);
v___x_3484_ = v___x_3476_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v_a_3469_);
lean_ctor_set(v_reuseFailAlloc_3485_, 1, v_b_3470_);
lean_ctor_set(v_reuseFailAlloc_3485_, 2, v_tail_3474_);
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
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_x_3487_, lean_object* v_x_3488_){
_start:
{
if (lean_obj_tag(v_x_3488_) == 0)
{
return v_x_3487_;
}
else
{
lean_object* v_key_3489_; lean_object* v_value_3490_; lean_object* v_tail_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3514_; 
v_key_3489_ = lean_ctor_get(v_x_3488_, 0);
v_value_3490_ = lean_ctor_get(v_x_3488_, 1);
v_tail_3491_ = lean_ctor_get(v_x_3488_, 2);
v_isSharedCheck_3514_ = !lean_is_exclusive(v_x_3488_);
if (v_isSharedCheck_3514_ == 0)
{
v___x_3493_ = v_x_3488_;
v_isShared_3494_ = v_isSharedCheck_3514_;
goto v_resetjp_3492_;
}
else
{
lean_inc(v_tail_3491_);
lean_inc(v_value_3490_);
lean_inc(v_key_3489_);
lean_dec(v_x_3488_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3514_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
lean_object* v___x_3495_; uint64_t v___x_3496_; uint64_t v___x_3497_; uint64_t v___x_3498_; uint64_t v_fold_3499_; uint64_t v___x_3500_; uint64_t v___x_3501_; uint64_t v___x_3502_; size_t v___x_3503_; size_t v___x_3504_; size_t v___x_3505_; size_t v___x_3506_; size_t v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3510_; 
v___x_3495_ = lean_array_get_size(v_x_3487_);
v___x_3496_ = lean_string_hash(v_key_3489_);
v___x_3497_ = 32ULL;
v___x_3498_ = lean_uint64_shift_right(v___x_3496_, v___x_3497_);
v_fold_3499_ = lean_uint64_xor(v___x_3496_, v___x_3498_);
v___x_3500_ = 16ULL;
v___x_3501_ = lean_uint64_shift_right(v_fold_3499_, v___x_3500_);
v___x_3502_ = lean_uint64_xor(v_fold_3499_, v___x_3501_);
v___x_3503_ = lean_uint64_to_usize(v___x_3502_);
v___x_3504_ = lean_usize_of_nat(v___x_3495_);
v___x_3505_ = ((size_t)1ULL);
v___x_3506_ = lean_usize_sub(v___x_3504_, v___x_3505_);
v___x_3507_ = lean_usize_land(v___x_3503_, v___x_3506_);
v___x_3508_ = lean_array_uget_borrowed(v_x_3487_, v___x_3507_);
lean_inc(v___x_3508_);
if (v_isShared_3494_ == 0)
{
lean_ctor_set(v___x_3493_, 2, v___x_3508_);
v___x_3510_ = v___x_3493_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3513_; 
v_reuseFailAlloc_3513_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3513_, 0, v_key_3489_);
lean_ctor_set(v_reuseFailAlloc_3513_, 1, v_value_3490_);
lean_ctor_set(v_reuseFailAlloc_3513_, 2, v___x_3508_);
v___x_3510_ = v_reuseFailAlloc_3513_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
lean_object* v___x_3511_; 
v___x_3511_ = lean_array_uset(v_x_3487_, v___x_3507_, v___x_3510_);
v_x_3487_ = v___x_3511_;
v_x_3488_ = v_tail_3491_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3___redArg(lean_object* v_i_3515_, lean_object* v_source_3516_, lean_object* v_target_3517_){
_start:
{
lean_object* v___x_3518_; uint8_t v___x_3519_; 
v___x_3518_ = lean_array_get_size(v_source_3516_);
v___x_3519_ = lean_nat_dec_lt(v_i_3515_, v___x_3518_);
if (v___x_3519_ == 0)
{
lean_dec_ref(v_source_3516_);
lean_dec(v_i_3515_);
return v_target_3517_;
}
else
{
lean_object* v_es_3520_; lean_object* v___x_3521_; lean_object* v_source_3522_; lean_object* v_target_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; 
v_es_3520_ = lean_array_fget(v_source_3516_, v_i_3515_);
v___x_3521_ = lean_box(0);
v_source_3522_ = lean_array_fset(v_source_3516_, v_i_3515_, v___x_3521_);
v_target_3523_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3_spec__5___redArg(v_target_3517_, v_es_3520_);
v___x_3524_ = lean_unsigned_to_nat(1u);
v___x_3525_ = lean_nat_add(v_i_3515_, v___x_3524_);
lean_dec(v_i_3515_);
v_i_3515_ = v___x_3525_;
v_source_3516_ = v_source_3522_;
v_target_3517_ = v_target_3523_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2___redArg(lean_object* v_data_3527_){
_start:
{
lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v_nbuckets_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; 
v___x_3528_ = lean_array_get_size(v_data_3527_);
v___x_3529_ = lean_unsigned_to_nat(2u);
v_nbuckets_3530_ = lean_nat_mul(v___x_3528_, v___x_3529_);
v___x_3531_ = lean_unsigned_to_nat(0u);
v___x_3532_ = lean_box(0);
v___x_3533_ = lean_mk_array(v_nbuckets_3530_, v___x_3532_);
v___x_3534_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3___redArg(v___x_3531_, v_data_3527_, v___x_3533_);
return v___x_3534_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(lean_object* v_a_3535_, lean_object* v_x_3536_){
_start:
{
if (lean_obj_tag(v_x_3536_) == 0)
{
uint8_t v___x_3537_; 
v___x_3537_ = 0;
return v___x_3537_;
}
else
{
lean_object* v_key_3538_; lean_object* v_tail_3539_; uint8_t v___x_3540_; 
v_key_3538_ = lean_ctor_get(v_x_3536_, 0);
v_tail_3539_ = lean_ctor_get(v_x_3536_, 2);
v___x_3540_ = lean_string_dec_eq(v_key_3538_, v_a_3535_);
if (v___x_3540_ == 0)
{
v_x_3536_ = v_tail_3539_;
goto _start;
}
else
{
return v___x_3540_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg___boxed(lean_object* v_a_3542_, lean_object* v_x_3543_){
_start:
{
uint8_t v_res_3544_; lean_object* v_r_3545_; 
v_res_3544_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(v_a_3542_, v_x_3543_);
lean_dec(v_x_3543_);
lean_dec_ref(v_a_3542_);
v_r_3545_ = lean_box(v_res_3544_);
return v_r_3545_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1___redArg(lean_object* v_m_3546_, lean_object* v_a_3547_, lean_object* v_b_3548_){
_start:
{
lean_object* v_size_3549_; lean_object* v_buckets_3550_; lean_object* v___x_3552_; uint8_t v_isShared_3553_; uint8_t v_isSharedCheck_3593_; 
v_size_3549_ = lean_ctor_get(v_m_3546_, 0);
v_buckets_3550_ = lean_ctor_get(v_m_3546_, 1);
v_isSharedCheck_3593_ = !lean_is_exclusive(v_m_3546_);
if (v_isSharedCheck_3593_ == 0)
{
v___x_3552_ = v_m_3546_;
v_isShared_3553_ = v_isSharedCheck_3593_;
goto v_resetjp_3551_;
}
else
{
lean_inc(v_buckets_3550_);
lean_inc(v_size_3549_);
lean_dec(v_m_3546_);
v___x_3552_ = lean_box(0);
v_isShared_3553_ = v_isSharedCheck_3593_;
goto v_resetjp_3551_;
}
v_resetjp_3551_:
{
lean_object* v___x_3554_; uint64_t v___x_3555_; uint64_t v___x_3556_; uint64_t v___x_3557_; uint64_t v_fold_3558_; uint64_t v___x_3559_; uint64_t v___x_3560_; uint64_t v___x_3561_; size_t v___x_3562_; size_t v___x_3563_; size_t v___x_3564_; size_t v___x_3565_; size_t v___x_3566_; lean_object* v_bkt_3567_; uint8_t v___x_3568_; 
v___x_3554_ = lean_array_get_size(v_buckets_3550_);
v___x_3555_ = lean_string_hash(v_a_3547_);
v___x_3556_ = 32ULL;
v___x_3557_ = lean_uint64_shift_right(v___x_3555_, v___x_3556_);
v_fold_3558_ = lean_uint64_xor(v___x_3555_, v___x_3557_);
v___x_3559_ = 16ULL;
v___x_3560_ = lean_uint64_shift_right(v_fold_3558_, v___x_3559_);
v___x_3561_ = lean_uint64_xor(v_fold_3558_, v___x_3560_);
v___x_3562_ = lean_uint64_to_usize(v___x_3561_);
v___x_3563_ = lean_usize_of_nat(v___x_3554_);
v___x_3564_ = ((size_t)1ULL);
v___x_3565_ = lean_usize_sub(v___x_3563_, v___x_3564_);
v___x_3566_ = lean_usize_land(v___x_3562_, v___x_3565_);
v_bkt_3567_ = lean_array_uget_borrowed(v_buckets_3550_, v___x_3566_);
v___x_3568_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(v_a_3547_, v_bkt_3567_);
if (v___x_3568_ == 0)
{
lean_object* v___x_3569_; lean_object* v_size_x27_3570_; lean_object* v___x_3571_; lean_object* v_buckets_x27_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; uint8_t v___x_3578_; 
v___x_3569_ = lean_unsigned_to_nat(1u);
v_size_x27_3570_ = lean_nat_add(v_size_3549_, v___x_3569_);
lean_dec(v_size_3549_);
lean_inc(v_bkt_3567_);
v___x_3571_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3571_, 0, v_a_3547_);
lean_ctor_set(v___x_3571_, 1, v_b_3548_);
lean_ctor_set(v___x_3571_, 2, v_bkt_3567_);
v_buckets_x27_3572_ = lean_array_uset(v_buckets_3550_, v___x_3566_, v___x_3571_);
v___x_3573_ = lean_unsigned_to_nat(4u);
v___x_3574_ = lean_nat_mul(v_size_x27_3570_, v___x_3573_);
v___x_3575_ = lean_unsigned_to_nat(3u);
v___x_3576_ = lean_nat_div(v___x_3574_, v___x_3575_);
lean_dec(v___x_3574_);
v___x_3577_ = lean_array_get_size(v_buckets_x27_3572_);
v___x_3578_ = lean_nat_dec_le(v___x_3576_, v___x_3577_);
lean_dec(v___x_3576_);
if (v___x_3578_ == 0)
{
lean_object* v_val_3579_; lean_object* v___x_3581_; 
v_val_3579_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2___redArg(v_buckets_x27_3572_);
if (v_isShared_3553_ == 0)
{
lean_ctor_set(v___x_3552_, 1, v_val_3579_);
lean_ctor_set(v___x_3552_, 0, v_size_x27_3570_);
v___x_3581_ = v___x_3552_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v_size_x27_3570_);
lean_ctor_set(v_reuseFailAlloc_3582_, 1, v_val_3579_);
v___x_3581_ = v_reuseFailAlloc_3582_;
goto v_reusejp_3580_;
}
v_reusejp_3580_:
{
return v___x_3581_;
}
}
else
{
lean_object* v___x_3584_; 
if (v_isShared_3553_ == 0)
{
lean_ctor_set(v___x_3552_, 1, v_buckets_x27_3572_);
lean_ctor_set(v___x_3552_, 0, v_size_x27_3570_);
v___x_3584_ = v___x_3552_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3585_; 
v_reuseFailAlloc_3585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3585_, 0, v_size_x27_3570_);
lean_ctor_set(v_reuseFailAlloc_3585_, 1, v_buckets_x27_3572_);
v___x_3584_ = v_reuseFailAlloc_3585_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
return v___x_3584_;
}
}
}
else
{
lean_object* v___x_3586_; lean_object* v_buckets_x27_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3591_; 
lean_inc(v_bkt_3567_);
v___x_3586_ = lean_box(0);
v_buckets_x27_3587_ = lean_array_uset(v_buckets_3550_, v___x_3566_, v___x_3586_);
v___x_3588_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3___redArg(v_a_3547_, v_b_3548_, v_bkt_3567_);
v___x_3589_ = lean_array_uset(v_buckets_x27_3587_, v___x_3566_, v___x_3588_);
if (v_isShared_3553_ == 0)
{
lean_ctor_set(v___x_3552_, 1, v___x_3589_);
v___x_3591_ = v___x_3552_;
goto v_reusejp_3590_;
}
else
{
lean_object* v_reuseFailAlloc_3592_; 
v_reuseFailAlloc_3592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3592_, 0, v_size_3549_);
lean_ctor_set(v_reuseFailAlloc_3592_, 1, v___x_3589_);
v___x_3591_ = v_reuseFailAlloc_3592_;
goto v_reusejp_3590_;
}
v_reusejp_3590_:
{
return v___x_3591_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg(lean_object* v_m_3594_, lean_object* v_a_3595_){
_start:
{
lean_object* v_buckets_3596_; lean_object* v___x_3597_; uint64_t v___x_3598_; uint64_t v___x_3599_; uint64_t v___x_3600_; uint64_t v_fold_3601_; uint64_t v___x_3602_; uint64_t v___x_3603_; uint64_t v___x_3604_; size_t v___x_3605_; size_t v___x_3606_; size_t v___x_3607_; size_t v___x_3608_; size_t v___x_3609_; lean_object* v___x_3610_; uint8_t v___x_3611_; 
v_buckets_3596_ = lean_ctor_get(v_m_3594_, 1);
v___x_3597_ = lean_array_get_size(v_buckets_3596_);
v___x_3598_ = lean_string_hash(v_a_3595_);
v___x_3599_ = 32ULL;
v___x_3600_ = lean_uint64_shift_right(v___x_3598_, v___x_3599_);
v_fold_3601_ = lean_uint64_xor(v___x_3598_, v___x_3600_);
v___x_3602_ = 16ULL;
v___x_3603_ = lean_uint64_shift_right(v_fold_3601_, v___x_3602_);
v___x_3604_ = lean_uint64_xor(v_fold_3601_, v___x_3603_);
v___x_3605_ = lean_uint64_to_usize(v___x_3604_);
v___x_3606_ = lean_usize_of_nat(v___x_3597_);
v___x_3607_ = ((size_t)1ULL);
v___x_3608_ = lean_usize_sub(v___x_3606_, v___x_3607_);
v___x_3609_ = lean_usize_land(v___x_3605_, v___x_3608_);
v___x_3610_ = lean_array_uget_borrowed(v_buckets_3596_, v___x_3609_);
v___x_3611_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(v_a_3595_, v___x_3610_);
return v___x_3611_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg___boxed(lean_object* v_m_3612_, lean_object* v_a_3613_){
_start:
{
uint8_t v_res_3614_; lean_object* v_r_3615_; 
v_res_3614_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg(v_m_3612_, v_a_3613_);
lean_dec_ref(v_a_3613_);
lean_dec_ref(v_m_3612_);
v_r_3615_ = lean_box(v_res_3614_);
return v_r_3615_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg(lean_object* v_cfg_3616_, lean_object* v_as_x27_3617_, lean_object* v_b_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_){
_start:
{
if (lean_obj_tag(v_as_x27_3617_) == 0)
{
lean_object* v___x_3624_; 
lean_dec_ref(v_cfg_3616_);
v___x_3624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3624_, 0, v_b_3618_);
return v___x_3624_;
}
else
{
lean_object* v_head_3625_; lean_object* v_snd_3626_; lean_object* v_tail_3627_; lean_object* v_fst_3628_; lean_object* v_fst_3629_; lean_object* v_snd_3630_; lean_object* v___x_3631_; 
v_head_3625_ = lean_ctor_get(v_as_x27_3617_, 0);
v_snd_3626_ = lean_ctor_get(v_head_3625_, 1);
v_tail_3627_ = lean_ctor_get(v_as_x27_3617_, 1);
v_fst_3628_ = lean_ctor_get(v_head_3625_, 0);
v_fst_3629_ = lean_ctor_get(v_snd_3626_, 0);
v_snd_3630_ = lean_ctor_get(v_snd_3626_, 1);
v___x_3631_ = l_Lean_getRemainingHeartbeats___redArg(v___y_3621_);
if (lean_obj_tag(v___x_3631_) == 0)
{
lean_object* v_snd_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3776_; 
v_snd_3632_ = lean_ctor_get(v_b_3618_, 1);
v_isSharedCheck_3776_ = !lean_is_exclusive(v_b_3618_);
if (v_isSharedCheck_3776_ == 0)
{
lean_object* v_unused_3777_; 
v_unused_3777_ = lean_ctor_get(v_b_3618_, 0);
lean_dec(v_unused_3777_);
v___x_3634_ = v_b_3618_;
v_isShared_3635_ = v_isSharedCheck_3776_;
goto v_resetjp_3633_;
}
else
{
lean_inc(v_snd_3632_);
lean_dec(v_b_3618_);
v___x_3634_ = lean_box(0);
v_isShared_3635_ = v_isSharedCheck_3776_;
goto v_resetjp_3633_;
}
v_resetjp_3633_:
{
lean_object* v_a_3636_; lean_object* v___x_3638_; uint8_t v_isShared_3639_; uint8_t v_isSharedCheck_3775_; 
v_a_3636_ = lean_ctor_get(v___x_3631_, 0);
v_isSharedCheck_3775_ = !lean_is_exclusive(v___x_3631_);
if (v_isSharedCheck_3775_ == 0)
{
v___x_3638_ = v___x_3631_;
v_isShared_3639_ = v_isSharedCheck_3775_;
goto v_resetjp_3637_;
}
else
{
lean_inc(v_a_3636_);
lean_dec(v___x_3631_);
v___x_3638_ = lean_box(0);
v_isShared_3639_ = v_isSharedCheck_3775_;
goto v_resetjp_3637_;
}
v_resetjp_3637_:
{
lean_object* v_fst_3640_; lean_object* v_snd_3641_; lean_object* v___x_3643_; uint8_t v_isShared_3644_; uint8_t v_isSharedCheck_3774_; 
v_fst_3640_ = lean_ctor_get(v_snd_3632_, 0);
v_snd_3641_ = lean_ctor_get(v_snd_3632_, 1);
v_isSharedCheck_3774_ = !lean_is_exclusive(v_snd_3632_);
if (v_isSharedCheck_3774_ == 0)
{
v___x_3643_ = v_snd_3632_;
v_isShared_3644_ = v_isSharedCheck_3774_;
goto v_resetjp_3642_;
}
else
{
lean_inc(v_snd_3641_);
lean_inc(v_fst_3640_);
lean_dec(v_snd_3632_);
v___x_3643_ = lean_box(0);
v_isShared_3644_ = v_isSharedCheck_3774_;
goto v_resetjp_3642_;
}
v_resetjp_3642_:
{
uint8_t v_stopAtRfl_3645_; lean_object* v_max_3646_; lean_object* v_minHeartbeats_3647_; lean_object* v_goal_3648_; lean_object* v_target_3649_; uint8_t v_side_3650_; lean_object* v_mctx_3651_; uint8_t v___x_3652_; 
v_stopAtRfl_3645_ = lean_ctor_get_uint8(v_cfg_3616_, sizeof(void*)*5);
v_max_3646_ = lean_ctor_get(v_cfg_3616_, 0);
v_minHeartbeats_3647_ = lean_ctor_get(v_cfg_3616_, 1);
v_goal_3648_ = lean_ctor_get(v_cfg_3616_, 2);
v_target_3649_ = lean_ctor_get(v_cfg_3616_, 3);
v_side_3650_ = lean_ctor_get_uint8(v_cfg_3616_, sizeof(void*)*5 + 1);
v_mctx_3651_ = lean_ctor_get(v_cfg_3616_, 4);
v___x_3652_ = lean_nat_dec_lt(v_a_3636_, v_minHeartbeats_3647_);
lean_dec(v_a_3636_);
if (v___x_3652_ == 0)
{
lean_object* v___x_3653_; uint8_t v___x_3654_; 
v___x_3653_ = lean_array_get_size(v_snd_3641_);
v___x_3654_ = lean_nat_dec_le(v_max_3646_, v___x_3653_);
if (v___x_3654_ == 0)
{
lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; 
lean_del_object(v___x_3638_);
v___x_3655_ = lean_box(v_side_3650_);
lean_inc(v_snd_3630_);
lean_inc(v_fst_3629_);
lean_inc(v_fst_3628_);
lean_inc_ref(v_target_3649_);
lean_inc(v_goal_3648_);
lean_inc_ref_n(v_mctx_3651_, 2);
v___x_3656_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_rwLemma___boxed), 12, 7);
lean_closure_set(v___x_3656_, 0, v_mctx_3651_);
lean_closure_set(v___x_3656_, 1, v_goal_3648_);
lean_closure_set(v___x_3656_, 2, v_target_3649_);
lean_closure_set(v___x_3656_, 3, v___x_3655_);
lean_closure_set(v___x_3656_, 4, v_fst_3628_);
lean_closure_set(v___x_3656_, 5, v_fst_3629_);
lean_closure_set(v___x_3656_, 6, v_snd_3630_);
v___x_3657_ = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___boxed), 8, 3);
lean_closure_set(v___x_3657_, 0, lean_box(0));
lean_closure_set(v___x_3657_, 1, v_mctx_3651_);
lean_closure_set(v___x_3657_, 2, v___x_3656_);
v___x_3658_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v___x_3657_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_);
if (lean_obj_tag(v___x_3658_) == 0)
{
lean_object* v_a_3659_; lean_object* v___x_3660_; 
v_a_3659_ = lean_ctor_get(v___x_3658_, 0);
lean_inc(v_a_3659_);
lean_dec_ref_known(v___x_3658_, 1);
v___x_3660_ = lean_box(0);
if (lean_obj_tag(v_a_3659_) == 0)
{
lean_object* v___x_3662_; 
if (v_isShared_3644_ == 0)
{
v___x_3662_ = v___x_3643_;
goto v_reusejp_3661_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v_fst_3640_);
lean_ctor_set(v_reuseFailAlloc_3667_, 1, v_snd_3641_);
v___x_3662_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3661_;
}
v_reusejp_3661_:
{
lean_object* v___x_3664_; 
if (v_isShared_3635_ == 0)
{
lean_ctor_set(v___x_3634_, 1, v___x_3662_);
lean_ctor_set(v___x_3634_, 0, v___x_3660_);
v___x_3664_ = v___x_3634_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v___x_3660_);
lean_ctor_set(v_reuseFailAlloc_3666_, 1, v___x_3662_);
v___x_3664_ = v_reuseFailAlloc_3666_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
v_as_x27_3617_ = v_tail_3627_;
v_b_3618_ = v___x_3664_;
goto _start;
}
}
}
else
{
lean_object* v_val_3668_; lean_object* v___x_3670_; uint8_t v_isShared_3671_; uint8_t v_isSharedCheck_3745_; 
v_val_3668_ = lean_ctor_get(v_a_3659_, 0);
v_isSharedCheck_3745_ = !lean_is_exclusive(v_a_3659_);
if (v_isSharedCheck_3745_ == 0)
{
v___x_3670_ = v_a_3659_;
v_isShared_3671_ = v_isSharedCheck_3745_;
goto v_resetjp_3669_;
}
else
{
lean_inc(v_val_3668_);
lean_dec(v_a_3659_);
v___x_3670_ = lean_box(0);
v_isShared_3671_ = v_isSharedCheck_3745_;
goto v_resetjp_3669_;
}
v_resetjp_3669_:
{
lean_object* v_result_3672_; lean_object* v_mctx_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; 
v_result_3672_ = lean_ctor_get(v_val_3668_, 2);
v_mctx_3673_ = lean_ctor_get(v_val_3668_, 3);
lean_inc(v_val_3668_);
v___x_3674_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult___boxed), 6, 1);
lean_closure_set(v___x_3674_, 0, v_val_3668_);
lean_inc_ref(v_mctx_3673_);
v___x_3675_ = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___boxed), 8, 3);
lean_closure_set(v___x_3675_, 0, lean_box(0));
lean_closure_set(v___x_3675_, 1, v_mctx_3673_);
lean_closure_set(v___x_3675_, 2, v___x_3674_);
v___x_3676_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v___x_3675_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_);
if (lean_obj_tag(v___x_3676_) == 0)
{
lean_object* v_a_3677_; uint8_t v___x_3678_; 
v_a_3677_ = lean_ctor_get(v___x_3676_, 0);
lean_inc(v_a_3677_);
lean_dec_ref_known(v___x_3676_, 1);
v___x_3678_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg(v_fst_3640_, v_a_3677_);
if (v___x_3678_ == 0)
{
lean_object* v_eNew_3679_; lean_object* v___x_3680_; 
v_eNew_3679_ = lean_ctor_get(v_result_3672_, 0);
lean_inc_ref(v_eNew_3679_);
lean_inc_ref(v_mctx_3673_);
v___x_3680_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(v_mctx_3673_, v_eNew_3679_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_);
if (lean_obj_tag(v___x_3680_) == 0)
{
if (v_stopAtRfl_3645_ == 0)
{
lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3685_; 
lean_dec_ref_known(v___x_3680_, 1);
lean_del_object(v___x_3670_);
v___x_3681_ = lean_box(0);
v___x_3682_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1___redArg(v_fst_3640_, v_a_3677_, v___x_3681_);
v___x_3683_ = lean_array_push(v_snd_3641_, v_val_3668_);
if (v_isShared_3644_ == 0)
{
lean_ctor_set(v___x_3643_, 1, v___x_3683_);
lean_ctor_set(v___x_3643_, 0, v___x_3682_);
v___x_3685_ = v___x_3643_;
goto v_reusejp_3684_;
}
else
{
lean_object* v_reuseFailAlloc_3690_; 
v_reuseFailAlloc_3690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3690_, 0, v___x_3682_);
lean_ctor_set(v_reuseFailAlloc_3690_, 1, v___x_3683_);
v___x_3685_ = v_reuseFailAlloc_3690_;
goto v_reusejp_3684_;
}
v_reusejp_3684_:
{
lean_object* v___x_3687_; 
if (v_isShared_3635_ == 0)
{
lean_ctor_set(v___x_3634_, 1, v___x_3685_);
lean_ctor_set(v___x_3634_, 0, v___x_3660_);
v___x_3687_ = v___x_3634_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3689_; 
v_reuseFailAlloc_3689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3689_, 0, v___x_3660_);
lean_ctor_set(v_reuseFailAlloc_3689_, 1, v___x_3685_);
v___x_3687_ = v_reuseFailAlloc_3689_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
v_as_x27_3617_ = v_tail_3627_;
v_b_3618_ = v___x_3687_;
goto _start;
}
}
}
else
{
lean_object* v_a_3691_; lean_object* v___x_3693_; uint8_t v_isShared_3694_; uint8_t v_isSharedCheck_3721_; 
v_a_3691_ = lean_ctor_get(v___x_3680_, 0);
v_isSharedCheck_3721_ = !lean_is_exclusive(v___x_3680_);
if (v_isSharedCheck_3721_ == 0)
{
v___x_3693_ = v___x_3680_;
v_isShared_3694_ = v_isSharedCheck_3721_;
goto v_resetjp_3692_;
}
else
{
lean_inc(v_a_3691_);
lean_dec(v___x_3680_);
v___x_3693_ = lean_box(0);
v_isShared_3694_ = v_isSharedCheck_3721_;
goto v_resetjp_3692_;
}
v_resetjp_3692_:
{
uint8_t v___x_3695_; 
v___x_3695_ = lean_unbox(v_a_3691_);
lean_dec(v_a_3691_);
if (v___x_3695_ == 0)
{
lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3700_; 
lean_del_object(v___x_3693_);
lean_del_object(v___x_3670_);
v___x_3696_ = lean_box(0);
v___x_3697_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1___redArg(v_fst_3640_, v_a_3677_, v___x_3696_);
v___x_3698_ = lean_array_push(v_snd_3641_, v_val_3668_);
if (v_isShared_3644_ == 0)
{
lean_ctor_set(v___x_3643_, 1, v___x_3698_);
lean_ctor_set(v___x_3643_, 0, v___x_3697_);
v___x_3700_ = v___x_3643_;
goto v_reusejp_3699_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v___x_3697_);
lean_ctor_set(v_reuseFailAlloc_3705_, 1, v___x_3698_);
v___x_3700_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3699_;
}
v_reusejp_3699_:
{
lean_object* v___x_3702_; 
if (v_isShared_3635_ == 0)
{
lean_ctor_set(v___x_3634_, 1, v___x_3700_);
lean_ctor_set(v___x_3634_, 0, v___x_3660_);
v___x_3702_ = v___x_3634_;
goto v_reusejp_3701_;
}
else
{
lean_object* v_reuseFailAlloc_3704_; 
v_reuseFailAlloc_3704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3704_, 0, v___x_3660_);
lean_ctor_set(v_reuseFailAlloc_3704_, 1, v___x_3700_);
v___x_3702_ = v_reuseFailAlloc_3704_;
goto v_reusejp_3701_;
}
v_reusejp_3701_:
{
v_as_x27_3617_ = v_tail_3627_;
v_b_3618_ = v___x_3702_;
goto _start;
}
}
}
else
{
lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3710_; 
lean_dec(v_a_3677_);
lean_dec_ref(v_cfg_3616_);
v___x_3706_ = lean_unsigned_to_nat(1u);
v___x_3707_ = lean_mk_empty_array_with_capacity(v___x_3706_);
v___x_3708_ = lean_array_push(v___x_3707_, v_val_3668_);
if (v_isShared_3671_ == 0)
{
lean_ctor_set(v___x_3670_, 0, v___x_3708_);
v___x_3710_ = v___x_3670_;
goto v_reusejp_3709_;
}
else
{
lean_object* v_reuseFailAlloc_3720_; 
v_reuseFailAlloc_3720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3720_, 0, v___x_3708_);
v___x_3710_ = v_reuseFailAlloc_3720_;
goto v_reusejp_3709_;
}
v_reusejp_3709_:
{
lean_object* v___x_3712_; 
if (v_isShared_3644_ == 0)
{
v___x_3712_ = v___x_3643_;
goto v_reusejp_3711_;
}
else
{
lean_object* v_reuseFailAlloc_3719_; 
v_reuseFailAlloc_3719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3719_, 0, v_fst_3640_);
lean_ctor_set(v_reuseFailAlloc_3719_, 1, v_snd_3641_);
v___x_3712_ = v_reuseFailAlloc_3719_;
goto v_reusejp_3711_;
}
v_reusejp_3711_:
{
lean_object* v___x_3714_; 
if (v_isShared_3635_ == 0)
{
lean_ctor_set(v___x_3634_, 1, v___x_3712_);
lean_ctor_set(v___x_3634_, 0, v___x_3710_);
v___x_3714_ = v___x_3634_;
goto v_reusejp_3713_;
}
else
{
lean_object* v_reuseFailAlloc_3718_; 
v_reuseFailAlloc_3718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3718_, 0, v___x_3710_);
lean_ctor_set(v_reuseFailAlloc_3718_, 1, v___x_3712_);
v___x_3714_ = v_reuseFailAlloc_3718_;
goto v_reusejp_3713_;
}
v_reusejp_3713_:
{
lean_object* v___x_3716_; 
if (v_isShared_3694_ == 0)
{
lean_ctor_set(v___x_3693_, 0, v___x_3714_);
v___x_3716_ = v___x_3693_;
goto v_reusejp_3715_;
}
else
{
lean_object* v_reuseFailAlloc_3717_; 
v_reuseFailAlloc_3717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3717_, 0, v___x_3714_);
v___x_3716_ = v_reuseFailAlloc_3717_;
goto v_reusejp_3715_;
}
v_reusejp_3715_:
{
return v___x_3716_;
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
lean_object* v_a_3722_; lean_object* v___x_3724_; uint8_t v_isShared_3725_; uint8_t v_isSharedCheck_3729_; 
lean_dec(v_a_3677_);
lean_del_object(v___x_3670_);
lean_dec(v_val_3668_);
lean_del_object(v___x_3643_);
lean_dec(v_snd_3641_);
lean_dec(v_fst_3640_);
lean_del_object(v___x_3634_);
lean_dec_ref(v_cfg_3616_);
v_a_3722_ = lean_ctor_get(v___x_3680_, 0);
v_isSharedCheck_3729_ = !lean_is_exclusive(v___x_3680_);
if (v_isSharedCheck_3729_ == 0)
{
v___x_3724_ = v___x_3680_;
v_isShared_3725_ = v_isSharedCheck_3729_;
goto v_resetjp_3723_;
}
else
{
lean_inc(v_a_3722_);
lean_dec(v___x_3680_);
v___x_3724_ = lean_box(0);
v_isShared_3725_ = v_isSharedCheck_3729_;
goto v_resetjp_3723_;
}
v_resetjp_3723_:
{
lean_object* v___x_3727_; 
if (v_isShared_3725_ == 0)
{
v___x_3727_ = v___x_3724_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v_a_3722_);
v___x_3727_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
return v___x_3727_;
}
}
}
}
else
{
lean_object* v___x_3731_; 
lean_dec(v_a_3677_);
lean_del_object(v___x_3670_);
lean_dec(v_val_3668_);
if (v_isShared_3644_ == 0)
{
v___x_3731_ = v___x_3643_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3736_; 
v_reuseFailAlloc_3736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3736_, 0, v_fst_3640_);
lean_ctor_set(v_reuseFailAlloc_3736_, 1, v_snd_3641_);
v___x_3731_ = v_reuseFailAlloc_3736_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
lean_object* v___x_3733_; 
if (v_isShared_3635_ == 0)
{
lean_ctor_set(v___x_3634_, 1, v___x_3731_);
lean_ctor_set(v___x_3634_, 0, v___x_3660_);
v___x_3733_ = v___x_3634_;
goto v_reusejp_3732_;
}
else
{
lean_object* v_reuseFailAlloc_3735_; 
v_reuseFailAlloc_3735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3735_, 0, v___x_3660_);
lean_ctor_set(v_reuseFailAlloc_3735_, 1, v___x_3731_);
v___x_3733_ = v_reuseFailAlloc_3735_;
goto v_reusejp_3732_;
}
v_reusejp_3732_:
{
v_as_x27_3617_ = v_tail_3627_;
v_b_3618_ = v___x_3733_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3737_; lean_object* v___x_3739_; uint8_t v_isShared_3740_; uint8_t v_isSharedCheck_3744_; 
lean_del_object(v___x_3670_);
lean_dec(v_val_3668_);
lean_del_object(v___x_3643_);
lean_dec(v_snd_3641_);
lean_dec(v_fst_3640_);
lean_del_object(v___x_3634_);
lean_dec_ref(v_cfg_3616_);
v_a_3737_ = lean_ctor_get(v___x_3676_, 0);
v_isSharedCheck_3744_ = !lean_is_exclusive(v___x_3676_);
if (v_isSharedCheck_3744_ == 0)
{
v___x_3739_ = v___x_3676_;
v_isShared_3740_ = v_isSharedCheck_3744_;
goto v_resetjp_3738_;
}
else
{
lean_inc(v_a_3737_);
lean_dec(v___x_3676_);
v___x_3739_ = lean_box(0);
v_isShared_3740_ = v_isSharedCheck_3744_;
goto v_resetjp_3738_;
}
v_resetjp_3738_:
{
lean_object* v___x_3742_; 
if (v_isShared_3740_ == 0)
{
v___x_3742_ = v___x_3739_;
goto v_reusejp_3741_;
}
else
{
lean_object* v_reuseFailAlloc_3743_; 
v_reuseFailAlloc_3743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3743_, 0, v_a_3737_);
v___x_3742_ = v_reuseFailAlloc_3743_;
goto v_reusejp_3741_;
}
v_reusejp_3741_:
{
return v___x_3742_;
}
}
}
}
}
}
else
{
lean_object* v_a_3746_; lean_object* v___x_3748_; uint8_t v_isShared_3749_; uint8_t v_isSharedCheck_3753_; 
lean_del_object(v___x_3643_);
lean_dec(v_snd_3641_);
lean_dec(v_fst_3640_);
lean_del_object(v___x_3634_);
lean_dec_ref(v_cfg_3616_);
v_a_3746_ = lean_ctor_get(v___x_3658_, 0);
v_isSharedCheck_3753_ = !lean_is_exclusive(v___x_3658_);
if (v_isSharedCheck_3753_ == 0)
{
v___x_3748_ = v___x_3658_;
v_isShared_3749_ = v_isSharedCheck_3753_;
goto v_resetjp_3747_;
}
else
{
lean_inc(v_a_3746_);
lean_dec(v___x_3658_);
v___x_3748_ = lean_box(0);
v_isShared_3749_ = v_isSharedCheck_3753_;
goto v_resetjp_3747_;
}
v_resetjp_3747_:
{
lean_object* v___x_3751_; 
if (v_isShared_3749_ == 0)
{
v___x_3751_ = v___x_3748_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v_a_3746_);
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
else
{
lean_object* v___x_3754_; lean_object* v___x_3756_; 
lean_dec_ref(v_cfg_3616_);
lean_inc(v_snd_3641_);
v___x_3754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3754_, 0, v_snd_3641_);
if (v_isShared_3644_ == 0)
{
v___x_3756_ = v___x_3643_;
goto v_reusejp_3755_;
}
else
{
lean_object* v_reuseFailAlloc_3763_; 
v_reuseFailAlloc_3763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3763_, 0, v_fst_3640_);
lean_ctor_set(v_reuseFailAlloc_3763_, 1, v_snd_3641_);
v___x_3756_ = v_reuseFailAlloc_3763_;
goto v_reusejp_3755_;
}
v_reusejp_3755_:
{
lean_object* v___x_3758_; 
if (v_isShared_3635_ == 0)
{
lean_ctor_set(v___x_3634_, 1, v___x_3756_);
lean_ctor_set(v___x_3634_, 0, v___x_3754_);
v___x_3758_ = v___x_3634_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3762_; 
v_reuseFailAlloc_3762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3762_, 0, v___x_3754_);
lean_ctor_set(v_reuseFailAlloc_3762_, 1, v___x_3756_);
v___x_3758_ = v_reuseFailAlloc_3762_;
goto v_reusejp_3757_;
}
v_reusejp_3757_:
{
lean_object* v___x_3760_; 
if (v_isShared_3639_ == 0)
{
lean_ctor_set(v___x_3638_, 0, v___x_3758_);
v___x_3760_ = v___x_3638_;
goto v_reusejp_3759_;
}
else
{
lean_object* v_reuseFailAlloc_3761_; 
v_reuseFailAlloc_3761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3761_, 0, v___x_3758_);
v___x_3760_ = v_reuseFailAlloc_3761_;
goto v_reusejp_3759_;
}
v_reusejp_3759_:
{
return v___x_3760_;
}
}
}
}
}
else
{
lean_object* v___x_3764_; lean_object* v___x_3766_; 
lean_dec_ref(v_cfg_3616_);
lean_inc(v_snd_3641_);
v___x_3764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3764_, 0, v_snd_3641_);
if (v_isShared_3644_ == 0)
{
v___x_3766_ = v___x_3643_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3773_; 
v_reuseFailAlloc_3773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3773_, 0, v_fst_3640_);
lean_ctor_set(v_reuseFailAlloc_3773_, 1, v_snd_3641_);
v___x_3766_ = v_reuseFailAlloc_3773_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
lean_object* v___x_3768_; 
if (v_isShared_3635_ == 0)
{
lean_ctor_set(v___x_3634_, 1, v___x_3766_);
lean_ctor_set(v___x_3634_, 0, v___x_3764_);
v___x_3768_ = v___x_3634_;
goto v_reusejp_3767_;
}
else
{
lean_object* v_reuseFailAlloc_3772_; 
v_reuseFailAlloc_3772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3772_, 0, v___x_3764_);
lean_ctor_set(v_reuseFailAlloc_3772_, 1, v___x_3766_);
v___x_3768_ = v_reuseFailAlloc_3772_;
goto v_reusejp_3767_;
}
v_reusejp_3767_:
{
lean_object* v___x_3770_; 
if (v_isShared_3639_ == 0)
{
lean_ctor_set(v___x_3638_, 0, v___x_3768_);
v___x_3770_ = v___x_3638_;
goto v_reusejp_3769_;
}
else
{
lean_object* v_reuseFailAlloc_3771_; 
v_reuseFailAlloc_3771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3771_, 0, v___x_3768_);
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
}
}
}
else
{
lean_object* v_a_3778_; lean_object* v___x_3780_; uint8_t v_isShared_3781_; uint8_t v_isSharedCheck_3785_; 
lean_dec_ref(v_b_3618_);
lean_dec_ref(v_cfg_3616_);
v_a_3778_ = lean_ctor_get(v___x_3631_, 0);
v_isSharedCheck_3785_ = !lean_is_exclusive(v___x_3631_);
if (v_isSharedCheck_3785_ == 0)
{
v___x_3780_ = v___x_3631_;
v_isShared_3781_ = v_isSharedCheck_3785_;
goto v_resetjp_3779_;
}
else
{
lean_inc(v_a_3778_);
lean_dec(v___x_3631_);
v___x_3780_ = lean_box(0);
v_isShared_3781_ = v_isSharedCheck_3785_;
goto v_resetjp_3779_;
}
v_resetjp_3779_:
{
lean_object* v___x_3783_; 
if (v_isShared_3781_ == 0)
{
v___x_3783_ = v___x_3780_;
goto v_reusejp_3782_;
}
else
{
lean_object* v_reuseFailAlloc_3784_; 
v_reuseFailAlloc_3784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3784_, 0, v_a_3778_);
v___x_3783_ = v_reuseFailAlloc_3784_;
goto v_reusejp_3782_;
}
v_reusejp_3782_:
{
return v___x_3783_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg___boxed(lean_object* v_cfg_3786_, lean_object* v_as_x27_3787_, lean_object* v_b_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_){
_start:
{
lean_object* v_res_3794_; 
v_res_3794_ = l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg(v_cfg_3786_, v_as_x27_3787_, v_b_3788_, v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_);
lean_dec(v___y_3792_);
lean_dec_ref(v___y_3791_);
lean_dec(v___y_3790_);
lean_dec_ref(v___y_3789_);
lean_dec(v_as_x27_3787_);
return v_res_3794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_takeListAux(lean_object* v_cfg_3795_, lean_object* v_seen_3796_, lean_object* v_acc_3797_, lean_object* v_xs_3798_, lean_object* v_a_3799_, lean_object* v_a_3800_, lean_object* v_a_3801_, lean_object* v_a_3802_){
_start:
{
lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; 
v___x_3804_ = lean_box(0);
v___x_3805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3805_, 0, v_seen_3796_);
lean_ctor_set(v___x_3805_, 1, v_acc_3797_);
v___x_3806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3806_, 0, v___x_3804_);
lean_ctor_set(v___x_3806_, 1, v___x_3805_);
v___x_3807_ = l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg(v_cfg_3795_, v_xs_3798_, v___x_3806_, v_a_3799_, v_a_3800_, v_a_3801_, v_a_3802_);
if (lean_obj_tag(v___x_3807_) == 0)
{
lean_object* v_a_3808_; lean_object* v___x_3810_; uint8_t v_isShared_3811_; uint8_t v_isSharedCheck_3822_; 
v_a_3808_ = lean_ctor_get(v___x_3807_, 0);
v_isSharedCheck_3822_ = !lean_is_exclusive(v___x_3807_);
if (v_isSharedCheck_3822_ == 0)
{
v___x_3810_ = v___x_3807_;
v_isShared_3811_ = v_isSharedCheck_3822_;
goto v_resetjp_3809_;
}
else
{
lean_inc(v_a_3808_);
lean_dec(v___x_3807_);
v___x_3810_ = lean_box(0);
v_isShared_3811_ = v_isSharedCheck_3822_;
goto v_resetjp_3809_;
}
v_resetjp_3809_:
{
lean_object* v_fst_3812_; 
v_fst_3812_ = lean_ctor_get(v_a_3808_, 0);
if (lean_obj_tag(v_fst_3812_) == 0)
{
lean_object* v_snd_3813_; lean_object* v_snd_3814_; lean_object* v___x_3816_; 
v_snd_3813_ = lean_ctor_get(v_a_3808_, 1);
lean_inc(v_snd_3813_);
lean_dec(v_a_3808_);
v_snd_3814_ = lean_ctor_get(v_snd_3813_, 1);
lean_inc(v_snd_3814_);
lean_dec(v_snd_3813_);
if (v_isShared_3811_ == 0)
{
lean_ctor_set(v___x_3810_, 0, v_snd_3814_);
v___x_3816_ = v___x_3810_;
goto v_reusejp_3815_;
}
else
{
lean_object* v_reuseFailAlloc_3817_; 
v_reuseFailAlloc_3817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3817_, 0, v_snd_3814_);
v___x_3816_ = v_reuseFailAlloc_3817_;
goto v_reusejp_3815_;
}
v_reusejp_3815_:
{
return v___x_3816_;
}
}
else
{
lean_object* v_val_3818_; lean_object* v___x_3820_; 
lean_inc_ref(v_fst_3812_);
lean_dec(v_a_3808_);
v_val_3818_ = lean_ctor_get(v_fst_3812_, 0);
lean_inc(v_val_3818_);
lean_dec_ref_known(v_fst_3812_, 1);
if (v_isShared_3811_ == 0)
{
lean_ctor_set(v___x_3810_, 0, v_val_3818_);
v___x_3820_ = v___x_3810_;
goto v_reusejp_3819_;
}
else
{
lean_object* v_reuseFailAlloc_3821_; 
v_reuseFailAlloc_3821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3821_, 0, v_val_3818_);
v___x_3820_ = v_reuseFailAlloc_3821_;
goto v_reusejp_3819_;
}
v_reusejp_3819_:
{
return v___x_3820_;
}
}
}
}
else
{
lean_object* v_a_3823_; lean_object* v___x_3825_; uint8_t v_isShared_3826_; uint8_t v_isSharedCheck_3830_; 
v_a_3823_ = lean_ctor_get(v___x_3807_, 0);
v_isSharedCheck_3830_ = !lean_is_exclusive(v___x_3807_);
if (v_isSharedCheck_3830_ == 0)
{
v___x_3825_ = v___x_3807_;
v_isShared_3826_ = v_isSharedCheck_3830_;
goto v_resetjp_3824_;
}
else
{
lean_inc(v_a_3823_);
lean_dec(v___x_3807_);
v___x_3825_ = lean_box(0);
v_isShared_3826_ = v_isSharedCheck_3830_;
goto v_resetjp_3824_;
}
v_resetjp_3824_:
{
lean_object* v___x_3828_; 
if (v_isShared_3826_ == 0)
{
v___x_3828_ = v___x_3825_;
goto v_reusejp_3827_;
}
else
{
lean_object* v_reuseFailAlloc_3829_; 
v_reuseFailAlloc_3829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3829_, 0, v_a_3823_);
v___x_3828_ = v_reuseFailAlloc_3829_;
goto v_reusejp_3827_;
}
v_reusejp_3827_:
{
return v___x_3828_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_takeListAux___boxed(lean_object* v_cfg_3831_, lean_object* v_seen_3832_, lean_object* v_acc_3833_, lean_object* v_xs_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_, lean_object* v_a_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_){
_start:
{
lean_object* v_res_3840_; 
v_res_3840_ = l_Lean_Meta_Rewrites_takeListAux(v_cfg_3831_, v_seen_3832_, v_acc_3833_, v_xs_3834_, v_a_3835_, v_a_3836_, v_a_3837_, v_a_3838_);
lean_dec(v_a_3838_);
lean_dec_ref(v_a_3837_);
lean_dec(v_a_3836_);
lean_dec_ref(v_a_3835_);
lean_dec(v_xs_3834_);
return v_res_3840_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0(lean_object* v_00_u03b2_3841_, lean_object* v_m_3842_, lean_object* v_a_3843_){
_start:
{
uint8_t v___x_3844_; 
v___x_3844_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg(v_m_3842_, v_a_3843_);
return v___x_3844_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___boxed(lean_object* v_00_u03b2_3845_, lean_object* v_m_3846_, lean_object* v_a_3847_){
_start:
{
uint8_t v_res_3848_; lean_object* v_r_3849_; 
v_res_3848_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0(v_00_u03b2_3845_, v_m_3846_, v_a_3847_);
lean_dec_ref(v_a_3847_);
lean_dec_ref(v_m_3846_);
v_r_3849_ = lean_box(v_res_3848_);
return v_r_3849_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1(lean_object* v_00_u03b2_3850_, lean_object* v_m_3851_, lean_object* v_a_3852_, lean_object* v_b_3853_){
_start:
{
lean_object* v___x_3854_; 
v___x_3854_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1___redArg(v_m_3851_, v_a_3852_, v_b_3853_);
return v___x_3854_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2(lean_object* v_cfg_3855_, lean_object* v_as_3856_, lean_object* v_as_x27_3857_, lean_object* v_b_3858_, lean_object* v_a_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_){
_start:
{
lean_object* v___x_3865_; 
v___x_3865_ = l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg(v_cfg_3855_, v_as_x27_3857_, v_b_3858_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_);
return v___x_3865_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___boxed(lean_object* v_cfg_3866_, lean_object* v_as_3867_, lean_object* v_as_x27_3868_, lean_object* v_b_3869_, lean_object* v_a_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_){
_start:
{
lean_object* v_res_3876_; 
v_res_3876_ = l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2(v_cfg_3866_, v_as_3867_, v_as_x27_3868_, v_b_3869_, v_a_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
lean_dec(v___y_3874_);
lean_dec_ref(v___y_3873_);
lean_dec(v___y_3872_);
lean_dec_ref(v___y_3871_);
lean_dec(v_as_x27_3868_);
lean_dec(v_as_3867_);
return v_res_3876_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0(lean_object* v_00_u03b2_3877_, lean_object* v_a_3878_, lean_object* v_x_3879_){
_start:
{
uint8_t v___x_3880_; 
v___x_3880_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(v_a_3878_, v_x_3879_);
return v___x_3880_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3881_, lean_object* v_a_3882_, lean_object* v_x_3883_){
_start:
{
uint8_t v_res_3884_; lean_object* v_r_3885_; 
v_res_3884_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0(v_00_u03b2_3881_, v_a_3882_, v_x_3883_);
lean_dec(v_x_3883_);
lean_dec_ref(v_a_3882_);
v_r_3885_ = lean_box(v_res_3884_);
return v_r_3885_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2(lean_object* v_00_u03b2_3886_, lean_object* v_data_3887_){
_start:
{
lean_object* v___x_3888_; 
v___x_3888_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2___redArg(v_data_3887_);
return v___x_3888_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3(lean_object* v_00_u03b2_3889_, lean_object* v_a_3890_, lean_object* v_b_3891_, lean_object* v_x_3892_){
_start:
{
lean_object* v___x_3893_; 
v___x_3893_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3___redArg(v_a_3890_, v_b_3891_, v_x_3892_);
return v___x_3893_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_3894_, lean_object* v_i_3895_, lean_object* v_source_3896_, lean_object* v_target_3897_){
_start:
{
lean_object* v___x_3898_; 
v___x_3898_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3___redArg(v_i_3895_, v_source_3896_, v_target_3897_);
return v___x_3898_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_3899_, lean_object* v_x_3900_, lean_object* v_x_3901_){
_start:
{
lean_object* v___x_3902_; 
v___x_3902_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3_spec__5___redArg(v_x_3900_, v_x_3901_);
return v___x_3902_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_findRewrites___closed__0(void){
_start:
{
lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; 
v___x_3903_ = lean_box(0);
v___x_3904_ = lean_unsigned_to_nat(16u);
v___x_3905_ = lean_mk_array(v___x_3904_, v___x_3903_);
return v___x_3905_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_findRewrites___closed__1(void){
_start:
{
lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; 
v___x_3906_ = lean_obj_once(&l_Lean_Meta_Rewrites_findRewrites___closed__0, &l_Lean_Meta_Rewrites_findRewrites___closed__0_once, _init_l_Lean_Meta_Rewrites_findRewrites___closed__0);
v___x_3907_ = lean_unsigned_to_nat(0u);
v___x_3908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3908_, 0, v___x_3907_);
lean_ctor_set(v___x_3908_, 1, v___x_3906_);
return v___x_3908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_findRewrites(lean_object* v_hyps_3909_, lean_object* v_moduleRef_3910_, lean_object* v_goal_3911_, lean_object* v_target_3912_, lean_object* v_forbidden_3913_, uint8_t v_side_3914_, uint8_t v_stopAtRfl_3915_, lean_object* v_max_3916_, lean_object* v_leavePercentHeartbeats_3917_, lean_object* v_a_3918_, lean_object* v_a_3919_, lean_object* v_a_3920_, lean_object* v_a_3921_){
_start:
{
lean_object* v___x_3923_; lean_object* v___x_3924_; 
v___x_3923_ = lean_st_ref_get(v_a_3919_);
lean_inc_ref(v_target_3912_);
v___x_3924_ = l_Lean_Meta_Rewrites_rewriteCandidates(v_hyps_3909_, v_moduleRef_3910_, v_target_3912_, v_forbidden_3913_, v_a_3918_, v_a_3919_, v_a_3920_, v_a_3921_);
if (lean_obj_tag(v___x_3924_) == 0)
{
lean_object* v_a_3925_; lean_object* v___x_3926_; 
v_a_3925_ = lean_ctor_get(v___x_3924_, 0);
lean_inc(v_a_3925_);
lean_dec_ref_known(v___x_3924_, 1);
v___x_3926_ = l_Lean_getMaxHeartbeats___redArg(v_a_3920_);
if (lean_obj_tag(v___x_3926_) == 0)
{
lean_object* v_a_3927_; lean_object* v_mctx_3928_; lean_object* v_minHeartbeats_3930_; lean_object* v___y_3931_; lean_object* v___y_3932_; lean_object* v___y_3933_; lean_object* v___y_3934_; lean_object* v___x_3957_; uint8_t v___x_3958_; 
v_a_3927_ = lean_ctor_get(v___x_3926_, 0);
lean_inc(v_a_3927_);
lean_dec_ref_known(v___x_3926_, 1);
v_mctx_3928_ = lean_ctor_get(v___x_3923_, 0);
lean_inc_ref(v_mctx_3928_);
lean_dec(v___x_3923_);
v___x_3957_ = lean_unsigned_to_nat(0u);
v___x_3958_ = lean_nat_dec_eq(v_a_3927_, v___x_3957_);
lean_dec(v_a_3927_);
if (v___x_3958_ == 0)
{
lean_object* v___x_3959_; 
v___x_3959_ = l_Lean_getRemainingHeartbeats___redArg(v_a_3920_);
if (lean_obj_tag(v___x_3959_) == 0)
{
lean_object* v_a_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; 
v_a_3960_ = lean_ctor_get(v___x_3959_, 0);
lean_inc(v_a_3960_);
lean_dec_ref_known(v___x_3959_, 1);
v___x_3961_ = lean_nat_mul(v_leavePercentHeartbeats_3917_, v_a_3960_);
lean_dec(v_a_3960_);
v___x_3962_ = lean_unsigned_to_nat(100u);
v___x_3963_ = lean_nat_div(v___x_3961_, v___x_3962_);
lean_dec(v___x_3961_);
v_minHeartbeats_3930_ = v___x_3963_;
v___y_3931_ = v_a_3918_;
v___y_3932_ = v_a_3919_;
v___y_3933_ = v_a_3920_;
v___y_3934_ = v_a_3921_;
goto v___jp_3929_;
}
else
{
lean_object* v_a_3964_; lean_object* v___x_3966_; uint8_t v_isShared_3967_; uint8_t v_isSharedCheck_3971_; 
lean_dec_ref(v_mctx_3928_);
lean_dec(v_a_3925_);
lean_dec(v_max_3916_);
lean_dec_ref(v_target_3912_);
lean_dec(v_goal_3911_);
v_a_3964_ = lean_ctor_get(v___x_3959_, 0);
v_isSharedCheck_3971_ = !lean_is_exclusive(v___x_3959_);
if (v_isSharedCheck_3971_ == 0)
{
v___x_3966_ = v___x_3959_;
v_isShared_3967_ = v_isSharedCheck_3971_;
goto v_resetjp_3965_;
}
else
{
lean_inc(v_a_3964_);
lean_dec(v___x_3959_);
v___x_3966_ = lean_box(0);
v_isShared_3967_ = v_isSharedCheck_3971_;
goto v_resetjp_3965_;
}
v_resetjp_3965_:
{
lean_object* v___x_3969_; 
if (v_isShared_3967_ == 0)
{
v___x_3969_ = v___x_3966_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_3970_; 
v_reuseFailAlloc_3970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3970_, 0, v_a_3964_);
v___x_3969_ = v_reuseFailAlloc_3970_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
return v___x_3969_;
}
}
}
}
else
{
v_minHeartbeats_3930_ = v___x_3957_;
v___y_3931_ = v_a_3918_;
v___y_3932_ = v_a_3919_;
v___y_3933_ = v_a_3920_;
v___y_3934_ = v_a_3921_;
goto v___jp_3929_;
}
v___jp_3929_:
{
lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; 
lean_inc(v_max_3916_);
v___x_3935_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_3935_, 0, v_max_3916_);
lean_ctor_set(v___x_3935_, 1, v_minHeartbeats_3930_);
lean_ctor_set(v___x_3935_, 2, v_goal_3911_);
lean_ctor_set(v___x_3935_, 3, v_target_3912_);
lean_ctor_set(v___x_3935_, 4, v_mctx_3928_);
lean_ctor_set_uint8(v___x_3935_, sizeof(void*)*5, v_stopAtRfl_3915_);
lean_ctor_set_uint8(v___x_3935_, sizeof(void*)*5 + 1, v_side_3914_);
v___x_3936_ = lean_obj_once(&l_Lean_Meta_Rewrites_findRewrites___closed__1, &l_Lean_Meta_Rewrites_findRewrites___closed__1_once, _init_l_Lean_Meta_Rewrites_findRewrites___closed__1);
v___x_3937_ = lean_mk_empty_array_with_capacity(v_max_3916_);
lean_dec(v_max_3916_);
v___x_3938_ = lean_array_to_list(v_a_3925_);
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
lean_object* v_a_3972_; lean_object* v___x_3974_; uint8_t v_isShared_3975_; uint8_t v_isSharedCheck_3979_; 
lean_dec(v_a_3925_);
lean_dec(v___x_3923_);
lean_dec(v_max_3916_);
lean_dec_ref(v_target_3912_);
lean_dec(v_goal_3911_);
v_a_3972_ = lean_ctor_get(v___x_3926_, 0);
v_isSharedCheck_3979_ = !lean_is_exclusive(v___x_3926_);
if (v_isSharedCheck_3979_ == 0)
{
v___x_3974_ = v___x_3926_;
v_isShared_3975_ = v_isSharedCheck_3979_;
goto v_resetjp_3973_;
}
else
{
lean_inc(v_a_3972_);
lean_dec(v___x_3926_);
v___x_3974_ = lean_box(0);
v_isShared_3975_ = v_isSharedCheck_3979_;
goto v_resetjp_3973_;
}
v_resetjp_3973_:
{
lean_object* v___x_3977_; 
if (v_isShared_3975_ == 0)
{
v___x_3977_ = v___x_3974_;
goto v_reusejp_3976_;
}
else
{
lean_object* v_reuseFailAlloc_3978_; 
v_reuseFailAlloc_3978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3978_, 0, v_a_3972_);
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
else
{
lean_object* v_a_3980_; lean_object* v___x_3982_; uint8_t v_isShared_3983_; uint8_t v_isSharedCheck_3987_; 
lean_dec(v___x_3923_);
lean_dec(v_max_3916_);
lean_dec_ref(v_target_3912_);
lean_dec(v_goal_3911_);
v_a_3980_ = lean_ctor_get(v___x_3924_, 0);
v_isSharedCheck_3987_ = !lean_is_exclusive(v___x_3924_);
if (v_isSharedCheck_3987_ == 0)
{
v___x_3982_ = v___x_3924_;
v_isShared_3983_ = v_isSharedCheck_3987_;
goto v_resetjp_3981_;
}
else
{
lean_inc(v_a_3980_);
lean_dec(v___x_3924_);
v___x_3982_ = lean_box(0);
v_isShared_3983_ = v_isSharedCheck_3987_;
goto v_resetjp_3981_;
}
v_resetjp_3981_:
{
lean_object* v___x_3985_; 
if (v_isShared_3983_ == 0)
{
v___x_3985_ = v___x_3982_;
goto v_reusejp_3984_;
}
else
{
lean_object* v_reuseFailAlloc_3986_; 
v_reuseFailAlloc_3986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3986_, 0, v_a_3980_);
v___x_3985_ = v_reuseFailAlloc_3986_;
goto v_reusejp_3984_;
}
v_reusejp_3984_:
{
return v___x_3985_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_findRewrites___boxed(lean_object* v_hyps_3988_, lean_object* v_moduleRef_3989_, lean_object* v_goal_3990_, lean_object* v_target_3991_, lean_object* v_forbidden_3992_, lean_object* v_side_3993_, lean_object* v_stopAtRfl_3994_, lean_object* v_max_3995_, lean_object* v_leavePercentHeartbeats_3996_, lean_object* v_a_3997_, lean_object* v_a_3998_, lean_object* v_a_3999_, lean_object* v_a_4000_, lean_object* v_a_4001_){
_start:
{
uint8_t v_side_boxed_4002_; uint8_t v_stopAtRfl_boxed_4003_; lean_object* v_res_4004_; 
v_side_boxed_4002_ = lean_unbox(v_side_3993_);
v_stopAtRfl_boxed_4003_ = lean_unbox(v_stopAtRfl_3994_);
v_res_4004_ = l_Lean_Meta_Rewrites_findRewrites(v_hyps_3988_, v_moduleRef_3989_, v_goal_3990_, v_target_3991_, v_forbidden_3992_, v_side_boxed_4002_, v_stopAtRfl_boxed_4003_, v_max_3995_, v_leavePercentHeartbeats_3996_, v_a_3997_, v_a_3998_, v_a_3999_, v_a_4000_);
lean_dec(v_a_4000_);
lean_dec_ref(v_a_3999_);
lean_dec(v_a_3998_);
lean_dec_ref(v_a_3997_);
lean_dec(v_leavePercentHeartbeats_3996_);
lean_dec(v_forbidden_3992_);
return v_res_4004_;
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

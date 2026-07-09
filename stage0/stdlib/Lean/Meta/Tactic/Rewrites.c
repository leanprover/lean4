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
uint8_t v___x_7261__boxed_511_; uint8_t v___x_7263__boxed_512_; lean_object* v_res_513_; 
v___x_7261__boxed_511_ = lean_unbox(v___x_502_);
v___x_7263__boxed_512_ = lean_unbox(v___x_505_);
v_res_513_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__1(v___x_7261__boxed_511_, v_type_503_, v___f_504_, v___x_7263__boxed_512_, v___y_506_, v___y_507_, v___y_508_, v___y_509_);
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
lean_object* v___x_530_; lean_object* v_env_534_; uint8_t v___x_535_; 
v___x_530_ = lean_st_ref_get(v_a_527_);
v_env_534_ = lean_ctor_get(v___x_530_, 0);
lean_inc_ref(v_env_534_);
lean_dec(v___x_530_);
lean_inc(v_name_522_);
v___x_535_ = l_Lean_Meta_allowCompletion(v_env_534_, v_name_522_);
if (v___x_535_ == 0)
{
lean_dec_ref(v_c_523_);
lean_dec(v_name_522_);
goto v___jp_531_;
}
else
{
if (v___x_529_ == 0)
{
lean_object* v___x_536_; lean_object* v_env_540_; uint8_t v___x_541_; 
v___x_536_ = lean_st_ref_get(v_a_527_);
v_env_540_ = lean_ctor_get(v___x_536_, 0);
lean_inc_ref(v_env_540_);
lean_dec(v___x_536_);
lean_inc(v_name_522_);
v___x_541_ = l_Lean_Linter_isDeprecated(v_env_540_, v_name_522_);
if (v___x_541_ == 0)
{
lean_object* v___f_542_; lean_object* v___y_544_; lean_object* v___y_545_; lean_object* v___y_546_; lean_object* v___y_547_; 
lean_inc(v_name_522_);
v___f_542_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___boxed), 8, 1);
lean_closure_set(v___f_542_, 0, v_name_522_);
if (lean_obj_tag(v_name_522_) == 1)
{
lean_object* v_str_558_; uint8_t v___y_560_; lean_object* v___x_568_; uint8_t v___x_569_; 
v_str_558_ = lean_ctor_get(v_name_522_, 1);
v___x_568_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__2));
v___x_569_ = lean_string_dec_eq(v_str_558_, v___x_568_);
if (v___x_569_ == 0)
{
lean_object* v___x_570_; uint8_t v___x_571_; 
v___x_570_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__3));
v___x_571_ = lean_string_dec_eq(v_str_558_, v___x_570_);
if (v___x_571_ == 0)
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; uint8_t v___x_575_; 
v___x_572_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__4));
v___x_573_ = lean_string_utf8_byte_size(v_str_558_);
v___x_574_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__5, &l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__5_once, _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__5);
v___x_575_ = lean_nat_dec_le(v___x_574_, v___x_573_);
if (v___x_575_ == 0)
{
v___y_560_ = v___x_541_;
goto v___jp_559_;
}
else
{
lean_object* v___x_576_; lean_object* v___x_577_; uint8_t v___x_578_; 
v___x_576_ = lean_unsigned_to_nat(0u);
v___x_577_ = lean_nat_sub(v___x_573_, v___x_574_);
v___x_578_ = lean_string_memcmp(v_str_558_, v___x_572_, v___x_577_, v___x_576_, v___x_574_);
lean_dec(v___x_577_);
v___y_560_ = v___x_578_;
goto v___jp_559_;
}
}
else
{
lean_dec_ref_known(v_name_522_, 2);
lean_dec_ref(v___f_542_);
lean_dec_ref(v_c_523_);
goto v___jp_537_;
}
}
else
{
lean_dec_ref_known(v_name_522_, 2);
lean_dec_ref(v___f_542_);
lean_dec_ref(v_c_523_);
goto v___jp_537_;
}
v___jp_559_:
{
if (v___y_560_ == 0)
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; uint8_t v___x_564_; 
v___x_561_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__0));
v___x_562_ = lean_string_utf8_byte_size(v_str_558_);
v___x_563_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__1, &l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__1_once, _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__1);
v___x_564_ = lean_nat_dec_le(v___x_563_, v___x_562_);
if (v___x_564_ == 0)
{
v___y_544_ = v_a_524_;
v___y_545_ = v_a_525_;
v___y_546_ = v_a_526_;
v___y_547_ = v_a_527_;
goto v___jp_543_;
}
else
{
lean_object* v___x_565_; lean_object* v___x_566_; uint8_t v___x_567_; 
v___x_565_ = lean_unsigned_to_nat(0u);
v___x_566_ = lean_nat_sub(v___x_562_, v___x_563_);
v___x_567_ = lean_string_memcmp(v_str_558_, v___x_561_, v___x_566_, v___x_565_, v___x_563_);
lean_dec(v___x_566_);
if (v___x_567_ == 0)
{
v___y_544_ = v_a_524_;
v___y_545_ = v_a_525_;
v___y_546_ = v_a_526_;
v___y_547_ = v_a_527_;
goto v___jp_543_;
}
else
{
lean_dec_ref_known(v_name_522_, 2);
lean_dec_ref(v___f_542_);
lean_dec_ref(v_c_523_);
goto v___jp_537_;
}
}
}
else
{
lean_dec_ref_known(v_name_522_, 2);
lean_dec_ref(v___f_542_);
lean_dec_ref(v_c_523_);
goto v___jp_537_;
}
}
}
else
{
v___y_544_ = v_a_524_;
v___y_545_ = v_a_525_;
v___y_546_ = v_a_526_;
v___y_547_ = v_a_527_;
goto v___jp_543_;
}
v___jp_543_:
{
uint8_t v___x_548_; 
v___x_548_ = l_Lean_Name_isMetaprogramming(v_name_522_);
if (v___x_548_ == 0)
{
lean_object* v___x_549_; lean_object* v_type_550_; uint8_t v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___f_554_; lean_object* v___x_555_; 
v___x_549_ = l_Lean_AsyncConstantInfo_toConstantVal(v_c_523_);
v_type_550_ = lean_ctor_get(v___x_549_, 2);
lean_inc_ref(v_type_550_);
lean_dec_ref(v___x_549_);
v___x_551_ = 2;
v___x_552_ = lean_box(v___x_551_);
v___x_553_ = lean_box(v___x_548_);
v___f_554_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__1___boxed), 9, 4);
lean_closure_set(v___f_554_, 0, v___x_552_);
lean_closure_set(v___f_554_, 1, v_type_550_);
lean_closure_set(v___f_554_, 2, v___f_542_);
lean_closure_set(v___f_554_, 3, v___x_553_);
v___x_555_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1___redArg(v___f_554_, v___x_548_, v___y_544_, v___y_545_, v___y_546_, v___y_547_);
return v___x_555_;
}
else
{
lean_object* v___x_556_; lean_object* v___x_557_; 
lean_dec_ref(v___f_542_);
lean_dec_ref(v_c_523_);
v___x_556_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0));
v___x_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_557_, 0, v___x_556_);
return v___x_557_;
}
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
v___jp_537_:
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0));
v___x_539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_539_, 0, v___x_538_);
return v___x_539_;
}
}
else
{
lean_dec_ref(v_c_523_);
lean_dec(v_name_522_);
goto v___jp_531_;
}
}
v___jp_531_:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0));
v___x_533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_533_, 0, v___x_532_);
return v___x_533_;
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
lean_object* v_snd_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_755_; 
v_snd_737_ = lean_ctor_get(v_b_733_, 1);
v_isSharedCheck_755_ = !lean_is_exclusive(v_b_733_);
if (v_isSharedCheck_755_ == 0)
{
lean_object* v_unused_756_; 
v_unused_756_ = lean_ctor_get(v_b_733_, 0);
lean_dec(v_unused_756_);
v___x_739_ = v_b_733_;
v_isShared_740_ = v_isSharedCheck_755_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_snd_737_);
lean_dec(v_b_733_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_755_;
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
lean_object* v_val_751_; uint8_t v___x_752_; 
v_val_751_ = lean_ctor_get(v_a_750_, 0);
v___x_752_ = l_Lean_LocalDecl_isImplementationDetail(v_val_751_);
if (v___x_752_ == 0)
{
lean_object* v___x_753_; lean_object* v___x_754_; 
lean_inc(v_val_751_);
v___x_753_ = l_Lean_LocalDecl_toExpr(v_val_751_);
v___x_754_ = lean_array_push(v_snd_737_, v___x_753_);
v_a_743_ = v___x_754_;
goto v___jp_742_;
}
else
{
v_a_743_ = v_snd_737_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___redArg___boxed(lean_object* v_as_757_, lean_object* v_sz_758_, lean_object* v_i_759_, lean_object* v_b_760_, lean_object* v___y_761_){
_start:
{
size_t v_sz_boxed_762_; size_t v_i_boxed_763_; lean_object* v_res_764_; 
v_sz_boxed_762_ = lean_unbox_usize(v_sz_758_);
lean_dec(v_sz_758_);
v_i_boxed_763_ = lean_unbox_usize(v_i_759_);
lean_dec(v_i_759_);
v_res_764_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(v_as_757_, v_sz_boxed_762_, v_i_boxed_763_, v_b_760_);
lean_dec_ref(v_as_757_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5(lean_object* v_as_765_, size_t v_sz_766_, size_t v_i_767_, lean_object* v_b_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_){
_start:
{
uint8_t v___x_774_; 
v___x_774_ = lean_usize_dec_lt(v_i_767_, v_sz_766_);
if (v___x_774_ == 0)
{
lean_object* v___x_775_; 
v___x_775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_775_, 0, v_b_768_);
return v___x_775_;
}
else
{
lean_object* v_snd_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_794_; 
v_snd_776_ = lean_ctor_get(v_b_768_, 1);
v_isSharedCheck_794_ = !lean_is_exclusive(v_b_768_);
if (v_isSharedCheck_794_ == 0)
{
lean_object* v_unused_795_; 
v_unused_795_ = lean_ctor_get(v_b_768_, 0);
lean_dec(v_unused_795_);
v___x_778_ = v_b_768_;
v_isShared_779_ = v_isSharedCheck_794_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_snd_776_);
lean_dec(v_b_768_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_794_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_780_; lean_object* v_a_782_; lean_object* v_a_789_; 
v___x_780_ = lean_box(0);
v_a_789_ = lean_array_uget_borrowed(v_as_765_, v_i_767_);
if (lean_obj_tag(v_a_789_) == 0)
{
v_a_782_ = v_snd_776_;
goto v___jp_781_;
}
else
{
lean_object* v_val_790_; uint8_t v___x_791_; 
v_val_790_ = lean_ctor_get(v_a_789_, 0);
v___x_791_ = l_Lean_LocalDecl_isImplementationDetail(v_val_790_);
if (v___x_791_ == 0)
{
lean_object* v___x_792_; lean_object* v___x_793_; 
lean_inc(v_val_790_);
v___x_792_ = l_Lean_LocalDecl_toExpr(v_val_790_);
v___x_793_ = lean_array_push(v_snd_776_, v___x_792_);
v_a_782_ = v___x_793_;
goto v___jp_781_;
}
else
{
v_a_782_ = v_snd_776_;
goto v___jp_781_;
}
}
v___jp_781_:
{
lean_object* v___x_784_; 
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 1, v_a_782_);
lean_ctor_set(v___x_778_, 0, v___x_780_);
v___x_784_ = v___x_778_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v___x_780_);
lean_ctor_set(v_reuseFailAlloc_788_, 1, v_a_782_);
v___x_784_ = v_reuseFailAlloc_788_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
size_t v___x_785_; size_t v___x_786_; lean_object* v___x_787_; 
v___x_785_ = ((size_t)1ULL);
v___x_786_ = lean_usize_add(v_i_767_, v___x_785_);
v___x_787_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(v_as_765_, v_sz_766_, v___x_786_, v___x_784_);
return v___x_787_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5___boxed(lean_object* v_as_796_, lean_object* v_sz_797_, lean_object* v_i_798_, lean_object* v_b_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
size_t v_sz_boxed_805_; size_t v_i_boxed_806_; lean_object* v_res_807_; 
v_sz_boxed_805_ = lean_unbox_usize(v_sz_797_);
lean_dec(v_sz_797_);
v_i_boxed_806_ = lean_unbox_usize(v_i_798_);
lean_dec(v_i_798_);
v_res_807_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5(v_as_796_, v_sz_boxed_805_, v_i_boxed_806_, v_b_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec_ref(v_as_796_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2(lean_object* v_init_808_, lean_object* v_n_809_, lean_object* v_b_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_){
_start:
{
if (lean_obj_tag(v_n_809_) == 0)
{
lean_object* v_cs_816_; lean_object* v___x_817_; lean_object* v___x_818_; size_t v_sz_819_; size_t v___x_820_; lean_object* v___x_821_; 
v_cs_816_ = lean_ctor_get(v_n_809_, 0);
v___x_817_ = lean_box(0);
v___x_818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_818_, 0, v___x_817_);
lean_ctor_set(v___x_818_, 1, v_b_810_);
v_sz_819_ = lean_array_size(v_cs_816_);
v___x_820_ = ((size_t)0ULL);
v___x_821_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__4(v_init_808_, v_cs_816_, v_sz_819_, v___x_820_, v___x_818_, v___y_811_, v___y_812_, v___y_813_, v___y_814_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_836_; 
v_a_822_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_836_ == 0)
{
v___x_824_ = v___x_821_;
v_isShared_825_ = v_isSharedCheck_836_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_821_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_836_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v_fst_826_; 
v_fst_826_ = lean_ctor_get(v_a_822_, 0);
if (lean_obj_tag(v_fst_826_) == 0)
{
lean_object* v_snd_827_; lean_object* v___x_828_; lean_object* v___x_830_; 
v_snd_827_ = lean_ctor_get(v_a_822_, 1);
lean_inc(v_snd_827_);
lean_dec(v_a_822_);
v___x_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_828_, 0, v_snd_827_);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 0, v___x_828_);
v___x_830_ = v___x_824_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v___x_828_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
else
{
lean_object* v_val_832_; lean_object* v___x_834_; 
lean_inc_ref(v_fst_826_);
lean_dec(v_a_822_);
v_val_832_ = lean_ctor_get(v_fst_826_, 0);
lean_inc(v_val_832_);
lean_dec_ref_known(v_fst_826_, 1);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 0, v_val_832_);
v___x_834_ = v___x_824_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_val_832_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
}
else
{
lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_844_; 
v_a_837_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_844_ == 0)
{
v___x_839_ = v___x_821_;
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_dec(v___x_821_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_842_; 
if (v_isShared_840_ == 0)
{
v___x_842_ = v___x_839_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_a_837_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
}
else
{
lean_object* v_vs_845_; lean_object* v___x_846_; lean_object* v___x_847_; size_t v_sz_848_; size_t v___x_849_; lean_object* v___x_850_; 
v_vs_845_ = lean_ctor_get(v_n_809_, 0);
v___x_846_ = lean_box(0);
v___x_847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_847_, 0, v___x_846_);
lean_ctor_set(v___x_847_, 1, v_b_810_);
v_sz_848_ = lean_array_size(v_vs_845_);
v___x_849_ = ((size_t)0ULL);
v___x_850_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5(v_vs_845_, v_sz_848_, v___x_849_, v___x_847_, v___y_811_, v___y_812_, v___y_813_, v___y_814_);
if (lean_obj_tag(v___x_850_) == 0)
{
lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_865_; 
v_a_851_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_865_ == 0)
{
v___x_853_ = v___x_850_;
v_isShared_854_ = v_isSharedCheck_865_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v___x_850_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_865_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v_fst_855_; 
v_fst_855_ = lean_ctor_get(v_a_851_, 0);
if (lean_obj_tag(v_fst_855_) == 0)
{
lean_object* v_snd_856_; lean_object* v___x_857_; lean_object* v___x_859_; 
v_snd_856_ = lean_ctor_get(v_a_851_, 1);
lean_inc(v_snd_856_);
lean_dec(v_a_851_);
v___x_857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_857_, 0, v_snd_856_);
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 0, v___x_857_);
v___x_859_ = v___x_853_;
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
lean_object* v_val_861_; lean_object* v___x_863_; 
lean_inc_ref(v_fst_855_);
lean_dec(v_a_851_);
v_val_861_ = lean_ctor_get(v_fst_855_, 0);
lean_inc(v_val_861_);
lean_dec_ref_known(v_fst_855_, 1);
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 0, v_val_861_);
v___x_863_ = v___x_853_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_val_861_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
else
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_873_; 
v_a_866_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_873_ == 0)
{
v___x_868_ = v___x_850_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_850_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_871_; 
if (v_isShared_869_ == 0)
{
v___x_871_ = v___x_868_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_a_866_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__4(lean_object* v_init_874_, lean_object* v_as_875_, size_t v_sz_876_, size_t v_i_877_, lean_object* v_b_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
uint8_t v___x_884_; 
v___x_884_ = lean_usize_dec_lt(v_i_877_, v_sz_876_);
if (v___x_884_ == 0)
{
lean_object* v___x_885_; 
v___x_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_885_, 0, v_b_878_);
return v___x_885_;
}
else
{
lean_object* v_snd_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_920_; 
v_snd_886_ = lean_ctor_get(v_b_878_, 1);
v_isSharedCheck_920_ = !lean_is_exclusive(v_b_878_);
if (v_isSharedCheck_920_ == 0)
{
lean_object* v_unused_921_; 
v_unused_921_ = lean_ctor_get(v_b_878_, 0);
lean_dec(v_unused_921_);
v___x_888_ = v_b_878_;
v_isShared_889_ = v_isSharedCheck_920_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_snd_886_);
lean_dec(v_b_878_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_920_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v_a_890_; lean_object* v___x_891_; 
v_a_890_ = lean_array_uget_borrowed(v_as_875_, v_i_877_);
lean_inc(v_snd_886_);
v___x_891_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2(v_init_874_, v_a_890_, v_snd_886_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
if (lean_obj_tag(v___x_891_) == 0)
{
lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_911_; 
v_a_892_ = lean_ctor_get(v___x_891_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_911_ == 0)
{
v___x_894_ = v___x_891_;
v_isShared_895_ = v_isSharedCheck_911_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_891_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_911_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
if (lean_obj_tag(v_a_892_) == 0)
{
lean_object* v___x_896_; lean_object* v___x_898_; 
v___x_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_896_, 0, v_a_892_);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 0, v___x_896_);
v___x_898_ = v___x_888_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v___x_896_);
lean_ctor_set(v_reuseFailAlloc_902_, 1, v_snd_886_);
v___x_898_ = v_reuseFailAlloc_902_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
lean_object* v___x_900_; 
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 0, v___x_898_);
v___x_900_ = v___x_894_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v___x_898_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
else
{
lean_object* v_a_903_; lean_object* v___x_904_; lean_object* v___x_906_; 
lean_del_object(v___x_894_);
lean_dec(v_snd_886_);
v_a_903_ = lean_ctor_get(v_a_892_, 0);
lean_inc(v_a_903_);
lean_dec_ref_known(v_a_892_, 1);
v___x_904_ = lean_box(0);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 1, v_a_903_);
lean_ctor_set(v___x_888_, 0, v___x_904_);
v___x_906_ = v___x_888_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v___x_904_);
lean_ctor_set(v_reuseFailAlloc_910_, 1, v_a_903_);
v___x_906_ = v_reuseFailAlloc_910_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
size_t v___x_907_; size_t v___x_908_; 
v___x_907_ = ((size_t)1ULL);
v___x_908_ = lean_usize_add(v_i_877_, v___x_907_);
v_i_877_ = v___x_908_;
v_b_878_ = v___x_906_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_919_; 
lean_del_object(v___x_888_);
lean_dec(v_snd_886_);
v_a_912_ = lean_ctor_get(v___x_891_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_919_ == 0)
{
v___x_914_ = v___x_891_;
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_891_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_917_; 
if (v_isShared_915_ == 0)
{
v___x_917_ = v___x_914_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_a_912_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_init_922_, lean_object* v_as_923_, lean_object* v_sz_924_, lean_object* v_i_925_, lean_object* v_b_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
size_t v_sz_boxed_932_; size_t v_i_boxed_933_; lean_object* v_res_934_; 
v_sz_boxed_932_ = lean_unbox_usize(v_sz_924_);
lean_dec(v_sz_924_);
v_i_boxed_933_ = lean_unbox_usize(v_i_925_);
lean_dec(v_i_925_);
v_res_934_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__4(v_init_922_, v_as_923_, v_sz_boxed_932_, v_i_boxed_933_, v_b_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
lean_dec_ref(v_as_923_);
lean_dec_ref(v_init_922_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2___boxed(lean_object* v_init_935_, lean_object* v_n_936_, lean_object* v_b_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2(v_init_935_, v_n_936_, v_b_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec_ref(v_n_936_);
lean_dec_ref(v_init_935_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___redArg(lean_object* v_as_944_, size_t v_sz_945_, size_t v_i_946_, lean_object* v_b_947_){
_start:
{
uint8_t v___x_949_; 
v___x_949_ = lean_usize_dec_lt(v_i_946_, v_sz_945_);
if (v___x_949_ == 0)
{
lean_object* v___x_950_; 
v___x_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_950_, 0, v_b_947_);
return v___x_950_;
}
else
{
lean_object* v_snd_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_969_; 
v_snd_951_ = lean_ctor_get(v_b_947_, 1);
v_isSharedCheck_969_ = !lean_is_exclusive(v_b_947_);
if (v_isSharedCheck_969_ == 0)
{
lean_object* v_unused_970_; 
v_unused_970_ = lean_ctor_get(v_b_947_, 0);
lean_dec(v_unused_970_);
v___x_953_ = v_b_947_;
v_isShared_954_ = v_isSharedCheck_969_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_snd_951_);
lean_dec(v_b_947_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_969_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_955_; lean_object* v_a_957_; lean_object* v_a_964_; 
v___x_955_ = lean_box(0);
v_a_964_ = lean_array_uget_borrowed(v_as_944_, v_i_946_);
if (lean_obj_tag(v_a_964_) == 0)
{
v_a_957_ = v_snd_951_;
goto v___jp_956_;
}
else
{
lean_object* v_val_965_; uint8_t v___x_966_; 
v_val_965_ = lean_ctor_get(v_a_964_, 0);
v___x_966_ = l_Lean_LocalDecl_isImplementationDetail(v_val_965_);
if (v___x_966_ == 0)
{
lean_object* v___x_967_; lean_object* v___x_968_; 
lean_inc(v_val_965_);
v___x_967_ = l_Lean_LocalDecl_toExpr(v_val_965_);
v___x_968_ = lean_array_push(v_snd_951_, v___x_967_);
v_a_957_ = v___x_968_;
goto v___jp_956_;
}
else
{
v_a_957_ = v_snd_951_;
goto v___jp_956_;
}
}
v___jp_956_:
{
lean_object* v___x_959_; 
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 1, v_a_957_);
lean_ctor_set(v___x_953_, 0, v___x_955_);
v___x_959_ = v___x_953_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v___x_955_);
lean_ctor_set(v_reuseFailAlloc_963_, 1, v_a_957_);
v___x_959_ = v_reuseFailAlloc_963_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
size_t v___x_960_; size_t v___x_961_; 
v___x_960_ = ((size_t)1ULL);
v___x_961_ = lean_usize_add(v_i_946_, v___x_960_);
v_i_946_ = v___x_961_;
v_b_947_ = v___x_959_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_as_971_, lean_object* v_sz_972_, lean_object* v_i_973_, lean_object* v_b_974_, lean_object* v___y_975_){
_start:
{
size_t v_sz_boxed_976_; size_t v_i_boxed_977_; lean_object* v_res_978_; 
v_sz_boxed_976_ = lean_unbox_usize(v_sz_972_);
lean_dec(v_sz_972_);
v_i_boxed_977_ = lean_unbox_usize(v_i_973_);
lean_dec(v_i_973_);
v_res_978_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___redArg(v_as_971_, v_sz_boxed_976_, v_i_boxed_977_, v_b_974_);
lean_dec_ref(v_as_971_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3(lean_object* v_as_979_, size_t v_sz_980_, size_t v_i_981_, lean_object* v_b_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
uint8_t v___x_988_; 
v___x_988_ = lean_usize_dec_lt(v_i_981_, v_sz_980_);
if (v___x_988_ == 0)
{
lean_object* v___x_989_; 
v___x_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_989_, 0, v_b_982_);
return v___x_989_;
}
else
{
lean_object* v_snd_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1008_; 
v_snd_990_ = lean_ctor_get(v_b_982_, 1);
v_isSharedCheck_1008_ = !lean_is_exclusive(v_b_982_);
if (v_isSharedCheck_1008_ == 0)
{
lean_object* v_unused_1009_; 
v_unused_1009_ = lean_ctor_get(v_b_982_, 0);
lean_dec(v_unused_1009_);
v___x_992_ = v_b_982_;
v_isShared_993_ = v_isSharedCheck_1008_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_snd_990_);
lean_dec(v_b_982_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1008_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_994_; lean_object* v_a_996_; lean_object* v_a_1003_; 
v___x_994_ = lean_box(0);
v_a_1003_ = lean_array_uget_borrowed(v_as_979_, v_i_981_);
if (lean_obj_tag(v_a_1003_) == 0)
{
v_a_996_ = v_snd_990_;
goto v___jp_995_;
}
else
{
lean_object* v_val_1004_; uint8_t v___x_1005_; 
v_val_1004_ = lean_ctor_get(v_a_1003_, 0);
v___x_1005_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1004_);
if (v___x_1005_ == 0)
{
lean_object* v___x_1006_; lean_object* v___x_1007_; 
lean_inc(v_val_1004_);
v___x_1006_ = l_Lean_LocalDecl_toExpr(v_val_1004_);
v___x_1007_ = lean_array_push(v_snd_990_, v___x_1006_);
v_a_996_ = v___x_1007_;
goto v___jp_995_;
}
else
{
v_a_996_ = v_snd_990_;
goto v___jp_995_;
}
}
v___jp_995_:
{
lean_object* v___x_998_; 
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 1, v_a_996_);
lean_ctor_set(v___x_992_, 0, v___x_994_);
v___x_998_ = v___x_992_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v___x_994_);
lean_ctor_set(v_reuseFailAlloc_1002_, 1, v_a_996_);
v___x_998_ = v_reuseFailAlloc_1002_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
size_t v___x_999_; size_t v___x_1000_; lean_object* v___x_1001_; 
v___x_999_ = ((size_t)1ULL);
v___x_1000_ = lean_usize_add(v_i_981_, v___x_999_);
v___x_1001_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___redArg(v_as_979_, v_sz_980_, v___x_1000_, v___x_998_);
return v___x_1001_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3___boxed(lean_object* v_as_1010_, lean_object* v_sz_1011_, lean_object* v_i_1012_, lean_object* v_b_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
size_t v_sz_boxed_1019_; size_t v_i_boxed_1020_; lean_object* v_res_1021_; 
v_sz_boxed_1019_ = lean_unbox_usize(v_sz_1011_);
lean_dec(v_sz_1011_);
v_i_boxed_1020_ = lean_unbox_usize(v_i_1012_);
lean_dec(v_i_1012_);
v_res_1021_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3(v_as_1010_, v_sz_boxed_1019_, v_i_boxed_1020_, v_b_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec_ref(v_as_1010_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1(lean_object* v_t_1022_, lean_object* v_init_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_){
_start:
{
lean_object* v_root_1029_; lean_object* v_tail_1030_; lean_object* v___x_1031_; 
v_root_1029_ = lean_ctor_get(v_t_1022_, 0);
v_tail_1030_ = lean_ctor_get(v_t_1022_, 1);
lean_inc_ref(v_init_1023_);
v___x_1031_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2(v_init_1023_, v_root_1029_, v_init_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
lean_dec_ref(v_init_1023_);
if (lean_obj_tag(v___x_1031_) == 0)
{
lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1068_; 
v_a_1032_ = lean_ctor_get(v___x_1031_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1034_ = v___x_1031_;
v_isShared_1035_ = v_isSharedCheck_1068_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_1031_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1068_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
if (lean_obj_tag(v_a_1032_) == 0)
{
lean_object* v_a_1036_; lean_object* v___x_1038_; 
v_a_1036_ = lean_ctor_get(v_a_1032_, 0);
lean_inc(v_a_1036_);
lean_dec_ref_known(v_a_1032_, 1);
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 0, v_a_1036_);
v___x_1038_ = v___x_1034_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_a_1036_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
else
{
lean_object* v_a_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; size_t v_sz_1043_; size_t v___x_1044_; lean_object* v___x_1045_; 
lean_del_object(v___x_1034_);
v_a_1040_ = lean_ctor_get(v_a_1032_, 0);
lean_inc(v_a_1040_);
lean_dec_ref_known(v_a_1032_, 1);
v___x_1041_ = lean_box(0);
v___x_1042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1041_);
lean_ctor_set(v___x_1042_, 1, v_a_1040_);
v_sz_1043_ = lean_array_size(v_tail_1030_);
v___x_1044_ = ((size_t)0ULL);
v___x_1045_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3(v_tail_1030_, v_sz_1043_, v___x_1044_, v___x_1042_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_object* v_a_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1059_; 
v_a_1046_ = lean_ctor_get(v___x_1045_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1048_ = v___x_1045_;
v_isShared_1049_ = v_isSharedCheck_1059_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_a_1046_);
lean_dec(v___x_1045_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1059_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v_fst_1050_; 
v_fst_1050_ = lean_ctor_get(v_a_1046_, 0);
if (lean_obj_tag(v_fst_1050_) == 0)
{
lean_object* v_snd_1051_; lean_object* v___x_1053_; 
v_snd_1051_ = lean_ctor_get(v_a_1046_, 1);
lean_inc(v_snd_1051_);
lean_dec(v_a_1046_);
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 0, v_snd_1051_);
v___x_1053_ = v___x_1048_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_snd_1051_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
else
{
lean_object* v_val_1055_; lean_object* v___x_1057_; 
lean_inc_ref(v_fst_1050_);
lean_dec(v_a_1046_);
v_val_1055_ = lean_ctor_get(v_fst_1050_, 0);
lean_inc(v_val_1055_);
lean_dec_ref_known(v_fst_1050_, 1);
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 0, v_val_1055_);
v___x_1057_ = v___x_1048_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_val_1055_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
else
{
lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1067_; 
v_a_1060_ = lean_ctor_get(v___x_1045_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1062_ = v___x_1045_;
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_dec(v___x_1045_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1065_; 
if (v_isShared_1063_ == 0)
{
v___x_1065_ = v___x_1062_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_a_1060_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
}
}
}
else
{
lean_object* v_a_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1076_; 
v_a_1069_ = lean_ctor_get(v___x_1031_, 0);
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1071_ = v___x_1031_;
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_a_1069_);
lean_dec(v___x_1031_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1074_; 
if (v_isShared_1072_ == 0)
{
v___x_1074_ = v___x_1071_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_a_1069_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1___boxed(lean_object* v_t_1077_, lean_object* v_init_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1(v_t_1077_, v_init_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec_ref(v_t_1077_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1(lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
lean_object* v_lctx_1092_; lean_object* v_decls_1093_; lean_object* v_hs_1094_; lean_object* v___x_1095_; 
v_lctx_1092_ = lean_ctor_get(v___y_1087_, 2);
v_decls_1093_ = lean_ctor_get(v_lctx_1092_, 1);
v_hs_1094_ = ((lean_object*)(l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1___closed__0));
v___x_1095_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1(v_decls_1093_, v_hs_1094_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1___boxed(lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1(v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_localHypotheses(lean_object* v_except_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_){
_start:
{
lean_object* v___x_1110_; 
v___x_1110_ = l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1(v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_object* v_a_1111_; lean_object* v___x_1112_; size_t v_sz_1113_; size_t v___x_1114_; lean_object* v___x_1115_; 
v_a_1111_ = lean_ctor_get(v___x_1110_, 0);
lean_inc(v_a_1111_);
lean_dec_ref_known(v___x_1110_, 1);
v___x_1112_ = ((lean_object*)(l_Lean_Meta_Rewrites_localHypotheses___closed__0));
v_sz_1113_ = lean_array_size(v_a_1111_);
v___x_1114_ = ((size_t)0ULL);
v___x_1115_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_localHypotheses_spec__2(v_except_1104_, v_a_1111_, v_sz_1113_, v___x_1114_, v___x_1112_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_);
lean_dec(v_a_1111_);
return v___x_1115_;
}
else
{
lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1123_; 
v_a_1116_ = lean_ctor_get(v___x_1110_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1118_ = v___x_1110_;
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1110_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1121_; 
if (v_isShared_1119_ == 0)
{
v___x_1121_ = v___x_1118_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_a_1116_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_localHypotheses___boxed(lean_object* v_except_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l_Lean_Meta_Rewrites_localHypotheses(v_except_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_);
lean_dec(v_a_1128_);
lean_dec_ref(v_a_1127_);
lean_dec(v_a_1126_);
lean_dec_ref(v_a_1125_);
lean_dec(v_except_1124_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7(lean_object* v_as_1131_, size_t v_sz_1132_, size_t v_i_1133_, lean_object* v_b_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v___x_1140_; 
v___x_1140_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___redArg(v_as_1131_, v_sz_1132_, v_i_1133_, v_b_1134_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___boxed(lean_object* v_as_1141_, lean_object* v_sz_1142_, lean_object* v_i_1143_, lean_object* v_b_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
size_t v_sz_boxed_1150_; size_t v_i_boxed_1151_; lean_object* v_res_1152_; 
v_sz_boxed_1150_ = lean_unbox_usize(v_sz_1142_);
lean_dec(v_sz_1142_);
v_i_boxed_1151_ = lean_unbox_usize(v_i_1143_);
lean_dec(v_i_1143_);
v_res_1152_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7(v_as_1141_, v_sz_boxed_1150_, v_i_boxed_1151_, v_b_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_);
lean_dec(v___y_1148_);
lean_dec_ref(v___y_1147_);
lean_dec(v___y_1146_);
lean_dec_ref(v___y_1145_);
lean_dec_ref(v_as_1141_);
return v_res_1152_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6(lean_object* v_as_1153_, size_t v_sz_1154_, size_t v_i_1155_, lean_object* v_b_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v___x_1162_; 
v___x_1162_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(v_as_1153_, v_sz_1154_, v_i_1155_, v_b_1156_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___boxed(lean_object* v_as_1163_, lean_object* v_sz_1164_, lean_object* v_i_1165_, lean_object* v_b_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
size_t v_sz_boxed_1172_; size_t v_i_boxed_1173_; lean_object* v_res_1174_; 
v_sz_boxed_1172_ = lean_unbox_usize(v_sz_1164_);
lean_dec(v_sz_1164_);
v_i_boxed_1173_ = lean_unbox_usize(v_i_1165_);
lean_dec(v_i_1165_);
v_res_1174_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6(v_as_1163_, v_sz_boxed_1172_, v_i_boxed_1173_, v_b_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
lean_dec_ref(v_as_1163_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_createModuleTreeRef(lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_){
_start:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1205_ = ((lean_object*)(l_Lean_Meta_Rewrites_createModuleTreeRef___closed__0));
v___x_1206_ = ((lean_object*)(l_Lean_Meta_Rewrites_droppedKeys));
v___x_1207_ = lean_box(0);
v___x_1208_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v___x_1205_, v___x_1206_, v___x_1207_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_createModuleTreeRef___boxed(lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l_Lean_Meta_Rewrites_createModuleTreeRef(v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_);
lean_dec(v_a_1212_);
lean_dec_ref(v_a_1211_);
lean_dec(v_a_1210_);
lean_dec_ref(v_a_1209_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_1824551397____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1216_ = lean_box(0);
v___x_1217_ = lean_st_mk_ref(v___x_1216_);
v___x_1218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1217_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_1824551397____hygCtx___hyg_2____boxed(lean_object* v_a_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_1824551397____hygCtx___hyg_2_();
return v_res_1220_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_constantsPerImportTask(void){
_start:
{
lean_object* v___x_1221_; 
v___x_1221_ = lean_unsigned_to_nat(6500u);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_incPrio(lean_object* v_x_1222_, lean_object* v_x_1223_){
_start:
{
lean_object* v_snd_1224_; uint8_t v___x_1225_; 
v_snd_1224_ = lean_ctor_get(v_x_1223_, 1);
v___x_1225_ = lean_unbox(v_snd_1224_);
if (v___x_1225_ == 0)
{
lean_object* v_fst_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1238_; 
v_fst_1226_ = lean_ctor_get(v_x_1223_, 0);
v_isSharedCheck_1238_ = !lean_is_exclusive(v_x_1223_);
if (v_isSharedCheck_1238_ == 0)
{
lean_object* v_unused_1239_; 
v_unused_1239_ = lean_ctor_get(v_x_1223_, 1);
lean_dec(v_unused_1239_);
v___x_1228_ = v_x_1223_;
v_isShared_1229_ = v_isSharedCheck_1238_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_fst_1226_);
lean_dec(v_x_1223_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1238_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
uint8_t v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1235_; 
v___x_1230_ = 0;
v___x_1231_ = lean_unsigned_to_nat(2u);
v___x_1232_ = lean_nat_mul(v___x_1231_, v_x_1222_);
lean_dec(v_x_1222_);
v___x_1233_ = lean_box(v___x_1230_);
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 1, v___x_1232_);
lean_ctor_set(v___x_1228_, 0, v___x_1233_);
v___x_1235_ = v___x_1228_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v___x_1233_);
lean_ctor_set(v_reuseFailAlloc_1237_, 1, v___x_1232_);
v___x_1235_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
lean_object* v___x_1236_; 
v___x_1236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1236_, 0, v_fst_1226_);
lean_ctor_set(v___x_1236_, 1, v___x_1235_);
return v___x_1236_;
}
}
}
else
{
lean_object* v_fst_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1250_; 
v_fst_1240_ = lean_ctor_get(v_x_1223_, 0);
v_isSharedCheck_1250_ = !lean_is_exclusive(v_x_1223_);
if (v_isSharedCheck_1250_ == 0)
{
lean_object* v_unused_1251_; 
v_unused_1251_ = lean_ctor_get(v_x_1223_, 1);
lean_dec(v_unused_1251_);
v___x_1242_ = v_x_1223_;
v_isShared_1243_ = v_isSharedCheck_1250_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_fst_1240_);
lean_dec(v_x_1223_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1250_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
uint8_t v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1247_; 
v___x_1244_ = 1;
v___x_1245_ = lean_box(v___x_1244_);
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 1, v_x_1222_);
lean_ctor_set(v___x_1242_, 0, v___x_1245_);
v___x_1247_ = v___x_1242_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v___x_1245_);
lean_ctor_set(v_reuseFailAlloc_1249_, 1, v_x_1222_);
v___x_1247_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
lean_object* v___x_1248_; 
v___x_1248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1248_, 0, v_fst_1240_);
lean_ctor_set(v___x_1248_, 1, v___x_1247_);
return v___x_1248_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwFindDecls(lean_object* v_moduleRef_1253_, lean_object* v_ty_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_){
_start:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1260_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_ext;
v___x_1261_ = ((lean_object*)(l_Lean_Meta_Rewrites_createModuleTreeRef___closed__0));
v___x_1262_ = ((lean_object*)(l_Lean_Meta_Rewrites_droppedKeys));
v___x_1263_ = lean_unsigned_to_nat(6500u);
v___x_1264_ = lean_box(0);
v___x_1265_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwFindDecls___closed__0));
v___x_1266_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_moduleRef_1253_, v___x_1260_, v___x_1261_, v___x_1262_, v___x_1263_, v___x_1264_, v___x_1265_, v_ty_1254_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwFindDecls___boxed(lean_object* v_moduleRef_1267_, lean_object* v_ty_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_){
_start:
{
lean_object* v_res_1274_; 
v_res_1274_ = l_Lean_Meta_Rewrites_rwFindDecls(v_moduleRef_1267_, v_ty_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
lean_dec(v_a_1272_);
lean_dec_ref(v_a_1271_);
lean_dec(v_a_1270_);
lean_dec_ref(v_a_1269_);
return v_res_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg(lean_object* v_mctx_1275_, lean_object* v_x_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v___x_1282_; 
v___x_1282_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp(lean_box(0), v_mctx_1275_, v_x_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1290_; 
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1285_ = v___x_1282_;
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1282_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1288_; 
if (v_isShared_1286_ == 0)
{
v___x_1288_ = v___x_1285_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_a_1283_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
else
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
v_a_1291_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1293_ = v___x_1282_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1282_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_a_1291_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg___boxed(lean_object* v_mctx_1299_, lean_object* v_x_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg(v_mctx_1299_, v_x_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
lean_dec(v___y_1302_);
lean_dec_ref(v___y_1301_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0(lean_object* v_00_u03b1_1307_, lean_object* v_mctx_1308_, lean_object* v_x_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_){
_start:
{
lean_object* v___x_1315_; 
v___x_1315_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg(v_mctx_1308_, v_x_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___boxed(lean_object* v_00_u03b1_1316_, lean_object* v_mctx_1317_, lean_object* v_x_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_){
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0(v_00_u03b1_1316_, v_mctx_1317_, v_x_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_);
lean_dec(v___y_1322_);
lean_dec_ref(v___y_1321_);
lean_dec(v___y_1320_);
lean_dec_ref(v___y_1319_);
return v_res_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(lean_object* v_x_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
lean_object* v___x_1331_; 
v___x_1331_ = l_Lean_Meta_saveState___redArg(v___y_1327_, v___y_1329_);
if (lean_obj_tag(v___x_1331_) == 0)
{
lean_object* v_a_1332_; lean_object* v_r_1333_; 
v_a_1332_ = lean_ctor_get(v___x_1331_, 0);
lean_inc(v_a_1332_);
lean_dec_ref_known(v___x_1331_, 1);
lean_inc(v___y_1329_);
lean_inc_ref(v___y_1328_);
lean_inc(v___y_1327_);
lean_inc_ref(v___y_1326_);
v_r_1333_ = lean_apply_5(v_x_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, lean_box(0));
if (lean_obj_tag(v_r_1333_) == 0)
{
lean_object* v_a_1334_; lean_object* v___x_1335_; 
v_a_1334_ = lean_ctor_get(v_r_1333_, 0);
lean_inc(v_a_1334_);
lean_dec_ref_known(v_r_1333_, 1);
v___x_1335_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1332_, v___y_1327_, v___y_1329_);
lean_dec(v_a_1332_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1342_; 
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1342_ == 0)
{
lean_object* v_unused_1343_; 
v_unused_1343_ = lean_ctor_get(v___x_1335_, 0);
lean_dec(v_unused_1343_);
v___x_1337_ = v___x_1335_;
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
else
{
lean_dec(v___x_1335_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1340_; 
if (v_isShared_1338_ == 0)
{
lean_ctor_set(v___x_1337_, 0, v_a_1334_);
v___x_1340_ = v___x_1337_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_a_1334_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
}
else
{
lean_object* v_a_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1351_; 
lean_dec(v_a_1334_);
v_a_1344_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1346_ = v___x_1335_;
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_a_1344_);
lean_dec(v___x_1335_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1349_; 
if (v_isShared_1347_ == 0)
{
v___x_1349_ = v___x_1346_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_a_1344_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
}
}
else
{
lean_object* v_a_1352_; lean_object* v___x_1353_; 
v_a_1352_ = lean_ctor_get(v_r_1333_, 0);
lean_inc(v_a_1352_);
lean_dec_ref_known(v_r_1333_, 1);
v___x_1353_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1332_, v___y_1327_, v___y_1329_);
lean_dec(v_a_1332_);
if (lean_obj_tag(v___x_1353_) == 0)
{
lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1360_; 
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1353_);
if (v_isSharedCheck_1360_ == 0)
{
lean_object* v_unused_1361_; 
v_unused_1361_ = lean_ctor_get(v___x_1353_, 0);
lean_dec(v_unused_1361_);
v___x_1355_ = v___x_1353_;
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
else
{
lean_dec(v___x_1353_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1358_; 
if (v_isShared_1356_ == 0)
{
lean_ctor_set_tag(v___x_1355_, 1);
lean_ctor_set(v___x_1355_, 0, v_a_1352_);
v___x_1358_ = v___x_1355_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_a_1352_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
else
{
lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1369_; 
lean_dec(v_a_1352_);
v_a_1362_ = lean_ctor_get(v___x_1353_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1353_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1364_ = v___x_1353_;
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1353_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1367_; 
if (v_isShared_1365_ == 0)
{
v___x_1367_ = v___x_1364_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_a_1362_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
}
}
else
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
lean_dec_ref(v_x_1325_);
v_a_1370_ = lean_ctor_get(v___x_1331_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1372_ = v___x_1331_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1331_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1375_; 
if (v_isShared_1373_ == 0)
{
v___x_1375_ = v___x_1372_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_a_1370_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg___boxed(lean_object* v_x_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v_x_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
lean_dec(v___y_1380_);
lean_dec_ref(v___y_1379_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1(lean_object* v_00_u03b1_1385_, lean_object* v_x_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
lean_object* v___x_1392_; 
v___x_1392_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v_x_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___boxed(lean_object* v_00_u03b1_1393_, lean_object* v_x_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_){
_start:
{
lean_object* v_res_1400_; 
v_res_1400_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1(v_00_u03b1_1393_, v_x_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_);
lean_dec(v___y_1398_);
lean_dec_ref(v___y_1397_);
lean_dec(v___y_1396_);
lean_dec_ref(v___y_1395_);
return v_res_1400_;
}
}
static uint64_t _init_l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___closed__0(void){
_start:
{
uint8_t v___x_1401_; uint64_t v___x_1402_; 
v___x_1401_ = 2;
v___x_1402_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_1401_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0(lean_object* v___x_1403_, uint8_t v___x_1404_, lean_object* v___x_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
lean_object* v___x_1411_; 
v___x_1411_ = l_Lean_Meta_mkFreshExprMVar(v___x_1403_, v___x_1404_, v___x_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_);
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_object* v_a_1412_; lean_object* v___x_1413_; uint8_t v_foApprox_1414_; uint8_t v_ctxApprox_1415_; uint8_t v_quasiPatternApprox_1416_; uint8_t v_constApprox_1417_; uint8_t v_isDefEqStuckEx_1418_; uint8_t v_unificationHints_1419_; uint8_t v_proofIrrelevance_1420_; uint8_t v_assignSyntheticOpaque_1421_; uint8_t v_offsetCnstrs_1422_; uint8_t v_etaStruct_1423_; uint8_t v_univApprox_1424_; uint8_t v_iota_1425_; uint8_t v_beta_1426_; uint8_t v_proj_1427_; uint8_t v_zeta_1428_; uint8_t v_zetaDelta_1429_; uint8_t v_zetaUnused_1430_; uint8_t v_zetaHave_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1490_; 
v_a_1412_ = lean_ctor_get(v___x_1411_, 0);
lean_inc(v_a_1412_);
lean_dec_ref_known(v___x_1411_, 1);
v___x_1413_ = l_Lean_Meta_Context_config(v___y_1406_);
v_foApprox_1414_ = lean_ctor_get_uint8(v___x_1413_, 0);
v_ctxApprox_1415_ = lean_ctor_get_uint8(v___x_1413_, 1);
v_quasiPatternApprox_1416_ = lean_ctor_get_uint8(v___x_1413_, 2);
v_constApprox_1417_ = lean_ctor_get_uint8(v___x_1413_, 3);
v_isDefEqStuckEx_1418_ = lean_ctor_get_uint8(v___x_1413_, 4);
v_unificationHints_1419_ = lean_ctor_get_uint8(v___x_1413_, 5);
v_proofIrrelevance_1420_ = lean_ctor_get_uint8(v___x_1413_, 6);
v_assignSyntheticOpaque_1421_ = lean_ctor_get_uint8(v___x_1413_, 7);
v_offsetCnstrs_1422_ = lean_ctor_get_uint8(v___x_1413_, 8);
v_etaStruct_1423_ = lean_ctor_get_uint8(v___x_1413_, 10);
v_univApprox_1424_ = lean_ctor_get_uint8(v___x_1413_, 11);
v_iota_1425_ = lean_ctor_get_uint8(v___x_1413_, 12);
v_beta_1426_ = lean_ctor_get_uint8(v___x_1413_, 13);
v_proj_1427_ = lean_ctor_get_uint8(v___x_1413_, 14);
v_zeta_1428_ = lean_ctor_get_uint8(v___x_1413_, 15);
v_zetaDelta_1429_ = lean_ctor_get_uint8(v___x_1413_, 16);
v_zetaUnused_1430_ = lean_ctor_get_uint8(v___x_1413_, 17);
v_zetaHave_1431_ = lean_ctor_get_uint8(v___x_1413_, 18);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1433_ = v___x_1413_;
v_isShared_1434_ = v_isSharedCheck_1490_;
goto v_resetjp_1432_;
}
else
{
lean_dec(v___x_1413_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1490_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
uint8_t v_trackZetaDelta_1435_; lean_object* v_zetaDeltaSet_1436_; lean_object* v_lctx_1437_; lean_object* v_localInstances_1438_; lean_object* v_defEqCtx_x3f_1439_; lean_object* v_synthPendingDepth_1440_; lean_object* v_canUnfold_x3f_1441_; uint8_t v_univApprox_1442_; uint8_t v_inTypeClassResolution_1443_; uint8_t v_cacheInferType_1444_; uint8_t v___x_1445_; lean_object* v_config_1447_; 
v_trackZetaDelta_1435_ = lean_ctor_get_uint8(v___y_1406_, sizeof(void*)*7);
v_zetaDeltaSet_1436_ = lean_ctor_get(v___y_1406_, 1);
lean_inc(v_zetaDeltaSet_1436_);
v_lctx_1437_ = lean_ctor_get(v___y_1406_, 2);
lean_inc_ref(v_lctx_1437_);
v_localInstances_1438_ = lean_ctor_get(v___y_1406_, 3);
lean_inc_ref(v_localInstances_1438_);
v_defEqCtx_x3f_1439_ = lean_ctor_get(v___y_1406_, 4);
lean_inc(v_defEqCtx_x3f_1439_);
v_synthPendingDepth_1440_ = lean_ctor_get(v___y_1406_, 5);
lean_inc(v_synthPendingDepth_1440_);
v_canUnfold_x3f_1441_ = lean_ctor_get(v___y_1406_, 6);
lean_inc(v_canUnfold_x3f_1441_);
v_univApprox_1442_ = lean_ctor_get_uint8(v___y_1406_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1443_ = lean_ctor_get_uint8(v___y_1406_, sizeof(void*)*7 + 2);
v_cacheInferType_1444_ = lean_ctor_get_uint8(v___y_1406_, sizeof(void*)*7 + 3);
v___x_1445_ = 2;
if (v_isShared_1434_ == 0)
{
v_config_1447_ = v___x_1433_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1489_, 0, v_foApprox_1414_);
lean_ctor_set_uint8(v_reuseFailAlloc_1489_, 1, v_ctxApprox_1415_);
lean_ctor_set_uint8(v_reuseFailAlloc_1489_, 2, v_quasiPatternApprox_1416_);
lean_ctor_set_uint8(v_reuseFailAlloc_1489_, 3, v_constApprox_1417_);
lean_ctor_set_uint8(v_reuseFailAlloc_1489_, 4, v_isDefEqStuckEx_1418_);
lean_ctor_set_uint8(v_reuseFailAlloc_1489_, 5, v_unificationHints_1419_);
lean_ctor_set_uint8(v_reuseFailAlloc_1489_, 6, v_proofIrrelevance_1420_);
lean_ctor_set_uint8(v_reuseFailAlloc_1489_, 7, v_assignSyntheticOpaque_1421_);
lean_ctor_set_uint8(v_reuseFailAlloc_1489_, 8, v_offsetCnstrs_1422_);
lean_ctor_set_uint8(v_reuseFailAlloc_1489_, 10, v_etaStruct_1423_);
lean_ctor_set_uint8(v_reuseFailAlloc_1489_, 11, v_univApprox_1424_);
lean_ctor_set_uint8(v_reuseFailAlloc_1489_, 12, v_iota_1425_);
lean_ctor_set_uint8(v_reuseFailAlloc_1489_, 13, v_beta_1426_);
lean_ctor_set_uint8(v_reuseFailAlloc_1489_, 14, v_proj_1427_);
lean_ctor_set_uint8(v_reuseFailAlloc_1489_, 15, v_zeta_1428_);
lean_ctor_set_uint8(v_reuseFailAlloc_1489_, 16, v_zetaDelta_1429_);
lean_ctor_set_uint8(v_reuseFailAlloc_1489_, 17, v_zetaUnused_1430_);
lean_ctor_set_uint8(v_reuseFailAlloc_1489_, 18, v_zetaHave_1431_);
v_config_1447_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
uint64_t v___x_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1481_; 
lean_ctor_set_uint8(v_config_1447_, 9, v___x_1445_);
v___x_1448_ = l_Lean_Meta_Context_configKey(v___y_1406_);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___y_1406_);
if (v_isSharedCheck_1481_ == 0)
{
lean_object* v_unused_1482_; lean_object* v_unused_1483_; lean_object* v_unused_1484_; lean_object* v_unused_1485_; lean_object* v_unused_1486_; lean_object* v_unused_1487_; lean_object* v_unused_1488_; 
v_unused_1482_ = lean_ctor_get(v___y_1406_, 6);
lean_dec(v_unused_1482_);
v_unused_1483_ = lean_ctor_get(v___y_1406_, 5);
lean_dec(v_unused_1483_);
v_unused_1484_ = lean_ctor_get(v___y_1406_, 4);
lean_dec(v_unused_1484_);
v_unused_1485_ = lean_ctor_get(v___y_1406_, 3);
lean_dec(v_unused_1485_);
v_unused_1486_ = lean_ctor_get(v___y_1406_, 2);
lean_dec(v_unused_1486_);
v_unused_1487_ = lean_ctor_get(v___y_1406_, 1);
lean_dec(v_unused_1487_);
v_unused_1488_ = lean_ctor_get(v___y_1406_, 0);
lean_dec(v_unused_1488_);
v___x_1450_ = v___y_1406_;
v_isShared_1451_ = v_isSharedCheck_1481_;
goto v_resetjp_1449_;
}
else
{
lean_dec(v___y_1406_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1481_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
uint64_t v___x_1452_; uint64_t v___x_1453_; lean_object* v___x_1454_; uint8_t v___x_1455_; uint64_t v___x_1456_; uint64_t v___x_1457_; uint64_t v_key_1458_; lean_object* v___x_1459_; lean_object* v___x_1461_; 
v___x_1452_ = 3ULL;
v___x_1453_ = lean_uint64_shift_right(v___x_1448_, v___x_1452_);
v___x_1454_ = l_Lean_Expr_mvarId_x21(v_a_1412_);
lean_dec(v_a_1412_);
v___x_1455_ = 1;
v___x_1456_ = lean_uint64_shift_left(v___x_1453_, v___x_1452_);
v___x_1457_ = lean_uint64_once(&l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___closed__0, &l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___closed__0_once, _init_l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___closed__0);
v_key_1458_ = lean_uint64_lor(v___x_1456_, v___x_1457_);
v___x_1459_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1459_, 0, v_config_1447_);
lean_ctor_set_uint64(v___x_1459_, sizeof(void*)*1, v_key_1458_);
if (v_isShared_1451_ == 0)
{
lean_ctor_set(v___x_1450_, 0, v___x_1459_);
v___x_1461_ = v___x_1450_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v___x_1459_);
lean_ctor_set(v_reuseFailAlloc_1480_, 1, v_zetaDeltaSet_1436_);
lean_ctor_set(v_reuseFailAlloc_1480_, 2, v_lctx_1437_);
lean_ctor_set(v_reuseFailAlloc_1480_, 3, v_localInstances_1438_);
lean_ctor_set(v_reuseFailAlloc_1480_, 4, v_defEqCtx_x3f_1439_);
lean_ctor_set(v_reuseFailAlloc_1480_, 5, v_synthPendingDepth_1440_);
lean_ctor_set(v_reuseFailAlloc_1480_, 6, v_canUnfold_x3f_1441_);
lean_ctor_set_uint8(v_reuseFailAlloc_1480_, sizeof(void*)*7, v_trackZetaDelta_1435_);
lean_ctor_set_uint8(v_reuseFailAlloc_1480_, sizeof(void*)*7 + 1, v_univApprox_1442_);
lean_ctor_set_uint8(v_reuseFailAlloc_1480_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1443_);
lean_ctor_set_uint8(v_reuseFailAlloc_1480_, sizeof(void*)*7 + 3, v_cacheInferType_1444_);
v___x_1461_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
lean_object* v___x_1462_; 
v___x_1462_ = l_Lean_MVarId_refl(v___x_1454_, v___x_1455_, v___x_1461_, v___y_1407_, v___y_1408_, v___y_1409_);
lean_dec_ref(v___x_1461_);
if (lean_obj_tag(v___x_1462_) == 0)
{
lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1470_; 
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1470_ == 0)
{
lean_object* v_unused_1471_; 
v_unused_1471_ = lean_ctor_get(v___x_1462_, 0);
lean_dec(v_unused_1471_);
v___x_1464_ = v___x_1462_;
v_isShared_1465_ = v_isSharedCheck_1470_;
goto v_resetjp_1463_;
}
else
{
lean_dec(v___x_1462_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1470_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1466_; lean_object* v___x_1468_; 
v___x_1466_ = lean_box(v___x_1455_);
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 0, v___x_1466_);
v___x_1468_ = v___x_1464_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v___x_1466_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
else
{
lean_object* v_a_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1479_; 
v_a_1472_ = lean_ctor_get(v___x_1462_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1474_ = v___x_1462_;
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_a_1472_);
lean_dec(v___x_1462_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1477_; 
if (v_isShared_1475_ == 0)
{
v___x_1477_ = v___x_1474_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_a_1472_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
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
lean_object* v_a_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1498_; 
lean_dec_ref(v___y_1406_);
v_a_1491_ = lean_ctor_get(v___x_1411_, 0);
v_isSharedCheck_1498_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1493_ = v___x_1411_;
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_a_1491_);
lean_dec(v___x_1411_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1496_; 
if (v_isShared_1494_ == 0)
{
v___x_1496_ = v___x_1493_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_a_1491_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___boxed(lean_object* v___x_1499_, lean_object* v___x_1500_, lean_object* v___x_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_){
_start:
{
uint8_t v___x_2362__boxed_1507_; lean_object* v_res_1508_; 
v___x_2362__boxed_1507_ = lean_unbox(v___x_1500_);
v_res_1508_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0(v___x_1499_, v___x_2362__boxed_1507_, v___x_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
lean_dec(v___y_1503_);
return v_res_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(lean_object* v_mctx_1509_, lean_object* v_e_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_){
_start:
{
lean_object* v___x_1516_; uint8_t v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___f_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1516_, 0, v_e_1510_);
v___x_1517_ = 0;
v___x_1518_ = lean_box(0);
v___x_1519_ = lean_box(v___x_1517_);
v___f_1520_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1520_, 0, v___x_1516_);
lean_closure_set(v___f_1520_, 1, v___x_1519_);
lean_closure_set(v___f_1520_, 2, v___x_1518_);
v___x_1521_ = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___boxed), 8, 3);
lean_closure_set(v___x_1521_, 0, lean_box(0));
lean_closure_set(v___x_1521_, 1, v_mctx_1509_);
lean_closure_set(v___x_1521_, 2, v___f_1520_);
v___x_1522_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v___x_1521_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
if (lean_obj_tag(v___x_1522_) == 0)
{
return v___x_1522_;
}
else
{
lean_object* v_a_1523_; uint8_t v___y_1525_; uint8_t v___x_1535_; 
v_a_1523_ = lean_ctor_get(v___x_1522_, 0);
lean_inc(v_a_1523_);
v___x_1535_ = l_Lean_Exception_isInterrupt(v_a_1523_);
if (v___x_1535_ == 0)
{
uint8_t v___x_1536_; 
v___x_1536_ = l_Lean_Exception_isRuntime(v_a_1523_);
v___y_1525_ = v___x_1536_;
goto v___jp_1524_;
}
else
{
lean_dec(v_a_1523_);
v___y_1525_ = v___x_1535_;
goto v___jp_1524_;
}
v___jp_1524_:
{
if (v___y_1525_ == 0)
{
lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1533_; 
v_isSharedCheck_1533_ = !lean_is_exclusive(v___x_1522_);
if (v_isSharedCheck_1533_ == 0)
{
lean_object* v_unused_1534_; 
v_unused_1534_ = lean_ctor_get(v___x_1522_, 0);
lean_dec(v_unused_1534_);
v___x_1527_ = v___x_1522_;
v_isShared_1528_ = v_isSharedCheck_1533_;
goto v_resetjp_1526_;
}
else
{
lean_dec(v___x_1522_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1533_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1529_; lean_object* v___x_1531_; 
v___x_1529_ = lean_box(v___y_1525_);
if (v_isShared_1528_ == 0)
{
lean_ctor_set_tag(v___x_1527_, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1529_);
v___x_1531_ = v___x_1527_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v___x_1529_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
}
else
{
return v___x_1522_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___boxed(lean_object* v_mctx_1537_, lean_object* v_e_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_){
_start:
{
lean_object* v_res_1544_; 
v_res_1544_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(v_mctx_1537_, v_e_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_);
lean_dec(v_a_1542_);
lean_dec_ref(v_a_1541_);
lean_dec(v_a_1540_);
lean_dec_ref(v_a_1539_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult(lean_object* v_r_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_){
_start:
{
lean_object* v_result_1551_; lean_object* v_eNew_1552_; lean_object* v___x_1553_; 
v_result_1551_ = lean_ctor_get(v_r_1545_, 2);
lean_inc_ref(v_result_1551_);
lean_dec_ref(v_r_1545_);
v_eNew_1552_ = lean_ctor_get(v_result_1551_, 0);
lean_inc_ref(v_eNew_1552_);
lean_dec_ref(v_result_1551_);
v___x_1553_ = l_Lean_Meta_ppExpr(v_eNew_1552_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_);
if (lean_obj_tag(v___x_1553_) == 0)
{
lean_object* v_a_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1564_; 
v_a_1554_ = lean_ctor_get(v___x_1553_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1556_ = v___x_1553_;
v_isShared_1557_ = v_isSharedCheck_1564_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_a_1554_);
lean_dec(v___x_1553_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1564_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1562_; 
v___x_1558_ = l_Std_Format_defWidth;
v___x_1559_ = lean_unsigned_to_nat(0u);
v___x_1560_ = l_Std_Format_pretty(v_a_1554_, v___x_1558_, v___x_1559_, v___x_1559_);
if (v_isShared_1557_ == 0)
{
lean_ctor_set(v___x_1556_, 0, v___x_1560_);
v___x_1562_ = v___x_1556_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v___x_1560_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
else
{
lean_object* v_a_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1572_; 
v_a_1565_ = lean_ctor_get(v___x_1553_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1567_ = v___x_1553_;
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_a_1565_);
lean_dec(v___x_1553_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult___boxed(lean_object* v_r_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_){
_start:
{
lean_object* v_res_1579_; 
v_res_1579_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult(v_r_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_);
lean_dec(v_a_1577_);
lean_dec_ref(v_a_1576_);
lean_dec(v_a_1575_);
lean_dec_ref(v_a_1574_);
return v_res_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorIdx(uint8_t v_x_1580_){
_start:
{
switch(v_x_1580_)
{
case 0:
{
lean_object* v___x_1581_; 
v___x_1581_ = lean_unsigned_to_nat(0u);
return v___x_1581_;
}
case 1:
{
lean_object* v___x_1582_; 
v___x_1582_ = lean_unsigned_to_nat(1u);
return v___x_1582_;
}
default: 
{
lean_object* v___x_1583_; 
v___x_1583_ = lean_unsigned_to_nat(2u);
return v___x_1583_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorIdx___boxed(lean_object* v_x_1584_){
_start:
{
uint8_t v_x_boxed_1585_; lean_object* v_res_1586_; 
v_x_boxed_1585_ = lean_unbox(v_x_1584_);
v_res_1586_ = l_Lean_Meta_Rewrites_SideConditions_ctorIdx(v_x_boxed_1585_);
return v_res_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_toCtorIdx(uint8_t v_x_1587_){
_start:
{
lean_object* v___x_1588_; 
v___x_1588_ = l_Lean_Meta_Rewrites_SideConditions_ctorIdx(v_x_1587_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_toCtorIdx___boxed(lean_object* v_x_1589_){
_start:
{
uint8_t v_x_4__boxed_1590_; lean_object* v_res_1591_; 
v_x_4__boxed_1590_ = lean_unbox(v_x_1589_);
v_res_1591_ = l_Lean_Meta_Rewrites_SideConditions_toCtorIdx(v_x_4__boxed_1590_);
return v_res_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorElim___redArg(lean_object* v_k_1592_){
_start:
{
lean_inc(v_k_1592_);
return v_k_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorElim___redArg___boxed(lean_object* v_k_1593_){
_start:
{
lean_object* v_res_1594_; 
v_res_1594_ = l_Lean_Meta_Rewrites_SideConditions_ctorElim___redArg(v_k_1593_);
lean_dec(v_k_1593_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorElim(lean_object* v_motive_1595_, lean_object* v_ctorIdx_1596_, uint8_t v_t_1597_, lean_object* v_h_1598_, lean_object* v_k_1599_){
_start:
{
lean_inc(v_k_1599_);
return v_k_1599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorElim___boxed(lean_object* v_motive_1600_, lean_object* v_ctorIdx_1601_, lean_object* v_t_1602_, lean_object* v_h_1603_, lean_object* v_k_1604_){
_start:
{
uint8_t v_t_boxed_1605_; lean_object* v_res_1606_; 
v_t_boxed_1605_ = lean_unbox(v_t_1602_);
v_res_1606_ = l_Lean_Meta_Rewrites_SideConditions_ctorElim(v_motive_1600_, v_ctorIdx_1601_, v_t_boxed_1605_, v_h_1603_, v_k_1604_);
lean_dec(v_k_1604_);
lean_dec(v_ctorIdx_1601_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_none_elim___redArg(lean_object* v_none_1607_){
_start:
{
lean_inc(v_none_1607_);
return v_none_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_none_elim___redArg___boxed(lean_object* v_none_1608_){
_start:
{
lean_object* v_res_1609_; 
v_res_1609_ = l_Lean_Meta_Rewrites_SideConditions_none_elim___redArg(v_none_1608_);
lean_dec(v_none_1608_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_none_elim(lean_object* v_motive_1610_, uint8_t v_t_1611_, lean_object* v_h_1612_, lean_object* v_none_1613_){
_start:
{
lean_inc(v_none_1613_);
return v_none_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_none_elim___boxed(lean_object* v_motive_1614_, lean_object* v_t_1615_, lean_object* v_h_1616_, lean_object* v_none_1617_){
_start:
{
uint8_t v_t_boxed_1618_; lean_object* v_res_1619_; 
v_t_boxed_1618_ = lean_unbox(v_t_1615_);
v_res_1619_ = l_Lean_Meta_Rewrites_SideConditions_none_elim(v_motive_1614_, v_t_boxed_1618_, v_h_1616_, v_none_1617_);
lean_dec(v_none_1617_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_assumption_elim___redArg(lean_object* v_assumption_1620_){
_start:
{
lean_inc(v_assumption_1620_);
return v_assumption_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_assumption_elim___redArg___boxed(lean_object* v_assumption_1621_){
_start:
{
lean_object* v_res_1622_; 
v_res_1622_ = l_Lean_Meta_Rewrites_SideConditions_assumption_elim___redArg(v_assumption_1621_);
lean_dec(v_assumption_1621_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_assumption_elim(lean_object* v_motive_1623_, uint8_t v_t_1624_, lean_object* v_h_1625_, lean_object* v_assumption_1626_){
_start:
{
lean_inc(v_assumption_1626_);
return v_assumption_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_assumption_elim___boxed(lean_object* v_motive_1627_, lean_object* v_t_1628_, lean_object* v_h_1629_, lean_object* v_assumption_1630_){
_start:
{
uint8_t v_t_boxed_1631_; lean_object* v_res_1632_; 
v_t_boxed_1631_ = lean_unbox(v_t_1628_);
v_res_1632_ = l_Lean_Meta_Rewrites_SideConditions_assumption_elim(v_motive_1627_, v_t_boxed_1631_, v_h_1629_, v_assumption_1630_);
lean_dec(v_assumption_1630_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim___redArg(lean_object* v_solveByElim_1633_){
_start:
{
lean_inc(v_solveByElim_1633_);
return v_solveByElim_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim___redArg___boxed(lean_object* v_solveByElim_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim___redArg(v_solveByElim_1634_);
lean_dec(v_solveByElim_1634_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim(lean_object* v_motive_1636_, uint8_t v_t_1637_, lean_object* v_h_1638_, lean_object* v_solveByElim_1639_){
_start:
{
lean_inc(v_solveByElim_1639_);
return v_solveByElim_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim___boxed(lean_object* v_motive_1640_, lean_object* v_t_1641_, lean_object* v_h_1642_, lean_object* v_solveByElim_1643_){
_start:
{
uint8_t v_t_boxed_1644_; lean_object* v_res_1645_; 
v_t_boxed_1644_ = lean_unbox(v_t_1641_);
v_res_1645_ = l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim(v_motive_1640_, v_t_boxed_1644_, v_h_1642_, v_solveByElim_1643_);
lean_dec(v_solveByElim_1643_);
return v_res_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__0(lean_object* v_x_1646_, lean_object* v_x_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_){
_start:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___x_1653_ = lean_box(0);
v___x_1654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1653_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__0___boxed(lean_object* v_x_1655_, lean_object* v_x_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l_Lean_Meta_Rewrites_solveByElim___lam__0(v_x_1655_, v_x_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
lean_dec(v_x_1656_);
lean_dec(v_x_1655_);
return v_res_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__1(lean_object* v_x_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_){
_start:
{
uint8_t v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1669_ = 0;
v___x_1670_ = lean_box(v___x_1669_);
v___x_1671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1670_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__1___boxed(lean_object* v_x_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l_Lean_Meta_Rewrites_solveByElim___lam__1(v_x_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v_x_1672_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0(lean_object* v_msgData_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_){
_start:
{
lean_object* v___x_1685_; lean_object* v_env_1686_; lean_object* v___x_1687_; lean_object* v_mctx_1688_; lean_object* v_lctx_1689_; lean_object* v_options_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1685_ = lean_st_ref_get(v___y_1683_);
v_env_1686_ = lean_ctor_get(v___x_1685_, 0);
lean_inc_ref(v_env_1686_);
lean_dec(v___x_1685_);
v___x_1687_ = lean_st_ref_get(v___y_1681_);
v_mctx_1688_ = lean_ctor_get(v___x_1687_, 0);
lean_inc_ref(v_mctx_1688_);
lean_dec(v___x_1687_);
v_lctx_1689_ = lean_ctor_get(v___y_1680_, 2);
v_options_1690_ = lean_ctor_get(v___y_1682_, 2);
lean_inc_ref(v_options_1690_);
lean_inc_ref(v_lctx_1689_);
v___x_1691_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1691_, 0, v_env_1686_);
lean_ctor_set(v___x_1691_, 1, v_mctx_1688_);
lean_ctor_set(v___x_1691_, 2, v_lctx_1689_);
lean_ctor_set(v___x_1691_, 3, v_options_1690_);
v___x_1692_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1692_, 0, v___x_1691_);
lean_ctor_set(v___x_1692_, 1, v_msgData_1679_);
v___x_1693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1692_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0___boxed(lean_object* v_msgData_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0(v_msgData_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_);
lean_dec(v___y_1698_);
lean_dec_ref(v___y_1697_);
lean_dec(v___y_1696_);
lean_dec_ref(v___y_1695_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(lean_object* v_msg_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
lean_object* v_ref_1707_; lean_object* v___x_1708_; lean_object* v_a_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1717_; 
v_ref_1707_ = lean_ctor_get(v___y_1704_, 5);
v___x_1708_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0(v_msg_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
v_a_1709_ = lean_ctor_get(v___x_1708_, 0);
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1711_ = v___x_1708_;
v_isShared_1712_ = v_isSharedCheck_1717_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_a_1709_);
lean_dec(v___x_1708_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1717_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1713_; lean_object* v___x_1715_; 
lean_inc(v_ref_1707_);
v___x_1713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1713_, 0, v_ref_1707_);
lean_ctor_set(v___x_1713_, 1, v_a_1709_);
if (v_isShared_1712_ == 0)
{
lean_ctor_set_tag(v___x_1711_, 1);
lean_ctor_set(v___x_1711_, 0, v___x_1713_);
v___x_1715_ = v___x_1711_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v___x_1713_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg___boxed(lean_object* v_msg_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(v_msg_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
lean_dec(v___y_1722_);
lean_dec_ref(v___y_1721_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
return v_res_1724_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1726_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__0));
v___x_1727_ = l_Lean_stringToMessageData(v___x_1726_);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__2(lean_object* v_x_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_){
_start:
{
lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1734_ = lean_obj_once(&l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1, &l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1_once, _init_l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1);
v___x_1735_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(v___x_1734_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_);
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__2___boxed(lean_object* v_x_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l_Lean_Meta_Rewrites_solveByElim___lam__2(v_x_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v_x_1736_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim(lean_object* v_goals_1752_, lean_object* v_depth_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_){
_start:
{
lean_object* v___f_1759_; lean_object* v___f_1760_; lean_object* v___f_1761_; uint8_t v___x_1762_; lean_object* v___x_1763_; uint8_t v___x_1764_; lean_object* v___x_1765_; uint8_t v___x_1766_; lean_object* v___x_1767_; lean_object* v_cfg_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___f_1759_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___closed__0));
v___f_1760_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___closed__1));
v___f_1761_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___closed__2));
v___x_1762_ = 0;
v___x_1763_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1763_, 0, v_depth_1753_);
lean_ctor_set(v___x_1763_, 1, v___f_1759_);
lean_ctor_set(v___x_1763_, 2, v___f_1760_);
lean_ctor_set(v___x_1763_, 3, v___f_1761_);
lean_ctor_set_uint8(v___x_1763_, sizeof(void*)*4, v___x_1762_);
v___x_1764_ = 1;
v___x_1765_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___closed__3));
v___x_1766_ = 1;
v___x_1767_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_1767_, 0, v___x_1763_);
lean_ctor_set(v___x_1767_, 1, v___x_1765_);
lean_ctor_set_uint8(v___x_1767_, sizeof(void*)*2, v___x_1766_);
lean_ctor_set_uint8(v___x_1767_, sizeof(void*)*2 + 1, v___x_1764_);
lean_ctor_set_uint8(v___x_1767_, sizeof(void*)*2 + 2, v___x_1762_);
v_cfg_1768_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_cfg_1768_, 0, v___x_1767_);
lean_ctor_set_uint8(v_cfg_1768_, sizeof(void*)*1, v___x_1764_);
lean_ctor_set_uint8(v_cfg_1768_, sizeof(void*)*1 + 1, v___x_1764_);
lean_ctor_set_uint8(v_cfg_1768_, sizeof(void*)*1 + 2, v___x_1764_);
lean_ctor_set_uint8(v_cfg_1768_, sizeof(void*)*1 + 3, v___x_1762_);
v___x_1769_ = lean_box(0);
v___x_1770_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___closed__4));
v___x_1771_ = l_Lean_Meta_SolveByElim_mkAssumptionSet(v___x_1762_, v___x_1762_, v___x_1769_, v___x_1769_, v___x_1770_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_);
if (lean_obj_tag(v___x_1771_) == 0)
{
lean_object* v_a_1772_; lean_object* v_fst_1773_; lean_object* v_snd_1774_; lean_object* v___x_1775_; 
v_a_1772_ = lean_ctor_get(v___x_1771_, 0);
lean_inc(v_a_1772_);
lean_dec_ref_known(v___x_1771_, 1);
v_fst_1773_ = lean_ctor_get(v_a_1772_, 0);
lean_inc(v_fst_1773_);
v_snd_1774_ = lean_ctor_get(v_a_1772_, 1);
lean_inc(v_snd_1774_);
lean_dec(v_a_1772_);
v___x_1775_ = l_Lean_Meta_SolveByElim_solveByElim(v_cfg_1768_, v_fst_1773_, v_snd_1774_, v_goals_1752_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_);
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_object* v_a_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1786_; 
v_a_1776_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1778_ = v___x_1775_;
v_isShared_1779_ = v_isSharedCheck_1786_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_a_1776_);
lean_dec(v___x_1775_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1786_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
if (lean_obj_tag(v_a_1776_) == 0)
{
lean_object* v___x_1780_; lean_object* v___x_1782_; 
v___x_1780_ = lean_box(0);
if (v_isShared_1779_ == 0)
{
lean_ctor_set(v___x_1778_, 0, v___x_1780_);
v___x_1782_ = v___x_1778_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v___x_1780_);
v___x_1782_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
return v___x_1782_;
}
}
else
{
lean_object* v___x_1784_; lean_object* v___x_1785_; 
lean_del_object(v___x_1778_);
lean_dec(v_a_1776_);
v___x_1784_ = lean_obj_once(&l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1, &l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1_once, _init_l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1);
v___x_1785_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(v___x_1784_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_);
return v___x_1785_;
}
}
}
else
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1794_; 
v_a_1787_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1789_ = v___x_1775_;
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1775_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1792_; 
if (v_isShared_1790_ == 0)
{
v___x_1792_ = v___x_1789_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_a_1787_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
}
}
else
{
lean_object* v_a_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1802_; 
lean_dec_ref_known(v_cfg_1768_, 1);
lean_dec(v_goals_1752_);
v_a_1795_ = lean_ctor_get(v___x_1771_, 0);
v_isSharedCheck_1802_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1797_ = v___x_1771_;
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_a_1795_);
lean_dec(v___x_1771_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1800_; 
if (v_isShared_1798_ == 0)
{
v___x_1800_ = v___x_1797_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_a_1795_);
v___x_1800_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
return v___x_1800_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___boxed(lean_object* v_goals_1803_, lean_object* v_depth_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_){
_start:
{
lean_object* v_res_1810_; 
v_res_1810_ = l_Lean_Meta_Rewrites_solveByElim(v_goals_1803_, v_depth_1804_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_);
lean_dec(v_a_1808_);
lean_dec_ref(v_a_1807_);
lean_dec(v_a_1806_);
lean_dec_ref(v_a_1805_);
return v_res_1810_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0(lean_object* v_00_u03b1_1811_, lean_object* v_msg_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_){
_start:
{
lean_object* v___x_1818_; 
v___x_1818_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(v_msg_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___boxed(lean_object* v_00_u03b1_1819_, lean_object* v_msg_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_){
_start:
{
lean_object* v_res_1826_; 
v_res_1826_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0(v_00_u03b1_1819_, v_msg_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_);
lean_dec(v___y_1824_);
lean_dec_ref(v___y_1823_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1821_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg(lean_object* v_e_1827_, lean_object* v___y_1828_){
_start:
{
uint8_t v___x_1830_; 
v___x_1830_ = l_Lean_Expr_hasMVar(v_e_1827_);
if (v___x_1830_ == 0)
{
lean_object* v___x_1831_; 
v___x_1831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1831_, 0, v_e_1827_);
return v___x_1831_;
}
else
{
lean_object* v___x_1832_; lean_object* v_mctx_1833_; lean_object* v___x_1834_; lean_object* v_fst_1835_; lean_object* v_snd_1836_; lean_object* v___x_1837_; lean_object* v_cache_1838_; lean_object* v_zetaDeltaFVarIds_1839_; lean_object* v_postponed_1840_; lean_object* v_diag_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1850_; 
v___x_1832_ = lean_st_ref_get(v___y_1828_);
v_mctx_1833_ = lean_ctor_get(v___x_1832_, 0);
lean_inc_ref(v_mctx_1833_);
lean_dec(v___x_1832_);
v___x_1834_ = l_Lean_instantiateMVarsCore(v_mctx_1833_, v_e_1827_);
v_fst_1835_ = lean_ctor_get(v___x_1834_, 0);
lean_inc(v_fst_1835_);
v_snd_1836_ = lean_ctor_get(v___x_1834_, 1);
lean_inc(v_snd_1836_);
lean_dec_ref(v___x_1834_);
v___x_1837_ = lean_st_ref_take(v___y_1828_);
v_cache_1838_ = lean_ctor_get(v___x_1837_, 1);
v_zetaDeltaFVarIds_1839_ = lean_ctor_get(v___x_1837_, 2);
v_postponed_1840_ = lean_ctor_get(v___x_1837_, 3);
v_diag_1841_ = lean_ctor_get(v___x_1837_, 4);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1850_ == 0)
{
lean_object* v_unused_1851_; 
v_unused_1851_ = lean_ctor_get(v___x_1837_, 0);
lean_dec(v_unused_1851_);
v___x_1843_ = v___x_1837_;
v_isShared_1844_ = v_isSharedCheck_1850_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_diag_1841_);
lean_inc(v_postponed_1840_);
lean_inc(v_zetaDeltaFVarIds_1839_);
lean_inc(v_cache_1838_);
lean_dec(v___x_1837_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1850_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1846_; 
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 0, v_snd_1836_);
v___x_1846_ = v___x_1843_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_snd_1836_);
lean_ctor_set(v_reuseFailAlloc_1849_, 1, v_cache_1838_);
lean_ctor_set(v_reuseFailAlloc_1849_, 2, v_zetaDeltaFVarIds_1839_);
lean_ctor_set(v_reuseFailAlloc_1849_, 3, v_postponed_1840_);
lean_ctor_set(v_reuseFailAlloc_1849_, 4, v_diag_1841_);
v___x_1846_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1847_ = lean_st_ref_set(v___y_1828_, v___x_1846_);
v___x_1848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1848_, 0, v_fst_1835_);
return v___x_1848_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg___boxed(lean_object* v_e_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_){
_start:
{
lean_object* v_res_1855_; 
v_res_1855_ = l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg(v_e_1852_, v___y_1853_);
lean_dec(v___y_1853_);
return v_res_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0(lean_object* v_e_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_){
_start:
{
lean_object* v___x_1862_; 
v___x_1862_ = l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg(v_e_1856_, v___y_1858_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___boxed(lean_object* v_e_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_){
_start:
{
lean_object* v_res_1869_; 
v_res_1869_ = l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0(v_e_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
return v_res_1869_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1870_; double v___x_1871_; 
v___x_1870_ = lean_unsigned_to_nat(0u);
v___x_1871_ = lean_float_of_nat(v___x_1870_);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2(lean_object* v_cls_1875_, lean_object* v_msg_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_){
_start:
{
lean_object* v_ref_1882_; lean_object* v___x_1883_; lean_object* v_a_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1928_; 
v_ref_1882_ = lean_ctor_get(v___y_1879_, 5);
v___x_1883_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0(v_msg_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_);
v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1886_ = v___x_1883_;
v_isShared_1887_ = v_isSharedCheck_1928_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_a_1884_);
lean_dec(v___x_1883_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1928_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1888_; lean_object* v_traceState_1889_; lean_object* v_env_1890_; lean_object* v_nextMacroScope_1891_; lean_object* v_ngen_1892_; lean_object* v_auxDeclNGen_1893_; lean_object* v_cache_1894_; lean_object* v_messages_1895_; lean_object* v_infoState_1896_; lean_object* v_snapshotTasks_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1927_; 
v___x_1888_ = lean_st_ref_take(v___y_1880_);
v_traceState_1889_ = lean_ctor_get(v___x_1888_, 4);
v_env_1890_ = lean_ctor_get(v___x_1888_, 0);
v_nextMacroScope_1891_ = lean_ctor_get(v___x_1888_, 1);
v_ngen_1892_ = lean_ctor_get(v___x_1888_, 2);
v_auxDeclNGen_1893_ = lean_ctor_get(v___x_1888_, 3);
v_cache_1894_ = lean_ctor_get(v___x_1888_, 5);
v_messages_1895_ = lean_ctor_get(v___x_1888_, 6);
v_infoState_1896_ = lean_ctor_get(v___x_1888_, 7);
v_snapshotTasks_1897_ = lean_ctor_get(v___x_1888_, 8);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1899_ = v___x_1888_;
v_isShared_1900_ = v_isSharedCheck_1927_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_snapshotTasks_1897_);
lean_inc(v_infoState_1896_);
lean_inc(v_messages_1895_);
lean_inc(v_cache_1894_);
lean_inc(v_traceState_1889_);
lean_inc(v_auxDeclNGen_1893_);
lean_inc(v_ngen_1892_);
lean_inc(v_nextMacroScope_1891_);
lean_inc(v_env_1890_);
lean_dec(v___x_1888_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1927_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
uint64_t v_tid_1901_; lean_object* v_traces_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1926_; 
v_tid_1901_ = lean_ctor_get_uint64(v_traceState_1889_, sizeof(void*)*1);
v_traces_1902_ = lean_ctor_get(v_traceState_1889_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v_traceState_1889_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1904_ = v_traceState_1889_;
v_isShared_1905_ = v_isSharedCheck_1926_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_traces_1902_);
lean_dec(v_traceState_1889_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1926_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1906_; double v___x_1907_; uint8_t v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1916_; 
v___x_1906_ = lean_box(0);
v___x_1907_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__0);
v___x_1908_ = 0;
v___x_1909_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__1));
v___x_1910_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1910_, 0, v_cls_1875_);
lean_ctor_set(v___x_1910_, 1, v___x_1906_);
lean_ctor_set(v___x_1910_, 2, v___x_1909_);
lean_ctor_set_float(v___x_1910_, sizeof(void*)*3, v___x_1907_);
lean_ctor_set_float(v___x_1910_, sizeof(void*)*3 + 8, v___x_1907_);
lean_ctor_set_uint8(v___x_1910_, sizeof(void*)*3 + 16, v___x_1908_);
v___x_1911_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__2));
v___x_1912_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1912_, 0, v___x_1910_);
lean_ctor_set(v___x_1912_, 1, v_a_1884_);
lean_ctor_set(v___x_1912_, 2, v___x_1911_);
lean_inc(v_ref_1882_);
v___x_1913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1913_, 0, v_ref_1882_);
lean_ctor_set(v___x_1913_, 1, v___x_1912_);
v___x_1914_ = l_Lean_PersistentArray_push___redArg(v_traces_1902_, v___x_1913_);
if (v_isShared_1905_ == 0)
{
lean_ctor_set(v___x_1904_, 0, v___x_1914_);
v___x_1916_ = v___x_1904_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v___x_1914_);
lean_ctor_set_uint64(v_reuseFailAlloc_1925_, sizeof(void*)*1, v_tid_1901_);
v___x_1916_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
lean_object* v___x_1918_; 
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 4, v___x_1916_);
v___x_1918_ = v___x_1899_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_env_1890_);
lean_ctor_set(v_reuseFailAlloc_1924_, 1, v_nextMacroScope_1891_);
lean_ctor_set(v_reuseFailAlloc_1924_, 2, v_ngen_1892_);
lean_ctor_set(v_reuseFailAlloc_1924_, 3, v_auxDeclNGen_1893_);
lean_ctor_set(v_reuseFailAlloc_1924_, 4, v___x_1916_);
lean_ctor_set(v_reuseFailAlloc_1924_, 5, v_cache_1894_);
lean_ctor_set(v_reuseFailAlloc_1924_, 6, v_messages_1895_);
lean_ctor_set(v_reuseFailAlloc_1924_, 7, v_infoState_1896_);
lean_ctor_set(v_reuseFailAlloc_1924_, 8, v_snapshotTasks_1897_);
v___x_1918_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1922_; 
v___x_1919_ = lean_st_ref_set(v___y_1880_, v___x_1918_);
v___x_1920_ = lean_box(0);
if (v_isShared_1887_ == 0)
{
lean_ctor_set(v___x_1886_, 0, v___x_1920_);
v___x_1922_ = v___x_1886_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v___x_1920_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
return v___x_1922_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___boxed(lean_object* v_cls_1929_, lean_object* v_msg_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_){
_start:
{
lean_object* v_res_1936_; 
v_res_1936_ = l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2(v_cls_1929_, v_msg_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_);
lean_dec(v___y_1934_);
lean_dec_ref(v___y_1933_);
lean_dec(v___y_1932_);
lean_dec_ref(v___y_1931_);
return v_res_1936_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Rewrites_rwLemma_spec__1(lean_object* v_x_1937_, lean_object* v_x_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_){
_start:
{
if (lean_obj_tag(v_x_1937_) == 0)
{
lean_object* v___x_1944_; lean_object* v___x_1945_; 
v___x_1944_ = l_List_reverse___redArg(v_x_1938_);
v___x_1945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1944_);
return v___x_1945_;
}
else
{
lean_object* v_head_1946_; lean_object* v_tail_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1965_; 
v_head_1946_ = lean_ctor_get(v_x_1937_, 0);
v_tail_1947_ = lean_ctor_get(v_x_1937_, 1);
v_isSharedCheck_1965_ = !lean_is_exclusive(v_x_1937_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1949_ = v_x_1937_;
v_isShared_1950_ = v_isSharedCheck_1965_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_tail_1947_);
lean_inc(v_head_1946_);
lean_dec(v_x_1937_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1965_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1951_; 
v___x_1951_ = l_Lean_MVarId_assumption(v_head_1946_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_);
if (lean_obj_tag(v___x_1951_) == 0)
{
lean_object* v_a_1952_; lean_object* v___x_1954_; 
v_a_1952_ = lean_ctor_get(v___x_1951_, 0);
lean_inc(v_a_1952_);
lean_dec_ref_known(v___x_1951_, 1);
if (v_isShared_1950_ == 0)
{
lean_ctor_set(v___x_1949_, 1, v_x_1938_);
lean_ctor_set(v___x_1949_, 0, v_a_1952_);
v___x_1954_ = v___x_1949_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_a_1952_);
lean_ctor_set(v_reuseFailAlloc_1956_, 1, v_x_1938_);
v___x_1954_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
v_x_1937_ = v_tail_1947_;
v_x_1938_ = v___x_1954_;
goto _start;
}
}
else
{
lean_object* v_a_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1964_; 
lean_del_object(v___x_1949_);
lean_dec(v_tail_1947_);
lean_dec(v_x_1938_);
v_a_1957_ = lean_ctor_get(v___x_1951_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v___x_1951_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1959_ = v___x_1951_;
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_a_1957_);
lean_dec(v___x_1951_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1962_; 
if (v_isShared_1960_ == 0)
{
v___x_1962_ = v___x_1959_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_a_1957_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Rewrites_rwLemma_spec__1___boxed(lean_object* v_x_1966_, lean_object* v_x_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_){
_start:
{
lean_object* v_res_1973_; 
v_res_1973_ = l_List_mapM_loop___at___00Lean_Meta_Rewrites_rwLemma_spec__1(v_x_1966_, v_x_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
return v_res_1973_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5(void){
_start:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1986_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_));
v___x_1987_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__4));
v___x_1988_ = l_Lean_Name_append(v___x_1987_, v___x_1986_);
return v___x_1988_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__7(void){
_start:
{
lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1990_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__6));
v___x_1991_ = l_Lean_stringToMessageData(v___x_1990_);
return v___x_1991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0(lean_object* v_weight_1993_, lean_object* v_goal_1994_, lean_object* v_target_1995_, uint8_t v_symm_1996_, uint8_t v_side_1997_, lean_object* v_lem_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_){
_start:
{
lean_object* v___y_2005_; lean_object* v___y_2006_; lean_object* v___y_2007_; lean_object* v___y_2008_; uint8_t v___y_2009_; lean_object* v___y_2030_; lean_object* v___y_2031_; lean_object* v___y_2032_; lean_object* v___y_2033_; lean_object* v___y_2034_; lean_object* v___y_2035_; lean_object* v_fst_2036_; uint8_t v_snd_2037_; lean_object* v___y_2061_; lean_object* v___y_2062_; uint8_t v___y_2063_; uint8_t v___y_2064_; lean_object* v___y_2065_; lean_object* v___y_2066_; lean_object* v___y_2067_; lean_object* v___y_2068_; lean_object* v___y_2088_; lean_object* v___y_2089_; lean_object* v___y_2090_; lean_object* v___y_2091_; uint8_t v___y_2092_; lean_object* v___y_2104_; lean_object* v___y_2105_; lean_object* v___y_2106_; lean_object* v___y_2107_; uint8_t v___y_2108_; lean_object* v___y_2120_; lean_object* v___y_2200_; lean_object* v___y_2201_; lean_object* v___y_2202_; lean_object* v___y_2203_; lean_object* v_val_2218_; 
if (lean_obj_tag(v_lem_1998_) == 0)
{
lean_object* v_val_2228_; 
v_val_2228_ = lean_ctor_get(v_lem_1998_, 0);
lean_inc(v_val_2228_);
lean_dec_ref_known(v_lem_1998_, 1);
v_val_2218_ = v_val_2228_;
goto v___jp_2217_;
}
else
{
lean_object* v_val_2229_; lean_object* v___x_2230_; 
v_val_2229_ = lean_ctor_get(v_lem_1998_, 0);
lean_inc(v_val_2229_);
lean_dec_ref_known(v_lem_1998_, 1);
v___x_2230_ = l_Lean_Meta_saveState___redArg(v___y_2000_, v___y_2002_);
if (lean_obj_tag(v___x_2230_) == 0)
{
lean_object* v_a_2231_; lean_object* v___x_2232_; 
v_a_2231_ = lean_ctor_get(v___x_2230_, 0);
lean_inc(v_a_2231_);
lean_dec_ref_known(v___x_2230_, 1);
v___x_2232_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_val_2229_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
if (lean_obj_tag(v___x_2232_) == 0)
{
lean_object* v_a_2233_; 
lean_dec(v_a_2231_);
v_a_2233_ = lean_ctor_get(v___x_2232_, 0);
lean_inc(v_a_2233_);
lean_dec_ref_known(v___x_2232_, 1);
v_val_2218_ = v_a_2233_;
goto v___jp_2217_;
}
else
{
lean_object* v_a_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2263_; 
lean_dec_ref(v_target_1995_);
lean_dec(v_goal_1994_);
lean_dec(v_weight_1993_);
v_a_2234_ = lean_ctor_get(v___x_2232_, 0);
v_isSharedCheck_2263_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2263_ == 0)
{
v___x_2236_ = v___x_2232_;
v_isShared_2237_ = v_isSharedCheck_2263_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_a_2234_);
lean_dec(v___x_2232_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2263_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
uint8_t v___y_2239_; uint8_t v___x_2261_; 
v___x_2261_ = l_Lean_Exception_isInterrupt(v_a_2234_);
if (v___x_2261_ == 0)
{
uint8_t v___x_2262_; 
lean_inc(v_a_2234_);
v___x_2262_ = l_Lean_Exception_isRuntime(v_a_2234_);
v___y_2239_ = v___x_2262_;
goto v___jp_2238_;
}
else
{
v___y_2239_ = v___x_2261_;
goto v___jp_2238_;
}
v___jp_2238_:
{
if (v___y_2239_ == 0)
{
lean_object* v___x_2240_; 
lean_del_object(v___x_2236_);
lean_dec(v_a_2234_);
v___x_2240_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2231_, v___y_2000_, v___y_2002_);
lean_dec(v_a_2231_);
if (lean_obj_tag(v___x_2240_) == 0)
{
lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2248_; 
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2248_ == 0)
{
lean_object* v_unused_2249_; 
v_unused_2249_ = lean_ctor_get(v___x_2240_, 0);
lean_dec(v_unused_2249_);
v___x_2242_ = v___x_2240_;
v_isShared_2243_ = v_isSharedCheck_2248_;
goto v_resetjp_2241_;
}
else
{
lean_dec(v___x_2240_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2248_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v___x_2244_; lean_object* v___x_2246_; 
v___x_2244_ = lean_box(0);
if (v_isShared_2243_ == 0)
{
lean_ctor_set(v___x_2242_, 0, v___x_2244_);
v___x_2246_ = v___x_2242_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v___x_2244_);
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
lean_object* v_a_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2257_; 
v_a_2250_ = lean_ctor_get(v___x_2240_, 0);
v_isSharedCheck_2257_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2252_ = v___x_2240_;
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_a_2250_);
lean_dec(v___x_2240_);
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
lean_object* v___x_2259_; 
lean_dec(v_a_2231_);
if (v_isShared_2237_ == 0)
{
v___x_2259_ = v___x_2236_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v_a_2234_);
v___x_2259_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
return v___x_2259_;
}
}
}
}
}
}
else
{
lean_object* v_a_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2271_; 
lean_dec(v_val_2229_);
lean_dec_ref(v_target_1995_);
lean_dec(v_goal_1994_);
lean_dec(v_weight_1993_);
v_a_2264_ = lean_ctor_get(v___x_2230_, 0);
v_isSharedCheck_2271_ = !lean_is_exclusive(v___x_2230_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2266_ = v___x_2230_;
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_a_2264_);
lean_dec(v___x_2230_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v___x_2269_; 
if (v_isShared_2267_ == 0)
{
v___x_2269_ = v___x_2266_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v_a_2264_);
v___x_2269_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
return v___x_2269_;
}
}
}
}
v___jp_2004_:
{
if (v___y_2009_ == 0)
{
lean_object* v___x_2010_; 
lean_dec_ref(v___y_2007_);
v___x_2010_ = l_Lean_Meta_SavedState_restore___redArg(v___y_2006_, v___y_2008_, v___y_2005_);
lean_dec_ref(v___y_2006_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2018_; 
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2018_ == 0)
{
lean_object* v_unused_2019_; 
v_unused_2019_ = lean_ctor_get(v___x_2010_, 0);
lean_dec(v_unused_2019_);
v___x_2012_ = v___x_2010_;
v_isShared_2013_ = v_isSharedCheck_2018_;
goto v_resetjp_2011_;
}
else
{
lean_dec(v___x_2010_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2018_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2014_; lean_object* v___x_2016_; 
v___x_2014_ = lean_box(0);
if (v_isShared_2013_ == 0)
{
lean_ctor_set(v___x_2012_, 0, v___x_2014_);
v___x_2016_ = v___x_2012_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v___x_2014_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
return v___x_2016_;
}
}
}
else
{
lean_object* v_a_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2027_; 
v_a_2020_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2022_ = v___x_2010_;
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_a_2020_);
lean_dec(v___x_2010_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2025_; 
if (v_isShared_2023_ == 0)
{
v___x_2025_ = v___x_2022_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(1, 1, 0);
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
else
{
lean_object* v___x_2028_; 
lean_dec_ref(v___y_2006_);
v___x_2028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2028_, 0, v___y_2007_);
return v___x_2028_;
}
}
v___jp_2029_:
{
lean_object* v___x_2038_; lean_object* v_mctx_2039_; lean_object* v___x_2040_; 
v___x_2038_ = lean_st_ref_get(v___y_2035_);
v_mctx_2039_ = lean_ctor_get(v___x_2038_, 0);
lean_inc_ref_n(v_mctx_2039_, 2);
lean_dec(v___x_2038_);
v___x_2040_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(v_mctx_2039_, v___y_2030_, v___y_2034_, v___y_2035_, v___y_2033_, v___y_2031_);
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_object* v_a_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2051_; 
v_a_2041_ = lean_ctor_get(v___x_2040_, 0);
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2043_ = v___x_2040_;
v_isShared_2044_ = v_isSharedCheck_2051_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_a_2041_);
lean_dec(v___x_2040_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2051_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2045_; uint8_t v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2049_; 
v___x_2045_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2045_, 0, v_fst_2036_);
lean_ctor_set(v___x_2045_, 1, v_weight_1993_);
lean_ctor_set(v___x_2045_, 2, v___y_2032_);
lean_ctor_set(v___x_2045_, 3, v_mctx_2039_);
lean_ctor_set_uint8(v___x_2045_, sizeof(void*)*4, v_snd_2037_);
v___x_2046_ = lean_unbox(v_a_2041_);
lean_dec(v_a_2041_);
lean_ctor_set_uint8(v___x_2045_, sizeof(void*)*4 + 1, v___x_2046_);
v___x_2047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2047_, 0, v___x_2045_);
if (v_isShared_2044_ == 0)
{
lean_ctor_set(v___x_2043_, 0, v___x_2047_);
v___x_2049_ = v___x_2043_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v___x_2047_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
return v___x_2049_;
}
}
}
else
{
lean_object* v_a_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2059_; 
lean_dec_ref(v_mctx_2039_);
lean_dec_ref(v_fst_2036_);
lean_dec_ref(v___y_2032_);
lean_dec(v_weight_1993_);
v_a_2052_ = lean_ctor_get(v___x_2040_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2054_ = v___x_2040_;
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_a_2052_);
lean_dec(v___x_2040_);
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
v___jp_2060_:
{
lean_object* v___x_2069_; 
v___x_2069_ = l_Lean_Meta_Rewrites_rewriteResultLemma(v___y_2062_);
if (lean_obj_tag(v___x_2069_) == 1)
{
lean_object* v_val_2070_; lean_object* v___x_2071_; lean_object* v_a_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; uint8_t v___x_2075_; 
v_val_2070_ = lean_ctor_get(v___x_2069_, 0);
lean_inc(v_val_2070_);
lean_dec_ref_known(v___x_2069_, 1);
v___x_2071_ = l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg(v_val_2070_, v___y_2066_);
v_a_2072_ = lean_ctor_get(v___x_2071_, 0);
lean_inc(v_a_2072_);
lean_dec_ref(v___x_2071_);
v___x_2073_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__1));
v___x_2074_ = lean_unsigned_to_nat(4u);
v___x_2075_ = l_Lean_Expr_isAppOfArity(v_a_2072_, v___x_2073_, v___x_2074_);
if (v___x_2075_ == 0)
{
v___y_2030_ = v___y_2061_;
v___y_2031_ = v___y_2068_;
v___y_2032_ = v___y_2062_;
v___y_2033_ = v___y_2067_;
v___y_2034_ = v___y_2065_;
v___y_2035_ = v___y_2066_;
v_fst_2036_ = v_a_2072_;
v_snd_2037_ = v___y_2063_;
goto v___jp_2029_;
}
else
{
lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2076_ = lean_unsigned_to_nat(3u);
v___x_2077_ = l_Lean_Expr_getAppNumArgs(v_a_2072_);
v___x_2078_ = lean_nat_sub(v___x_2077_, v___x_2076_);
lean_dec(v___x_2077_);
v___x_2079_ = lean_unsigned_to_nat(1u);
v___x_2080_ = lean_nat_sub(v___x_2078_, v___x_2079_);
lean_dec(v___x_2078_);
v___x_2081_ = l_Lean_Expr_getRevArg_x21(v_a_2072_, v___x_2080_);
lean_dec(v_a_2072_);
v___y_2030_ = v___y_2061_;
v___y_2031_ = v___y_2068_;
v___y_2032_ = v___y_2062_;
v___y_2033_ = v___y_2067_;
v___y_2034_ = v___y_2065_;
v___y_2035_ = v___y_2066_;
v_fst_2036_ = v___x_2081_;
v_snd_2037_ = v___y_2064_;
goto v___jp_2029_;
}
}
else
{
lean_object* v___x_2082_; lean_object* v___x_2083_; 
lean_dec(v___x_2069_);
lean_dec_ref(v___y_2062_);
lean_dec_ref(v___y_2061_);
lean_dec(v_weight_1993_);
v___x_2082_ = lean_box(0);
v___x_2083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2082_);
return v___x_2083_;
}
}
v___jp_2084_:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; 
v___x_2085_ = lean_box(0);
v___x_2086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2085_);
return v___x_2086_;
}
v___jp_2087_:
{
if (v___y_2092_ == 0)
{
lean_object* v___x_2093_; 
lean_dec_ref(v___y_2089_);
v___x_2093_ = l_Lean_Meta_SavedState_restore___redArg(v___y_2090_, v___y_2091_, v___y_2088_);
lean_dec_ref(v___y_2090_);
if (lean_obj_tag(v___x_2093_) == 0)
{
lean_dec_ref_known(v___x_2093_, 1);
goto v___jp_2084_;
}
else
{
lean_object* v_a_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2101_; 
v_a_2094_ = lean_ctor_get(v___x_2093_, 0);
v_isSharedCheck_2101_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2101_ == 0)
{
v___x_2096_ = v___x_2093_;
v_isShared_2097_ = v_isSharedCheck_2101_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_a_2094_);
lean_dec(v___x_2093_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2101_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v___x_2099_; 
if (v_isShared_2097_ == 0)
{
v___x_2099_ = v___x_2096_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v_a_2094_);
v___x_2099_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
return v___x_2099_;
}
}
}
}
else
{
lean_object* v___x_2102_; 
lean_dec_ref(v___y_2090_);
v___x_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2102_, 0, v___y_2089_);
return v___x_2102_;
}
}
v___jp_2103_:
{
if (v___y_2108_ == 0)
{
lean_object* v___x_2109_; 
lean_dec_ref(v___y_2105_);
v___x_2109_ = l_Lean_Meta_SavedState_restore___redArg(v___y_2107_, v___y_2106_, v___y_2104_);
lean_dec_ref(v___y_2107_);
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_dec_ref_known(v___x_2109_, 1);
goto v___jp_2084_;
}
else
{
lean_object* v_a_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2117_; 
v_a_2110_ = lean_ctor_get(v___x_2109_, 0);
v_isSharedCheck_2117_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2112_ = v___x_2109_;
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_a_2110_);
lean_dec(v___x_2109_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2115_; 
if (v_isShared_2113_ == 0)
{
v___x_2115_ = v___x_2112_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_a_2110_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
}
}
else
{
lean_object* v___x_2118_; 
lean_dec_ref(v___y_2107_);
v___x_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2118_, 0, v___y_2105_);
return v___x_2118_;
}
}
v___jp_2119_:
{
lean_object* v___x_2121_; 
v___x_2121_ = l_Lean_Meta_saveState___redArg(v___y_2000_, v___y_2002_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v_a_2122_; uint8_t v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; 
v_a_2122_ = lean_ctor_get(v___x_2121_, 0);
lean_inc(v_a_2122_);
lean_dec_ref_known(v___x_2121_, 1);
v___x_2123_ = 1;
v___x_2124_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__2));
lean_inc_ref(v___y_2120_);
v___x_2125_ = l_Lean_MVarId_rewrite(v_goal_1994_, v_target_1995_, v___y_2120_, v_symm_1996_, v___x_2124_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v_a_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2187_; 
lean_dec(v_a_2122_);
v_a_2126_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2128_ = v___x_2125_;
v_isShared_2129_ = v_isSharedCheck_2187_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_a_2126_);
lean_dec(v___x_2125_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2187_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v_eNew_2130_; lean_object* v_mvarIds_2131_; uint8_t v___x_2132_; 
v_eNew_2130_ = lean_ctor_get(v_a_2126_, 0);
v_mvarIds_2131_ = lean_ctor_get(v_a_2126_, 2);
v___x_2132_ = l_List_isEmpty___redArg(v_mvarIds_2131_);
if (v___x_2132_ == 0)
{
lean_inc_ref(v_eNew_2130_);
lean_del_object(v___x_2128_);
lean_dec_ref(v___y_2120_);
switch(v_side_1997_)
{
case 0:
{
if (v___x_2132_ == 0)
{
lean_dec_ref(v_eNew_2130_);
lean_dec(v_a_2126_);
lean_dec(v_weight_1993_);
goto v___jp_2084_;
}
else
{
v___y_2061_ = v_eNew_2130_;
v___y_2062_ = v_a_2126_;
v___y_2063_ = v___x_2132_;
v___y_2064_ = v___x_2123_;
v___y_2065_ = v___y_1999_;
v___y_2066_ = v___y_2000_;
v___y_2067_ = v___y_2001_;
v___y_2068_ = v___y_2002_;
goto v___jp_2060_;
}
}
case 1:
{
lean_object* v___x_2133_; 
v___x_2133_ = l_Lean_Meta_saveState___redArg(v___y_2000_, v___y_2002_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_object* v_a_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; 
v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
lean_inc(v_a_2134_);
lean_dec_ref_known(v___x_2133_, 1);
v___x_2135_ = lean_box(0);
lean_inc(v_mvarIds_2131_);
v___x_2136_ = l_List_mapM_loop___at___00Lean_Meta_Rewrites_rwLemma_spec__1(v_mvarIds_2131_, v___x_2135_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_dec_ref_known(v___x_2136_, 1);
lean_dec(v_a_2134_);
v___y_2061_ = v_eNew_2130_;
v___y_2062_ = v_a_2126_;
v___y_2063_ = v___x_2132_;
v___y_2064_ = v___x_2123_;
v___y_2065_ = v___y_1999_;
v___y_2066_ = v___y_2000_;
v___y_2067_ = v___y_2001_;
v___y_2068_ = v___y_2002_;
goto v___jp_2060_;
}
else
{
lean_object* v_a_2137_; uint8_t v___x_2138_; 
lean_dec_ref(v_eNew_2130_);
lean_dec(v_a_2126_);
lean_dec(v_weight_1993_);
v_a_2137_ = lean_ctor_get(v___x_2136_, 0);
lean_inc(v_a_2137_);
lean_dec_ref_known(v___x_2136_, 1);
v___x_2138_ = l_Lean_Exception_isInterrupt(v_a_2137_);
if (v___x_2138_ == 0)
{
uint8_t v___x_2139_; 
lean_inc(v_a_2137_);
v___x_2139_ = l_Lean_Exception_isRuntime(v_a_2137_);
v___y_2104_ = v___y_2002_;
v___y_2105_ = v_a_2137_;
v___y_2106_ = v___y_2000_;
v___y_2107_ = v_a_2134_;
v___y_2108_ = v___x_2139_;
goto v___jp_2103_;
}
else
{
v___y_2104_ = v___y_2002_;
v___y_2105_ = v_a_2137_;
v___y_2106_ = v___y_2000_;
v___y_2107_ = v_a_2134_;
v___y_2108_ = v___x_2138_;
goto v___jp_2103_;
}
}
}
else
{
lean_object* v_a_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2147_; 
lean_dec_ref(v_eNew_2130_);
lean_dec(v_a_2126_);
lean_dec(v_weight_1993_);
v_a_2140_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2142_ = v___x_2133_;
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_a_2140_);
lean_dec(v___x_2133_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2145_; 
if (v_isShared_2143_ == 0)
{
v___x_2145_ = v___x_2142_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_a_2140_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
return v___x_2145_;
}
}
}
}
default: 
{
lean_object* v___x_2148_; 
v___x_2148_ = l_Lean_Meta_saveState___redArg(v___y_2000_, v___y_2002_);
if (lean_obj_tag(v___x_2148_) == 0)
{
lean_object* v_a_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; 
v_a_2149_ = lean_ctor_get(v___x_2148_, 0);
lean_inc(v_a_2149_);
lean_dec_ref_known(v___x_2148_, 1);
v___x_2150_ = lean_unsigned_to_nat(6u);
lean_inc(v_mvarIds_2131_);
v___x_2151_ = l_Lean_Meta_Rewrites_solveByElim(v_mvarIds_2131_, v___x_2150_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
if (lean_obj_tag(v___x_2151_) == 0)
{
lean_dec_ref_known(v___x_2151_, 1);
lean_dec(v_a_2149_);
v___y_2061_ = v_eNew_2130_;
v___y_2062_ = v_a_2126_;
v___y_2063_ = v___x_2132_;
v___y_2064_ = v___x_2123_;
v___y_2065_ = v___y_1999_;
v___y_2066_ = v___y_2000_;
v___y_2067_ = v___y_2001_;
v___y_2068_ = v___y_2002_;
goto v___jp_2060_;
}
else
{
lean_object* v_a_2152_; uint8_t v___x_2153_; 
lean_dec_ref(v_eNew_2130_);
lean_dec(v_a_2126_);
lean_dec(v_weight_1993_);
v_a_2152_ = lean_ctor_get(v___x_2151_, 0);
lean_inc(v_a_2152_);
lean_dec_ref_known(v___x_2151_, 1);
v___x_2153_ = l_Lean_Exception_isInterrupt(v_a_2152_);
if (v___x_2153_ == 0)
{
uint8_t v___x_2154_; 
lean_inc(v_a_2152_);
v___x_2154_ = l_Lean_Exception_isRuntime(v_a_2152_);
v___y_2088_ = v___y_2002_;
v___y_2089_ = v_a_2152_;
v___y_2090_ = v_a_2149_;
v___y_2091_ = v___y_2000_;
v___y_2092_ = v___x_2154_;
goto v___jp_2087_;
}
else
{
v___y_2088_ = v___y_2002_;
v___y_2089_ = v_a_2152_;
v___y_2090_ = v_a_2149_;
v___y_2091_ = v___y_2000_;
v___y_2092_ = v___x_2153_;
goto v___jp_2087_;
}
}
}
else
{
lean_object* v_a_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2162_; 
lean_dec_ref(v_eNew_2130_);
lean_dec(v_a_2126_);
lean_dec(v_weight_1993_);
v_a_2155_ = lean_ctor_get(v___x_2148_, 0);
v_isSharedCheck_2162_ = !lean_is_exclusive(v___x_2148_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2157_ = v___x_2148_;
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_a_2155_);
lean_dec(v___x_2148_);
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
}
}
else
{
lean_object* v___x_2163_; lean_object* v_mctx_2164_; lean_object* v___x_2165_; 
v___x_2163_ = lean_st_ref_get(v___y_2000_);
v_mctx_2164_ = lean_ctor_get(v___x_2163_, 0);
lean_inc_ref_n(v_mctx_2164_, 2);
lean_dec(v___x_2163_);
lean_inc_ref(v_eNew_2130_);
v___x_2165_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(v_mctx_2164_, v_eNew_2130_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
if (lean_obj_tag(v___x_2165_) == 0)
{
lean_object* v_a_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2178_; 
v_a_2166_ = lean_ctor_get(v___x_2165_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2165_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2168_ = v___x_2165_;
v_isShared_2169_ = v_isSharedCheck_2178_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_a_2166_);
lean_dec(v___x_2165_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2178_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v___x_2170_; uint8_t v___x_2171_; lean_object* v___x_2173_; 
v___x_2170_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2170_, 0, v___y_2120_);
lean_ctor_set(v___x_2170_, 1, v_weight_1993_);
lean_ctor_set(v___x_2170_, 2, v_a_2126_);
lean_ctor_set(v___x_2170_, 3, v_mctx_2164_);
lean_ctor_set_uint8(v___x_2170_, sizeof(void*)*4, v_symm_1996_);
v___x_2171_ = lean_unbox(v_a_2166_);
lean_dec(v_a_2166_);
lean_ctor_set_uint8(v___x_2170_, sizeof(void*)*4 + 1, v___x_2171_);
if (v_isShared_2129_ == 0)
{
lean_ctor_set_tag(v___x_2128_, 1);
lean_ctor_set(v___x_2128_, 0, v___x_2170_);
v___x_2173_ = v___x_2128_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v___x_2170_);
v___x_2173_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
lean_object* v___x_2175_; 
if (v_isShared_2169_ == 0)
{
lean_ctor_set(v___x_2168_, 0, v___x_2173_);
v___x_2175_ = v___x_2168_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v___x_2173_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
return v___x_2175_;
}
}
}
}
else
{
lean_object* v_a_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2186_; 
lean_dec_ref(v_mctx_2164_);
lean_del_object(v___x_2128_);
lean_dec(v_a_2126_);
lean_dec_ref(v___y_2120_);
lean_dec(v_weight_1993_);
v_a_2179_ = lean_ctor_get(v___x_2165_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2165_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2181_ = v___x_2165_;
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_a_2179_);
lean_dec(v___x_2165_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2184_; 
if (v_isShared_2182_ == 0)
{
v___x_2184_ = v___x_2181_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_a_2179_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
}
}
}
}
else
{
lean_object* v_a_2188_; uint8_t v___x_2189_; 
lean_dec_ref(v___y_2120_);
lean_dec(v_weight_1993_);
v_a_2188_ = lean_ctor_get(v___x_2125_, 0);
lean_inc(v_a_2188_);
lean_dec_ref_known(v___x_2125_, 1);
v___x_2189_ = l_Lean_Exception_isInterrupt(v_a_2188_);
if (v___x_2189_ == 0)
{
uint8_t v___x_2190_; 
lean_inc(v_a_2188_);
v___x_2190_ = l_Lean_Exception_isRuntime(v_a_2188_);
v___y_2005_ = v___y_2002_;
v___y_2006_ = v_a_2122_;
v___y_2007_ = v_a_2188_;
v___y_2008_ = v___y_2000_;
v___y_2009_ = v___x_2190_;
goto v___jp_2004_;
}
else
{
v___y_2005_ = v___y_2002_;
v___y_2006_ = v_a_2122_;
v___y_2007_ = v_a_2188_;
v___y_2008_ = v___y_2000_;
v___y_2009_ = v___x_2189_;
goto v___jp_2004_;
}
}
}
else
{
lean_object* v_a_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2198_; 
lean_dec_ref(v___y_2120_);
lean_dec_ref(v_target_1995_);
lean_dec(v_goal_1994_);
lean_dec(v_weight_1993_);
v_a_2191_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2198_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2193_ = v___x_2121_;
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_a_2191_);
lean_dec(v___x_2121_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2196_; 
if (v_isShared_2194_ == 0)
{
v___x_2196_ = v___x_2193_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_a_2191_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
}
}
}
}
v___jp_2199_:
{
lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
lean_inc_ref(v___y_2203_);
v___x_2204_ = l_Lean_stringToMessageData(v___y_2203_);
lean_inc_ref(v___y_2201_);
v___x_2205_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2205_, 0, v___y_2201_);
lean_ctor_set(v___x_2205_, 1, v___x_2204_);
lean_inc_ref(v___y_2200_);
v___x_2206_ = l_Lean_MessageData_ofExpr(v___y_2200_);
v___x_2207_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2205_);
lean_ctor_set(v___x_2207_, 1, v___x_2206_);
lean_inc(v___y_2202_);
v___x_2208_ = l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2(v___y_2202_, v___x_2207_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
if (lean_obj_tag(v___x_2208_) == 0)
{
lean_dec_ref_known(v___x_2208_, 1);
v___y_2120_ = v___y_2200_;
goto v___jp_2119_;
}
else
{
lean_object* v_a_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2216_; 
lean_dec_ref(v___y_2200_);
lean_dec_ref(v_target_1995_);
lean_dec(v_goal_1994_);
lean_dec(v_weight_1993_);
v_a_2209_ = lean_ctor_get(v___x_2208_, 0);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2208_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2211_ = v___x_2208_;
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_a_2209_);
lean_dec(v___x_2208_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v___x_2214_; 
if (v_isShared_2212_ == 0)
{
v___x_2214_ = v___x_2211_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v_a_2209_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
return v___x_2214_;
}
}
}
}
v___jp_2217_:
{
lean_object* v_options_2219_; uint8_t v_hasTrace_2220_; 
v_options_2219_ = lean_ctor_get(v___y_2001_, 2);
v_hasTrace_2220_ = lean_ctor_get_uint8(v_options_2219_, sizeof(void*)*1);
if (v_hasTrace_2220_ == 0)
{
v___y_2120_ = v_val_2218_;
goto v___jp_2119_;
}
else
{
lean_object* v_inheritedTraceOptions_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; uint8_t v___x_2224_; 
v_inheritedTraceOptions_2221_ = lean_ctor_get(v___y_2001_, 13);
v___x_2222_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_));
v___x_2223_ = lean_obj_once(&l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5, &l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5_once, _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5);
v___x_2224_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2221_, v_options_2219_, v___x_2223_);
if (v___x_2224_ == 0)
{
v___y_2120_ = v_val_2218_;
goto v___jp_2119_;
}
else
{
lean_object* v___x_2225_; 
v___x_2225_ = lean_obj_once(&l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__7, &l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__7_once, _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__7);
if (v_symm_1996_ == 0)
{
lean_object* v___x_2226_; 
v___x_2226_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__1));
v___y_2200_ = v_val_2218_;
v___y_2201_ = v___x_2225_;
v___y_2202_ = v___x_2222_;
v___y_2203_ = v___x_2226_;
goto v___jp_2199_;
}
else
{
lean_object* v___x_2227_; 
v___x_2227_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__8));
v___y_2200_ = v_val_2218_;
v___y_2201_ = v___x_2225_;
v___y_2202_ = v___x_2222_;
v___y_2203_ = v___x_2227_;
goto v___jp_2199_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0___boxed(lean_object* v_weight_2272_, lean_object* v_goal_2273_, lean_object* v_target_2274_, lean_object* v_symm_2275_, lean_object* v_side_2276_, lean_object* v_lem_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
uint8_t v_symm_boxed_2283_; uint8_t v_side_boxed_2284_; lean_object* v_res_2285_; 
v_symm_boxed_2283_ = lean_unbox(v_symm_2275_);
v_side_boxed_2284_ = lean_unbox(v_side_2276_);
v_res_2285_ = l_Lean_Meta_Rewrites_rwLemma___lam__0(v_weight_2272_, v_goal_2273_, v_target_2274_, v_symm_boxed_2283_, v_side_boxed_2284_, v_lem_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
return v_res_2285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma(lean_object* v_ctx_2286_, lean_object* v_goal_2287_, lean_object* v_target_2288_, uint8_t v_side_2289_, lean_object* v_lem_2290_, uint8_t v_symm_2291_, lean_object* v_weight_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_){
_start:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___f_2300_; lean_object* v___x_2301_; 
v___x_2298_ = lean_box(v_symm_2291_);
v___x_2299_ = lean_box(v_side_2289_);
v___f_2300_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___boxed), 11, 6);
lean_closure_set(v___f_2300_, 0, v_weight_2292_);
lean_closure_set(v___f_2300_, 1, v_goal_2287_);
lean_closure_set(v___f_2300_, 2, v_target_2288_);
lean_closure_set(v___f_2300_, 3, v___x_2298_);
lean_closure_set(v___f_2300_, 4, v___x_2299_);
lean_closure_set(v___f_2300_, 5, v_lem_2290_);
v___x_2301_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg(v_ctx_2286_, v___f_2300_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
return v___x_2301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___boxed(lean_object* v_ctx_2302_, lean_object* v_goal_2303_, lean_object* v_target_2304_, lean_object* v_side_2305_, lean_object* v_lem_2306_, lean_object* v_symm_2307_, lean_object* v_weight_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_){
_start:
{
uint8_t v_side_boxed_2314_; uint8_t v_symm_boxed_2315_; lean_object* v_res_2316_; 
v_side_boxed_2314_ = lean_unbox(v_side_2305_);
v_symm_boxed_2315_ = lean_unbox(v_symm_2307_);
v_res_2316_ = l_Lean_Meta_Rewrites_rwLemma(v_ctx_2302_, v_goal_2303_, v_target_2304_, v_side_boxed_2314_, v_lem_2306_, v_symm_boxed_2315_, v_weight_2308_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_);
lean_dec(v_a_2312_);
lean_dec_ref(v_a_2311_);
lean_dec(v_a_2310_);
lean_dec_ref(v_a_2309_);
return v_res_2316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(lean_object* v_type_2317_, lean_object* v_k_2318_, uint8_t v_cleanupAnnotations_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_){
_start:
{
lean_object* v___f_2325_; uint8_t v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; 
v___f_2325_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2325_, 0, v_k_2318_);
v___x_2326_ = 0;
v___x_2327_ = lean_box(0);
v___x_2328_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_2326_, v___x_2327_, v_type_2317_, v___f_2325_, v_cleanupAnnotations_2319_, v___x_2326_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_);
if (lean_obj_tag(v___x_2328_) == 0)
{
lean_object* v_a_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2336_; 
v_a_2329_ = lean_ctor_get(v___x_2328_, 0);
v_isSharedCheck_2336_ = !lean_is_exclusive(v___x_2328_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2331_ = v___x_2328_;
v_isShared_2332_ = v_isSharedCheck_2336_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_a_2329_);
lean_dec(v___x_2328_);
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
v_reuseFailAlloc_2335_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2344_; 
v_a_2337_ = lean_ctor_get(v___x_2328_, 0);
v_isSharedCheck_2344_ = !lean_is_exclusive(v___x_2328_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2339_ = v___x_2328_;
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_a_2337_);
lean_dec(v___x_2328_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v___x_2342_; 
if (v_isShared_2340_ == 0)
{
v___x_2342_ = v___x_2339_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v_a_2337_);
v___x_2342_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
return v___x_2342_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg___boxed(lean_object* v_type_2345_, lean_object* v_k_2346_, lean_object* v_cleanupAnnotations_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2353_; lean_object* v_res_2354_; 
v_cleanupAnnotations_boxed_2353_ = lean_unbox(v_cleanupAnnotations_2347_);
v_res_2354_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(v_type_2345_, v_k_2346_, v_cleanupAnnotations_boxed_2353_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
lean_dec(v___y_2349_);
lean_dec_ref(v___y_2348_);
return v_res_2354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1(lean_object* v_00_u03b1_2355_, lean_object* v_type_2356_, lean_object* v_k_2357_, uint8_t v_cleanupAnnotations_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_){
_start:
{
lean_object* v___x_2364_; 
v___x_2364_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(v_type_2356_, v_k_2357_, v_cleanupAnnotations_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_);
return v___x_2364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___boxed(lean_object* v_00_u03b1_2365_, lean_object* v_type_2366_, lean_object* v_k_2367_, lean_object* v_cleanupAnnotations_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2374_; lean_object* v_res_2375_; 
v_cleanupAnnotations_boxed_2374_ = lean_unbox(v_cleanupAnnotations_2368_);
v_res_2375_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1(v_00_u03b1_2365_, v_type_2366_, v_k_2367_, v_cleanupAnnotations_boxed_2374_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_);
lean_dec(v___y_2372_);
lean_dec_ref(v___y_2371_);
lean_dec(v___y_2370_);
lean_dec_ref(v___y_2369_);
return v_res_2375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(lean_object* v_e_2376_, lean_object* v_k_2377_, uint8_t v_cleanupAnnotations_2378_, uint8_t v_preserveNondepLet_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_){
_start:
{
lean_object* v___f_2385_; uint8_t v___x_2386_; uint8_t v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; 
v___f_2385_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2385_, 0, v_k_2377_);
v___x_2386_ = 1;
v___x_2387_ = 0;
v___x_2388_ = lean_box(0);
v___x_2389_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2376_, v___x_2386_, v___x_2386_, v_preserveNondepLet_2379_, v___x_2387_, v___x_2388_, v___f_2385_, v_cleanupAnnotations_2378_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_);
if (lean_obj_tag(v___x_2389_) == 0)
{
lean_object* v_a_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2397_; 
v_a_2390_ = lean_ctor_get(v___x_2389_, 0);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2389_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2392_ = v___x_2389_;
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_a_2390_);
lean_dec(v___x_2389_);
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
v_reuseFailAlloc_2396_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2405_; 
v_a_2398_ = lean_ctor_get(v___x_2389_, 0);
v_isSharedCheck_2405_ = !lean_is_exclusive(v___x_2389_);
if (v_isSharedCheck_2405_ == 0)
{
v___x_2400_ = v___x_2389_;
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_a_2398_);
lean_dec(v___x_2389_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg___boxed(lean_object* v_e_2406_, lean_object* v_k_2407_, lean_object* v_cleanupAnnotations_2408_, lean_object* v_preserveNondepLet_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2415_; uint8_t v_preserveNondepLet_boxed_2416_; lean_object* v_res_2417_; 
v_cleanupAnnotations_boxed_2415_ = lean_unbox(v_cleanupAnnotations_2408_);
v_preserveNondepLet_boxed_2416_ = lean_unbox(v_preserveNondepLet_2409_);
v_res_2417_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(v_e_2406_, v_k_2407_, v_cleanupAnnotations_boxed_2415_, v_preserveNondepLet_boxed_2416_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_);
lean_dec(v___y_2413_);
lean_dec_ref(v___y_2412_);
lean_dec(v___y_2411_);
lean_dec_ref(v___y_2410_);
return v_res_2417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2(lean_object* v_00_u03b1_2418_, lean_object* v_e_2419_, lean_object* v_k_2420_, uint8_t v_cleanupAnnotations_2421_, uint8_t v_preserveNondepLet_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_){
_start:
{
lean_object* v___x_2428_; 
v___x_2428_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(v_e_2419_, v_k_2420_, v_cleanupAnnotations_2421_, v_preserveNondepLet_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_);
return v___x_2428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___boxed(lean_object* v_00_u03b1_2429_, lean_object* v_e_2430_, lean_object* v_k_2431_, lean_object* v_cleanupAnnotations_2432_, lean_object* v_preserveNondepLet_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2439_; uint8_t v_preserveNondepLet_boxed_2440_; lean_object* v_res_2441_; 
v_cleanupAnnotations_boxed_2439_ = lean_unbox(v_cleanupAnnotations_2432_);
v_preserveNondepLet_boxed_2440_ = lean_unbox(v_preserveNondepLet_2433_);
v_res_2441_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2(v_00_u03b1_2429_, v_e_2430_, v_k_2431_, v_cleanupAnnotations_boxed_2439_, v_preserveNondepLet_boxed_2440_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_);
lean_dec(v___y_2437_);
lean_dec_ref(v___y_2436_);
lean_dec(v___y_2435_);
lean_dec_ref(v___y_2434_);
return v_res_2441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(lean_object* v_f_2442_, lean_object* v_e_x27_2443_, lean_object* v_a_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_){
_start:
{
lean_object* v___x_2450_; 
lean_inc(v___y_2448_);
lean_inc_ref(v___y_2447_);
lean_inc(v___y_2446_);
lean_inc_ref(v___y_2445_);
lean_inc_ref(v_e_x27_2443_);
v___x_2450_ = lean_apply_7(v_f_2442_, v_a_2444_, v_e_x27_2443_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, lean_box(0));
if (lean_obj_tag(v___x_2450_) == 0)
{
lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2459_; 
v_a_2451_ = lean_ctor_get(v___x_2450_, 0);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2453_ = v___x_2450_;
v_isShared_2454_ = v_isSharedCheck_2459_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v___x_2450_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2459_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2455_; lean_object* v___x_2457_; 
v___x_2455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2455_, 0, v_e_x27_2443_);
lean_ctor_set(v___x_2455_, 1, v_a_2451_);
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 0, v___x_2455_);
v___x_2457_ = v___x_2453_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v___x_2455_);
v___x_2457_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
return v___x_2457_;
}
}
}
else
{
lean_object* v_a_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2467_; 
lean_dec_ref(v_e_x27_2443_);
v_a_2460_ = lean_ctor_get(v___x_2450_, 0);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2462_ = v___x_2450_;
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_a_2460_);
lean_dec(v___x_2450_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___x_2465_; 
if (v_isShared_2463_ == 0)
{
v___x_2465_ = v___x_2462_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v_a_2460_);
v___x_2465_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
return v___x_2465_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0___boxed(lean_object* v_f_2468_, lean_object* v_e_x27_2469_, lean_object* v_a_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_){
_start:
{
lean_object* v_res_2476_; 
v_res_2476_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2468_, v_e_x27_2469_, v_a_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_);
lean_dec(v___y_2474_);
lean_dec_ref(v___y_2473_);
lean_dec(v___y_2472_);
lean_dec_ref(v___y_2471_);
return v_res_2476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg(lean_object* v_f_2477_, lean_object* v_x_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_){
_start:
{
switch(lean_obj_tag(v_x_2478_))
{
case 7:
{
lean_object* v_binderName_2485_; lean_object* v_binderType_2486_; lean_object* v_body_2487_; uint8_t v_binderInfo_2488_; lean_object* v___x_2489_; 
v_binderName_2485_ = lean_ctor_get(v_x_2478_, 0);
v_binderType_2486_ = lean_ctor_get(v_x_2478_, 1);
v_body_2487_ = lean_ctor_get(v_x_2478_, 2);
v_binderInfo_2488_ = lean_ctor_get_uint8(v_x_2478_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2486_);
lean_inc_ref(v_f_2477_);
v___x_2489_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2477_, v_binderType_2486_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_);
if (lean_obj_tag(v___x_2489_) == 0)
{
lean_object* v_a_2490_; lean_object* v_fst_2491_; lean_object* v_snd_2492_; lean_object* v___x_2493_; 
v_a_2490_ = lean_ctor_get(v___x_2489_, 0);
lean_inc(v_a_2490_);
lean_dec_ref_known(v___x_2489_, 1);
v_fst_2491_ = lean_ctor_get(v_a_2490_, 0);
lean_inc(v_fst_2491_);
v_snd_2492_ = lean_ctor_get(v_a_2490_, 1);
lean_inc(v_snd_2492_);
lean_dec(v_a_2490_);
lean_inc_ref(v_body_2487_);
v___x_2493_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2477_, v_body_2487_, v_snd_2492_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_);
if (lean_obj_tag(v___x_2493_) == 0)
{
lean_object* v_a_2494_; lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2523_; 
v_a_2494_ = lean_ctor_get(v___x_2493_, 0);
v_isSharedCheck_2523_ = !lean_is_exclusive(v___x_2493_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2496_ = v___x_2493_;
v_isShared_2497_ = v_isSharedCheck_2523_;
goto v_resetjp_2495_;
}
else
{
lean_inc(v_a_2494_);
lean_dec(v___x_2493_);
v___x_2496_ = lean_box(0);
v_isShared_2497_ = v_isSharedCheck_2523_;
goto v_resetjp_2495_;
}
v_resetjp_2495_:
{
lean_object* v_fst_2498_; lean_object* v_snd_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2522_; 
v_fst_2498_ = lean_ctor_get(v_a_2494_, 0);
v_snd_2499_ = lean_ctor_get(v_a_2494_, 1);
v_isSharedCheck_2522_ = !lean_is_exclusive(v_a_2494_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2501_ = v_a_2494_;
v_isShared_2502_ = v_isSharedCheck_2522_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_snd_2499_);
lean_inc(v_fst_2498_);
lean_dec(v_a_2494_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2522_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v___y_2504_; uint8_t v___y_2512_; size_t v___x_2516_; size_t v___x_2517_; uint8_t v___x_2518_; 
v___x_2516_ = lean_ptr_addr(v_binderType_2486_);
v___x_2517_ = lean_ptr_addr(v_fst_2491_);
v___x_2518_ = lean_usize_dec_eq(v___x_2516_, v___x_2517_);
if (v___x_2518_ == 0)
{
v___y_2512_ = v___x_2518_;
goto v___jp_2511_;
}
else
{
size_t v___x_2519_; size_t v___x_2520_; uint8_t v___x_2521_; 
v___x_2519_ = lean_ptr_addr(v_body_2487_);
v___x_2520_ = lean_ptr_addr(v_fst_2498_);
v___x_2521_ = lean_usize_dec_eq(v___x_2519_, v___x_2520_);
v___y_2512_ = v___x_2521_;
goto v___jp_2511_;
}
v___jp_2503_:
{
lean_object* v___x_2506_; 
if (v_isShared_2502_ == 0)
{
lean_ctor_set(v___x_2501_, 0, v___y_2504_);
v___x_2506_ = v___x_2501_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v___y_2504_);
lean_ctor_set(v_reuseFailAlloc_2510_, 1, v_snd_2499_);
v___x_2506_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
lean_object* v___x_2508_; 
if (v_isShared_2497_ == 0)
{
lean_ctor_set(v___x_2496_, 0, v___x_2506_);
v___x_2508_ = v___x_2496_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v___x_2506_);
v___x_2508_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
return v___x_2508_;
}
}
}
v___jp_2511_:
{
if (v___y_2512_ == 0)
{
lean_object* v___x_2513_; 
lean_inc(v_binderName_2485_);
lean_dec_ref_known(v_x_2478_, 3);
v___x_2513_ = l_Lean_Expr_forallE___override(v_binderName_2485_, v_fst_2491_, v_fst_2498_, v_binderInfo_2488_);
v___y_2504_ = v___x_2513_;
goto v___jp_2503_;
}
else
{
uint8_t v___x_2514_; 
v___x_2514_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2488_, v_binderInfo_2488_);
if (v___x_2514_ == 0)
{
lean_object* v___x_2515_; 
lean_inc(v_binderName_2485_);
lean_dec_ref_known(v_x_2478_, 3);
v___x_2515_ = l_Lean_Expr_forallE___override(v_binderName_2485_, v_fst_2491_, v_fst_2498_, v_binderInfo_2488_);
v___y_2504_ = v___x_2515_;
goto v___jp_2503_;
}
else
{
lean_dec(v_fst_2498_);
lean_dec(v_fst_2491_);
v___y_2504_ = v_x_2478_;
goto v___jp_2503_;
}
}
}
}
}
}
else
{
lean_dec(v_fst_2491_);
lean_dec_ref_known(v_x_2478_, 3);
return v___x_2493_;
}
}
else
{
lean_dec_ref_known(v_x_2478_, 3);
lean_dec_ref(v_f_2477_);
return v___x_2489_;
}
}
case 6:
{
lean_object* v_binderName_2524_; lean_object* v_binderType_2525_; lean_object* v_body_2526_; uint8_t v_binderInfo_2527_; lean_object* v___x_2528_; 
v_binderName_2524_ = lean_ctor_get(v_x_2478_, 0);
v_binderType_2525_ = lean_ctor_get(v_x_2478_, 1);
v_body_2526_ = lean_ctor_get(v_x_2478_, 2);
v_binderInfo_2527_ = lean_ctor_get_uint8(v_x_2478_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2525_);
lean_inc_ref(v_f_2477_);
v___x_2528_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2477_, v_binderType_2525_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_);
if (lean_obj_tag(v___x_2528_) == 0)
{
lean_object* v_a_2529_; lean_object* v_fst_2530_; lean_object* v_snd_2531_; lean_object* v___x_2532_; 
v_a_2529_ = lean_ctor_get(v___x_2528_, 0);
lean_inc(v_a_2529_);
lean_dec_ref_known(v___x_2528_, 1);
v_fst_2530_ = lean_ctor_get(v_a_2529_, 0);
lean_inc(v_fst_2530_);
v_snd_2531_ = lean_ctor_get(v_a_2529_, 1);
lean_inc(v_snd_2531_);
lean_dec(v_a_2529_);
lean_inc_ref(v_body_2526_);
v___x_2532_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2477_, v_body_2526_, v_snd_2531_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_object* v_a_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2562_; 
v_a_2533_ = lean_ctor_get(v___x_2532_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2535_ = v___x_2532_;
v_isShared_2536_ = v_isSharedCheck_2562_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_a_2533_);
lean_dec(v___x_2532_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2562_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v_fst_2537_; lean_object* v_snd_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2561_; 
v_fst_2537_ = lean_ctor_get(v_a_2533_, 0);
v_snd_2538_ = lean_ctor_get(v_a_2533_, 1);
v_isSharedCheck_2561_ = !lean_is_exclusive(v_a_2533_);
if (v_isSharedCheck_2561_ == 0)
{
v___x_2540_ = v_a_2533_;
v_isShared_2541_ = v_isSharedCheck_2561_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_snd_2538_);
lean_inc(v_fst_2537_);
lean_dec(v_a_2533_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2561_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___y_2543_; uint8_t v___y_2551_; size_t v___x_2555_; size_t v___x_2556_; uint8_t v___x_2557_; 
v___x_2555_ = lean_ptr_addr(v_binderType_2525_);
v___x_2556_ = lean_ptr_addr(v_fst_2530_);
v___x_2557_ = lean_usize_dec_eq(v___x_2555_, v___x_2556_);
if (v___x_2557_ == 0)
{
v___y_2551_ = v___x_2557_;
goto v___jp_2550_;
}
else
{
size_t v___x_2558_; size_t v___x_2559_; uint8_t v___x_2560_; 
v___x_2558_ = lean_ptr_addr(v_body_2526_);
v___x_2559_ = lean_ptr_addr(v_fst_2537_);
v___x_2560_ = lean_usize_dec_eq(v___x_2558_, v___x_2559_);
v___y_2551_ = v___x_2560_;
goto v___jp_2550_;
}
v___jp_2542_:
{
lean_object* v___x_2545_; 
if (v_isShared_2541_ == 0)
{
lean_ctor_set(v___x_2540_, 0, v___y_2543_);
v___x_2545_ = v___x_2540_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v___y_2543_);
lean_ctor_set(v_reuseFailAlloc_2549_, 1, v_snd_2538_);
v___x_2545_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
lean_object* v___x_2547_; 
if (v_isShared_2536_ == 0)
{
lean_ctor_set(v___x_2535_, 0, v___x_2545_);
v___x_2547_ = v___x_2535_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v___x_2545_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
return v___x_2547_;
}
}
}
v___jp_2550_:
{
if (v___y_2551_ == 0)
{
lean_object* v___x_2552_; 
lean_inc(v_binderName_2524_);
lean_dec_ref_known(v_x_2478_, 3);
v___x_2552_ = l_Lean_Expr_lam___override(v_binderName_2524_, v_fst_2530_, v_fst_2537_, v_binderInfo_2527_);
v___y_2543_ = v___x_2552_;
goto v___jp_2542_;
}
else
{
uint8_t v___x_2553_; 
v___x_2553_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2527_, v_binderInfo_2527_);
if (v___x_2553_ == 0)
{
lean_object* v___x_2554_; 
lean_inc(v_binderName_2524_);
lean_dec_ref_known(v_x_2478_, 3);
v___x_2554_ = l_Lean_Expr_lam___override(v_binderName_2524_, v_fst_2530_, v_fst_2537_, v_binderInfo_2527_);
v___y_2543_ = v___x_2554_;
goto v___jp_2542_;
}
else
{
lean_dec(v_fst_2537_);
lean_dec(v_fst_2530_);
v___y_2543_ = v_x_2478_;
goto v___jp_2542_;
}
}
}
}
}
}
else
{
lean_dec(v_fst_2530_);
lean_dec_ref_known(v_x_2478_, 3);
return v___x_2532_;
}
}
else
{
lean_dec_ref_known(v_x_2478_, 3);
lean_dec_ref(v_f_2477_);
return v___x_2528_;
}
}
case 10:
{
lean_object* v_data_2563_; lean_object* v_expr_2564_; lean_object* v___x_2565_; 
v_data_2563_ = lean_ctor_get(v_x_2478_, 0);
v_expr_2564_ = lean_ctor_get(v_x_2478_, 1);
lean_inc_ref(v_expr_2564_);
v___x_2565_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2477_, v_expr_2564_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_);
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v_a_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2588_; 
v_a_2566_ = lean_ctor_get(v___x_2565_, 0);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2568_ = v___x_2565_;
v_isShared_2569_ = v_isSharedCheck_2588_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_a_2566_);
lean_dec(v___x_2565_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2588_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v_fst_2570_; lean_object* v_snd_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2587_; 
v_fst_2570_ = lean_ctor_get(v_a_2566_, 0);
v_snd_2571_ = lean_ctor_get(v_a_2566_, 1);
v_isSharedCheck_2587_ = !lean_is_exclusive(v_a_2566_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2573_ = v_a_2566_;
v_isShared_2574_ = v_isSharedCheck_2587_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_snd_2571_);
lean_inc(v_fst_2570_);
lean_dec(v_a_2566_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2587_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v___y_2576_; size_t v___x_2583_; size_t v___x_2584_; uint8_t v___x_2585_; 
v___x_2583_ = lean_ptr_addr(v_expr_2564_);
v___x_2584_ = lean_ptr_addr(v_fst_2570_);
v___x_2585_ = lean_usize_dec_eq(v___x_2583_, v___x_2584_);
if (v___x_2585_ == 0)
{
lean_object* v___x_2586_; 
lean_inc(v_data_2563_);
lean_dec_ref_known(v_x_2478_, 2);
v___x_2586_ = l_Lean_Expr_mdata___override(v_data_2563_, v_fst_2570_);
v___y_2576_ = v___x_2586_;
goto v___jp_2575_;
}
else
{
lean_dec(v_fst_2570_);
v___y_2576_ = v_x_2478_;
goto v___jp_2575_;
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
lean_dec_ref_known(v_x_2478_, 2);
return v___x_2565_;
}
}
case 8:
{
lean_object* v_declName_2589_; lean_object* v_type_2590_; lean_object* v_value_2591_; lean_object* v_body_2592_; uint8_t v_nondep_2593_; lean_object* v___x_2594_; 
v_declName_2589_ = lean_ctor_get(v_x_2478_, 0);
v_type_2590_ = lean_ctor_get(v_x_2478_, 1);
v_value_2591_ = lean_ctor_get(v_x_2478_, 2);
v_body_2592_ = lean_ctor_get(v_x_2478_, 3);
v_nondep_2593_ = lean_ctor_get_uint8(v_x_2478_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_2590_);
lean_inc_ref(v_f_2477_);
v___x_2594_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2477_, v_type_2590_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_);
if (lean_obj_tag(v___x_2594_) == 0)
{
lean_object* v_a_2595_; lean_object* v_fst_2596_; lean_object* v_snd_2597_; lean_object* v___x_2598_; 
v_a_2595_ = lean_ctor_get(v___x_2594_, 0);
lean_inc(v_a_2595_);
lean_dec_ref_known(v___x_2594_, 1);
v_fst_2596_ = lean_ctor_get(v_a_2595_, 0);
lean_inc(v_fst_2596_);
v_snd_2597_ = lean_ctor_get(v_a_2595_, 1);
lean_inc(v_snd_2597_);
lean_dec(v_a_2595_);
lean_inc_ref(v_value_2591_);
lean_inc_ref(v_f_2477_);
v___x_2598_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2477_, v_value_2591_, v_snd_2597_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_);
if (lean_obj_tag(v___x_2598_) == 0)
{
lean_object* v_a_2599_; lean_object* v_fst_2600_; lean_object* v_snd_2601_; lean_object* v___x_2602_; 
v_a_2599_ = lean_ctor_get(v___x_2598_, 0);
lean_inc(v_a_2599_);
lean_dec_ref_known(v___x_2598_, 1);
v_fst_2600_ = lean_ctor_get(v_a_2599_, 0);
lean_inc(v_fst_2600_);
v_snd_2601_ = lean_ctor_get(v_a_2599_, 1);
lean_inc(v_snd_2601_);
lean_dec(v_a_2599_);
lean_inc_ref(v_body_2592_);
v___x_2602_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2477_, v_body_2592_, v_snd_2601_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_);
if (lean_obj_tag(v___x_2602_) == 0)
{
lean_object* v_a_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2634_; 
v_a_2603_ = lean_ctor_get(v___x_2602_, 0);
v_isSharedCheck_2634_ = !lean_is_exclusive(v___x_2602_);
if (v_isSharedCheck_2634_ == 0)
{
v___x_2605_ = v___x_2602_;
v_isShared_2606_ = v_isSharedCheck_2634_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_a_2603_);
lean_dec(v___x_2602_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2634_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v_fst_2607_; lean_object* v_snd_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2633_; 
v_fst_2607_ = lean_ctor_get(v_a_2603_, 0);
v_snd_2608_ = lean_ctor_get(v_a_2603_, 1);
v_isSharedCheck_2633_ = !lean_is_exclusive(v_a_2603_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2610_ = v_a_2603_;
v_isShared_2611_ = v_isSharedCheck_2633_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_snd_2608_);
lean_inc(v_fst_2607_);
lean_dec(v_a_2603_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2633_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___y_2613_; uint8_t v___y_2621_; size_t v___x_2627_; size_t v___x_2628_; uint8_t v___x_2629_; 
v___x_2627_ = lean_ptr_addr(v_type_2590_);
v___x_2628_ = lean_ptr_addr(v_fst_2596_);
v___x_2629_ = lean_usize_dec_eq(v___x_2627_, v___x_2628_);
if (v___x_2629_ == 0)
{
v___y_2621_ = v___x_2629_;
goto v___jp_2620_;
}
else
{
size_t v___x_2630_; size_t v___x_2631_; uint8_t v___x_2632_; 
v___x_2630_ = lean_ptr_addr(v_value_2591_);
v___x_2631_ = lean_ptr_addr(v_fst_2600_);
v___x_2632_ = lean_usize_dec_eq(v___x_2630_, v___x_2631_);
v___y_2621_ = v___x_2632_;
goto v___jp_2620_;
}
v___jp_2612_:
{
lean_object* v___x_2615_; 
if (v_isShared_2611_ == 0)
{
lean_ctor_set(v___x_2610_, 0, v___y_2613_);
v___x_2615_ = v___x_2610_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v___y_2613_);
lean_ctor_set(v_reuseFailAlloc_2619_, 1, v_snd_2608_);
v___x_2615_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
lean_object* v___x_2617_; 
if (v_isShared_2606_ == 0)
{
lean_ctor_set(v___x_2605_, 0, v___x_2615_);
v___x_2617_ = v___x_2605_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v___x_2615_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
return v___x_2617_;
}
}
}
v___jp_2620_:
{
if (v___y_2621_ == 0)
{
lean_object* v___x_2622_; 
lean_inc(v_declName_2589_);
lean_dec_ref_known(v_x_2478_, 4);
v___x_2622_ = l_Lean_Expr_letE___override(v_declName_2589_, v_fst_2596_, v_fst_2600_, v_fst_2607_, v_nondep_2593_);
v___y_2613_ = v___x_2622_;
goto v___jp_2612_;
}
else
{
size_t v___x_2623_; size_t v___x_2624_; uint8_t v___x_2625_; 
v___x_2623_ = lean_ptr_addr(v_body_2592_);
v___x_2624_ = lean_ptr_addr(v_fst_2607_);
v___x_2625_ = lean_usize_dec_eq(v___x_2623_, v___x_2624_);
if (v___x_2625_ == 0)
{
lean_object* v___x_2626_; 
lean_inc(v_declName_2589_);
lean_dec_ref_known(v_x_2478_, 4);
v___x_2626_ = l_Lean_Expr_letE___override(v_declName_2589_, v_fst_2596_, v_fst_2600_, v_fst_2607_, v_nondep_2593_);
v___y_2613_ = v___x_2626_;
goto v___jp_2612_;
}
else
{
lean_dec(v_fst_2607_);
lean_dec(v_fst_2600_);
lean_dec(v_fst_2596_);
v___y_2613_ = v_x_2478_;
goto v___jp_2612_;
}
}
}
}
}
}
else
{
lean_dec(v_fst_2600_);
lean_dec(v_fst_2596_);
lean_dec_ref_known(v_x_2478_, 4);
return v___x_2602_;
}
}
else
{
lean_dec(v_fst_2596_);
lean_dec_ref_known(v_x_2478_, 4);
lean_dec_ref(v_f_2477_);
return v___x_2598_;
}
}
else
{
lean_dec_ref_known(v_x_2478_, 4);
lean_dec_ref(v_f_2477_);
return v___x_2594_;
}
}
case 5:
{
lean_object* v_fn_2635_; lean_object* v_arg_2636_; lean_object* v___x_2637_; 
v_fn_2635_ = lean_ctor_get(v_x_2478_, 0);
v_arg_2636_ = lean_ctor_get(v_x_2478_, 1);
lean_inc_ref(v_fn_2635_);
lean_inc_ref(v_f_2477_);
v___x_2637_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2477_, v_fn_2635_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_);
if (lean_obj_tag(v___x_2637_) == 0)
{
lean_object* v_a_2638_; lean_object* v_fst_2639_; lean_object* v_snd_2640_; lean_object* v___x_2641_; 
v_a_2638_ = lean_ctor_get(v___x_2637_, 0);
lean_inc(v_a_2638_);
lean_dec_ref_known(v___x_2637_, 1);
v_fst_2639_ = lean_ctor_get(v_a_2638_, 0);
lean_inc(v_fst_2639_);
v_snd_2640_ = lean_ctor_get(v_a_2638_, 1);
lean_inc(v_snd_2640_);
lean_dec(v_a_2638_);
lean_inc_ref(v_arg_2636_);
v___x_2641_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2477_, v_arg_2636_, v_snd_2640_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_);
if (lean_obj_tag(v___x_2641_) == 0)
{
lean_object* v_a_2642_; lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_2669_; 
v_a_2642_ = lean_ctor_get(v___x_2641_, 0);
v_isSharedCheck_2669_ = !lean_is_exclusive(v___x_2641_);
if (v_isSharedCheck_2669_ == 0)
{
v___x_2644_ = v___x_2641_;
v_isShared_2645_ = v_isSharedCheck_2669_;
goto v_resetjp_2643_;
}
else
{
lean_inc(v_a_2642_);
lean_dec(v___x_2641_);
v___x_2644_ = lean_box(0);
v_isShared_2645_ = v_isSharedCheck_2669_;
goto v_resetjp_2643_;
}
v_resetjp_2643_:
{
lean_object* v_fst_2646_; lean_object* v_snd_2647_; lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2668_; 
v_fst_2646_ = lean_ctor_get(v_a_2642_, 0);
v_snd_2647_ = lean_ctor_get(v_a_2642_, 1);
v_isSharedCheck_2668_ = !lean_is_exclusive(v_a_2642_);
if (v_isSharedCheck_2668_ == 0)
{
v___x_2649_ = v_a_2642_;
v_isShared_2650_ = v_isSharedCheck_2668_;
goto v_resetjp_2648_;
}
else
{
lean_inc(v_snd_2647_);
lean_inc(v_fst_2646_);
lean_dec(v_a_2642_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2668_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
lean_object* v___y_2652_; uint8_t v___y_2660_; size_t v___x_2662_; size_t v___x_2663_; uint8_t v___x_2664_; 
v___x_2662_ = lean_ptr_addr(v_fn_2635_);
v___x_2663_ = lean_ptr_addr(v_fst_2639_);
v___x_2664_ = lean_usize_dec_eq(v___x_2662_, v___x_2663_);
if (v___x_2664_ == 0)
{
v___y_2660_ = v___x_2664_;
goto v___jp_2659_;
}
else
{
size_t v___x_2665_; size_t v___x_2666_; uint8_t v___x_2667_; 
v___x_2665_ = lean_ptr_addr(v_arg_2636_);
v___x_2666_ = lean_ptr_addr(v_fst_2646_);
v___x_2667_ = lean_usize_dec_eq(v___x_2665_, v___x_2666_);
v___y_2660_ = v___x_2667_;
goto v___jp_2659_;
}
v___jp_2651_:
{
lean_object* v___x_2654_; 
if (v_isShared_2650_ == 0)
{
lean_ctor_set(v___x_2649_, 0, v___y_2652_);
v___x_2654_ = v___x_2649_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v___y_2652_);
lean_ctor_set(v_reuseFailAlloc_2658_, 1, v_snd_2647_);
v___x_2654_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
lean_object* v___x_2656_; 
if (v_isShared_2645_ == 0)
{
lean_ctor_set(v___x_2644_, 0, v___x_2654_);
v___x_2656_ = v___x_2644_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v___x_2654_);
v___x_2656_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
return v___x_2656_;
}
}
}
v___jp_2659_:
{
if (v___y_2660_ == 0)
{
lean_object* v___x_2661_; 
lean_dec_ref_known(v_x_2478_, 2);
v___x_2661_ = l_Lean_Expr_app___override(v_fst_2639_, v_fst_2646_);
v___y_2652_ = v___x_2661_;
goto v___jp_2651_;
}
else
{
lean_dec(v_fst_2646_);
lean_dec(v_fst_2639_);
v___y_2652_ = v_x_2478_;
goto v___jp_2651_;
}
}
}
}
}
else
{
lean_dec(v_fst_2639_);
lean_dec_ref_known(v_x_2478_, 2);
return v___x_2641_;
}
}
else
{
lean_dec_ref_known(v_x_2478_, 2);
lean_dec_ref(v_f_2477_);
return v___x_2637_;
}
}
case 11:
{
lean_object* v_typeName_2670_; lean_object* v_idx_2671_; lean_object* v_struct_2672_; lean_object* v___x_2673_; 
v_typeName_2670_ = lean_ctor_get(v_x_2478_, 0);
v_idx_2671_ = lean_ctor_get(v_x_2478_, 1);
v_struct_2672_ = lean_ctor_get(v_x_2478_, 2);
lean_inc_ref(v_struct_2672_);
v___x_2673_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2477_, v_struct_2672_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_);
if (lean_obj_tag(v___x_2673_) == 0)
{
lean_object* v_a_2674_; lean_object* v___x_2676_; uint8_t v_isShared_2677_; uint8_t v_isSharedCheck_2696_; 
v_a_2674_ = lean_ctor_get(v___x_2673_, 0);
v_isSharedCheck_2696_ = !lean_is_exclusive(v___x_2673_);
if (v_isSharedCheck_2696_ == 0)
{
v___x_2676_ = v___x_2673_;
v_isShared_2677_ = v_isSharedCheck_2696_;
goto v_resetjp_2675_;
}
else
{
lean_inc(v_a_2674_);
lean_dec(v___x_2673_);
v___x_2676_ = lean_box(0);
v_isShared_2677_ = v_isSharedCheck_2696_;
goto v_resetjp_2675_;
}
v_resetjp_2675_:
{
lean_object* v_fst_2678_; lean_object* v_snd_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2695_; 
v_fst_2678_ = lean_ctor_get(v_a_2674_, 0);
v_snd_2679_ = lean_ctor_get(v_a_2674_, 1);
v_isSharedCheck_2695_ = !lean_is_exclusive(v_a_2674_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2681_ = v_a_2674_;
v_isShared_2682_ = v_isSharedCheck_2695_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_snd_2679_);
lean_inc(v_fst_2678_);
lean_dec(v_a_2674_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2695_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___y_2684_; size_t v___x_2691_; size_t v___x_2692_; uint8_t v___x_2693_; 
v___x_2691_ = lean_ptr_addr(v_struct_2672_);
v___x_2692_ = lean_ptr_addr(v_fst_2678_);
v___x_2693_ = lean_usize_dec_eq(v___x_2691_, v___x_2692_);
if (v___x_2693_ == 0)
{
lean_object* v___x_2694_; 
lean_inc(v_idx_2671_);
lean_inc(v_typeName_2670_);
lean_dec_ref_known(v_x_2478_, 3);
v___x_2694_ = l_Lean_Expr_proj___override(v_typeName_2670_, v_idx_2671_, v_fst_2678_);
v___y_2684_ = v___x_2694_;
goto v___jp_2683_;
}
else
{
lean_dec(v_fst_2678_);
v___y_2684_ = v_x_2478_;
goto v___jp_2683_;
}
v___jp_2683_:
{
lean_object* v___x_2686_; 
if (v_isShared_2682_ == 0)
{
lean_ctor_set(v___x_2681_, 0, v___y_2684_);
v___x_2686_ = v___x_2681_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v___y_2684_);
lean_ctor_set(v_reuseFailAlloc_2690_, 1, v_snd_2679_);
v___x_2686_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
lean_object* v___x_2688_; 
if (v_isShared_2677_ == 0)
{
lean_ctor_set(v___x_2676_, 0, v___x_2686_);
v___x_2688_ = v___x_2676_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v___x_2686_);
v___x_2688_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
return v___x_2688_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_x_2478_, 3);
return v___x_2673_;
}
}
default: 
{
lean_object* v___x_2697_; lean_object* v___x_2698_; 
lean_dec_ref(v_f_2477_);
v___x_2697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2697_, 0, v_x_2478_);
lean_ctor_set(v___x_2697_, 1, v___y_2479_);
v___x_2698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2698_, 0, v___x_2697_);
return v___x_2698_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___boxed(lean_object* v_f_2699_, lean_object* v_x_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_){
_start:
{
lean_object* v_res_2707_; 
v_res_2707_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg(v_f_2699_, v_x_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_);
lean_dec(v___y_2705_);
lean_dec_ref(v___y_2704_);
lean_dec(v___y_2703_);
lean_dec_ref(v___y_2702_);
return v_res_2707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg(lean_object* v_f_2708_, lean_object* v_init_2709_, lean_object* v_e_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_){
_start:
{
lean_object* v___x_2716_; 
v___x_2716_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg(v_f_2708_, v_e_2710_, v_init_2709_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_);
if (lean_obj_tag(v___x_2716_) == 0)
{
lean_object* v_a_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2725_; 
v_a_2717_ = lean_ctor_get(v___x_2716_, 0);
v_isSharedCheck_2725_ = !lean_is_exclusive(v___x_2716_);
if (v_isSharedCheck_2725_ == 0)
{
v___x_2719_ = v___x_2716_;
v_isShared_2720_ = v_isSharedCheck_2725_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_a_2717_);
lean_dec(v___x_2716_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2725_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
lean_object* v_snd_2721_; lean_object* v___x_2723_; 
v_snd_2721_ = lean_ctor_get(v_a_2717_, 1);
lean_inc(v_snd_2721_);
lean_dec(v_a_2717_);
if (v_isShared_2720_ == 0)
{
lean_ctor_set(v___x_2719_, 0, v_snd_2721_);
v___x_2723_ = v___x_2719_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v_snd_2721_);
v___x_2723_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
return v___x_2723_;
}
}
}
else
{
lean_object* v_a_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2733_; 
v_a_2726_ = lean_ctor_get(v___x_2716_, 0);
v_isSharedCheck_2733_ = !lean_is_exclusive(v___x_2716_);
if (v_isSharedCheck_2733_ == 0)
{
v___x_2728_ = v___x_2716_;
v_isShared_2729_ = v_isSharedCheck_2733_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_a_2726_);
lean_dec(v___x_2716_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2733_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
lean_object* v___x_2731_; 
if (v_isShared_2729_ == 0)
{
v___x_2731_ = v___x_2728_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v_a_2726_);
v___x_2731_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
return v___x_2731_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg___boxed(lean_object* v_f_2734_, lean_object* v_init_2735_, lean_object* v_e_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_){
_start:
{
lean_object* v_res_2742_; 
v_res_2742_ = l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg(v_f_2734_, v_init_2735_, v_e_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_);
lean_dec(v___y_2740_);
lean_dec_ref(v___y_2739_);
lean_dec(v___y_2738_);
lean_dec_ref(v___y_2737_);
return v_res_2742_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(lean_object* v_op_2745_, lean_object* v_as_2746_, size_t v_i_2747_, size_t v_stop_2748_, lean_object* v_b_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_){
_start:
{
lean_object* v_a_2756_; uint8_t v___x_2760_; 
v___x_2760_ = lean_usize_dec_eq(v_i_2747_, v_stop_2748_);
if (v___x_2760_ == 0)
{
lean_object* v___x_2761_; lean_object* v___x_2762_; 
v___x_2761_ = lean_array_uget_borrowed(v_as_2746_, v_i_2747_);
lean_inc(v___y_2753_);
lean_inc_ref(v___y_2752_);
lean_inc(v___y_2751_);
lean_inc_ref(v___y_2750_);
lean_inc(v___x_2761_);
v___x_2762_ = lean_infer_type(v___x_2761_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_);
if (lean_obj_tag(v___x_2762_) == 0)
{
lean_object* v_a_2763_; lean_object* v___x_2764_; 
v_a_2763_ = lean_ctor_get(v___x_2762_, 0);
lean_inc(v_a_2763_);
lean_dec_ref_known(v___x_2762_, 1);
lean_inc_ref(v_op_2745_);
v___x_2764_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v_op_2745_, v_a_2763_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_);
if (lean_obj_tag(v___x_2764_) == 0)
{
lean_object* v_a_2765_; lean_object* v___x_2766_; 
v_a_2765_ = lean_ctor_get(v___x_2764_, 0);
lean_inc(v_a_2765_);
lean_dec_ref_known(v___x_2764_, 1);
v___x_2766_ = l_Array_append___redArg(v_b_2749_, v_a_2765_);
lean_dec(v_a_2765_);
v_a_2756_ = v___x_2766_;
goto v___jp_2755_;
}
else
{
lean_dec_ref(v_b_2749_);
if (lean_obj_tag(v___x_2764_) == 0)
{
lean_object* v_a_2767_; 
v_a_2767_ = lean_ctor_get(v___x_2764_, 0);
lean_inc(v_a_2767_);
lean_dec_ref_known(v___x_2764_, 1);
v_a_2756_ = v_a_2767_;
goto v___jp_2755_;
}
else
{
lean_dec_ref(v_op_2745_);
return v___x_2764_;
}
}
}
else
{
lean_object* v_a_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2775_; 
lean_dec_ref(v_b_2749_);
lean_dec_ref(v_op_2745_);
v_a_2768_ = lean_ctor_get(v___x_2762_, 0);
v_isSharedCheck_2775_ = !lean_is_exclusive(v___x_2762_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2770_ = v___x_2762_;
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_a_2768_);
lean_dec(v___x_2762_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___x_2773_; 
if (v_isShared_2771_ == 0)
{
v___x_2773_ = v___x_2770_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_a_2768_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
return v___x_2773_;
}
}
}
}
else
{
lean_object* v___x_2776_; 
lean_dec_ref(v_op_2745_);
v___x_2776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2776_, 0, v_b_2749_);
return v___x_2776_;
}
v___jp_2755_:
{
size_t v___x_2757_; size_t v___x_2758_; 
v___x_2757_ = ((size_t)1ULL);
v___x_2758_ = lean_usize_add(v_i_2747_, v___x_2757_);
v_i_2747_ = v___x_2758_;
v_b_2749_ = v_a_2756_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0(lean_object* v_op_2777_, lean_object* v_args_2778_, lean_object* v_body_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_){
_start:
{
lean_object* v___x_2785_; 
lean_inc_ref(v_op_2777_);
v___x_2785_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v_op_2777_, v_body_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_);
if (lean_obj_tag(v___x_2785_) == 0)
{
lean_object* v_a_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2807_; 
v_a_2786_ = lean_ctor_get(v___x_2785_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2785_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2788_ = v___x_2785_;
v_isShared_2789_ = v_isSharedCheck_2807_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_a_2786_);
lean_dec(v___x_2785_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2807_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; uint8_t v___x_2793_; 
v___x_2790_ = l_Array_reverse___redArg(v_a_2786_);
v___x_2791_ = lean_unsigned_to_nat(0u);
v___x_2792_ = lean_array_get_size(v_args_2778_);
v___x_2793_ = lean_nat_dec_lt(v___x_2791_, v___x_2792_);
if (v___x_2793_ == 0)
{
lean_object* v___x_2795_; 
lean_dec_ref(v_op_2777_);
if (v_isShared_2789_ == 0)
{
lean_ctor_set(v___x_2788_, 0, v___x_2790_);
v___x_2795_ = v___x_2788_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v___x_2790_);
v___x_2795_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
return v___x_2795_;
}
}
else
{
uint8_t v___x_2797_; 
v___x_2797_ = lean_nat_dec_le(v___x_2792_, v___x_2792_);
if (v___x_2797_ == 0)
{
if (v___x_2793_ == 0)
{
lean_object* v___x_2799_; 
lean_dec_ref(v_op_2777_);
if (v_isShared_2789_ == 0)
{
lean_ctor_set(v___x_2788_, 0, v___x_2790_);
v___x_2799_ = v___x_2788_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v___x_2790_);
v___x_2799_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
return v___x_2799_;
}
}
else
{
size_t v___x_2801_; size_t v___x_2802_; lean_object* v___x_2803_; 
lean_del_object(v___x_2788_);
v___x_2801_ = ((size_t)0ULL);
v___x_2802_ = lean_usize_of_nat(v___x_2792_);
v___x_2803_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(v_op_2777_, v_args_2778_, v___x_2801_, v___x_2802_, v___x_2790_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_);
return v___x_2803_;
}
}
else
{
size_t v___x_2804_; size_t v___x_2805_; lean_object* v___x_2806_; 
lean_del_object(v___x_2788_);
v___x_2804_ = ((size_t)0ULL);
v___x_2805_ = lean_usize_of_nat(v___x_2792_);
v___x_2806_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(v_op_2777_, v_args_2778_, v___x_2804_, v___x_2805_, v___x_2790_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_);
return v___x_2806_;
}
}
}
}
else
{
lean_dec_ref(v_op_2777_);
return v___x_2785_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed(lean_object* v_op_2808_, lean_object* v_args_2809_, lean_object* v_body_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_){
_start:
{
lean_object* v_res_2816_; 
v_res_2816_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0(v_op_2808_, v_args_2809_, v_body_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_);
lean_dec(v___y_2814_);
lean_dec_ref(v___y_2813_);
lean_dec(v___y_2812_);
lean_dec_ref(v___y_2811_);
lean_dec_ref(v_args_2809_);
return v_res_2816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3___boxed(lean_object* v_op_2817_, lean_object* v_a_2818_, lean_object* v_f_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_){
_start:
{
lean_object* v_res_2825_; 
v_res_2825_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3(v_op_2817_, v_a_2818_, v_f_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_);
lean_dec(v___y_2823_);
lean_dec_ref(v___y_2822_);
lean_dec(v___y_2821_);
lean_dec_ref(v___y_2820_);
return v_res_2825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(lean_object* v_op_2826_, lean_object* v_e_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_){
_start:
{
switch(lean_obj_tag(v_e_2827_))
{
case 0:
{
lean_object* v___x_2833_; lean_object* v___x_2834_; 
lean_dec_ref_known(v_e_2827_, 1);
lean_dec_ref(v_op_2826_);
v___x_2833_ = ((lean_object*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___closed__0));
v___x_2834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2834_, 0, v___x_2833_);
return v___x_2834_;
}
case 7:
{
lean_object* v___f_2835_; uint8_t v___x_2836_; lean_object* v___x_2837_; 
v___f_2835_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2835_, 0, v_op_2826_);
v___x_2836_ = 0;
v___x_2837_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(v_e_2827_, v___f_2835_, v___x_2836_, v_a_2828_, v_a_2829_, v_a_2830_, v_a_2831_);
return v___x_2837_;
}
case 6:
{
lean_object* v___f_2838_; uint8_t v___x_2839_; uint8_t v___x_2840_; lean_object* v___x_2841_; 
v___f_2838_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2838_, 0, v_op_2826_);
v___x_2839_ = 0;
v___x_2840_ = 1;
v___x_2841_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(v_e_2827_, v___f_2838_, v___x_2839_, v___x_2840_, v_a_2828_, v_a_2829_, v_a_2830_, v_a_2831_);
return v___x_2841_;
}
case 8:
{
lean_object* v___f_2842_; uint8_t v___x_2843_; uint8_t v___x_2844_; lean_object* v___x_2845_; 
v___f_2842_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2842_, 0, v_op_2826_);
v___x_2843_ = 0;
v___x_2844_ = 1;
v___x_2845_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(v_e_2827_, v___f_2842_, v___x_2843_, v___x_2844_, v_a_2828_, v_a_2829_, v_a_2830_, v_a_2831_);
return v___x_2845_;
}
default: 
{
lean_object* v___x_2846_; 
lean_inc_ref(v_op_2826_);
lean_inc(v_a_2831_);
lean_inc_ref(v_a_2830_);
lean_inc(v_a_2829_);
lean_inc_ref(v_a_2828_);
lean_inc_ref(v_e_2827_);
v___x_2846_ = lean_apply_6(v_op_2826_, v_e_2827_, v_a_2828_, v_a_2829_, v_a_2830_, v_a_2831_, lean_box(0));
if (lean_obj_tag(v___x_2846_) == 0)
{
lean_object* v_a_2847_; lean_object* v___f_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; 
v_a_2847_ = lean_ctor_get(v___x_2846_, 0);
lean_inc(v_a_2847_);
lean_dec_ref_known(v___x_2846_, 1);
v___f_2848_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3___boxed), 8, 1);
lean_closure_set(v___f_2848_, 0, v_op_2826_);
v___x_2849_ = l_Array_reverse___redArg(v_a_2847_);
v___x_2850_ = l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg(v___f_2848_, v___x_2849_, v_e_2827_, v_a_2828_, v_a_2829_, v_a_2830_, v_a_2831_);
return v___x_2850_;
}
else
{
lean_dec_ref(v_e_2827_);
lean_dec_ref(v_op_2826_);
return v___x_2846_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3(lean_object* v_op_2851_, lean_object* v_a_2852_, lean_object* v_f_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_){
_start:
{
lean_object* v___x_2859_; 
v___x_2859_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v_op_2851_, v_f_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_);
if (lean_obj_tag(v___x_2859_) == 0)
{
lean_object* v_a_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_2868_; 
v_a_2860_ = lean_ctor_get(v___x_2859_, 0);
v_isSharedCheck_2868_ = !lean_is_exclusive(v___x_2859_);
if (v_isSharedCheck_2868_ == 0)
{
v___x_2862_ = v___x_2859_;
v_isShared_2863_ = v_isSharedCheck_2868_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_a_2860_);
lean_dec(v___x_2859_);
v___x_2862_ = lean_box(0);
v_isShared_2863_ = v_isSharedCheck_2868_;
goto v_resetjp_2861_;
}
v_resetjp_2861_:
{
lean_object* v___x_2864_; lean_object* v___x_2866_; 
v___x_2864_ = l_Array_append___redArg(v_a_2852_, v_a_2860_);
lean_dec(v_a_2860_);
if (v_isShared_2863_ == 0)
{
lean_ctor_set(v___x_2862_, 0, v___x_2864_);
v___x_2866_ = v___x_2862_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v___x_2864_);
v___x_2866_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
return v___x_2866_;
}
}
}
else
{
lean_dec_ref(v_a_2852_);
return v___x_2859_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg___boxed(lean_object* v_op_2869_, lean_object* v_as_2870_, lean_object* v_i_2871_, lean_object* v_stop_2872_, lean_object* v_b_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_){
_start:
{
size_t v_i_boxed_2879_; size_t v_stop_boxed_2880_; lean_object* v_res_2881_; 
v_i_boxed_2879_ = lean_unbox_usize(v_i_2871_);
lean_dec(v_i_2871_);
v_stop_boxed_2880_ = lean_unbox_usize(v_stop_2872_);
lean_dec(v_stop_2872_);
v_res_2881_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(v_op_2869_, v_as_2870_, v_i_boxed_2879_, v_stop_boxed_2880_, v_b_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_);
lean_dec(v___y_2877_);
lean_dec_ref(v___y_2876_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec_ref(v_as_2870_);
return v_res_2881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___boxed(lean_object* v_op_2882_, lean_object* v_e_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_){
_start:
{
lean_object* v_res_2889_; 
v_res_2889_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v_op_2882_, v_e_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_);
lean_dec(v_a_2887_);
lean_dec_ref(v_a_2886_);
lean_dec(v_a_2885_);
lean_dec_ref(v_a_2884_);
return v_res_2889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches(lean_object* v_00_u03b1_2890_, lean_object* v_op_2891_, lean_object* v_e_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_){
_start:
{
lean_object* v___x_2898_; 
v___x_2898_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v_op_2891_, v_e_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_);
return v___x_2898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___boxed(lean_object* v_00_u03b1_2899_, lean_object* v_op_2900_, lean_object* v_e_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_){
_start:
{
lean_object* v_res_2907_; 
v_res_2907_ = l_Lean_Meta_Rewrites_getSubexpressionMatches(v_00_u03b1_2899_, v_op_2900_, v_e_2901_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_);
lean_dec(v_a_2905_);
lean_dec_ref(v_a_2904_);
lean_dec(v_a_2903_);
lean_dec_ref(v_a_2902_);
return v_res_2907_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0(lean_object* v_00_u03b1_2908_, lean_object* v_op_2909_, lean_object* v_as_2910_, size_t v_i_2911_, size_t v_stop_2912_, lean_object* v_b_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_){
_start:
{
lean_object* v___x_2919_; 
v___x_2919_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(v_op_2909_, v_as_2910_, v_i_2911_, v_stop_2912_, v_b_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_);
return v___x_2919_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___boxed(lean_object* v_00_u03b1_2920_, lean_object* v_op_2921_, lean_object* v_as_2922_, lean_object* v_i_2923_, lean_object* v_stop_2924_, lean_object* v_b_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_){
_start:
{
size_t v_i_boxed_2931_; size_t v_stop_boxed_2932_; lean_object* v_res_2933_; 
v_i_boxed_2931_ = lean_unbox_usize(v_i_2923_);
lean_dec(v_i_2923_);
v_stop_boxed_2932_ = lean_unbox_usize(v_stop_2924_);
lean_dec(v_stop_2924_);
v_res_2933_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0(v_00_u03b1_2920_, v_op_2921_, v_as_2922_, v_i_boxed_2931_, v_stop_boxed_2932_, v_b_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v___y_2927_);
lean_dec_ref(v___y_2926_);
lean_dec_ref(v_as_2922_);
return v_res_2933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3(lean_object* v_00_u03b1_2934_, lean_object* v_f_2935_, lean_object* v_x_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_){
_start:
{
lean_object* v___x_2943_; 
v___x_2943_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg(v_f_2935_, v_x_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_);
return v___x_2943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___boxed(lean_object* v_00_u03b1_2944_, lean_object* v_f_2945_, lean_object* v_x_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_){
_start:
{
lean_object* v_res_2953_; 
v_res_2953_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3(v_00_u03b1_2944_, v_f_2945_, v_x_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_);
lean_dec(v___y_2951_);
lean_dec_ref(v___y_2950_);
lean_dec(v___y_2949_);
lean_dec_ref(v___y_2948_);
return v_res_2953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3(lean_object* v_00_u03b1_2954_, lean_object* v_f_2955_, lean_object* v_init_2956_, lean_object* v_e_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_){
_start:
{
lean_object* v___x_2963_; 
v___x_2963_ = l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg(v_f_2955_, v_init_2956_, v_e_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_);
return v___x_2963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___boxed(lean_object* v_00_u03b1_2964_, lean_object* v_f_2965_, lean_object* v_init_2966_, lean_object* v_e_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_){
_start:
{
lean_object* v_res_2973_; 
v_res_2973_ = l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3(v_00_u03b1_2964_, v_f_2965_, v_init_2966_, v_e_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_);
lean_dec(v___y_2971_);
lean_dec_ref(v___y_2970_);
lean_dec(v___y_2969_);
lean_dec_ref(v___y_2968_);
return v_res_2973_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__3(size_t v_sz_2974_, size_t v_i_2975_, lean_object* v_bs_2976_){
_start:
{
uint8_t v___x_2977_; 
v___x_2977_ = lean_usize_dec_lt(v_i_2975_, v_sz_2974_);
if (v___x_2977_ == 0)
{
return v_bs_2976_;
}
else
{
lean_object* v_v_2978_; lean_object* v_fst_2979_; lean_object* v_snd_2980_; lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_2994_; 
v_v_2978_ = lean_array_uget(v_bs_2976_, v_i_2975_);
v_fst_2979_ = lean_ctor_get(v_v_2978_, 0);
v_snd_2980_ = lean_ctor_get(v_v_2978_, 1);
v_isSharedCheck_2994_ = !lean_is_exclusive(v_v_2978_);
if (v_isSharedCheck_2994_ == 0)
{
v___x_2982_ = v_v_2978_;
v_isShared_2983_ = v_isSharedCheck_2994_;
goto v_resetjp_2981_;
}
else
{
lean_inc(v_snd_2980_);
lean_inc(v_fst_2979_);
lean_dec(v_v_2978_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_2994_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
lean_object* v___x_2984_; lean_object* v_bs_x27_2985_; lean_object* v___x_2986_; lean_object* v___x_2988_; 
v___x_2984_ = lean_unsigned_to_nat(0u);
v_bs_x27_2985_ = lean_array_uset(v_bs_2976_, v_i_2975_, v___x_2984_);
v___x_2986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2986_, 0, v_fst_2979_);
if (v_isShared_2983_ == 0)
{
lean_ctor_set(v___x_2982_, 0, v___x_2986_);
v___x_2988_ = v___x_2982_;
goto v_reusejp_2987_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2993_, 0, v___x_2986_);
lean_ctor_set(v_reuseFailAlloc_2993_, 1, v_snd_2980_);
v___x_2988_ = v_reuseFailAlloc_2993_;
goto v_reusejp_2987_;
}
v_reusejp_2987_:
{
size_t v___x_2989_; size_t v___x_2990_; lean_object* v___x_2991_; 
v___x_2989_ = ((size_t)1ULL);
v___x_2990_ = lean_usize_add(v_i_2975_, v___x_2989_);
v___x_2991_ = lean_array_uset(v_bs_x27_2985_, v_i_2975_, v___x_2988_);
v_i_2975_ = v___x_2990_;
v_bs_2976_ = v___x_2991_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__3___boxed(lean_object* v_sz_2995_, lean_object* v_i_2996_, lean_object* v_bs_2997_){
_start:
{
size_t v_sz_boxed_2998_; size_t v_i_boxed_2999_; lean_object* v_res_3000_; 
v_sz_boxed_2998_ = lean_unbox_usize(v_sz_2995_);
lean_dec(v_sz_2995_);
v_i_boxed_2999_ = lean_unbox_usize(v_i_2996_);
lean_dec(v_i_2996_);
v_res_3000_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__3(v_sz_boxed_2998_, v_i_boxed_2999_, v_bs_2997_);
return v_res_3000_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0___redArg(lean_object* v_xs_3001_, lean_object* v_j_3002_){
_start:
{
lean_object* v_zero_3003_; uint8_t v_isZero_3004_; 
v_zero_3003_ = lean_unsigned_to_nat(0u);
v_isZero_3004_ = lean_nat_dec_eq(v_j_3002_, v_zero_3003_);
if (v_isZero_3004_ == 1)
{
lean_dec(v_j_3002_);
return v_xs_3001_;
}
else
{
lean_object* v___x_3005_; lean_object* v_snd_3006_; lean_object* v_snd_3007_; lean_object* v_one_3008_; lean_object* v_n_3009_; lean_object* v___x_3010_; lean_object* v_snd_3011_; lean_object* v_snd_3012_; uint8_t v___x_3013_; 
v___x_3005_ = lean_array_fget_borrowed(v_xs_3001_, v_j_3002_);
v_snd_3006_ = lean_ctor_get(v___x_3005_, 1);
v_snd_3007_ = lean_ctor_get(v_snd_3006_, 1);
v_one_3008_ = lean_unsigned_to_nat(1u);
v_n_3009_ = lean_nat_sub(v_j_3002_, v_one_3008_);
v___x_3010_ = lean_array_fget_borrowed(v_xs_3001_, v_n_3009_);
v_snd_3011_ = lean_ctor_get(v___x_3010_, 1);
v_snd_3012_ = lean_ctor_get(v_snd_3011_, 1);
v___x_3013_ = lean_nat_dec_lt(v_snd_3012_, v_snd_3007_);
if (v___x_3013_ == 0)
{
lean_dec(v_n_3009_);
lean_dec(v_j_3002_);
return v_xs_3001_;
}
else
{
lean_object* v___x_3014_; 
v___x_3014_ = lean_array_fswap(v_xs_3001_, v_j_3002_, v_n_3009_);
lean_dec(v_j_3002_);
v_xs_3001_ = v___x_3014_;
v_j_3002_ = v_n_3009_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0(lean_object* v_xs_3016_, lean_object* v_i_3017_, lean_object* v_fuel_3018_){
_start:
{
lean_object* v_zero_3019_; uint8_t v_isZero_3020_; 
v_zero_3019_ = lean_unsigned_to_nat(0u);
v_isZero_3020_ = lean_nat_dec_eq(v_fuel_3018_, v_zero_3019_);
if (v_isZero_3020_ == 1)
{
lean_dec(v_fuel_3018_);
lean_dec(v_i_3017_);
return v_xs_3016_;
}
else
{
lean_object* v___x_3021_; uint8_t v___x_3022_; 
v___x_3021_ = lean_array_get_size(v_xs_3016_);
v___x_3022_ = lean_nat_dec_lt(v_i_3017_, v___x_3021_);
if (v___x_3022_ == 0)
{
lean_dec(v_fuel_3018_);
lean_dec(v_i_3017_);
return v_xs_3016_;
}
else
{
lean_object* v_one_3023_; lean_object* v_n_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; 
v_one_3023_ = lean_unsigned_to_nat(1u);
v_n_3024_ = lean_nat_sub(v_fuel_3018_, v_one_3023_);
lean_dec(v_fuel_3018_);
lean_inc(v_i_3017_);
v___x_3025_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0___redArg(v_xs_3016_, v_i_3017_);
v___x_3026_ = lean_nat_add(v_i_3017_, v_one_3023_);
lean_dec(v_i_3017_);
v_xs_3016_ = v___x_3025_;
v_i_3017_ = v___x_3026_;
v_fuel_3018_ = v_n_3024_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__2(size_t v_sz_3028_, size_t v_i_3029_, lean_object* v_bs_3030_){
_start:
{
uint8_t v___x_3031_; 
v___x_3031_ = lean_usize_dec_lt(v_i_3029_, v_sz_3028_);
if (v___x_3031_ == 0)
{
return v_bs_3030_;
}
else
{
lean_object* v_v_3032_; lean_object* v_fst_3033_; lean_object* v_snd_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3048_; 
v_v_3032_ = lean_array_uget(v_bs_3030_, v_i_3029_);
v_fst_3033_ = lean_ctor_get(v_v_3032_, 0);
v_snd_3034_ = lean_ctor_get(v_v_3032_, 1);
v_isSharedCheck_3048_ = !lean_is_exclusive(v_v_3032_);
if (v_isSharedCheck_3048_ == 0)
{
v___x_3036_ = v_v_3032_;
v_isShared_3037_ = v_isSharedCheck_3048_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_snd_3034_);
lean_inc(v_fst_3033_);
lean_dec(v_v_3032_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3048_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v___x_3038_; lean_object* v_bs_x27_3039_; lean_object* v___x_3040_; lean_object* v___x_3042_; 
v___x_3038_ = lean_unsigned_to_nat(0u);
v_bs_x27_3039_ = lean_array_uset(v_bs_3030_, v_i_3029_, v___x_3038_);
v___x_3040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3040_, 0, v_fst_3033_);
if (v_isShared_3037_ == 0)
{
lean_ctor_set(v___x_3036_, 0, v___x_3040_);
v___x_3042_ = v___x_3036_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v___x_3040_);
lean_ctor_set(v_reuseFailAlloc_3047_, 1, v_snd_3034_);
v___x_3042_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
size_t v___x_3043_; size_t v___x_3044_; lean_object* v___x_3045_; 
v___x_3043_ = ((size_t)1ULL);
v___x_3044_ = lean_usize_add(v_i_3029_, v___x_3043_);
v___x_3045_ = lean_array_uset(v_bs_x27_3039_, v_i_3029_, v___x_3042_);
v_i_3029_ = v___x_3044_;
v_bs_3030_ = v___x_3045_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__2___boxed(lean_object* v_sz_3049_, lean_object* v_i_3050_, lean_object* v_bs_3051_){
_start:
{
size_t v_sz_boxed_3052_; size_t v_i_boxed_3053_; lean_object* v_res_3054_; 
v_sz_boxed_3052_ = lean_unbox_usize(v_sz_3049_);
lean_dec(v_sz_3049_);
v_i_boxed_3053_ = lean_unbox_usize(v_i_3050_);
lean_dec(v_i_3050_);
v_res_3054_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__2(v_sz_boxed_3052_, v_i_boxed_3053_, v_bs_3051_);
return v_res_3054_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg(lean_object* v_forbidden_3055_, lean_object* v_as_3056_, size_t v_sz_3057_, size_t v_i_3058_, lean_object* v_b_3059_){
_start:
{
lean_object* v_a_3062_; uint8_t v___x_3066_; 
v___x_3066_ = lean_usize_dec_lt(v_i_3058_, v_sz_3057_);
if (v___x_3066_ == 0)
{
lean_object* v___x_3067_; 
v___x_3067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3067_, 0, v_b_3059_);
return v___x_3067_;
}
else
{
lean_object* v_a_3068_; lean_object* v_snd_3069_; lean_object* v_snd_3070_; lean_object* v_fst_3071_; lean_object* v_fst_3072_; lean_object* v___x_3074_; uint8_t v_isShared_3075_; uint8_t v_isSharedCheck_3122_; 
v_a_3068_ = lean_array_uget(v_as_3056_, v_i_3058_);
v_snd_3069_ = lean_ctor_get(v_a_3068_, 1);
lean_inc(v_snd_3069_);
v_snd_3070_ = lean_ctor_get(v_b_3059_, 1);
lean_inc(v_snd_3070_);
v_fst_3071_ = lean_ctor_get(v_a_3068_, 0);
v_fst_3072_ = lean_ctor_get(v_snd_3069_, 0);
v_isSharedCheck_3122_ = !lean_is_exclusive(v_snd_3069_);
if (v_isSharedCheck_3122_ == 0)
{
lean_object* v_unused_3123_; 
v_unused_3123_ = lean_ctor_get(v_snd_3069_, 1);
lean_dec(v_unused_3123_);
v___x_3074_ = v_snd_3069_;
v_isShared_3075_ = v_isSharedCheck_3122_;
goto v_resetjp_3073_;
}
else
{
lean_inc(v_fst_3072_);
lean_dec(v_snd_3069_);
v___x_3074_ = lean_box(0);
v_isShared_3075_ = v_isSharedCheck_3122_;
goto v_resetjp_3073_;
}
v_resetjp_3073_:
{
lean_object* v_fst_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3120_; 
v_fst_3076_ = lean_ctor_get(v_b_3059_, 0);
v_isSharedCheck_3120_ = !lean_is_exclusive(v_b_3059_);
if (v_isSharedCheck_3120_ == 0)
{
lean_object* v_unused_3121_; 
v_unused_3121_ = lean_ctor_get(v_b_3059_, 1);
lean_dec(v_unused_3121_);
v___x_3078_ = v_b_3059_;
v_isShared_3079_ = v_isSharedCheck_3120_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_fst_3076_);
lean_dec(v_b_3059_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3120_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v_fst_3080_; lean_object* v_snd_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3119_; 
v_fst_3080_ = lean_ctor_get(v_snd_3070_, 0);
v_snd_3081_ = lean_ctor_get(v_snd_3070_, 1);
v_isSharedCheck_3119_ = !lean_is_exclusive(v_snd_3070_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3083_ = v_snd_3070_;
v_isShared_3084_ = v_isSharedCheck_3119_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_snd_3081_);
lean_inc(v_fst_3080_);
lean_dec(v_snd_3070_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3119_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
uint8_t v___x_3097_; 
v___x_3097_ = l_Lean_NameSet_contains(v_forbidden_3055_, v_fst_3071_);
if (v___x_3097_ == 0)
{
uint8_t v___x_3098_; 
lean_inc(v_fst_3071_);
v___x_3098_ = lean_unbox(v_fst_3072_);
lean_dec(v_fst_3072_);
if (v___x_3098_ == 0)
{
uint8_t v___x_3099_; 
lean_del_object(v___x_3083_);
lean_del_object(v___x_3078_);
v___x_3099_ = l_Lean_NameSet_contains(v_fst_3076_, v_fst_3071_);
if (v___x_3099_ == 0)
{
if (v___x_3066_ == 0)
{
lean_dec(v_fst_3071_);
lean_dec(v_a_3068_);
goto v___jp_3092_;
}
else
{
lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; 
lean_del_object(v___x_3074_);
v___x_3100_ = lean_array_push(v_snd_3081_, v_a_3068_);
v___x_3101_ = l_Lean_NameSet_insert(v_fst_3076_, v_fst_3071_);
v___x_3102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3102_, 0, v_fst_3080_);
lean_ctor_set(v___x_3102_, 1, v___x_3100_);
v___x_3103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3103_, 0, v___x_3101_);
lean_ctor_set(v___x_3103_, 1, v___x_3102_);
v_a_3062_ = v___x_3103_;
goto v___jp_3061_;
}
}
else
{
lean_dec(v_fst_3071_);
lean_dec(v_a_3068_);
goto v___jp_3092_;
}
}
else
{
uint8_t v___x_3104_; 
lean_del_object(v___x_3074_);
v___x_3104_ = l_Lean_NameSet_contains(v_fst_3080_, v_fst_3071_);
if (v___x_3104_ == 0)
{
if (v___x_3066_ == 0)
{
lean_dec(v_fst_3071_);
lean_dec(v_a_3068_);
goto v___jp_3085_;
}
else
{
lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; 
lean_del_object(v___x_3083_);
lean_del_object(v___x_3078_);
v___x_3105_ = lean_array_push(v_snd_3081_, v_a_3068_);
v___x_3106_ = l_Lean_NameSet_insert(v_fst_3080_, v_fst_3071_);
v___x_3107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3107_, 0, v___x_3106_);
lean_ctor_set(v___x_3107_, 1, v___x_3105_);
v___x_3108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3108_, 0, v_fst_3076_);
lean_ctor_set(v___x_3108_, 1, v___x_3107_);
v_a_3062_ = v___x_3108_;
goto v___jp_3061_;
}
}
else
{
lean_dec(v_fst_3071_);
lean_dec(v_a_3068_);
goto v___jp_3085_;
}
}
}
else
{
lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3116_; 
lean_del_object(v___x_3083_);
lean_del_object(v___x_3078_);
lean_del_object(v___x_3074_);
lean_dec(v_fst_3072_);
v_isSharedCheck_3116_ = !lean_is_exclusive(v_a_3068_);
if (v_isSharedCheck_3116_ == 0)
{
lean_object* v_unused_3117_; lean_object* v_unused_3118_; 
v_unused_3117_ = lean_ctor_get(v_a_3068_, 1);
lean_dec(v_unused_3117_);
v_unused_3118_ = lean_ctor_get(v_a_3068_, 0);
lean_dec(v_unused_3118_);
v___x_3110_ = v_a_3068_;
v_isShared_3111_ = v_isSharedCheck_3116_;
goto v_resetjp_3109_;
}
else
{
lean_dec(v_a_3068_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3116_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
lean_object* v___x_3113_; 
if (v_isShared_3111_ == 0)
{
lean_ctor_set(v___x_3110_, 1, v_snd_3081_);
lean_ctor_set(v___x_3110_, 0, v_fst_3080_);
v___x_3113_ = v___x_3110_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v_fst_3080_);
lean_ctor_set(v_reuseFailAlloc_3115_, 1, v_snd_3081_);
v___x_3113_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
lean_object* v___x_3114_; 
v___x_3114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3114_, 0, v_fst_3076_);
lean_ctor_set(v___x_3114_, 1, v___x_3113_);
v_a_3062_ = v___x_3114_;
goto v___jp_3061_;
}
}
}
v___jp_3085_:
{
lean_object* v___x_3087_; 
if (v_isShared_3084_ == 0)
{
v___x_3087_ = v___x_3083_;
goto v_reusejp_3086_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v_fst_3080_);
lean_ctor_set(v_reuseFailAlloc_3091_, 1, v_snd_3081_);
v___x_3087_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3086_;
}
v_reusejp_3086_:
{
lean_object* v___x_3089_; 
if (v_isShared_3079_ == 0)
{
lean_ctor_set(v___x_3078_, 1, v___x_3087_);
v___x_3089_ = v___x_3078_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_fst_3076_);
lean_ctor_set(v_reuseFailAlloc_3090_, 1, v___x_3087_);
v___x_3089_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
v_a_3062_ = v___x_3089_;
goto v___jp_3061_;
}
}
}
v___jp_3092_:
{
lean_object* v___x_3094_; 
if (v_isShared_3075_ == 0)
{
lean_ctor_set(v___x_3074_, 1, v_snd_3081_);
lean_ctor_set(v___x_3074_, 0, v_fst_3080_);
v___x_3094_ = v___x_3074_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3096_; 
v_reuseFailAlloc_3096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3096_, 0, v_fst_3080_);
lean_ctor_set(v_reuseFailAlloc_3096_, 1, v_snd_3081_);
v___x_3094_ = v_reuseFailAlloc_3096_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
lean_object* v___x_3095_; 
v___x_3095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3095_, 0, v_fst_3076_);
lean_ctor_set(v___x_3095_, 1, v___x_3094_);
v_a_3062_ = v___x_3095_;
goto v___jp_3061_;
}
}
}
}
}
}
v___jp_3061_:
{
size_t v___x_3063_; size_t v___x_3064_; 
v___x_3063_ = ((size_t)1ULL);
v___x_3064_ = lean_usize_add(v_i_3058_, v___x_3063_);
v_i_3058_ = v___x_3064_;
v_b_3059_ = v_a_3062_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg___boxed(lean_object* v_forbidden_3124_, lean_object* v_as_3125_, lean_object* v_sz_3126_, lean_object* v_i_3127_, lean_object* v_b_3128_, lean_object* v___y_3129_){
_start:
{
size_t v_sz_boxed_3130_; size_t v_i_boxed_3131_; lean_object* v_res_3132_; 
v_sz_boxed_3130_ = lean_unbox_usize(v_sz_3126_);
lean_dec(v_sz_3126_);
v_i_boxed_3131_ = lean_unbox_usize(v_i_3127_);
lean_dec(v_i_3127_);
v_res_3132_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg(v_forbidden_3124_, v_as_3125_, v_sz_boxed_3130_, v_i_boxed_3131_, v_b_3128_);
lean_dec_ref(v_as_3125_);
lean_dec(v_forbidden_3124_);
return v_res_3132_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__2(void){
_start:
{
lean_object* v___x_3136_; lean_object* v___x_3137_; 
v___x_3136_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__1));
v___x_3137_ = l_Lean_MessageData_ofFormat(v___x_3136_);
return v___x_3137_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__3(void){
_start:
{
lean_object* v___x_3138_; lean_object* v___x_3139_; 
v___x_3138_ = lean_box(1);
v___x_3139_ = l_Lean_MessageData_ofFormat(v___x_3138_);
return v___x_3139_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4(lean_object* v_a_3142_, lean_object* v_a_3143_){
_start:
{
if (lean_obj_tag(v_a_3142_) == 0)
{
lean_object* v___x_3144_; 
v___x_3144_ = l_List_reverse___redArg(v_a_3143_);
return v___x_3144_;
}
else
{
lean_object* v_head_3145_; lean_object* v_snd_3146_; lean_object* v_tail_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3192_; 
v_head_3145_ = lean_ctor_get(v_a_3142_, 0);
lean_inc(v_head_3145_);
v_snd_3146_ = lean_ctor_get(v_head_3145_, 1);
lean_inc(v_snd_3146_);
v_tail_3147_ = lean_ctor_get(v_a_3142_, 1);
v_isSharedCheck_3192_ = !lean_is_exclusive(v_a_3142_);
if (v_isSharedCheck_3192_ == 0)
{
lean_object* v_unused_3193_; 
v_unused_3193_ = lean_ctor_get(v_a_3142_, 0);
lean_dec(v_unused_3193_);
v___x_3149_ = v_a_3142_;
v_isShared_3150_ = v_isSharedCheck_3192_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_tail_3147_);
lean_dec(v_a_3142_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3192_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v_fst_3151_; lean_object* v___x_3153_; uint8_t v_isShared_3154_; uint8_t v_isSharedCheck_3190_; 
v_fst_3151_ = lean_ctor_get(v_head_3145_, 0);
v_isSharedCheck_3190_ = !lean_is_exclusive(v_head_3145_);
if (v_isSharedCheck_3190_ == 0)
{
lean_object* v_unused_3191_; 
v_unused_3191_ = lean_ctor_get(v_head_3145_, 1);
lean_dec(v_unused_3191_);
v___x_3153_ = v_head_3145_;
v_isShared_3154_ = v_isSharedCheck_3190_;
goto v_resetjp_3152_;
}
else
{
lean_inc(v_fst_3151_);
lean_dec(v_head_3145_);
v___x_3153_ = lean_box(0);
v_isShared_3154_ = v_isSharedCheck_3190_;
goto v_resetjp_3152_;
}
v_resetjp_3152_:
{
lean_object* v_fst_3155_; lean_object* v_snd_3156_; lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3189_; 
v_fst_3155_ = lean_ctor_get(v_snd_3146_, 0);
v_snd_3156_ = lean_ctor_get(v_snd_3146_, 1);
v_isSharedCheck_3189_ = !lean_is_exclusive(v_snd_3146_);
if (v_isSharedCheck_3189_ == 0)
{
v___x_3158_ = v_snd_3146_;
v_isShared_3159_ = v_isSharedCheck_3189_;
goto v_resetjp_3157_;
}
else
{
lean_inc(v_snd_3156_);
lean_inc(v_fst_3155_);
lean_dec(v_snd_3146_);
v___x_3158_ = lean_box(0);
v_isShared_3159_ = v_isSharedCheck_3189_;
goto v_resetjp_3157_;
}
v_resetjp_3157_:
{
lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3163_; 
v___x_3160_ = l_Lean_MessageData_ofName(v_fst_3151_);
v___x_3161_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__2, &l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__2_once, _init_l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__2);
if (v_isShared_3159_ == 0)
{
lean_ctor_set_tag(v___x_3158_, 7);
lean_ctor_set(v___x_3158_, 1, v___x_3161_);
lean_ctor_set(v___x_3158_, 0, v___x_3160_);
v___x_3163_ = v___x_3158_;
goto v_reusejp_3162_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v___x_3160_);
lean_ctor_set(v_reuseFailAlloc_3188_, 1, v___x_3161_);
v___x_3163_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3162_;
}
v_reusejp_3162_:
{
lean_object* v___x_3164_; lean_object* v___x_3166_; 
v___x_3164_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__3, &l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__3_once, _init_l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__3);
if (v_isShared_3154_ == 0)
{
lean_ctor_set_tag(v___x_3153_, 7);
lean_ctor_set(v___x_3153_, 1, v___x_3164_);
lean_ctor_set(v___x_3153_, 0, v___x_3163_);
v___x_3166_ = v___x_3153_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3187_; 
v_reuseFailAlloc_3187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3187_, 0, v___x_3163_);
lean_ctor_set(v_reuseFailAlloc_3187_, 1, v___x_3164_);
v___x_3166_ = v_reuseFailAlloc_3187_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
lean_object* v___y_3168_; uint8_t v___x_3184_; 
v___x_3184_ = lean_unbox(v_fst_3155_);
lean_dec(v_fst_3155_);
if (v___x_3184_ == 0)
{
lean_object* v___x_3185_; 
v___x_3185_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__4));
v___y_3168_ = v___x_3185_;
goto v___jp_3167_;
}
else
{
lean_object* v___x_3186_; 
v___x_3186_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__5));
v___y_3168_ = v___x_3186_;
goto v___jp_3167_;
}
v___jp_3167_:
{
lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3181_; 
lean_inc_ref(v___y_3168_);
v___x_3169_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3169_, 0, v___y_3168_);
v___x_3170_ = l_Lean_MessageData_ofFormat(v___x_3169_);
v___x_3171_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3171_, 0, v___x_3170_);
lean_ctor_set(v___x_3171_, 1, v___x_3161_);
v___x_3172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3172_, 0, v___x_3171_);
lean_ctor_set(v___x_3172_, 1, v___x_3164_);
v___x_3173_ = l_Nat_reprFast(v_snd_3156_);
v___x_3174_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3174_, 0, v___x_3173_);
v___x_3175_ = l_Lean_MessageData_ofFormat(v___x_3174_);
v___x_3176_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3176_, 0, v___x_3172_);
lean_ctor_set(v___x_3176_, 1, v___x_3175_);
v___x_3177_ = l_Lean_MessageData_paren(v___x_3176_);
v___x_3178_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3178_, 0, v___x_3166_);
lean_ctor_set(v___x_3178_, 1, v___x_3177_);
v___x_3179_ = l_Lean_MessageData_paren(v___x_3178_);
if (v_isShared_3150_ == 0)
{
lean_ctor_set(v___x_3149_, 1, v_a_3143_);
lean_ctor_set(v___x_3149_, 0, v___x_3179_);
v___x_3181_ = v___x_3149_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v___x_3179_);
lean_ctor_set(v_reuseFailAlloc_3183_, 1, v_a_3143_);
v___x_3181_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3180_;
}
v_reusejp_3180_:
{
v_a_3142_ = v_tail_3147_;
v_a_3143_ = v___x_3181_;
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
lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; 
v___x_3196_ = ((lean_object*)(l_Lean_Meta_Rewrites_rewriteCandidates___closed__0));
v___x_3197_ = l_Lean_NameSet_empty;
v___x_3198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3198_, 0, v___x_3197_);
lean_ctor_set(v___x_3198_, 1, v___x_3196_);
return v___x_3198_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__2(void){
_start:
{
lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; 
v___x_3199_ = lean_obj_once(&l_Lean_Meta_Rewrites_rewriteCandidates___closed__1, &l_Lean_Meta_Rewrites_rewriteCandidates___closed__1_once, _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__1);
v___x_3200_ = l_Lean_NameSet_empty;
v___x_3201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3201_, 0, v___x_3200_);
lean_ctor_set(v___x_3201_, 1, v___x_3199_);
return v___x_3201_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__3(void){
_start:
{
lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; 
v___x_3202_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_));
v___x_3203_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__4));
v___x_3204_ = l_Lean_Name_append(v___x_3203_, v___x_3202_);
return v___x_3204_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__5(void){
_start:
{
lean_object* v___x_3206_; lean_object* v___x_3207_; 
v___x_3206_ = ((lean_object*)(l_Lean_Meta_Rewrites_rewriteCandidates___closed__4));
v___x_3207_ = l_Lean_stringToMessageData(v___x_3206_);
return v___x_3207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rewriteCandidates(lean_object* v_hyps_3208_, lean_object* v_moduleRef_3209_, lean_object* v_target_3210_, lean_object* v_forbidden_3211_, lean_object* v_a_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_, lean_object* v_a_3215_){
_start:
{
lean_object* v___x_3217_; lean_object* v___x_3218_; 
v___x_3217_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_rwFindDecls___boxed), 7, 1);
lean_closure_set(v___x_3217_, 0, v_moduleRef_3209_);
v___x_3218_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v___x_3217_, v_target_3210_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_);
if (lean_obj_tag(v___x_3218_) == 0)
{
lean_object* v_a_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; size_t v_sz_3224_; size_t v___x_3225_; lean_object* v___x_3226_; 
v_a_3219_ = lean_ctor_get(v___x_3218_, 0);
lean_inc(v_a_3219_);
lean_dec_ref_known(v___x_3218_, 1);
v___x_3220_ = lean_unsigned_to_nat(0u);
v___x_3221_ = lean_array_get_size(v_a_3219_);
v___x_3222_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0(v_a_3219_, v___x_3220_, v___x_3221_);
v___x_3223_ = lean_obj_once(&l_Lean_Meta_Rewrites_rewriteCandidates___closed__2, &l_Lean_Meta_Rewrites_rewriteCandidates___closed__2_once, _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__2);
v_sz_3224_ = lean_array_size(v___x_3222_);
v___x_3225_ = ((size_t)0ULL);
v___x_3226_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg(v_forbidden_3211_, v___x_3222_, v_sz_3224_, v___x_3225_, v___x_3223_);
lean_dec_ref(v___x_3222_);
if (lean_obj_tag(v___x_3226_) == 0)
{
lean_object* v_a_3227_; lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3270_; 
v_a_3227_ = lean_ctor_get(v___x_3226_, 0);
v_isSharedCheck_3270_ = !lean_is_exclusive(v___x_3226_);
if (v_isSharedCheck_3270_ == 0)
{
v___x_3229_ = v___x_3226_;
v_isShared_3230_ = v_isSharedCheck_3270_;
goto v_resetjp_3228_;
}
else
{
lean_inc(v_a_3227_);
lean_dec(v___x_3226_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3270_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
lean_object* v_snd_3231_; lean_object* v_snd_3232_; lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3268_; 
v_snd_3231_ = lean_ctor_get(v_a_3227_, 1);
lean_inc(v_snd_3231_);
lean_dec(v_a_3227_);
v_snd_3232_ = lean_ctor_get(v_snd_3231_, 1);
v_isSharedCheck_3268_ = !lean_is_exclusive(v_snd_3231_);
if (v_isSharedCheck_3268_ == 0)
{
lean_object* v_unused_3269_; 
v_unused_3269_ = lean_ctor_get(v_snd_3231_, 0);
lean_dec(v_unused_3269_);
v___x_3234_ = v_snd_3231_;
v_isShared_3235_ = v_isSharedCheck_3268_;
goto v_resetjp_3233_;
}
else
{
lean_inc(v_snd_3232_);
lean_dec(v_snd_3231_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3268_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
lean_object* v_options_3245_; uint8_t v_hasTrace_3246_; 
v_options_3245_ = lean_ctor_get(v_a_3214_, 2);
v_hasTrace_3246_ = lean_ctor_get_uint8(v_options_3245_, sizeof(void*)*1);
if (v_hasTrace_3246_ == 0)
{
lean_del_object(v___x_3234_);
goto v___jp_3236_;
}
else
{
lean_object* v_inheritedTraceOptions_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; uint8_t v___x_3250_; 
v_inheritedTraceOptions_3247_ = lean_ctor_get(v_a_3214_, 13);
v___x_3248_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_));
v___x_3249_ = lean_obj_once(&l_Lean_Meta_Rewrites_rewriteCandidates___closed__3, &l_Lean_Meta_Rewrites_rewriteCandidates___closed__3_once, _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__3);
v___x_3250_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3247_, v_options_3245_, v___x_3249_);
if (v___x_3250_ == 0)
{
lean_del_object(v___x_3234_);
goto v___jp_3236_;
}
else
{
lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3257_; 
v___x_3251_ = lean_obj_once(&l_Lean_Meta_Rewrites_rewriteCandidates___closed__5, &l_Lean_Meta_Rewrites_rewriteCandidates___closed__5_once, _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__5);
lean_inc(v_snd_3232_);
v___x_3252_ = lean_array_to_list(v_snd_3232_);
v___x_3253_ = lean_box(0);
v___x_3254_ = l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4(v___x_3252_, v___x_3253_);
v___x_3255_ = l_Lean_MessageData_ofList(v___x_3254_);
if (v_isShared_3235_ == 0)
{
lean_ctor_set_tag(v___x_3234_, 7);
lean_ctor_set(v___x_3234_, 1, v___x_3255_);
lean_ctor_set(v___x_3234_, 0, v___x_3251_);
v___x_3257_ = v___x_3234_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3267_; 
v_reuseFailAlloc_3267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3267_, 0, v___x_3251_);
lean_ctor_set(v_reuseFailAlloc_3267_, 1, v___x_3255_);
v___x_3257_ = v_reuseFailAlloc_3267_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
lean_object* v___x_3258_; 
v___x_3258_ = l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2(v___x_3248_, v___x_3257_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_);
if (lean_obj_tag(v___x_3258_) == 0)
{
lean_dec_ref_known(v___x_3258_, 1);
goto v___jp_3236_;
}
else
{
lean_object* v_a_3259_; lean_object* v___x_3261_; uint8_t v_isShared_3262_; uint8_t v_isSharedCheck_3266_; 
lean_dec(v_snd_3232_);
lean_del_object(v___x_3229_);
lean_dec_ref(v_hyps_3208_);
v_a_3259_ = lean_ctor_get(v___x_3258_, 0);
v_isSharedCheck_3266_ = !lean_is_exclusive(v___x_3258_);
if (v_isSharedCheck_3266_ == 0)
{
v___x_3261_ = v___x_3258_;
v_isShared_3262_ = v_isSharedCheck_3266_;
goto v_resetjp_3260_;
}
else
{
lean_inc(v_a_3259_);
lean_dec(v___x_3258_);
v___x_3261_ = lean_box(0);
v_isShared_3262_ = v_isSharedCheck_3266_;
goto v_resetjp_3260_;
}
v_resetjp_3260_:
{
lean_object* v___x_3264_; 
if (v_isShared_3262_ == 0)
{
v___x_3264_ = v___x_3261_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3265_; 
v_reuseFailAlloc_3265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3265_, 0, v_a_3259_);
v___x_3264_ = v_reuseFailAlloc_3265_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
return v___x_3264_;
}
}
}
}
}
}
v___jp_3236_:
{
size_t v_sz_3237_; lean_object* v___x_3238_; size_t v_sz_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3243_; 
v_sz_3237_ = lean_array_size(v_hyps_3208_);
v___x_3238_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__2(v_sz_3237_, v___x_3225_, v_hyps_3208_);
v_sz_3239_ = lean_array_size(v_snd_3232_);
v___x_3240_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__3(v_sz_3239_, v___x_3225_, v_snd_3232_);
v___x_3241_ = l_Array_append___redArg(v___x_3238_, v___x_3240_);
lean_dec_ref(v___x_3240_);
if (v_isShared_3230_ == 0)
{
lean_ctor_set(v___x_3229_, 0, v___x_3241_);
v___x_3243_ = v___x_3229_;
goto v_reusejp_3242_;
}
else
{
lean_object* v_reuseFailAlloc_3244_; 
v_reuseFailAlloc_3244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3244_, 0, v___x_3241_);
v___x_3243_ = v_reuseFailAlloc_3244_;
goto v_reusejp_3242_;
}
v_reusejp_3242_:
{
return v___x_3243_;
}
}
}
}
}
else
{
lean_object* v_a_3271_; lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3278_; 
lean_dec_ref(v_hyps_3208_);
v_a_3271_ = lean_ctor_get(v___x_3226_, 0);
v_isSharedCheck_3278_ = !lean_is_exclusive(v___x_3226_);
if (v_isSharedCheck_3278_ == 0)
{
v___x_3273_ = v___x_3226_;
v_isShared_3274_ = v_isSharedCheck_3278_;
goto v_resetjp_3272_;
}
else
{
lean_inc(v_a_3271_);
lean_dec(v___x_3226_);
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
else
{
lean_object* v_a_3279_; lean_object* v___x_3281_; uint8_t v_isShared_3282_; uint8_t v_isSharedCheck_3286_; 
lean_dec_ref(v_hyps_3208_);
v_a_3279_ = lean_ctor_get(v___x_3218_, 0);
v_isSharedCheck_3286_ = !lean_is_exclusive(v___x_3218_);
if (v_isSharedCheck_3286_ == 0)
{
v___x_3281_ = v___x_3218_;
v_isShared_3282_ = v_isSharedCheck_3286_;
goto v_resetjp_3280_;
}
else
{
lean_inc(v_a_3279_);
lean_dec(v___x_3218_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rewriteCandidates___boxed(lean_object* v_hyps_3287_, lean_object* v_moduleRef_3288_, lean_object* v_target_3289_, lean_object* v_forbidden_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_){
_start:
{
lean_object* v_res_3296_; 
v_res_3296_ = l_Lean_Meta_Rewrites_rewriteCandidates(v_hyps_3287_, v_moduleRef_3288_, v_target_3289_, v_forbidden_3290_, v_a_3291_, v_a_3292_, v_a_3293_, v_a_3294_);
lean_dec(v_a_3294_);
lean_dec_ref(v_a_3293_);
lean_dec(v_a_3292_);
lean_dec_ref(v_a_3291_);
lean_dec(v_forbidden_3290_);
return v_res_3296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1(lean_object* v_forbidden_3297_, lean_object* v_as_3298_, size_t v_sz_3299_, size_t v_i_3300_, lean_object* v_b_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_){
_start:
{
lean_object* v___x_3307_; 
v___x_3307_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg(v_forbidden_3297_, v_as_3298_, v_sz_3299_, v_i_3300_, v_b_3301_);
return v___x_3307_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___boxed(lean_object* v_forbidden_3308_, lean_object* v_as_3309_, lean_object* v_sz_3310_, lean_object* v_i_3311_, lean_object* v_b_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_){
_start:
{
size_t v_sz_boxed_3318_; size_t v_i_boxed_3319_; lean_object* v_res_3320_; 
v_sz_boxed_3318_ = lean_unbox_usize(v_sz_3310_);
lean_dec(v_sz_3310_);
v_i_boxed_3319_ = lean_unbox_usize(v_i_3311_);
lean_dec(v_i_3311_);
v_res_3320_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1(v_forbidden_3308_, v_as_3309_, v_sz_boxed_3318_, v_i_boxed_3319_, v_b_3312_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_);
lean_dec(v___y_3316_);
lean_dec_ref(v___y_3315_);
lean_dec(v___y_3314_);
lean_dec_ref(v___y_3313_);
lean_dec_ref(v_as_3309_);
lean_dec(v_forbidden_3308_);
return v_res_3320_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0(lean_object* v_xs_3321_, lean_object* v_j_3322_, lean_object* v_h_3323_){
_start:
{
lean_object* v___x_3324_; 
v___x_3324_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0___redArg(v_xs_3321_, v_j_3322_);
return v___x_3324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_newGoal(lean_object* v_r_3325_){
_start:
{
uint8_t v_rfl_x3f_3326_; 
v_rfl_x3f_3326_ = lean_ctor_get_uint8(v_r_3325_, sizeof(void*)*4 + 1);
if (v_rfl_x3f_3326_ == 0)
{
lean_object* v_result_3327_; lean_object* v_eNew_3328_; lean_object* v___x_3329_; 
v_result_3327_ = lean_ctor_get(v_r_3325_, 2);
v_eNew_3328_ = lean_ctor_get(v_result_3327_, 0);
lean_inc_ref(v_eNew_3328_);
v___x_3329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3329_, 0, v_eNew_3328_);
return v___x_3329_;
}
else
{
lean_object* v___x_3330_; 
v___x_3330_ = lean_box(0);
return v___x_3330_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_newGoal___boxed(lean_object* v_r_3331_){
_start:
{
lean_object* v_res_3332_; 
v_res_3332_ = l_Lean_Meta_Rewrites_RewriteResult_newGoal(v_r_3331_);
lean_dec_ref(v_r_3331_);
return v_res_3332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0(lean_object* v_x_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_){
_start:
{
lean_object* v___x_3343_; 
lean_inc(v___y_3337_);
lean_inc_ref(v___y_3336_);
lean_inc(v___y_3335_);
lean_inc_ref(v___y_3334_);
v___x_3343_ = lean_apply_9(v_x_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_, lean_box(0));
return v___x_3343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0___boxed(lean_object* v_x_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_){
_start:
{
lean_object* v_res_3354_; 
v_res_3354_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0(v_x_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_);
lean_dec(v___y_3348_);
lean_dec_ref(v___y_3347_);
lean_dec(v___y_3346_);
lean_dec_ref(v___y_3345_);
return v_res_3354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg(lean_object* v_mctx_3355_, lean_object* v_x_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_){
_start:
{
lean_object* v___f_3366_; lean_object* v___x_3367_; 
lean_inc(v___y_3360_);
lean_inc_ref(v___y_3359_);
lean_inc(v___y_3358_);
lean_inc_ref(v___y_3357_);
v___f_3366_ = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3366_, 0, v_x_3356_);
lean_closure_set(v___f_3366_, 1, v___y_3357_);
lean_closure_set(v___f_3366_, 2, v___y_3358_);
lean_closure_set(v___f_3366_, 3, v___y_3359_);
lean_closure_set(v___f_3366_, 4, v___y_3360_);
v___x_3367_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp(lean_box(0), v_mctx_3355_, v___f_3366_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_);
if (lean_obj_tag(v___x_3367_) == 0)
{
return v___x_3367_;
}
else
{
lean_object* v_a_3368_; lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3375_; 
v_a_3368_ = lean_ctor_get(v___x_3367_, 0);
v_isSharedCheck_3375_ = !lean_is_exclusive(v___x_3367_);
if (v_isSharedCheck_3375_ == 0)
{
v___x_3370_ = v___x_3367_;
v_isShared_3371_ = v_isSharedCheck_3375_;
goto v_resetjp_3369_;
}
else
{
lean_inc(v_a_3368_);
lean_dec(v___x_3367_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3375_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
lean_object* v___x_3373_; 
if (v_isShared_3371_ == 0)
{
v___x_3373_ = v___x_3370_;
goto v_reusejp_3372_;
}
else
{
lean_object* v_reuseFailAlloc_3374_; 
v_reuseFailAlloc_3374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3374_, 0, v_a_3368_);
v___x_3373_ = v_reuseFailAlloc_3374_;
goto v_reusejp_3372_;
}
v_reusejp_3372_:
{
return v___x_3373_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___boxed(lean_object* v_mctx_3376_, lean_object* v_x_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_){
_start:
{
lean_object* v_res_3387_; 
v_res_3387_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg(v_mctx_3376_, v_x_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_);
lean_dec(v___y_3385_);
lean_dec_ref(v___y_3384_);
lean_dec(v___y_3383_);
lean_dec_ref(v___y_3382_);
lean_dec(v___y_3381_);
lean_dec_ref(v___y_3380_);
lean_dec(v___y_3379_);
lean_dec_ref(v___y_3378_);
return v_res_3387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0(lean_object* v_00_u03b1_3388_, lean_object* v_mctx_3389_, lean_object* v_x_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_){
_start:
{
lean_object* v___x_3400_; 
v___x_3400_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg(v_mctx_3389_, v_x_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_);
return v___x_3400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___boxed(lean_object* v_00_u03b1_3401_, lean_object* v_mctx_3402_, lean_object* v_x_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_){
_start:
{
lean_object* v_res_3413_; 
v_res_3413_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0(v_00_u03b1_3401_, v_mctx_3402_, v_x_3403_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_);
lean_dec(v___y_3411_);
lean_dec_ref(v___y_3410_);
lean_dec(v___y_3409_);
lean_dec_ref(v___y_3408_);
lean_dec(v___y_3407_);
lean_dec_ref(v___y_3406_);
lean_dec(v___y_3405_);
lean_dec_ref(v___y_3404_);
return v_res_3413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0(lean_object* v_expr_3414_, uint8_t v_symm_3415_, lean_object* v_r_3416_, lean_object* v_ref_3417_, lean_object* v_checkState_x3f_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_){
_start:
{
lean_object* v___x_3428_; 
v___x_3428_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_3420_, v___y_3422_, v___y_3424_, v___y_3426_);
if (lean_obj_tag(v___x_3428_) == 0)
{
lean_object* v_a_3429_; lean_object* v_ref_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___y_3440_; 
v_a_3429_ = lean_ctor_get(v___x_3428_, 0);
lean_inc(v_a_3429_);
lean_dec_ref_known(v___x_3428_, 1);
v_ref_3430_ = lean_ctor_get(v___y_3425_, 5);
v___x_3431_ = lean_box(v_symm_3415_);
v___x_3432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3432_, 0, v_expr_3414_);
lean_ctor_set(v___x_3432_, 1, v___x_3431_);
v___x_3433_ = lean_box(0);
v___x_3434_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3434_, 0, v___x_3432_);
lean_ctor_set(v___x_3434_, 1, v___x_3433_);
v___x_3435_ = l_Lean_Meta_Rewrites_RewriteResult_newGoal(v_r_3416_);
v___x_3436_ = l_Lean_Option_toLOption___redArg(v___x_3435_);
v___x_3437_ = lean_box(0);
lean_inc(v_ref_3430_);
v___x_3438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3438_, 0, v_ref_3430_);
if (lean_obj_tag(v_checkState_x3f_3418_) == 0)
{
v___y_3440_ = v_a_3429_;
goto v___jp_3439_;
}
else
{
lean_object* v_val_3443_; 
lean_dec(v_a_3429_);
v_val_3443_ = lean_ctor_get(v_checkState_x3f_3418_, 0);
lean_inc(v_val_3443_);
lean_dec_ref_known(v_checkState_x3f_3418_, 1);
v___y_3440_ = v_val_3443_;
goto v___jp_3439_;
}
v___jp_3439_:
{
lean_object* v___x_3441_; lean_object* v___x_3442_; 
v___x_3441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3441_, 0, v___y_3440_);
v___x_3442_ = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion(v_ref_3417_, v___x_3434_, v___x_3436_, v___x_3437_, v___x_3438_, v___x_3441_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_);
return v___x_3442_;
}
}
else
{
lean_object* v_a_3444_; lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3451_; 
lean_dec(v_checkState_x3f_3418_);
lean_dec(v_ref_3417_);
lean_dec_ref(v_expr_3414_);
v_a_3444_ = lean_ctor_get(v___x_3428_, 0);
v_isSharedCheck_3451_ = !lean_is_exclusive(v___x_3428_);
if (v_isSharedCheck_3451_ == 0)
{
v___x_3446_ = v___x_3428_;
v_isShared_3447_ = v_isSharedCheck_3451_;
goto v_resetjp_3445_;
}
else
{
lean_inc(v_a_3444_);
lean_dec(v___x_3428_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3451_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
lean_object* v___x_3449_; 
if (v_isShared_3447_ == 0)
{
v___x_3449_ = v___x_3446_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v_a_3444_);
v___x_3449_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
return v___x_3449_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0___boxed(lean_object* v_expr_3452_, lean_object* v_symm_3453_, lean_object* v_r_3454_, lean_object* v_ref_3455_, lean_object* v_checkState_x3f_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_){
_start:
{
uint8_t v_symm_boxed_3466_; lean_object* v_res_3467_; 
v_symm_boxed_3466_ = lean_unbox(v_symm_3453_);
v_res_3467_ = l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0(v_expr_3452_, v_symm_boxed_3466_, v_r_3454_, v_ref_3455_, v_checkState_x3f_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_);
lean_dec(v___y_3464_);
lean_dec_ref(v___y_3463_);
lean_dec(v___y_3462_);
lean_dec_ref(v___y_3461_);
lean_dec(v___y_3460_);
lean_dec_ref(v___y_3459_);
lean_dec(v___y_3458_);
lean_dec_ref(v___y_3457_);
lean_dec_ref(v_r_3454_);
return v_res_3467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion(lean_object* v_ref_3468_, lean_object* v_r_3469_, lean_object* v_checkState_x3f_3470_, lean_object* v_a_3471_, lean_object* v_a_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_){
_start:
{
lean_object* v_expr_3480_; uint8_t v_symm_3481_; lean_object* v_mctx_3482_; lean_object* v___x_3483_; lean_object* v___f_3484_; lean_object* v___x_3485_; 
v_expr_3480_ = lean_ctor_get(v_r_3469_, 0);
lean_inc_ref(v_expr_3480_);
v_symm_3481_ = lean_ctor_get_uint8(v_r_3469_, sizeof(void*)*4);
v_mctx_3482_ = lean_ctor_get(v_r_3469_, 3);
lean_inc_ref(v_mctx_3482_);
v___x_3483_ = lean_box(v_symm_3481_);
v___f_3484_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0___boxed), 14, 5);
lean_closure_set(v___f_3484_, 0, v_expr_3480_);
lean_closure_set(v___f_3484_, 1, v___x_3483_);
lean_closure_set(v___f_3484_, 2, v_r_3469_);
lean_closure_set(v___f_3484_, 3, v_ref_3468_);
lean_closure_set(v___f_3484_, 4, v_checkState_x3f_3470_);
v___x_3485_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg(v_mctx_3482_, v___f_3484_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_);
return v___x_3485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___boxed(lean_object* v_ref_3486_, lean_object* v_r_3487_, lean_object* v_checkState_x3f_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_, lean_object* v_a_3493_, lean_object* v_a_3494_, lean_object* v_a_3495_, lean_object* v_a_3496_, lean_object* v_a_3497_){
_start:
{
lean_object* v_res_3498_; 
v_res_3498_ = l_Lean_Meta_Rewrites_RewriteResult_addSuggestion(v_ref_3486_, v_r_3487_, v_checkState_x3f_3488_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_, v_a_3495_, v_a_3496_);
lean_dec(v_a_3496_);
lean_dec_ref(v_a_3495_);
lean_dec(v_a_3494_);
lean_dec_ref(v_a_3493_);
lean_dec(v_a_3492_);
lean_dec_ref(v_a_3491_);
lean_dec(v_a_3490_);
lean_dec_ref(v_a_3489_);
return v_res_3498_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3___redArg(lean_object* v_a_3499_, lean_object* v_b_3500_, lean_object* v_x_3501_){
_start:
{
if (lean_obj_tag(v_x_3501_) == 0)
{
lean_dec(v_b_3500_);
lean_dec_ref(v_a_3499_);
return v_x_3501_;
}
else
{
lean_object* v_key_3502_; lean_object* v_value_3503_; lean_object* v_tail_3504_; lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3516_; 
v_key_3502_ = lean_ctor_get(v_x_3501_, 0);
v_value_3503_ = lean_ctor_get(v_x_3501_, 1);
v_tail_3504_ = lean_ctor_get(v_x_3501_, 2);
v_isSharedCheck_3516_ = !lean_is_exclusive(v_x_3501_);
if (v_isSharedCheck_3516_ == 0)
{
v___x_3506_ = v_x_3501_;
v_isShared_3507_ = v_isSharedCheck_3516_;
goto v_resetjp_3505_;
}
else
{
lean_inc(v_tail_3504_);
lean_inc(v_value_3503_);
lean_inc(v_key_3502_);
lean_dec(v_x_3501_);
v___x_3506_ = lean_box(0);
v_isShared_3507_ = v_isSharedCheck_3516_;
goto v_resetjp_3505_;
}
v_resetjp_3505_:
{
uint8_t v___x_3508_; 
v___x_3508_ = lean_string_dec_eq(v_key_3502_, v_a_3499_);
if (v___x_3508_ == 0)
{
lean_object* v___x_3509_; lean_object* v___x_3511_; 
v___x_3509_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3___redArg(v_a_3499_, v_b_3500_, v_tail_3504_);
if (v_isShared_3507_ == 0)
{
lean_ctor_set(v___x_3506_, 2, v___x_3509_);
v___x_3511_ = v___x_3506_;
goto v_reusejp_3510_;
}
else
{
lean_object* v_reuseFailAlloc_3512_; 
v_reuseFailAlloc_3512_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3512_, 0, v_key_3502_);
lean_ctor_set(v_reuseFailAlloc_3512_, 1, v_value_3503_);
lean_ctor_set(v_reuseFailAlloc_3512_, 2, v___x_3509_);
v___x_3511_ = v_reuseFailAlloc_3512_;
goto v_reusejp_3510_;
}
v_reusejp_3510_:
{
return v___x_3511_;
}
}
else
{
lean_object* v___x_3514_; 
lean_dec(v_value_3503_);
lean_dec(v_key_3502_);
if (v_isShared_3507_ == 0)
{
lean_ctor_set(v___x_3506_, 1, v_b_3500_);
lean_ctor_set(v___x_3506_, 0, v_a_3499_);
v___x_3514_ = v___x_3506_;
goto v_reusejp_3513_;
}
else
{
lean_object* v_reuseFailAlloc_3515_; 
v_reuseFailAlloc_3515_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3515_, 0, v_a_3499_);
lean_ctor_set(v_reuseFailAlloc_3515_, 1, v_b_3500_);
lean_ctor_set(v_reuseFailAlloc_3515_, 2, v_tail_3504_);
v___x_3514_ = v_reuseFailAlloc_3515_;
goto v_reusejp_3513_;
}
v_reusejp_3513_:
{
return v___x_3514_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_x_3517_, lean_object* v_x_3518_){
_start:
{
if (lean_obj_tag(v_x_3518_) == 0)
{
return v_x_3517_;
}
else
{
lean_object* v_key_3519_; lean_object* v_value_3520_; lean_object* v_tail_3521_; lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3544_; 
v_key_3519_ = lean_ctor_get(v_x_3518_, 0);
v_value_3520_ = lean_ctor_get(v_x_3518_, 1);
v_tail_3521_ = lean_ctor_get(v_x_3518_, 2);
v_isSharedCheck_3544_ = !lean_is_exclusive(v_x_3518_);
if (v_isSharedCheck_3544_ == 0)
{
v___x_3523_ = v_x_3518_;
v_isShared_3524_ = v_isSharedCheck_3544_;
goto v_resetjp_3522_;
}
else
{
lean_inc(v_tail_3521_);
lean_inc(v_value_3520_);
lean_inc(v_key_3519_);
lean_dec(v_x_3518_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3544_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
lean_object* v___x_3525_; uint64_t v___x_3526_; uint64_t v___x_3527_; uint64_t v___x_3528_; uint64_t v_fold_3529_; uint64_t v___x_3530_; uint64_t v___x_3531_; uint64_t v___x_3532_; size_t v___x_3533_; size_t v___x_3534_; size_t v___x_3535_; size_t v___x_3536_; size_t v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3540_; 
v___x_3525_ = lean_array_get_size(v_x_3517_);
v___x_3526_ = lean_string_hash(v_key_3519_);
v___x_3527_ = 32ULL;
v___x_3528_ = lean_uint64_shift_right(v___x_3526_, v___x_3527_);
v_fold_3529_ = lean_uint64_xor(v___x_3526_, v___x_3528_);
v___x_3530_ = 16ULL;
v___x_3531_ = lean_uint64_shift_right(v_fold_3529_, v___x_3530_);
v___x_3532_ = lean_uint64_xor(v_fold_3529_, v___x_3531_);
v___x_3533_ = lean_uint64_to_usize(v___x_3532_);
v___x_3534_ = lean_usize_of_nat(v___x_3525_);
v___x_3535_ = ((size_t)1ULL);
v___x_3536_ = lean_usize_sub(v___x_3534_, v___x_3535_);
v___x_3537_ = lean_usize_land(v___x_3533_, v___x_3536_);
v___x_3538_ = lean_array_uget_borrowed(v_x_3517_, v___x_3537_);
lean_inc(v___x_3538_);
if (v_isShared_3524_ == 0)
{
lean_ctor_set(v___x_3523_, 2, v___x_3538_);
v___x_3540_ = v___x_3523_;
goto v_reusejp_3539_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v_key_3519_);
lean_ctor_set(v_reuseFailAlloc_3543_, 1, v_value_3520_);
lean_ctor_set(v_reuseFailAlloc_3543_, 2, v___x_3538_);
v___x_3540_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3539_;
}
v_reusejp_3539_:
{
lean_object* v___x_3541_; 
v___x_3541_ = lean_array_uset(v_x_3517_, v___x_3537_, v___x_3540_);
v_x_3517_ = v___x_3541_;
v_x_3518_ = v_tail_3521_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3___redArg(lean_object* v_i_3545_, lean_object* v_source_3546_, lean_object* v_target_3547_){
_start:
{
lean_object* v___x_3548_; uint8_t v___x_3549_; 
v___x_3548_ = lean_array_get_size(v_source_3546_);
v___x_3549_ = lean_nat_dec_lt(v_i_3545_, v___x_3548_);
if (v___x_3549_ == 0)
{
lean_dec_ref(v_source_3546_);
lean_dec(v_i_3545_);
return v_target_3547_;
}
else
{
lean_object* v_es_3550_; lean_object* v___x_3551_; lean_object* v_source_3552_; lean_object* v_target_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; 
v_es_3550_ = lean_array_fget(v_source_3546_, v_i_3545_);
v___x_3551_ = lean_box(0);
v_source_3552_ = lean_array_fset(v_source_3546_, v_i_3545_, v___x_3551_);
v_target_3553_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3_spec__5___redArg(v_target_3547_, v_es_3550_);
v___x_3554_ = lean_unsigned_to_nat(1u);
v___x_3555_ = lean_nat_add(v_i_3545_, v___x_3554_);
lean_dec(v_i_3545_);
v_i_3545_ = v___x_3555_;
v_source_3546_ = v_source_3552_;
v_target_3547_ = v_target_3553_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2___redArg(lean_object* v_data_3557_){
_start:
{
lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v_nbuckets_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; 
v___x_3558_ = lean_array_get_size(v_data_3557_);
v___x_3559_ = lean_unsigned_to_nat(2u);
v_nbuckets_3560_ = lean_nat_mul(v___x_3558_, v___x_3559_);
v___x_3561_ = lean_unsigned_to_nat(0u);
v___x_3562_ = lean_box(0);
v___x_3563_ = lean_mk_array(v_nbuckets_3560_, v___x_3562_);
v___x_3564_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3___redArg(v___x_3561_, v_data_3557_, v___x_3563_);
return v___x_3564_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(lean_object* v_a_3565_, lean_object* v_x_3566_){
_start:
{
if (lean_obj_tag(v_x_3566_) == 0)
{
uint8_t v___x_3567_; 
v___x_3567_ = 0;
return v___x_3567_;
}
else
{
lean_object* v_key_3568_; lean_object* v_tail_3569_; uint8_t v___x_3570_; 
v_key_3568_ = lean_ctor_get(v_x_3566_, 0);
v_tail_3569_ = lean_ctor_get(v_x_3566_, 2);
v___x_3570_ = lean_string_dec_eq(v_key_3568_, v_a_3565_);
if (v___x_3570_ == 0)
{
v_x_3566_ = v_tail_3569_;
goto _start;
}
else
{
return v___x_3570_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg___boxed(lean_object* v_a_3572_, lean_object* v_x_3573_){
_start:
{
uint8_t v_res_3574_; lean_object* v_r_3575_; 
v_res_3574_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(v_a_3572_, v_x_3573_);
lean_dec(v_x_3573_);
lean_dec_ref(v_a_3572_);
v_r_3575_ = lean_box(v_res_3574_);
return v_r_3575_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1___redArg(lean_object* v_m_3576_, lean_object* v_a_3577_, lean_object* v_b_3578_){
_start:
{
lean_object* v_size_3579_; lean_object* v_buckets_3580_; lean_object* v___x_3582_; uint8_t v_isShared_3583_; uint8_t v_isSharedCheck_3623_; 
v_size_3579_ = lean_ctor_get(v_m_3576_, 0);
v_buckets_3580_ = lean_ctor_get(v_m_3576_, 1);
v_isSharedCheck_3623_ = !lean_is_exclusive(v_m_3576_);
if (v_isSharedCheck_3623_ == 0)
{
v___x_3582_ = v_m_3576_;
v_isShared_3583_ = v_isSharedCheck_3623_;
goto v_resetjp_3581_;
}
else
{
lean_inc(v_buckets_3580_);
lean_inc(v_size_3579_);
lean_dec(v_m_3576_);
v___x_3582_ = lean_box(0);
v_isShared_3583_ = v_isSharedCheck_3623_;
goto v_resetjp_3581_;
}
v_resetjp_3581_:
{
lean_object* v___x_3584_; uint64_t v___x_3585_; uint64_t v___x_3586_; uint64_t v___x_3587_; uint64_t v_fold_3588_; uint64_t v___x_3589_; uint64_t v___x_3590_; uint64_t v___x_3591_; size_t v___x_3592_; size_t v___x_3593_; size_t v___x_3594_; size_t v___x_3595_; size_t v___x_3596_; lean_object* v_bkt_3597_; uint8_t v___x_3598_; 
v___x_3584_ = lean_array_get_size(v_buckets_3580_);
v___x_3585_ = lean_string_hash(v_a_3577_);
v___x_3586_ = 32ULL;
v___x_3587_ = lean_uint64_shift_right(v___x_3585_, v___x_3586_);
v_fold_3588_ = lean_uint64_xor(v___x_3585_, v___x_3587_);
v___x_3589_ = 16ULL;
v___x_3590_ = lean_uint64_shift_right(v_fold_3588_, v___x_3589_);
v___x_3591_ = lean_uint64_xor(v_fold_3588_, v___x_3590_);
v___x_3592_ = lean_uint64_to_usize(v___x_3591_);
v___x_3593_ = lean_usize_of_nat(v___x_3584_);
v___x_3594_ = ((size_t)1ULL);
v___x_3595_ = lean_usize_sub(v___x_3593_, v___x_3594_);
v___x_3596_ = lean_usize_land(v___x_3592_, v___x_3595_);
v_bkt_3597_ = lean_array_uget_borrowed(v_buckets_3580_, v___x_3596_);
v___x_3598_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(v_a_3577_, v_bkt_3597_);
if (v___x_3598_ == 0)
{
lean_object* v___x_3599_; lean_object* v_size_x27_3600_; lean_object* v___x_3601_; lean_object* v_buckets_x27_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; uint8_t v___x_3608_; 
v___x_3599_ = lean_unsigned_to_nat(1u);
v_size_x27_3600_ = lean_nat_add(v_size_3579_, v___x_3599_);
lean_dec(v_size_3579_);
lean_inc(v_bkt_3597_);
v___x_3601_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3601_, 0, v_a_3577_);
lean_ctor_set(v___x_3601_, 1, v_b_3578_);
lean_ctor_set(v___x_3601_, 2, v_bkt_3597_);
v_buckets_x27_3602_ = lean_array_uset(v_buckets_3580_, v___x_3596_, v___x_3601_);
v___x_3603_ = lean_unsigned_to_nat(4u);
v___x_3604_ = lean_nat_mul(v_size_x27_3600_, v___x_3603_);
v___x_3605_ = lean_unsigned_to_nat(3u);
v___x_3606_ = lean_nat_div(v___x_3604_, v___x_3605_);
lean_dec(v___x_3604_);
v___x_3607_ = lean_array_get_size(v_buckets_x27_3602_);
v___x_3608_ = lean_nat_dec_le(v___x_3606_, v___x_3607_);
lean_dec(v___x_3606_);
if (v___x_3608_ == 0)
{
lean_object* v_val_3609_; lean_object* v___x_3611_; 
v_val_3609_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2___redArg(v_buckets_x27_3602_);
if (v_isShared_3583_ == 0)
{
lean_ctor_set(v___x_3582_, 1, v_val_3609_);
lean_ctor_set(v___x_3582_, 0, v_size_x27_3600_);
v___x_3611_ = v___x_3582_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v_size_x27_3600_);
lean_ctor_set(v_reuseFailAlloc_3612_, 1, v_val_3609_);
v___x_3611_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
return v___x_3611_;
}
}
else
{
lean_object* v___x_3614_; 
if (v_isShared_3583_ == 0)
{
lean_ctor_set(v___x_3582_, 1, v_buckets_x27_3602_);
lean_ctor_set(v___x_3582_, 0, v_size_x27_3600_);
v___x_3614_ = v___x_3582_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3615_; 
v_reuseFailAlloc_3615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3615_, 0, v_size_x27_3600_);
lean_ctor_set(v_reuseFailAlloc_3615_, 1, v_buckets_x27_3602_);
v___x_3614_ = v_reuseFailAlloc_3615_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
return v___x_3614_;
}
}
}
else
{
lean_object* v___x_3616_; lean_object* v_buckets_x27_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3621_; 
lean_inc(v_bkt_3597_);
v___x_3616_ = lean_box(0);
v_buckets_x27_3617_ = lean_array_uset(v_buckets_3580_, v___x_3596_, v___x_3616_);
v___x_3618_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3___redArg(v_a_3577_, v_b_3578_, v_bkt_3597_);
v___x_3619_ = lean_array_uset(v_buckets_x27_3617_, v___x_3596_, v___x_3618_);
if (v_isShared_3583_ == 0)
{
lean_ctor_set(v___x_3582_, 1, v___x_3619_);
v___x_3621_ = v___x_3582_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v_size_3579_);
lean_ctor_set(v_reuseFailAlloc_3622_, 1, v___x_3619_);
v___x_3621_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
return v___x_3621_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg(lean_object* v_m_3624_, lean_object* v_a_3625_){
_start:
{
lean_object* v_buckets_3626_; lean_object* v___x_3627_; uint64_t v___x_3628_; uint64_t v___x_3629_; uint64_t v___x_3630_; uint64_t v_fold_3631_; uint64_t v___x_3632_; uint64_t v___x_3633_; uint64_t v___x_3634_; size_t v___x_3635_; size_t v___x_3636_; size_t v___x_3637_; size_t v___x_3638_; size_t v___x_3639_; lean_object* v___x_3640_; uint8_t v___x_3641_; 
v_buckets_3626_ = lean_ctor_get(v_m_3624_, 1);
v___x_3627_ = lean_array_get_size(v_buckets_3626_);
v___x_3628_ = lean_string_hash(v_a_3625_);
v___x_3629_ = 32ULL;
v___x_3630_ = lean_uint64_shift_right(v___x_3628_, v___x_3629_);
v_fold_3631_ = lean_uint64_xor(v___x_3628_, v___x_3630_);
v___x_3632_ = 16ULL;
v___x_3633_ = lean_uint64_shift_right(v_fold_3631_, v___x_3632_);
v___x_3634_ = lean_uint64_xor(v_fold_3631_, v___x_3633_);
v___x_3635_ = lean_uint64_to_usize(v___x_3634_);
v___x_3636_ = lean_usize_of_nat(v___x_3627_);
v___x_3637_ = ((size_t)1ULL);
v___x_3638_ = lean_usize_sub(v___x_3636_, v___x_3637_);
v___x_3639_ = lean_usize_land(v___x_3635_, v___x_3638_);
v___x_3640_ = lean_array_uget_borrowed(v_buckets_3626_, v___x_3639_);
v___x_3641_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(v_a_3625_, v___x_3640_);
return v___x_3641_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg___boxed(lean_object* v_m_3642_, lean_object* v_a_3643_){
_start:
{
uint8_t v_res_3644_; lean_object* v_r_3645_; 
v_res_3644_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg(v_m_3642_, v_a_3643_);
lean_dec_ref(v_a_3643_);
lean_dec_ref(v_m_3642_);
v_r_3645_ = lean_box(v_res_3644_);
return v_r_3645_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg(lean_object* v_cfg_3646_, lean_object* v_as_x27_3647_, lean_object* v_b_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_){
_start:
{
if (lean_obj_tag(v_as_x27_3647_) == 0)
{
lean_object* v___x_3654_; 
lean_dec_ref(v_cfg_3646_);
v___x_3654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3654_, 0, v_b_3648_);
return v___x_3654_;
}
else
{
lean_object* v_head_3655_; lean_object* v_snd_3656_; lean_object* v_tail_3657_; lean_object* v_fst_3658_; lean_object* v_fst_3659_; lean_object* v_snd_3660_; lean_object* v___x_3661_; 
v_head_3655_ = lean_ctor_get(v_as_x27_3647_, 0);
v_snd_3656_ = lean_ctor_get(v_head_3655_, 1);
v_tail_3657_ = lean_ctor_get(v_as_x27_3647_, 1);
v_fst_3658_ = lean_ctor_get(v_head_3655_, 0);
v_fst_3659_ = lean_ctor_get(v_snd_3656_, 0);
v_snd_3660_ = lean_ctor_get(v_snd_3656_, 1);
v___x_3661_ = l_Lean_getRemainingHeartbeats___redArg(v___y_3651_);
if (lean_obj_tag(v___x_3661_) == 0)
{
lean_object* v_snd_3662_; lean_object* v___x_3664_; uint8_t v_isShared_3665_; uint8_t v_isSharedCheck_3806_; 
v_snd_3662_ = lean_ctor_get(v_b_3648_, 1);
v_isSharedCheck_3806_ = !lean_is_exclusive(v_b_3648_);
if (v_isSharedCheck_3806_ == 0)
{
lean_object* v_unused_3807_; 
v_unused_3807_ = lean_ctor_get(v_b_3648_, 0);
lean_dec(v_unused_3807_);
v___x_3664_ = v_b_3648_;
v_isShared_3665_ = v_isSharedCheck_3806_;
goto v_resetjp_3663_;
}
else
{
lean_inc(v_snd_3662_);
lean_dec(v_b_3648_);
v___x_3664_ = lean_box(0);
v_isShared_3665_ = v_isSharedCheck_3806_;
goto v_resetjp_3663_;
}
v_resetjp_3663_:
{
lean_object* v_a_3666_; lean_object* v___x_3668_; uint8_t v_isShared_3669_; uint8_t v_isSharedCheck_3805_; 
v_a_3666_ = lean_ctor_get(v___x_3661_, 0);
v_isSharedCheck_3805_ = !lean_is_exclusive(v___x_3661_);
if (v_isSharedCheck_3805_ == 0)
{
v___x_3668_ = v___x_3661_;
v_isShared_3669_ = v_isSharedCheck_3805_;
goto v_resetjp_3667_;
}
else
{
lean_inc(v_a_3666_);
lean_dec(v___x_3661_);
v___x_3668_ = lean_box(0);
v_isShared_3669_ = v_isSharedCheck_3805_;
goto v_resetjp_3667_;
}
v_resetjp_3667_:
{
lean_object* v_fst_3670_; lean_object* v_snd_3671_; lean_object* v___x_3673_; uint8_t v_isShared_3674_; uint8_t v_isSharedCheck_3804_; 
v_fst_3670_ = lean_ctor_get(v_snd_3662_, 0);
v_snd_3671_ = lean_ctor_get(v_snd_3662_, 1);
v_isSharedCheck_3804_ = !lean_is_exclusive(v_snd_3662_);
if (v_isSharedCheck_3804_ == 0)
{
v___x_3673_ = v_snd_3662_;
v_isShared_3674_ = v_isSharedCheck_3804_;
goto v_resetjp_3672_;
}
else
{
lean_inc(v_snd_3671_);
lean_inc(v_fst_3670_);
lean_dec(v_snd_3662_);
v___x_3673_ = lean_box(0);
v_isShared_3674_ = v_isSharedCheck_3804_;
goto v_resetjp_3672_;
}
v_resetjp_3672_:
{
uint8_t v_stopAtRfl_3675_; lean_object* v_max_3676_; lean_object* v_minHeartbeats_3677_; lean_object* v_goal_3678_; lean_object* v_target_3679_; uint8_t v_side_3680_; lean_object* v_mctx_3681_; uint8_t v___x_3682_; 
v_stopAtRfl_3675_ = lean_ctor_get_uint8(v_cfg_3646_, sizeof(void*)*5);
v_max_3676_ = lean_ctor_get(v_cfg_3646_, 0);
v_minHeartbeats_3677_ = lean_ctor_get(v_cfg_3646_, 1);
v_goal_3678_ = lean_ctor_get(v_cfg_3646_, 2);
v_target_3679_ = lean_ctor_get(v_cfg_3646_, 3);
v_side_3680_ = lean_ctor_get_uint8(v_cfg_3646_, sizeof(void*)*5 + 1);
v_mctx_3681_ = lean_ctor_get(v_cfg_3646_, 4);
v___x_3682_ = lean_nat_dec_lt(v_a_3666_, v_minHeartbeats_3677_);
lean_dec(v_a_3666_);
if (v___x_3682_ == 0)
{
lean_object* v___x_3683_; uint8_t v___x_3684_; 
v___x_3683_ = lean_array_get_size(v_snd_3671_);
v___x_3684_ = lean_nat_dec_le(v_max_3676_, v___x_3683_);
if (v___x_3684_ == 0)
{
lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; 
lean_del_object(v___x_3668_);
v___x_3685_ = lean_box(v_side_3680_);
lean_inc(v_snd_3660_);
lean_inc(v_fst_3659_);
lean_inc(v_fst_3658_);
lean_inc_ref(v_target_3679_);
lean_inc(v_goal_3678_);
lean_inc_ref_n(v_mctx_3681_, 2);
v___x_3686_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_rwLemma___boxed), 12, 7);
lean_closure_set(v___x_3686_, 0, v_mctx_3681_);
lean_closure_set(v___x_3686_, 1, v_goal_3678_);
lean_closure_set(v___x_3686_, 2, v_target_3679_);
lean_closure_set(v___x_3686_, 3, v___x_3685_);
lean_closure_set(v___x_3686_, 4, v_fst_3658_);
lean_closure_set(v___x_3686_, 5, v_fst_3659_);
lean_closure_set(v___x_3686_, 6, v_snd_3660_);
v___x_3687_ = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___boxed), 8, 3);
lean_closure_set(v___x_3687_, 0, lean_box(0));
lean_closure_set(v___x_3687_, 1, v_mctx_3681_);
lean_closure_set(v___x_3687_, 2, v___x_3686_);
v___x_3688_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v___x_3687_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_);
if (lean_obj_tag(v___x_3688_) == 0)
{
lean_object* v_a_3689_; lean_object* v___x_3690_; 
v_a_3689_ = lean_ctor_get(v___x_3688_, 0);
lean_inc(v_a_3689_);
lean_dec_ref_known(v___x_3688_, 1);
v___x_3690_ = lean_box(0);
if (lean_obj_tag(v_a_3689_) == 0)
{
lean_object* v___x_3692_; 
if (v_isShared_3674_ == 0)
{
v___x_3692_ = v___x_3673_;
goto v_reusejp_3691_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v_fst_3670_);
lean_ctor_set(v_reuseFailAlloc_3697_, 1, v_snd_3671_);
v___x_3692_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3691_;
}
v_reusejp_3691_:
{
lean_object* v___x_3694_; 
if (v_isShared_3665_ == 0)
{
lean_ctor_set(v___x_3664_, 1, v___x_3692_);
lean_ctor_set(v___x_3664_, 0, v___x_3690_);
v___x_3694_ = v___x_3664_;
goto v_reusejp_3693_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v___x_3690_);
lean_ctor_set(v_reuseFailAlloc_3696_, 1, v___x_3692_);
v___x_3694_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3693_;
}
v_reusejp_3693_:
{
v_as_x27_3647_ = v_tail_3657_;
v_b_3648_ = v___x_3694_;
goto _start;
}
}
}
else
{
lean_object* v_val_3698_; lean_object* v___x_3700_; uint8_t v_isShared_3701_; uint8_t v_isSharedCheck_3775_; 
v_val_3698_ = lean_ctor_get(v_a_3689_, 0);
v_isSharedCheck_3775_ = !lean_is_exclusive(v_a_3689_);
if (v_isSharedCheck_3775_ == 0)
{
v___x_3700_ = v_a_3689_;
v_isShared_3701_ = v_isSharedCheck_3775_;
goto v_resetjp_3699_;
}
else
{
lean_inc(v_val_3698_);
lean_dec(v_a_3689_);
v___x_3700_ = lean_box(0);
v_isShared_3701_ = v_isSharedCheck_3775_;
goto v_resetjp_3699_;
}
v_resetjp_3699_:
{
lean_object* v_result_3702_; lean_object* v_mctx_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; 
v_result_3702_ = lean_ctor_get(v_val_3698_, 2);
v_mctx_3703_ = lean_ctor_get(v_val_3698_, 3);
lean_inc(v_val_3698_);
v___x_3704_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult___boxed), 6, 1);
lean_closure_set(v___x_3704_, 0, v_val_3698_);
lean_inc_ref(v_mctx_3703_);
v___x_3705_ = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___boxed), 8, 3);
lean_closure_set(v___x_3705_, 0, lean_box(0));
lean_closure_set(v___x_3705_, 1, v_mctx_3703_);
lean_closure_set(v___x_3705_, 2, v___x_3704_);
v___x_3706_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v___x_3705_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_);
if (lean_obj_tag(v___x_3706_) == 0)
{
lean_object* v_a_3707_; uint8_t v___x_3708_; 
v_a_3707_ = lean_ctor_get(v___x_3706_, 0);
lean_inc(v_a_3707_);
lean_dec_ref_known(v___x_3706_, 1);
v___x_3708_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg(v_fst_3670_, v_a_3707_);
if (v___x_3708_ == 0)
{
lean_object* v_eNew_3709_; lean_object* v___x_3710_; 
v_eNew_3709_ = lean_ctor_get(v_result_3702_, 0);
lean_inc_ref(v_eNew_3709_);
lean_inc_ref(v_mctx_3703_);
v___x_3710_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(v_mctx_3703_, v_eNew_3709_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_);
if (lean_obj_tag(v___x_3710_) == 0)
{
if (v_stopAtRfl_3675_ == 0)
{
lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3715_; 
lean_dec_ref_known(v___x_3710_, 1);
lean_del_object(v___x_3700_);
v___x_3711_ = lean_box(0);
v___x_3712_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1___redArg(v_fst_3670_, v_a_3707_, v___x_3711_);
v___x_3713_ = lean_array_push(v_snd_3671_, v_val_3698_);
if (v_isShared_3674_ == 0)
{
lean_ctor_set(v___x_3673_, 1, v___x_3713_);
lean_ctor_set(v___x_3673_, 0, v___x_3712_);
v___x_3715_ = v___x_3673_;
goto v_reusejp_3714_;
}
else
{
lean_object* v_reuseFailAlloc_3720_; 
v_reuseFailAlloc_3720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3720_, 0, v___x_3712_);
lean_ctor_set(v_reuseFailAlloc_3720_, 1, v___x_3713_);
v___x_3715_ = v_reuseFailAlloc_3720_;
goto v_reusejp_3714_;
}
v_reusejp_3714_:
{
lean_object* v___x_3717_; 
if (v_isShared_3665_ == 0)
{
lean_ctor_set(v___x_3664_, 1, v___x_3715_);
lean_ctor_set(v___x_3664_, 0, v___x_3690_);
v___x_3717_ = v___x_3664_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3719_; 
v_reuseFailAlloc_3719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3719_, 0, v___x_3690_);
lean_ctor_set(v_reuseFailAlloc_3719_, 1, v___x_3715_);
v___x_3717_ = v_reuseFailAlloc_3719_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
v_as_x27_3647_ = v_tail_3657_;
v_b_3648_ = v___x_3717_;
goto _start;
}
}
}
else
{
lean_object* v_a_3721_; lean_object* v___x_3723_; uint8_t v_isShared_3724_; uint8_t v_isSharedCheck_3751_; 
v_a_3721_ = lean_ctor_get(v___x_3710_, 0);
v_isSharedCheck_3751_ = !lean_is_exclusive(v___x_3710_);
if (v_isSharedCheck_3751_ == 0)
{
v___x_3723_ = v___x_3710_;
v_isShared_3724_ = v_isSharedCheck_3751_;
goto v_resetjp_3722_;
}
else
{
lean_inc(v_a_3721_);
lean_dec(v___x_3710_);
v___x_3723_ = lean_box(0);
v_isShared_3724_ = v_isSharedCheck_3751_;
goto v_resetjp_3722_;
}
v_resetjp_3722_:
{
uint8_t v___x_3725_; 
v___x_3725_ = lean_unbox(v_a_3721_);
lean_dec(v_a_3721_);
if (v___x_3725_ == 0)
{
lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3730_; 
lean_del_object(v___x_3723_);
lean_del_object(v___x_3700_);
v___x_3726_ = lean_box(0);
v___x_3727_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1___redArg(v_fst_3670_, v_a_3707_, v___x_3726_);
v___x_3728_ = lean_array_push(v_snd_3671_, v_val_3698_);
if (v_isShared_3674_ == 0)
{
lean_ctor_set(v___x_3673_, 1, v___x_3728_);
lean_ctor_set(v___x_3673_, 0, v___x_3727_);
v___x_3730_ = v___x_3673_;
goto v_reusejp_3729_;
}
else
{
lean_object* v_reuseFailAlloc_3735_; 
v_reuseFailAlloc_3735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3735_, 0, v___x_3727_);
lean_ctor_set(v_reuseFailAlloc_3735_, 1, v___x_3728_);
v___x_3730_ = v_reuseFailAlloc_3735_;
goto v_reusejp_3729_;
}
v_reusejp_3729_:
{
lean_object* v___x_3732_; 
if (v_isShared_3665_ == 0)
{
lean_ctor_set(v___x_3664_, 1, v___x_3730_);
lean_ctor_set(v___x_3664_, 0, v___x_3690_);
v___x_3732_ = v___x_3664_;
goto v_reusejp_3731_;
}
else
{
lean_object* v_reuseFailAlloc_3734_; 
v_reuseFailAlloc_3734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3734_, 0, v___x_3690_);
lean_ctor_set(v_reuseFailAlloc_3734_, 1, v___x_3730_);
v___x_3732_ = v_reuseFailAlloc_3734_;
goto v_reusejp_3731_;
}
v_reusejp_3731_:
{
v_as_x27_3647_ = v_tail_3657_;
v_b_3648_ = v___x_3732_;
goto _start;
}
}
}
else
{
lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3740_; 
lean_dec(v_a_3707_);
lean_dec_ref(v_cfg_3646_);
v___x_3736_ = lean_unsigned_to_nat(1u);
v___x_3737_ = lean_mk_empty_array_with_capacity(v___x_3736_);
v___x_3738_ = lean_array_push(v___x_3737_, v_val_3698_);
if (v_isShared_3701_ == 0)
{
lean_ctor_set(v___x_3700_, 0, v___x_3738_);
v___x_3740_ = v___x_3700_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v___x_3738_);
v___x_3740_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
lean_object* v___x_3742_; 
if (v_isShared_3674_ == 0)
{
v___x_3742_ = v___x_3673_;
goto v_reusejp_3741_;
}
else
{
lean_object* v_reuseFailAlloc_3749_; 
v_reuseFailAlloc_3749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3749_, 0, v_fst_3670_);
lean_ctor_set(v_reuseFailAlloc_3749_, 1, v_snd_3671_);
v___x_3742_ = v_reuseFailAlloc_3749_;
goto v_reusejp_3741_;
}
v_reusejp_3741_:
{
lean_object* v___x_3744_; 
if (v_isShared_3665_ == 0)
{
lean_ctor_set(v___x_3664_, 1, v___x_3742_);
lean_ctor_set(v___x_3664_, 0, v___x_3740_);
v___x_3744_ = v___x_3664_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v___x_3740_);
lean_ctor_set(v_reuseFailAlloc_3748_, 1, v___x_3742_);
v___x_3744_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
lean_object* v___x_3746_; 
if (v_isShared_3724_ == 0)
{
lean_ctor_set(v___x_3723_, 0, v___x_3744_);
v___x_3746_ = v___x_3723_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v___x_3744_);
v___x_3746_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
return v___x_3746_;
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
lean_object* v_a_3752_; lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_3759_; 
lean_dec(v_a_3707_);
lean_del_object(v___x_3700_);
lean_dec(v_val_3698_);
lean_del_object(v___x_3673_);
lean_dec(v_snd_3671_);
lean_dec(v_fst_3670_);
lean_del_object(v___x_3664_);
lean_dec_ref(v_cfg_3646_);
v_a_3752_ = lean_ctor_get(v___x_3710_, 0);
v_isSharedCheck_3759_ = !lean_is_exclusive(v___x_3710_);
if (v_isSharedCheck_3759_ == 0)
{
v___x_3754_ = v___x_3710_;
v_isShared_3755_ = v_isSharedCheck_3759_;
goto v_resetjp_3753_;
}
else
{
lean_inc(v_a_3752_);
lean_dec(v___x_3710_);
v___x_3754_ = lean_box(0);
v_isShared_3755_ = v_isSharedCheck_3759_;
goto v_resetjp_3753_;
}
v_resetjp_3753_:
{
lean_object* v___x_3757_; 
if (v_isShared_3755_ == 0)
{
v___x_3757_ = v___x_3754_;
goto v_reusejp_3756_;
}
else
{
lean_object* v_reuseFailAlloc_3758_; 
v_reuseFailAlloc_3758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3758_, 0, v_a_3752_);
v___x_3757_ = v_reuseFailAlloc_3758_;
goto v_reusejp_3756_;
}
v_reusejp_3756_:
{
return v___x_3757_;
}
}
}
}
else
{
lean_object* v___x_3761_; 
lean_dec(v_a_3707_);
lean_del_object(v___x_3700_);
lean_dec(v_val_3698_);
if (v_isShared_3674_ == 0)
{
v___x_3761_ = v___x_3673_;
goto v_reusejp_3760_;
}
else
{
lean_object* v_reuseFailAlloc_3766_; 
v_reuseFailAlloc_3766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3766_, 0, v_fst_3670_);
lean_ctor_set(v_reuseFailAlloc_3766_, 1, v_snd_3671_);
v___x_3761_ = v_reuseFailAlloc_3766_;
goto v_reusejp_3760_;
}
v_reusejp_3760_:
{
lean_object* v___x_3763_; 
if (v_isShared_3665_ == 0)
{
lean_ctor_set(v___x_3664_, 1, v___x_3761_);
lean_ctor_set(v___x_3664_, 0, v___x_3690_);
v___x_3763_ = v___x_3664_;
goto v_reusejp_3762_;
}
else
{
lean_object* v_reuseFailAlloc_3765_; 
v_reuseFailAlloc_3765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3765_, 0, v___x_3690_);
lean_ctor_set(v_reuseFailAlloc_3765_, 1, v___x_3761_);
v___x_3763_ = v_reuseFailAlloc_3765_;
goto v_reusejp_3762_;
}
v_reusejp_3762_:
{
v_as_x27_3647_ = v_tail_3657_;
v_b_3648_ = v___x_3763_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3767_; lean_object* v___x_3769_; uint8_t v_isShared_3770_; uint8_t v_isSharedCheck_3774_; 
lean_del_object(v___x_3700_);
lean_dec(v_val_3698_);
lean_del_object(v___x_3673_);
lean_dec(v_snd_3671_);
lean_dec(v_fst_3670_);
lean_del_object(v___x_3664_);
lean_dec_ref(v_cfg_3646_);
v_a_3767_ = lean_ctor_get(v___x_3706_, 0);
v_isSharedCheck_3774_ = !lean_is_exclusive(v___x_3706_);
if (v_isSharedCheck_3774_ == 0)
{
v___x_3769_ = v___x_3706_;
v_isShared_3770_ = v_isSharedCheck_3774_;
goto v_resetjp_3768_;
}
else
{
lean_inc(v_a_3767_);
lean_dec(v___x_3706_);
v___x_3769_ = lean_box(0);
v_isShared_3770_ = v_isSharedCheck_3774_;
goto v_resetjp_3768_;
}
v_resetjp_3768_:
{
lean_object* v___x_3772_; 
if (v_isShared_3770_ == 0)
{
v___x_3772_ = v___x_3769_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3773_; 
v_reuseFailAlloc_3773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3773_, 0, v_a_3767_);
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
lean_object* v_a_3776_; lean_object* v___x_3778_; uint8_t v_isShared_3779_; uint8_t v_isSharedCheck_3783_; 
lean_del_object(v___x_3673_);
lean_dec(v_snd_3671_);
lean_dec(v_fst_3670_);
lean_del_object(v___x_3664_);
lean_dec_ref(v_cfg_3646_);
v_a_3776_ = lean_ctor_get(v___x_3688_, 0);
v_isSharedCheck_3783_ = !lean_is_exclusive(v___x_3688_);
if (v_isSharedCheck_3783_ == 0)
{
v___x_3778_ = v___x_3688_;
v_isShared_3779_ = v_isSharedCheck_3783_;
goto v_resetjp_3777_;
}
else
{
lean_inc(v_a_3776_);
lean_dec(v___x_3688_);
v___x_3778_ = lean_box(0);
v_isShared_3779_ = v_isSharedCheck_3783_;
goto v_resetjp_3777_;
}
v_resetjp_3777_:
{
lean_object* v___x_3781_; 
if (v_isShared_3779_ == 0)
{
v___x_3781_ = v___x_3778_;
goto v_reusejp_3780_;
}
else
{
lean_object* v_reuseFailAlloc_3782_; 
v_reuseFailAlloc_3782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3782_, 0, v_a_3776_);
v___x_3781_ = v_reuseFailAlloc_3782_;
goto v_reusejp_3780_;
}
v_reusejp_3780_:
{
return v___x_3781_;
}
}
}
}
else
{
lean_object* v___x_3784_; lean_object* v___x_3786_; 
lean_dec_ref(v_cfg_3646_);
lean_inc(v_snd_3671_);
v___x_3784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3784_, 0, v_snd_3671_);
if (v_isShared_3674_ == 0)
{
v___x_3786_ = v___x_3673_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3793_; 
v_reuseFailAlloc_3793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3793_, 0, v_fst_3670_);
lean_ctor_set(v_reuseFailAlloc_3793_, 1, v_snd_3671_);
v___x_3786_ = v_reuseFailAlloc_3793_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
lean_object* v___x_3788_; 
if (v_isShared_3665_ == 0)
{
lean_ctor_set(v___x_3664_, 1, v___x_3786_);
lean_ctor_set(v___x_3664_, 0, v___x_3784_);
v___x_3788_ = v___x_3664_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3792_; 
v_reuseFailAlloc_3792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3792_, 0, v___x_3784_);
lean_ctor_set(v_reuseFailAlloc_3792_, 1, v___x_3786_);
v___x_3788_ = v_reuseFailAlloc_3792_;
goto v_reusejp_3787_;
}
v_reusejp_3787_:
{
lean_object* v___x_3790_; 
if (v_isShared_3669_ == 0)
{
lean_ctor_set(v___x_3668_, 0, v___x_3788_);
v___x_3790_ = v___x_3668_;
goto v_reusejp_3789_;
}
else
{
lean_object* v_reuseFailAlloc_3791_; 
v_reuseFailAlloc_3791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3791_, 0, v___x_3788_);
v___x_3790_ = v_reuseFailAlloc_3791_;
goto v_reusejp_3789_;
}
v_reusejp_3789_:
{
return v___x_3790_;
}
}
}
}
}
else
{
lean_object* v___x_3794_; lean_object* v___x_3796_; 
lean_dec_ref(v_cfg_3646_);
lean_inc(v_snd_3671_);
v___x_3794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3794_, 0, v_snd_3671_);
if (v_isShared_3674_ == 0)
{
v___x_3796_ = v___x_3673_;
goto v_reusejp_3795_;
}
else
{
lean_object* v_reuseFailAlloc_3803_; 
v_reuseFailAlloc_3803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3803_, 0, v_fst_3670_);
lean_ctor_set(v_reuseFailAlloc_3803_, 1, v_snd_3671_);
v___x_3796_ = v_reuseFailAlloc_3803_;
goto v_reusejp_3795_;
}
v_reusejp_3795_:
{
lean_object* v___x_3798_; 
if (v_isShared_3665_ == 0)
{
lean_ctor_set(v___x_3664_, 1, v___x_3796_);
lean_ctor_set(v___x_3664_, 0, v___x_3794_);
v___x_3798_ = v___x_3664_;
goto v_reusejp_3797_;
}
else
{
lean_object* v_reuseFailAlloc_3802_; 
v_reuseFailAlloc_3802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3802_, 0, v___x_3794_);
lean_ctor_set(v_reuseFailAlloc_3802_, 1, v___x_3796_);
v___x_3798_ = v_reuseFailAlloc_3802_;
goto v_reusejp_3797_;
}
v_reusejp_3797_:
{
lean_object* v___x_3800_; 
if (v_isShared_3669_ == 0)
{
lean_ctor_set(v___x_3668_, 0, v___x_3798_);
v___x_3800_ = v___x_3668_;
goto v_reusejp_3799_;
}
else
{
lean_object* v_reuseFailAlloc_3801_; 
v_reuseFailAlloc_3801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3801_, 0, v___x_3798_);
v___x_3800_ = v_reuseFailAlloc_3801_;
goto v_reusejp_3799_;
}
v_reusejp_3799_:
{
return v___x_3800_;
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
lean_object* v_a_3808_; lean_object* v___x_3810_; uint8_t v_isShared_3811_; uint8_t v_isSharedCheck_3815_; 
lean_dec_ref(v_b_3648_);
lean_dec_ref(v_cfg_3646_);
v_a_3808_ = lean_ctor_get(v___x_3661_, 0);
v_isSharedCheck_3815_ = !lean_is_exclusive(v___x_3661_);
if (v_isSharedCheck_3815_ == 0)
{
v___x_3810_ = v___x_3661_;
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
else
{
lean_inc(v_a_3808_);
lean_dec(v___x_3661_);
v___x_3810_ = lean_box(0);
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
v_resetjp_3809_:
{
lean_object* v___x_3813_; 
if (v_isShared_3811_ == 0)
{
v___x_3813_ = v___x_3810_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v_a_3808_);
v___x_3813_ = v_reuseFailAlloc_3814_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
return v___x_3813_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg___boxed(lean_object* v_cfg_3816_, lean_object* v_as_x27_3817_, lean_object* v_b_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_){
_start:
{
lean_object* v_res_3824_; 
v_res_3824_ = l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg(v_cfg_3816_, v_as_x27_3817_, v_b_3818_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_);
lean_dec(v___y_3822_);
lean_dec_ref(v___y_3821_);
lean_dec(v___y_3820_);
lean_dec_ref(v___y_3819_);
lean_dec(v_as_x27_3817_);
return v_res_3824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_takeListAux(lean_object* v_cfg_3825_, lean_object* v_seen_3826_, lean_object* v_acc_3827_, lean_object* v_xs_3828_, lean_object* v_a_3829_, lean_object* v_a_3830_, lean_object* v_a_3831_, lean_object* v_a_3832_){
_start:
{
lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; 
v___x_3834_ = lean_box(0);
v___x_3835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3835_, 0, v_seen_3826_);
lean_ctor_set(v___x_3835_, 1, v_acc_3827_);
v___x_3836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3836_, 0, v___x_3834_);
lean_ctor_set(v___x_3836_, 1, v___x_3835_);
v___x_3837_ = l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg(v_cfg_3825_, v_xs_3828_, v___x_3836_, v_a_3829_, v_a_3830_, v_a_3831_, v_a_3832_);
if (lean_obj_tag(v___x_3837_) == 0)
{
lean_object* v_a_3838_; lean_object* v___x_3840_; uint8_t v_isShared_3841_; uint8_t v_isSharedCheck_3852_; 
v_a_3838_ = lean_ctor_get(v___x_3837_, 0);
v_isSharedCheck_3852_ = !lean_is_exclusive(v___x_3837_);
if (v_isSharedCheck_3852_ == 0)
{
v___x_3840_ = v___x_3837_;
v_isShared_3841_ = v_isSharedCheck_3852_;
goto v_resetjp_3839_;
}
else
{
lean_inc(v_a_3838_);
lean_dec(v___x_3837_);
v___x_3840_ = lean_box(0);
v_isShared_3841_ = v_isSharedCheck_3852_;
goto v_resetjp_3839_;
}
v_resetjp_3839_:
{
lean_object* v_fst_3842_; 
v_fst_3842_ = lean_ctor_get(v_a_3838_, 0);
if (lean_obj_tag(v_fst_3842_) == 0)
{
lean_object* v_snd_3843_; lean_object* v_snd_3844_; lean_object* v___x_3846_; 
v_snd_3843_ = lean_ctor_get(v_a_3838_, 1);
lean_inc(v_snd_3843_);
lean_dec(v_a_3838_);
v_snd_3844_ = lean_ctor_get(v_snd_3843_, 1);
lean_inc(v_snd_3844_);
lean_dec(v_snd_3843_);
if (v_isShared_3841_ == 0)
{
lean_ctor_set(v___x_3840_, 0, v_snd_3844_);
v___x_3846_ = v___x_3840_;
goto v_reusejp_3845_;
}
else
{
lean_object* v_reuseFailAlloc_3847_; 
v_reuseFailAlloc_3847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3847_, 0, v_snd_3844_);
v___x_3846_ = v_reuseFailAlloc_3847_;
goto v_reusejp_3845_;
}
v_reusejp_3845_:
{
return v___x_3846_;
}
}
else
{
lean_object* v_val_3848_; lean_object* v___x_3850_; 
lean_inc_ref(v_fst_3842_);
lean_dec(v_a_3838_);
v_val_3848_ = lean_ctor_get(v_fst_3842_, 0);
lean_inc(v_val_3848_);
lean_dec_ref_known(v_fst_3842_, 1);
if (v_isShared_3841_ == 0)
{
lean_ctor_set(v___x_3840_, 0, v_val_3848_);
v___x_3850_ = v___x_3840_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v_val_3848_);
v___x_3850_ = v_reuseFailAlloc_3851_;
goto v_reusejp_3849_;
}
v_reusejp_3849_:
{
return v___x_3850_;
}
}
}
}
else
{
lean_object* v_a_3853_; lean_object* v___x_3855_; uint8_t v_isShared_3856_; uint8_t v_isSharedCheck_3860_; 
v_a_3853_ = lean_ctor_get(v___x_3837_, 0);
v_isSharedCheck_3860_ = !lean_is_exclusive(v___x_3837_);
if (v_isSharedCheck_3860_ == 0)
{
v___x_3855_ = v___x_3837_;
v_isShared_3856_ = v_isSharedCheck_3860_;
goto v_resetjp_3854_;
}
else
{
lean_inc(v_a_3853_);
lean_dec(v___x_3837_);
v___x_3855_ = lean_box(0);
v_isShared_3856_ = v_isSharedCheck_3860_;
goto v_resetjp_3854_;
}
v_resetjp_3854_:
{
lean_object* v___x_3858_; 
if (v_isShared_3856_ == 0)
{
v___x_3858_ = v___x_3855_;
goto v_reusejp_3857_;
}
else
{
lean_object* v_reuseFailAlloc_3859_; 
v_reuseFailAlloc_3859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3859_, 0, v_a_3853_);
v___x_3858_ = v_reuseFailAlloc_3859_;
goto v_reusejp_3857_;
}
v_reusejp_3857_:
{
return v___x_3858_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_takeListAux___boxed(lean_object* v_cfg_3861_, lean_object* v_seen_3862_, lean_object* v_acc_3863_, lean_object* v_xs_3864_, lean_object* v_a_3865_, lean_object* v_a_3866_, lean_object* v_a_3867_, lean_object* v_a_3868_, lean_object* v_a_3869_){
_start:
{
lean_object* v_res_3870_; 
v_res_3870_ = l_Lean_Meta_Rewrites_takeListAux(v_cfg_3861_, v_seen_3862_, v_acc_3863_, v_xs_3864_, v_a_3865_, v_a_3866_, v_a_3867_, v_a_3868_);
lean_dec(v_a_3868_);
lean_dec_ref(v_a_3867_);
lean_dec(v_a_3866_);
lean_dec_ref(v_a_3865_);
lean_dec(v_xs_3864_);
return v_res_3870_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0(lean_object* v_00_u03b2_3871_, lean_object* v_m_3872_, lean_object* v_a_3873_){
_start:
{
uint8_t v___x_3874_; 
v___x_3874_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg(v_m_3872_, v_a_3873_);
return v___x_3874_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___boxed(lean_object* v_00_u03b2_3875_, lean_object* v_m_3876_, lean_object* v_a_3877_){
_start:
{
uint8_t v_res_3878_; lean_object* v_r_3879_; 
v_res_3878_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0(v_00_u03b2_3875_, v_m_3876_, v_a_3877_);
lean_dec_ref(v_a_3877_);
lean_dec_ref(v_m_3876_);
v_r_3879_ = lean_box(v_res_3878_);
return v_r_3879_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1(lean_object* v_00_u03b2_3880_, lean_object* v_m_3881_, lean_object* v_a_3882_, lean_object* v_b_3883_){
_start:
{
lean_object* v___x_3884_; 
v___x_3884_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1___redArg(v_m_3881_, v_a_3882_, v_b_3883_);
return v___x_3884_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2(lean_object* v_cfg_3885_, lean_object* v_as_3886_, lean_object* v_as_x27_3887_, lean_object* v_b_3888_, lean_object* v_a_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_){
_start:
{
lean_object* v___x_3895_; 
v___x_3895_ = l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg(v_cfg_3885_, v_as_x27_3887_, v_b_3888_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
return v___x_3895_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___boxed(lean_object* v_cfg_3896_, lean_object* v_as_3897_, lean_object* v_as_x27_3898_, lean_object* v_b_3899_, lean_object* v_a_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_){
_start:
{
lean_object* v_res_3906_; 
v_res_3906_ = l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2(v_cfg_3896_, v_as_3897_, v_as_x27_3898_, v_b_3899_, v_a_3900_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_);
lean_dec(v___y_3904_);
lean_dec_ref(v___y_3903_);
lean_dec(v___y_3902_);
lean_dec_ref(v___y_3901_);
lean_dec(v_as_x27_3898_);
lean_dec(v_as_3897_);
return v_res_3906_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0(lean_object* v_00_u03b2_3907_, lean_object* v_a_3908_, lean_object* v_x_3909_){
_start:
{
uint8_t v___x_3910_; 
v___x_3910_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(v_a_3908_, v_x_3909_);
return v___x_3910_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3911_, lean_object* v_a_3912_, lean_object* v_x_3913_){
_start:
{
uint8_t v_res_3914_; lean_object* v_r_3915_; 
v_res_3914_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0(v_00_u03b2_3911_, v_a_3912_, v_x_3913_);
lean_dec(v_x_3913_);
lean_dec_ref(v_a_3912_);
v_r_3915_ = lean_box(v_res_3914_);
return v_r_3915_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2(lean_object* v_00_u03b2_3916_, lean_object* v_data_3917_){
_start:
{
lean_object* v___x_3918_; 
v___x_3918_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2___redArg(v_data_3917_);
return v___x_3918_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3(lean_object* v_00_u03b2_3919_, lean_object* v_a_3920_, lean_object* v_b_3921_, lean_object* v_x_3922_){
_start:
{
lean_object* v___x_3923_; 
v___x_3923_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3___redArg(v_a_3920_, v_b_3921_, v_x_3922_);
return v___x_3923_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_3924_, lean_object* v_i_3925_, lean_object* v_source_3926_, lean_object* v_target_3927_){
_start:
{
lean_object* v___x_3928_; 
v___x_3928_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3___redArg(v_i_3925_, v_source_3926_, v_target_3927_);
return v___x_3928_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_3929_, lean_object* v_x_3930_, lean_object* v_x_3931_){
_start:
{
lean_object* v___x_3932_; 
v___x_3932_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3_spec__5___redArg(v_x_3930_, v_x_3931_);
return v___x_3932_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_findRewrites___closed__0(void){
_start:
{
lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; 
v___x_3933_ = lean_box(0);
v___x_3934_ = lean_unsigned_to_nat(16u);
v___x_3935_ = lean_mk_array(v___x_3934_, v___x_3933_);
return v___x_3935_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_findRewrites___closed__1(void){
_start:
{
lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; 
v___x_3936_ = lean_obj_once(&l_Lean_Meta_Rewrites_findRewrites___closed__0, &l_Lean_Meta_Rewrites_findRewrites___closed__0_once, _init_l_Lean_Meta_Rewrites_findRewrites___closed__0);
v___x_3937_ = lean_unsigned_to_nat(0u);
v___x_3938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3938_, 0, v___x_3937_);
lean_ctor_set(v___x_3938_, 1, v___x_3936_);
return v___x_3938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_findRewrites(lean_object* v_hyps_3939_, lean_object* v_moduleRef_3940_, lean_object* v_goal_3941_, lean_object* v_target_3942_, lean_object* v_forbidden_3943_, uint8_t v_side_3944_, uint8_t v_stopAtRfl_3945_, lean_object* v_max_3946_, lean_object* v_leavePercentHeartbeats_3947_, lean_object* v_a_3948_, lean_object* v_a_3949_, lean_object* v_a_3950_, lean_object* v_a_3951_){
_start:
{
lean_object* v___x_3953_; lean_object* v___x_3954_; 
v___x_3953_ = lean_st_ref_get(v_a_3949_);
lean_inc_ref(v_target_3942_);
v___x_3954_ = l_Lean_Meta_Rewrites_rewriteCandidates(v_hyps_3939_, v_moduleRef_3940_, v_target_3942_, v_forbidden_3943_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_);
if (lean_obj_tag(v___x_3954_) == 0)
{
lean_object* v_a_3955_; lean_object* v___x_3956_; 
v_a_3955_ = lean_ctor_get(v___x_3954_, 0);
lean_inc(v_a_3955_);
lean_dec_ref_known(v___x_3954_, 1);
v___x_3956_ = l_Lean_getMaxHeartbeats___redArg(v_a_3950_);
if (lean_obj_tag(v___x_3956_) == 0)
{
lean_object* v_a_3957_; lean_object* v_mctx_3958_; lean_object* v_minHeartbeats_3960_; lean_object* v___y_3961_; lean_object* v___y_3962_; lean_object* v___y_3963_; lean_object* v___y_3964_; lean_object* v___x_3987_; uint8_t v___x_3988_; 
v_a_3957_ = lean_ctor_get(v___x_3956_, 0);
lean_inc(v_a_3957_);
lean_dec_ref_known(v___x_3956_, 1);
v_mctx_3958_ = lean_ctor_get(v___x_3953_, 0);
lean_inc_ref(v_mctx_3958_);
lean_dec(v___x_3953_);
v___x_3987_ = lean_unsigned_to_nat(0u);
v___x_3988_ = lean_nat_dec_eq(v_a_3957_, v___x_3987_);
lean_dec(v_a_3957_);
if (v___x_3988_ == 0)
{
lean_object* v___x_3989_; 
v___x_3989_ = l_Lean_getRemainingHeartbeats___redArg(v_a_3950_);
if (lean_obj_tag(v___x_3989_) == 0)
{
lean_object* v_a_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; 
v_a_3990_ = lean_ctor_get(v___x_3989_, 0);
lean_inc(v_a_3990_);
lean_dec_ref_known(v___x_3989_, 1);
v___x_3991_ = lean_nat_mul(v_leavePercentHeartbeats_3947_, v_a_3990_);
lean_dec(v_a_3990_);
v___x_3992_ = lean_unsigned_to_nat(100u);
v___x_3993_ = lean_nat_div(v___x_3991_, v___x_3992_);
lean_dec(v___x_3991_);
v_minHeartbeats_3960_ = v___x_3993_;
v___y_3961_ = v_a_3948_;
v___y_3962_ = v_a_3949_;
v___y_3963_ = v_a_3950_;
v___y_3964_ = v_a_3951_;
goto v___jp_3959_;
}
else
{
lean_object* v_a_3994_; lean_object* v___x_3996_; uint8_t v_isShared_3997_; uint8_t v_isSharedCheck_4001_; 
lean_dec_ref(v_mctx_3958_);
lean_dec(v_a_3955_);
lean_dec(v_max_3946_);
lean_dec_ref(v_target_3942_);
lean_dec(v_goal_3941_);
v_a_3994_ = lean_ctor_get(v___x_3989_, 0);
v_isSharedCheck_4001_ = !lean_is_exclusive(v___x_3989_);
if (v_isSharedCheck_4001_ == 0)
{
v___x_3996_ = v___x_3989_;
v_isShared_3997_ = v_isSharedCheck_4001_;
goto v_resetjp_3995_;
}
else
{
lean_inc(v_a_3994_);
lean_dec(v___x_3989_);
v___x_3996_ = lean_box(0);
v_isShared_3997_ = v_isSharedCheck_4001_;
goto v_resetjp_3995_;
}
v_resetjp_3995_:
{
lean_object* v___x_3999_; 
if (v_isShared_3997_ == 0)
{
v___x_3999_ = v___x_3996_;
goto v_reusejp_3998_;
}
else
{
lean_object* v_reuseFailAlloc_4000_; 
v_reuseFailAlloc_4000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4000_, 0, v_a_3994_);
v___x_3999_ = v_reuseFailAlloc_4000_;
goto v_reusejp_3998_;
}
v_reusejp_3998_:
{
return v___x_3999_;
}
}
}
}
else
{
v_minHeartbeats_3960_ = v___x_3987_;
v___y_3961_ = v_a_3948_;
v___y_3962_ = v_a_3949_;
v___y_3963_ = v_a_3950_;
v___y_3964_ = v_a_3951_;
goto v___jp_3959_;
}
v___jp_3959_:
{
lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; 
lean_inc(v_max_3946_);
v___x_3965_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_3965_, 0, v_max_3946_);
lean_ctor_set(v___x_3965_, 1, v_minHeartbeats_3960_);
lean_ctor_set(v___x_3965_, 2, v_goal_3941_);
lean_ctor_set(v___x_3965_, 3, v_target_3942_);
lean_ctor_set(v___x_3965_, 4, v_mctx_3958_);
lean_ctor_set_uint8(v___x_3965_, sizeof(void*)*5, v_stopAtRfl_3945_);
lean_ctor_set_uint8(v___x_3965_, sizeof(void*)*5 + 1, v_side_3944_);
v___x_3966_ = lean_obj_once(&l_Lean_Meta_Rewrites_findRewrites___closed__1, &l_Lean_Meta_Rewrites_findRewrites___closed__1_once, _init_l_Lean_Meta_Rewrites_findRewrites___closed__1);
v___x_3967_ = lean_mk_empty_array_with_capacity(v_max_3946_);
lean_dec(v_max_3946_);
v___x_3968_ = lean_array_to_list(v_a_3955_);
v___x_3969_ = l_Lean_Meta_Rewrites_takeListAux(v___x_3965_, v___x_3966_, v___x_3967_, v___x_3968_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_);
lean_dec(v___x_3968_);
if (lean_obj_tag(v___x_3969_) == 0)
{
lean_object* v_a_3970_; lean_object* v___x_3972_; uint8_t v_isShared_3973_; uint8_t v_isSharedCheck_3978_; 
v_a_3970_ = lean_ctor_get(v___x_3969_, 0);
v_isSharedCheck_3978_ = !lean_is_exclusive(v___x_3969_);
if (v_isSharedCheck_3978_ == 0)
{
v___x_3972_ = v___x_3969_;
v_isShared_3973_ = v_isSharedCheck_3978_;
goto v_resetjp_3971_;
}
else
{
lean_inc(v_a_3970_);
lean_dec(v___x_3969_);
v___x_3972_ = lean_box(0);
v_isShared_3973_ = v_isSharedCheck_3978_;
goto v_resetjp_3971_;
}
v_resetjp_3971_:
{
lean_object* v___x_3974_; lean_object* v___x_3976_; 
v___x_3974_ = lean_array_to_list(v_a_3970_);
if (v_isShared_3973_ == 0)
{
lean_ctor_set(v___x_3972_, 0, v___x_3974_);
v___x_3976_ = v___x_3972_;
goto v_reusejp_3975_;
}
else
{
lean_object* v_reuseFailAlloc_3977_; 
v_reuseFailAlloc_3977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3977_, 0, v___x_3974_);
v___x_3976_ = v_reuseFailAlloc_3977_;
goto v_reusejp_3975_;
}
v_reusejp_3975_:
{
return v___x_3976_;
}
}
}
else
{
lean_object* v_a_3979_; lean_object* v___x_3981_; uint8_t v_isShared_3982_; uint8_t v_isSharedCheck_3986_; 
v_a_3979_ = lean_ctor_get(v___x_3969_, 0);
v_isSharedCheck_3986_ = !lean_is_exclusive(v___x_3969_);
if (v_isSharedCheck_3986_ == 0)
{
v___x_3981_ = v___x_3969_;
v_isShared_3982_ = v_isSharedCheck_3986_;
goto v_resetjp_3980_;
}
else
{
lean_inc(v_a_3979_);
lean_dec(v___x_3969_);
v___x_3981_ = lean_box(0);
v_isShared_3982_ = v_isSharedCheck_3986_;
goto v_resetjp_3980_;
}
v_resetjp_3980_:
{
lean_object* v___x_3984_; 
if (v_isShared_3982_ == 0)
{
v___x_3984_ = v___x_3981_;
goto v_reusejp_3983_;
}
else
{
lean_object* v_reuseFailAlloc_3985_; 
v_reuseFailAlloc_3985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3985_, 0, v_a_3979_);
v___x_3984_ = v_reuseFailAlloc_3985_;
goto v_reusejp_3983_;
}
v_reusejp_3983_:
{
return v___x_3984_;
}
}
}
}
}
else
{
lean_object* v_a_4002_; lean_object* v___x_4004_; uint8_t v_isShared_4005_; uint8_t v_isSharedCheck_4009_; 
lean_dec(v_a_3955_);
lean_dec(v___x_3953_);
lean_dec(v_max_3946_);
lean_dec_ref(v_target_3942_);
lean_dec(v_goal_3941_);
v_a_4002_ = lean_ctor_get(v___x_3956_, 0);
v_isSharedCheck_4009_ = !lean_is_exclusive(v___x_3956_);
if (v_isSharedCheck_4009_ == 0)
{
v___x_4004_ = v___x_3956_;
v_isShared_4005_ = v_isSharedCheck_4009_;
goto v_resetjp_4003_;
}
else
{
lean_inc(v_a_4002_);
lean_dec(v___x_3956_);
v___x_4004_ = lean_box(0);
v_isShared_4005_ = v_isSharedCheck_4009_;
goto v_resetjp_4003_;
}
v_resetjp_4003_:
{
lean_object* v___x_4007_; 
if (v_isShared_4005_ == 0)
{
v___x_4007_ = v___x_4004_;
goto v_reusejp_4006_;
}
else
{
lean_object* v_reuseFailAlloc_4008_; 
v_reuseFailAlloc_4008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4008_, 0, v_a_4002_);
v___x_4007_ = v_reuseFailAlloc_4008_;
goto v_reusejp_4006_;
}
v_reusejp_4006_:
{
return v___x_4007_;
}
}
}
}
else
{
lean_object* v_a_4010_; lean_object* v___x_4012_; uint8_t v_isShared_4013_; uint8_t v_isSharedCheck_4017_; 
lean_dec(v___x_3953_);
lean_dec(v_max_3946_);
lean_dec_ref(v_target_3942_);
lean_dec(v_goal_3941_);
v_a_4010_ = lean_ctor_get(v___x_3954_, 0);
v_isSharedCheck_4017_ = !lean_is_exclusive(v___x_3954_);
if (v_isSharedCheck_4017_ == 0)
{
v___x_4012_ = v___x_3954_;
v_isShared_4013_ = v_isSharedCheck_4017_;
goto v_resetjp_4011_;
}
else
{
lean_inc(v_a_4010_);
lean_dec(v___x_3954_);
v___x_4012_ = lean_box(0);
v_isShared_4013_ = v_isSharedCheck_4017_;
goto v_resetjp_4011_;
}
v_resetjp_4011_:
{
lean_object* v___x_4015_; 
if (v_isShared_4013_ == 0)
{
v___x_4015_ = v___x_4012_;
goto v_reusejp_4014_;
}
else
{
lean_object* v_reuseFailAlloc_4016_; 
v_reuseFailAlloc_4016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4016_, 0, v_a_4010_);
v___x_4015_ = v_reuseFailAlloc_4016_;
goto v_reusejp_4014_;
}
v_reusejp_4014_:
{
return v___x_4015_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_findRewrites___boxed(lean_object* v_hyps_4018_, lean_object* v_moduleRef_4019_, lean_object* v_goal_4020_, lean_object* v_target_4021_, lean_object* v_forbidden_4022_, lean_object* v_side_4023_, lean_object* v_stopAtRfl_4024_, lean_object* v_max_4025_, lean_object* v_leavePercentHeartbeats_4026_, lean_object* v_a_4027_, lean_object* v_a_4028_, lean_object* v_a_4029_, lean_object* v_a_4030_, lean_object* v_a_4031_){
_start:
{
uint8_t v_side_boxed_4032_; uint8_t v_stopAtRfl_boxed_4033_; lean_object* v_res_4034_; 
v_side_boxed_4032_ = lean_unbox(v_side_4023_);
v_stopAtRfl_boxed_4033_ = lean_unbox(v_stopAtRfl_4024_);
v_res_4034_ = l_Lean_Meta_Rewrites_findRewrites(v_hyps_4018_, v_moduleRef_4019_, v_goal_4020_, v_target_4021_, v_forbidden_4022_, v_side_boxed_4032_, v_stopAtRfl_boxed_4033_, v_max_4025_, v_leavePercentHeartbeats_4026_, v_a_4027_, v_a_4028_, v_a_4029_, v_a_4030_);
lean_dec(v_a_4030_);
lean_dec_ref(v_a_4029_);
lean_dec(v_a_4028_);
lean_dec_ref(v_a_4027_);
lean_dec(v_leavePercentHeartbeats_4026_);
lean_dec(v_forbidden_4022_);
return v_res_4034_;
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

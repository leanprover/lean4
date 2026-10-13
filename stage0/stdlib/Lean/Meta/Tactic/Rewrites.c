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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
lean_object* lean_obj_tag_nat(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_ctorIdx___impl___boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "injEq"};
static const lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "sizeOf_spec"};
static const lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_inj"};
static const lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__3_value;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_ctorIdx___impl(uint8_t v_x_122_){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_123_ = lean_box(v_x_122_);
v___x_124_ = lean_obj_tag_nat(v___x_123_);
lean_dec(v___x_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_ctorIdx___impl___boxed(lean_object* v_x_125_){
_start:
{
uint8_t v_x_4__boxed_126_; lean_object* v_res_127_; 
v_x_4__boxed_126_ = lean_unbox(v_x_125_);
v_res_127_ = l_Lean_Meta_Rewrites_RwDirection_ctorIdx___impl(v_x_4__boxed_126_);
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
uint8_t v___x_4850__boxed_490_; uint8_t v___x_4852__boxed_491_; lean_object* v_res_492_; 
v___x_4850__boxed_490_ = lean_unbox(v___x_481_);
v___x_4852__boxed_491_ = lean_unbox(v___x_484_);
v_res_492_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__1(v___x_4850__boxed_490_, v_type_482_, v___f_483_, v___x_4852__boxed_491_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec(v___y_486_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport(lean_object* v_name_497_, lean_object* v_c_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_){
_start:
{
uint8_t v___x_504_; 
lean_inc_ref(v_c_498_);
v___x_504_ = l_Lean_AsyncConstantInfo_isUnsafe(v_c_498_);
if (v___x_504_ == 0)
{
lean_object* v___f_505_; lean_object* v___y_507_; lean_object* v___y_508_; lean_object* v___y_509_; lean_object* v___y_510_; lean_object* v___x_521_; lean_object* v_env_525_; uint8_t v___x_526_; 
lean_inc_n(v_name_497_, 2);
v___f_505_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___boxed), 8, 1);
lean_closure_set(v___f_505_, 0, v_name_497_);
v___x_521_ = lean_st_ref_get(v_a_502_);
v_env_525_ = lean_ctor_get(v___x_521_, 0);
lean_inc_ref(v_env_525_);
lean_dec(v___x_521_);
v___x_526_ = l_Lean_Meta_allowCompletion(v_env_525_, v_name_497_);
if (v___x_526_ == 0)
{
lean_dec_ref(v___f_505_);
lean_dec_ref(v_c_498_);
lean_dec(v_name_497_);
goto v___jp_522_;
}
else
{
if (v___x_504_ == 0)
{
lean_object* v___x_527_; lean_object* v_env_531_; uint8_t v___x_532_; 
v___x_527_ = lean_st_ref_get(v_a_502_);
v_env_531_ = lean_ctor_get(v___x_527_, 0);
lean_inc_ref(v_env_531_);
lean_dec(v___x_527_);
lean_inc(v_name_497_);
v___x_532_ = l_Lean_Linter_isDeprecated(v_env_531_, v_name_497_);
if (v___x_532_ == 0)
{
if (lean_obj_tag(v_name_497_) == 1)
{
lean_object* v_str_533_; lean_object* v___x_542_; uint8_t v___x_543_; 
v_str_533_ = lean_ctor_get(v_name_497_, 1);
v___x_542_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__1));
v___x_543_ = lean_string_dec_eq(v_str_533_, v___x_542_);
if (v___x_543_ == 0)
{
lean_object* v___x_544_; uint8_t v___x_545_; 
v___x_544_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__2));
v___x_545_ = lean_string_dec_eq(v_str_533_, v___x_544_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; lean_object* v___x_547_; uint8_t v___x_548_; 
v___x_546_ = lean_string_utf8_byte_size(v_str_533_);
v___x_547_ = lean_unsigned_to_nat(4u);
v___x_548_ = lean_nat_dec_le(v___x_547_, v___x_546_);
if (v___x_548_ == 0)
{
goto v___jp_534_;
}
else
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; uint8_t v___x_552_; 
v___x_549_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__3));
v___x_550_ = lean_unsigned_to_nat(0u);
v___x_551_ = lean_nat_sub(v___x_546_, v___x_547_);
v___x_552_ = lean_string_memcmp(v_str_533_, v___x_549_, v___x_551_, v___x_550_, v___x_547_);
lean_dec(v___x_551_);
if (v___x_552_ == 0)
{
goto v___jp_534_;
}
else
{
lean_dec_ref_known(v_name_497_, 2);
lean_dec_ref(v___f_505_);
lean_dec_ref(v_c_498_);
goto v___jp_528_;
}
}
}
else
{
lean_dec_ref_known(v_name_497_, 2);
lean_dec_ref(v___f_505_);
lean_dec_ref(v_c_498_);
goto v___jp_528_;
}
}
else
{
lean_dec_ref_known(v_name_497_, 2);
lean_dec_ref(v___f_505_);
lean_dec_ref(v_c_498_);
goto v___jp_528_;
}
v___jp_534_:
{
lean_object* v___x_535_; lean_object* v___x_536_; uint8_t v___x_537_; 
v___x_535_ = lean_string_utf8_byte_size(v_str_533_);
v___x_536_ = lean_unsigned_to_nat(5u);
v___x_537_ = lean_nat_dec_le(v___x_536_, v___x_535_);
if (v___x_537_ == 0)
{
v___y_507_ = v_a_499_;
v___y_508_ = v_a_500_;
v___y_509_ = v_a_501_;
v___y_510_ = v_a_502_;
goto v___jp_506_;
}
else
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; uint8_t v___x_541_; 
v___x_538_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__0));
v___x_539_ = lean_unsigned_to_nat(0u);
v___x_540_ = lean_nat_sub(v___x_535_, v___x_536_);
v___x_541_ = lean_string_memcmp(v_str_533_, v___x_538_, v___x_540_, v___x_539_, v___x_536_);
lean_dec(v___x_540_);
if (v___x_541_ == 0)
{
v___y_507_ = v_a_499_;
v___y_508_ = v_a_500_;
v___y_509_ = v_a_501_;
v___y_510_ = v_a_502_;
goto v___jp_506_;
}
else
{
lean_dec_ref_known(v_name_497_, 2);
lean_dec_ref(v___f_505_);
lean_dec_ref(v_c_498_);
goto v___jp_528_;
}
}
}
}
else
{
v___y_507_ = v_a_499_;
v___y_508_ = v_a_500_;
v___y_509_ = v_a_501_;
v___y_510_ = v_a_502_;
goto v___jp_506_;
}
}
else
{
lean_object* v___x_553_; lean_object* v___x_554_; 
lean_dec_ref(v___f_505_);
lean_dec_ref(v_c_498_);
lean_dec(v_name_497_);
v___x_553_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0));
v___x_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_554_, 0, v___x_553_);
return v___x_554_;
}
v___jp_528_:
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0));
v___x_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
return v___x_530_;
}
}
else
{
lean_dec_ref(v___f_505_);
lean_dec_ref(v_c_498_);
lean_dec(v_name_497_);
goto v___jp_522_;
}
}
v___jp_506_:
{
uint8_t v___x_511_; 
v___x_511_ = l_Lean_Name_isMetaprogramming(v_name_497_);
if (v___x_511_ == 0)
{
lean_object* v___x_512_; lean_object* v_type_513_; uint8_t v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___f_517_; lean_object* v___x_518_; 
v___x_512_ = l_Lean_AsyncConstantInfo_toConstantVal(v_c_498_);
v_type_513_ = lean_ctor_get(v___x_512_, 2);
lean_inc_ref(v_type_513_);
lean_dec_ref(v___x_512_);
v___x_514_ = 2;
v___x_515_ = lean_box(v___x_514_);
v___x_516_ = lean_box(v___x_511_);
v___f_517_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__1___boxed), 9, 4);
lean_closure_set(v___f_517_, 0, v___x_515_);
lean_closure_set(v___f_517_, 1, v_type_513_);
lean_closure_set(v___f_517_, 2, v___f_505_);
lean_closure_set(v___f_517_, 3, v___x_516_);
v___x_518_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1___redArg(v___f_517_, v___x_511_, v___y_507_, v___y_508_, v___y_509_, v___y_510_);
return v___x_518_;
}
else
{
lean_object* v___x_519_; lean_object* v___x_520_; 
lean_dec_ref(v___f_505_);
lean_dec_ref(v_c_498_);
v___x_519_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0));
v___x_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
return v___x_520_;
}
}
v___jp_522_:
{
lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_523_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0));
v___x_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_524_, 0, v___x_523_);
return v___x_524_;
}
}
else
{
lean_object* v___x_555_; lean_object* v___x_556_; 
lean_dec_ref(v_c_498_);
lean_dec(v_name_497_);
v___x_555_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0));
v___x_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
return v___x_556_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___boxed(lean_object* v_name_557_, lean_object* v_c_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport(v_name_557_, v_c_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_);
lean_dec(v_a_562_);
lean_dec_ref(v_a_561_);
lean_dec(v_a_560_);
lean_dec_ref(v_a_559_);
return v_res_564_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_Rewrites_localHypotheses_spec__0(lean_object* v_a_565_, lean_object* v_x_566_){
_start:
{
if (lean_obj_tag(v_x_566_) == 0)
{
uint8_t v___x_567_; 
v___x_567_ = 0;
return v___x_567_;
}
else
{
lean_object* v_head_568_; lean_object* v_tail_569_; uint8_t v___x_570_; 
v_head_568_ = lean_ctor_get(v_x_566_, 0);
v_tail_569_ = lean_ctor_get(v_x_566_, 1);
v___x_570_ = l_Lean_instBEqFVarId_beq(v_a_565_, v_head_568_);
if (v___x_570_ == 0)
{
v_x_566_ = v_tail_569_;
goto _start;
}
else
{
return v___x_570_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_Rewrites_localHypotheses_spec__0___boxed(lean_object* v_a_572_, lean_object* v_x_573_){
_start:
{
uint8_t v_res_574_; lean_object* v_r_575_; 
v_res_574_ = l_List_elem___at___00Lean_Meta_Rewrites_localHypotheses_spec__0(v_a_572_, v_x_573_);
lean_dec(v_x_573_);
lean_dec(v_a_572_);
v_r_575_ = lean_box(v_res_574_);
return v_r_575_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_localHypotheses_spec__2(lean_object* v_except_576_, lean_object* v_as_577_, size_t v_sz_578_, size_t v_i_579_, lean_object* v_b_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_){
_start:
{
lean_object* v_a_587_; uint8_t v___x_591_; 
v___x_591_ = lean_usize_dec_lt(v_i_579_, v_sz_578_);
if (v___x_591_ == 0)
{
lean_object* v___x_592_; 
v___x_592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_592_, 0, v_b_580_);
return v___x_592_;
}
else
{
lean_object* v_a_593_; lean_object* v___x_594_; uint8_t v___x_595_; 
v_a_593_ = lean_array_uget_borrowed(v_as_577_, v_i_579_);
v___x_594_ = l_Lean_Expr_fvarId_x21(v_a_593_);
v___x_595_ = l_List_elem___at___00Lean_Meta_Rewrites_localHypotheses_spec__0(v___x_594_, v_except_576_);
lean_dec(v___x_594_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; 
lean_inc(v___y_584_);
lean_inc_ref(v___y_583_);
lean_inc(v___y_582_);
lean_inc_ref(v___y_581_);
lean_inc(v_a_593_);
v___x_596_ = lean_infer_type(v_a_593_, v___y_581_, v___y_582_, v___y_583_, v___y_584_);
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v_a_597_; lean_object* v___x_598_; uint8_t v___x_599_; lean_object* v___x_600_; 
v_a_597_ = lean_ctor_get(v___x_596_, 0);
lean_inc(v_a_597_);
lean_dec_ref_known(v___x_596_, 1);
v___x_598_ = lean_box(0);
v___x_599_ = 0;
v___x_600_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_597_, v___x_598_, v___x_599_, v___y_581_, v___y_582_, v___y_583_, v___y_584_);
if (lean_obj_tag(v___x_600_) == 0)
{
lean_object* v_a_601_; lean_object* v_snd_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_673_; 
v_a_601_ = lean_ctor_get(v___x_600_, 0);
lean_inc(v_a_601_);
lean_dec_ref_known(v___x_600_, 1);
v_snd_602_ = lean_ctor_get(v_a_601_, 1);
v_isSharedCheck_673_ = !lean_is_exclusive(v_a_601_);
if (v_isSharedCheck_673_ == 0)
{
lean_object* v_unused_674_; 
v_unused_674_ = lean_ctor_get(v_a_601_, 0);
lean_dec(v_unused_674_);
v___x_604_ = v_a_601_;
v_isShared_605_ = v_isSharedCheck_673_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_snd_602_);
lean_dec(v_a_601_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_673_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v_snd_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_671_; 
v_snd_606_ = lean_ctor_get(v_snd_602_, 1);
v_isSharedCheck_671_ = !lean_is_exclusive(v_snd_602_);
if (v_isSharedCheck_671_ == 0)
{
lean_object* v_unused_672_; 
v_unused_672_ = lean_ctor_get(v_snd_602_, 0);
lean_dec(v_unused_672_);
v___x_608_ = v_snd_602_;
v_isShared_609_ = v_isSharedCheck_671_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_snd_606_);
lean_dec(v_snd_602_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_671_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_610_; 
v___x_610_ = l_Lean_Meta_whnfR(v_snd_606_, v___y_581_, v___y_582_, v___y_583_, v___y_584_);
if (lean_obj_tag(v___x_610_) == 0)
{
lean_object* v_a_611_; lean_object* v___x_612_; lean_object* v_fst_613_; 
v_a_611_ = lean_ctor_get(v___x_610_, 0);
lean_inc(v_a_611_);
lean_dec_ref_known(v___x_610_, 1);
v___x_612_ = l_Lean_Expr_getAppFnArgs(v_a_611_);
v_fst_613_ = lean_ctor_get(v___x_612_, 0);
lean_inc(v_fst_613_);
if (lean_obj_tag(v_fst_613_) == 1)
{
lean_object* v_pre_614_; 
v_pre_614_ = lean_ctor_get(v_fst_613_, 0);
if (lean_obj_tag(v_pre_614_) == 0)
{
lean_object* v_snd_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_661_; 
v_snd_615_ = lean_ctor_get(v___x_612_, 1);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_661_ == 0)
{
lean_object* v_unused_662_; 
v_unused_662_ = lean_ctor_get(v___x_612_, 0);
lean_dec(v_unused_662_);
v___x_617_ = v___x_612_;
v_isShared_618_ = v_isSharedCheck_661_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_snd_615_);
lean_dec(v___x_612_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_661_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v_str_619_; lean_object* v___x_620_; uint8_t v___x_621_; 
v_str_619_ = lean_ctor_get(v_fst_613_, 1);
lean_inc_ref(v_str_619_);
lean_dec_ref_known(v_fst_613_, 2);
v___x_620_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__1));
v___x_621_ = lean_string_dec_eq(v_str_619_, v___x_620_);
if (v___x_621_ == 0)
{
lean_object* v___x_622_; uint8_t v___x_623_; 
v___x_622_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__2));
v___x_623_ = lean_string_dec_eq(v_str_619_, v___x_622_);
lean_dec_ref(v_str_619_);
if (v___x_623_ == 0)
{
lean_del_object(v___x_617_);
lean_dec(v_snd_615_);
lean_del_object(v___x_608_);
lean_del_object(v___x_604_);
v_a_587_ = v_b_580_;
goto v___jp_586_;
}
else
{
lean_object* v___x_624_; lean_object* v___x_625_; uint8_t v___x_626_; 
v___x_624_ = lean_array_get_size(v_snd_615_);
lean_dec(v_snd_615_);
v___x_625_ = lean_unsigned_to_nat(2u);
v___x_626_ = lean_nat_dec_eq(v___x_624_, v___x_625_);
if (v___x_626_ == 0)
{
lean_del_object(v___x_617_);
lean_del_object(v___x_608_);
lean_del_object(v___x_604_);
v_a_587_ = v_b_580_;
goto v___jp_586_;
}
else
{
lean_object* v___x_627_; lean_object* v___x_629_; 
v___x_627_ = lean_box(v___x_595_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 1, v___x_625_);
lean_ctor_set(v___x_617_, 0, v___x_627_);
v___x_629_ = v___x_617_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v___x_627_);
lean_ctor_set(v_reuseFailAlloc_641_, 1, v___x_625_);
v___x_629_ = v_reuseFailAlloc_641_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
lean_object* v___x_631_; 
lean_inc(v_a_593_);
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 1, v___x_629_);
lean_ctor_set(v___x_608_, 0, v_a_593_);
v___x_631_ = v___x_608_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_a_593_);
lean_ctor_set(v_reuseFailAlloc_640_, 1, v___x_629_);
v___x_631_ = v_reuseFailAlloc_640_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_636_; 
v___x_632_ = lean_array_push(v_b_580_, v___x_631_);
v___x_633_ = lean_unsigned_to_nat(1u);
v___x_634_ = lean_box(v___x_591_);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 1, v___x_633_);
lean_ctor_set(v___x_604_, 0, v___x_634_);
v___x_636_ = v___x_604_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v___x_634_);
lean_ctor_set(v_reuseFailAlloc_639_, 1, v___x_633_);
v___x_636_ = v_reuseFailAlloc_639_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
lean_object* v___x_637_; lean_object* v___x_638_; 
lean_inc(v_a_593_);
v___x_637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_637_, 0, v_a_593_);
lean_ctor_set(v___x_637_, 1, v___x_636_);
v___x_638_ = lean_array_push(v___x_632_, v___x_637_);
v_a_587_ = v___x_638_;
goto v___jp_586_;
}
}
}
}
}
}
else
{
lean_object* v___x_642_; lean_object* v___x_643_; uint8_t v___x_644_; 
lean_dec_ref(v_str_619_);
v___x_642_ = lean_array_get_size(v_snd_615_);
lean_dec(v_snd_615_);
v___x_643_ = lean_unsigned_to_nat(3u);
v___x_644_ = lean_nat_dec_eq(v___x_642_, v___x_643_);
if (v___x_644_ == 0)
{
lean_del_object(v___x_617_);
lean_del_object(v___x_608_);
lean_del_object(v___x_604_);
v_a_587_ = v_b_580_;
goto v___jp_586_;
}
else
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_648_; 
v___x_645_ = lean_unsigned_to_nat(2u);
v___x_646_ = lean_box(v___x_595_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 1, v___x_645_);
lean_ctor_set(v___x_617_, 0, v___x_646_);
v___x_648_ = v___x_617_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v___x_646_);
lean_ctor_set(v_reuseFailAlloc_660_, 1, v___x_645_);
v___x_648_ = v_reuseFailAlloc_660_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
lean_object* v___x_650_; 
lean_inc(v_a_593_);
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 1, v___x_648_);
lean_ctor_set(v___x_608_, 0, v_a_593_);
v___x_650_ = v___x_608_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_a_593_);
lean_ctor_set(v_reuseFailAlloc_659_, 1, v___x_648_);
v___x_650_ = v_reuseFailAlloc_659_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_655_; 
v___x_651_ = lean_array_push(v_b_580_, v___x_650_);
v___x_652_ = lean_unsigned_to_nat(1u);
v___x_653_ = lean_box(v___x_591_);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 1, v___x_652_);
lean_ctor_set(v___x_604_, 0, v___x_653_);
v___x_655_ = v___x_604_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v___x_653_);
lean_ctor_set(v_reuseFailAlloc_658_, 1, v___x_652_);
v___x_655_ = v_reuseFailAlloc_658_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
lean_object* v___x_656_; lean_object* v___x_657_; 
lean_inc(v_a_593_);
v___x_656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_656_, 0, v_a_593_);
lean_ctor_set(v___x_656_, 1, v___x_655_);
v___x_657_ = lean_array_push(v___x_651_, v___x_656_);
v_a_587_ = v___x_657_;
goto v___jp_586_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_fst_613_, 2);
lean_dec_ref(v___x_612_);
lean_del_object(v___x_608_);
lean_del_object(v___x_604_);
v_a_587_ = v_b_580_;
goto v___jp_586_;
}
}
else
{
lean_dec(v_fst_613_);
lean_dec_ref(v___x_612_);
lean_del_object(v___x_608_);
lean_del_object(v___x_604_);
v_a_587_ = v_b_580_;
goto v___jp_586_;
}
}
else
{
lean_object* v_a_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_670_; 
lean_del_object(v___x_608_);
lean_del_object(v___x_604_);
lean_dec_ref(v_b_580_);
v_a_663_ = lean_ctor_get(v___x_610_, 0);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_670_ == 0)
{
v___x_665_ = v___x_610_;
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_a_663_);
lean_dec(v___x_610_);
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
}
}
else
{
lean_object* v_a_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_682_; 
lean_dec_ref(v_b_580_);
v_a_675_ = lean_ctor_get(v___x_600_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_682_ == 0)
{
v___x_677_ = v___x_600_;
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_a_675_);
lean_dec(v___x_600_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_680_; 
if (v_isShared_678_ == 0)
{
v___x_680_ = v___x_677_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_a_675_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
}
else
{
lean_object* v_a_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_690_; 
lean_dec_ref(v_b_580_);
v_a_683_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_690_ == 0)
{
v___x_685_ = v___x_596_;
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_a_683_);
lean_dec(v___x_596_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_688_; 
if (v_isShared_686_ == 0)
{
v___x_688_ = v___x_685_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_a_683_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
}
}
else
{
v_a_587_ = v_b_580_;
goto v___jp_586_;
}
}
v___jp_586_:
{
size_t v___x_588_; size_t v___x_589_; 
v___x_588_ = ((size_t)1ULL);
v___x_589_ = lean_usize_add(v_i_579_, v___x_588_);
v_i_579_ = v___x_589_;
v_b_580_ = v_a_587_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_localHypotheses_spec__2___boxed(lean_object* v_except_691_, lean_object* v_as_692_, lean_object* v_sz_693_, lean_object* v_i_694_, lean_object* v_b_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
size_t v_sz_boxed_701_; size_t v_i_boxed_702_; lean_object* v_res_703_; 
v_sz_boxed_701_ = lean_unbox_usize(v_sz_693_);
lean_dec(v_sz_693_);
v_i_boxed_702_ = lean_unbox_usize(v_i_694_);
lean_dec(v_i_694_);
v_res_703_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_localHypotheses_spec__2(v_except_691_, v_as_692_, v_sz_boxed_701_, v_i_boxed_702_, v_b_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec_ref(v_as_692_);
lean_dec(v_except_691_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(lean_object* v_as_704_, size_t v_sz_705_, size_t v_i_706_, lean_object* v_b_707_){
_start:
{
uint8_t v___x_709_; 
v___x_709_ = lean_usize_dec_lt(v_i_706_, v_sz_705_);
if (v___x_709_ == 0)
{
lean_object* v___x_710_; 
v___x_710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_710_, 0, v_b_707_);
return v___x_710_;
}
else
{
lean_object* v_snd_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_729_; 
v_snd_711_ = lean_ctor_get(v_b_707_, 1);
v_isSharedCheck_729_ = !lean_is_exclusive(v_b_707_);
if (v_isSharedCheck_729_ == 0)
{
lean_object* v_unused_730_; 
v_unused_730_ = lean_ctor_get(v_b_707_, 0);
lean_dec(v_unused_730_);
v___x_713_ = v_b_707_;
v_isShared_714_ = v_isSharedCheck_729_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_snd_711_);
lean_dec(v_b_707_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_729_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_715_; lean_object* v_a_717_; lean_object* v_a_724_; 
v___x_715_ = lean_box(0);
v_a_724_ = lean_array_uget_borrowed(v_as_704_, v_i_706_);
if (lean_obj_tag(v_a_724_) == 0)
{
v_a_717_ = v_snd_711_;
goto v___jp_716_;
}
else
{
lean_object* v_val_725_; uint8_t v___x_726_; 
v_val_725_ = lean_ctor_get(v_a_724_, 0);
v___x_726_ = l_Lean_LocalDecl_isImplementationDetail(v_val_725_);
if (v___x_726_ == 0)
{
lean_object* v___x_727_; lean_object* v___x_728_; 
lean_inc(v_val_725_);
v___x_727_ = l_Lean_LocalDecl_toExpr(v_val_725_);
v___x_728_ = lean_array_push(v_snd_711_, v___x_727_);
v_a_717_ = v___x_728_;
goto v___jp_716_;
}
else
{
v_a_717_ = v_snd_711_;
goto v___jp_716_;
}
}
v___jp_716_:
{
lean_object* v___x_719_; 
if (v_isShared_714_ == 0)
{
lean_ctor_set(v___x_713_, 1, v_a_717_);
lean_ctor_set(v___x_713_, 0, v___x_715_);
v___x_719_ = v___x_713_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_715_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v_a_717_);
v___x_719_ = v_reuseFailAlloc_723_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
size_t v___x_720_; size_t v___x_721_; 
v___x_720_ = ((size_t)1ULL);
v___x_721_ = lean_usize_add(v_i_706_, v___x_720_);
v_i_706_ = v___x_721_;
v_b_707_ = v___x_719_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___redArg___boxed(lean_object* v_as_731_, lean_object* v_sz_732_, lean_object* v_i_733_, lean_object* v_b_734_, lean_object* v___y_735_){
_start:
{
size_t v_sz_boxed_736_; size_t v_i_boxed_737_; lean_object* v_res_738_; 
v_sz_boxed_736_ = lean_unbox_usize(v_sz_732_);
lean_dec(v_sz_732_);
v_i_boxed_737_ = lean_unbox_usize(v_i_733_);
lean_dec(v_i_733_);
v_res_738_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(v_as_731_, v_sz_boxed_736_, v_i_boxed_737_, v_b_734_);
lean_dec_ref(v_as_731_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5(lean_object* v_as_739_, size_t v_sz_740_, size_t v_i_741_, lean_object* v_b_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_){
_start:
{
uint8_t v___x_748_; 
v___x_748_ = lean_usize_dec_lt(v_i_741_, v_sz_740_);
if (v___x_748_ == 0)
{
lean_object* v___x_749_; 
v___x_749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_749_, 0, v_b_742_);
return v___x_749_;
}
else
{
lean_object* v_snd_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_768_; 
v_snd_750_ = lean_ctor_get(v_b_742_, 1);
v_isSharedCheck_768_ = !lean_is_exclusive(v_b_742_);
if (v_isSharedCheck_768_ == 0)
{
lean_object* v_unused_769_; 
v_unused_769_ = lean_ctor_get(v_b_742_, 0);
lean_dec(v_unused_769_);
v___x_752_ = v_b_742_;
v_isShared_753_ = v_isSharedCheck_768_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_snd_750_);
lean_dec(v_b_742_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_768_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_754_; lean_object* v_a_756_; lean_object* v_a_763_; 
v___x_754_ = lean_box(0);
v_a_763_ = lean_array_uget_borrowed(v_as_739_, v_i_741_);
if (lean_obj_tag(v_a_763_) == 0)
{
v_a_756_ = v_snd_750_;
goto v___jp_755_;
}
else
{
lean_object* v_val_764_; uint8_t v___x_765_; 
v_val_764_ = lean_ctor_get(v_a_763_, 0);
v___x_765_ = l_Lean_LocalDecl_isImplementationDetail(v_val_764_);
if (v___x_765_ == 0)
{
lean_object* v___x_766_; lean_object* v___x_767_; 
lean_inc(v_val_764_);
v___x_766_ = l_Lean_LocalDecl_toExpr(v_val_764_);
v___x_767_ = lean_array_push(v_snd_750_, v___x_766_);
v_a_756_ = v___x_767_;
goto v___jp_755_;
}
else
{
v_a_756_ = v_snd_750_;
goto v___jp_755_;
}
}
v___jp_755_:
{
lean_object* v___x_758_; 
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 1, v_a_756_);
lean_ctor_set(v___x_752_, 0, v___x_754_);
v___x_758_ = v___x_752_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v___x_754_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v_a_756_);
v___x_758_ = v_reuseFailAlloc_762_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
size_t v___x_759_; size_t v___x_760_; lean_object* v___x_761_; 
v___x_759_ = ((size_t)1ULL);
v___x_760_ = lean_usize_add(v_i_741_, v___x_759_);
v___x_761_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(v_as_739_, v_sz_740_, v___x_760_, v___x_758_);
return v___x_761_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5___boxed(lean_object* v_as_770_, lean_object* v_sz_771_, lean_object* v_i_772_, lean_object* v_b_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
size_t v_sz_boxed_779_; size_t v_i_boxed_780_; lean_object* v_res_781_; 
v_sz_boxed_779_ = lean_unbox_usize(v_sz_771_);
lean_dec(v_sz_771_);
v_i_boxed_780_ = lean_unbox_usize(v_i_772_);
lean_dec(v_i_772_);
v_res_781_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5(v_as_770_, v_sz_boxed_779_, v_i_boxed_780_, v_b_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_);
lean_dec(v___y_777_);
lean_dec_ref(v___y_776_);
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
lean_dec_ref(v_as_770_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2(lean_object* v_init_782_, lean_object* v_n_783_, lean_object* v_b_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
if (lean_obj_tag(v_n_783_) == 0)
{
lean_object* v_cs_790_; lean_object* v___x_791_; lean_object* v___x_792_; size_t v_sz_793_; size_t v___x_794_; lean_object* v___x_795_; 
v_cs_790_ = lean_ctor_get(v_n_783_, 0);
v___x_791_ = lean_box(0);
v___x_792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_792_, 0, v___x_791_);
lean_ctor_set(v___x_792_, 1, v_b_784_);
v_sz_793_ = lean_array_size(v_cs_790_);
v___x_794_ = ((size_t)0ULL);
v___x_795_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__4(v_init_782_, v_cs_790_, v_sz_793_, v___x_794_, v___x_792_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_810_; 
v_a_796_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_810_ == 0)
{
v___x_798_ = v___x_795_;
v_isShared_799_ = v_isSharedCheck_810_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_795_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_810_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v_fst_800_; 
v_fst_800_ = lean_ctor_get(v_a_796_, 0);
if (lean_obj_tag(v_fst_800_) == 0)
{
lean_object* v_snd_801_; lean_object* v___x_802_; lean_object* v___x_804_; 
v_snd_801_ = lean_ctor_get(v_a_796_, 1);
lean_inc(v_snd_801_);
lean_dec(v_a_796_);
v___x_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_802_, 0, v_snd_801_);
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 0, v___x_802_);
v___x_804_ = v___x_798_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_802_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
else
{
lean_object* v_val_806_; lean_object* v___x_808_; 
lean_inc_ref(v_fst_800_);
lean_dec(v_a_796_);
v_val_806_ = lean_ctor_get(v_fst_800_, 0);
lean_inc(v_val_806_);
lean_dec_ref_known(v_fst_800_, 1);
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 0, v_val_806_);
v___x_808_ = v___x_798_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_val_806_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
}
}
else
{
lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_818_; 
v_a_811_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_818_ == 0)
{
v___x_813_ = v___x_795_;
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___x_795_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_816_; 
if (v_isShared_814_ == 0)
{
v___x_816_ = v___x_813_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_a_811_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
}
else
{
lean_object* v_vs_819_; lean_object* v___x_820_; lean_object* v___x_821_; size_t v_sz_822_; size_t v___x_823_; lean_object* v___x_824_; 
v_vs_819_ = lean_ctor_get(v_n_783_, 0);
v___x_820_ = lean_box(0);
v___x_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_821_, 0, v___x_820_);
lean_ctor_set(v___x_821_, 1, v_b_784_);
v_sz_822_ = lean_array_size(v_vs_819_);
v___x_823_ = ((size_t)0ULL);
v___x_824_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5(v_vs_819_, v_sz_822_, v___x_823_, v___x_821_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
if (lean_obj_tag(v___x_824_) == 0)
{
lean_object* v_a_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_839_; 
v_a_825_ = lean_ctor_get(v___x_824_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_824_);
if (v_isSharedCheck_839_ == 0)
{
v___x_827_ = v___x_824_;
v_isShared_828_ = v_isSharedCheck_839_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_a_825_);
lean_dec(v___x_824_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_839_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v_fst_829_; 
v_fst_829_ = lean_ctor_get(v_a_825_, 0);
if (lean_obj_tag(v_fst_829_) == 0)
{
lean_object* v_snd_830_; lean_object* v___x_831_; lean_object* v___x_833_; 
v_snd_830_ = lean_ctor_get(v_a_825_, 1);
lean_inc(v_snd_830_);
lean_dec(v_a_825_);
v___x_831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_831_, 0, v_snd_830_);
if (v_isShared_828_ == 0)
{
lean_ctor_set(v___x_827_, 0, v___x_831_);
v___x_833_ = v___x_827_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v___x_831_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
else
{
lean_object* v_val_835_; lean_object* v___x_837_; 
lean_inc_ref(v_fst_829_);
lean_dec(v_a_825_);
v_val_835_ = lean_ctor_get(v_fst_829_, 0);
lean_inc(v_val_835_);
lean_dec_ref_known(v_fst_829_, 1);
if (v_isShared_828_ == 0)
{
lean_ctor_set(v___x_827_, 0, v_val_835_);
v___x_837_ = v___x_827_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_val_835_);
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
else
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_847_; 
v_a_840_ = lean_ctor_get(v___x_824_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_824_);
if (v_isSharedCheck_847_ == 0)
{
v___x_842_ = v___x_824_;
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_824_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_843_ == 0)
{
v___x_845_ = v___x_842_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_a_840_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__4(lean_object* v_init_848_, lean_object* v_as_849_, size_t v_sz_850_, size_t v_i_851_, lean_object* v_b_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
uint8_t v___x_858_; 
v___x_858_ = lean_usize_dec_lt(v_i_851_, v_sz_850_);
if (v___x_858_ == 0)
{
lean_object* v___x_859_; 
v___x_859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_859_, 0, v_b_852_);
return v___x_859_;
}
else
{
lean_object* v_snd_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_894_; 
v_snd_860_ = lean_ctor_get(v_b_852_, 1);
v_isSharedCheck_894_ = !lean_is_exclusive(v_b_852_);
if (v_isSharedCheck_894_ == 0)
{
lean_object* v_unused_895_; 
v_unused_895_ = lean_ctor_get(v_b_852_, 0);
lean_dec(v_unused_895_);
v___x_862_ = v_b_852_;
v_isShared_863_ = v_isSharedCheck_894_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_snd_860_);
lean_dec(v_b_852_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_894_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_864_; lean_object* v_a_865_; lean_object* v___x_866_; 
v___x_864_ = lean_box(0);
v_a_865_ = lean_array_uget_borrowed(v_as_849_, v_i_851_);
lean_inc(v_snd_860_);
v___x_866_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2(v_init_848_, v_a_865_, v_snd_860_, v___y_853_, v___y_854_, v___y_855_, v___y_856_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v_a_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_885_; 
v_a_867_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_885_ == 0)
{
v___x_869_ = v___x_866_;
v_isShared_870_ = v_isSharedCheck_885_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_a_867_);
lean_dec(v___x_866_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_885_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
if (lean_obj_tag(v_a_867_) == 0)
{
lean_object* v___x_871_; lean_object* v___x_873_; 
v___x_871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_871_, 0, v_a_867_);
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 0, v___x_871_);
v___x_873_ = v___x_862_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_871_);
lean_ctor_set(v_reuseFailAlloc_877_, 1, v_snd_860_);
v___x_873_ = v_reuseFailAlloc_877_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
lean_object* v___x_875_; 
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 0, v___x_873_);
v___x_875_ = v___x_869_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_873_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
else
{
lean_object* v_a_878_; lean_object* v___x_880_; 
lean_del_object(v___x_869_);
lean_dec(v_snd_860_);
v_a_878_ = lean_ctor_get(v_a_867_, 0);
lean_inc(v_a_878_);
lean_dec_ref_known(v_a_867_, 1);
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 1, v_a_878_);
lean_ctor_set(v___x_862_, 0, v___x_864_);
v___x_880_ = v___x_862_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v___x_864_);
lean_ctor_set(v_reuseFailAlloc_884_, 1, v_a_878_);
v___x_880_ = v_reuseFailAlloc_884_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
size_t v___x_881_; size_t v___x_882_; 
v___x_881_ = ((size_t)1ULL);
v___x_882_ = lean_usize_add(v_i_851_, v___x_881_);
v_i_851_ = v___x_882_;
v_b_852_ = v___x_880_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_893_; 
lean_del_object(v___x_862_);
lean_dec(v_snd_860_);
v_a_886_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_893_ == 0)
{
v___x_888_ = v___x_866_;
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_866_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_891_; 
if (v_isShared_889_ == 0)
{
v___x_891_ = v___x_888_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_a_886_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_init_896_, lean_object* v_as_897_, lean_object* v_sz_898_, lean_object* v_i_899_, lean_object* v_b_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
size_t v_sz_boxed_906_; size_t v_i_boxed_907_; lean_object* v_res_908_; 
v_sz_boxed_906_ = lean_unbox_usize(v_sz_898_);
lean_dec(v_sz_898_);
v_i_boxed_907_ = lean_unbox_usize(v_i_899_);
lean_dec(v_i_899_);
v_res_908_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__4(v_init_896_, v_as_897_, v_sz_boxed_906_, v_i_boxed_907_, v_b_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
lean_dec_ref(v_as_897_);
lean_dec_ref(v_init_896_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2___boxed(lean_object* v_init_909_, lean_object* v_n_910_, lean_object* v_b_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2(v_init_909_, v_n_910_, v_b_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
lean_dec_ref(v_n_910_);
lean_dec_ref(v_init_909_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___redArg(lean_object* v_as_918_, size_t v_sz_919_, size_t v_i_920_, lean_object* v_b_921_){
_start:
{
uint8_t v___x_923_; 
v___x_923_ = lean_usize_dec_lt(v_i_920_, v_sz_919_);
if (v___x_923_ == 0)
{
lean_object* v___x_924_; 
v___x_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_924_, 0, v_b_921_);
return v___x_924_;
}
else
{
lean_object* v_snd_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_943_; 
v_snd_925_ = lean_ctor_get(v_b_921_, 1);
v_isSharedCheck_943_ = !lean_is_exclusive(v_b_921_);
if (v_isSharedCheck_943_ == 0)
{
lean_object* v_unused_944_; 
v_unused_944_ = lean_ctor_get(v_b_921_, 0);
lean_dec(v_unused_944_);
v___x_927_ = v_b_921_;
v_isShared_928_ = v_isSharedCheck_943_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_snd_925_);
lean_dec(v_b_921_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_943_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_929_; lean_object* v_a_931_; lean_object* v_a_938_; 
v___x_929_ = lean_box(0);
v_a_938_ = lean_array_uget_borrowed(v_as_918_, v_i_920_);
if (lean_obj_tag(v_a_938_) == 0)
{
v_a_931_ = v_snd_925_;
goto v___jp_930_;
}
else
{
lean_object* v_val_939_; uint8_t v___x_940_; 
v_val_939_ = lean_ctor_get(v_a_938_, 0);
v___x_940_ = l_Lean_LocalDecl_isImplementationDetail(v_val_939_);
if (v___x_940_ == 0)
{
lean_object* v___x_941_; lean_object* v___x_942_; 
lean_inc(v_val_939_);
v___x_941_ = l_Lean_LocalDecl_toExpr(v_val_939_);
v___x_942_ = lean_array_push(v_snd_925_, v___x_941_);
v_a_931_ = v___x_942_;
goto v___jp_930_;
}
else
{
v_a_931_ = v_snd_925_;
goto v___jp_930_;
}
}
v___jp_930_:
{
lean_object* v___x_933_; 
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 1, v_a_931_);
lean_ctor_set(v___x_927_, 0, v___x_929_);
v___x_933_ = v___x_927_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v___x_929_);
lean_ctor_set(v_reuseFailAlloc_937_, 1, v_a_931_);
v___x_933_ = v_reuseFailAlloc_937_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
size_t v___x_934_; size_t v___x_935_; 
v___x_934_ = ((size_t)1ULL);
v___x_935_ = lean_usize_add(v_i_920_, v___x_934_);
v_i_920_ = v___x_935_;
v_b_921_ = v___x_933_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_as_945_, lean_object* v_sz_946_, lean_object* v_i_947_, lean_object* v_b_948_, lean_object* v___y_949_){
_start:
{
size_t v_sz_boxed_950_; size_t v_i_boxed_951_; lean_object* v_res_952_; 
v_sz_boxed_950_ = lean_unbox_usize(v_sz_946_);
lean_dec(v_sz_946_);
v_i_boxed_951_ = lean_unbox_usize(v_i_947_);
lean_dec(v_i_947_);
v_res_952_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___redArg(v_as_945_, v_sz_boxed_950_, v_i_boxed_951_, v_b_948_);
lean_dec_ref(v_as_945_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3(lean_object* v_as_953_, size_t v_sz_954_, size_t v_i_955_, lean_object* v_b_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
uint8_t v___x_962_; 
v___x_962_ = lean_usize_dec_lt(v_i_955_, v_sz_954_);
if (v___x_962_ == 0)
{
lean_object* v___x_963_; 
v___x_963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_963_, 0, v_b_956_);
return v___x_963_;
}
else
{
lean_object* v_snd_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_982_; 
v_snd_964_ = lean_ctor_get(v_b_956_, 1);
v_isSharedCheck_982_ = !lean_is_exclusive(v_b_956_);
if (v_isSharedCheck_982_ == 0)
{
lean_object* v_unused_983_; 
v_unused_983_ = lean_ctor_get(v_b_956_, 0);
lean_dec(v_unused_983_);
v___x_966_ = v_b_956_;
v_isShared_967_ = v_isSharedCheck_982_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_snd_964_);
lean_dec(v_b_956_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_982_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_968_; lean_object* v_a_970_; lean_object* v_a_977_; 
v___x_968_ = lean_box(0);
v_a_977_ = lean_array_uget_borrowed(v_as_953_, v_i_955_);
if (lean_obj_tag(v_a_977_) == 0)
{
v_a_970_ = v_snd_964_;
goto v___jp_969_;
}
else
{
lean_object* v_val_978_; uint8_t v___x_979_; 
v_val_978_ = lean_ctor_get(v_a_977_, 0);
v___x_979_ = l_Lean_LocalDecl_isImplementationDetail(v_val_978_);
if (v___x_979_ == 0)
{
lean_object* v___x_980_; lean_object* v___x_981_; 
lean_inc(v_val_978_);
v___x_980_ = l_Lean_LocalDecl_toExpr(v_val_978_);
v___x_981_ = lean_array_push(v_snd_964_, v___x_980_);
v_a_970_ = v___x_981_;
goto v___jp_969_;
}
else
{
v_a_970_ = v_snd_964_;
goto v___jp_969_;
}
}
v___jp_969_:
{
lean_object* v___x_972_; 
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 1, v_a_970_);
lean_ctor_set(v___x_966_, 0, v___x_968_);
v___x_972_ = v___x_966_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v___x_968_);
lean_ctor_set(v_reuseFailAlloc_976_, 1, v_a_970_);
v___x_972_ = v_reuseFailAlloc_976_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
size_t v___x_973_; size_t v___x_974_; lean_object* v___x_975_; 
v___x_973_ = ((size_t)1ULL);
v___x_974_ = lean_usize_add(v_i_955_, v___x_973_);
v___x_975_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___redArg(v_as_953_, v_sz_954_, v___x_974_, v___x_972_);
return v___x_975_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3___boxed(lean_object* v_as_984_, lean_object* v_sz_985_, lean_object* v_i_986_, lean_object* v_b_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
size_t v_sz_boxed_993_; size_t v_i_boxed_994_; lean_object* v_res_995_; 
v_sz_boxed_993_ = lean_unbox_usize(v_sz_985_);
lean_dec(v_sz_985_);
v_i_boxed_994_ = lean_unbox_usize(v_i_986_);
lean_dec(v_i_986_);
v_res_995_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3(v_as_984_, v_sz_boxed_993_, v_i_boxed_994_, v_b_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec_ref(v_as_984_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1(lean_object* v_t_996_, lean_object* v_init_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
lean_object* v_root_1003_; lean_object* v_tail_1004_; lean_object* v___x_1005_; 
v_root_1003_ = lean_ctor_get(v_t_996_, 0);
v_tail_1004_ = lean_ctor_get(v_t_996_, 1);
lean_inc_ref(v_init_997_);
v___x_1005_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2(v_init_997_, v_root_1003_, v_init_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_);
lean_dec_ref(v_init_997_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1042_; 
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1008_ = v___x_1005_;
v_isShared_1009_ = v_isSharedCheck_1042_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_1005_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1042_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
if (lean_obj_tag(v_a_1006_) == 0)
{
lean_object* v_a_1010_; lean_object* v___x_1012_; 
v_a_1010_ = lean_ctor_get(v_a_1006_, 0);
lean_inc(v_a_1010_);
lean_dec_ref_known(v_a_1006_, 1);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 0, v_a_1010_);
v___x_1012_ = v___x_1008_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_a_1010_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
else
{
lean_object* v_a_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; size_t v_sz_1017_; size_t v___x_1018_; lean_object* v___x_1019_; 
lean_del_object(v___x_1008_);
v_a_1014_ = lean_ctor_get(v_a_1006_, 0);
lean_inc(v_a_1014_);
lean_dec_ref_known(v_a_1006_, 1);
v___x_1015_ = lean_box(0);
v___x_1016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1015_);
lean_ctor_set(v___x_1016_, 1, v_a_1014_);
v_sz_1017_ = lean_array_size(v_tail_1004_);
v___x_1018_ = ((size_t)0ULL);
v___x_1019_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3(v_tail_1004_, v_sz_1017_, v___x_1018_, v___x_1016_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_);
if (lean_obj_tag(v___x_1019_) == 0)
{
lean_object* v_a_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1033_; 
v_a_1020_ = lean_ctor_get(v___x_1019_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1022_ = v___x_1019_;
v_isShared_1023_ = v_isSharedCheck_1033_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_a_1020_);
lean_dec(v___x_1019_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1033_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v_fst_1024_; 
v_fst_1024_ = lean_ctor_get(v_a_1020_, 0);
if (lean_obj_tag(v_fst_1024_) == 0)
{
lean_object* v_snd_1025_; lean_object* v___x_1027_; 
v_snd_1025_ = lean_ctor_get(v_a_1020_, 1);
lean_inc(v_snd_1025_);
lean_dec(v_a_1020_);
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 0, v_snd_1025_);
v___x_1027_ = v___x_1022_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_snd_1025_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
else
{
lean_object* v_val_1029_; lean_object* v___x_1031_; 
lean_inc_ref(v_fst_1024_);
lean_dec(v_a_1020_);
v_val_1029_ = lean_ctor_get(v_fst_1024_, 0);
lean_inc(v_val_1029_);
lean_dec_ref_known(v_fst_1024_, 1);
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 0, v_val_1029_);
v___x_1031_ = v___x_1022_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_val_1029_);
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
else
{
lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1041_; 
v_a_1034_ = lean_ctor_get(v___x_1019_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1036_ = v___x_1019_;
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_1019_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1039_; 
if (v_isShared_1037_ == 0)
{
v___x_1039_ = v___x_1036_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_a_1034_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
}
}
}
else
{
lean_object* v_a_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1050_; 
v_a_1043_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1045_ = v___x_1005_;
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_a_1043_);
lean_dec(v___x_1005_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1048_; 
if (v_isShared_1046_ == 0)
{
v___x_1048_ = v___x_1045_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_a_1043_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1___boxed(lean_object* v_t_1051_, lean_object* v_init_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1(v_t_1051_, v_init_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_);
lean_dec(v___y_1056_);
lean_dec_ref(v___y_1055_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
lean_dec_ref(v_t_1051_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1(lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
lean_object* v_lctx_1066_; lean_object* v_decls_1067_; lean_object* v_hs_1068_; lean_object* v___x_1069_; 
v_lctx_1066_ = lean_ctor_get(v___y_1061_, 2);
v_decls_1067_ = lean_ctor_get(v_lctx_1066_, 1);
v_hs_1068_ = ((lean_object*)(l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1___closed__0));
v___x_1069_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1(v_decls_1067_, v_hs_1068_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1___boxed(lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1(v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_localHypotheses(lean_object* v_except_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_){
_start:
{
lean_object* v___x_1084_; 
v___x_1084_ = l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1(v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; lean_object* v___x_1086_; size_t v_sz_1087_; size_t v___x_1088_; lean_object* v___x_1089_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc(v_a_1085_);
lean_dec_ref_known(v___x_1084_, 1);
v___x_1086_ = ((lean_object*)(l_Lean_Meta_Rewrites_localHypotheses___closed__0));
v_sz_1087_ = lean_array_size(v_a_1085_);
v___x_1088_ = ((size_t)0ULL);
v___x_1089_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_localHypotheses_spec__2(v_except_1078_, v_a_1085_, v_sz_1087_, v___x_1088_, v___x_1086_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_);
lean_dec(v_a_1085_);
return v___x_1089_;
}
else
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1097_; 
v_a_1090_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1092_ = v___x_1084_;
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1084_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1095_; 
if (v_isShared_1093_ == 0)
{
v___x_1095_ = v___x_1092_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_a_1090_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_localHypotheses___boxed(lean_object* v_except_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l_Lean_Meta_Rewrites_localHypotheses(v_except_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_);
lean_dec(v_a_1102_);
lean_dec_ref(v_a_1101_);
lean_dec(v_a_1100_);
lean_dec_ref(v_a_1099_);
lean_dec(v_except_1098_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7(lean_object* v_as_1105_, size_t v_sz_1106_, size_t v_i_1107_, lean_object* v_b_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_){
_start:
{
lean_object* v___x_1114_; 
v___x_1114_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___redArg(v_as_1105_, v_sz_1106_, v_i_1107_, v_b_1108_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___boxed(lean_object* v_as_1115_, lean_object* v_sz_1116_, lean_object* v_i_1117_, lean_object* v_b_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
size_t v_sz_boxed_1124_; size_t v_i_boxed_1125_; lean_object* v_res_1126_; 
v_sz_boxed_1124_ = lean_unbox_usize(v_sz_1116_);
lean_dec(v_sz_1116_);
v_i_boxed_1125_ = lean_unbox_usize(v_i_1117_);
lean_dec(v_i_1117_);
v_res_1126_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7(v_as_1115_, v_sz_boxed_1124_, v_i_boxed_1125_, v_b_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
lean_dec(v___y_1120_);
lean_dec_ref(v___y_1119_);
lean_dec_ref(v_as_1115_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6(lean_object* v_as_1127_, size_t v_sz_1128_, size_t v_i_1129_, lean_object* v_b_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_){
_start:
{
lean_object* v___x_1136_; 
v___x_1136_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(v_as_1127_, v_sz_1128_, v_i_1129_, v_b_1130_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___boxed(lean_object* v_as_1137_, lean_object* v_sz_1138_, lean_object* v_i_1139_, lean_object* v_b_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_){
_start:
{
size_t v_sz_boxed_1146_; size_t v_i_boxed_1147_; lean_object* v_res_1148_; 
v_sz_boxed_1146_ = lean_unbox_usize(v_sz_1138_);
lean_dec(v_sz_1138_);
v_i_boxed_1147_ = lean_unbox_usize(v_i_1139_);
lean_dec(v_i_1139_);
v_res_1148_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6(v_as_1137_, v_sz_boxed_1146_, v_i_boxed_1147_, v_b_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
lean_dec_ref(v_as_1137_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_createModuleTreeRef(lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_){
_start:
{
lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1179_ = ((lean_object*)(l_Lean_Meta_Rewrites_createModuleTreeRef___closed__0));
v___x_1180_ = ((lean_object*)(l_Lean_Meta_Rewrites_droppedKeys));
v___x_1181_ = lean_box(0);
v___x_1182_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v___x_1179_, v___x_1180_, v___x_1181_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_createModuleTreeRef___boxed(lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_Lean_Meta_Rewrites_createModuleTreeRef(v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_);
lean_dec(v_a_1186_);
lean_dec_ref(v_a_1185_);
lean_dec(v_a_1184_);
lean_dec_ref(v_a_1183_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_1824551397____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1190_ = lean_box(0);
v___x_1191_ = lean_st_mk_ref(v___x_1190_);
v___x_1192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1191_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_1824551397____hygCtx___hyg_2____boxed(lean_object* v_a_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_1824551397____hygCtx___hyg_2_();
return v_res_1194_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_constantsPerImportTask(void){
_start:
{
lean_object* v___x_1195_; 
v___x_1195_ = lean_unsigned_to_nat(6500u);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_incPrio(lean_object* v_x_1196_, lean_object* v_x_1197_){
_start:
{
lean_object* v_snd_1198_; uint8_t v___x_1199_; 
v_snd_1198_ = lean_ctor_get(v_x_1197_, 1);
v___x_1199_ = lean_unbox(v_snd_1198_);
if (v___x_1199_ == 0)
{
lean_object* v_fst_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1212_; 
v_fst_1200_ = lean_ctor_get(v_x_1197_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v_x_1197_);
if (v_isSharedCheck_1212_ == 0)
{
lean_object* v_unused_1213_; 
v_unused_1213_ = lean_ctor_get(v_x_1197_, 1);
lean_dec(v_unused_1213_);
v___x_1202_ = v_x_1197_;
v_isShared_1203_ = v_isSharedCheck_1212_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_fst_1200_);
lean_dec(v_x_1197_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1212_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
uint8_t v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1209_; 
v___x_1204_ = 0;
v___x_1205_ = lean_unsigned_to_nat(2u);
v___x_1206_ = lean_nat_mul(v___x_1205_, v_x_1196_);
lean_dec(v_x_1196_);
v___x_1207_ = lean_box(v___x_1204_);
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 1, v___x_1206_);
lean_ctor_set(v___x_1202_, 0, v___x_1207_);
v___x_1209_ = v___x_1202_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v___x_1207_);
lean_ctor_set(v_reuseFailAlloc_1211_, 1, v___x_1206_);
v___x_1209_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
lean_object* v___x_1210_; 
v___x_1210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1210_, 0, v_fst_1200_);
lean_ctor_set(v___x_1210_, 1, v___x_1209_);
return v___x_1210_;
}
}
}
else
{
lean_object* v_fst_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1224_; 
v_fst_1214_ = lean_ctor_get(v_x_1197_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v_x_1197_);
if (v_isSharedCheck_1224_ == 0)
{
lean_object* v_unused_1225_; 
v_unused_1225_ = lean_ctor_get(v_x_1197_, 1);
lean_dec(v_unused_1225_);
v___x_1216_ = v_x_1197_;
v_isShared_1217_ = v_isSharedCheck_1224_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_fst_1214_);
lean_dec(v_x_1197_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1224_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
uint8_t v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1221_; 
v___x_1218_ = 1;
v___x_1219_ = lean_box(v___x_1218_);
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 1, v_x_1196_);
lean_ctor_set(v___x_1216_, 0, v___x_1219_);
v___x_1221_ = v___x_1216_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v___x_1219_);
lean_ctor_set(v_reuseFailAlloc_1223_, 1, v_x_1196_);
v___x_1221_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
lean_object* v___x_1222_; 
v___x_1222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1222_, 0, v_fst_1214_);
lean_ctor_set(v___x_1222_, 1, v___x_1221_);
return v___x_1222_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwFindDecls(lean_object* v_moduleRef_1227_, lean_object* v_ty_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_){
_start:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1234_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_ext;
v___x_1235_ = ((lean_object*)(l_Lean_Meta_Rewrites_createModuleTreeRef___closed__0));
v___x_1236_ = ((lean_object*)(l_Lean_Meta_Rewrites_droppedKeys));
v___x_1237_ = lean_unsigned_to_nat(6500u);
v___x_1238_ = lean_box(0);
v___x_1239_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwFindDecls___closed__0));
v___x_1240_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_moduleRef_1227_, v___x_1234_, v___x_1235_, v___x_1236_, v___x_1237_, v___x_1238_, v___x_1239_, v_ty_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwFindDecls___boxed(lean_object* v_moduleRef_1241_, lean_object* v_ty_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l_Lean_Meta_Rewrites_rwFindDecls(v_moduleRef_1241_, v_ty_1242_, v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_);
lean_dec(v_a_1246_);
lean_dec_ref(v_a_1245_);
lean_dec(v_a_1244_);
lean_dec_ref(v_a_1243_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg(lean_object* v_mctx_1249_, lean_object* v_x_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_){
_start:
{
lean_object* v___x_1256_; 
v___x_1256_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp(lean_box(0), v_mctx_1249_, v_x_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_);
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_object* v_a_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1264_; 
v_a_1257_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1259_ = v___x_1256_;
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_a_1257_);
lean_dec(v___x_1256_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1262_; 
if (v_isShared_1260_ == 0)
{
v___x_1262_ = v___x_1259_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_a_1257_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
else
{
lean_object* v_a_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1272_; 
v_a_1265_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1267_ = v___x_1256_;
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_a_1265_);
lean_dec(v___x_1256_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1270_; 
if (v_isShared_1268_ == 0)
{
v___x_1270_ = v___x_1267_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_a_1265_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg___boxed(lean_object* v_mctx_1273_, lean_object* v_x_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg(v_mctx_1273_, v_x_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1277_);
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0(lean_object* v_00_u03b1_1281_, lean_object* v_mctx_1282_, lean_object* v_x_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_){
_start:
{
lean_object* v___x_1289_; 
v___x_1289_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg(v_mctx_1282_, v_x_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___boxed(lean_object* v_00_u03b1_1290_, lean_object* v_mctx_1291_, lean_object* v_x_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_){
_start:
{
lean_object* v_res_1298_; 
v_res_1298_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0(v_00_u03b1_1290_, v_mctx_1291_, v_x_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_);
lean_dec(v___y_1296_);
lean_dec_ref(v___y_1295_);
lean_dec(v___y_1294_);
lean_dec_ref(v___y_1293_);
return v_res_1298_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(lean_object* v_x_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
lean_object* v___x_1305_; 
v___x_1305_ = l_Lean_Meta_saveState___redArg(v___y_1301_, v___y_1303_);
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_object* v_a_1306_; lean_object* v_r_1307_; 
v_a_1306_ = lean_ctor_get(v___x_1305_, 0);
lean_inc(v_a_1306_);
lean_dec_ref_known(v___x_1305_, 1);
lean_inc(v___y_1303_);
lean_inc_ref(v___y_1302_);
lean_inc(v___y_1301_);
lean_inc_ref(v___y_1300_);
v_r_1307_ = lean_apply_5(v_x_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, lean_box(0));
if (lean_obj_tag(v_r_1307_) == 0)
{
lean_object* v_a_1308_; lean_object* v___x_1309_; 
v_a_1308_ = lean_ctor_get(v_r_1307_, 0);
lean_inc(v_a_1308_);
lean_dec_ref_known(v_r_1307_, 1);
v___x_1309_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1306_, v___y_1301_, v___y_1303_);
if (lean_obj_tag(v___x_1309_) == 0)
{
lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1316_; 
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1316_ == 0)
{
lean_object* v_unused_1317_; 
v_unused_1317_ = lean_ctor_get(v___x_1309_, 0);
lean_dec(v_unused_1317_);
v___x_1311_ = v___x_1309_;
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
else
{
lean_dec(v___x_1309_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1314_; 
if (v_isShared_1312_ == 0)
{
lean_ctor_set(v___x_1311_, 0, v_a_1308_);
v___x_1314_ = v___x_1311_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_a_1308_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
else
{
lean_object* v_a_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1325_; 
lean_dec(v_a_1308_);
v_a_1318_ = lean_ctor_get(v___x_1309_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1320_ = v___x_1309_;
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_a_1318_);
lean_dec(v___x_1309_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1323_; 
if (v_isShared_1321_ == 0)
{
v___x_1323_ = v___x_1320_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_a_1318_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
}
else
{
lean_object* v_a_1326_; lean_object* v___x_1327_; 
v_a_1326_ = lean_ctor_get(v_r_1307_, 0);
lean_inc(v_a_1326_);
lean_dec_ref_known(v_r_1307_, 1);
v___x_1327_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1306_, v___y_1301_, v___y_1303_);
if (lean_obj_tag(v___x_1327_) == 0)
{
lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1334_; 
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1334_ == 0)
{
lean_object* v_unused_1335_; 
v_unused_1335_ = lean_ctor_get(v___x_1327_, 0);
lean_dec(v_unused_1335_);
v___x_1329_ = v___x_1327_;
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
else
{
lean_dec(v___x_1327_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1332_; 
if (v_isShared_1330_ == 0)
{
lean_ctor_set_tag(v___x_1329_, 1);
lean_ctor_set(v___x_1329_, 0, v_a_1326_);
v___x_1332_ = v___x_1329_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_a_1326_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
else
{
lean_object* v_a_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1343_; 
lean_dec(v_a_1326_);
v_a_1336_ = lean_ctor_get(v___x_1327_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1338_ = v___x_1327_;
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_a_1336_);
lean_dec(v___x_1327_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___x_1341_; 
if (v_isShared_1339_ == 0)
{
v___x_1341_ = v___x_1338_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_a_1336_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
}
}
}
else
{
lean_object* v_a_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1351_; 
lean_dec_ref(v_x_1299_);
v_a_1344_ = lean_ctor_get(v___x_1305_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1305_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1346_ = v___x_1305_;
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_a_1344_);
lean_dec(v___x_1305_);
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
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg___boxed(lean_object* v_x_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v_x_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1(lean_object* v_00_u03b1_1359_, lean_object* v_x_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_){
_start:
{
lean_object* v___x_1366_; 
v___x_1366_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v_x_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_);
return v___x_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___boxed(lean_object* v_00_u03b1_1367_, lean_object* v_x_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_){
_start:
{
lean_object* v_res_1374_; 
v_res_1374_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1(v_00_u03b1_1367_, v_x_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_);
lean_dec(v___y_1372_);
lean_dec_ref(v___y_1371_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
return v_res_1374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0(lean_object* v___x_1375_, uint8_t v___x_1376_, lean_object* v___x_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_){
_start:
{
lean_object* v___x_1383_; 
v___x_1383_ = l_Lean_Meta_mkFreshExprMVar(v___x_1375_, v___x_1376_, v___x_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v_a_1384_; lean_object* v___x_1385_; uint8_t v_transparency_1386_; lean_object* v___x_1387_; uint8_t v___x_1388_; lean_object* v___y_1390_; uint8_t v___x_1408_; uint8_t v___x_1409_; 
v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
lean_inc(v_a_1384_);
lean_dec_ref_known(v___x_1383_, 1);
v___x_1385_ = l_Lean_Meta_Context_config(v___y_1378_);
v_transparency_1386_ = lean_ctor_get_uint8(v___x_1385_, 9);
lean_dec_ref(v___x_1385_);
v___x_1387_ = l_Lean_Expr_mvarId_x21(v_a_1384_);
lean_dec(v_a_1384_);
v___x_1388_ = 1;
v___x_1408_ = 2;
v___x_1409_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_1386_, v___x_1408_);
if (v___x_1409_ == 0)
{
lean_object* v_keyedConfig_1410_; uint8_t v_trackZetaDelta_1411_; lean_object* v_zetaDeltaSet_1412_; lean_object* v_lctx_1413_; lean_object* v_localInstances_1414_; lean_object* v_defEqCtx_x3f_1415_; lean_object* v_synthPendingDepth_1416_; lean_object* v_customCanUnfoldPredicate_x3f_1417_; uint8_t v_univApprox_1418_; uint8_t v_inTypeClassResolution_1419_; uint8_t v_cacheInferType_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1429_; 
v_keyedConfig_1410_ = lean_ctor_get(v___y_1378_, 0);
v_trackZetaDelta_1411_ = lean_ctor_get_uint8(v___y_1378_, sizeof(void*)*7);
v_zetaDeltaSet_1412_ = lean_ctor_get(v___y_1378_, 1);
v_lctx_1413_ = lean_ctor_get(v___y_1378_, 2);
v_localInstances_1414_ = lean_ctor_get(v___y_1378_, 3);
v_defEqCtx_x3f_1415_ = lean_ctor_get(v___y_1378_, 4);
v_synthPendingDepth_1416_ = lean_ctor_get(v___y_1378_, 5);
v_customCanUnfoldPredicate_x3f_1417_ = lean_ctor_get(v___y_1378_, 6);
v_univApprox_1418_ = lean_ctor_get_uint8(v___y_1378_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1419_ = lean_ctor_get_uint8(v___y_1378_, sizeof(void*)*7 + 2);
v_cacheInferType_1420_ = lean_ctor_get_uint8(v___y_1378_, sizeof(void*)*7 + 3);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___y_1378_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1422_ = v___y_1378_;
v_isShared_1423_ = v_isSharedCheck_1429_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_1417_);
lean_inc(v_synthPendingDepth_1416_);
lean_inc(v_defEqCtx_x3f_1415_);
lean_inc(v_localInstances_1414_);
lean_inc(v_lctx_1413_);
lean_inc(v_zetaDeltaSet_1412_);
lean_inc(v_keyedConfig_1410_);
lean_dec(v___y_1378_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1429_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1424_; lean_object* v___x_1426_; 
v___x_1424_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1408_, v_keyedConfig_1410_);
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 0, v___x_1424_);
v___x_1426_ = v___x_1422_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v___x_1424_);
lean_ctor_set(v_reuseFailAlloc_1428_, 1, v_zetaDeltaSet_1412_);
lean_ctor_set(v_reuseFailAlloc_1428_, 2, v_lctx_1413_);
lean_ctor_set(v_reuseFailAlloc_1428_, 3, v_localInstances_1414_);
lean_ctor_set(v_reuseFailAlloc_1428_, 4, v_defEqCtx_x3f_1415_);
lean_ctor_set(v_reuseFailAlloc_1428_, 5, v_synthPendingDepth_1416_);
lean_ctor_set(v_reuseFailAlloc_1428_, 6, v_customCanUnfoldPredicate_x3f_1417_);
lean_ctor_set_uint8(v_reuseFailAlloc_1428_, sizeof(void*)*7, v_trackZetaDelta_1411_);
lean_ctor_set_uint8(v_reuseFailAlloc_1428_, sizeof(void*)*7 + 1, v_univApprox_1418_);
lean_ctor_set_uint8(v_reuseFailAlloc_1428_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1419_);
lean_ctor_set_uint8(v_reuseFailAlloc_1428_, sizeof(void*)*7 + 3, v_cacheInferType_1420_);
v___x_1426_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
lean_object* v___x_1427_; 
v___x_1427_ = l_Lean_MVarId_refl(v___x_1387_, v___x_1388_, v___x_1426_, v___y_1379_, v___y_1380_, v___y_1381_);
lean_dec_ref(v___x_1426_);
v___y_1390_ = v___x_1427_;
goto v___jp_1389_;
}
}
}
else
{
lean_object* v___x_1430_; 
v___x_1430_ = l_Lean_MVarId_refl(v___x_1387_, v___x_1388_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_);
lean_dec_ref(v___y_1378_);
v___y_1390_ = v___x_1430_;
goto v___jp_1389_;
}
v___jp_1389_:
{
if (lean_obj_tag(v___y_1390_) == 0)
{
lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1398_; 
v_isSharedCheck_1398_ = !lean_is_exclusive(v___y_1390_);
if (v_isSharedCheck_1398_ == 0)
{
lean_object* v_unused_1399_; 
v_unused_1399_ = lean_ctor_get(v___y_1390_, 0);
lean_dec(v_unused_1399_);
v___x_1392_ = v___y_1390_;
v_isShared_1393_ = v_isSharedCheck_1398_;
goto v_resetjp_1391_;
}
else
{
lean_dec(v___y_1390_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1398_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1394_; lean_object* v___x_1396_; 
v___x_1394_ = lean_box(v___x_1388_);
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 0, v___x_1394_);
v___x_1396_ = v___x_1392_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v___x_1394_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
return v___x_1396_;
}
}
}
else
{
lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1407_; 
v_a_1400_ = lean_ctor_get(v___y_1390_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___y_1390_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1402_ = v___y_1390_;
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v___y_1390_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1405_; 
if (v_isShared_1403_ == 0)
{
v___x_1405_ = v___x_1402_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_a_1400_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
}
}
else
{
lean_object* v_a_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1438_; 
lean_dec_ref(v___y_1378_);
v_a_1431_ = lean_ctor_get(v___x_1383_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1433_ = v___x_1383_;
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_a_1431_);
lean_dec(v___x_1383_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1436_; 
if (v_isShared_1434_ == 0)
{
v___x_1436_ = v___x_1433_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_a_1431_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___boxed(lean_object* v___x_1439_, lean_object* v___x_1440_, lean_object* v___x_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_){
_start:
{
uint8_t v___x_2261__boxed_1447_; lean_object* v_res_1448_; 
v___x_2261__boxed_1447_ = lean_unbox(v___x_1440_);
v_res_1448_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0(v___x_1439_, v___x_2261__boxed_1447_, v___x_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
lean_dec(v___y_1443_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(lean_object* v_mctx_1449_, lean_object* v_e_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_){
_start:
{
lean_object* v___x_1456_; uint8_t v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___f_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; 
v___x_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1456_, 0, v_e_1450_);
v___x_1457_ = 0;
v___x_1458_ = lean_box(0);
v___x_1459_ = lean_box(v___x_1457_);
v___f_1460_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1460_, 0, v___x_1456_);
lean_closure_set(v___f_1460_, 1, v___x_1459_);
lean_closure_set(v___f_1460_, 2, v___x_1458_);
v___x_1461_ = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___boxed), 8, 3);
lean_closure_set(v___x_1461_, 0, lean_box(0));
lean_closure_set(v___x_1461_, 1, v_mctx_1449_);
lean_closure_set(v___x_1461_, 2, v___f_1460_);
v___x_1462_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v___x_1461_, v_a_1451_, v_a_1452_, v_a_1453_, v_a_1454_);
if (lean_obj_tag(v___x_1462_) == 0)
{
return v___x_1462_;
}
else
{
lean_object* v_a_1463_; uint8_t v___y_1465_; uint8_t v___x_1475_; 
v_a_1463_ = lean_ctor_get(v___x_1462_, 0);
v___x_1475_ = l_Lean_Exception_isInterrupt(v_a_1463_);
if (v___x_1475_ == 0)
{
uint8_t v___x_1476_; 
lean_inc(v_a_1463_);
v___x_1476_ = l_Lean_Exception_isRuntime(v_a_1463_);
v___y_1465_ = v___x_1476_;
goto v___jp_1464_;
}
else
{
v___y_1465_ = v___x_1475_;
goto v___jp_1464_;
}
v___jp_1464_:
{
if (v___y_1465_ == 0)
{
lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1473_; 
v_isSharedCheck_1473_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1473_ == 0)
{
lean_object* v_unused_1474_; 
v_unused_1474_ = lean_ctor_get(v___x_1462_, 0);
lean_dec(v_unused_1474_);
v___x_1467_ = v___x_1462_;
v_isShared_1468_ = v_isSharedCheck_1473_;
goto v_resetjp_1466_;
}
else
{
lean_dec(v___x_1462_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1473_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1469_; lean_object* v___x_1471_; 
v___x_1469_ = lean_box(v___y_1465_);
if (v_isShared_1468_ == 0)
{
lean_ctor_set_tag(v___x_1467_, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1469_);
v___x_1471_ = v___x_1467_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v___x_1469_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
return v___x_1471_;
}
}
}
else
{
return v___x_1462_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___boxed(lean_object* v_mctx_1477_, lean_object* v_e_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(v_mctx_1477_, v_e_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_);
lean_dec(v_a_1482_);
lean_dec_ref(v_a_1481_);
lean_dec(v_a_1480_);
lean_dec_ref(v_a_1479_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult(lean_object* v_r_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_){
_start:
{
lean_object* v_result_1491_; lean_object* v_eNew_1492_; lean_object* v___x_1493_; 
v_result_1491_ = lean_ctor_get(v_r_1485_, 2);
lean_inc_ref(v_result_1491_);
lean_dec_ref(v_r_1485_);
v_eNew_1492_ = lean_ctor_get(v_result_1491_, 0);
lean_inc_ref(v_eNew_1492_);
lean_dec_ref(v_result_1491_);
v___x_1493_ = l_Lean_Meta_ppExpr(v_eNew_1492_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_);
if (lean_obj_tag(v___x_1493_) == 0)
{
lean_object* v_a_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1504_; 
v_a_1494_ = lean_ctor_get(v___x_1493_, 0);
v_isSharedCheck_1504_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1496_ = v___x_1493_;
v_isShared_1497_ = v_isSharedCheck_1504_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_a_1494_);
lean_dec(v___x_1493_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1504_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1502_; 
v___x_1498_ = l_Std_Format_defWidth;
v___x_1499_ = lean_unsigned_to_nat(0u);
v___x_1500_ = l_Std_Format_pretty(v_a_1494_, v___x_1498_, v___x_1499_, v___x_1499_);
if (v_isShared_1497_ == 0)
{
lean_ctor_set(v___x_1496_, 0, v___x_1500_);
v___x_1502_ = v___x_1496_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v___x_1500_);
v___x_1502_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
return v___x_1502_;
}
}
}
else
{
lean_object* v_a_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1512_; 
v_a_1505_ = lean_ctor_get(v___x_1493_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1507_ = v___x_1493_;
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_a_1505_);
lean_dec(v___x_1493_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1510_; 
if (v_isShared_1508_ == 0)
{
v___x_1510_ = v___x_1507_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_a_1505_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
return v___x_1510_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult___boxed(lean_object* v_r_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult(v_r_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_);
lean_dec(v_a_1517_);
lean_dec_ref(v_a_1516_);
lean_dec(v_a_1515_);
lean_dec_ref(v_a_1514_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorIdx___impl(uint8_t v_x_1520_){
_start:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1521_ = lean_box(v_x_1520_);
v___x_1522_ = lean_obj_tag_nat(v___x_1521_);
lean_dec(v___x_1521_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorIdx___impl___boxed(lean_object* v_x_1523_){
_start:
{
uint8_t v_x_4__boxed_1524_; lean_object* v_res_1525_; 
v_x_4__boxed_1524_ = lean_unbox(v_x_1523_);
v_res_1525_ = l_Lean_Meta_Rewrites_SideConditions_ctorIdx___impl(v_x_4__boxed_1524_);
return v_res_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorElim___redArg(lean_object* v_k_1526_){
_start:
{
lean_inc(v_k_1526_);
return v_k_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorElim___redArg___boxed(lean_object* v_k_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l_Lean_Meta_Rewrites_SideConditions_ctorElim___redArg(v_k_1527_);
lean_dec(v_k_1527_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorElim(lean_object* v_motive_1529_, lean_object* v_ctorIdx_1530_, uint8_t v_t_1531_, lean_object* v_h_1532_, lean_object* v_k_1533_){
_start:
{
lean_inc(v_k_1533_);
return v_k_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorElim___boxed(lean_object* v_motive_1534_, lean_object* v_ctorIdx_1535_, lean_object* v_t_1536_, lean_object* v_h_1537_, lean_object* v_k_1538_){
_start:
{
uint8_t v_t_boxed_1539_; lean_object* v_res_1540_; 
v_t_boxed_1539_ = lean_unbox(v_t_1536_);
v_res_1540_ = l_Lean_Meta_Rewrites_SideConditions_ctorElim(v_motive_1534_, v_ctorIdx_1535_, v_t_boxed_1539_, v_h_1537_, v_k_1538_);
lean_dec(v_k_1538_);
lean_dec(v_ctorIdx_1535_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_none_elim___redArg(lean_object* v_none_1541_){
_start:
{
lean_inc(v_none_1541_);
return v_none_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_none_elim___redArg___boxed(lean_object* v_none_1542_){
_start:
{
lean_object* v_res_1543_; 
v_res_1543_ = l_Lean_Meta_Rewrites_SideConditions_none_elim___redArg(v_none_1542_);
lean_dec(v_none_1542_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_none_elim(lean_object* v_motive_1544_, uint8_t v_t_1545_, lean_object* v_h_1546_, lean_object* v_none_1547_){
_start:
{
lean_inc(v_none_1547_);
return v_none_1547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_none_elim___boxed(lean_object* v_motive_1548_, lean_object* v_t_1549_, lean_object* v_h_1550_, lean_object* v_none_1551_){
_start:
{
uint8_t v_t_boxed_1552_; lean_object* v_res_1553_; 
v_t_boxed_1552_ = lean_unbox(v_t_1549_);
v_res_1553_ = l_Lean_Meta_Rewrites_SideConditions_none_elim(v_motive_1548_, v_t_boxed_1552_, v_h_1550_, v_none_1551_);
lean_dec(v_none_1551_);
return v_res_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_assumption_elim___redArg(lean_object* v_assumption_1554_){
_start:
{
lean_inc(v_assumption_1554_);
return v_assumption_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_assumption_elim___redArg___boxed(lean_object* v_assumption_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l_Lean_Meta_Rewrites_SideConditions_assumption_elim___redArg(v_assumption_1555_);
lean_dec(v_assumption_1555_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_assumption_elim(lean_object* v_motive_1557_, uint8_t v_t_1558_, lean_object* v_h_1559_, lean_object* v_assumption_1560_){
_start:
{
lean_inc(v_assumption_1560_);
return v_assumption_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_assumption_elim___boxed(lean_object* v_motive_1561_, lean_object* v_t_1562_, lean_object* v_h_1563_, lean_object* v_assumption_1564_){
_start:
{
uint8_t v_t_boxed_1565_; lean_object* v_res_1566_; 
v_t_boxed_1565_ = lean_unbox(v_t_1562_);
v_res_1566_ = l_Lean_Meta_Rewrites_SideConditions_assumption_elim(v_motive_1561_, v_t_boxed_1565_, v_h_1563_, v_assumption_1564_);
lean_dec(v_assumption_1564_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim___redArg(lean_object* v_solveByElim_1567_){
_start:
{
lean_inc(v_solveByElim_1567_);
return v_solveByElim_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim___redArg___boxed(lean_object* v_solveByElim_1568_){
_start:
{
lean_object* v_res_1569_; 
v_res_1569_ = l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim___redArg(v_solveByElim_1568_);
lean_dec(v_solveByElim_1568_);
return v_res_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim(lean_object* v_motive_1570_, uint8_t v_t_1571_, lean_object* v_h_1572_, lean_object* v_solveByElim_1573_){
_start:
{
lean_inc(v_solveByElim_1573_);
return v_solveByElim_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim___boxed(lean_object* v_motive_1574_, lean_object* v_t_1575_, lean_object* v_h_1576_, lean_object* v_solveByElim_1577_){
_start:
{
uint8_t v_t_boxed_1578_; lean_object* v_res_1579_; 
v_t_boxed_1578_ = lean_unbox(v_t_1575_);
v_res_1579_ = l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim(v_motive_1574_, v_t_boxed_1578_, v_h_1576_, v_solveByElim_1577_);
lean_dec(v_solveByElim_1577_);
return v_res_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__0(lean_object* v_x_1580_, lean_object* v_x_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_){
_start:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1587_ = lean_box(0);
v___x_1588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1587_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__0___boxed(lean_object* v_x_1589_, lean_object* v_x_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_){
_start:
{
lean_object* v_res_1596_; 
v_res_1596_ = l_Lean_Meta_Rewrites_solveByElim___lam__0(v_x_1589_, v_x_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_);
lean_dec(v___y_1594_);
lean_dec_ref(v___y_1593_);
lean_dec(v___y_1592_);
lean_dec_ref(v___y_1591_);
lean_dec(v_x_1590_);
lean_dec(v_x_1589_);
return v_res_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__1(lean_object* v_x_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_){
_start:
{
uint8_t v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; 
v___x_1603_ = 0;
v___x_1604_ = lean_box(v___x_1603_);
v___x_1605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1604_);
return v___x_1605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__1___boxed(lean_object* v_x_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_){
_start:
{
lean_object* v_res_1612_; 
v_res_1612_ = l_Lean_Meta_Rewrites_solveByElim___lam__1(v_x_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_);
lean_dec(v___y_1610_);
lean_dec_ref(v___y_1609_);
lean_dec(v___y_1608_);
lean_dec_ref(v___y_1607_);
lean_dec(v_x_1606_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0(lean_object* v_msgData_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
lean_object* v___x_1619_; lean_object* v_env_1620_; uint8_t v___x_1621_; lean_object* v_env_1622_; lean_object* v___x_1623_; lean_object* v_toCold_1624_; lean_object* v_mctx_1625_; lean_object* v_lctx_1626_; lean_object* v_options_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1619_ = lean_st_ref_get(v___y_1617_);
v_env_1620_ = lean_ctor_get(v___x_1619_, 0);
lean_inc_ref(v_env_1620_);
lean_dec(v___x_1619_);
v___x_1621_ = 0;
v_env_1622_ = l_Lean_Environment_setRecordingDeps(v_env_1620_, v___x_1621_);
v___x_1623_ = lean_st_ref_get(v___y_1615_);
v_toCold_1624_ = lean_ctor_get(v___y_1616_, 0);
v_mctx_1625_ = lean_ctor_get(v___x_1623_, 0);
lean_inc_ref(v_mctx_1625_);
lean_dec(v___x_1623_);
v_lctx_1626_ = lean_ctor_get(v___y_1614_, 2);
v_options_1627_ = lean_ctor_get(v_toCold_1624_, 2);
lean_inc_ref(v_options_1627_);
lean_inc_ref(v_lctx_1626_);
v___x_1628_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1628_, 0, v_env_1622_);
lean_ctor_set(v___x_1628_, 1, v_mctx_1625_);
lean_ctor_set(v___x_1628_, 2, v_lctx_1626_);
lean_ctor_set(v___x_1628_, 3, v_options_1627_);
v___x_1629_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1628_);
lean_ctor_set(v___x_1629_, 1, v_msgData_1613_);
v___x_1630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1629_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0___boxed(lean_object* v_msgData_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
lean_object* v_res_1637_; 
v_res_1637_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0(v_msgData_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
return v_res_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(lean_object* v_msg_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_){
_start:
{
lean_object* v_ref_1644_; lean_object* v___x_1645_; lean_object* v_a_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1654_; 
v_ref_1644_ = lean_ctor_get(v___y_1641_, 2);
v___x_1645_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0(v_msg_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v___x_1645_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1648_ = v___x_1645_;
v_isShared_1649_ = v_isSharedCheck_1654_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_a_1646_);
lean_dec(v___x_1645_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1654_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1650_; lean_object* v___x_1652_; 
lean_inc(v_ref_1644_);
v___x_1650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1650_, 0, v_ref_1644_);
lean_ctor_set(v___x_1650_, 1, v_a_1646_);
if (v_isShared_1649_ == 0)
{
lean_ctor_set_tag(v___x_1648_, 1);
lean_ctor_set(v___x_1648_, 0, v___x_1650_);
v___x_1652_ = v___x_1648_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v___x_1650_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
return v___x_1652_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg___boxed(lean_object* v_msg_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_){
_start:
{
lean_object* v_res_1661_; 
v_res_1661_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(v_msg_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_);
lean_dec(v___y_1659_);
lean_dec_ref(v___y_1658_);
lean_dec(v___y_1657_);
lean_dec_ref(v___y_1656_);
return v_res_1661_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1663_; lean_object* v___x_1664_; 
v___x_1663_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__0));
v___x_1664_ = l_Lean_stringToMessageData(v___x_1663_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__2(lean_object* v_x_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_){
_start:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1671_ = lean_obj_once(&l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1, &l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1_once, _init_l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1);
v___x_1672_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(v___x_1671_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__2___boxed(lean_object* v_x_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
lean_object* v_res_1679_; 
v_res_1679_ = l_Lean_Meta_Rewrites_solveByElim___lam__2(v_x_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1676_);
lean_dec(v___y_1675_);
lean_dec_ref(v___y_1674_);
lean_dec(v_x_1673_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim(lean_object* v_goals_1689_, lean_object* v_depth_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_){
_start:
{
lean_object* v___f_1696_; lean_object* v___f_1697_; lean_object* v___f_1698_; uint8_t v___x_1699_; lean_object* v___x_1700_; uint8_t v___x_1701_; lean_object* v___x_1702_; uint8_t v___x_1703_; lean_object* v___x_1704_; lean_object* v_cfg_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___f_1696_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___closed__0));
v___f_1697_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___closed__1));
v___f_1698_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___closed__2));
v___x_1699_ = 0;
v___x_1700_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1700_, 0, v_depth_1690_);
lean_ctor_set(v___x_1700_, 1, v___f_1696_);
lean_ctor_set(v___x_1700_, 2, v___f_1697_);
lean_ctor_set(v___x_1700_, 3, v___f_1698_);
lean_ctor_set_uint8(v___x_1700_, sizeof(void*)*4, v___x_1699_);
v___x_1701_ = 1;
v___x_1702_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___closed__3));
v___x_1703_ = 1;
v___x_1704_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_1704_, 0, v___x_1700_);
lean_ctor_set(v___x_1704_, 1, v___x_1702_);
lean_ctor_set_uint8(v___x_1704_, sizeof(void*)*2, v___x_1703_);
lean_ctor_set_uint8(v___x_1704_, sizeof(void*)*2 + 1, v___x_1701_);
lean_ctor_set_uint8(v___x_1704_, sizeof(void*)*2 + 2, v___x_1699_);
v_cfg_1705_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_cfg_1705_, 0, v___x_1704_);
lean_ctor_set_uint8(v_cfg_1705_, sizeof(void*)*1, v___x_1701_);
lean_ctor_set_uint8(v_cfg_1705_, sizeof(void*)*1 + 1, v___x_1701_);
lean_ctor_set_uint8(v_cfg_1705_, sizeof(void*)*1 + 2, v___x_1701_);
lean_ctor_set_uint8(v_cfg_1705_, sizeof(void*)*1 + 3, v___x_1699_);
v___x_1706_ = lean_box(0);
v___x_1707_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___closed__4));
v___x_1708_ = l_Lean_Meta_SolveByElim_mkAssumptionSet(v___x_1699_, v___x_1699_, v___x_1706_, v___x_1706_, v___x_1707_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_);
if (lean_obj_tag(v___x_1708_) == 0)
{
lean_object* v_a_1709_; lean_object* v_fst_1710_; lean_object* v_snd_1711_; lean_object* v___x_1712_; 
v_a_1709_ = lean_ctor_get(v___x_1708_, 0);
lean_inc(v_a_1709_);
lean_dec_ref_known(v___x_1708_, 1);
v_fst_1710_ = lean_ctor_get(v_a_1709_, 0);
lean_inc(v_fst_1710_);
v_snd_1711_ = lean_ctor_get(v_a_1709_, 1);
lean_inc(v_snd_1711_);
lean_dec(v_a_1709_);
v___x_1712_ = l_Lean_Meta_SolveByElim_solveByElim(v_cfg_1705_, v_fst_1710_, v_snd_1711_, v_goals_1689_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_);
if (lean_obj_tag(v___x_1712_) == 0)
{
lean_object* v_a_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1723_; 
v_a_1713_ = lean_ctor_get(v___x_1712_, 0);
v_isSharedCheck_1723_ = !lean_is_exclusive(v___x_1712_);
if (v_isSharedCheck_1723_ == 0)
{
v___x_1715_ = v___x_1712_;
v_isShared_1716_ = v_isSharedCheck_1723_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_a_1713_);
lean_dec(v___x_1712_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1723_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
if (lean_obj_tag(v_a_1713_) == 0)
{
lean_object* v___x_1717_; lean_object* v___x_1719_; 
v___x_1717_ = lean_box(0);
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 0, v___x_1717_);
v___x_1719_ = v___x_1715_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v___x_1717_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
else
{
lean_object* v___x_1721_; lean_object* v___x_1722_; 
lean_del_object(v___x_1715_);
lean_dec(v_a_1713_);
v___x_1721_ = lean_obj_once(&l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1, &l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1_once, _init_l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1);
v___x_1722_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(v___x_1721_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_);
return v___x_1722_;
}
}
}
else
{
lean_object* v_a_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1731_; 
v_a_1724_ = lean_ctor_get(v___x_1712_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1712_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1726_ = v___x_1712_;
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_a_1724_);
lean_dec(v___x_1712_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1729_; 
if (v_isShared_1727_ == 0)
{
v___x_1729_ = v___x_1726_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_a_1724_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
}
}
else
{
lean_object* v_a_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1739_; 
lean_dec_ref_known(v_cfg_1705_, 1);
lean_dec(v_goals_1689_);
v_a_1732_ = lean_ctor_get(v___x_1708_, 0);
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1734_ = v___x_1708_;
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_a_1732_);
lean_dec(v___x_1708_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1737_; 
if (v_isShared_1735_ == 0)
{
v___x_1737_ = v___x_1734_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v_a_1732_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
return v___x_1737_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___boxed(lean_object* v_goals_1740_, lean_object* v_depth_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l_Lean_Meta_Rewrites_solveByElim(v_goals_1740_, v_depth_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_);
lean_dec(v_a_1745_);
lean_dec_ref(v_a_1744_);
lean_dec(v_a_1743_);
lean_dec_ref(v_a_1742_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0(lean_object* v_00_u03b1_1748_, lean_object* v_msg_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_){
_start:
{
lean_object* v___x_1755_; 
v___x_1755_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(v_msg_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
return v___x_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___boxed(lean_object* v_00_u03b1_1756_, lean_object* v_msg_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_){
_start:
{
lean_object* v_res_1763_; 
v_res_1763_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0(v_00_u03b1_1756_, v_msg_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_);
lean_dec(v___y_1761_);
lean_dec_ref(v___y_1760_);
lean_dec(v___y_1759_);
lean_dec_ref(v___y_1758_);
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg(lean_object* v_e_1764_, lean_object* v___y_1765_){
_start:
{
uint8_t v___x_1767_; 
v___x_1767_ = l_Lean_Expr_hasMVar(v_e_1764_);
if (v___x_1767_ == 0)
{
lean_object* v___x_1768_; 
v___x_1768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1768_, 0, v_e_1764_);
return v___x_1768_;
}
else
{
lean_object* v___x_1769_; lean_object* v_mctx_1770_; lean_object* v___x_1771_; lean_object* v_fst_1772_; lean_object* v_snd_1773_; lean_object* v___x_1774_; lean_object* v_cache_1775_; lean_object* v_zetaDeltaFVarIds_1776_; lean_object* v_postponed_1777_; lean_object* v_diag_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1787_; 
v___x_1769_ = lean_st_ref_get(v___y_1765_);
v_mctx_1770_ = lean_ctor_get(v___x_1769_, 0);
lean_inc_ref(v_mctx_1770_);
lean_dec(v___x_1769_);
v___x_1771_ = l_Lean_instantiateMVarsCore(v_mctx_1770_, v_e_1764_);
v_fst_1772_ = lean_ctor_get(v___x_1771_, 0);
lean_inc(v_fst_1772_);
v_snd_1773_ = lean_ctor_get(v___x_1771_, 1);
lean_inc(v_snd_1773_);
lean_dec_ref(v___x_1771_);
v___x_1774_ = lean_st_ref_take(v___y_1765_);
v_cache_1775_ = lean_ctor_get(v___x_1774_, 1);
v_zetaDeltaFVarIds_1776_ = lean_ctor_get(v___x_1774_, 2);
v_postponed_1777_ = lean_ctor_get(v___x_1774_, 3);
v_diag_1778_ = lean_ctor_get(v___x_1774_, 4);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1787_ == 0)
{
lean_object* v_unused_1788_; 
v_unused_1788_ = lean_ctor_get(v___x_1774_, 0);
lean_dec(v_unused_1788_);
v___x_1780_ = v___x_1774_;
v_isShared_1781_ = v_isSharedCheck_1787_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_diag_1778_);
lean_inc(v_postponed_1777_);
lean_inc(v_zetaDeltaFVarIds_1776_);
lean_inc(v_cache_1775_);
lean_dec(v___x_1774_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1787_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1783_; 
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 0, v_snd_1773_);
v___x_1783_ = v___x_1780_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_snd_1773_);
lean_ctor_set(v_reuseFailAlloc_1786_, 1, v_cache_1775_);
lean_ctor_set(v_reuseFailAlloc_1786_, 2, v_zetaDeltaFVarIds_1776_);
lean_ctor_set(v_reuseFailAlloc_1786_, 3, v_postponed_1777_);
lean_ctor_set(v_reuseFailAlloc_1786_, 4, v_diag_1778_);
v___x_1783_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1784_ = lean_st_ref_put(v___y_1765_, v___x_1783_);
v___x_1785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1785_, 0, v_fst_1772_);
return v___x_1785_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg___boxed(lean_object* v_e_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
lean_object* v_res_1792_; 
v_res_1792_ = l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg(v_e_1789_, v___y_1790_);
lean_dec(v___y_1790_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0(lean_object* v_e_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
lean_object* v___x_1799_; 
v___x_1799_ = l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg(v_e_1793_, v___y_1795_);
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___boxed(lean_object* v_e_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_){
_start:
{
lean_object* v_res_1806_; 
v_res_1806_ = l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0(v_e_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
return v_res_1806_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1807_; double v___x_1808_; 
v___x_1807_ = lean_unsigned_to_nat(0u);
v___x_1808_ = lean_float_of_nat(v___x_1807_);
return v___x_1808_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2(lean_object* v_cls_1812_, lean_object* v_msg_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_){
_start:
{
lean_object* v_ref_1819_; lean_object* v___x_1820_; lean_object* v_a_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1866_; 
v_ref_1819_ = lean_ctor_get(v___y_1816_, 2);
v___x_1820_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0(v_msg_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_);
v_a_1821_ = lean_ctor_get(v___x_1820_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1820_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1823_ = v___x_1820_;
v_isShared_1824_ = v_isSharedCheck_1866_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_a_1821_);
lean_dec(v___x_1820_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1866_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1825_; lean_object* v_traceState_1826_; lean_object* v_env_1827_; lean_object* v_nextMacroScope_1828_; lean_object* v_ngen_1829_; lean_object* v_auxDeclNGen_1830_; lean_object* v_cache_1831_; lean_object* v_recordedDeps_1832_; lean_object* v_messages_1833_; lean_object* v_infoState_1834_; lean_object* v_snapshotTasks_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1865_; 
v___x_1825_ = lean_st_ref_take(v___y_1817_);
v_traceState_1826_ = lean_ctor_get(v___x_1825_, 4);
v_env_1827_ = lean_ctor_get(v___x_1825_, 0);
v_nextMacroScope_1828_ = lean_ctor_get(v___x_1825_, 1);
v_ngen_1829_ = lean_ctor_get(v___x_1825_, 2);
v_auxDeclNGen_1830_ = lean_ctor_get(v___x_1825_, 3);
v_cache_1831_ = lean_ctor_get(v___x_1825_, 5);
v_recordedDeps_1832_ = lean_ctor_get(v___x_1825_, 6);
v_messages_1833_ = lean_ctor_get(v___x_1825_, 7);
v_infoState_1834_ = lean_ctor_get(v___x_1825_, 8);
v_snapshotTasks_1835_ = lean_ctor_get(v___x_1825_, 9);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1837_ = v___x_1825_;
v_isShared_1838_ = v_isSharedCheck_1865_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_snapshotTasks_1835_);
lean_inc(v_infoState_1834_);
lean_inc(v_messages_1833_);
lean_inc(v_recordedDeps_1832_);
lean_inc(v_cache_1831_);
lean_inc(v_traceState_1826_);
lean_inc(v_auxDeclNGen_1830_);
lean_inc(v_ngen_1829_);
lean_inc(v_nextMacroScope_1828_);
lean_inc(v_env_1827_);
lean_dec(v___x_1825_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1865_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
uint64_t v_tid_1839_; lean_object* v_traces_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1864_; 
v_tid_1839_ = lean_ctor_get_uint64(v_traceState_1826_, sizeof(void*)*1);
v_traces_1840_ = lean_ctor_get(v_traceState_1826_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v_traceState_1826_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1842_ = v_traceState_1826_;
v_isShared_1843_ = v_isSharedCheck_1864_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_traces_1840_);
lean_dec(v_traceState_1826_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1864_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; double v___x_1846_; uint8_t v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1855_; 
v___x_1844_ = lean_box(0);
v___x_1845_ = lean_box(0);
v___x_1846_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__0);
v___x_1847_ = 0;
v___x_1848_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__1));
v___x_1849_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1849_, 0, v_cls_1812_);
lean_ctor_set(v___x_1849_, 1, v___x_1845_);
lean_ctor_set(v___x_1849_, 2, v___x_1848_);
lean_ctor_set_float(v___x_1849_, sizeof(void*)*3, v___x_1846_);
lean_ctor_set_float(v___x_1849_, sizeof(void*)*3 + 8, v___x_1846_);
lean_ctor_set_uint8(v___x_1849_, sizeof(void*)*3 + 16, v___x_1847_);
v___x_1850_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__2));
v___x_1851_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1849_);
lean_ctor_set(v___x_1851_, 1, v_a_1821_);
lean_ctor_set(v___x_1851_, 2, v___x_1850_);
lean_inc(v_ref_1819_);
v___x_1852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1852_, 0, v_ref_1819_);
lean_ctor_set(v___x_1852_, 1, v___x_1851_);
v___x_1853_ = l_Lean_PersistentArray_push___redArg(v_traces_1840_, v___x_1852_);
if (v_isShared_1843_ == 0)
{
lean_ctor_set(v___x_1842_, 0, v___x_1853_);
v___x_1855_ = v___x_1842_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v___x_1853_);
lean_ctor_set_uint64(v_reuseFailAlloc_1863_, sizeof(void*)*1, v_tid_1839_);
v___x_1855_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
lean_object* v___x_1857_; 
if (v_isShared_1838_ == 0)
{
lean_ctor_set(v___x_1837_, 4, v___x_1855_);
v___x_1857_ = v___x_1837_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v_env_1827_);
lean_ctor_set(v_reuseFailAlloc_1862_, 1, v_nextMacroScope_1828_);
lean_ctor_set(v_reuseFailAlloc_1862_, 2, v_ngen_1829_);
lean_ctor_set(v_reuseFailAlloc_1862_, 3, v_auxDeclNGen_1830_);
lean_ctor_set(v_reuseFailAlloc_1862_, 4, v___x_1855_);
lean_ctor_set(v_reuseFailAlloc_1862_, 5, v_cache_1831_);
lean_ctor_set(v_reuseFailAlloc_1862_, 6, v_recordedDeps_1832_);
lean_ctor_set(v_reuseFailAlloc_1862_, 7, v_messages_1833_);
lean_ctor_set(v_reuseFailAlloc_1862_, 8, v_infoState_1834_);
lean_ctor_set(v_reuseFailAlloc_1862_, 9, v_snapshotTasks_1835_);
v___x_1857_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
lean_object* v___x_1858_; lean_object* v___x_1860_; 
v___x_1858_ = lean_st_ref_put(v___y_1817_, v___x_1857_);
if (v_isShared_1824_ == 0)
{
lean_ctor_set(v___x_1823_, 0, v___x_1844_);
v___x_1860_ = v___x_1823_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v___x_1844_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___boxed(lean_object* v_cls_1867_, lean_object* v_msg_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_){
_start:
{
lean_object* v_res_1874_; 
v_res_1874_ = l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2(v_cls_1867_, v_msg_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
return v_res_1874_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Rewrites_rwLemma_spec__1(lean_object* v_x_1875_, lean_object* v_x_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_){
_start:
{
if (lean_obj_tag(v_x_1875_) == 0)
{
lean_object* v___x_1882_; lean_object* v___x_1883_; 
v___x_1882_ = l_List_reverse___redArg(v_x_1876_);
v___x_1883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1882_);
return v___x_1883_;
}
else
{
lean_object* v_head_1884_; lean_object* v_tail_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1903_; 
v_head_1884_ = lean_ctor_get(v_x_1875_, 0);
v_tail_1885_ = lean_ctor_get(v_x_1875_, 1);
v_isSharedCheck_1903_ = !lean_is_exclusive(v_x_1875_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1887_ = v_x_1875_;
v_isShared_1888_ = v_isSharedCheck_1903_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_tail_1885_);
lean_inc(v_head_1884_);
lean_dec(v_x_1875_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1903_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1889_; 
v___x_1889_ = l_Lean_MVarId_assumption(v_head_1884_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_);
if (lean_obj_tag(v___x_1889_) == 0)
{
lean_object* v_a_1890_; lean_object* v___x_1892_; 
v_a_1890_ = lean_ctor_get(v___x_1889_, 0);
lean_inc(v_a_1890_);
lean_dec_ref_known(v___x_1889_, 1);
if (v_isShared_1888_ == 0)
{
lean_ctor_set(v___x_1887_, 1, v_x_1876_);
lean_ctor_set(v___x_1887_, 0, v_a_1890_);
v___x_1892_ = v___x_1887_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_a_1890_);
lean_ctor_set(v_reuseFailAlloc_1894_, 1, v_x_1876_);
v___x_1892_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
v_x_1875_ = v_tail_1885_;
v_x_1876_ = v___x_1892_;
goto _start;
}
}
else
{
lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1902_; 
lean_del_object(v___x_1887_);
lean_dec(v_tail_1885_);
lean_dec(v_x_1876_);
v_a_1895_ = lean_ctor_get(v___x_1889_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1897_ = v___x_1889_;
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_dec(v___x_1889_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1900_; 
if (v_isShared_1898_ == 0)
{
v___x_1900_ = v___x_1897_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_a_1895_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Rewrites_rwLemma_spec__1___boxed(lean_object* v_x_1904_, lean_object* v_x_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_){
_start:
{
lean_object* v_res_1911_; 
v_res_1911_ = l_List_mapM_loop___at___00Lean_Meta_Rewrites_rwLemma_spec__1(v_x_1904_, v_x_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
return v_res_1911_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5(void){
_start:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1924_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_));
v___x_1925_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__4));
v___x_1926_ = l_Lean_Name_append(v___x_1925_, v___x_1924_);
return v___x_1926_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__7(void){
_start:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1928_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__6));
v___x_1929_ = l_Lean_stringToMessageData(v___x_1928_);
return v___x_1929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0(lean_object* v_weight_1931_, lean_object* v_goal_1932_, lean_object* v_target_1933_, uint8_t v_symm_1934_, uint8_t v_side_1935_, lean_object* v_lem_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_){
_start:
{
lean_object* v___y_1943_; lean_object* v___y_1944_; lean_object* v___y_1945_; lean_object* v___y_1946_; uint8_t v___y_1947_; lean_object* v___y_1968_; lean_object* v___y_1969_; lean_object* v___y_1970_; lean_object* v___y_1971_; lean_object* v___y_1972_; lean_object* v_fst_1973_; uint8_t v_snd_1974_; lean_object* v___y_1999_; uint8_t v___y_2000_; lean_object* v___y_2001_; lean_object* v___y_2002_; lean_object* v___y_2003_; lean_object* v___y_2004_; lean_object* v___y_2021_; uint8_t v___y_2022_; uint8_t v_discharge_2023_; lean_object* v___y_2024_; lean_object* v___y_2025_; lean_object* v___y_2026_; lean_object* v___y_2027_; uint8_t v___y_2031_; lean_object* v___y_2032_; lean_object* v___y_2033_; lean_object* v___y_2034_; lean_object* v___y_2035_; uint8_t v___y_2036_; lean_object* v___y_2037_; lean_object* v___y_2038_; lean_object* v___y_2039_; uint8_t v___y_2040_; lean_object* v___y_2052_; lean_object* v___y_2053_; uint8_t v___y_2054_; lean_object* v___y_2055_; lean_object* v___y_2056_; lean_object* v___y_2057_; uint8_t v___y_2058_; lean_object* v___y_2059_; lean_object* v___y_2060_; uint8_t v___y_2061_; lean_object* v___y_2073_; lean_object* v___y_2153_; lean_object* v___y_2154_; lean_object* v___y_2155_; lean_object* v___y_2156_; lean_object* v_val_2171_; 
if (lean_obj_tag(v_lem_1936_) == 0)
{
lean_object* v_val_2182_; 
v_val_2182_ = lean_ctor_get(v_lem_1936_, 0);
lean_inc(v_val_2182_);
lean_dec_ref_known(v_lem_1936_, 1);
v_val_2171_ = v_val_2182_;
goto v___jp_2170_;
}
else
{
lean_object* v_val_2183_; lean_object* v___x_2184_; 
v_val_2183_ = lean_ctor_get(v_lem_1936_, 0);
lean_inc(v_val_2183_);
lean_dec_ref_known(v_lem_1936_, 1);
v___x_2184_ = l_Lean_Meta_saveState___redArg(v___y_1938_, v___y_1940_);
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_object* v_a_2185_; lean_object* v___x_2186_; 
v_a_2185_ = lean_ctor_get(v___x_2184_, 0);
lean_inc(v_a_2185_);
lean_dec_ref_known(v___x_2184_, 1);
v___x_2186_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_val_2183_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
if (lean_obj_tag(v___x_2186_) == 0)
{
lean_object* v_a_2187_; 
lean_dec(v_a_2185_);
v_a_2187_ = lean_ctor_get(v___x_2186_, 0);
lean_inc(v_a_2187_);
lean_dec_ref_known(v___x_2186_, 1);
v_val_2171_ = v_a_2187_;
goto v___jp_2170_;
}
else
{
lean_object* v_a_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2217_; 
lean_dec_ref(v_target_1933_);
lean_dec(v_goal_1932_);
lean_dec(v_weight_1931_);
v_a_2188_ = lean_ctor_get(v___x_2186_, 0);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2186_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2190_ = v___x_2186_;
v_isShared_2191_ = v_isSharedCheck_2217_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_a_2188_);
lean_dec(v___x_2186_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2217_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
uint8_t v___y_2193_; uint8_t v___x_2215_; 
v___x_2215_ = l_Lean_Exception_isInterrupt(v_a_2188_);
if (v___x_2215_ == 0)
{
uint8_t v___x_2216_; 
lean_inc(v_a_2188_);
v___x_2216_ = l_Lean_Exception_isRuntime(v_a_2188_);
v___y_2193_ = v___x_2216_;
goto v___jp_2192_;
}
else
{
v___y_2193_ = v___x_2215_;
goto v___jp_2192_;
}
v___jp_2192_:
{
if (v___y_2193_ == 0)
{
lean_object* v___x_2194_; 
lean_del_object(v___x_2190_);
lean_dec(v_a_2188_);
v___x_2194_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2185_, v___y_1938_, v___y_1940_);
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2202_; 
v_isSharedCheck_2202_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2202_ == 0)
{
lean_object* v_unused_2203_; 
v_unused_2203_ = lean_ctor_get(v___x_2194_, 0);
lean_dec(v_unused_2203_);
v___x_2196_ = v___x_2194_;
v_isShared_2197_ = v_isSharedCheck_2202_;
goto v_resetjp_2195_;
}
else
{
lean_dec(v___x_2194_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2202_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v___x_2198_; lean_object* v___x_2200_; 
v___x_2198_ = lean_box(0);
if (v_isShared_2197_ == 0)
{
lean_ctor_set(v___x_2196_, 0, v___x_2198_);
v___x_2200_ = v___x_2196_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v___x_2198_);
v___x_2200_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
return v___x_2200_;
}
}
}
else
{
lean_object* v_a_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2211_; 
v_a_2204_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2206_ = v___x_2194_;
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_a_2204_);
lean_dec(v___x_2194_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2209_; 
if (v_isShared_2207_ == 0)
{
v___x_2209_ = v___x_2206_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v_a_2204_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
}
else
{
lean_object* v___x_2213_; 
lean_dec(v_a_2185_);
if (v_isShared_2191_ == 0)
{
v___x_2213_ = v___x_2190_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v_a_2188_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
}
}
}
}
else
{
lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2225_; 
lean_dec(v_val_2183_);
lean_dec_ref(v_target_1933_);
lean_dec(v_goal_1932_);
lean_dec(v_weight_1931_);
v_a_2218_ = lean_ctor_get(v___x_2184_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2220_ = v___x_2184_;
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_dec(v___x_2184_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2223_; 
if (v_isShared_2221_ == 0)
{
v___x_2223_ = v___x_2220_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_a_2218_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
}
v___jp_1942_:
{
if (v___y_1947_ == 0)
{
lean_object* v___x_1948_; 
lean_dec_ref(v___y_1946_);
v___x_1948_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1945_, v___y_1944_, v___y_1943_);
if (lean_obj_tag(v___x_1948_) == 0)
{
lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1956_; 
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1948_);
if (v_isSharedCheck_1956_ == 0)
{
lean_object* v_unused_1957_; 
v_unused_1957_ = lean_ctor_get(v___x_1948_, 0);
lean_dec(v_unused_1957_);
v___x_1950_ = v___x_1948_;
v_isShared_1951_ = v_isSharedCheck_1956_;
goto v_resetjp_1949_;
}
else
{
lean_dec(v___x_1948_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1956_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1952_; lean_object* v___x_1954_; 
v___x_1952_ = lean_box(0);
if (v_isShared_1951_ == 0)
{
lean_ctor_set(v___x_1950_, 0, v___x_1952_);
v___x_1954_ = v___x_1950_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v___x_1952_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
else
{
lean_object* v_a_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1965_; 
v_a_1958_ = lean_ctor_get(v___x_1948_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1948_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1960_ = v___x_1948_;
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_a_1958_);
lean_dec(v___x_1948_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1963_; 
if (v_isShared_1961_ == 0)
{
v___x_1963_ = v___x_1960_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_a_1958_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
}
else
{
lean_object* v___x_1966_; 
lean_dec_ref(v___y_1945_);
v___x_1966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1966_, 0, v___y_1946_);
return v___x_1966_;
}
}
v___jp_1967_:
{
lean_object* v___x_1975_; lean_object* v_mctx_1976_; lean_object* v_eNew_1977_; lean_object* v___x_1978_; 
v___x_1975_ = lean_st_ref_get(v___y_1968_);
v_mctx_1976_ = lean_ctor_get(v___x_1975_, 0);
lean_inc_ref_n(v_mctx_1976_, 2);
lean_dec(v___x_1975_);
v_eNew_1977_ = lean_ctor_get(v___y_1969_, 0);
lean_inc_ref(v_eNew_1977_);
v___x_1978_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(v_mctx_1976_, v_eNew_1977_, v___y_1972_, v___y_1968_, v___y_1970_, v___y_1971_);
if (lean_obj_tag(v___x_1978_) == 0)
{
lean_object* v_a_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_1989_; 
v_a_1979_ = lean_ctor_get(v___x_1978_, 0);
v_isSharedCheck_1989_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1981_ = v___x_1978_;
v_isShared_1982_ = v_isSharedCheck_1989_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_a_1979_);
lean_dec(v___x_1978_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_1989_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___x_1983_; uint8_t v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1987_; 
v___x_1983_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1983_, 0, v_fst_1973_);
lean_ctor_set(v___x_1983_, 1, v_weight_1931_);
lean_ctor_set(v___x_1983_, 2, v___y_1969_);
lean_ctor_set(v___x_1983_, 3, v_mctx_1976_);
lean_ctor_set_uint8(v___x_1983_, sizeof(void*)*4, v_snd_1974_);
v___x_1984_ = lean_unbox(v_a_1979_);
lean_dec(v_a_1979_);
lean_ctor_set_uint8(v___x_1983_, sizeof(void*)*4 + 1, v___x_1984_);
v___x_1985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1985_, 0, v___x_1983_);
if (v_isShared_1982_ == 0)
{
lean_ctor_set(v___x_1981_, 0, v___x_1985_);
v___x_1987_ = v___x_1981_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v___x_1985_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
return v___x_1987_;
}
}
}
else
{
lean_object* v_a_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_1997_; 
lean_dec_ref(v_mctx_1976_);
lean_dec_ref(v_fst_1973_);
lean_dec_ref(v___y_1969_);
lean_dec(v_weight_1931_);
v_a_1990_ = lean_ctor_get(v___x_1978_, 0);
v_isSharedCheck_1997_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1992_ = v___x_1978_;
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_a_1990_);
lean_dec(v___x_1978_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1995_; 
if (v_isShared_1993_ == 0)
{
v___x_1995_ = v___x_1992_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_a_1990_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
return v___x_1995_;
}
}
}
}
v___jp_1998_:
{
lean_object* v___x_2005_; 
v___x_2005_ = l_Lean_Meta_Rewrites_rewriteResultLemma(v___y_1999_);
if (lean_obj_tag(v___x_2005_) == 1)
{
lean_object* v_val_2006_; lean_object* v___x_2007_; lean_object* v_a_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; uint8_t v___x_2011_; 
v_val_2006_ = lean_ctor_get(v___x_2005_, 0);
lean_inc(v_val_2006_);
lean_dec_ref_known(v___x_2005_, 1);
v___x_2007_ = l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg(v_val_2006_, v___y_2002_);
v_a_2008_ = lean_ctor_get(v___x_2007_, 0);
lean_inc(v_a_2008_);
lean_dec_ref(v___x_2007_);
v___x_2009_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__1));
v___x_2010_ = lean_unsigned_to_nat(4u);
v___x_2011_ = l_Lean_Expr_isAppOfArity(v_a_2008_, v___x_2009_, v___x_2010_);
if (v___x_2011_ == 0)
{
v___y_1968_ = v___y_2002_;
v___y_1969_ = v___y_1999_;
v___y_1970_ = v___y_2003_;
v___y_1971_ = v___y_2004_;
v___y_1972_ = v___y_2001_;
v_fst_1973_ = v_a_2008_;
v_snd_1974_ = v___x_2011_;
goto v___jp_1967_;
}
else
{
lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; 
v___x_2012_ = lean_unsigned_to_nat(3u);
v___x_2013_ = l_Lean_Expr_getAppNumArgs(v_a_2008_);
v___x_2014_ = lean_nat_sub(v___x_2013_, v___x_2012_);
lean_dec(v___x_2013_);
v___x_2015_ = lean_unsigned_to_nat(1u);
v___x_2016_ = lean_nat_sub(v___x_2014_, v___x_2015_);
lean_dec(v___x_2014_);
v___x_2017_ = l_Lean_Expr_getRevArg_x21(v_a_2008_, v___x_2016_);
lean_dec(v_a_2008_);
v___y_1968_ = v___y_2002_;
v___y_1969_ = v___y_1999_;
v___y_1970_ = v___y_2003_;
v___y_1971_ = v___y_2004_;
v___y_1972_ = v___y_2001_;
v_fst_1973_ = v___x_2017_;
v_snd_1974_ = v___y_2000_;
goto v___jp_1967_;
}
}
else
{
lean_object* v___x_2018_; lean_object* v___x_2019_; 
lean_dec(v___x_2005_);
lean_dec_ref(v___y_1999_);
lean_dec(v_weight_1931_);
v___x_2018_ = lean_box(0);
v___x_2019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2019_, 0, v___x_2018_);
return v___x_2019_;
}
}
v___jp_2020_:
{
if (v_discharge_2023_ == 0)
{
lean_object* v___x_2028_; lean_object* v___x_2029_; 
lean_dec_ref(v___y_2021_);
lean_dec(v_weight_1931_);
v___x_2028_ = lean_box(0);
v___x_2029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2029_, 0, v___x_2028_);
return v___x_2029_;
}
else
{
v___y_1999_ = v___y_2021_;
v___y_2000_ = v___y_2022_;
v___y_2001_ = v___y_2024_;
v___y_2002_ = v___y_2025_;
v___y_2003_ = v___y_2026_;
v___y_2004_ = v___y_2027_;
goto v___jp_1998_;
}
}
v___jp_2030_:
{
if (v___y_2040_ == 0)
{
lean_object* v___x_2041_; 
lean_dec_ref(v___y_2037_);
v___x_2041_ = l_Lean_Meta_SavedState_restore___redArg(v___y_2035_, v___y_2033_, v___y_2032_);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_dec_ref_known(v___x_2041_, 1);
v___y_2021_ = v___y_2034_;
v___y_2022_ = v___y_2036_;
v_discharge_2023_ = v___y_2031_;
v___y_2024_ = v___y_2039_;
v___y_2025_ = v___y_2033_;
v___y_2026_ = v___y_2038_;
v___y_2027_ = v___y_2032_;
goto v___jp_2020_;
}
else
{
lean_object* v_a_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2049_; 
lean_dec_ref(v___y_2034_);
lean_dec(v_weight_1931_);
v_a_2042_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2044_ = v___x_2041_;
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_a_2042_);
lean_dec(v___x_2041_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2047_; 
if (v_isShared_2045_ == 0)
{
v___x_2047_ = v___x_2044_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_a_2042_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
}
}
else
{
lean_object* v___x_2050_; 
lean_dec_ref(v___y_2035_);
lean_dec_ref(v___y_2034_);
lean_dec(v_weight_1931_);
v___x_2050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2050_, 0, v___y_2037_);
return v___x_2050_;
}
}
v___jp_2051_:
{
if (v___y_2061_ == 0)
{
lean_object* v___x_2062_; 
lean_dec_ref(v___y_2052_);
v___x_2062_ = l_Lean_Meta_SavedState_restore___redArg(v___y_2053_, v___y_2056_, v___y_2055_);
if (lean_obj_tag(v___x_2062_) == 0)
{
lean_dec_ref_known(v___x_2062_, 1);
v___y_2021_ = v___y_2057_;
v___y_2022_ = v___y_2058_;
v_discharge_2023_ = v___y_2054_;
v___y_2024_ = v___y_2060_;
v___y_2025_ = v___y_2056_;
v___y_2026_ = v___y_2059_;
v___y_2027_ = v___y_2055_;
goto v___jp_2020_;
}
else
{
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2070_; 
lean_dec_ref(v___y_2057_);
lean_dec(v_weight_1931_);
v_a_2063_ = lean_ctor_get(v___x_2062_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2065_ = v___x_2062_;
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___x_2062_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2068_; 
if (v_isShared_2066_ == 0)
{
v___x_2068_ = v___x_2065_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v_a_2063_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
return v___x_2068_;
}
}
}
}
else
{
lean_object* v___x_2071_; 
lean_dec_ref(v___y_2057_);
lean_dec_ref(v___y_2053_);
lean_dec(v_weight_1931_);
v___x_2071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2071_, 0, v___y_2052_);
return v___x_2071_;
}
}
v___jp_2072_:
{
uint8_t v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; 
v___x_2074_ = 1;
v___x_2075_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__2));
v___x_2076_ = l_Lean_Meta_saveState___redArg(v___y_1938_, v___y_1940_);
if (lean_obj_tag(v___x_2076_) == 0)
{
lean_object* v_a_2077_; lean_object* v___x_2078_; 
v_a_2077_ = lean_ctor_get(v___x_2076_, 0);
lean_inc(v_a_2077_);
lean_dec_ref_known(v___x_2076_, 1);
lean_inc_ref(v___y_2073_);
v___x_2078_ = l_Lean_MVarId_rewrite(v_goal_1932_, v_target_1933_, v___y_2073_, v_symm_1934_, v___x_2075_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
if (lean_obj_tag(v___x_2078_) == 0)
{
lean_object* v_a_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2140_; 
lean_dec(v_a_2077_);
v_a_2079_ = lean_ctor_get(v___x_2078_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2078_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2081_ = v___x_2078_;
v_isShared_2082_ = v_isSharedCheck_2140_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_a_2079_);
lean_dec(v___x_2078_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2140_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v_eNew_2083_; lean_object* v_mvarIds_2084_; uint8_t v___x_2085_; 
v_eNew_2083_ = lean_ctor_get(v_a_2079_, 0);
v_mvarIds_2084_ = lean_ctor_get(v_a_2079_, 2);
v___x_2085_ = l_List_isEmpty___redArg(v_mvarIds_2084_);
if (v___x_2085_ == 0)
{
lean_del_object(v___x_2081_);
lean_dec_ref(v___y_2073_);
switch(v_side_1935_)
{
case 0:
{
v___y_2021_ = v_a_2079_;
v___y_2022_ = v___x_2074_;
v_discharge_2023_ = v___x_2085_;
v___y_2024_ = v___y_1937_;
v___y_2025_ = v___y_1938_;
v___y_2026_ = v___y_1939_;
v___y_2027_ = v___y_1940_;
goto v___jp_2020_;
}
case 1:
{
lean_object* v___x_2086_; lean_object* v___x_2087_; 
v___x_2086_ = lean_box(0);
v___x_2087_ = l_Lean_Meta_saveState___redArg(v___y_1938_, v___y_1940_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v_a_2088_; lean_object* v___x_2089_; 
v_a_2088_ = lean_ctor_get(v___x_2087_, 0);
lean_inc(v_a_2088_);
lean_dec_ref_known(v___x_2087_, 1);
lean_inc(v_mvarIds_2084_);
v___x_2089_ = l_List_mapM_loop___at___00Lean_Meta_Rewrites_rwLemma_spec__1(v_mvarIds_2084_, v___x_2086_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
if (lean_obj_tag(v___x_2089_) == 0)
{
lean_dec_ref_known(v___x_2089_, 1);
lean_dec(v_a_2088_);
v___y_1999_ = v_a_2079_;
v___y_2000_ = v___x_2074_;
v___y_2001_ = v___y_1937_;
v___y_2002_ = v___y_1938_;
v___y_2003_ = v___y_1939_;
v___y_2004_ = v___y_1940_;
goto v___jp_1998_;
}
else
{
lean_object* v_a_2090_; uint8_t v___x_2091_; 
v_a_2090_ = lean_ctor_get(v___x_2089_, 0);
lean_inc(v_a_2090_);
lean_dec_ref_known(v___x_2089_, 1);
v___x_2091_ = l_Lean_Exception_isInterrupt(v_a_2090_);
if (v___x_2091_ == 0)
{
uint8_t v___x_2092_; 
lean_inc(v_a_2090_);
v___x_2092_ = l_Lean_Exception_isRuntime(v_a_2090_);
v___y_2052_ = v_a_2090_;
v___y_2053_ = v_a_2088_;
v___y_2054_ = v___x_2085_;
v___y_2055_ = v___y_1940_;
v___y_2056_ = v___y_1938_;
v___y_2057_ = v_a_2079_;
v___y_2058_ = v___x_2074_;
v___y_2059_ = v___y_1939_;
v___y_2060_ = v___y_1937_;
v___y_2061_ = v___x_2092_;
goto v___jp_2051_;
}
else
{
v___y_2052_ = v_a_2090_;
v___y_2053_ = v_a_2088_;
v___y_2054_ = v___x_2085_;
v___y_2055_ = v___y_1940_;
v___y_2056_ = v___y_1938_;
v___y_2057_ = v_a_2079_;
v___y_2058_ = v___x_2074_;
v___y_2059_ = v___y_1939_;
v___y_2060_ = v___y_1937_;
v___y_2061_ = v___x_2091_;
goto v___jp_2051_;
}
}
}
else
{
lean_object* v_a_2093_; lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2100_; 
lean_dec(v_a_2079_);
lean_dec(v_weight_1931_);
v_a_2093_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2100_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2100_ == 0)
{
v___x_2095_ = v___x_2087_;
v_isShared_2096_ = v_isSharedCheck_2100_;
goto v_resetjp_2094_;
}
else
{
lean_inc(v_a_2093_);
lean_dec(v___x_2087_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2100_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
lean_object* v___x_2098_; 
if (v_isShared_2096_ == 0)
{
v___x_2098_ = v___x_2095_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v_a_2093_);
v___x_2098_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
return v___x_2098_;
}
}
}
}
default: 
{
lean_object* v___x_2101_; lean_object* v___x_2102_; 
v___x_2101_ = lean_unsigned_to_nat(6u);
v___x_2102_ = l_Lean_Meta_saveState___redArg(v___y_1938_, v___y_1940_);
if (lean_obj_tag(v___x_2102_) == 0)
{
lean_object* v_a_2103_; lean_object* v___x_2104_; 
v_a_2103_ = lean_ctor_get(v___x_2102_, 0);
lean_inc(v_a_2103_);
lean_dec_ref_known(v___x_2102_, 1);
lean_inc(v_mvarIds_2084_);
v___x_2104_ = l_Lean_Meta_Rewrites_solveByElim(v_mvarIds_2084_, v___x_2101_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
if (lean_obj_tag(v___x_2104_) == 0)
{
lean_dec_ref_known(v___x_2104_, 1);
lean_dec(v_a_2103_);
v___y_1999_ = v_a_2079_;
v___y_2000_ = v___x_2074_;
v___y_2001_ = v___y_1937_;
v___y_2002_ = v___y_1938_;
v___y_2003_ = v___y_1939_;
v___y_2004_ = v___y_1940_;
goto v___jp_1998_;
}
else
{
lean_object* v_a_2105_; uint8_t v___x_2106_; 
v_a_2105_ = lean_ctor_get(v___x_2104_, 0);
lean_inc(v_a_2105_);
lean_dec_ref_known(v___x_2104_, 1);
v___x_2106_ = l_Lean_Exception_isInterrupt(v_a_2105_);
if (v___x_2106_ == 0)
{
uint8_t v___x_2107_; 
lean_inc(v_a_2105_);
v___x_2107_ = l_Lean_Exception_isRuntime(v_a_2105_);
v___y_2031_ = v___x_2085_;
v___y_2032_ = v___y_1940_;
v___y_2033_ = v___y_1938_;
v___y_2034_ = v_a_2079_;
v___y_2035_ = v_a_2103_;
v___y_2036_ = v___x_2074_;
v___y_2037_ = v_a_2105_;
v___y_2038_ = v___y_1939_;
v___y_2039_ = v___y_1937_;
v___y_2040_ = v___x_2107_;
goto v___jp_2030_;
}
else
{
v___y_2031_ = v___x_2085_;
v___y_2032_ = v___y_1940_;
v___y_2033_ = v___y_1938_;
v___y_2034_ = v_a_2079_;
v___y_2035_ = v_a_2103_;
v___y_2036_ = v___x_2074_;
v___y_2037_ = v_a_2105_;
v___y_2038_ = v___y_1939_;
v___y_2039_ = v___y_1937_;
v___y_2040_ = v___x_2106_;
goto v___jp_2030_;
}
}
}
else
{
lean_object* v_a_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2115_; 
lean_dec(v_a_2079_);
lean_dec(v_weight_1931_);
v_a_2108_ = lean_ctor_get(v___x_2102_, 0);
v_isSharedCheck_2115_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2110_ = v___x_2102_;
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_a_2108_);
lean_dec(v___x_2102_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v___x_2113_; 
if (v_isShared_2111_ == 0)
{
v___x_2113_ = v___x_2110_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v_a_2108_);
v___x_2113_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
return v___x_2113_;
}
}
}
}
}
}
else
{
lean_object* v___x_2116_; lean_object* v_mctx_2117_; lean_object* v___x_2118_; 
v___x_2116_ = lean_st_ref_get(v___y_1938_);
v_mctx_2117_ = lean_ctor_get(v___x_2116_, 0);
lean_inc_ref_n(v_mctx_2117_, 2);
lean_dec(v___x_2116_);
lean_inc_ref(v_eNew_2083_);
v___x_2118_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(v_mctx_2117_, v_eNew_2083_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2131_; 
v_a_2119_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2121_ = v___x_2118_;
v_isShared_2122_ = v_isSharedCheck_2131_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_2118_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2131_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2123_; uint8_t v___x_2124_; lean_object* v___x_2126_; 
v___x_2123_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2123_, 0, v___y_2073_);
lean_ctor_set(v___x_2123_, 1, v_weight_1931_);
lean_ctor_set(v___x_2123_, 2, v_a_2079_);
lean_ctor_set(v___x_2123_, 3, v_mctx_2117_);
lean_ctor_set_uint8(v___x_2123_, sizeof(void*)*4, v_symm_1934_);
v___x_2124_ = lean_unbox(v_a_2119_);
lean_dec(v_a_2119_);
lean_ctor_set_uint8(v___x_2123_, sizeof(void*)*4 + 1, v___x_2124_);
if (v_isShared_2082_ == 0)
{
lean_ctor_set_tag(v___x_2081_, 1);
lean_ctor_set(v___x_2081_, 0, v___x_2123_);
v___x_2126_ = v___x_2081_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v___x_2123_);
v___x_2126_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
lean_object* v___x_2128_; 
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 0, v___x_2126_);
v___x_2128_ = v___x_2121_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v___x_2126_);
v___x_2128_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
return v___x_2128_;
}
}
}
}
else
{
lean_object* v_a_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2139_; 
lean_dec_ref(v_mctx_2117_);
lean_del_object(v___x_2081_);
lean_dec(v_a_2079_);
lean_dec_ref(v___y_2073_);
lean_dec(v_weight_1931_);
v_a_2132_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2139_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2134_ = v___x_2118_;
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_a_2132_);
lean_dec(v___x_2118_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2137_; 
if (v_isShared_2135_ == 0)
{
v___x_2137_ = v___x_2134_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_a_2132_);
v___x_2137_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
return v___x_2137_;
}
}
}
}
}
}
else
{
lean_object* v_a_2141_; uint8_t v___x_2142_; 
lean_dec_ref(v___y_2073_);
lean_dec(v_weight_1931_);
v_a_2141_ = lean_ctor_get(v___x_2078_, 0);
lean_inc(v_a_2141_);
lean_dec_ref_known(v___x_2078_, 1);
v___x_2142_ = l_Lean_Exception_isInterrupt(v_a_2141_);
if (v___x_2142_ == 0)
{
uint8_t v___x_2143_; 
lean_inc(v_a_2141_);
v___x_2143_ = l_Lean_Exception_isRuntime(v_a_2141_);
v___y_1943_ = v___y_1940_;
v___y_1944_ = v___y_1938_;
v___y_1945_ = v_a_2077_;
v___y_1946_ = v_a_2141_;
v___y_1947_ = v___x_2143_;
goto v___jp_1942_;
}
else
{
v___y_1943_ = v___y_1940_;
v___y_1944_ = v___y_1938_;
v___y_1945_ = v_a_2077_;
v___y_1946_ = v_a_2141_;
v___y_1947_ = v___x_2142_;
goto v___jp_1942_;
}
}
}
else
{
lean_object* v_a_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2151_; 
lean_dec_ref(v___y_2073_);
lean_dec_ref(v_target_1933_);
lean_dec(v_goal_1932_);
lean_dec(v_weight_1931_);
v_a_2144_ = lean_ctor_get(v___x_2076_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2146_ = v___x_2076_;
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_a_2144_);
lean_dec(v___x_2076_);
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
v___jp_2152_:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; 
lean_inc_ref(v___y_2156_);
v___x_2157_ = l_Lean_stringToMessageData(v___y_2156_);
lean_inc_ref(v___y_2154_);
v___x_2158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2158_, 0, v___y_2154_);
lean_ctor_set(v___x_2158_, 1, v___x_2157_);
lean_inc_ref(v___y_2155_);
v___x_2159_ = l_Lean_MessageData_ofExpr(v___y_2155_);
v___x_2160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2158_);
lean_ctor_set(v___x_2160_, 1, v___x_2159_);
lean_inc(v___y_2153_);
v___x_2161_ = l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2(v___y_2153_, v___x_2160_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
if (lean_obj_tag(v___x_2161_) == 0)
{
lean_dec_ref_known(v___x_2161_, 1);
v___y_2073_ = v___y_2155_;
goto v___jp_2072_;
}
else
{
lean_object* v_a_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2169_; 
lean_dec_ref(v___y_2155_);
lean_dec_ref(v_target_1933_);
lean_dec(v_goal_1932_);
lean_dec(v_weight_1931_);
v_a_2162_ = lean_ctor_get(v___x_2161_, 0);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2161_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2164_ = v___x_2161_;
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_a_2162_);
lean_dec(v___x_2161_);
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
v___jp_2170_:
{
lean_object* v_toCold_2172_; lean_object* v_options_2173_; uint8_t v_hasTrace_2174_; 
v_toCold_2172_ = lean_ctor_get(v___y_1939_, 0);
v_options_2173_ = lean_ctor_get(v_toCold_2172_, 2);
v_hasTrace_2174_ = lean_ctor_get_uint8(v_options_2173_, sizeof(void*)*1);
if (v_hasTrace_2174_ == 0)
{
v___y_2073_ = v_val_2171_;
goto v___jp_2072_;
}
else
{
lean_object* v_inheritedTraceOptions_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; uint8_t v___x_2178_; 
v_inheritedTraceOptions_2175_ = lean_ctor_get(v_toCold_2172_, 11);
v___x_2176_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_));
v___x_2177_ = lean_obj_once(&l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5, &l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5_once, _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5);
v___x_2178_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2175_, v_options_2173_, v___x_2177_);
if (v___x_2178_ == 0)
{
v___y_2073_ = v_val_2171_;
goto v___jp_2072_;
}
else
{
lean_object* v___x_2179_; 
v___x_2179_ = lean_obj_once(&l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__7, &l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__7_once, _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__7);
if (v_symm_1934_ == 0)
{
lean_object* v___x_2180_; 
v___x_2180_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__1));
v___y_2153_ = v___x_2176_;
v___y_2154_ = v___x_2179_;
v___y_2155_ = v_val_2171_;
v___y_2156_ = v___x_2180_;
goto v___jp_2152_;
}
else
{
lean_object* v___x_2181_; 
v___x_2181_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__8));
v___y_2153_ = v___x_2176_;
v___y_2154_ = v___x_2179_;
v___y_2155_ = v_val_2171_;
v___y_2156_ = v___x_2181_;
goto v___jp_2152_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0___boxed(lean_object* v_weight_2226_, lean_object* v_goal_2227_, lean_object* v_target_2228_, lean_object* v_symm_2229_, lean_object* v_side_2230_, lean_object* v_lem_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_){
_start:
{
uint8_t v_symm_boxed_2237_; uint8_t v_side_boxed_2238_; lean_object* v_res_2239_; 
v_symm_boxed_2237_ = lean_unbox(v_symm_2229_);
v_side_boxed_2238_ = lean_unbox(v_side_2230_);
v_res_2239_ = l_Lean_Meta_Rewrites_rwLemma___lam__0(v_weight_2226_, v_goal_2227_, v_target_2228_, v_symm_boxed_2237_, v_side_boxed_2238_, v_lem_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
lean_dec(v___y_2235_);
lean_dec_ref(v___y_2234_);
lean_dec(v___y_2233_);
lean_dec_ref(v___y_2232_);
return v_res_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma(lean_object* v_ctx_2240_, lean_object* v_goal_2241_, lean_object* v_target_2242_, uint8_t v_side_2243_, lean_object* v_lem_2244_, uint8_t v_symm_2245_, lean_object* v_weight_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_){
_start:
{
lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___f_2254_; lean_object* v___x_2255_; 
v___x_2252_ = lean_box(v_symm_2245_);
v___x_2253_ = lean_box(v_side_2243_);
v___f_2254_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___boxed), 11, 6);
lean_closure_set(v___f_2254_, 0, v_weight_2246_);
lean_closure_set(v___f_2254_, 1, v_goal_2241_);
lean_closure_set(v___f_2254_, 2, v_target_2242_);
lean_closure_set(v___f_2254_, 3, v___x_2252_);
lean_closure_set(v___f_2254_, 4, v___x_2253_);
lean_closure_set(v___f_2254_, 5, v_lem_2244_);
v___x_2255_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg(v_ctx_2240_, v___f_2254_, v_a_2247_, v_a_2248_, v_a_2249_, v_a_2250_);
return v___x_2255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___boxed(lean_object* v_ctx_2256_, lean_object* v_goal_2257_, lean_object* v_target_2258_, lean_object* v_side_2259_, lean_object* v_lem_2260_, lean_object* v_symm_2261_, lean_object* v_weight_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_){
_start:
{
uint8_t v_side_boxed_2268_; uint8_t v_symm_boxed_2269_; lean_object* v_res_2270_; 
v_side_boxed_2268_ = lean_unbox(v_side_2259_);
v_symm_boxed_2269_ = lean_unbox(v_symm_2261_);
v_res_2270_ = l_Lean_Meta_Rewrites_rwLemma(v_ctx_2256_, v_goal_2257_, v_target_2258_, v_side_boxed_2268_, v_lem_2260_, v_symm_boxed_2269_, v_weight_2262_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_);
lean_dec(v_a_2266_);
lean_dec_ref(v_a_2265_);
lean_dec(v_a_2264_);
lean_dec_ref(v_a_2263_);
return v_res_2270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(lean_object* v_type_2271_, lean_object* v_k_2272_, uint8_t v_cleanupAnnotations_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_){
_start:
{
lean_object* v___f_2279_; uint8_t v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___f_2279_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2279_, 0, v_k_2272_);
v___x_2280_ = 0;
v___x_2281_ = lean_box(0);
v___x_2282_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_2280_, v___x_2281_, v_type_2271_, v___f_2279_, v_cleanupAnnotations_2273_, v___x_2280_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_);
if (lean_obj_tag(v___x_2282_) == 0)
{
lean_object* v_a_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2290_; 
v_a_2283_ = lean_ctor_get(v___x_2282_, 0);
v_isSharedCheck_2290_ = !lean_is_exclusive(v___x_2282_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2285_ = v___x_2282_;
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_a_2283_);
lean_dec(v___x_2282_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2288_; 
if (v_isShared_2286_ == 0)
{
v___x_2288_ = v___x_2285_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v_a_2283_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
return v___x_2288_;
}
}
}
else
{
lean_object* v_a_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2298_; 
v_a_2291_ = lean_ctor_get(v___x_2282_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2282_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2293_ = v___x_2282_;
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_a_2291_);
lean_dec(v___x_2282_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2296_; 
if (v_isShared_2294_ == 0)
{
v___x_2296_ = v___x_2293_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_a_2291_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg___boxed(lean_object* v_type_2299_, lean_object* v_k_2300_, lean_object* v_cleanupAnnotations_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2307_; lean_object* v_res_2308_; 
v_cleanupAnnotations_boxed_2307_ = lean_unbox(v_cleanupAnnotations_2301_);
v_res_2308_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(v_type_2299_, v_k_2300_, v_cleanupAnnotations_boxed_2307_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_);
lean_dec(v___y_2305_);
lean_dec_ref(v___y_2304_);
lean_dec(v___y_2303_);
lean_dec_ref(v___y_2302_);
return v_res_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1(lean_object* v_00_u03b1_2309_, lean_object* v_type_2310_, lean_object* v_k_2311_, uint8_t v_cleanupAnnotations_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_){
_start:
{
lean_object* v___x_2318_; 
v___x_2318_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(v_type_2310_, v_k_2311_, v_cleanupAnnotations_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
return v___x_2318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___boxed(lean_object* v_00_u03b1_2319_, lean_object* v_type_2320_, lean_object* v_k_2321_, lean_object* v_cleanupAnnotations_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2328_; lean_object* v_res_2329_; 
v_cleanupAnnotations_boxed_2328_ = lean_unbox(v_cleanupAnnotations_2322_);
v_res_2329_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1(v_00_u03b1_2319_, v_type_2320_, v_k_2321_, v_cleanupAnnotations_boxed_2328_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_);
lean_dec(v___y_2326_);
lean_dec_ref(v___y_2325_);
lean_dec(v___y_2324_);
lean_dec_ref(v___y_2323_);
return v_res_2329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(lean_object* v_e_2330_, lean_object* v_k_2331_, uint8_t v_cleanupAnnotations_2332_, uint8_t v_preserveNondepLet_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_){
_start:
{
lean_object* v___f_2339_; uint8_t v___x_2340_; uint8_t v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; 
v___f_2339_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2339_, 0, v_k_2331_);
v___x_2340_ = 1;
v___x_2341_ = 0;
v___x_2342_ = lean_box(0);
v___x_2343_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2330_, v___x_2340_, v___x_2340_, v_preserveNondepLet_2333_, v___x_2341_, v___x_2342_, v___f_2339_, v_cleanupAnnotations_2332_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_);
if (lean_obj_tag(v___x_2343_) == 0)
{
lean_object* v_a_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2351_; 
v_a_2344_ = lean_ctor_get(v___x_2343_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___x_2343_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2346_ = v___x_2343_;
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_a_2344_);
lean_dec(v___x_2343_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v___x_2349_; 
if (v_isShared_2347_ == 0)
{
v___x_2349_ = v___x_2346_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v_a_2344_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
}
}
}
else
{
lean_object* v_a_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2359_; 
v_a_2352_ = lean_ctor_get(v___x_2343_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2343_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2354_ = v___x_2343_;
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_a_2352_);
lean_dec(v___x_2343_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2357_; 
if (v_isShared_2355_ == 0)
{
v___x_2357_ = v___x_2354_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_a_2352_);
v___x_2357_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
return v___x_2357_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg___boxed(lean_object* v_e_2360_, lean_object* v_k_2361_, lean_object* v_cleanupAnnotations_2362_, lean_object* v_preserveNondepLet_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2369_; uint8_t v_preserveNondepLet_boxed_2370_; lean_object* v_res_2371_; 
v_cleanupAnnotations_boxed_2369_ = lean_unbox(v_cleanupAnnotations_2362_);
v_preserveNondepLet_boxed_2370_ = lean_unbox(v_preserveNondepLet_2363_);
v_res_2371_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(v_e_2360_, v_k_2361_, v_cleanupAnnotations_boxed_2369_, v_preserveNondepLet_boxed_2370_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_);
lean_dec(v___y_2367_);
lean_dec_ref(v___y_2366_);
lean_dec(v___y_2365_);
lean_dec_ref(v___y_2364_);
return v_res_2371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2(lean_object* v_00_u03b1_2372_, lean_object* v_e_2373_, lean_object* v_k_2374_, uint8_t v_cleanupAnnotations_2375_, uint8_t v_preserveNondepLet_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_){
_start:
{
lean_object* v___x_2382_; 
v___x_2382_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(v_e_2373_, v_k_2374_, v_cleanupAnnotations_2375_, v_preserveNondepLet_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_);
return v___x_2382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___boxed(lean_object* v_00_u03b1_2383_, lean_object* v_e_2384_, lean_object* v_k_2385_, lean_object* v_cleanupAnnotations_2386_, lean_object* v_preserveNondepLet_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2393_; uint8_t v_preserveNondepLet_boxed_2394_; lean_object* v_res_2395_; 
v_cleanupAnnotations_boxed_2393_ = lean_unbox(v_cleanupAnnotations_2386_);
v_preserveNondepLet_boxed_2394_ = lean_unbox(v_preserveNondepLet_2387_);
v_res_2395_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2(v_00_u03b1_2383_, v_e_2384_, v_k_2385_, v_cleanupAnnotations_boxed_2393_, v_preserveNondepLet_boxed_2394_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_);
lean_dec(v___y_2391_);
lean_dec_ref(v___y_2390_);
lean_dec(v___y_2389_);
lean_dec_ref(v___y_2388_);
return v_res_2395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(lean_object* v_f_2396_, lean_object* v_e_x27_2397_, lean_object* v_a_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_){
_start:
{
lean_object* v___x_2404_; 
lean_inc(v___y_2402_);
lean_inc_ref(v___y_2401_);
lean_inc(v___y_2400_);
lean_inc_ref(v___y_2399_);
lean_inc_ref(v_e_x27_2397_);
v___x_2404_ = lean_apply_7(v_f_2396_, v_a_2398_, v_e_x27_2397_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, lean_box(0));
if (lean_obj_tag(v___x_2404_) == 0)
{
lean_object* v_a_2405_; lean_object* v___x_2407_; uint8_t v_isShared_2408_; uint8_t v_isSharedCheck_2413_; 
v_a_2405_ = lean_ctor_get(v___x_2404_, 0);
v_isSharedCheck_2413_ = !lean_is_exclusive(v___x_2404_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2407_ = v___x_2404_;
v_isShared_2408_ = v_isSharedCheck_2413_;
goto v_resetjp_2406_;
}
else
{
lean_inc(v_a_2405_);
lean_dec(v___x_2404_);
v___x_2407_ = lean_box(0);
v_isShared_2408_ = v_isSharedCheck_2413_;
goto v_resetjp_2406_;
}
v_resetjp_2406_:
{
lean_object* v___x_2409_; lean_object* v___x_2411_; 
v___x_2409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2409_, 0, v_e_x27_2397_);
lean_ctor_set(v___x_2409_, 1, v_a_2405_);
if (v_isShared_2408_ == 0)
{
lean_ctor_set(v___x_2407_, 0, v___x_2409_);
v___x_2411_ = v___x_2407_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v___x_2409_);
v___x_2411_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
return v___x_2411_;
}
}
}
else
{
lean_object* v_a_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2421_; 
lean_dec_ref(v_e_x27_2397_);
v_a_2414_ = lean_ctor_get(v___x_2404_, 0);
v_isSharedCheck_2421_ = !lean_is_exclusive(v___x_2404_);
if (v_isSharedCheck_2421_ == 0)
{
v___x_2416_ = v___x_2404_;
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_a_2414_);
lean_dec(v___x_2404_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v___x_2419_; 
if (v_isShared_2417_ == 0)
{
v___x_2419_ = v___x_2416_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v_a_2414_);
v___x_2419_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
return v___x_2419_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0___boxed(lean_object* v_f_2422_, lean_object* v_e_x27_2423_, lean_object* v_a_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_){
_start:
{
lean_object* v_res_2430_; 
v_res_2430_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2422_, v_e_x27_2423_, v_a_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
lean_dec(v___y_2426_);
lean_dec_ref(v___y_2425_);
return v_res_2430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg(lean_object* v_f_2431_, lean_object* v_x_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_){
_start:
{
switch(lean_obj_tag(v_x_2432_))
{
case 7:
{
lean_object* v_binderName_2439_; lean_object* v_binderType_2440_; lean_object* v_body_2441_; uint8_t v_binderInfo_2442_; lean_object* v___x_2443_; 
v_binderName_2439_ = lean_ctor_get(v_x_2432_, 0);
v_binderType_2440_ = lean_ctor_get(v_x_2432_, 1);
v_body_2441_ = lean_ctor_get(v_x_2432_, 2);
v_binderInfo_2442_ = lean_ctor_get_uint8(v_x_2432_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2440_);
lean_inc_ref(v_f_2431_);
v___x_2443_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2431_, v_binderType_2440_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_);
if (lean_obj_tag(v___x_2443_) == 0)
{
lean_object* v_a_2444_; lean_object* v_fst_2445_; lean_object* v_snd_2446_; lean_object* v___x_2447_; 
v_a_2444_ = lean_ctor_get(v___x_2443_, 0);
lean_inc(v_a_2444_);
lean_dec_ref_known(v___x_2443_, 1);
v_fst_2445_ = lean_ctor_get(v_a_2444_, 0);
lean_inc(v_fst_2445_);
v_snd_2446_ = lean_ctor_get(v_a_2444_, 1);
lean_inc(v_snd_2446_);
lean_dec(v_a_2444_);
lean_inc_ref(v_body_2441_);
v___x_2447_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2431_, v_body_2441_, v_snd_2446_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_);
if (lean_obj_tag(v___x_2447_) == 0)
{
lean_object* v_a_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2476_; 
v_a_2448_ = lean_ctor_get(v___x_2447_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2447_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2450_ = v___x_2447_;
v_isShared_2451_ = v_isSharedCheck_2476_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_a_2448_);
lean_dec(v___x_2447_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2476_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v_fst_2452_; lean_object* v_snd_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2475_; 
v_fst_2452_ = lean_ctor_get(v_a_2448_, 0);
v_snd_2453_ = lean_ctor_get(v_a_2448_, 1);
v_isSharedCheck_2475_ = !lean_is_exclusive(v_a_2448_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2455_ = v_a_2448_;
v_isShared_2456_ = v_isSharedCheck_2475_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_snd_2453_);
lean_inc(v_fst_2452_);
lean_dec(v_a_2448_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2475_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v___y_2458_; size_t v___x_2465_; size_t v___x_2466_; uint8_t v___x_2467_; 
v___x_2465_ = lean_ptr_addr(v_binderType_2440_);
v___x_2466_ = lean_ptr_addr(v_fst_2445_);
v___x_2467_ = lean_usize_dec_eq(v___x_2465_, v___x_2466_);
if (v___x_2467_ == 0)
{
lean_object* v___x_2468_; 
lean_inc(v_binderName_2439_);
lean_dec_ref_known(v_x_2432_, 3);
v___x_2468_ = l_Lean_Expr_forallE___override(v_binderName_2439_, v_fst_2445_, v_fst_2452_, v_binderInfo_2442_);
v___y_2458_ = v___x_2468_;
goto v___jp_2457_;
}
else
{
size_t v___x_2469_; size_t v___x_2470_; uint8_t v___x_2471_; 
v___x_2469_ = lean_ptr_addr(v_body_2441_);
v___x_2470_ = lean_ptr_addr(v_fst_2452_);
v___x_2471_ = lean_usize_dec_eq(v___x_2469_, v___x_2470_);
if (v___x_2471_ == 0)
{
lean_object* v___x_2472_; 
lean_inc(v_binderName_2439_);
lean_dec_ref_known(v_x_2432_, 3);
v___x_2472_ = l_Lean_Expr_forallE___override(v_binderName_2439_, v_fst_2445_, v_fst_2452_, v_binderInfo_2442_);
v___y_2458_ = v___x_2472_;
goto v___jp_2457_;
}
else
{
uint8_t v___x_2473_; 
v___x_2473_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2442_, v_binderInfo_2442_);
if (v___x_2473_ == 0)
{
lean_object* v___x_2474_; 
lean_inc(v_binderName_2439_);
lean_dec_ref_known(v_x_2432_, 3);
v___x_2474_ = l_Lean_Expr_forallE___override(v_binderName_2439_, v_fst_2445_, v_fst_2452_, v_binderInfo_2442_);
v___y_2458_ = v___x_2474_;
goto v___jp_2457_;
}
else
{
lean_dec(v_fst_2452_);
lean_dec(v_fst_2445_);
v___y_2458_ = v_x_2432_;
goto v___jp_2457_;
}
}
}
v___jp_2457_:
{
lean_object* v___x_2460_; 
if (v_isShared_2456_ == 0)
{
lean_ctor_set(v___x_2455_, 0, v___y_2458_);
v___x_2460_ = v___x_2455_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v___y_2458_);
lean_ctor_set(v_reuseFailAlloc_2464_, 1, v_snd_2453_);
v___x_2460_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
lean_object* v___x_2462_; 
if (v_isShared_2451_ == 0)
{
lean_ctor_set(v___x_2450_, 0, v___x_2460_);
v___x_2462_ = v___x_2450_;
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
}
}
}
else
{
lean_dec(v_fst_2445_);
lean_dec_ref_known(v_x_2432_, 3);
return v___x_2447_;
}
}
else
{
lean_dec_ref_known(v_x_2432_, 3);
lean_dec_ref(v_f_2431_);
return v___x_2443_;
}
}
case 6:
{
lean_object* v_binderName_2477_; lean_object* v_binderType_2478_; lean_object* v_body_2479_; uint8_t v_binderInfo_2480_; lean_object* v___x_2481_; 
v_binderName_2477_ = lean_ctor_get(v_x_2432_, 0);
v_binderType_2478_ = lean_ctor_get(v_x_2432_, 1);
v_body_2479_ = lean_ctor_get(v_x_2432_, 2);
v_binderInfo_2480_ = lean_ctor_get_uint8(v_x_2432_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2478_);
lean_inc_ref(v_f_2431_);
v___x_2481_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2431_, v_binderType_2478_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_);
if (lean_obj_tag(v___x_2481_) == 0)
{
lean_object* v_a_2482_; lean_object* v_fst_2483_; lean_object* v_snd_2484_; lean_object* v___x_2485_; 
v_a_2482_ = lean_ctor_get(v___x_2481_, 0);
lean_inc(v_a_2482_);
lean_dec_ref_known(v___x_2481_, 1);
v_fst_2483_ = lean_ctor_get(v_a_2482_, 0);
lean_inc(v_fst_2483_);
v_snd_2484_ = lean_ctor_get(v_a_2482_, 1);
lean_inc(v_snd_2484_);
lean_dec(v_a_2482_);
lean_inc_ref(v_body_2479_);
v___x_2485_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2431_, v_body_2479_, v_snd_2484_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_);
if (lean_obj_tag(v___x_2485_) == 0)
{
lean_object* v_a_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2514_; 
v_a_2486_ = lean_ctor_get(v___x_2485_, 0);
v_isSharedCheck_2514_ = !lean_is_exclusive(v___x_2485_);
if (v_isSharedCheck_2514_ == 0)
{
v___x_2488_ = v___x_2485_;
v_isShared_2489_ = v_isSharedCheck_2514_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_a_2486_);
lean_dec(v___x_2485_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2514_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v_fst_2490_; lean_object* v_snd_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2513_; 
v_fst_2490_ = lean_ctor_get(v_a_2486_, 0);
v_snd_2491_ = lean_ctor_get(v_a_2486_, 1);
v_isSharedCheck_2513_ = !lean_is_exclusive(v_a_2486_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2493_ = v_a_2486_;
v_isShared_2494_ = v_isSharedCheck_2513_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_snd_2491_);
lean_inc(v_fst_2490_);
lean_dec(v_a_2486_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2513_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v___y_2496_; size_t v___x_2503_; size_t v___x_2504_; uint8_t v___x_2505_; 
v___x_2503_ = lean_ptr_addr(v_binderType_2478_);
v___x_2504_ = lean_ptr_addr(v_fst_2483_);
v___x_2505_ = lean_usize_dec_eq(v___x_2503_, v___x_2504_);
if (v___x_2505_ == 0)
{
lean_object* v___x_2506_; 
lean_inc(v_binderName_2477_);
lean_dec_ref_known(v_x_2432_, 3);
v___x_2506_ = l_Lean_Expr_lam___override(v_binderName_2477_, v_fst_2483_, v_fst_2490_, v_binderInfo_2480_);
v___y_2496_ = v___x_2506_;
goto v___jp_2495_;
}
else
{
size_t v___x_2507_; size_t v___x_2508_; uint8_t v___x_2509_; 
v___x_2507_ = lean_ptr_addr(v_body_2479_);
v___x_2508_ = lean_ptr_addr(v_fst_2490_);
v___x_2509_ = lean_usize_dec_eq(v___x_2507_, v___x_2508_);
if (v___x_2509_ == 0)
{
lean_object* v___x_2510_; 
lean_inc(v_binderName_2477_);
lean_dec_ref_known(v_x_2432_, 3);
v___x_2510_ = l_Lean_Expr_lam___override(v_binderName_2477_, v_fst_2483_, v_fst_2490_, v_binderInfo_2480_);
v___y_2496_ = v___x_2510_;
goto v___jp_2495_;
}
else
{
uint8_t v___x_2511_; 
v___x_2511_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2480_, v_binderInfo_2480_);
if (v___x_2511_ == 0)
{
lean_object* v___x_2512_; 
lean_inc(v_binderName_2477_);
lean_dec_ref_known(v_x_2432_, 3);
v___x_2512_ = l_Lean_Expr_lam___override(v_binderName_2477_, v_fst_2483_, v_fst_2490_, v_binderInfo_2480_);
v___y_2496_ = v___x_2512_;
goto v___jp_2495_;
}
else
{
lean_dec(v_fst_2490_);
lean_dec(v_fst_2483_);
v___y_2496_ = v_x_2432_;
goto v___jp_2495_;
}
}
}
v___jp_2495_:
{
lean_object* v___x_2498_; 
if (v_isShared_2494_ == 0)
{
lean_ctor_set(v___x_2493_, 0, v___y_2496_);
v___x_2498_ = v___x_2493_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v___y_2496_);
lean_ctor_set(v_reuseFailAlloc_2502_, 1, v_snd_2491_);
v___x_2498_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
lean_object* v___x_2500_; 
if (v_isShared_2489_ == 0)
{
lean_ctor_set(v___x_2488_, 0, v___x_2498_);
v___x_2500_ = v___x_2488_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v___x_2498_);
v___x_2500_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
return v___x_2500_;
}
}
}
}
}
}
else
{
lean_dec(v_fst_2483_);
lean_dec_ref_known(v_x_2432_, 3);
return v___x_2485_;
}
}
else
{
lean_dec_ref_known(v_x_2432_, 3);
lean_dec_ref(v_f_2431_);
return v___x_2481_;
}
}
case 10:
{
lean_object* v_data_2515_; lean_object* v_expr_2516_; lean_object* v___x_2517_; 
v_data_2515_ = lean_ctor_get(v_x_2432_, 0);
v_expr_2516_ = lean_ctor_get(v_x_2432_, 1);
lean_inc_ref(v_expr_2516_);
v___x_2517_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2431_, v_expr_2516_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_);
if (lean_obj_tag(v___x_2517_) == 0)
{
lean_object* v_a_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2540_; 
v_a_2518_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2520_ = v___x_2517_;
v_isShared_2521_ = v_isSharedCheck_2540_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_a_2518_);
lean_dec(v___x_2517_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2540_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v_fst_2522_; lean_object* v_snd_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2539_; 
v_fst_2522_ = lean_ctor_get(v_a_2518_, 0);
v_snd_2523_ = lean_ctor_get(v_a_2518_, 1);
v_isSharedCheck_2539_ = !lean_is_exclusive(v_a_2518_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2525_ = v_a_2518_;
v_isShared_2526_ = v_isSharedCheck_2539_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_snd_2523_);
lean_inc(v_fst_2522_);
lean_dec(v_a_2518_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2539_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v___y_2528_; size_t v___x_2535_; size_t v___x_2536_; uint8_t v___x_2537_; 
v___x_2535_ = lean_ptr_addr(v_expr_2516_);
v___x_2536_ = lean_ptr_addr(v_fst_2522_);
v___x_2537_ = lean_usize_dec_eq(v___x_2535_, v___x_2536_);
if (v___x_2537_ == 0)
{
lean_object* v___x_2538_; 
lean_inc(v_data_2515_);
lean_dec_ref_known(v_x_2432_, 2);
v___x_2538_ = l_Lean_Expr_mdata___override(v_data_2515_, v_fst_2522_);
v___y_2528_ = v___x_2538_;
goto v___jp_2527_;
}
else
{
lean_dec(v_fst_2522_);
v___y_2528_ = v_x_2432_;
goto v___jp_2527_;
}
v___jp_2527_:
{
lean_object* v___x_2530_; 
if (v_isShared_2526_ == 0)
{
lean_ctor_set(v___x_2525_, 0, v___y_2528_);
v___x_2530_ = v___x_2525_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v___y_2528_);
lean_ctor_set(v_reuseFailAlloc_2534_, 1, v_snd_2523_);
v___x_2530_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
lean_object* v___x_2532_; 
if (v_isShared_2521_ == 0)
{
lean_ctor_set(v___x_2520_, 0, v___x_2530_);
v___x_2532_ = v___x_2520_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v___x_2530_);
v___x_2532_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
return v___x_2532_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_x_2432_, 2);
return v___x_2517_;
}
}
case 8:
{
lean_object* v_declName_2541_; lean_object* v_type_2542_; lean_object* v_value_2543_; lean_object* v_body_2544_; uint8_t v_nondep_2545_; lean_object* v___x_2546_; 
v_declName_2541_ = lean_ctor_get(v_x_2432_, 0);
v_type_2542_ = lean_ctor_get(v_x_2432_, 1);
v_value_2543_ = lean_ctor_get(v_x_2432_, 2);
v_body_2544_ = lean_ctor_get(v_x_2432_, 3);
v_nondep_2545_ = lean_ctor_get_uint8(v_x_2432_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_2542_);
lean_inc_ref(v_f_2431_);
v___x_2546_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2431_, v_type_2542_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_);
if (lean_obj_tag(v___x_2546_) == 0)
{
lean_object* v_a_2547_; lean_object* v_fst_2548_; lean_object* v_snd_2549_; lean_object* v___x_2550_; 
v_a_2547_ = lean_ctor_get(v___x_2546_, 0);
lean_inc(v_a_2547_);
lean_dec_ref_known(v___x_2546_, 1);
v_fst_2548_ = lean_ctor_get(v_a_2547_, 0);
lean_inc(v_fst_2548_);
v_snd_2549_ = lean_ctor_get(v_a_2547_, 1);
lean_inc(v_snd_2549_);
lean_dec(v_a_2547_);
lean_inc_ref(v_value_2543_);
lean_inc_ref(v_f_2431_);
v___x_2550_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2431_, v_value_2543_, v_snd_2549_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_);
if (lean_obj_tag(v___x_2550_) == 0)
{
lean_object* v_a_2551_; lean_object* v_fst_2552_; lean_object* v_snd_2553_; lean_object* v___x_2554_; 
v_a_2551_ = lean_ctor_get(v___x_2550_, 0);
lean_inc(v_a_2551_);
lean_dec_ref_known(v___x_2550_, 1);
v_fst_2552_ = lean_ctor_get(v_a_2551_, 0);
lean_inc(v_fst_2552_);
v_snd_2553_ = lean_ctor_get(v_a_2551_, 1);
lean_inc(v_snd_2553_);
lean_dec(v_a_2551_);
lean_inc_ref(v_body_2544_);
v___x_2554_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2431_, v_body_2544_, v_snd_2553_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_);
if (lean_obj_tag(v___x_2554_) == 0)
{
lean_object* v_a_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2585_; 
v_a_2555_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2585_ == 0)
{
v___x_2557_ = v___x_2554_;
v_isShared_2558_ = v_isSharedCheck_2585_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_a_2555_);
lean_dec(v___x_2554_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2585_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v_fst_2559_; lean_object* v_snd_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2584_; 
v_fst_2559_ = lean_ctor_get(v_a_2555_, 0);
v_snd_2560_ = lean_ctor_get(v_a_2555_, 1);
v_isSharedCheck_2584_ = !lean_is_exclusive(v_a_2555_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2562_ = v_a_2555_;
v_isShared_2563_ = v_isSharedCheck_2584_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_snd_2560_);
lean_inc(v_fst_2559_);
lean_dec(v_a_2555_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2584_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___y_2565_; size_t v___x_2572_; size_t v___x_2573_; uint8_t v___x_2574_; 
v___x_2572_ = lean_ptr_addr(v_type_2542_);
v___x_2573_ = lean_ptr_addr(v_fst_2548_);
v___x_2574_ = lean_usize_dec_eq(v___x_2572_, v___x_2573_);
if (v___x_2574_ == 0)
{
lean_object* v___x_2575_; 
lean_inc(v_declName_2541_);
lean_dec_ref_known(v_x_2432_, 4);
v___x_2575_ = l_Lean_Expr_letE___override(v_declName_2541_, v_fst_2548_, v_fst_2552_, v_fst_2559_, v_nondep_2545_);
v___y_2565_ = v___x_2575_;
goto v___jp_2564_;
}
else
{
size_t v___x_2576_; size_t v___x_2577_; uint8_t v___x_2578_; 
v___x_2576_ = lean_ptr_addr(v_value_2543_);
v___x_2577_ = lean_ptr_addr(v_fst_2552_);
v___x_2578_ = lean_usize_dec_eq(v___x_2576_, v___x_2577_);
if (v___x_2578_ == 0)
{
lean_object* v___x_2579_; 
lean_inc(v_declName_2541_);
lean_dec_ref_known(v_x_2432_, 4);
v___x_2579_ = l_Lean_Expr_letE___override(v_declName_2541_, v_fst_2548_, v_fst_2552_, v_fst_2559_, v_nondep_2545_);
v___y_2565_ = v___x_2579_;
goto v___jp_2564_;
}
else
{
size_t v___x_2580_; size_t v___x_2581_; uint8_t v___x_2582_; 
v___x_2580_ = lean_ptr_addr(v_body_2544_);
v___x_2581_ = lean_ptr_addr(v_fst_2559_);
v___x_2582_ = lean_usize_dec_eq(v___x_2580_, v___x_2581_);
if (v___x_2582_ == 0)
{
lean_object* v___x_2583_; 
lean_inc(v_declName_2541_);
lean_dec_ref_known(v_x_2432_, 4);
v___x_2583_ = l_Lean_Expr_letE___override(v_declName_2541_, v_fst_2548_, v_fst_2552_, v_fst_2559_, v_nondep_2545_);
v___y_2565_ = v___x_2583_;
goto v___jp_2564_;
}
else
{
lean_dec(v_fst_2559_);
lean_dec(v_fst_2552_);
lean_dec(v_fst_2548_);
v___y_2565_ = v_x_2432_;
goto v___jp_2564_;
}
}
}
v___jp_2564_:
{
lean_object* v___x_2567_; 
if (v_isShared_2563_ == 0)
{
lean_ctor_set(v___x_2562_, 0, v___y_2565_);
v___x_2567_ = v___x_2562_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v___y_2565_);
lean_ctor_set(v_reuseFailAlloc_2571_, 1, v_snd_2560_);
v___x_2567_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
lean_object* v___x_2569_; 
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 0, v___x_2567_);
v___x_2569_ = v___x_2557_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v___x_2567_);
v___x_2569_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
return v___x_2569_;
}
}
}
}
}
}
else
{
lean_dec(v_fst_2552_);
lean_dec(v_fst_2548_);
lean_dec_ref_known(v_x_2432_, 4);
return v___x_2554_;
}
}
else
{
lean_dec(v_fst_2548_);
lean_dec_ref_known(v_x_2432_, 4);
lean_dec_ref(v_f_2431_);
return v___x_2550_;
}
}
else
{
lean_dec_ref_known(v_x_2432_, 4);
lean_dec_ref(v_f_2431_);
return v___x_2546_;
}
}
case 5:
{
lean_object* v_fn_2586_; lean_object* v_arg_2587_; lean_object* v___x_2588_; 
v_fn_2586_ = lean_ctor_get(v_x_2432_, 0);
v_arg_2587_ = lean_ctor_get(v_x_2432_, 1);
lean_inc_ref(v_fn_2586_);
lean_inc_ref(v_f_2431_);
v___x_2588_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2431_, v_fn_2586_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_);
if (lean_obj_tag(v___x_2588_) == 0)
{
lean_object* v_a_2589_; lean_object* v_fst_2590_; lean_object* v_snd_2591_; lean_object* v___x_2592_; 
v_a_2589_ = lean_ctor_get(v___x_2588_, 0);
lean_inc(v_a_2589_);
lean_dec_ref_known(v___x_2588_, 1);
v_fst_2590_ = lean_ctor_get(v_a_2589_, 0);
lean_inc(v_fst_2590_);
v_snd_2591_ = lean_ctor_get(v_a_2589_, 1);
lean_inc(v_snd_2591_);
lean_dec(v_a_2589_);
lean_inc_ref(v_arg_2587_);
v___x_2592_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2431_, v_arg_2587_, v_snd_2591_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_);
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_object* v_a_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2619_; 
v_a_2593_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2619_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2595_ = v___x_2592_;
v_isShared_2596_ = v_isSharedCheck_2619_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_a_2593_);
lean_dec(v___x_2592_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2619_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v_fst_2597_; lean_object* v_snd_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2618_; 
v_fst_2597_ = lean_ctor_get(v_a_2593_, 0);
v_snd_2598_ = lean_ctor_get(v_a_2593_, 1);
v_isSharedCheck_2618_ = !lean_is_exclusive(v_a_2593_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2600_ = v_a_2593_;
v_isShared_2601_ = v_isSharedCheck_2618_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_snd_2598_);
lean_inc(v_fst_2597_);
lean_dec(v_a_2593_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2618_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v___y_2603_; size_t v___x_2610_; size_t v___x_2611_; uint8_t v___x_2612_; 
v___x_2610_ = lean_ptr_addr(v_fn_2586_);
v___x_2611_ = lean_ptr_addr(v_fst_2590_);
v___x_2612_ = lean_usize_dec_eq(v___x_2610_, v___x_2611_);
if (v___x_2612_ == 0)
{
lean_object* v___x_2613_; 
lean_dec_ref_known(v_x_2432_, 2);
v___x_2613_ = l_Lean_Expr_app___override(v_fst_2590_, v_fst_2597_);
v___y_2603_ = v___x_2613_;
goto v___jp_2602_;
}
else
{
size_t v___x_2614_; size_t v___x_2615_; uint8_t v___x_2616_; 
v___x_2614_ = lean_ptr_addr(v_arg_2587_);
v___x_2615_ = lean_ptr_addr(v_fst_2597_);
v___x_2616_ = lean_usize_dec_eq(v___x_2614_, v___x_2615_);
if (v___x_2616_ == 0)
{
lean_object* v___x_2617_; 
lean_dec_ref_known(v_x_2432_, 2);
v___x_2617_ = l_Lean_Expr_app___override(v_fst_2590_, v_fst_2597_);
v___y_2603_ = v___x_2617_;
goto v___jp_2602_;
}
else
{
lean_dec(v_fst_2597_);
lean_dec(v_fst_2590_);
v___y_2603_ = v_x_2432_;
goto v___jp_2602_;
}
}
v___jp_2602_:
{
lean_object* v___x_2605_; 
if (v_isShared_2601_ == 0)
{
lean_ctor_set(v___x_2600_, 0, v___y_2603_);
v___x_2605_ = v___x_2600_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v___y_2603_);
lean_ctor_set(v_reuseFailAlloc_2609_, 1, v_snd_2598_);
v___x_2605_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
lean_object* v___x_2607_; 
if (v_isShared_2596_ == 0)
{
lean_ctor_set(v___x_2595_, 0, v___x_2605_);
v___x_2607_ = v___x_2595_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v___x_2605_);
v___x_2607_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
return v___x_2607_;
}
}
}
}
}
}
else
{
lean_dec(v_fst_2590_);
lean_dec_ref_known(v_x_2432_, 2);
return v___x_2592_;
}
}
else
{
lean_dec_ref_known(v_x_2432_, 2);
lean_dec_ref(v_f_2431_);
return v___x_2588_;
}
}
case 11:
{
lean_object* v_typeName_2620_; lean_object* v_idx_2621_; lean_object* v_struct_2622_; lean_object* v___x_2623_; 
v_typeName_2620_ = lean_ctor_get(v_x_2432_, 0);
v_idx_2621_ = lean_ctor_get(v_x_2432_, 1);
v_struct_2622_ = lean_ctor_get(v_x_2432_, 2);
lean_inc_ref(v_struct_2622_);
v___x_2623_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2431_, v_struct_2622_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_);
if (lean_obj_tag(v___x_2623_) == 0)
{
lean_object* v_a_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2646_; 
v_a_2624_ = lean_ctor_get(v___x_2623_, 0);
v_isSharedCheck_2646_ = !lean_is_exclusive(v___x_2623_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2626_ = v___x_2623_;
v_isShared_2627_ = v_isSharedCheck_2646_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_a_2624_);
lean_dec(v___x_2623_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2646_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v_fst_2628_; lean_object* v_snd_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2645_; 
v_fst_2628_ = lean_ctor_get(v_a_2624_, 0);
v_snd_2629_ = lean_ctor_get(v_a_2624_, 1);
v_isSharedCheck_2645_ = !lean_is_exclusive(v_a_2624_);
if (v_isSharedCheck_2645_ == 0)
{
v___x_2631_ = v_a_2624_;
v_isShared_2632_ = v_isSharedCheck_2645_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_snd_2629_);
lean_inc(v_fst_2628_);
lean_dec(v_a_2624_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2645_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v___y_2634_; size_t v___x_2641_; size_t v___x_2642_; uint8_t v___x_2643_; 
v___x_2641_ = lean_ptr_addr(v_struct_2622_);
v___x_2642_ = lean_ptr_addr(v_fst_2628_);
v___x_2643_ = lean_usize_dec_eq(v___x_2641_, v___x_2642_);
if (v___x_2643_ == 0)
{
lean_object* v___x_2644_; 
lean_inc(v_idx_2621_);
lean_inc(v_typeName_2620_);
lean_dec_ref_known(v_x_2432_, 3);
v___x_2644_ = l_Lean_Expr_proj___override(v_typeName_2620_, v_idx_2621_, v_fst_2628_);
v___y_2634_ = v___x_2644_;
goto v___jp_2633_;
}
else
{
lean_dec(v_fst_2628_);
v___y_2634_ = v_x_2432_;
goto v___jp_2633_;
}
v___jp_2633_:
{
lean_object* v___x_2636_; 
if (v_isShared_2632_ == 0)
{
lean_ctor_set(v___x_2631_, 0, v___y_2634_);
v___x_2636_ = v___x_2631_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v___y_2634_);
lean_ctor_set(v_reuseFailAlloc_2640_, 1, v_snd_2629_);
v___x_2636_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
lean_object* v___x_2638_; 
if (v_isShared_2627_ == 0)
{
lean_ctor_set(v___x_2626_, 0, v___x_2636_);
v___x_2638_ = v___x_2626_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v___x_2636_);
v___x_2638_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
return v___x_2638_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_x_2432_, 3);
return v___x_2623_;
}
}
default: 
{
lean_object* v___x_2647_; lean_object* v___x_2648_; 
lean_dec_ref(v_f_2431_);
v___x_2647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2647_, 0, v_x_2432_);
lean_ctor_set(v___x_2647_, 1, v___y_2433_);
v___x_2648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2648_, 0, v___x_2647_);
return v___x_2648_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___boxed(lean_object* v_f_2649_, lean_object* v_x_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_){
_start:
{
lean_object* v_res_2657_; 
v_res_2657_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg(v_f_2649_, v_x_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_);
lean_dec(v___y_2655_);
lean_dec_ref(v___y_2654_);
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
return v_res_2657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg(lean_object* v_f_2658_, lean_object* v_init_2659_, lean_object* v_e_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_){
_start:
{
lean_object* v___x_2666_; 
v___x_2666_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg(v_f_2658_, v_e_2660_, v_init_2659_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_);
if (lean_obj_tag(v___x_2666_) == 0)
{
lean_object* v_a_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2675_; 
v_a_2667_ = lean_ctor_get(v___x_2666_, 0);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2669_ = v___x_2666_;
v_isShared_2670_ = v_isSharedCheck_2675_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_a_2667_);
lean_dec(v___x_2666_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2675_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v_snd_2671_; lean_object* v___x_2673_; 
v_snd_2671_ = lean_ctor_get(v_a_2667_, 1);
lean_inc(v_snd_2671_);
lean_dec(v_a_2667_);
if (v_isShared_2670_ == 0)
{
lean_ctor_set(v___x_2669_, 0, v_snd_2671_);
v___x_2673_ = v___x_2669_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_snd_2671_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
}
}
}
else
{
lean_object* v_a_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2683_; 
v_a_2676_ = lean_ctor_get(v___x_2666_, 0);
v_isSharedCheck_2683_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2678_ = v___x_2666_;
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_a_2676_);
lean_dec(v___x_2666_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v___x_2681_; 
if (v_isShared_2679_ == 0)
{
v___x_2681_ = v___x_2678_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_a_2676_);
v___x_2681_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
return v___x_2681_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg___boxed(lean_object* v_f_2684_, lean_object* v_init_2685_, lean_object* v_e_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_){
_start:
{
lean_object* v_res_2692_; 
v_res_2692_ = l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg(v_f_2684_, v_init_2685_, v_e_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_);
lean_dec(v___y_2690_);
lean_dec_ref(v___y_2689_);
lean_dec(v___y_2688_);
lean_dec_ref(v___y_2687_);
return v_res_2692_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(lean_object* v_op_2695_, lean_object* v_as_2696_, size_t v_i_2697_, size_t v_stop_2698_, lean_object* v_b_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_){
_start:
{
lean_object* v_a_2706_; uint8_t v___x_2710_; 
v___x_2710_ = lean_usize_dec_eq(v_i_2697_, v_stop_2698_);
if (v___x_2710_ == 0)
{
lean_object* v___x_2711_; lean_object* v___x_2712_; 
v___x_2711_ = lean_array_uget_borrowed(v_as_2696_, v_i_2697_);
lean_inc(v___y_2703_);
lean_inc_ref(v___y_2702_);
lean_inc(v___y_2701_);
lean_inc_ref(v___y_2700_);
lean_inc(v___x_2711_);
v___x_2712_ = lean_infer_type(v___x_2711_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_);
if (lean_obj_tag(v___x_2712_) == 0)
{
lean_object* v_a_2713_; lean_object* v___x_2714_; 
v_a_2713_ = lean_ctor_get(v___x_2712_, 0);
lean_inc(v_a_2713_);
lean_dec_ref_known(v___x_2712_, 1);
lean_inc_ref(v_op_2695_);
v___x_2714_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v_op_2695_, v_a_2713_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_);
if (lean_obj_tag(v___x_2714_) == 0)
{
lean_object* v_a_2715_; lean_object* v___x_2716_; 
v_a_2715_ = lean_ctor_get(v___x_2714_, 0);
lean_inc(v_a_2715_);
lean_dec_ref_known(v___x_2714_, 1);
v___x_2716_ = l_Array_append___redArg(v_b_2699_, v_a_2715_);
lean_dec(v_a_2715_);
v_a_2706_ = v___x_2716_;
goto v___jp_2705_;
}
else
{
lean_dec_ref(v_b_2699_);
if (lean_obj_tag(v___x_2714_) == 0)
{
lean_object* v_a_2717_; 
v_a_2717_ = lean_ctor_get(v___x_2714_, 0);
lean_inc(v_a_2717_);
lean_dec_ref_known(v___x_2714_, 1);
v_a_2706_ = v_a_2717_;
goto v___jp_2705_;
}
else
{
lean_dec_ref(v_op_2695_);
return v___x_2714_;
}
}
}
else
{
lean_object* v_a_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2725_; 
lean_dec_ref(v_b_2699_);
lean_dec_ref(v_op_2695_);
v_a_2718_ = lean_ctor_get(v___x_2712_, 0);
v_isSharedCheck_2725_ = !lean_is_exclusive(v___x_2712_);
if (v_isSharedCheck_2725_ == 0)
{
v___x_2720_ = v___x_2712_;
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_a_2718_);
lean_dec(v___x_2712_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v___x_2723_; 
if (v_isShared_2721_ == 0)
{
v___x_2723_ = v___x_2720_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v_a_2718_);
v___x_2723_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
return v___x_2723_;
}
}
}
}
else
{
lean_object* v___x_2726_; 
lean_dec_ref(v_op_2695_);
v___x_2726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2726_, 0, v_b_2699_);
return v___x_2726_;
}
v___jp_2705_:
{
size_t v___x_2707_; size_t v___x_2708_; 
v___x_2707_ = ((size_t)1ULL);
v___x_2708_ = lean_usize_add(v_i_2697_, v___x_2707_);
v_i_2697_ = v___x_2708_;
v_b_2699_ = v_a_2706_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0(lean_object* v_op_2727_, lean_object* v_args_2728_, lean_object* v_body_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_){
_start:
{
lean_object* v___x_2735_; 
lean_inc_ref(v_op_2727_);
v___x_2735_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v_op_2727_, v_body_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_);
if (lean_obj_tag(v___x_2735_) == 0)
{
lean_object* v_a_2736_; lean_object* v___x_2738_; uint8_t v_isShared_2739_; uint8_t v_isSharedCheck_2757_; 
v_a_2736_ = lean_ctor_get(v___x_2735_, 0);
v_isSharedCheck_2757_ = !lean_is_exclusive(v___x_2735_);
if (v_isSharedCheck_2757_ == 0)
{
v___x_2738_ = v___x_2735_;
v_isShared_2739_ = v_isSharedCheck_2757_;
goto v_resetjp_2737_;
}
else
{
lean_inc(v_a_2736_);
lean_dec(v___x_2735_);
v___x_2738_ = lean_box(0);
v_isShared_2739_ = v_isSharedCheck_2757_;
goto v_resetjp_2737_;
}
v_resetjp_2737_:
{
lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; uint8_t v___x_2743_; 
v___x_2740_ = l_Array_reverse___redArg(v_a_2736_);
v___x_2741_ = lean_unsigned_to_nat(0u);
v___x_2742_ = lean_array_get_size(v_args_2728_);
v___x_2743_ = lean_nat_dec_lt(v___x_2741_, v___x_2742_);
if (v___x_2743_ == 0)
{
lean_object* v___x_2745_; 
lean_dec_ref(v_op_2727_);
if (v_isShared_2739_ == 0)
{
lean_ctor_set(v___x_2738_, 0, v___x_2740_);
v___x_2745_ = v___x_2738_;
goto v_reusejp_2744_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v___x_2740_);
v___x_2745_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2744_;
}
v_reusejp_2744_:
{
return v___x_2745_;
}
}
else
{
uint8_t v___x_2747_; 
v___x_2747_ = lean_nat_dec_le(v___x_2742_, v___x_2742_);
if (v___x_2747_ == 0)
{
if (v___x_2743_ == 0)
{
lean_object* v___x_2749_; 
lean_dec_ref(v_op_2727_);
if (v_isShared_2739_ == 0)
{
lean_ctor_set(v___x_2738_, 0, v___x_2740_);
v___x_2749_ = v___x_2738_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v___x_2740_);
v___x_2749_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
return v___x_2749_;
}
}
else
{
size_t v___x_2751_; size_t v___x_2752_; lean_object* v___x_2753_; 
lean_del_object(v___x_2738_);
v___x_2751_ = ((size_t)0ULL);
v___x_2752_ = lean_usize_of_nat(v___x_2742_);
v___x_2753_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(v_op_2727_, v_args_2728_, v___x_2751_, v___x_2752_, v___x_2740_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_);
return v___x_2753_;
}
}
else
{
size_t v___x_2754_; size_t v___x_2755_; lean_object* v___x_2756_; 
lean_del_object(v___x_2738_);
v___x_2754_ = ((size_t)0ULL);
v___x_2755_ = lean_usize_of_nat(v___x_2742_);
v___x_2756_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(v_op_2727_, v_args_2728_, v___x_2754_, v___x_2755_, v___x_2740_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_);
return v___x_2756_;
}
}
}
}
else
{
lean_dec_ref(v_op_2727_);
return v___x_2735_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed(lean_object* v_op_2758_, lean_object* v_args_2759_, lean_object* v_body_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_){
_start:
{
lean_object* v_res_2766_; 
v_res_2766_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0(v_op_2758_, v_args_2759_, v_body_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
lean_dec(v___y_2764_);
lean_dec_ref(v___y_2763_);
lean_dec(v___y_2762_);
lean_dec_ref(v___y_2761_);
lean_dec_ref(v_args_2759_);
return v_res_2766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3___boxed(lean_object* v_op_2767_, lean_object* v_a_2768_, lean_object* v_f_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_){
_start:
{
lean_object* v_res_2775_; 
v_res_2775_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3(v_op_2767_, v_a_2768_, v_f_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
lean_dec(v___y_2773_);
lean_dec_ref(v___y_2772_);
lean_dec(v___y_2771_);
lean_dec_ref(v___y_2770_);
return v_res_2775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(lean_object* v_op_2776_, lean_object* v_e_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_){
_start:
{
switch(lean_obj_tag(v_e_2777_))
{
case 0:
{
lean_object* v___x_2783_; lean_object* v___x_2784_; 
lean_dec_ref_known(v_e_2777_, 1);
lean_dec_ref(v_op_2776_);
v___x_2783_ = ((lean_object*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___closed__0));
v___x_2784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2784_, 0, v___x_2783_);
return v___x_2784_;
}
case 7:
{
lean_object* v___f_2785_; uint8_t v___x_2786_; lean_object* v___x_2787_; 
v___f_2785_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2785_, 0, v_op_2776_);
v___x_2786_ = 0;
v___x_2787_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(v_e_2777_, v___f_2785_, v___x_2786_, v_a_2778_, v_a_2779_, v_a_2780_, v_a_2781_);
return v___x_2787_;
}
case 6:
{
lean_object* v___f_2788_; uint8_t v___x_2789_; uint8_t v___x_2790_; lean_object* v___x_2791_; 
v___f_2788_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2788_, 0, v_op_2776_);
v___x_2789_ = 0;
v___x_2790_ = 1;
v___x_2791_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(v_e_2777_, v___f_2788_, v___x_2789_, v___x_2790_, v_a_2778_, v_a_2779_, v_a_2780_, v_a_2781_);
return v___x_2791_;
}
case 8:
{
lean_object* v___f_2792_; uint8_t v___x_2793_; uint8_t v___x_2794_; lean_object* v___x_2795_; 
v___f_2792_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2792_, 0, v_op_2776_);
v___x_2793_ = 0;
v___x_2794_ = 1;
v___x_2795_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(v_e_2777_, v___f_2792_, v___x_2793_, v___x_2794_, v_a_2778_, v_a_2779_, v_a_2780_, v_a_2781_);
return v___x_2795_;
}
default: 
{
lean_object* v___f_2796_; lean_object* v___x_2797_; 
lean_inc_ref(v_op_2776_);
v___f_2796_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3___boxed), 8, 1);
lean_closure_set(v___f_2796_, 0, v_op_2776_);
lean_inc(v_a_2781_);
lean_inc_ref(v_a_2780_);
lean_inc(v_a_2779_);
lean_inc_ref(v_a_2778_);
lean_inc_ref(v_e_2777_);
v___x_2797_ = lean_apply_6(v_op_2776_, v_e_2777_, v_a_2778_, v_a_2779_, v_a_2780_, v_a_2781_, lean_box(0));
if (lean_obj_tag(v___x_2797_) == 0)
{
lean_object* v_a_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; 
v_a_2798_ = lean_ctor_get(v___x_2797_, 0);
lean_inc(v_a_2798_);
lean_dec_ref_known(v___x_2797_, 1);
v___x_2799_ = l_Array_reverse___redArg(v_a_2798_);
v___x_2800_ = l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg(v___f_2796_, v___x_2799_, v_e_2777_, v_a_2778_, v_a_2779_, v_a_2780_, v_a_2781_);
return v___x_2800_;
}
else
{
lean_dec_ref(v___f_2796_);
lean_dec_ref(v_e_2777_);
return v___x_2797_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3(lean_object* v_op_2801_, lean_object* v_a_2802_, lean_object* v_f_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_){
_start:
{
lean_object* v___x_2809_; 
v___x_2809_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v_op_2801_, v_f_2803_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
if (lean_obj_tag(v___x_2809_) == 0)
{
lean_object* v_a_2810_; lean_object* v___x_2812_; uint8_t v_isShared_2813_; uint8_t v_isSharedCheck_2818_; 
v_a_2810_ = lean_ctor_get(v___x_2809_, 0);
v_isSharedCheck_2818_ = !lean_is_exclusive(v___x_2809_);
if (v_isSharedCheck_2818_ == 0)
{
v___x_2812_ = v___x_2809_;
v_isShared_2813_ = v_isSharedCheck_2818_;
goto v_resetjp_2811_;
}
else
{
lean_inc(v_a_2810_);
lean_dec(v___x_2809_);
v___x_2812_ = lean_box(0);
v_isShared_2813_ = v_isSharedCheck_2818_;
goto v_resetjp_2811_;
}
v_resetjp_2811_:
{
lean_object* v___x_2814_; lean_object* v___x_2816_; 
v___x_2814_ = l_Array_append___redArg(v_a_2802_, v_a_2810_);
lean_dec(v_a_2810_);
if (v_isShared_2813_ == 0)
{
lean_ctor_set(v___x_2812_, 0, v___x_2814_);
v___x_2816_ = v___x_2812_;
goto v_reusejp_2815_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v___x_2814_);
v___x_2816_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2815_;
}
v_reusejp_2815_:
{
return v___x_2816_;
}
}
}
else
{
lean_dec_ref(v_a_2802_);
return v___x_2809_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg___boxed(lean_object* v_op_2819_, lean_object* v_as_2820_, lean_object* v_i_2821_, lean_object* v_stop_2822_, lean_object* v_b_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_){
_start:
{
size_t v_i_boxed_2829_; size_t v_stop_boxed_2830_; lean_object* v_res_2831_; 
v_i_boxed_2829_ = lean_unbox_usize(v_i_2821_);
lean_dec(v_i_2821_);
v_stop_boxed_2830_ = lean_unbox_usize(v_stop_2822_);
lean_dec(v_stop_2822_);
v_res_2831_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(v_op_2819_, v_as_2820_, v_i_boxed_2829_, v_stop_boxed_2830_, v_b_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
lean_dec(v___y_2827_);
lean_dec_ref(v___y_2826_);
lean_dec(v___y_2825_);
lean_dec_ref(v___y_2824_);
lean_dec_ref(v_as_2820_);
return v_res_2831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___boxed(lean_object* v_op_2832_, lean_object* v_e_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_){
_start:
{
lean_object* v_res_2839_; 
v_res_2839_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v_op_2832_, v_e_2833_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_);
lean_dec(v_a_2837_);
lean_dec_ref(v_a_2836_);
lean_dec(v_a_2835_);
lean_dec_ref(v_a_2834_);
return v_res_2839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches(lean_object* v_00_u03b1_2840_, lean_object* v_op_2841_, lean_object* v_e_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_){
_start:
{
lean_object* v___x_2848_; 
v___x_2848_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v_op_2841_, v_e_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_);
return v___x_2848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___boxed(lean_object* v_00_u03b1_2849_, lean_object* v_op_2850_, lean_object* v_e_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_){
_start:
{
lean_object* v_res_2857_; 
v_res_2857_ = l_Lean_Meta_Rewrites_getSubexpressionMatches(v_00_u03b1_2849_, v_op_2850_, v_e_2851_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_);
lean_dec(v_a_2855_);
lean_dec_ref(v_a_2854_);
lean_dec(v_a_2853_);
lean_dec_ref(v_a_2852_);
return v_res_2857_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0(lean_object* v_00_u03b1_2858_, lean_object* v_op_2859_, lean_object* v_as_2860_, size_t v_i_2861_, size_t v_stop_2862_, lean_object* v_b_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_){
_start:
{
lean_object* v___x_2869_; 
v___x_2869_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(v_op_2859_, v_as_2860_, v_i_2861_, v_stop_2862_, v_b_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_);
return v___x_2869_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___boxed(lean_object* v_00_u03b1_2870_, lean_object* v_op_2871_, lean_object* v_as_2872_, lean_object* v_i_2873_, lean_object* v_stop_2874_, lean_object* v_b_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_){
_start:
{
size_t v_i_boxed_2881_; size_t v_stop_boxed_2882_; lean_object* v_res_2883_; 
v_i_boxed_2881_ = lean_unbox_usize(v_i_2873_);
lean_dec(v_i_2873_);
v_stop_boxed_2882_ = lean_unbox_usize(v_stop_2874_);
lean_dec(v_stop_2874_);
v_res_2883_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0(v_00_u03b1_2870_, v_op_2871_, v_as_2872_, v_i_boxed_2881_, v_stop_boxed_2882_, v_b_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_);
lean_dec(v___y_2879_);
lean_dec_ref(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec_ref(v___y_2876_);
lean_dec_ref(v_as_2872_);
return v_res_2883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3(lean_object* v_00_u03b1_2884_, lean_object* v_f_2885_, lean_object* v_x_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_){
_start:
{
lean_object* v___x_2893_; 
v___x_2893_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg(v_f_2885_, v_x_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_);
return v___x_2893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___boxed(lean_object* v_00_u03b1_2894_, lean_object* v_f_2895_, lean_object* v_x_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_){
_start:
{
lean_object* v_res_2903_; 
v_res_2903_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3(v_00_u03b1_2894_, v_f_2895_, v_x_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
lean_dec(v___y_2901_);
lean_dec_ref(v___y_2900_);
lean_dec(v___y_2899_);
lean_dec_ref(v___y_2898_);
return v_res_2903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3(lean_object* v_00_u03b1_2904_, lean_object* v_f_2905_, lean_object* v_init_2906_, lean_object* v_e_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_){
_start:
{
lean_object* v___x_2913_; 
v___x_2913_ = l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg(v_f_2905_, v_init_2906_, v_e_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_);
return v___x_2913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___boxed(lean_object* v_00_u03b1_2914_, lean_object* v_f_2915_, lean_object* v_init_2916_, lean_object* v_e_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_){
_start:
{
lean_object* v_res_2923_; 
v_res_2923_ = l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3(v_00_u03b1_2914_, v_f_2915_, v_init_2916_, v_e_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_);
lean_dec(v___y_2921_);
lean_dec_ref(v___y_2920_);
lean_dec(v___y_2919_);
lean_dec_ref(v___y_2918_);
return v_res_2923_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__3(size_t v_sz_2924_, size_t v_i_2925_, lean_object* v_bs_2926_){
_start:
{
uint8_t v___x_2927_; 
v___x_2927_ = lean_usize_dec_lt(v_i_2925_, v_sz_2924_);
if (v___x_2927_ == 0)
{
return v_bs_2926_;
}
else
{
lean_object* v_v_2928_; lean_object* v_fst_2929_; lean_object* v_snd_2930_; lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_2944_; 
v_v_2928_ = lean_array_uget(v_bs_2926_, v_i_2925_);
v_fst_2929_ = lean_ctor_get(v_v_2928_, 0);
v_snd_2930_ = lean_ctor_get(v_v_2928_, 1);
v_isSharedCheck_2944_ = !lean_is_exclusive(v_v_2928_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2932_ = v_v_2928_;
v_isShared_2933_ = v_isSharedCheck_2944_;
goto v_resetjp_2931_;
}
else
{
lean_inc(v_snd_2930_);
lean_inc(v_fst_2929_);
lean_dec(v_v_2928_);
v___x_2932_ = lean_box(0);
v_isShared_2933_ = v_isSharedCheck_2944_;
goto v_resetjp_2931_;
}
v_resetjp_2931_:
{
lean_object* v___x_2934_; lean_object* v_bs_x27_2935_; lean_object* v___x_2936_; lean_object* v___x_2938_; 
v___x_2934_ = lean_unsigned_to_nat(0u);
v_bs_x27_2935_ = lean_array_uset(v_bs_2926_, v_i_2925_, v___x_2934_);
v___x_2936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2936_, 0, v_fst_2929_);
if (v_isShared_2933_ == 0)
{
lean_ctor_set(v___x_2932_, 0, v___x_2936_);
v___x_2938_ = v___x_2932_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v___x_2936_);
lean_ctor_set(v_reuseFailAlloc_2943_, 1, v_snd_2930_);
v___x_2938_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
size_t v___x_2939_; size_t v___x_2940_; lean_object* v___x_2941_; 
v___x_2939_ = ((size_t)1ULL);
v___x_2940_ = lean_usize_add(v_i_2925_, v___x_2939_);
v___x_2941_ = lean_array_uset(v_bs_x27_2935_, v_i_2925_, v___x_2938_);
v_i_2925_ = v___x_2940_;
v_bs_2926_ = v___x_2941_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__3___boxed(lean_object* v_sz_2945_, lean_object* v_i_2946_, lean_object* v_bs_2947_){
_start:
{
size_t v_sz_boxed_2948_; size_t v_i_boxed_2949_; lean_object* v_res_2950_; 
v_sz_boxed_2948_ = lean_unbox_usize(v_sz_2945_);
lean_dec(v_sz_2945_);
v_i_boxed_2949_ = lean_unbox_usize(v_i_2946_);
lean_dec(v_i_2946_);
v_res_2950_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__3(v_sz_boxed_2948_, v_i_boxed_2949_, v_bs_2947_);
return v_res_2950_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0___redArg(lean_object* v_xs_2951_, lean_object* v_j_2952_){
_start:
{
lean_object* v_zero_2953_; uint8_t v_isZero_2954_; 
v_zero_2953_ = lean_unsigned_to_nat(0u);
v_isZero_2954_ = lean_nat_dec_eq(v_j_2952_, v_zero_2953_);
if (v_isZero_2954_ == 1)
{
lean_dec(v_j_2952_);
return v_xs_2951_;
}
else
{
lean_object* v___x_2955_; lean_object* v_snd_2956_; lean_object* v_snd_2957_; lean_object* v_one_2958_; lean_object* v_n_2959_; lean_object* v___x_2960_; lean_object* v_snd_2961_; lean_object* v_snd_2962_; uint8_t v___x_2963_; 
v___x_2955_ = lean_array_fget_borrowed(v_xs_2951_, v_j_2952_);
v_snd_2956_ = lean_ctor_get(v___x_2955_, 1);
v_snd_2957_ = lean_ctor_get(v_snd_2956_, 1);
v_one_2958_ = lean_unsigned_to_nat(1u);
v_n_2959_ = lean_nat_sub(v_j_2952_, v_one_2958_);
v___x_2960_ = lean_array_fget_borrowed(v_xs_2951_, v_n_2959_);
v_snd_2961_ = lean_ctor_get(v___x_2960_, 1);
v_snd_2962_ = lean_ctor_get(v_snd_2961_, 1);
v___x_2963_ = lean_nat_dec_lt(v_snd_2962_, v_snd_2957_);
if (v___x_2963_ == 0)
{
lean_dec(v_n_2959_);
lean_dec(v_j_2952_);
return v_xs_2951_;
}
else
{
lean_object* v___x_2964_; 
v___x_2964_ = lean_array_fswap(v_xs_2951_, v_j_2952_, v_n_2959_);
lean_dec(v_j_2952_);
v_xs_2951_ = v___x_2964_;
v_j_2952_ = v_n_2959_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0(lean_object* v_xs_2966_, lean_object* v_i_2967_, lean_object* v_fuel_2968_){
_start:
{
lean_object* v_zero_2969_; uint8_t v_isZero_2970_; 
v_zero_2969_ = lean_unsigned_to_nat(0u);
v_isZero_2970_ = lean_nat_dec_eq(v_fuel_2968_, v_zero_2969_);
if (v_isZero_2970_ == 1)
{
lean_dec(v_fuel_2968_);
lean_dec(v_i_2967_);
return v_xs_2966_;
}
else
{
lean_object* v___x_2971_; uint8_t v___x_2972_; 
v___x_2971_ = lean_array_get_size(v_xs_2966_);
v___x_2972_ = lean_nat_dec_lt(v_i_2967_, v___x_2971_);
if (v___x_2972_ == 0)
{
lean_dec(v_fuel_2968_);
lean_dec(v_i_2967_);
return v_xs_2966_;
}
else
{
lean_object* v_one_2973_; lean_object* v_n_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; 
v_one_2973_ = lean_unsigned_to_nat(1u);
v_n_2974_ = lean_nat_sub(v_fuel_2968_, v_one_2973_);
lean_dec(v_fuel_2968_);
lean_inc(v_i_2967_);
v___x_2975_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0___redArg(v_xs_2966_, v_i_2967_);
v___x_2976_ = lean_nat_add(v_i_2967_, v_one_2973_);
lean_dec(v_i_2967_);
v_xs_2966_ = v___x_2975_;
v_i_2967_ = v___x_2976_;
v_fuel_2968_ = v_n_2974_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__2(size_t v_sz_2978_, size_t v_i_2979_, lean_object* v_bs_2980_){
_start:
{
uint8_t v___x_2981_; 
v___x_2981_ = lean_usize_dec_lt(v_i_2979_, v_sz_2978_);
if (v___x_2981_ == 0)
{
return v_bs_2980_;
}
else
{
lean_object* v_v_2982_; lean_object* v_fst_2983_; lean_object* v_snd_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_2998_; 
v_v_2982_ = lean_array_uget(v_bs_2980_, v_i_2979_);
v_fst_2983_ = lean_ctor_get(v_v_2982_, 0);
v_snd_2984_ = lean_ctor_get(v_v_2982_, 1);
v_isSharedCheck_2998_ = !lean_is_exclusive(v_v_2982_);
if (v_isSharedCheck_2998_ == 0)
{
v___x_2986_ = v_v_2982_;
v_isShared_2987_ = v_isSharedCheck_2998_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_snd_2984_);
lean_inc(v_fst_2983_);
lean_dec(v_v_2982_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_2998_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
lean_object* v___x_2988_; lean_object* v_bs_x27_2989_; lean_object* v___x_2990_; lean_object* v___x_2992_; 
v___x_2988_ = lean_unsigned_to_nat(0u);
v_bs_x27_2989_ = lean_array_uset(v_bs_2980_, v_i_2979_, v___x_2988_);
v___x_2990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2990_, 0, v_fst_2983_);
if (v_isShared_2987_ == 0)
{
lean_ctor_set(v___x_2986_, 0, v___x_2990_);
v___x_2992_ = v___x_2986_;
goto v_reusejp_2991_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v___x_2990_);
lean_ctor_set(v_reuseFailAlloc_2997_, 1, v_snd_2984_);
v___x_2992_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2991_;
}
v_reusejp_2991_:
{
size_t v___x_2993_; size_t v___x_2994_; lean_object* v___x_2995_; 
v___x_2993_ = ((size_t)1ULL);
v___x_2994_ = lean_usize_add(v_i_2979_, v___x_2993_);
v___x_2995_ = lean_array_uset(v_bs_x27_2989_, v_i_2979_, v___x_2992_);
v_i_2979_ = v___x_2994_;
v_bs_2980_ = v___x_2995_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__2___boxed(lean_object* v_sz_2999_, lean_object* v_i_3000_, lean_object* v_bs_3001_){
_start:
{
size_t v_sz_boxed_3002_; size_t v_i_boxed_3003_; lean_object* v_res_3004_; 
v_sz_boxed_3002_ = lean_unbox_usize(v_sz_2999_);
lean_dec(v_sz_2999_);
v_i_boxed_3003_ = lean_unbox_usize(v_i_3000_);
lean_dec(v_i_3000_);
v_res_3004_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__2(v_sz_boxed_3002_, v_i_boxed_3003_, v_bs_3001_);
return v_res_3004_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg(lean_object* v_forbidden_3005_, lean_object* v_as_3006_, size_t v_sz_3007_, size_t v_i_3008_, lean_object* v_b_3009_){
_start:
{
lean_object* v_a_3012_; uint8_t v___x_3016_; 
v___x_3016_ = lean_usize_dec_lt(v_i_3008_, v_sz_3007_);
if (v___x_3016_ == 0)
{
lean_object* v___x_3017_; 
v___x_3017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3017_, 0, v_b_3009_);
return v___x_3017_;
}
else
{
lean_object* v_a_3018_; lean_object* v_snd_3019_; lean_object* v_snd_3020_; lean_object* v_fst_3021_; lean_object* v_fst_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3080_; 
v_a_3018_ = lean_array_uget(v_as_3006_, v_i_3008_);
v_snd_3019_ = lean_ctor_get(v_a_3018_, 1);
lean_inc(v_snd_3019_);
v_snd_3020_ = lean_ctor_get(v_b_3009_, 1);
lean_inc(v_snd_3020_);
v_fst_3021_ = lean_ctor_get(v_a_3018_, 0);
v_fst_3022_ = lean_ctor_get(v_snd_3019_, 0);
v_isSharedCheck_3080_ = !lean_is_exclusive(v_snd_3019_);
if (v_isSharedCheck_3080_ == 0)
{
lean_object* v_unused_3081_; 
v_unused_3081_ = lean_ctor_get(v_snd_3019_, 1);
lean_dec(v_unused_3081_);
v___x_3024_ = v_snd_3019_;
v_isShared_3025_ = v_isSharedCheck_3080_;
goto v_resetjp_3023_;
}
else
{
lean_inc(v_fst_3022_);
lean_dec(v_snd_3019_);
v___x_3024_ = lean_box(0);
v_isShared_3025_ = v_isSharedCheck_3080_;
goto v_resetjp_3023_;
}
v_resetjp_3023_:
{
lean_object* v_fst_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3078_; 
v_fst_3026_ = lean_ctor_get(v_b_3009_, 0);
v_isSharedCheck_3078_ = !lean_is_exclusive(v_b_3009_);
if (v_isSharedCheck_3078_ == 0)
{
lean_object* v_unused_3079_; 
v_unused_3079_ = lean_ctor_get(v_b_3009_, 1);
lean_dec(v_unused_3079_);
v___x_3028_ = v_b_3009_;
v_isShared_3029_ = v_isSharedCheck_3078_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_fst_3026_);
lean_dec(v_b_3009_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3078_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v_fst_3030_; lean_object* v_snd_3031_; lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3077_; 
v_fst_3030_ = lean_ctor_get(v_snd_3020_, 0);
v_snd_3031_ = lean_ctor_get(v_snd_3020_, 1);
v_isSharedCheck_3077_ = !lean_is_exclusive(v_snd_3020_);
if (v_isSharedCheck_3077_ == 0)
{
v___x_3033_ = v_snd_3020_;
v_isShared_3034_ = v_isSharedCheck_3077_;
goto v_resetjp_3032_;
}
else
{
lean_inc(v_snd_3031_);
lean_inc(v_fst_3030_);
lean_dec(v_snd_3020_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3077_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
uint8_t v___x_3049_; 
v___x_3049_ = l_Lean_NameSet_contains(v_forbidden_3005_, v_fst_3021_);
if (v___x_3049_ == 0)
{
uint8_t v___x_3050_; 
v___x_3050_ = lean_unbox(v_fst_3022_);
lean_dec(v_fst_3022_);
if (v___x_3050_ == 0)
{
uint8_t v___x_3051_; 
lean_inc(v_fst_3021_);
lean_del_object(v___x_3033_);
lean_del_object(v___x_3028_);
v___x_3051_ = l_Lean_NameSet_contains(v_fst_3026_, v_fst_3021_);
if (v___x_3051_ == 0)
{
if (v___x_3016_ == 0)
{
lean_dec(v_fst_3021_);
lean_dec(v_a_3018_);
goto v___jp_3044_;
}
else
{
lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; 
lean_del_object(v___x_3024_);
v___x_3052_ = lean_array_push(v_snd_3031_, v_a_3018_);
v___x_3053_ = l_Lean_NameSet_insert(v_fst_3026_, v_fst_3021_);
v___x_3054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3054_, 0, v_fst_3030_);
lean_ctor_set(v___x_3054_, 1, v___x_3052_);
v___x_3055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3053_);
lean_ctor_set(v___x_3055_, 1, v___x_3054_);
v_a_3012_ = v___x_3055_;
goto v___jp_3011_;
}
}
else
{
lean_dec(v_fst_3021_);
lean_dec(v_a_3018_);
goto v___jp_3044_;
}
}
else
{
uint8_t v___x_3056_; 
lean_del_object(v___x_3024_);
v___x_3056_ = l_Lean_NameSet_contains(v_fst_3030_, v_fst_3021_);
if (v___x_3056_ == 0)
{
lean_inc(v_fst_3021_);
goto v___jp_3035_;
}
else
{
if (v___x_3049_ == 0)
{
lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3064_; 
lean_del_object(v___x_3033_);
lean_del_object(v___x_3028_);
v_isSharedCheck_3064_ = !lean_is_exclusive(v_a_3018_);
if (v_isSharedCheck_3064_ == 0)
{
lean_object* v_unused_3065_; lean_object* v_unused_3066_; 
v_unused_3065_ = lean_ctor_get(v_a_3018_, 1);
lean_dec(v_unused_3065_);
v_unused_3066_ = lean_ctor_get(v_a_3018_, 0);
lean_dec(v_unused_3066_);
v___x_3058_ = v_a_3018_;
v_isShared_3059_ = v_isSharedCheck_3064_;
goto v_resetjp_3057_;
}
else
{
lean_dec(v_a_3018_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3064_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v___x_3061_; 
if (v_isShared_3059_ == 0)
{
lean_ctor_set(v___x_3058_, 1, v_snd_3031_);
lean_ctor_set(v___x_3058_, 0, v_fst_3030_);
v___x_3061_ = v___x_3058_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v_fst_3030_);
lean_ctor_set(v_reuseFailAlloc_3063_, 1, v_snd_3031_);
v___x_3061_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
lean_object* v___x_3062_; 
v___x_3062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3062_, 0, v_fst_3026_);
lean_ctor_set(v___x_3062_, 1, v___x_3061_);
v_a_3012_ = v___x_3062_;
goto v___jp_3011_;
}
}
}
else
{
lean_inc(v_fst_3021_);
goto v___jp_3035_;
}
}
}
}
else
{
lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3074_; 
lean_del_object(v___x_3033_);
lean_del_object(v___x_3028_);
lean_del_object(v___x_3024_);
lean_dec(v_fst_3022_);
v_isSharedCheck_3074_ = !lean_is_exclusive(v_a_3018_);
if (v_isSharedCheck_3074_ == 0)
{
lean_object* v_unused_3075_; lean_object* v_unused_3076_; 
v_unused_3075_ = lean_ctor_get(v_a_3018_, 1);
lean_dec(v_unused_3075_);
v_unused_3076_ = lean_ctor_get(v_a_3018_, 0);
lean_dec(v_unused_3076_);
v___x_3068_ = v_a_3018_;
v_isShared_3069_ = v_isSharedCheck_3074_;
goto v_resetjp_3067_;
}
else
{
lean_dec(v_a_3018_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3074_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
lean_object* v___x_3071_; 
if (v_isShared_3069_ == 0)
{
lean_ctor_set(v___x_3068_, 1, v_snd_3031_);
lean_ctor_set(v___x_3068_, 0, v_fst_3030_);
v___x_3071_ = v___x_3068_;
goto v_reusejp_3070_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v_fst_3030_);
lean_ctor_set(v_reuseFailAlloc_3073_, 1, v_snd_3031_);
v___x_3071_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3070_;
}
v_reusejp_3070_:
{
lean_object* v___x_3072_; 
v___x_3072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3072_, 0, v_fst_3026_);
lean_ctor_set(v___x_3072_, 1, v___x_3071_);
v_a_3012_ = v___x_3072_;
goto v___jp_3011_;
}
}
}
v___jp_3035_:
{
lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3039_; 
v___x_3036_ = lean_array_push(v_snd_3031_, v_a_3018_);
v___x_3037_ = l_Lean_NameSet_insert(v_fst_3030_, v_fst_3021_);
if (v_isShared_3034_ == 0)
{
lean_ctor_set(v___x_3033_, 1, v___x_3036_);
lean_ctor_set(v___x_3033_, 0, v___x_3037_);
v___x_3039_ = v___x_3033_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v___x_3037_);
lean_ctor_set(v_reuseFailAlloc_3043_, 1, v___x_3036_);
v___x_3039_ = v_reuseFailAlloc_3043_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
lean_object* v___x_3041_; 
if (v_isShared_3029_ == 0)
{
lean_ctor_set(v___x_3028_, 1, v___x_3039_);
v___x_3041_ = v___x_3028_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v_fst_3026_);
lean_ctor_set(v_reuseFailAlloc_3042_, 1, v___x_3039_);
v___x_3041_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
v_a_3012_ = v___x_3041_;
goto v___jp_3011_;
}
}
}
v___jp_3044_:
{
lean_object* v___x_3046_; 
if (v_isShared_3025_ == 0)
{
lean_ctor_set(v___x_3024_, 1, v_snd_3031_);
lean_ctor_set(v___x_3024_, 0, v_fst_3030_);
v___x_3046_ = v___x_3024_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v_fst_3030_);
lean_ctor_set(v_reuseFailAlloc_3048_, 1, v_snd_3031_);
v___x_3046_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
lean_object* v___x_3047_; 
v___x_3047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3047_, 0, v_fst_3026_);
lean_ctor_set(v___x_3047_, 1, v___x_3046_);
v_a_3012_ = v___x_3047_;
goto v___jp_3011_;
}
}
}
}
}
}
v___jp_3011_:
{
size_t v___x_3013_; size_t v___x_3014_; 
v___x_3013_ = ((size_t)1ULL);
v___x_3014_ = lean_usize_add(v_i_3008_, v___x_3013_);
v_i_3008_ = v___x_3014_;
v_b_3009_ = v_a_3012_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg___boxed(lean_object* v_forbidden_3082_, lean_object* v_as_3083_, lean_object* v_sz_3084_, lean_object* v_i_3085_, lean_object* v_b_3086_, lean_object* v___y_3087_){
_start:
{
size_t v_sz_boxed_3088_; size_t v_i_boxed_3089_; lean_object* v_res_3090_; 
v_sz_boxed_3088_ = lean_unbox_usize(v_sz_3084_);
lean_dec(v_sz_3084_);
v_i_boxed_3089_ = lean_unbox_usize(v_i_3085_);
lean_dec(v_i_3085_);
v_res_3090_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg(v_forbidden_3082_, v_as_3083_, v_sz_boxed_3088_, v_i_boxed_3089_, v_b_3086_);
lean_dec_ref(v_as_3083_);
lean_dec(v_forbidden_3082_);
return v_res_3090_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__2(void){
_start:
{
lean_object* v___x_3094_; lean_object* v___x_3095_; 
v___x_3094_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__1));
v___x_3095_ = l_Lean_MessageData_ofFormat(v___x_3094_);
return v___x_3095_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__3(void){
_start:
{
lean_object* v___x_3096_; lean_object* v___x_3097_; 
v___x_3096_ = lean_box(1);
v___x_3097_ = l_Lean_MessageData_ofFormat(v___x_3096_);
return v___x_3097_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4(lean_object* v_a_3100_, lean_object* v_a_3101_){
_start:
{
if (lean_obj_tag(v_a_3100_) == 0)
{
lean_object* v___x_3102_; 
v___x_3102_ = l_List_reverse___redArg(v_a_3101_);
return v___x_3102_;
}
else
{
lean_object* v_head_3103_; lean_object* v_snd_3104_; lean_object* v_tail_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3150_; 
v_head_3103_ = lean_ctor_get(v_a_3100_, 0);
lean_inc(v_head_3103_);
v_snd_3104_ = lean_ctor_get(v_head_3103_, 1);
lean_inc(v_snd_3104_);
v_tail_3105_ = lean_ctor_get(v_a_3100_, 1);
v_isSharedCheck_3150_ = !lean_is_exclusive(v_a_3100_);
if (v_isSharedCheck_3150_ == 0)
{
lean_object* v_unused_3151_; 
v_unused_3151_ = lean_ctor_get(v_a_3100_, 0);
lean_dec(v_unused_3151_);
v___x_3107_ = v_a_3100_;
v_isShared_3108_ = v_isSharedCheck_3150_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_tail_3105_);
lean_dec(v_a_3100_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3150_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
lean_object* v_fst_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3148_; 
v_fst_3109_ = lean_ctor_get(v_head_3103_, 0);
v_isSharedCheck_3148_ = !lean_is_exclusive(v_head_3103_);
if (v_isSharedCheck_3148_ == 0)
{
lean_object* v_unused_3149_; 
v_unused_3149_ = lean_ctor_get(v_head_3103_, 1);
lean_dec(v_unused_3149_);
v___x_3111_ = v_head_3103_;
v_isShared_3112_ = v_isSharedCheck_3148_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_fst_3109_);
lean_dec(v_head_3103_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3148_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
lean_object* v_fst_3113_; lean_object* v_snd_3114_; lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3147_; 
v_fst_3113_ = lean_ctor_get(v_snd_3104_, 0);
v_snd_3114_ = lean_ctor_get(v_snd_3104_, 1);
v_isSharedCheck_3147_ = !lean_is_exclusive(v_snd_3104_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3116_ = v_snd_3104_;
v_isShared_3117_ = v_isSharedCheck_3147_;
goto v_resetjp_3115_;
}
else
{
lean_inc(v_snd_3114_);
lean_inc(v_fst_3113_);
lean_dec(v_snd_3104_);
v___x_3116_ = lean_box(0);
v_isShared_3117_ = v_isSharedCheck_3147_;
goto v_resetjp_3115_;
}
v_resetjp_3115_:
{
lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3121_; 
v___x_3118_ = l_Lean_MessageData_ofName(v_fst_3109_);
v___x_3119_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__2, &l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__2_once, _init_l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__2);
if (v_isShared_3117_ == 0)
{
lean_ctor_set_tag(v___x_3116_, 7);
lean_ctor_set(v___x_3116_, 1, v___x_3119_);
lean_ctor_set(v___x_3116_, 0, v___x_3118_);
v___x_3121_ = v___x_3116_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v___x_3118_);
lean_ctor_set(v_reuseFailAlloc_3146_, 1, v___x_3119_);
v___x_3121_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3120_;
}
v_reusejp_3120_:
{
lean_object* v___x_3122_; lean_object* v___x_3124_; 
v___x_3122_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__3, &l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__3_once, _init_l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__3);
if (v_isShared_3112_ == 0)
{
lean_ctor_set_tag(v___x_3111_, 7);
lean_ctor_set(v___x_3111_, 1, v___x_3122_);
lean_ctor_set(v___x_3111_, 0, v___x_3121_);
v___x_3124_ = v___x_3111_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v___x_3121_);
lean_ctor_set(v_reuseFailAlloc_3145_, 1, v___x_3122_);
v___x_3124_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
lean_object* v___y_3126_; uint8_t v___x_3142_; 
v___x_3142_ = lean_unbox(v_fst_3113_);
lean_dec(v_fst_3113_);
if (v___x_3142_ == 0)
{
lean_object* v___x_3143_; 
v___x_3143_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__4));
v___y_3126_ = v___x_3143_;
goto v___jp_3125_;
}
else
{
lean_object* v___x_3144_; 
v___x_3144_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__5));
v___y_3126_ = v___x_3144_;
goto v___jp_3125_;
}
v___jp_3125_:
{
lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3139_; 
lean_inc_ref(v___y_3126_);
v___x_3127_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3127_, 0, v___y_3126_);
v___x_3128_ = l_Lean_MessageData_ofFormat(v___x_3127_);
v___x_3129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3129_, 0, v___x_3128_);
lean_ctor_set(v___x_3129_, 1, v___x_3119_);
v___x_3130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3130_, 0, v___x_3129_);
lean_ctor_set(v___x_3130_, 1, v___x_3122_);
v___x_3131_ = l_Nat_reprFast(v_snd_3114_);
v___x_3132_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3132_, 0, v___x_3131_);
v___x_3133_ = l_Lean_MessageData_ofFormat(v___x_3132_);
v___x_3134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3134_, 0, v___x_3130_);
lean_ctor_set(v___x_3134_, 1, v___x_3133_);
v___x_3135_ = l_Lean_MessageData_paren(v___x_3134_);
v___x_3136_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3136_, 0, v___x_3124_);
lean_ctor_set(v___x_3136_, 1, v___x_3135_);
v___x_3137_ = l_Lean_MessageData_paren(v___x_3136_);
if (v_isShared_3108_ == 0)
{
lean_ctor_set(v___x_3107_, 1, v_a_3101_);
lean_ctor_set(v___x_3107_, 0, v___x_3137_);
v___x_3139_ = v___x_3107_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3141_; 
v_reuseFailAlloc_3141_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3141_, 0, v___x_3137_);
lean_ctor_set(v_reuseFailAlloc_3141_, 1, v_a_3101_);
v___x_3139_ = v_reuseFailAlloc_3141_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
v_a_3100_ = v_tail_3105_;
v_a_3101_ = v___x_3139_;
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
lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; 
v___x_3154_ = ((lean_object*)(l_Lean_Meta_Rewrites_rewriteCandidates___closed__0));
v___x_3155_ = l_Lean_NameSet_empty;
v___x_3156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3156_, 0, v___x_3155_);
lean_ctor_set(v___x_3156_, 1, v___x_3154_);
return v___x_3156_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__2(void){
_start:
{
lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; 
v___x_3157_ = lean_obj_once(&l_Lean_Meta_Rewrites_rewriteCandidates___closed__1, &l_Lean_Meta_Rewrites_rewriteCandidates___closed__1_once, _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__1);
v___x_3158_ = l_Lean_NameSet_empty;
v___x_3159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3159_, 0, v___x_3158_);
lean_ctor_set(v___x_3159_, 1, v___x_3157_);
return v___x_3159_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__3(void){
_start:
{
lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; 
v___x_3160_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_));
v___x_3161_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__4));
v___x_3162_ = l_Lean_Name_append(v___x_3161_, v___x_3160_);
return v___x_3162_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__5(void){
_start:
{
lean_object* v___x_3164_; lean_object* v___x_3165_; 
v___x_3164_ = ((lean_object*)(l_Lean_Meta_Rewrites_rewriteCandidates___closed__4));
v___x_3165_ = l_Lean_stringToMessageData(v___x_3164_);
return v___x_3165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rewriteCandidates(lean_object* v_hyps_3166_, lean_object* v_moduleRef_3167_, lean_object* v_target_3168_, lean_object* v_forbidden_3169_, lean_object* v_a_3170_, lean_object* v_a_3171_, lean_object* v_a_3172_, lean_object* v_a_3173_){
_start:
{
lean_object* v___x_3175_; lean_object* v___x_3176_; 
v___x_3175_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_rwFindDecls___boxed), 7, 1);
lean_closure_set(v___x_3175_, 0, v_moduleRef_3167_);
v___x_3176_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v___x_3175_, v_target_3168_, v_a_3170_, v_a_3171_, v_a_3172_, v_a_3173_);
if (lean_obj_tag(v___x_3176_) == 0)
{
lean_object* v_a_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; size_t v_sz_3182_; size_t v___x_3183_; lean_object* v___x_3184_; 
v_a_3177_ = lean_ctor_get(v___x_3176_, 0);
lean_inc(v_a_3177_);
lean_dec_ref_known(v___x_3176_, 1);
v___x_3178_ = lean_unsigned_to_nat(0u);
v___x_3179_ = lean_array_get_size(v_a_3177_);
v___x_3180_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0(v_a_3177_, v___x_3178_, v___x_3179_);
v___x_3181_ = lean_obj_once(&l_Lean_Meta_Rewrites_rewriteCandidates___closed__2, &l_Lean_Meta_Rewrites_rewriteCandidates___closed__2_once, _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__2);
v_sz_3182_ = lean_array_size(v___x_3180_);
v___x_3183_ = ((size_t)0ULL);
v___x_3184_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg(v_forbidden_3169_, v___x_3180_, v_sz_3182_, v___x_3183_, v___x_3181_);
lean_dec_ref(v___x_3180_);
if (lean_obj_tag(v___x_3184_) == 0)
{
lean_object* v_a_3185_; lean_object* v___x_3187_; uint8_t v_isShared_3188_; uint8_t v_isSharedCheck_3229_; 
v_a_3185_ = lean_ctor_get(v___x_3184_, 0);
v_isSharedCheck_3229_ = !lean_is_exclusive(v___x_3184_);
if (v_isSharedCheck_3229_ == 0)
{
v___x_3187_ = v___x_3184_;
v_isShared_3188_ = v_isSharedCheck_3229_;
goto v_resetjp_3186_;
}
else
{
lean_inc(v_a_3185_);
lean_dec(v___x_3184_);
v___x_3187_ = lean_box(0);
v_isShared_3188_ = v_isSharedCheck_3229_;
goto v_resetjp_3186_;
}
v_resetjp_3186_:
{
lean_object* v_snd_3189_; lean_object* v_snd_3190_; lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3227_; 
v_snd_3189_ = lean_ctor_get(v_a_3185_, 1);
lean_inc(v_snd_3189_);
lean_dec(v_a_3185_);
v_snd_3190_ = lean_ctor_get(v_snd_3189_, 1);
v_isSharedCheck_3227_ = !lean_is_exclusive(v_snd_3189_);
if (v_isSharedCheck_3227_ == 0)
{
lean_object* v_unused_3228_; 
v_unused_3228_ = lean_ctor_get(v_snd_3189_, 0);
lean_dec(v_unused_3228_);
v___x_3192_ = v_snd_3189_;
v_isShared_3193_ = v_isSharedCheck_3227_;
goto v_resetjp_3191_;
}
else
{
lean_inc(v_snd_3190_);
lean_dec(v_snd_3189_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3227_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
lean_object* v_toCold_3203_; lean_object* v_options_3204_; uint8_t v_hasTrace_3205_; 
v_toCold_3203_ = lean_ctor_get(v_a_3172_, 0);
v_options_3204_ = lean_ctor_get(v_toCold_3203_, 2);
v_hasTrace_3205_ = lean_ctor_get_uint8(v_options_3204_, sizeof(void*)*1);
if (v_hasTrace_3205_ == 0)
{
lean_del_object(v___x_3192_);
goto v___jp_3194_;
}
else
{
lean_object* v_inheritedTraceOptions_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; uint8_t v___x_3209_; 
v_inheritedTraceOptions_3206_ = lean_ctor_get(v_toCold_3203_, 11);
v___x_3207_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_));
v___x_3208_ = lean_obj_once(&l_Lean_Meta_Rewrites_rewriteCandidates___closed__3, &l_Lean_Meta_Rewrites_rewriteCandidates___closed__3_once, _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__3);
v___x_3209_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3206_, v_options_3204_, v___x_3208_);
if (v___x_3209_ == 0)
{
lean_del_object(v___x_3192_);
goto v___jp_3194_;
}
else
{
lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3216_; 
v___x_3210_ = lean_obj_once(&l_Lean_Meta_Rewrites_rewriteCandidates___closed__5, &l_Lean_Meta_Rewrites_rewriteCandidates___closed__5_once, _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__5);
lean_inc(v_snd_3190_);
v___x_3211_ = lean_array_to_list(v_snd_3190_);
v___x_3212_ = lean_box(0);
v___x_3213_ = l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4(v___x_3211_, v___x_3212_);
v___x_3214_ = l_Lean_MessageData_ofList(v___x_3213_);
if (v_isShared_3193_ == 0)
{
lean_ctor_set_tag(v___x_3192_, 7);
lean_ctor_set(v___x_3192_, 1, v___x_3214_);
lean_ctor_set(v___x_3192_, 0, v___x_3210_);
v___x_3216_ = v___x_3192_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v___x_3210_);
lean_ctor_set(v_reuseFailAlloc_3226_, 1, v___x_3214_);
v___x_3216_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
lean_object* v___x_3217_; 
v___x_3217_ = l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2(v___x_3207_, v___x_3216_, v_a_3170_, v_a_3171_, v_a_3172_, v_a_3173_);
if (lean_obj_tag(v___x_3217_) == 0)
{
lean_dec_ref_known(v___x_3217_, 1);
goto v___jp_3194_;
}
else
{
lean_object* v_a_3218_; lean_object* v___x_3220_; uint8_t v_isShared_3221_; uint8_t v_isSharedCheck_3225_; 
lean_dec(v_snd_3190_);
lean_del_object(v___x_3187_);
lean_dec_ref(v_hyps_3166_);
v_a_3218_ = lean_ctor_get(v___x_3217_, 0);
v_isSharedCheck_3225_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3225_ == 0)
{
v___x_3220_ = v___x_3217_;
v_isShared_3221_ = v_isSharedCheck_3225_;
goto v_resetjp_3219_;
}
else
{
lean_inc(v_a_3218_);
lean_dec(v___x_3217_);
v___x_3220_ = lean_box(0);
v_isShared_3221_ = v_isSharedCheck_3225_;
goto v_resetjp_3219_;
}
v_resetjp_3219_:
{
lean_object* v___x_3223_; 
if (v_isShared_3221_ == 0)
{
v___x_3223_ = v___x_3220_;
goto v_reusejp_3222_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v_a_3218_);
v___x_3223_ = v_reuseFailAlloc_3224_;
goto v_reusejp_3222_;
}
v_reusejp_3222_:
{
return v___x_3223_;
}
}
}
}
}
}
v___jp_3194_:
{
size_t v_sz_3195_; lean_object* v___x_3196_; size_t v_sz_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3201_; 
v_sz_3195_ = lean_array_size(v_hyps_3166_);
v___x_3196_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__2(v_sz_3195_, v___x_3183_, v_hyps_3166_);
v_sz_3197_ = lean_array_size(v_snd_3190_);
v___x_3198_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__3(v_sz_3197_, v___x_3183_, v_snd_3190_);
v___x_3199_ = l_Array_append___redArg(v___x_3196_, v___x_3198_);
lean_dec_ref(v___x_3198_);
if (v_isShared_3188_ == 0)
{
lean_ctor_set(v___x_3187_, 0, v___x_3199_);
v___x_3201_ = v___x_3187_;
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
}
}
}
else
{
lean_object* v_a_3230_; lean_object* v___x_3232_; uint8_t v_isShared_3233_; uint8_t v_isSharedCheck_3237_; 
lean_dec_ref(v_hyps_3166_);
v_a_3230_ = lean_ctor_get(v___x_3184_, 0);
v_isSharedCheck_3237_ = !lean_is_exclusive(v___x_3184_);
if (v_isSharedCheck_3237_ == 0)
{
v___x_3232_ = v___x_3184_;
v_isShared_3233_ = v_isSharedCheck_3237_;
goto v_resetjp_3231_;
}
else
{
lean_inc(v_a_3230_);
lean_dec(v___x_3184_);
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
else
{
lean_object* v_a_3238_; lean_object* v___x_3240_; uint8_t v_isShared_3241_; uint8_t v_isSharedCheck_3245_; 
lean_dec_ref(v_hyps_3166_);
v_a_3238_ = lean_ctor_get(v___x_3176_, 0);
v_isSharedCheck_3245_ = !lean_is_exclusive(v___x_3176_);
if (v_isSharedCheck_3245_ == 0)
{
v___x_3240_ = v___x_3176_;
v_isShared_3241_ = v_isSharedCheck_3245_;
goto v_resetjp_3239_;
}
else
{
lean_inc(v_a_3238_);
lean_dec(v___x_3176_);
v___x_3240_ = lean_box(0);
v_isShared_3241_ = v_isSharedCheck_3245_;
goto v_resetjp_3239_;
}
v_resetjp_3239_:
{
lean_object* v___x_3243_; 
if (v_isShared_3241_ == 0)
{
v___x_3243_ = v___x_3240_;
goto v_reusejp_3242_;
}
else
{
lean_object* v_reuseFailAlloc_3244_; 
v_reuseFailAlloc_3244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3244_, 0, v_a_3238_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rewriteCandidates___boxed(lean_object* v_hyps_3246_, lean_object* v_moduleRef_3247_, lean_object* v_target_3248_, lean_object* v_forbidden_3249_, lean_object* v_a_3250_, lean_object* v_a_3251_, lean_object* v_a_3252_, lean_object* v_a_3253_, lean_object* v_a_3254_){
_start:
{
lean_object* v_res_3255_; 
v_res_3255_ = l_Lean_Meta_Rewrites_rewriteCandidates(v_hyps_3246_, v_moduleRef_3247_, v_target_3248_, v_forbidden_3249_, v_a_3250_, v_a_3251_, v_a_3252_, v_a_3253_);
lean_dec(v_a_3253_);
lean_dec_ref(v_a_3252_);
lean_dec(v_a_3251_);
lean_dec_ref(v_a_3250_);
lean_dec(v_forbidden_3249_);
return v_res_3255_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1(lean_object* v_forbidden_3256_, lean_object* v_as_3257_, size_t v_sz_3258_, size_t v_i_3259_, lean_object* v_b_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_){
_start:
{
lean_object* v___x_3266_; 
v___x_3266_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg(v_forbidden_3256_, v_as_3257_, v_sz_3258_, v_i_3259_, v_b_3260_);
return v___x_3266_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___boxed(lean_object* v_forbidden_3267_, lean_object* v_as_3268_, lean_object* v_sz_3269_, lean_object* v_i_3270_, lean_object* v_b_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_){
_start:
{
size_t v_sz_boxed_3277_; size_t v_i_boxed_3278_; lean_object* v_res_3279_; 
v_sz_boxed_3277_ = lean_unbox_usize(v_sz_3269_);
lean_dec(v_sz_3269_);
v_i_boxed_3278_ = lean_unbox_usize(v_i_3270_);
lean_dec(v_i_3270_);
v_res_3279_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1(v_forbidden_3267_, v_as_3268_, v_sz_boxed_3277_, v_i_boxed_3278_, v_b_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_);
lean_dec(v___y_3275_);
lean_dec_ref(v___y_3274_);
lean_dec(v___y_3273_);
lean_dec_ref(v___y_3272_);
lean_dec_ref(v_as_3268_);
lean_dec(v_forbidden_3267_);
return v_res_3279_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0(lean_object* v_xs_3280_, lean_object* v_j_3281_, lean_object* v_h_3282_){
_start:
{
lean_object* v___x_3283_; 
v___x_3283_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0___redArg(v_xs_3280_, v_j_3281_);
return v___x_3283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_newGoal(lean_object* v_r_3284_){
_start:
{
uint8_t v_rfl_x3f_3285_; 
v_rfl_x3f_3285_ = lean_ctor_get_uint8(v_r_3284_, sizeof(void*)*4 + 1);
if (v_rfl_x3f_3285_ == 0)
{
lean_object* v_result_3286_; lean_object* v_eNew_3287_; lean_object* v___x_3288_; 
v_result_3286_ = lean_ctor_get(v_r_3284_, 2);
v_eNew_3287_ = lean_ctor_get(v_result_3286_, 0);
lean_inc_ref(v_eNew_3287_);
v___x_3288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3288_, 0, v_eNew_3287_);
return v___x_3288_;
}
else
{
lean_object* v___x_3289_; 
v___x_3289_ = lean_box(0);
return v___x_3289_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_newGoal___boxed(lean_object* v_r_3290_){
_start:
{
lean_object* v_res_3291_; 
v_res_3291_ = l_Lean_Meta_Rewrites_RewriteResult_newGoal(v_r_3290_);
lean_dec_ref(v_r_3290_);
return v_res_3291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0(lean_object* v_x_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_){
_start:
{
lean_object* v___x_3302_; 
lean_inc(v___y_3296_);
lean_inc_ref(v___y_3295_);
lean_inc(v___y_3294_);
lean_inc_ref(v___y_3293_);
v___x_3302_ = lean_apply_9(v_x_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_, lean_box(0));
return v___x_3302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0___boxed(lean_object* v_x_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_){
_start:
{
lean_object* v_res_3313_; 
v_res_3313_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0(v_x_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_);
lean_dec(v___y_3307_);
lean_dec_ref(v___y_3306_);
lean_dec(v___y_3305_);
lean_dec_ref(v___y_3304_);
return v_res_3313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg(lean_object* v_mctx_3314_, lean_object* v_x_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_){
_start:
{
lean_object* v___f_3325_; lean_object* v___x_3326_; 
lean_inc(v___y_3319_);
lean_inc_ref(v___y_3318_);
lean_inc(v___y_3317_);
lean_inc_ref(v___y_3316_);
v___f_3325_ = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3325_, 0, v_x_3315_);
lean_closure_set(v___f_3325_, 1, v___y_3316_);
lean_closure_set(v___f_3325_, 2, v___y_3317_);
lean_closure_set(v___f_3325_, 3, v___y_3318_);
lean_closure_set(v___f_3325_, 4, v___y_3319_);
v___x_3326_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp(lean_box(0), v_mctx_3314_, v___f_3325_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_);
if (lean_obj_tag(v___x_3326_) == 0)
{
return v___x_3326_;
}
else
{
lean_object* v_a_3327_; lean_object* v___x_3329_; uint8_t v_isShared_3330_; uint8_t v_isSharedCheck_3334_; 
v_a_3327_ = lean_ctor_get(v___x_3326_, 0);
v_isSharedCheck_3334_ = !lean_is_exclusive(v___x_3326_);
if (v_isSharedCheck_3334_ == 0)
{
v___x_3329_ = v___x_3326_;
v_isShared_3330_ = v_isSharedCheck_3334_;
goto v_resetjp_3328_;
}
else
{
lean_inc(v_a_3327_);
lean_dec(v___x_3326_);
v___x_3329_ = lean_box(0);
v_isShared_3330_ = v_isSharedCheck_3334_;
goto v_resetjp_3328_;
}
v_resetjp_3328_:
{
lean_object* v___x_3332_; 
if (v_isShared_3330_ == 0)
{
v___x_3332_ = v___x_3329_;
goto v_reusejp_3331_;
}
else
{
lean_object* v_reuseFailAlloc_3333_; 
v_reuseFailAlloc_3333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3333_, 0, v_a_3327_);
v___x_3332_ = v_reuseFailAlloc_3333_;
goto v_reusejp_3331_;
}
v_reusejp_3331_:
{
return v___x_3332_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___boxed(lean_object* v_mctx_3335_, lean_object* v_x_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_){
_start:
{
lean_object* v_res_3346_; 
v_res_3346_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg(v_mctx_3335_, v_x_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
lean_dec(v___y_3344_);
lean_dec_ref(v___y_3343_);
lean_dec(v___y_3342_);
lean_dec_ref(v___y_3341_);
lean_dec(v___y_3340_);
lean_dec_ref(v___y_3339_);
lean_dec(v___y_3338_);
lean_dec_ref(v___y_3337_);
return v_res_3346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0(lean_object* v_00_u03b1_3347_, lean_object* v_mctx_3348_, lean_object* v_x_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_){
_start:
{
lean_object* v___x_3359_; 
v___x_3359_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg(v_mctx_3348_, v_x_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_);
return v___x_3359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___boxed(lean_object* v_00_u03b1_3360_, lean_object* v_mctx_3361_, lean_object* v_x_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_){
_start:
{
lean_object* v_res_3372_; 
v_res_3372_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0(v_00_u03b1_3360_, v_mctx_3361_, v_x_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_);
lean_dec(v___y_3370_);
lean_dec_ref(v___y_3369_);
lean_dec(v___y_3368_);
lean_dec_ref(v___y_3367_);
lean_dec(v___y_3366_);
lean_dec_ref(v___y_3365_);
lean_dec(v___y_3364_);
lean_dec_ref(v___y_3363_);
return v_res_3372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0(lean_object* v_expr_3373_, uint8_t v_symm_3374_, lean_object* v_r_3375_, lean_object* v_ref_3376_, lean_object* v_checkState_x3f_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_){
_start:
{
lean_object* v_ref_3387_; lean_object* v___x_3388_; 
v_ref_3387_ = lean_ctor_get(v___y_3384_, 2);
v___x_3388_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_3379_, v___y_3381_, v___y_3383_, v___y_3385_);
if (lean_obj_tag(v___x_3388_) == 0)
{
lean_object* v_a_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___y_3399_; 
v_a_3389_ = lean_ctor_get(v___x_3388_, 0);
lean_inc(v_a_3389_);
lean_dec_ref_known(v___x_3388_, 1);
v___x_3390_ = lean_box(v_symm_3374_);
v___x_3391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3391_, 0, v_expr_3373_);
lean_ctor_set(v___x_3391_, 1, v___x_3390_);
v___x_3392_ = lean_box(0);
v___x_3393_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3393_, 0, v___x_3391_);
lean_ctor_set(v___x_3393_, 1, v___x_3392_);
v___x_3394_ = l_Lean_Meta_Rewrites_RewriteResult_newGoal(v_r_3375_);
v___x_3395_ = l_Lean_Option_toLOption___redArg(v___x_3394_);
v___x_3396_ = lean_box(0);
lean_inc(v_ref_3387_);
v___x_3397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3397_, 0, v_ref_3387_);
if (lean_obj_tag(v_checkState_x3f_3377_) == 0)
{
v___y_3399_ = v_a_3389_;
goto v___jp_3398_;
}
else
{
lean_object* v_val_3402_; 
lean_dec(v_a_3389_);
v_val_3402_ = lean_ctor_get(v_checkState_x3f_3377_, 0);
lean_inc(v_val_3402_);
lean_dec_ref_known(v_checkState_x3f_3377_, 1);
v___y_3399_ = v_val_3402_;
goto v___jp_3398_;
}
v___jp_3398_:
{
lean_object* v___x_3400_; lean_object* v___x_3401_; 
v___x_3400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3400_, 0, v___y_3399_);
v___x_3401_ = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion(v_ref_3376_, v___x_3393_, v___x_3395_, v___x_3396_, v___x_3397_, v___x_3400_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_);
return v___x_3401_;
}
}
else
{
lean_object* v_a_3403_; lean_object* v___x_3405_; uint8_t v_isShared_3406_; uint8_t v_isSharedCheck_3410_; 
lean_dec(v_checkState_x3f_3377_);
lean_dec(v_ref_3376_);
lean_dec_ref(v_expr_3373_);
v_a_3403_ = lean_ctor_get(v___x_3388_, 0);
v_isSharedCheck_3410_ = !lean_is_exclusive(v___x_3388_);
if (v_isSharedCheck_3410_ == 0)
{
v___x_3405_ = v___x_3388_;
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
else
{
lean_inc(v_a_3403_);
lean_dec(v___x_3388_);
v___x_3405_ = lean_box(0);
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
v_resetjp_3404_:
{
lean_object* v___x_3408_; 
if (v_isShared_3406_ == 0)
{
v___x_3408_ = v___x_3405_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v_a_3403_);
v___x_3408_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
return v___x_3408_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0___boxed(lean_object* v_expr_3411_, lean_object* v_symm_3412_, lean_object* v_r_3413_, lean_object* v_ref_3414_, lean_object* v_checkState_x3f_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_){
_start:
{
uint8_t v_symm_boxed_3425_; lean_object* v_res_3426_; 
v_symm_boxed_3425_ = lean_unbox(v_symm_3412_);
v_res_3426_ = l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0(v_expr_3411_, v_symm_boxed_3425_, v_r_3413_, v_ref_3414_, v_checkState_x3f_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_);
lean_dec(v___y_3423_);
lean_dec_ref(v___y_3422_);
lean_dec(v___y_3421_);
lean_dec_ref(v___y_3420_);
lean_dec(v___y_3419_);
lean_dec_ref(v___y_3418_);
lean_dec(v___y_3417_);
lean_dec_ref(v___y_3416_);
lean_dec_ref(v_r_3413_);
return v_res_3426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion(lean_object* v_ref_3427_, lean_object* v_r_3428_, lean_object* v_checkState_x3f_3429_, lean_object* v_a_3430_, lean_object* v_a_3431_, lean_object* v_a_3432_, lean_object* v_a_3433_, lean_object* v_a_3434_, lean_object* v_a_3435_, lean_object* v_a_3436_, lean_object* v_a_3437_){
_start:
{
lean_object* v_expr_3439_; uint8_t v_symm_3440_; lean_object* v_mctx_3441_; lean_object* v___x_3442_; lean_object* v___f_3443_; lean_object* v___x_3444_; 
v_expr_3439_ = lean_ctor_get(v_r_3428_, 0);
lean_inc_ref(v_expr_3439_);
v_symm_3440_ = lean_ctor_get_uint8(v_r_3428_, sizeof(void*)*4);
v_mctx_3441_ = lean_ctor_get(v_r_3428_, 3);
lean_inc_ref(v_mctx_3441_);
v___x_3442_ = lean_box(v_symm_3440_);
v___f_3443_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0___boxed), 14, 5);
lean_closure_set(v___f_3443_, 0, v_expr_3439_);
lean_closure_set(v___f_3443_, 1, v___x_3442_);
lean_closure_set(v___f_3443_, 2, v_r_3428_);
lean_closure_set(v___f_3443_, 3, v_ref_3427_);
lean_closure_set(v___f_3443_, 4, v_checkState_x3f_3429_);
v___x_3444_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg(v_mctx_3441_, v___f_3443_, v_a_3430_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_);
return v___x_3444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___boxed(lean_object* v_ref_3445_, lean_object* v_r_3446_, lean_object* v_checkState_x3f_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_, lean_object* v_a_3450_, lean_object* v_a_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_){
_start:
{
lean_object* v_res_3457_; 
v_res_3457_ = l_Lean_Meta_Rewrites_RewriteResult_addSuggestion(v_ref_3445_, v_r_3446_, v_checkState_x3f_3447_, v_a_3448_, v_a_3449_, v_a_3450_, v_a_3451_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_);
lean_dec(v_a_3455_);
lean_dec_ref(v_a_3454_);
lean_dec(v_a_3453_);
lean_dec_ref(v_a_3452_);
lean_dec(v_a_3451_);
lean_dec_ref(v_a_3450_);
lean_dec(v_a_3449_);
lean_dec_ref(v_a_3448_);
return v_res_3457_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3___redArg(lean_object* v_a_3458_, lean_object* v_b_3459_, lean_object* v_x_3460_){
_start:
{
if (lean_obj_tag(v_x_3460_) == 0)
{
lean_dec(v_b_3459_);
lean_dec_ref(v_a_3458_);
return v_x_3460_;
}
else
{
lean_object* v_key_3461_; lean_object* v_value_3462_; lean_object* v_tail_3463_; lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3475_; 
v_key_3461_ = lean_ctor_get(v_x_3460_, 0);
v_value_3462_ = lean_ctor_get(v_x_3460_, 1);
v_tail_3463_ = lean_ctor_get(v_x_3460_, 2);
v_isSharedCheck_3475_ = !lean_is_exclusive(v_x_3460_);
if (v_isSharedCheck_3475_ == 0)
{
v___x_3465_ = v_x_3460_;
v_isShared_3466_ = v_isSharedCheck_3475_;
goto v_resetjp_3464_;
}
else
{
lean_inc(v_tail_3463_);
lean_inc(v_value_3462_);
lean_inc(v_key_3461_);
lean_dec(v_x_3460_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3475_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
uint8_t v___x_3467_; 
v___x_3467_ = lean_string_dec_eq(v_key_3461_, v_a_3458_);
if (v___x_3467_ == 0)
{
lean_object* v___x_3468_; lean_object* v___x_3470_; 
v___x_3468_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3___redArg(v_a_3458_, v_b_3459_, v_tail_3463_);
if (v_isShared_3466_ == 0)
{
lean_ctor_set(v___x_3465_, 2, v___x_3468_);
v___x_3470_ = v___x_3465_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v_key_3461_);
lean_ctor_set(v_reuseFailAlloc_3471_, 1, v_value_3462_);
lean_ctor_set(v_reuseFailAlloc_3471_, 2, v___x_3468_);
v___x_3470_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
return v___x_3470_;
}
}
else
{
lean_object* v___x_3473_; 
lean_dec(v_value_3462_);
lean_dec(v_key_3461_);
if (v_isShared_3466_ == 0)
{
lean_ctor_set(v___x_3465_, 1, v_b_3459_);
lean_ctor_set(v___x_3465_, 0, v_a_3458_);
v___x_3473_ = v___x_3465_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v_a_3458_);
lean_ctor_set(v_reuseFailAlloc_3474_, 1, v_b_3459_);
lean_ctor_set(v_reuseFailAlloc_3474_, 2, v_tail_3463_);
v___x_3473_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
return v___x_3473_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_x_3476_, lean_object* v_x_3477_){
_start:
{
if (lean_obj_tag(v_x_3477_) == 0)
{
return v_x_3476_;
}
else
{
lean_object* v_key_3478_; lean_object* v_value_3479_; lean_object* v_tail_3480_; lean_object* v___x_3482_; uint8_t v_isShared_3483_; uint8_t v_isSharedCheck_3503_; 
v_key_3478_ = lean_ctor_get(v_x_3477_, 0);
v_value_3479_ = lean_ctor_get(v_x_3477_, 1);
v_tail_3480_ = lean_ctor_get(v_x_3477_, 2);
v_isSharedCheck_3503_ = !lean_is_exclusive(v_x_3477_);
if (v_isSharedCheck_3503_ == 0)
{
v___x_3482_ = v_x_3477_;
v_isShared_3483_ = v_isSharedCheck_3503_;
goto v_resetjp_3481_;
}
else
{
lean_inc(v_tail_3480_);
lean_inc(v_value_3479_);
lean_inc(v_key_3478_);
lean_dec(v_x_3477_);
v___x_3482_ = lean_box(0);
v_isShared_3483_ = v_isSharedCheck_3503_;
goto v_resetjp_3481_;
}
v_resetjp_3481_:
{
lean_object* v___x_3484_; uint64_t v___x_3485_; uint64_t v___x_3486_; uint64_t v___x_3487_; uint64_t v_fold_3488_; uint64_t v___x_3489_; uint64_t v___x_3490_; uint64_t v___x_3491_; size_t v___x_3492_; size_t v___x_3493_; size_t v___x_3494_; size_t v___x_3495_; size_t v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3499_; 
v___x_3484_ = lean_array_get_size(v_x_3476_);
v___x_3485_ = lean_string_hash(v_key_3478_);
v___x_3486_ = 32ULL;
v___x_3487_ = lean_uint64_shift_right(v___x_3485_, v___x_3486_);
v_fold_3488_ = lean_uint64_xor(v___x_3485_, v___x_3487_);
v___x_3489_ = 16ULL;
v___x_3490_ = lean_uint64_shift_right(v_fold_3488_, v___x_3489_);
v___x_3491_ = lean_uint64_xor(v_fold_3488_, v___x_3490_);
v___x_3492_ = lean_uint64_to_usize(v___x_3491_);
v___x_3493_ = lean_usize_of_nat(v___x_3484_);
v___x_3494_ = ((size_t)1ULL);
v___x_3495_ = lean_usize_sub(v___x_3493_, v___x_3494_);
v___x_3496_ = lean_usize_land(v___x_3492_, v___x_3495_);
v___x_3497_ = lean_array_uget_borrowed(v_x_3476_, v___x_3496_);
lean_inc(v___x_3497_);
if (v_isShared_3483_ == 0)
{
lean_ctor_set(v___x_3482_, 2, v___x_3497_);
v___x_3499_ = v___x_3482_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v_key_3478_);
lean_ctor_set(v_reuseFailAlloc_3502_, 1, v_value_3479_);
lean_ctor_set(v_reuseFailAlloc_3502_, 2, v___x_3497_);
v___x_3499_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
lean_object* v___x_3500_; 
v___x_3500_ = lean_array_uset(v_x_3476_, v___x_3496_, v___x_3499_);
v_x_3476_ = v___x_3500_;
v_x_3477_ = v_tail_3480_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3___redArg(lean_object* v_i_3504_, lean_object* v_source_3505_, lean_object* v_target_3506_){
_start:
{
lean_object* v___x_3507_; uint8_t v___x_3508_; 
v___x_3507_ = lean_array_get_size(v_source_3505_);
v___x_3508_ = lean_nat_dec_lt(v_i_3504_, v___x_3507_);
if (v___x_3508_ == 0)
{
lean_dec_ref(v_source_3505_);
lean_dec(v_i_3504_);
return v_target_3506_;
}
else
{
lean_object* v_es_3509_; lean_object* v___x_3510_; lean_object* v_source_3511_; lean_object* v_target_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; 
v_es_3509_ = lean_array_fget(v_source_3505_, v_i_3504_);
v___x_3510_ = lean_box(0);
v_source_3511_ = lean_array_fset(v_source_3505_, v_i_3504_, v___x_3510_);
v_target_3512_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3_spec__5___redArg(v_target_3506_, v_es_3509_);
v___x_3513_ = lean_unsigned_to_nat(1u);
v___x_3514_ = lean_nat_add(v_i_3504_, v___x_3513_);
lean_dec(v_i_3504_);
v_i_3504_ = v___x_3514_;
v_source_3505_ = v_source_3511_;
v_target_3506_ = v_target_3512_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2___redArg(lean_object* v_data_3516_){
_start:
{
lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v_nbuckets_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; 
v___x_3517_ = lean_array_get_size(v_data_3516_);
v___x_3518_ = lean_unsigned_to_nat(2u);
v_nbuckets_3519_ = lean_nat_mul(v___x_3517_, v___x_3518_);
v___x_3520_ = lean_unsigned_to_nat(0u);
v___x_3521_ = lean_box(0);
v___x_3522_ = lean_mk_array(v_nbuckets_3519_, v___x_3521_);
v___x_3523_ = lean_array_propagate_mark(v_data_3516_, v___x_3522_);
v___x_3524_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3___redArg(v___x_3520_, v_data_3516_, v___x_3523_);
return v___x_3524_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(lean_object* v_a_3525_, lean_object* v_x_3526_){
_start:
{
if (lean_obj_tag(v_x_3526_) == 0)
{
uint8_t v___x_3527_; 
v___x_3527_ = 0;
return v___x_3527_;
}
else
{
lean_object* v_key_3528_; lean_object* v_tail_3529_; uint8_t v___x_3530_; 
v_key_3528_ = lean_ctor_get(v_x_3526_, 0);
v_tail_3529_ = lean_ctor_get(v_x_3526_, 2);
v___x_3530_ = lean_string_dec_eq(v_key_3528_, v_a_3525_);
if (v___x_3530_ == 0)
{
v_x_3526_ = v_tail_3529_;
goto _start;
}
else
{
return v___x_3530_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg___boxed(lean_object* v_a_3532_, lean_object* v_x_3533_){
_start:
{
uint8_t v_res_3534_; lean_object* v_r_3535_; 
v_res_3534_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(v_a_3532_, v_x_3533_);
lean_dec(v_x_3533_);
lean_dec_ref(v_a_3532_);
v_r_3535_ = lean_box(v_res_3534_);
return v_r_3535_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1___redArg(lean_object* v_m_3536_, lean_object* v_a_3537_, lean_object* v_b_3538_){
_start:
{
lean_object* v_size_3539_; lean_object* v_buckets_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3583_; 
v_size_3539_ = lean_ctor_get(v_m_3536_, 0);
v_buckets_3540_ = lean_ctor_get(v_m_3536_, 1);
v_isSharedCheck_3583_ = !lean_is_exclusive(v_m_3536_);
if (v_isSharedCheck_3583_ == 0)
{
v___x_3542_ = v_m_3536_;
v_isShared_3543_ = v_isSharedCheck_3583_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_buckets_3540_);
lean_inc(v_size_3539_);
lean_dec(v_m_3536_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3583_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v___x_3544_; uint64_t v___x_3545_; uint64_t v___x_3546_; uint64_t v___x_3547_; uint64_t v_fold_3548_; uint64_t v___x_3549_; uint64_t v___x_3550_; uint64_t v___x_3551_; size_t v___x_3552_; size_t v___x_3553_; size_t v___x_3554_; size_t v___x_3555_; size_t v___x_3556_; lean_object* v_bkt_3557_; uint8_t v___x_3558_; 
v___x_3544_ = lean_array_get_size(v_buckets_3540_);
v___x_3545_ = lean_string_hash(v_a_3537_);
v___x_3546_ = 32ULL;
v___x_3547_ = lean_uint64_shift_right(v___x_3545_, v___x_3546_);
v_fold_3548_ = lean_uint64_xor(v___x_3545_, v___x_3547_);
v___x_3549_ = 16ULL;
v___x_3550_ = lean_uint64_shift_right(v_fold_3548_, v___x_3549_);
v___x_3551_ = lean_uint64_xor(v_fold_3548_, v___x_3550_);
v___x_3552_ = lean_uint64_to_usize(v___x_3551_);
v___x_3553_ = lean_usize_of_nat(v___x_3544_);
v___x_3554_ = ((size_t)1ULL);
v___x_3555_ = lean_usize_sub(v___x_3553_, v___x_3554_);
v___x_3556_ = lean_usize_land(v___x_3552_, v___x_3555_);
v_bkt_3557_ = lean_array_uget_borrowed(v_buckets_3540_, v___x_3556_);
v___x_3558_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(v_a_3537_, v_bkt_3557_);
if (v___x_3558_ == 0)
{
lean_object* v___x_3559_; lean_object* v_size_x27_3560_; lean_object* v___x_3561_; lean_object* v_buckets_x27_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; uint8_t v___x_3568_; 
v___x_3559_ = lean_unsigned_to_nat(1u);
v_size_x27_3560_ = lean_nat_add(v_size_3539_, v___x_3559_);
lean_dec(v_size_3539_);
lean_inc(v_bkt_3557_);
v___x_3561_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3561_, 0, v_a_3537_);
lean_ctor_set(v___x_3561_, 1, v_b_3538_);
lean_ctor_set(v___x_3561_, 2, v_bkt_3557_);
v_buckets_x27_3562_ = lean_array_uset(v_buckets_3540_, v___x_3556_, v___x_3561_);
v___x_3563_ = lean_unsigned_to_nat(4u);
v___x_3564_ = lean_nat_mul(v_size_x27_3560_, v___x_3563_);
v___x_3565_ = lean_unsigned_to_nat(3u);
v___x_3566_ = lean_nat_div(v___x_3564_, v___x_3565_);
lean_dec(v___x_3564_);
v___x_3567_ = lean_array_get_size(v_buckets_x27_3562_);
v___x_3568_ = lean_nat_dec_le(v___x_3566_, v___x_3567_);
lean_dec(v___x_3566_);
if (v___x_3568_ == 0)
{
lean_object* v_val_3569_; lean_object* v___x_3571_; 
v_val_3569_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2___redArg(v_buckets_x27_3562_);
if (v_isShared_3543_ == 0)
{
lean_ctor_set(v___x_3542_, 1, v_val_3569_);
lean_ctor_set(v___x_3542_, 0, v_size_x27_3560_);
v___x_3571_ = v___x_3542_;
goto v_reusejp_3570_;
}
else
{
lean_object* v_reuseFailAlloc_3572_; 
v_reuseFailAlloc_3572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3572_, 0, v_size_x27_3560_);
lean_ctor_set(v_reuseFailAlloc_3572_, 1, v_val_3569_);
v___x_3571_ = v_reuseFailAlloc_3572_;
goto v_reusejp_3570_;
}
v_reusejp_3570_:
{
return v___x_3571_;
}
}
else
{
lean_object* v___x_3574_; 
if (v_isShared_3543_ == 0)
{
lean_ctor_set(v___x_3542_, 1, v_buckets_x27_3562_);
lean_ctor_set(v___x_3542_, 0, v_size_x27_3560_);
v___x_3574_ = v___x_3542_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v_size_x27_3560_);
lean_ctor_set(v_reuseFailAlloc_3575_, 1, v_buckets_x27_3562_);
v___x_3574_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
return v___x_3574_;
}
}
}
else
{
lean_object* v___x_3576_; lean_object* v_buckets_x27_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3581_; 
lean_inc(v_bkt_3557_);
v___x_3576_ = lean_box(0);
v_buckets_x27_3577_ = lean_array_uset(v_buckets_3540_, v___x_3556_, v___x_3576_);
v___x_3578_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3___redArg(v_a_3537_, v_b_3538_, v_bkt_3557_);
v___x_3579_ = lean_array_uset(v_buckets_x27_3577_, v___x_3556_, v___x_3578_);
if (v_isShared_3543_ == 0)
{
lean_ctor_set(v___x_3542_, 1, v___x_3579_);
v___x_3581_ = v___x_3542_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v_size_3539_);
lean_ctor_set(v_reuseFailAlloc_3582_, 1, v___x_3579_);
v___x_3581_ = v_reuseFailAlloc_3582_;
goto v_reusejp_3580_;
}
v_reusejp_3580_:
{
return v___x_3581_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg(lean_object* v_m_3584_, lean_object* v_a_3585_){
_start:
{
lean_object* v_buckets_3586_; lean_object* v___x_3587_; uint64_t v___x_3588_; uint64_t v___x_3589_; uint64_t v___x_3590_; uint64_t v_fold_3591_; uint64_t v___x_3592_; uint64_t v___x_3593_; uint64_t v___x_3594_; size_t v___x_3595_; size_t v___x_3596_; size_t v___x_3597_; size_t v___x_3598_; size_t v___x_3599_; lean_object* v___x_3600_; uint8_t v___x_3601_; 
v_buckets_3586_ = lean_ctor_get(v_m_3584_, 1);
v___x_3587_ = lean_array_get_size(v_buckets_3586_);
v___x_3588_ = lean_string_hash(v_a_3585_);
v___x_3589_ = 32ULL;
v___x_3590_ = lean_uint64_shift_right(v___x_3588_, v___x_3589_);
v_fold_3591_ = lean_uint64_xor(v___x_3588_, v___x_3590_);
v___x_3592_ = 16ULL;
v___x_3593_ = lean_uint64_shift_right(v_fold_3591_, v___x_3592_);
v___x_3594_ = lean_uint64_xor(v_fold_3591_, v___x_3593_);
v___x_3595_ = lean_uint64_to_usize(v___x_3594_);
v___x_3596_ = lean_usize_of_nat(v___x_3587_);
v___x_3597_ = ((size_t)1ULL);
v___x_3598_ = lean_usize_sub(v___x_3596_, v___x_3597_);
v___x_3599_ = lean_usize_land(v___x_3595_, v___x_3598_);
v___x_3600_ = lean_array_uget_borrowed(v_buckets_3586_, v___x_3599_);
v___x_3601_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(v_a_3585_, v___x_3600_);
return v___x_3601_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg___boxed(lean_object* v_m_3602_, lean_object* v_a_3603_){
_start:
{
uint8_t v_res_3604_; lean_object* v_r_3605_; 
v_res_3604_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg(v_m_3602_, v_a_3603_);
lean_dec_ref(v_a_3603_);
lean_dec_ref(v_m_3602_);
v_r_3605_ = lean_box(v_res_3604_);
return v_r_3605_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg(lean_object* v_cfg_3606_, lean_object* v_as_x27_3607_, lean_object* v_b_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_){
_start:
{
if (lean_obj_tag(v_as_x27_3607_) == 0)
{
lean_object* v___x_3614_; 
lean_dec_ref(v_cfg_3606_);
v___x_3614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3614_, 0, v_b_3608_);
return v___x_3614_;
}
else
{
lean_object* v_head_3615_; lean_object* v_snd_3616_; lean_object* v_snd_3617_; lean_object* v___x_3619_; uint8_t v_isShared_3620_; uint8_t v_isSharedCheck_3774_; 
v_head_3615_ = lean_ctor_get(v_as_x27_3607_, 0);
v_snd_3616_ = lean_ctor_get(v_head_3615_, 1);
v_snd_3617_ = lean_ctor_get(v_b_3608_, 1);
v_isSharedCheck_3774_ = !lean_is_exclusive(v_b_3608_);
if (v_isSharedCheck_3774_ == 0)
{
lean_object* v_unused_3775_; 
v_unused_3775_ = lean_ctor_get(v_b_3608_, 0);
lean_dec(v_unused_3775_);
v___x_3619_ = v_b_3608_;
v_isShared_3620_ = v_isSharedCheck_3774_;
goto v_resetjp_3618_;
}
else
{
lean_inc(v_snd_3617_);
lean_dec(v_b_3608_);
v___x_3619_ = lean_box(0);
v_isShared_3620_ = v_isSharedCheck_3774_;
goto v_resetjp_3618_;
}
v_resetjp_3618_:
{
lean_object* v_tail_3621_; lean_object* v_fst_3622_; lean_object* v_fst_3623_; lean_object* v_snd_3624_; lean_object* v_fst_3625_; lean_object* v_snd_3626_; lean_object* v___x_3628_; uint8_t v_isShared_3629_; uint8_t v_isSharedCheck_3773_; 
v_tail_3621_ = lean_ctor_get(v_as_x27_3607_, 1);
v_fst_3622_ = lean_ctor_get(v_head_3615_, 0);
v_fst_3623_ = lean_ctor_get(v_snd_3616_, 0);
v_snd_3624_ = lean_ctor_get(v_snd_3616_, 1);
v_fst_3625_ = lean_ctor_get(v_snd_3617_, 0);
v_snd_3626_ = lean_ctor_get(v_snd_3617_, 1);
v_isSharedCheck_3773_ = !lean_is_exclusive(v_snd_3617_);
if (v_isSharedCheck_3773_ == 0)
{
v___x_3628_ = v_snd_3617_;
v_isShared_3629_ = v_isSharedCheck_3773_;
goto v_resetjp_3627_;
}
else
{
lean_inc(v_snd_3626_);
lean_inc(v_fst_3625_);
lean_dec(v_snd_3617_);
v___x_3628_ = lean_box(0);
v_isShared_3629_ = v_isSharedCheck_3773_;
goto v_resetjp_3627_;
}
v_resetjp_3627_:
{
lean_object* v___x_3630_; lean_object* v___x_3631_; 
v___x_3630_ = lean_box(0);
v___x_3631_ = l_Lean_getRemainingHeartbeats___redArg(v___y_3611_);
if (lean_obj_tag(v___x_3631_) == 0)
{
lean_object* v_a_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3764_; 
v_a_3632_ = lean_ctor_get(v___x_3631_, 0);
v_isSharedCheck_3764_ = !lean_is_exclusive(v___x_3631_);
if (v_isSharedCheck_3764_ == 0)
{
v___x_3634_ = v___x_3631_;
v_isShared_3635_ = v_isSharedCheck_3764_;
goto v_resetjp_3633_;
}
else
{
lean_inc(v_a_3632_);
lean_dec(v___x_3631_);
v___x_3634_ = lean_box(0);
v_isShared_3635_ = v_isSharedCheck_3764_;
goto v_resetjp_3633_;
}
v_resetjp_3633_:
{
uint8_t v_stopAtRfl_3636_; lean_object* v_max_3637_; lean_object* v_minHeartbeats_3638_; lean_object* v_goal_3639_; lean_object* v_target_3640_; uint8_t v_side_3641_; lean_object* v_mctx_3642_; uint8_t v___x_3643_; 
v_stopAtRfl_3636_ = lean_ctor_get_uint8(v_cfg_3606_, sizeof(void*)*5);
v_max_3637_ = lean_ctor_get(v_cfg_3606_, 0);
v_minHeartbeats_3638_ = lean_ctor_get(v_cfg_3606_, 1);
v_goal_3639_ = lean_ctor_get(v_cfg_3606_, 2);
v_target_3640_ = lean_ctor_get(v_cfg_3606_, 3);
v_side_3641_ = lean_ctor_get_uint8(v_cfg_3606_, sizeof(void*)*5 + 1);
v_mctx_3642_ = lean_ctor_get(v_cfg_3606_, 4);
v___x_3643_ = lean_nat_dec_lt(v_a_3632_, v_minHeartbeats_3638_);
lean_dec(v_a_3632_);
if (v___x_3643_ == 0)
{
lean_object* v___x_3644_; uint8_t v___x_3645_; 
v___x_3644_ = lean_array_get_size(v_snd_3626_);
v___x_3645_ = lean_nat_dec_le(v_max_3637_, v___x_3644_);
if (v___x_3645_ == 0)
{
lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; 
lean_del_object(v___x_3634_);
v___x_3646_ = lean_box(v_side_3641_);
lean_inc(v_snd_3624_);
lean_inc(v_fst_3623_);
lean_inc(v_fst_3622_);
lean_inc_ref(v_target_3640_);
lean_inc(v_goal_3639_);
lean_inc_ref_n(v_mctx_3642_, 2);
v___x_3647_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_rwLemma___boxed), 12, 7);
lean_closure_set(v___x_3647_, 0, v_mctx_3642_);
lean_closure_set(v___x_3647_, 1, v_goal_3639_);
lean_closure_set(v___x_3647_, 2, v_target_3640_);
lean_closure_set(v___x_3647_, 3, v___x_3646_);
lean_closure_set(v___x_3647_, 4, v_fst_3622_);
lean_closure_set(v___x_3647_, 5, v_fst_3623_);
lean_closure_set(v___x_3647_, 6, v_snd_3624_);
v___x_3648_ = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___boxed), 8, 3);
lean_closure_set(v___x_3648_, 0, lean_box(0));
lean_closure_set(v___x_3648_, 1, v_mctx_3642_);
lean_closure_set(v___x_3648_, 2, v___x_3647_);
v___x_3649_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v___x_3648_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_);
if (lean_obj_tag(v___x_3649_) == 0)
{
lean_object* v_a_3650_; 
v_a_3650_ = lean_ctor_get(v___x_3649_, 0);
lean_inc(v_a_3650_);
lean_dec_ref_known(v___x_3649_, 1);
if (lean_obj_tag(v_a_3650_) == 0)
{
lean_object* v___x_3652_; 
if (v_isShared_3629_ == 0)
{
v___x_3652_ = v___x_3628_;
goto v_reusejp_3651_;
}
else
{
lean_object* v_reuseFailAlloc_3657_; 
v_reuseFailAlloc_3657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3657_, 0, v_fst_3625_);
lean_ctor_set(v_reuseFailAlloc_3657_, 1, v_snd_3626_);
v___x_3652_ = v_reuseFailAlloc_3657_;
goto v_reusejp_3651_;
}
v_reusejp_3651_:
{
lean_object* v___x_3654_; 
if (v_isShared_3620_ == 0)
{
lean_ctor_set(v___x_3619_, 1, v___x_3652_);
lean_ctor_set(v___x_3619_, 0, v___x_3630_);
v___x_3654_ = v___x_3619_;
goto v_reusejp_3653_;
}
else
{
lean_object* v_reuseFailAlloc_3656_; 
v_reuseFailAlloc_3656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3656_, 0, v___x_3630_);
lean_ctor_set(v_reuseFailAlloc_3656_, 1, v___x_3652_);
v___x_3654_ = v_reuseFailAlloc_3656_;
goto v_reusejp_3653_;
}
v_reusejp_3653_:
{
v_as_x27_3607_ = v_tail_3621_;
v_b_3608_ = v___x_3654_;
goto _start;
}
}
}
else
{
lean_object* v_val_3658_; lean_object* v___x_3660_; uint8_t v_isShared_3661_; uint8_t v_isSharedCheck_3735_; 
v_val_3658_ = lean_ctor_get(v_a_3650_, 0);
v_isSharedCheck_3735_ = !lean_is_exclusive(v_a_3650_);
if (v_isSharedCheck_3735_ == 0)
{
v___x_3660_ = v_a_3650_;
v_isShared_3661_ = v_isSharedCheck_3735_;
goto v_resetjp_3659_;
}
else
{
lean_inc(v_val_3658_);
lean_dec(v_a_3650_);
v___x_3660_ = lean_box(0);
v_isShared_3661_ = v_isSharedCheck_3735_;
goto v_resetjp_3659_;
}
v_resetjp_3659_:
{
lean_object* v_result_3662_; lean_object* v_mctx_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; 
v_result_3662_ = lean_ctor_get(v_val_3658_, 2);
v_mctx_3663_ = lean_ctor_get(v_val_3658_, 3);
lean_inc(v_val_3658_);
v___x_3664_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult___boxed), 6, 1);
lean_closure_set(v___x_3664_, 0, v_val_3658_);
lean_inc_ref(v_mctx_3663_);
v___x_3665_ = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___boxed), 8, 3);
lean_closure_set(v___x_3665_, 0, lean_box(0));
lean_closure_set(v___x_3665_, 1, v_mctx_3663_);
lean_closure_set(v___x_3665_, 2, v___x_3664_);
v___x_3666_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v___x_3665_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_);
if (lean_obj_tag(v___x_3666_) == 0)
{
lean_object* v_a_3667_; uint8_t v___x_3668_; 
v_a_3667_ = lean_ctor_get(v___x_3666_, 0);
lean_inc(v_a_3667_);
lean_dec_ref_known(v___x_3666_, 1);
v___x_3668_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg(v_fst_3625_, v_a_3667_);
if (v___x_3668_ == 0)
{
lean_object* v_eNew_3669_; lean_object* v___x_3670_; 
v_eNew_3669_ = lean_ctor_get(v_result_3662_, 0);
lean_inc_ref(v_eNew_3669_);
lean_inc_ref(v_mctx_3663_);
v___x_3670_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(v_mctx_3663_, v_eNew_3669_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_);
if (lean_obj_tag(v___x_3670_) == 0)
{
if (v_stopAtRfl_3636_ == 0)
{
lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3675_; 
lean_dec_ref_known(v___x_3670_, 1);
lean_del_object(v___x_3660_);
v___x_3671_ = lean_box(0);
v___x_3672_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1___redArg(v_fst_3625_, v_a_3667_, v___x_3671_);
v___x_3673_ = lean_array_push(v_snd_3626_, v_val_3658_);
if (v_isShared_3629_ == 0)
{
lean_ctor_set(v___x_3628_, 1, v___x_3673_);
lean_ctor_set(v___x_3628_, 0, v___x_3672_);
v___x_3675_ = v___x_3628_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v___x_3672_);
lean_ctor_set(v_reuseFailAlloc_3680_, 1, v___x_3673_);
v___x_3675_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3674_;
}
v_reusejp_3674_:
{
lean_object* v___x_3677_; 
if (v_isShared_3620_ == 0)
{
lean_ctor_set(v___x_3619_, 1, v___x_3675_);
lean_ctor_set(v___x_3619_, 0, v___x_3630_);
v___x_3677_ = v___x_3619_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v___x_3630_);
lean_ctor_set(v_reuseFailAlloc_3679_, 1, v___x_3675_);
v___x_3677_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
v_as_x27_3607_ = v_tail_3621_;
v_b_3608_ = v___x_3677_;
goto _start;
}
}
}
else
{
lean_object* v_a_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3711_; 
v_a_3681_ = lean_ctor_get(v___x_3670_, 0);
v_isSharedCheck_3711_ = !lean_is_exclusive(v___x_3670_);
if (v_isSharedCheck_3711_ == 0)
{
v___x_3683_ = v___x_3670_;
v_isShared_3684_ = v_isSharedCheck_3711_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_a_3681_);
lean_dec(v___x_3670_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3711_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
uint8_t v___x_3685_; 
v___x_3685_ = lean_unbox(v_a_3681_);
lean_dec(v_a_3681_);
if (v___x_3685_ == 0)
{
lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3690_; 
lean_del_object(v___x_3683_);
lean_del_object(v___x_3660_);
v___x_3686_ = lean_box(0);
v___x_3687_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1___redArg(v_fst_3625_, v_a_3667_, v___x_3686_);
v___x_3688_ = lean_array_push(v_snd_3626_, v_val_3658_);
if (v_isShared_3629_ == 0)
{
lean_ctor_set(v___x_3628_, 1, v___x_3688_);
lean_ctor_set(v___x_3628_, 0, v___x_3687_);
v___x_3690_ = v___x_3628_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3695_; 
v_reuseFailAlloc_3695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3695_, 0, v___x_3687_);
lean_ctor_set(v_reuseFailAlloc_3695_, 1, v___x_3688_);
v___x_3690_ = v_reuseFailAlloc_3695_;
goto v_reusejp_3689_;
}
v_reusejp_3689_:
{
lean_object* v___x_3692_; 
if (v_isShared_3620_ == 0)
{
lean_ctor_set(v___x_3619_, 1, v___x_3690_);
lean_ctor_set(v___x_3619_, 0, v___x_3630_);
v___x_3692_ = v___x_3619_;
goto v_reusejp_3691_;
}
else
{
lean_object* v_reuseFailAlloc_3694_; 
v_reuseFailAlloc_3694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3694_, 0, v___x_3630_);
lean_ctor_set(v_reuseFailAlloc_3694_, 1, v___x_3690_);
v___x_3692_ = v_reuseFailAlloc_3694_;
goto v_reusejp_3691_;
}
v_reusejp_3691_:
{
v_as_x27_3607_ = v_tail_3621_;
v_b_3608_ = v___x_3692_;
goto _start;
}
}
}
else
{
lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3700_; 
lean_dec(v_a_3667_);
lean_dec_ref(v_cfg_3606_);
v___x_3696_ = lean_unsigned_to_nat(1u);
v___x_3697_ = lean_mk_empty_array_with_capacity(v___x_3696_);
v___x_3698_ = lean_array_push(v___x_3697_, v_val_3658_);
if (v_isShared_3661_ == 0)
{
lean_ctor_set(v___x_3660_, 0, v___x_3698_);
v___x_3700_ = v___x_3660_;
goto v_reusejp_3699_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v___x_3698_);
v___x_3700_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3699_;
}
v_reusejp_3699_:
{
lean_object* v___x_3702_; 
if (v_isShared_3629_ == 0)
{
v___x_3702_ = v___x_3628_;
goto v_reusejp_3701_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v_fst_3625_);
lean_ctor_set(v_reuseFailAlloc_3709_, 1, v_snd_3626_);
v___x_3702_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3701_;
}
v_reusejp_3701_:
{
lean_object* v___x_3704_; 
if (v_isShared_3620_ == 0)
{
lean_ctor_set(v___x_3619_, 1, v___x_3702_);
lean_ctor_set(v___x_3619_, 0, v___x_3700_);
v___x_3704_ = v___x_3619_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v___x_3700_);
lean_ctor_set(v_reuseFailAlloc_3708_, 1, v___x_3702_);
v___x_3704_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
lean_object* v___x_3706_; 
if (v_isShared_3684_ == 0)
{
lean_ctor_set(v___x_3683_, 0, v___x_3704_);
v___x_3706_ = v___x_3683_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v___x_3704_);
v___x_3706_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
return v___x_3706_;
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
lean_object* v_a_3712_; lean_object* v___x_3714_; uint8_t v_isShared_3715_; uint8_t v_isSharedCheck_3719_; 
lean_dec(v_a_3667_);
lean_del_object(v___x_3660_);
lean_dec(v_val_3658_);
lean_del_object(v___x_3628_);
lean_dec(v_snd_3626_);
lean_dec(v_fst_3625_);
lean_del_object(v___x_3619_);
lean_dec_ref(v_cfg_3606_);
v_a_3712_ = lean_ctor_get(v___x_3670_, 0);
v_isSharedCheck_3719_ = !lean_is_exclusive(v___x_3670_);
if (v_isSharedCheck_3719_ == 0)
{
v___x_3714_ = v___x_3670_;
v_isShared_3715_ = v_isSharedCheck_3719_;
goto v_resetjp_3713_;
}
else
{
lean_inc(v_a_3712_);
lean_dec(v___x_3670_);
v___x_3714_ = lean_box(0);
v_isShared_3715_ = v_isSharedCheck_3719_;
goto v_resetjp_3713_;
}
v_resetjp_3713_:
{
lean_object* v___x_3717_; 
if (v_isShared_3715_ == 0)
{
v___x_3717_ = v___x_3714_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3718_; 
v_reuseFailAlloc_3718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3718_, 0, v_a_3712_);
v___x_3717_ = v_reuseFailAlloc_3718_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
return v___x_3717_;
}
}
}
}
else
{
lean_object* v___x_3721_; 
lean_dec(v_a_3667_);
lean_del_object(v___x_3660_);
lean_dec(v_val_3658_);
if (v_isShared_3629_ == 0)
{
v___x_3721_ = v___x_3628_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v_fst_3625_);
lean_ctor_set(v_reuseFailAlloc_3726_, 1, v_snd_3626_);
v___x_3721_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
lean_object* v___x_3723_; 
if (v_isShared_3620_ == 0)
{
lean_ctor_set(v___x_3619_, 1, v___x_3721_);
lean_ctor_set(v___x_3619_, 0, v___x_3630_);
v___x_3723_ = v___x_3619_;
goto v_reusejp_3722_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v___x_3630_);
lean_ctor_set(v_reuseFailAlloc_3725_, 1, v___x_3721_);
v___x_3723_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3722_;
}
v_reusejp_3722_:
{
v_as_x27_3607_ = v_tail_3621_;
v_b_3608_ = v___x_3723_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3727_; lean_object* v___x_3729_; uint8_t v_isShared_3730_; uint8_t v_isSharedCheck_3734_; 
lean_del_object(v___x_3660_);
lean_dec(v_val_3658_);
lean_del_object(v___x_3628_);
lean_dec(v_snd_3626_);
lean_dec(v_fst_3625_);
lean_del_object(v___x_3619_);
lean_dec_ref(v_cfg_3606_);
v_a_3727_ = lean_ctor_get(v___x_3666_, 0);
v_isSharedCheck_3734_ = !lean_is_exclusive(v___x_3666_);
if (v_isSharedCheck_3734_ == 0)
{
v___x_3729_ = v___x_3666_;
v_isShared_3730_ = v_isSharedCheck_3734_;
goto v_resetjp_3728_;
}
else
{
lean_inc(v_a_3727_);
lean_dec(v___x_3666_);
v___x_3729_ = lean_box(0);
v_isShared_3730_ = v_isSharedCheck_3734_;
goto v_resetjp_3728_;
}
v_resetjp_3728_:
{
lean_object* v___x_3732_; 
if (v_isShared_3730_ == 0)
{
v___x_3732_ = v___x_3729_;
goto v_reusejp_3731_;
}
else
{
lean_object* v_reuseFailAlloc_3733_; 
v_reuseFailAlloc_3733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3733_, 0, v_a_3727_);
v___x_3732_ = v_reuseFailAlloc_3733_;
goto v_reusejp_3731_;
}
v_reusejp_3731_:
{
return v___x_3732_;
}
}
}
}
}
}
else
{
lean_object* v_a_3736_; lean_object* v___x_3738_; uint8_t v_isShared_3739_; uint8_t v_isSharedCheck_3743_; 
lean_del_object(v___x_3628_);
lean_dec(v_snd_3626_);
lean_dec(v_fst_3625_);
lean_del_object(v___x_3619_);
lean_dec_ref(v_cfg_3606_);
v_a_3736_ = lean_ctor_get(v___x_3649_, 0);
v_isSharedCheck_3743_ = !lean_is_exclusive(v___x_3649_);
if (v_isSharedCheck_3743_ == 0)
{
v___x_3738_ = v___x_3649_;
v_isShared_3739_ = v_isSharedCheck_3743_;
goto v_resetjp_3737_;
}
else
{
lean_inc(v_a_3736_);
lean_dec(v___x_3649_);
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
lean_object* v___x_3744_; lean_object* v___x_3746_; 
lean_dec_ref(v_cfg_3606_);
lean_inc(v_snd_3626_);
v___x_3744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3744_, 0, v_snd_3626_);
if (v_isShared_3629_ == 0)
{
v___x_3746_ = v___x_3628_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v_fst_3625_);
lean_ctor_set(v_reuseFailAlloc_3753_, 1, v_snd_3626_);
v___x_3746_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
lean_object* v___x_3748_; 
if (v_isShared_3620_ == 0)
{
lean_ctor_set(v___x_3619_, 1, v___x_3746_);
lean_ctor_set(v___x_3619_, 0, v___x_3744_);
v___x_3748_ = v___x_3619_;
goto v_reusejp_3747_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v___x_3744_);
lean_ctor_set(v_reuseFailAlloc_3752_, 1, v___x_3746_);
v___x_3748_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3747_;
}
v_reusejp_3747_:
{
lean_object* v___x_3750_; 
if (v_isShared_3635_ == 0)
{
lean_ctor_set(v___x_3634_, 0, v___x_3748_);
v___x_3750_ = v___x_3634_;
goto v_reusejp_3749_;
}
else
{
lean_object* v_reuseFailAlloc_3751_; 
v_reuseFailAlloc_3751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3751_, 0, v___x_3748_);
v___x_3750_ = v_reuseFailAlloc_3751_;
goto v_reusejp_3749_;
}
v_reusejp_3749_:
{
return v___x_3750_;
}
}
}
}
}
else
{
lean_object* v___x_3754_; lean_object* v___x_3756_; 
lean_dec_ref(v_cfg_3606_);
lean_inc(v_snd_3626_);
v___x_3754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3754_, 0, v_snd_3626_);
if (v_isShared_3629_ == 0)
{
v___x_3756_ = v___x_3628_;
goto v_reusejp_3755_;
}
else
{
lean_object* v_reuseFailAlloc_3763_; 
v_reuseFailAlloc_3763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3763_, 0, v_fst_3625_);
lean_ctor_set(v_reuseFailAlloc_3763_, 1, v_snd_3626_);
v___x_3756_ = v_reuseFailAlloc_3763_;
goto v_reusejp_3755_;
}
v_reusejp_3755_:
{
lean_object* v___x_3758_; 
if (v_isShared_3620_ == 0)
{
lean_ctor_set(v___x_3619_, 1, v___x_3756_);
lean_ctor_set(v___x_3619_, 0, v___x_3754_);
v___x_3758_ = v___x_3619_;
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
if (v_isShared_3635_ == 0)
{
lean_ctor_set(v___x_3634_, 0, v___x_3758_);
v___x_3760_ = v___x_3634_;
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
}
else
{
lean_object* v_a_3765_; lean_object* v___x_3767_; uint8_t v_isShared_3768_; uint8_t v_isSharedCheck_3772_; 
lean_del_object(v___x_3628_);
lean_dec(v_snd_3626_);
lean_dec(v_fst_3625_);
lean_del_object(v___x_3619_);
lean_dec_ref(v_cfg_3606_);
v_a_3765_ = lean_ctor_get(v___x_3631_, 0);
v_isSharedCheck_3772_ = !lean_is_exclusive(v___x_3631_);
if (v_isSharedCheck_3772_ == 0)
{
v___x_3767_ = v___x_3631_;
v_isShared_3768_ = v_isSharedCheck_3772_;
goto v_resetjp_3766_;
}
else
{
lean_inc(v_a_3765_);
lean_dec(v___x_3631_);
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
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg___boxed(lean_object* v_cfg_3776_, lean_object* v_as_x27_3777_, lean_object* v_b_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_){
_start:
{
lean_object* v_res_3784_; 
v_res_3784_ = l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg(v_cfg_3776_, v_as_x27_3777_, v_b_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_);
lean_dec(v___y_3782_);
lean_dec_ref(v___y_3781_);
lean_dec(v___y_3780_);
lean_dec_ref(v___y_3779_);
lean_dec(v_as_x27_3777_);
return v_res_3784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_takeListAux(lean_object* v_cfg_3785_, lean_object* v_seen_3786_, lean_object* v_acc_3787_, lean_object* v_xs_3788_, lean_object* v_a_3789_, lean_object* v_a_3790_, lean_object* v_a_3791_, lean_object* v_a_3792_){
_start:
{
lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; 
v___x_3794_ = lean_box(0);
v___x_3795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3795_, 0, v_seen_3786_);
lean_ctor_set(v___x_3795_, 1, v_acc_3787_);
v___x_3796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3796_, 0, v___x_3794_);
lean_ctor_set(v___x_3796_, 1, v___x_3795_);
v___x_3797_ = l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg(v_cfg_3785_, v_xs_3788_, v___x_3796_, v_a_3789_, v_a_3790_, v_a_3791_, v_a_3792_);
if (lean_obj_tag(v___x_3797_) == 0)
{
lean_object* v_a_3798_; lean_object* v___x_3800_; uint8_t v_isShared_3801_; uint8_t v_isSharedCheck_3812_; 
v_a_3798_ = lean_ctor_get(v___x_3797_, 0);
v_isSharedCheck_3812_ = !lean_is_exclusive(v___x_3797_);
if (v_isSharedCheck_3812_ == 0)
{
v___x_3800_ = v___x_3797_;
v_isShared_3801_ = v_isSharedCheck_3812_;
goto v_resetjp_3799_;
}
else
{
lean_inc(v_a_3798_);
lean_dec(v___x_3797_);
v___x_3800_ = lean_box(0);
v_isShared_3801_ = v_isSharedCheck_3812_;
goto v_resetjp_3799_;
}
v_resetjp_3799_:
{
lean_object* v_fst_3802_; 
v_fst_3802_ = lean_ctor_get(v_a_3798_, 0);
if (lean_obj_tag(v_fst_3802_) == 0)
{
lean_object* v_snd_3803_; lean_object* v_snd_3804_; lean_object* v___x_3806_; 
v_snd_3803_ = lean_ctor_get(v_a_3798_, 1);
lean_inc(v_snd_3803_);
lean_dec(v_a_3798_);
v_snd_3804_ = lean_ctor_get(v_snd_3803_, 1);
lean_inc(v_snd_3804_);
lean_dec(v_snd_3803_);
if (v_isShared_3801_ == 0)
{
lean_ctor_set(v___x_3800_, 0, v_snd_3804_);
v___x_3806_ = v___x_3800_;
goto v_reusejp_3805_;
}
else
{
lean_object* v_reuseFailAlloc_3807_; 
v_reuseFailAlloc_3807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3807_, 0, v_snd_3804_);
v___x_3806_ = v_reuseFailAlloc_3807_;
goto v_reusejp_3805_;
}
v_reusejp_3805_:
{
return v___x_3806_;
}
}
else
{
lean_object* v_val_3808_; lean_object* v___x_3810_; 
lean_inc_ref(v_fst_3802_);
lean_dec(v_a_3798_);
v_val_3808_ = lean_ctor_get(v_fst_3802_, 0);
lean_inc(v_val_3808_);
lean_dec_ref_known(v_fst_3802_, 1);
if (v_isShared_3801_ == 0)
{
lean_ctor_set(v___x_3800_, 0, v_val_3808_);
v___x_3810_ = v___x_3800_;
goto v_reusejp_3809_;
}
else
{
lean_object* v_reuseFailAlloc_3811_; 
v_reuseFailAlloc_3811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3811_, 0, v_val_3808_);
v___x_3810_ = v_reuseFailAlloc_3811_;
goto v_reusejp_3809_;
}
v_reusejp_3809_:
{
return v___x_3810_;
}
}
}
}
else
{
lean_object* v_a_3813_; lean_object* v___x_3815_; uint8_t v_isShared_3816_; uint8_t v_isSharedCheck_3820_; 
v_a_3813_ = lean_ctor_get(v___x_3797_, 0);
v_isSharedCheck_3820_ = !lean_is_exclusive(v___x_3797_);
if (v_isSharedCheck_3820_ == 0)
{
v___x_3815_ = v___x_3797_;
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
else
{
lean_inc(v_a_3813_);
lean_dec(v___x_3797_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_takeListAux___boxed(lean_object* v_cfg_3821_, lean_object* v_seen_3822_, lean_object* v_acc_3823_, lean_object* v_xs_3824_, lean_object* v_a_3825_, lean_object* v_a_3826_, lean_object* v_a_3827_, lean_object* v_a_3828_, lean_object* v_a_3829_){
_start:
{
lean_object* v_res_3830_; 
v_res_3830_ = l_Lean_Meta_Rewrites_takeListAux(v_cfg_3821_, v_seen_3822_, v_acc_3823_, v_xs_3824_, v_a_3825_, v_a_3826_, v_a_3827_, v_a_3828_);
lean_dec(v_a_3828_);
lean_dec_ref(v_a_3827_);
lean_dec(v_a_3826_);
lean_dec_ref(v_a_3825_);
lean_dec(v_xs_3824_);
return v_res_3830_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0(lean_object* v_00_u03b2_3831_, lean_object* v_m_3832_, lean_object* v_a_3833_){
_start:
{
uint8_t v___x_3834_; 
v___x_3834_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg(v_m_3832_, v_a_3833_);
return v___x_3834_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___boxed(lean_object* v_00_u03b2_3835_, lean_object* v_m_3836_, lean_object* v_a_3837_){
_start:
{
uint8_t v_res_3838_; lean_object* v_r_3839_; 
v_res_3838_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0(v_00_u03b2_3835_, v_m_3836_, v_a_3837_);
lean_dec_ref(v_a_3837_);
lean_dec_ref(v_m_3836_);
v_r_3839_ = lean_box(v_res_3838_);
return v_r_3839_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1(lean_object* v_00_u03b2_3840_, lean_object* v_m_3841_, lean_object* v_a_3842_, lean_object* v_b_3843_){
_start:
{
lean_object* v___x_3844_; 
v___x_3844_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1___redArg(v_m_3841_, v_a_3842_, v_b_3843_);
return v___x_3844_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2(lean_object* v_cfg_3845_, lean_object* v_as_3846_, lean_object* v_as_x27_3847_, lean_object* v_b_3848_, lean_object* v_a_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_){
_start:
{
lean_object* v___x_3855_; 
v___x_3855_ = l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg(v_cfg_3845_, v_as_x27_3847_, v_b_3848_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_);
return v___x_3855_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___boxed(lean_object* v_cfg_3856_, lean_object* v_as_3857_, lean_object* v_as_x27_3858_, lean_object* v_b_3859_, lean_object* v_a_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_){
_start:
{
lean_object* v_res_3866_; 
v_res_3866_ = l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2(v_cfg_3856_, v_as_3857_, v_as_x27_3858_, v_b_3859_, v_a_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_);
lean_dec(v___y_3864_);
lean_dec_ref(v___y_3863_);
lean_dec(v___y_3862_);
lean_dec_ref(v___y_3861_);
lean_dec(v_as_x27_3858_);
lean_dec(v_as_3857_);
return v_res_3866_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0(lean_object* v_00_u03b2_3867_, lean_object* v_a_3868_, lean_object* v_x_3869_){
_start:
{
uint8_t v___x_3870_; 
v___x_3870_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(v_a_3868_, v_x_3869_);
return v___x_3870_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3871_, lean_object* v_a_3872_, lean_object* v_x_3873_){
_start:
{
uint8_t v_res_3874_; lean_object* v_r_3875_; 
v_res_3874_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0(v_00_u03b2_3871_, v_a_3872_, v_x_3873_);
lean_dec(v_x_3873_);
lean_dec_ref(v_a_3872_);
v_r_3875_ = lean_box(v_res_3874_);
return v_r_3875_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2(lean_object* v_00_u03b2_3876_, lean_object* v_data_3877_){
_start:
{
lean_object* v___x_3878_; 
v___x_3878_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2___redArg(v_data_3877_);
return v___x_3878_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3(lean_object* v_00_u03b2_3879_, lean_object* v_a_3880_, lean_object* v_b_3881_, lean_object* v_x_3882_){
_start:
{
lean_object* v___x_3883_; 
v___x_3883_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3___redArg(v_a_3880_, v_b_3881_, v_x_3882_);
return v___x_3883_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_3884_, lean_object* v_i_3885_, lean_object* v_source_3886_, lean_object* v_target_3887_){
_start:
{
lean_object* v___x_3888_; 
v___x_3888_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3___redArg(v_i_3885_, v_source_3886_, v_target_3887_);
return v___x_3888_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_3889_, lean_object* v_x_3890_, lean_object* v_x_3891_){
_start:
{
lean_object* v___x_3892_; 
v___x_3892_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3_spec__5___redArg(v_x_3890_, v_x_3891_);
return v___x_3892_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_findRewrites___closed__0(void){
_start:
{
lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; 
v___x_3893_ = lean_box(0);
v___x_3894_ = lean_unsigned_to_nat(16u);
v___x_3895_ = lean_mk_array(v___x_3894_, v___x_3893_);
return v___x_3895_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_findRewrites___closed__1(void){
_start:
{
lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; 
v___x_3896_ = lean_obj_once(&l_Lean_Meta_Rewrites_findRewrites___closed__0, &l_Lean_Meta_Rewrites_findRewrites___closed__0_once, _init_l_Lean_Meta_Rewrites_findRewrites___closed__0);
v___x_3897_ = lean_unsigned_to_nat(0u);
v___x_3898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3898_, 0, v___x_3897_);
lean_ctor_set(v___x_3898_, 1, v___x_3896_);
return v___x_3898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_findRewrites(lean_object* v_hyps_3899_, lean_object* v_moduleRef_3900_, lean_object* v_goal_3901_, lean_object* v_target_3902_, lean_object* v_forbidden_3903_, uint8_t v_side_3904_, uint8_t v_stopAtRfl_3905_, lean_object* v_max_3906_, lean_object* v_leavePercentHeartbeats_3907_, lean_object* v_a_3908_, lean_object* v_a_3909_, lean_object* v_a_3910_, lean_object* v_a_3911_){
_start:
{
lean_object* v___x_3913_; lean_object* v_mctx_3914_; lean_object* v___x_3915_; 
v___x_3913_ = lean_st_ref_get(v_a_3909_);
v_mctx_3914_ = lean_ctor_get(v___x_3913_, 0);
lean_inc_ref(v_mctx_3914_);
lean_dec(v___x_3913_);
lean_inc_ref(v_target_3902_);
v___x_3915_ = l_Lean_Meta_Rewrites_rewriteCandidates(v_hyps_3899_, v_moduleRef_3900_, v_target_3902_, v_forbidden_3903_, v_a_3908_, v_a_3909_, v_a_3910_, v_a_3911_);
if (lean_obj_tag(v___x_3915_) == 0)
{
lean_object* v_a_3916_; lean_object* v_minHeartbeats_3918_; lean_object* v___y_3919_; lean_object* v___y_3920_; lean_object* v___y_3921_; lean_object* v___y_3922_; lean_object* v___x_3945_; 
v_a_3916_ = lean_ctor_get(v___x_3915_, 0);
lean_inc(v_a_3916_);
lean_dec_ref_known(v___x_3915_, 1);
v___x_3945_ = l_Lean_getMaxHeartbeats___redArg(v_a_3910_);
if (lean_obj_tag(v___x_3945_) == 0)
{
lean_object* v_a_3946_; lean_object* v___x_3947_; uint8_t v___x_3948_; 
v_a_3946_ = lean_ctor_get(v___x_3945_, 0);
lean_inc(v_a_3946_);
lean_dec_ref_known(v___x_3945_, 1);
v___x_3947_ = lean_unsigned_to_nat(0u);
v___x_3948_ = lean_nat_dec_eq(v_a_3946_, v___x_3947_);
lean_dec(v_a_3946_);
if (v___x_3948_ == 0)
{
lean_object* v___x_3949_; 
v___x_3949_ = l_Lean_getRemainingHeartbeats___redArg(v_a_3910_);
if (lean_obj_tag(v___x_3949_) == 0)
{
lean_object* v_a_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; 
v_a_3950_ = lean_ctor_get(v___x_3949_, 0);
lean_inc(v_a_3950_);
lean_dec_ref_known(v___x_3949_, 1);
v___x_3951_ = lean_nat_mul(v_leavePercentHeartbeats_3907_, v_a_3950_);
lean_dec(v_a_3950_);
v___x_3952_ = lean_unsigned_to_nat(100u);
v___x_3953_ = lean_nat_div(v___x_3951_, v___x_3952_);
lean_dec(v___x_3951_);
v_minHeartbeats_3918_ = v___x_3953_;
v___y_3919_ = v_a_3908_;
v___y_3920_ = v_a_3909_;
v___y_3921_ = v_a_3910_;
v___y_3922_ = v_a_3911_;
goto v___jp_3917_;
}
else
{
lean_object* v_a_3954_; lean_object* v___x_3956_; uint8_t v_isShared_3957_; uint8_t v_isSharedCheck_3961_; 
lean_dec(v_a_3916_);
lean_dec_ref(v_mctx_3914_);
lean_dec(v_max_3906_);
lean_dec_ref(v_target_3902_);
lean_dec(v_goal_3901_);
v_a_3954_ = lean_ctor_get(v___x_3949_, 0);
v_isSharedCheck_3961_ = !lean_is_exclusive(v___x_3949_);
if (v_isSharedCheck_3961_ == 0)
{
v___x_3956_ = v___x_3949_;
v_isShared_3957_ = v_isSharedCheck_3961_;
goto v_resetjp_3955_;
}
else
{
lean_inc(v_a_3954_);
lean_dec(v___x_3949_);
v___x_3956_ = lean_box(0);
v_isShared_3957_ = v_isSharedCheck_3961_;
goto v_resetjp_3955_;
}
v_resetjp_3955_:
{
lean_object* v___x_3959_; 
if (v_isShared_3957_ == 0)
{
v___x_3959_ = v___x_3956_;
goto v_reusejp_3958_;
}
else
{
lean_object* v_reuseFailAlloc_3960_; 
v_reuseFailAlloc_3960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3960_, 0, v_a_3954_);
v___x_3959_ = v_reuseFailAlloc_3960_;
goto v_reusejp_3958_;
}
v_reusejp_3958_:
{
return v___x_3959_;
}
}
}
}
else
{
v_minHeartbeats_3918_ = v___x_3947_;
v___y_3919_ = v_a_3908_;
v___y_3920_ = v_a_3909_;
v___y_3921_ = v_a_3910_;
v___y_3922_ = v_a_3911_;
goto v___jp_3917_;
}
}
else
{
lean_object* v_a_3962_; lean_object* v___x_3964_; uint8_t v_isShared_3965_; uint8_t v_isSharedCheck_3969_; 
lean_dec(v_a_3916_);
lean_dec_ref(v_mctx_3914_);
lean_dec(v_max_3906_);
lean_dec_ref(v_target_3902_);
lean_dec(v_goal_3901_);
v_a_3962_ = lean_ctor_get(v___x_3945_, 0);
v_isSharedCheck_3969_ = !lean_is_exclusive(v___x_3945_);
if (v_isSharedCheck_3969_ == 0)
{
v___x_3964_ = v___x_3945_;
v_isShared_3965_ = v_isSharedCheck_3969_;
goto v_resetjp_3963_;
}
else
{
lean_inc(v_a_3962_);
lean_dec(v___x_3945_);
v___x_3964_ = lean_box(0);
v_isShared_3965_ = v_isSharedCheck_3969_;
goto v_resetjp_3963_;
}
v_resetjp_3963_:
{
lean_object* v___x_3967_; 
if (v_isShared_3965_ == 0)
{
v___x_3967_ = v___x_3964_;
goto v_reusejp_3966_;
}
else
{
lean_object* v_reuseFailAlloc_3968_; 
v_reuseFailAlloc_3968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3968_, 0, v_a_3962_);
v___x_3967_ = v_reuseFailAlloc_3968_;
goto v_reusejp_3966_;
}
v_reusejp_3966_:
{
return v___x_3967_;
}
}
}
v___jp_3917_:
{
lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; 
lean_inc(v_max_3906_);
v___x_3923_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_3923_, 0, v_max_3906_);
lean_ctor_set(v___x_3923_, 1, v_minHeartbeats_3918_);
lean_ctor_set(v___x_3923_, 2, v_goal_3901_);
lean_ctor_set(v___x_3923_, 3, v_target_3902_);
lean_ctor_set(v___x_3923_, 4, v_mctx_3914_);
lean_ctor_set_uint8(v___x_3923_, sizeof(void*)*5, v_stopAtRfl_3905_);
lean_ctor_set_uint8(v___x_3923_, sizeof(void*)*5 + 1, v_side_3904_);
v___x_3924_ = lean_obj_once(&l_Lean_Meta_Rewrites_findRewrites___closed__1, &l_Lean_Meta_Rewrites_findRewrites___closed__1_once, _init_l_Lean_Meta_Rewrites_findRewrites___closed__1);
v___x_3925_ = lean_mk_empty_array_with_capacity(v_max_3906_);
lean_dec(v_max_3906_);
v___x_3926_ = lean_array_to_list(v_a_3916_);
v___x_3927_ = l_Lean_Meta_Rewrites_takeListAux(v___x_3923_, v___x_3924_, v___x_3925_, v___x_3926_, v___y_3919_, v___y_3920_, v___y_3921_, v___y_3922_);
lean_dec(v___x_3926_);
if (lean_obj_tag(v___x_3927_) == 0)
{
lean_object* v_a_3928_; lean_object* v___x_3930_; uint8_t v_isShared_3931_; uint8_t v_isSharedCheck_3936_; 
v_a_3928_ = lean_ctor_get(v___x_3927_, 0);
v_isSharedCheck_3936_ = !lean_is_exclusive(v___x_3927_);
if (v_isSharedCheck_3936_ == 0)
{
v___x_3930_ = v___x_3927_;
v_isShared_3931_ = v_isSharedCheck_3936_;
goto v_resetjp_3929_;
}
else
{
lean_inc(v_a_3928_);
lean_dec(v___x_3927_);
v___x_3930_ = lean_box(0);
v_isShared_3931_ = v_isSharedCheck_3936_;
goto v_resetjp_3929_;
}
v_resetjp_3929_:
{
lean_object* v___x_3932_; lean_object* v___x_3934_; 
v___x_3932_ = lean_array_to_list(v_a_3928_);
if (v_isShared_3931_ == 0)
{
lean_ctor_set(v___x_3930_, 0, v___x_3932_);
v___x_3934_ = v___x_3930_;
goto v_reusejp_3933_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v___x_3932_);
v___x_3934_ = v_reuseFailAlloc_3935_;
goto v_reusejp_3933_;
}
v_reusejp_3933_:
{
return v___x_3934_;
}
}
}
else
{
lean_object* v_a_3937_; lean_object* v___x_3939_; uint8_t v_isShared_3940_; uint8_t v_isSharedCheck_3944_; 
v_a_3937_ = lean_ctor_get(v___x_3927_, 0);
v_isSharedCheck_3944_ = !lean_is_exclusive(v___x_3927_);
if (v_isSharedCheck_3944_ == 0)
{
v___x_3939_ = v___x_3927_;
v_isShared_3940_ = v_isSharedCheck_3944_;
goto v_resetjp_3938_;
}
else
{
lean_inc(v_a_3937_);
lean_dec(v___x_3927_);
v___x_3939_ = lean_box(0);
v_isShared_3940_ = v_isSharedCheck_3944_;
goto v_resetjp_3938_;
}
v_resetjp_3938_:
{
lean_object* v___x_3942_; 
if (v_isShared_3940_ == 0)
{
v___x_3942_ = v___x_3939_;
goto v_reusejp_3941_;
}
else
{
lean_object* v_reuseFailAlloc_3943_; 
v_reuseFailAlloc_3943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3943_, 0, v_a_3937_);
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
else
{
lean_object* v_a_3970_; lean_object* v___x_3972_; uint8_t v_isShared_3973_; uint8_t v_isSharedCheck_3977_; 
lean_dec_ref(v_mctx_3914_);
lean_dec(v_max_3906_);
lean_dec_ref(v_target_3902_);
lean_dec(v_goal_3901_);
v_a_3970_ = lean_ctor_get(v___x_3915_, 0);
v_isSharedCheck_3977_ = !lean_is_exclusive(v___x_3915_);
if (v_isSharedCheck_3977_ == 0)
{
v___x_3972_ = v___x_3915_;
v_isShared_3973_ = v_isSharedCheck_3977_;
goto v_resetjp_3971_;
}
else
{
lean_inc(v_a_3970_);
lean_dec(v___x_3915_);
v___x_3972_ = lean_box(0);
v_isShared_3973_ = v_isSharedCheck_3977_;
goto v_resetjp_3971_;
}
v_resetjp_3971_:
{
lean_object* v___x_3975_; 
if (v_isShared_3973_ == 0)
{
v___x_3975_ = v___x_3972_;
goto v_reusejp_3974_;
}
else
{
lean_object* v_reuseFailAlloc_3976_; 
v_reuseFailAlloc_3976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3976_, 0, v_a_3970_);
v___x_3975_ = v_reuseFailAlloc_3976_;
goto v_reusejp_3974_;
}
v_reusejp_3974_:
{
return v___x_3975_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_findRewrites___boxed(lean_object* v_hyps_3978_, lean_object* v_moduleRef_3979_, lean_object* v_goal_3980_, lean_object* v_target_3981_, lean_object* v_forbidden_3982_, lean_object* v_side_3983_, lean_object* v_stopAtRfl_3984_, lean_object* v_max_3985_, lean_object* v_leavePercentHeartbeats_3986_, lean_object* v_a_3987_, lean_object* v_a_3988_, lean_object* v_a_3989_, lean_object* v_a_3990_, lean_object* v_a_3991_){
_start:
{
uint8_t v_side_boxed_3992_; uint8_t v_stopAtRfl_boxed_3993_; lean_object* v_res_3994_; 
v_side_boxed_3992_ = lean_unbox(v_side_3983_);
v_stopAtRfl_boxed_3993_ = lean_unbox(v_stopAtRfl_3984_);
v_res_3994_ = l_Lean_Meta_Rewrites_findRewrites(v_hyps_3978_, v_moduleRef_3979_, v_goal_3980_, v_target_3981_, v_forbidden_3982_, v_side_boxed_3992_, v_stopAtRfl_boxed_3993_, v_max_3985_, v_leavePercentHeartbeats_3986_, v_a_3987_, v_a_3988_, v_a_3989_, v_a_3990_);
lean_dec(v_a_3990_);
lean_dec_ref(v_a_3989_);
lean_dec(v_a_3988_);
lean_dec_ref(v_a_3987_);
lean_dec(v_leavePercentHeartbeats_3986_);
lean_dec(v_forbidden_3982_);
return v_res_3994_;
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

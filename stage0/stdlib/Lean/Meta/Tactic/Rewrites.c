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
lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_(){
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
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_76_;
v_res_76_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_();
stack->m_obj
 = v_res_76_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2____boxed(lean_object* v_a_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_();
return v_res_78_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_97_; uint8_t v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_97_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_));
v___x_98_ = 0;
v___x_99_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__5_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_));
v___x_100_ = l_Lean_registerTraceClass(v___x_97_, v___x_98_, v___x_99_);
return v___x_100_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_101_;
v_res_101_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_();
stack->m_obj
 = v_res_101_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2____boxed(lean_object* v_a_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_();
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rewriteResultLemma(lean_object* v_r_107_){
_start:
{
lean_object* v_eqProof_108_; lean_object* v___x_109_; lean_object* v___x_110_; uint8_t v___x_111_; 
v_eqProof_108_ = lean_ctor_get(v_r_107_, 1);
v___x_109_ = ((lean_object*)(l_Lean_Meta_Rewrites_rewriteResultLemma___closed__1));
v___x_110_ = lean_unsigned_to_nat(6u);
v___x_111_ = l_Lean_Expr_isAppOfArity(v_eqProof_108_, v___x_109_, v___x_110_);
if (v___x_111_ == 0)
{
lean_object* v___x_112_; 
v___x_112_ = lean_box(0);
return v___x_112_;
}
else
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_113_ = lean_unsigned_to_nat(5u);
v___x_114_ = l_Lean_Expr_getAppNumArgs(v_eqProof_108_);
v___x_115_ = lean_nat_sub(v___x_114_, v___x_113_);
lean_dec(v___x_114_);
v___x_116_ = lean_unsigned_to_nat(1u);
v___x_117_ = lean_nat_sub(v___x_115_, v___x_116_);
lean_dec(v___x_115_);
v___x_118_ = l_Lean_Expr_getRevArg_x21(v_eqProof_108_, v___x_117_);
v___x_119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_119_, 0, v___x_118_);
return v___x_119_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rewriteResultLemma___boxed(lean_object* v_r_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Lean_Meta_Rewrites_rewriteResultLemma(v_r_120_);
lean_dec_ref(v_r_120_);
return v_res_121_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_forwardWeight(void){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = lean_unsigned_to_nat(2u);
return v___x_122_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_backwardWeight(void){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = lean_unsigned_to_nat(1u);
return v___x_123_;
}
}
lean_object* l_Lean_Meta_Rewrites_RwDirection_ctorIdx___impl(uint8_t v_x_124_){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_125_ = lean_box(v_x_124_);
v___x_126_ = lean_obj_tag_nat(v___x_125_);
lean_dec(v___x_125_);
return v___x_126_;
}
}
LEAN_EXPORT void l_Lean_Meta_Rewrites_RwDirection_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_124_ = stack[0].m_num;
lean_object* v_res_127_;
v_res_127_ = l_Lean_Meta_Rewrites_RwDirection_ctorIdx___impl(v_x_124_);
stack->m_obj
 = v_res_127_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_ctorIdx___impl___boxed(lean_object* v_x_128_){
_start:
{
uint8_t v_x_4__boxed_129_; lean_object* v_res_130_; 
v_x_4__boxed_129_ = lean_unbox(v_x_128_);
v_res_130_ = l_Lean_Meta_Rewrites_RwDirection_ctorIdx___impl(v_x_4__boxed_129_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_ctorElim___redArg(lean_object* v_k_131_){
_start:
{
lean_inc(v_k_131_);
return v_k_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_ctorElim___redArg___boxed(lean_object* v_k_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_Lean_Meta_Rewrites_RwDirection_ctorElim___redArg(v_k_132_);
lean_dec(v_k_132_);
return v_res_133_;
}
}
lean_object* l_Lean_Meta_Rewrites_RwDirection_ctorElim(lean_object* v_motive_134_, lean_object* v_ctorIdx_135_, uint8_t v_t_136_, lean_object* v_h_137_, lean_object* v_k_138_){
_start:
{
lean_inc(v_k_138_);
return v_k_138_;
}
}
LEAN_EXPORT void l_Lean_Meta_Rewrites_RwDirection_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_135_ = stack[1].m_obj;
uint8_t v_t_136_ = stack[2].m_num;
lean_object* v_k_138_ = stack[4].m_obj;
lean_object* v_res_139_;
v_res_139_ = l_Lean_Meta_Rewrites_RwDirection_ctorElim(lean_box(0), v_ctorIdx_135_, v_t_136_, lean_box(0), v_k_138_);
stack->m_obj
 = v_res_139_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_ctorElim___boxed(lean_object* v_motive_140_, lean_object* v_ctorIdx_141_, lean_object* v_t_142_, lean_object* v_h_143_, lean_object* v_k_144_){
_start:
{
uint8_t v_t_boxed_145_; lean_object* v_res_146_; 
v_t_boxed_145_ = lean_unbox(v_t_142_);
v_res_146_ = l_Lean_Meta_Rewrites_RwDirection_ctorElim(v_motive_140_, v_ctorIdx_141_, v_t_boxed_145_, v_h_143_, v_k_144_);
lean_dec(v_k_144_);
lean_dec(v_ctorIdx_141_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_forward_elim___redArg(lean_object* v_forward_147_){
_start:
{
lean_inc(v_forward_147_);
return v_forward_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_forward_elim___redArg___boxed(lean_object* v_forward_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Lean_Meta_Rewrites_RwDirection_forward_elim___redArg(v_forward_148_);
lean_dec(v_forward_148_);
return v_res_149_;
}
}
lean_object* l_Lean_Meta_Rewrites_RwDirection_forward_elim(lean_object* v_motive_150_, uint8_t v_t_151_, lean_object* v_h_152_, lean_object* v_forward_153_){
_start:
{
lean_inc(v_forward_153_);
return v_forward_153_;
}
}
LEAN_EXPORT void l_Lean_Meta_Rewrites_RwDirection_forward_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_151_ = stack[1].m_num;
lean_object* v_forward_153_ = stack[3].m_obj;
lean_object* v_res_154_;
v_res_154_ = l_Lean_Meta_Rewrites_RwDirection_forward_elim(lean_box(0), v_t_151_, lean_box(0), v_forward_153_);
stack->m_obj
 = v_res_154_;
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
lean_object* l_Lean_Meta_Rewrites_RwDirection_backward_elim(lean_object* v_motive_164_, uint8_t v_t_165_, lean_object* v_h_166_, lean_object* v_backward_167_){
_start:
{
lean_inc(v_backward_167_);
return v_backward_167_;
}
}
LEAN_EXPORT void l_Lean_Meta_Rewrites_RwDirection_backward_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_165_ = stack[1].m_num;
lean_object* v_backward_167_ = stack[3].m_obj;
lean_object* v_res_168_;
v_res_168_ = l_Lean_Meta_Rewrites_RwDirection_backward_elim(lean_box(0), v_t_165_, lean_box(0), v_backward_167_);
stack->m_obj
 = v_res_168_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_backward_elim___boxed(lean_object* v_motive_169_, lean_object* v_t_170_, lean_object* v_h_171_, lean_object* v_backward_172_){
_start:
{
uint8_t v_t_boxed_173_; lean_object* v_res_174_; 
v_t_boxed_173_ = lean_unbox(v_t_170_);
v_res_174_ = l_Lean_Meta_Rewrites_RwDirection_backward_elim(v_motive_169_, v_t_boxed_173_, v_h_171_, v_backward_172_);
lean_dec(v_backward_172_);
return v_res_174_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___lam__0(lean_object* v_k_175_, lean_object* v_b_176_, lean_object* v_c_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_){
_start:
{
lean_object* v___x_183_; 
lean_inc(v___y_181_);
lean_inc_ref(v___y_180_);
lean_inc(v___y_179_);
lean_inc_ref(v___y_178_);
v___x_183_ = lean_apply_7(v_k_175_, v_b_176_, v_c_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_, lean_box(0));
return v___x_183_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_175_ = stack[0].m_obj;
lean_object* v_b_176_ = stack[1].m_obj;
lean_object* v_c_177_ = stack[2].m_obj;
lean_object* v___y_178_ = stack[3].m_obj;
lean_object* v___y_179_ = stack[4].m_obj;
lean_object* v___y_180_ = stack[5].m_obj;
lean_object* v___y_181_ = stack[6].m_obj;
lean_object* v_res_184_;
v_res_184_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___lam__0(v_k_175_, v_b_176_, v_c_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_);
stack->m_obj
 = v_res_184_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___lam__0___boxed(lean_object* v_k_185_, lean_object* v_b_186_, lean_object* v_c_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___lam__0(v_k_185_, v_b_186_, v_c_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_);
lean_dec(v___y_191_);
lean_dec_ref(v___y_190_);
lean_dec(v___y_189_);
lean_dec_ref(v___y_188_);
return v_res_193_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg(lean_object* v_type_194_, lean_object* v_k_195_, uint8_t v_cleanupAnnotations_196_, uint8_t v_whnfType_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_){
_start:
{
lean_object* v___f_203_; lean_object* v___x_204_; 
v___f_203_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_203_, 0, v_k_195_);
v___x_204_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_194_, v___f_203_, v_cleanupAnnotations_196_, v_whnfType_197_, v___y_198_, v___y_199_, v___y_200_, v___y_201_);
if (lean_obj_tag(v___x_204_) == 0)
{
lean_object* v_a_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_212_; 
v_a_205_ = lean_ctor_get(v___x_204_, 0);
v_isSharedCheck_212_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_212_ == 0)
{
v___x_207_ = v___x_204_;
v_isShared_208_ = v_isSharedCheck_212_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_a_205_);
lean_dec(v___x_204_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_212_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_210_; 
if (v_isShared_208_ == 0)
{
v___x_210_ = v___x_207_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_a_205_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
}
else
{
lean_object* v_a_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_220_; 
v_a_213_ = lean_ctor_get(v___x_204_, 0);
v_isSharedCheck_220_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_220_ == 0)
{
v___x_215_ = v___x_204_;
v_isShared_216_ = v_isSharedCheck_220_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_a_213_);
lean_dec(v___x_204_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_220_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v___x_218_; 
if (v_isShared_216_ == 0)
{
v___x_218_ = v___x_215_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v_a_213_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
return v___x_218_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_194_ = stack[0].m_obj;
lean_object* v_k_195_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_196_ = stack[2].m_num;
uint8_t v_whnfType_197_ = stack[3].m_num;
lean_object* v___y_198_ = stack[4].m_obj;
lean_object* v___y_199_ = stack[5].m_obj;
lean_object* v___y_200_ = stack[6].m_obj;
lean_object* v___y_201_ = stack[7].m_obj;
lean_object* v_res_221_;
v_res_221_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg(v_type_194_, v_k_195_, v_cleanupAnnotations_196_, v_whnfType_197_, v___y_198_, v___y_199_, v___y_200_, v___y_201_);
stack->m_obj
 = v_res_221_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___boxed(lean_object* v_type_222_, lean_object* v_k_223_, lean_object* v_cleanupAnnotations_224_, lean_object* v_whnfType_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_231_; uint8_t v_whnfType_boxed_232_; lean_object* v_res_233_; 
v_cleanupAnnotations_boxed_231_ = lean_unbox(v_cleanupAnnotations_224_);
v_whnfType_boxed_232_ = lean_unbox(v_whnfType_225_);
v_res_233_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg(v_type_222_, v_k_223_, v_cleanupAnnotations_boxed_231_, v_whnfType_boxed_232_, v___y_226_, v___y_227_, v___y_228_, v___y_229_);
lean_dec(v___y_229_);
lean_dec_ref(v___y_228_);
lean_dec(v___y_227_);
lean_dec_ref(v___y_226_);
return v_res_233_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0(lean_object* v_00_u03b1_234_, lean_object* v_type_235_, lean_object* v_k_236_, uint8_t v_cleanupAnnotations_237_, uint8_t v_whnfType_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg(v_type_235_, v_k_236_, v_cleanupAnnotations_237_, v_whnfType_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_);
return v___x_244_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_235_ = stack[1].m_obj;
lean_object* v_k_236_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_237_ = stack[3].m_num;
uint8_t v_whnfType_238_ = stack[4].m_num;
lean_object* v___y_239_ = stack[5].m_obj;
lean_object* v___y_240_ = stack[6].m_obj;
lean_object* v___y_241_ = stack[7].m_obj;
lean_object* v___y_242_ = stack[8].m_obj;
lean_object* v_res_245_;
v_res_245_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0(lean_box(0), v_type_235_, v_k_236_, v_cleanupAnnotations_237_, v_whnfType_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_);
stack->m_obj
 = v_res_245_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___boxed(lean_object* v_00_u03b1_246_, lean_object* v_type_247_, lean_object* v_k_248_, lean_object* v_cleanupAnnotations_249_, lean_object* v_whnfType_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_256_; uint8_t v_whnfType_boxed_257_; lean_object* v_res_258_; 
v_cleanupAnnotations_boxed_256_ = lean_unbox(v_cleanupAnnotations_249_);
v_whnfType_boxed_257_ = lean_unbox(v_whnfType_250_);
v_res_258_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0(v_00_u03b1_246_, v_type_247_, v_k_248_, v_cleanupAnnotations_boxed_256_, v_whnfType_boxed_257_, v___y_251_, v___y_252_, v___y_253_, v___y_254_);
lean_dec(v___y_254_);
lean_dec_ref(v___y_253_);
lean_dec(v___y_252_);
lean_dec_ref(v___y_251_);
return v_res_258_;
}
}
lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1___redArg(lean_object* v_k_259_, uint8_t v_allowLevelAssignments_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_260_, v_k_259_, v___y_261_, v___y_262_, v___y_263_, v___y_264_);
if (lean_obj_tag(v___x_266_) == 0)
{
lean_object* v_a_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_274_; 
v_a_267_ = lean_ctor_get(v___x_266_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_274_ == 0)
{
v___x_269_ = v___x_266_;
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_a_267_);
lean_dec(v___x_266_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_272_; 
if (v_isShared_270_ == 0)
{
v___x_272_ = v___x_269_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_a_267_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
else
{
lean_object* v_a_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_282_; 
v_a_275_ = lean_ctor_get(v___x_266_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_282_ == 0)
{
v___x_277_ = v___x_266_;
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_a_275_);
lean_dec(v___x_266_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_280_; 
if (v_isShared_278_ == 0)
{
v___x_280_ = v___x_277_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_a_275_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_259_ = stack[0].m_obj;
uint8_t v_allowLevelAssignments_260_ = stack[1].m_num;
lean_object* v___y_261_ = stack[2].m_obj;
lean_object* v___y_262_ = stack[3].m_obj;
lean_object* v___y_263_ = stack[4].m_obj;
lean_object* v___y_264_ = stack[5].m_obj;
lean_object* v_res_283_;
v_res_283_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1___redArg(v_k_259_, v_allowLevelAssignments_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_);
stack->m_obj
 = v_res_283_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1___redArg___boxed(lean_object* v_k_284_, lean_object* v_allowLevelAssignments_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_291_; lean_object* v_res_292_; 
v_allowLevelAssignments_boxed_291_ = lean_unbox(v_allowLevelAssignments_285_);
v_res_292_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1___redArg(v_k_284_, v_allowLevelAssignments_boxed_291_, v___y_286_, v___y_287_, v___y_288_, v___y_289_);
lean_dec(v___y_289_);
lean_dec_ref(v___y_288_);
lean_dec(v___y_287_);
lean_dec_ref(v___y_286_);
return v_res_292_;
}
}
lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1(lean_object* v_00_u03b1_293_, lean_object* v_k_294_, uint8_t v_allowLevelAssignments_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1___redArg(v_k_294_, v_allowLevelAssignments_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_);
return v___x_301_;
}
}
LEAN_EXPORT void l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_294_ = stack[1].m_obj;
uint8_t v_allowLevelAssignments_295_ = stack[2].m_num;
lean_object* v___y_296_ = stack[3].m_obj;
lean_object* v___y_297_ = stack[4].m_obj;
lean_object* v___y_298_ = stack[5].m_obj;
lean_object* v___y_299_ = stack[6].m_obj;
lean_object* v_res_302_;
v_res_302_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1(lean_box(0), v_k_294_, v_allowLevelAssignments_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_);
stack->m_obj
 = v_res_302_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1___boxed(lean_object* v_00_u03b1_303_, lean_object* v_k_304_, lean_object* v_allowLevelAssignments_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_311_; lean_object* v_res_312_; 
v_allowLevelAssignments_boxed_311_ = lean_unbox(v_allowLevelAssignments_305_);
v_res_312_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1(v_00_u03b1_303_, v_k_304_, v_allowLevelAssignments_boxed_311_, v___y_306_, v___y_307_, v___y_308_, v___y_309_);
lean_dec(v___y_309_);
lean_dec_ref(v___y_308_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
return v_res_312_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0(lean_object* v_name_317_, lean_object* v_x_318_, lean_object* v_type_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_){
_start:
{
lean_object* v___x_328_; lean_object* v_fst_329_; 
v___x_328_ = l_Lean_Expr_getAppFnArgs(v_type_319_);
v_fst_329_ = lean_ctor_get(v___x_328_, 0);
lean_inc(v_fst_329_);
if (lean_obj_tag(v_fst_329_) == 1)
{
lean_object* v_pre_330_; 
v_pre_330_ = lean_ctor_get(v_fst_329_, 0);
if (lean_obj_tag(v_pre_330_) == 0)
{
lean_object* v_snd_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_430_; 
v_snd_331_ = lean_ctor_get(v___x_328_, 1);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_328_);
if (v_isSharedCheck_430_ == 0)
{
lean_object* v_unused_431_; 
v_unused_431_ = lean_ctor_get(v___x_328_, 0);
lean_dec(v_unused_431_);
v___x_333_ = v___x_328_;
v_isShared_334_ = v_isSharedCheck_430_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_snd_331_);
lean_dec(v___x_328_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_430_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v_str_335_; lean_object* v___x_336_; uint8_t v___x_337_; 
v_str_335_ = lean_ctor_get(v_fst_329_, 1);
lean_inc_ref(v_str_335_);
lean_dec_ref_known(v_fst_329_, 2);
v___x_336_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__1));
v___x_337_ = lean_string_dec_eq(v_str_335_, v___x_336_);
if (v___x_337_ == 0)
{
lean_object* v___x_338_; uint8_t v___x_339_; 
v___x_338_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__2));
v___x_339_ = lean_string_dec_eq(v_str_335_, v___x_338_);
lean_dec_ref(v_str_335_);
if (v___x_339_ == 0)
{
lean_del_object(v___x_333_);
lean_dec(v_snd_331_);
lean_dec(v_name_317_);
goto v___jp_325_;
}
else
{
lean_object* v___x_340_; lean_object* v___x_341_; uint8_t v___x_342_; 
v___x_340_ = lean_array_get_size(v_snd_331_);
v___x_341_ = lean_unsigned_to_nat(2u);
v___x_342_ = lean_nat_dec_eq(v___x_340_, v___x_341_);
if (v___x_342_ == 0)
{
lean_del_object(v___x_333_);
lean_dec(v_snd_331_);
lean_dec(v_name_317_);
goto v___jp_325_;
}
else
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; uint8_t v___x_348_; lean_object* v___x_349_; lean_object* v___x_351_; 
v___x_343_ = lean_unsigned_to_nat(0u);
v___x_344_ = lean_array_fget(v_snd_331_, v___x_343_);
v___x_345_ = lean_unsigned_to_nat(1u);
v___x_346_ = lean_array_fget(v_snd_331_, v___x_345_);
lean_dec(v_snd_331_);
v___x_347_ = lean_mk_empty_array_with_capacity(v___x_341_);
v___x_348_ = 0;
v___x_349_ = lean_box(v___x_348_);
lean_inc(v_name_317_);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 1, v___x_349_);
lean_ctor_set(v___x_333_, 0, v_name_317_);
v___x_351_ = v___x_333_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v_name_317_);
lean_ctor_set(v_reuseFailAlloc_384_, 1, v___x_349_);
v___x_351_ = v_reuseFailAlloc_384_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
lean_object* v___x_352_; 
v___x_352_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(v___x_344_, v___x_351_, v___y_320_, v___y_321_, v___y_322_, v___y_323_);
if (lean_obj_tag(v___x_352_) == 0)
{
lean_object* v_a_353_; lean_object* v___x_354_; uint8_t v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v_a_353_ = lean_ctor_get(v___x_352_, 0);
lean_inc(v_a_353_);
lean_dec_ref_known(v___x_352_, 1);
v___x_354_ = lean_array_push(v___x_347_, v_a_353_);
v___x_355_ = 1;
v___x_356_ = lean_box(v___x_355_);
v___x_357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_357_, 0, v_name_317_);
lean_ctor_set(v___x_357_, 1, v___x_356_);
v___x_358_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(v___x_346_, v___x_357_, v___y_320_, v___y_321_, v___y_322_, v___y_323_);
if (lean_obj_tag(v___x_358_) == 0)
{
lean_object* v_a_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_367_; 
v_a_359_ = lean_ctor_get(v___x_358_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_358_);
if (v_isSharedCheck_367_ == 0)
{
v___x_361_ = v___x_358_;
v_isShared_362_ = v_isSharedCheck_367_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_a_359_);
lean_dec(v___x_358_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_367_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_363_; lean_object* v___x_365_; 
v___x_363_ = lean_array_push(v___x_354_, v_a_359_);
if (v_isShared_362_ == 0)
{
lean_ctor_set(v___x_361_, 0, v___x_363_);
v___x_365_ = v___x_361_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v___x_363_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
else
{
lean_object* v_a_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_375_; 
lean_dec_ref(v___x_354_);
v_a_368_ = lean_ctor_get(v___x_358_, 0);
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_358_);
if (v_isSharedCheck_375_ == 0)
{
v___x_370_ = v___x_358_;
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_a_368_);
lean_dec(v___x_358_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_373_; 
if (v_isShared_371_ == 0)
{
v___x_373_ = v___x_370_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_a_368_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
}
else
{
lean_object* v_a_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_383_; 
lean_dec_ref(v___x_347_);
lean_dec(v___x_346_);
lean_dec(v_name_317_);
v_a_376_ = lean_ctor_get(v___x_352_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_383_ == 0)
{
v___x_378_ = v___x_352_;
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_a_376_);
lean_dec(v___x_352_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_381_; 
if (v_isShared_379_ == 0)
{
v___x_381_ = v___x_378_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_a_376_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_385_; lean_object* v___x_386_; uint8_t v___x_387_; 
lean_dec_ref(v_str_335_);
v___x_385_ = lean_array_get_size(v_snd_331_);
v___x_386_ = lean_unsigned_to_nat(3u);
v___x_387_ = lean_nat_dec_eq(v___x_385_, v___x_386_);
if (v___x_387_ == 0)
{
lean_del_object(v___x_333_);
lean_dec(v_snd_331_);
lean_dec(v_name_317_);
goto v___jp_325_;
}
else
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; uint8_t v___x_393_; lean_object* v___x_394_; lean_object* v___x_396_; 
v___x_388_ = lean_unsigned_to_nat(1u);
v___x_389_ = lean_array_fget(v_snd_331_, v___x_388_);
v___x_390_ = lean_unsigned_to_nat(2u);
v___x_391_ = lean_array_fget(v_snd_331_, v___x_390_);
lean_dec(v_snd_331_);
v___x_392_ = lean_mk_empty_array_with_capacity(v___x_390_);
v___x_393_ = 0;
v___x_394_ = lean_box(v___x_393_);
lean_inc(v_name_317_);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 1, v___x_394_);
lean_ctor_set(v___x_333_, 0, v_name_317_);
v___x_396_ = v___x_333_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_name_317_);
lean_ctor_set(v_reuseFailAlloc_429_, 1, v___x_394_);
v___x_396_ = v_reuseFailAlloc_429_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
lean_object* v___x_397_; 
v___x_397_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(v___x_389_, v___x_396_, v___y_320_, v___y_321_, v___y_322_, v___y_323_);
if (lean_obj_tag(v___x_397_) == 0)
{
lean_object* v_a_398_; lean_object* v___x_399_; uint8_t v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v_a_398_ = lean_ctor_get(v___x_397_, 0);
lean_inc(v_a_398_);
lean_dec_ref_known(v___x_397_, 1);
v___x_399_ = lean_array_push(v___x_392_, v_a_398_);
v___x_400_ = 1;
v___x_401_ = lean_box(v___x_400_);
v___x_402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_402_, 0, v_name_317_);
lean_ctor_set(v___x_402_, 1, v___x_401_);
v___x_403_ = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(v___x_391_, v___x_402_, v___y_320_, v___y_321_, v___y_322_, v___y_323_);
if (lean_obj_tag(v___x_403_) == 0)
{
lean_object* v_a_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_412_; 
v_a_404_ = lean_ctor_get(v___x_403_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_412_ == 0)
{
v___x_406_ = v___x_403_;
v_isShared_407_ = v_isSharedCheck_412_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_a_404_);
lean_dec(v___x_403_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_412_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_408_; lean_object* v___x_410_; 
v___x_408_ = lean_array_push(v___x_399_, v_a_404_);
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 0, v___x_408_);
v___x_410_ = v___x_406_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v___x_408_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
else
{
lean_object* v_a_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_420_; 
lean_dec_ref(v___x_399_);
v_a_413_ = lean_ctor_get(v___x_403_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_420_ == 0)
{
v___x_415_ = v___x_403_;
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_a_413_);
lean_dec(v___x_403_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_418_; 
if (v_isShared_416_ == 0)
{
v___x_418_ = v___x_415_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_a_413_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
else
{
lean_object* v_a_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_428_; 
lean_dec_ref(v___x_392_);
lean_dec(v___x_391_);
lean_dec(v_name_317_);
v_a_421_ = lean_ctor_get(v___x_397_, 0);
v_isSharedCheck_428_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_428_ == 0)
{
v___x_423_ = v___x_397_;
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_a_421_);
lean_dec(v___x_397_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_426_; 
if (v_isShared_424_ == 0)
{
v___x_426_ = v___x_423_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_a_421_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
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
lean_dec_ref_known(v_fst_329_, 2);
lean_dec_ref(v___x_328_);
lean_dec(v_name_317_);
goto v___jp_325_;
}
}
else
{
lean_dec(v_fst_329_);
lean_dec_ref(v___x_328_);
lean_dec(v_name_317_);
goto v___jp_325_;
}
v___jp_325_:
{
lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_326_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0));
v___x_327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
return v___x_327_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_317_ = stack[0].m_obj;
lean_object* v_x_318_ = stack[1].m_obj;
lean_object* v_type_319_ = stack[2].m_obj;
lean_object* v___y_320_ = stack[3].m_obj;
lean_object* v___y_321_ = stack[4].m_obj;
lean_object* v___y_322_ = stack[5].m_obj;
lean_object* v___y_323_ = stack[6].m_obj;
lean_object* v_res_432_;
v_res_432_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0(v_name_317_, v_x_318_, v_type_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_);
stack->m_obj
 = v_res_432_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___boxed(lean_object* v_name_433_, lean_object* v_x_434_, lean_object* v_type_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0(v_name_433_, v_x_434_, v_type_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
lean_dec(v___y_437_);
lean_dec_ref(v___y_436_);
lean_dec_ref(v_x_434_);
return v_res_441_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__1(uint8_t v___x_442_, lean_object* v_type_443_, lean_object* v___f_444_, uint8_t v___x_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_){
_start:
{
lean_object* v___y_452_; lean_object* v___x_469_; uint8_t v_transparency_470_; uint8_t v___x_471_; 
v___x_469_ = l_Lean_Meta_Context_config(v___y_446_);
v_transparency_470_ = lean_ctor_get_uint8(v___x_469_, 9);
lean_dec_ref(v___x_469_);
v___x_471_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_470_, v___x_442_);
if (v___x_471_ == 0)
{
lean_object* v_keyedConfig_472_; uint8_t v_trackZetaDelta_473_; lean_object* v_zetaDeltaSet_474_; lean_object* v_lctx_475_; lean_object* v_localInstances_476_; lean_object* v_defEqCtx_x3f_477_; lean_object* v_synthPendingDepth_478_; lean_object* v_customCanUnfoldPredicate_x3f_479_; uint8_t v_univApprox_480_; uint8_t v_inTypeClassResolution_481_; uint8_t v_cacheInferType_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_491_; 
v_keyedConfig_472_ = lean_ctor_get(v___y_446_, 0);
v_trackZetaDelta_473_ = lean_ctor_get_uint8(v___y_446_, sizeof(void*)*7);
v_zetaDeltaSet_474_ = lean_ctor_get(v___y_446_, 1);
v_lctx_475_ = lean_ctor_get(v___y_446_, 2);
v_localInstances_476_ = lean_ctor_get(v___y_446_, 3);
v_defEqCtx_x3f_477_ = lean_ctor_get(v___y_446_, 4);
v_synthPendingDepth_478_ = lean_ctor_get(v___y_446_, 5);
v_customCanUnfoldPredicate_x3f_479_ = lean_ctor_get(v___y_446_, 6);
v_univApprox_480_ = lean_ctor_get_uint8(v___y_446_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_481_ = lean_ctor_get_uint8(v___y_446_, sizeof(void*)*7 + 2);
v_cacheInferType_482_ = lean_ctor_get_uint8(v___y_446_, sizeof(void*)*7 + 3);
v_isSharedCheck_491_ = !lean_is_exclusive(v___y_446_);
if (v_isSharedCheck_491_ == 0)
{
v___x_484_ = v___y_446_;
v_isShared_485_ = v_isSharedCheck_491_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_479_);
lean_inc(v_synthPendingDepth_478_);
lean_inc(v_defEqCtx_x3f_477_);
lean_inc(v_localInstances_476_);
lean_inc(v_lctx_475_);
lean_inc(v_zetaDeltaSet_474_);
lean_inc(v_keyedConfig_472_);
lean_dec(v___y_446_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_491_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_486_; lean_object* v___x_488_; 
v___x_486_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_442_, v_keyedConfig_472_);
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 0, v___x_486_);
v___x_488_ = v___x_484_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v___x_486_);
lean_ctor_set(v_reuseFailAlloc_490_, 1, v_zetaDeltaSet_474_);
lean_ctor_set(v_reuseFailAlloc_490_, 2, v_lctx_475_);
lean_ctor_set(v_reuseFailAlloc_490_, 3, v_localInstances_476_);
lean_ctor_set(v_reuseFailAlloc_490_, 4, v_defEqCtx_x3f_477_);
lean_ctor_set(v_reuseFailAlloc_490_, 5, v_synthPendingDepth_478_);
lean_ctor_set(v_reuseFailAlloc_490_, 6, v_customCanUnfoldPredicate_x3f_479_);
lean_ctor_set_uint8(v_reuseFailAlloc_490_, sizeof(void*)*7, v_trackZetaDelta_473_);
lean_ctor_set_uint8(v_reuseFailAlloc_490_, sizeof(void*)*7 + 1, v_univApprox_480_);
lean_ctor_set_uint8(v_reuseFailAlloc_490_, sizeof(void*)*7 + 2, v_inTypeClassResolution_481_);
lean_ctor_set_uint8(v_reuseFailAlloc_490_, sizeof(void*)*7 + 3, v_cacheInferType_482_);
v___x_488_ = v_reuseFailAlloc_490_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
lean_object* v___x_489_; 
v___x_489_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg(v_type_443_, v___f_444_, v___x_445_, v___x_445_, v___x_488_, v___y_447_, v___y_448_, v___y_449_);
lean_dec_ref(v___x_488_);
v___y_452_ = v___x_489_;
goto v___jp_451_;
}
}
}
else
{
lean_object* v___x_492_; 
v___x_492_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg(v_type_443_, v___f_444_, v___x_445_, v___x_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
lean_dec_ref(v___y_446_);
v___y_452_ = v___x_492_;
goto v___jp_451_;
}
v___jp_451_:
{
if (lean_obj_tag(v___y_452_) == 0)
{
lean_object* v_a_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_460_; 
v_a_453_ = lean_ctor_get(v___y_452_, 0);
v_isSharedCheck_460_ = !lean_is_exclusive(v___y_452_);
if (v_isSharedCheck_460_ == 0)
{
v___x_455_ = v___y_452_;
v_isShared_456_ = v_isSharedCheck_460_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_a_453_);
lean_dec(v___y_452_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_460_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_458_; 
if (v_isShared_456_ == 0)
{
v___x_458_ = v___x_455_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_a_453_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
}
else
{
lean_object* v_a_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_468_; 
v_a_461_ = lean_ctor_get(v___y_452_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v___y_452_);
if (v_isSharedCheck_468_ == 0)
{
v___x_463_ = v___y_452_;
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_a_461_);
lean_dec(v___y_452_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_466_; 
if (v_isShared_464_ == 0)
{
v___x_466_ = v___x_463_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_a_461_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_442_ = stack[0].m_num;
lean_object* v_type_443_ = stack[1].m_obj;
lean_object* v___f_444_ = stack[2].m_obj;
uint8_t v___x_445_ = stack[3].m_num;
lean_object* v___y_446_ = stack[4].m_obj;
lean_object* v___y_447_ = stack[5].m_obj;
lean_object* v___y_448_ = stack[6].m_obj;
lean_object* v___y_449_ = stack[7].m_obj;
lean_object* v_res_493_;
v_res_493_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__1(v___x_442_, v_type_443_, v___f_444_, v___x_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
stack->m_obj
 = v_res_493_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__1___boxed(lean_object* v___x_494_, lean_object* v_type_495_, lean_object* v___f_496_, lean_object* v___x_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
uint8_t v___x_5061__boxed_503_; uint8_t v___x_5063__boxed_504_; lean_object* v_res_505_; 
v___x_5061__boxed_503_ = lean_unbox(v___x_494_);
v___x_5063__boxed_504_ = lean_unbox(v___x_497_);
v_res_505_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__1(v___x_5061__boxed_503_, v_type_495_, v___f_496_, v___x_5063__boxed_504_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec(v___y_499_);
return v_res_505_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport(lean_object* v_name_510_, lean_object* v_c_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_){
_start:
{
uint8_t v___x_517_; 
lean_inc_ref(v_c_511_);
v___x_517_ = l_Lean_AsyncConstantInfo_isUnsafe(v_c_511_);
if (v___x_517_ == 0)
{
lean_object* v___f_518_; lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v___y_522_; lean_object* v___y_523_; lean_object* v___x_534_; lean_object* v_env_538_; uint8_t v___x_539_; 
lean_inc_n(v_name_510_, 2);
v___f_518_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___boxed), 8, 1);
lean_closure_set(v___f_518_, 0, v_name_510_);
v___x_534_ = lean_st_ref_get(v_a_515_);
v_env_538_ = lean_ctor_get(v___x_534_, 0);
lean_inc_ref(v_env_538_);
lean_dec(v___x_534_);
v___x_539_ = l_Lean_Meta_allowCompletion(v_env_538_, v_name_510_);
if (v___x_539_ == 0)
{
lean_dec_ref(v___f_518_);
lean_dec_ref(v_c_511_);
lean_dec(v_name_510_);
goto v___jp_535_;
}
else
{
if (v___x_517_ == 0)
{
lean_object* v___x_540_; lean_object* v_env_544_; uint8_t v___x_545_; 
v___x_540_ = lean_st_ref_get(v_a_515_);
v_env_544_ = lean_ctor_get(v___x_540_, 0);
lean_inc_ref(v_env_544_);
lean_dec(v___x_540_);
lean_inc(v_name_510_);
v___x_545_ = l_Lean_Linter_isDeprecated(v_env_544_, v_name_510_);
if (v___x_545_ == 0)
{
if (lean_obj_tag(v_name_510_) == 1)
{
lean_object* v_str_546_; lean_object* v___x_555_; uint8_t v___x_556_; 
v_str_546_ = lean_ctor_get(v_name_510_, 1);
v___x_555_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__1));
v___x_556_ = lean_string_dec_eq(v_str_546_, v___x_555_);
if (v___x_556_ == 0)
{
lean_object* v___x_557_; uint8_t v___x_558_; 
v___x_557_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__2));
v___x_558_ = lean_string_dec_eq(v_str_546_, v___x_557_);
if (v___x_558_ == 0)
{
lean_object* v___x_559_; lean_object* v___x_560_; uint8_t v___x_561_; 
v___x_559_ = lean_string_utf8_byte_size(v_str_546_);
v___x_560_ = lean_unsigned_to_nat(4u);
v___x_561_ = lean_nat_dec_le(v___x_560_, v___x_559_);
if (v___x_561_ == 0)
{
goto v___jp_547_;
}
else
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; uint8_t v___x_565_; 
v___x_562_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__3));
v___x_563_ = lean_unsigned_to_nat(0u);
v___x_564_ = lean_nat_sub(v___x_559_, v___x_560_);
v___x_565_ = lean_string_memcmp(v_str_546_, v___x_562_, v___x_564_, v___x_563_, v___x_560_);
lean_dec(v___x_564_);
if (v___x_565_ == 0)
{
goto v___jp_547_;
}
else
{
lean_dec_ref_known(v_name_510_, 2);
lean_dec_ref(v___f_518_);
lean_dec_ref(v_c_511_);
goto v___jp_541_;
}
}
}
else
{
lean_dec_ref_known(v_name_510_, 2);
lean_dec_ref(v___f_518_);
lean_dec_ref(v_c_511_);
goto v___jp_541_;
}
}
else
{
lean_dec_ref_known(v_name_510_, 2);
lean_dec_ref(v___f_518_);
lean_dec_ref(v_c_511_);
goto v___jp_541_;
}
v___jp_547_:
{
lean_object* v___x_548_; lean_object* v___x_549_; uint8_t v___x_550_; 
v___x_548_ = lean_string_utf8_byte_size(v_str_546_);
v___x_549_ = lean_unsigned_to_nat(5u);
v___x_550_ = lean_nat_dec_le(v___x_549_, v___x_548_);
if (v___x_550_ == 0)
{
v___y_520_ = v_a_512_;
v___y_521_ = v_a_513_;
v___y_522_ = v_a_514_;
v___y_523_ = v_a_515_;
goto v___jp_519_;
}
else
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; uint8_t v___x_554_; 
v___x_551_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__0));
v___x_552_ = lean_unsigned_to_nat(0u);
v___x_553_ = lean_nat_sub(v___x_548_, v___x_549_);
v___x_554_ = lean_string_memcmp(v_str_546_, v___x_551_, v___x_553_, v___x_552_, v___x_549_);
lean_dec(v___x_553_);
if (v___x_554_ == 0)
{
v___y_520_ = v_a_512_;
v___y_521_ = v_a_513_;
v___y_522_ = v_a_514_;
v___y_523_ = v_a_515_;
goto v___jp_519_;
}
else
{
lean_dec_ref_known(v_name_510_, 2);
lean_dec_ref(v___f_518_);
lean_dec_ref(v_c_511_);
goto v___jp_541_;
}
}
}
}
else
{
v___y_520_ = v_a_512_;
v___y_521_ = v_a_513_;
v___y_522_ = v_a_514_;
v___y_523_ = v_a_515_;
goto v___jp_519_;
}
}
else
{
lean_object* v___x_566_; lean_object* v___x_567_; 
lean_dec_ref(v___f_518_);
lean_dec_ref(v_c_511_);
lean_dec(v_name_510_);
v___x_566_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0));
v___x_567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
return v___x_567_;
}
v___jp_541_:
{
lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_542_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0));
v___x_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_543_, 0, v___x_542_);
return v___x_543_;
}
}
else
{
lean_dec_ref(v___f_518_);
lean_dec_ref(v_c_511_);
lean_dec(v_name_510_);
goto v___jp_535_;
}
}
v___jp_519_:
{
uint8_t v___x_524_; 
v___x_524_ = l_Lean_Name_isMetaprogramming(v_name_510_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; lean_object* v_type_526_; uint8_t v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___f_530_; lean_object* v___x_531_; 
v___x_525_ = l_Lean_AsyncConstantInfo_toConstantVal(v_c_511_);
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
lean_dec_ref(v_c_511_);
v___x_532_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0));
v___x_533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_533_, 0, v___x_532_);
return v___x_533_;
}
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
lean_object* v___x_568_; lean_object* v___x_569_; 
lean_dec_ref(v_c_511_);
lean_dec(v_name_510_);
v___x_568_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0));
v___x_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
return v___x_569_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_510_ = stack[0].m_obj;
lean_object* v_c_511_ = stack[1].m_obj;
lean_object* v_a_512_ = stack[2].m_obj;
lean_object* v_a_513_ = stack[3].m_obj;
lean_object* v_a_514_ = stack[4].m_obj;
lean_object* v_a_515_ = stack[5].m_obj;
lean_object* v_res_570_;
v_res_570_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport(v_name_510_, v_c_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_);
stack->m_obj
 = v_res_570_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___boxed(lean_object* v_name_571_, lean_object* v_c_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport(v_name_571_, v_c_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_);
lean_dec(v_a_576_);
lean_dec_ref(v_a_575_);
lean_dec(v_a_574_);
lean_dec_ref(v_a_573_);
return v_res_578_;
}
}
uint8_t l_List_elem___at___00Lean_Meta_Rewrites_localHypotheses_spec__0(lean_object* v_a_579_, lean_object* v_x_580_){
_start:
{
if (lean_obj_tag(v_x_580_) == 0)
{
uint8_t v___x_581_; 
v___x_581_ = 0;
return v___x_581_;
}
else
{
lean_object* v_head_582_; lean_object* v_tail_583_; uint8_t v___x_584_; 
v_head_582_ = lean_ctor_get(v_x_580_, 0);
v_tail_583_ = lean_ctor_get(v_x_580_, 1);
v___x_584_ = l_Lean_instBEqFVarId_beq(v_a_579_, v_head_582_);
if (v___x_584_ == 0)
{
v_x_580_ = v_tail_583_;
goto _start;
}
else
{
return v___x_584_;
}
}
}
}
LEAN_EXPORT void l_List_elem___at___00Lean_Meta_Rewrites_localHypotheses_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_579_ = stack[0].m_obj;
lean_object* v_x_580_ = stack[1].m_obj;
uint8_t v_res_586_;
v_res_586_ = l_List_elem___at___00Lean_Meta_Rewrites_localHypotheses_spec__0(v_a_579_, v_x_580_);
stack->m_num = v_res_586_;
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_Rewrites_localHypotheses_spec__0___boxed(lean_object* v_a_587_, lean_object* v_x_588_){
_start:
{
uint8_t v_res_589_; lean_object* v_r_590_; 
v_res_589_ = l_List_elem___at___00Lean_Meta_Rewrites_localHypotheses_spec__0(v_a_587_, v_x_588_);
lean_dec(v_x_588_);
lean_dec(v_a_587_);
v_r_590_ = lean_box(v_res_589_);
return v_r_590_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_localHypotheses_spec__2(lean_object* v_except_591_, lean_object* v_as_592_, size_t v_sz_593_, size_t v_i_594_, lean_object* v_b_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_){
_start:
{
lean_object* v_a_602_; uint8_t v___x_606_; 
v___x_606_ = lean_usize_dec_lt(v_i_594_, v_sz_593_);
if (v___x_606_ == 0)
{
lean_object* v___x_607_; 
v___x_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_607_, 0, v_b_595_);
return v___x_607_;
}
else
{
lean_object* v_a_608_; lean_object* v___x_609_; uint8_t v___x_610_; 
v_a_608_ = lean_array_uget_borrowed(v_as_592_, v_i_594_);
v___x_609_ = l_Lean_Expr_fvarId_x21(v_a_608_);
v___x_610_ = l_List_elem___at___00Lean_Meta_Rewrites_localHypotheses_spec__0(v___x_609_, v_except_591_);
lean_dec(v___x_609_);
if (v___x_610_ == 0)
{
lean_object* v___x_611_; 
lean_inc(v___y_599_);
lean_inc_ref(v___y_598_);
lean_inc(v___y_597_);
lean_inc_ref(v___y_596_);
lean_inc(v_a_608_);
v___x_611_ = lean_infer_type(v_a_608_, v___y_596_, v___y_597_, v___y_598_, v___y_599_);
if (lean_obj_tag(v___x_611_) == 0)
{
lean_object* v_a_612_; lean_object* v___x_613_; uint8_t v___x_614_; lean_object* v___x_615_; 
v_a_612_ = lean_ctor_get(v___x_611_, 0);
lean_inc(v_a_612_);
lean_dec_ref_known(v___x_611_, 1);
v___x_613_ = lean_box(0);
v___x_614_ = 0;
v___x_615_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_612_, v___x_613_, v___x_614_, v___y_596_, v___y_597_, v___y_598_, v___y_599_);
if (lean_obj_tag(v___x_615_) == 0)
{
lean_object* v_a_616_; lean_object* v_snd_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_688_; 
v_a_616_ = lean_ctor_get(v___x_615_, 0);
lean_inc(v_a_616_);
lean_dec_ref_known(v___x_615_, 1);
v_snd_617_ = lean_ctor_get(v_a_616_, 1);
v_isSharedCheck_688_ = !lean_is_exclusive(v_a_616_);
if (v_isSharedCheck_688_ == 0)
{
lean_object* v_unused_689_; 
v_unused_689_ = lean_ctor_get(v_a_616_, 0);
lean_dec(v_unused_689_);
v___x_619_ = v_a_616_;
v_isShared_620_ = v_isSharedCheck_688_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_snd_617_);
lean_dec(v_a_616_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_688_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v_snd_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_686_; 
v_snd_621_ = lean_ctor_get(v_snd_617_, 1);
v_isSharedCheck_686_ = !lean_is_exclusive(v_snd_617_);
if (v_isSharedCheck_686_ == 0)
{
lean_object* v_unused_687_; 
v_unused_687_ = lean_ctor_get(v_snd_617_, 0);
lean_dec(v_unused_687_);
v___x_623_ = v_snd_617_;
v_isShared_624_ = v_isSharedCheck_686_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_snd_621_);
lean_dec(v_snd_617_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_686_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_625_; 
v___x_625_ = l_Lean_Meta_whnfR(v_snd_621_, v___y_596_, v___y_597_, v___y_598_, v___y_599_);
if (lean_obj_tag(v___x_625_) == 0)
{
lean_object* v_a_626_; lean_object* v___x_627_; lean_object* v_fst_628_; 
v_a_626_ = lean_ctor_get(v___x_625_, 0);
lean_inc(v_a_626_);
lean_dec_ref_known(v___x_625_, 1);
v___x_627_ = l_Lean_Expr_getAppFnArgs(v_a_626_);
v_fst_628_ = lean_ctor_get(v___x_627_, 0);
lean_inc(v_fst_628_);
if (lean_obj_tag(v_fst_628_) == 1)
{
lean_object* v_pre_629_; 
v_pre_629_ = lean_ctor_get(v_fst_628_, 0);
if (lean_obj_tag(v_pre_629_) == 0)
{
lean_object* v_snd_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_676_; 
v_snd_630_ = lean_ctor_get(v___x_627_, 1);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_676_ == 0)
{
lean_object* v_unused_677_; 
v_unused_677_ = lean_ctor_get(v___x_627_, 0);
lean_dec(v_unused_677_);
v___x_632_ = v___x_627_;
v_isShared_633_ = v_isSharedCheck_676_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_snd_630_);
lean_dec(v___x_627_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_676_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v_str_634_; lean_object* v___x_635_; uint8_t v___x_636_; 
v_str_634_ = lean_ctor_get(v_fst_628_, 1);
lean_inc_ref(v_str_634_);
lean_dec_ref_known(v_fst_628_, 2);
v___x_635_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__1));
v___x_636_ = lean_string_dec_eq(v_str_634_, v___x_635_);
if (v___x_636_ == 0)
{
lean_object* v___x_637_; uint8_t v___x_638_; 
v___x_637_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__2));
v___x_638_ = lean_string_dec_eq(v_str_634_, v___x_637_);
lean_dec_ref(v_str_634_);
if (v___x_638_ == 0)
{
lean_del_object(v___x_632_);
lean_dec(v_snd_630_);
lean_del_object(v___x_623_);
lean_del_object(v___x_619_);
v_a_602_ = v_b_595_;
goto v___jp_601_;
}
else
{
lean_object* v___x_639_; lean_object* v___x_640_; uint8_t v___x_641_; 
v___x_639_ = lean_array_get_size(v_snd_630_);
lean_dec(v_snd_630_);
v___x_640_ = lean_unsigned_to_nat(2u);
v___x_641_ = lean_nat_dec_eq(v___x_639_, v___x_640_);
if (v___x_641_ == 0)
{
lean_del_object(v___x_632_);
lean_del_object(v___x_623_);
lean_del_object(v___x_619_);
v_a_602_ = v_b_595_;
goto v___jp_601_;
}
else
{
lean_object* v___x_642_; lean_object* v___x_644_; 
v___x_642_ = lean_box(v___x_610_);
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 1, v___x_640_);
lean_ctor_set(v___x_632_, 0, v___x_642_);
v___x_644_ = v___x_632_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v___x_642_);
lean_ctor_set(v_reuseFailAlloc_656_, 1, v___x_640_);
v___x_644_ = v_reuseFailAlloc_656_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
lean_object* v___x_646_; 
lean_inc(v_a_608_);
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 1, v___x_644_);
lean_ctor_set(v___x_623_, 0, v_a_608_);
v___x_646_ = v___x_623_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_a_608_);
lean_ctor_set(v_reuseFailAlloc_655_, 1, v___x_644_);
v___x_646_ = v_reuseFailAlloc_655_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_651_; 
v___x_647_ = lean_array_push(v_b_595_, v___x_646_);
v___x_648_ = lean_unsigned_to_nat(1u);
v___x_649_ = lean_box(v___x_606_);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 1, v___x_648_);
lean_ctor_set(v___x_619_, 0, v___x_649_);
v___x_651_ = v___x_619_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v___x_649_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v___x_648_);
v___x_651_ = v_reuseFailAlloc_654_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
lean_object* v___x_652_; lean_object* v___x_653_; 
lean_inc(v_a_608_);
v___x_652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_652_, 0, v_a_608_);
lean_ctor_set(v___x_652_, 1, v___x_651_);
v___x_653_ = lean_array_push(v___x_647_, v___x_652_);
v_a_602_ = v___x_653_;
goto v___jp_601_;
}
}
}
}
}
}
else
{
lean_object* v___x_657_; lean_object* v___x_658_; uint8_t v___x_659_; 
lean_dec_ref(v_str_634_);
v___x_657_ = lean_array_get_size(v_snd_630_);
lean_dec(v_snd_630_);
v___x_658_ = lean_unsigned_to_nat(3u);
v___x_659_ = lean_nat_dec_eq(v___x_657_, v___x_658_);
if (v___x_659_ == 0)
{
lean_del_object(v___x_632_);
lean_del_object(v___x_623_);
lean_del_object(v___x_619_);
v_a_602_ = v_b_595_;
goto v___jp_601_;
}
else
{
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_663_; 
v___x_660_ = lean_unsigned_to_nat(2u);
v___x_661_ = lean_box(v___x_610_);
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 1, v___x_660_);
lean_ctor_set(v___x_632_, 0, v___x_661_);
v___x_663_ = v___x_632_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v___x_661_);
lean_ctor_set(v_reuseFailAlloc_675_, 1, v___x_660_);
v___x_663_ = v_reuseFailAlloc_675_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
lean_object* v___x_665_; 
lean_inc(v_a_608_);
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 1, v___x_663_);
lean_ctor_set(v___x_623_, 0, v_a_608_);
v___x_665_ = v___x_623_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_a_608_);
lean_ctor_set(v_reuseFailAlloc_674_, 1, v___x_663_);
v___x_665_ = v_reuseFailAlloc_674_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_670_; 
v___x_666_ = lean_array_push(v_b_595_, v___x_665_);
v___x_667_ = lean_unsigned_to_nat(1u);
v___x_668_ = lean_box(v___x_606_);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 1, v___x_667_);
lean_ctor_set(v___x_619_, 0, v___x_668_);
v___x_670_ = v___x_619_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v___x_668_);
lean_ctor_set(v_reuseFailAlloc_673_, 1, v___x_667_);
v___x_670_ = v_reuseFailAlloc_673_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
lean_object* v___x_671_; lean_object* v___x_672_; 
lean_inc(v_a_608_);
v___x_671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_671_, 0, v_a_608_);
lean_ctor_set(v___x_671_, 1, v___x_670_);
v___x_672_ = lean_array_push(v___x_666_, v___x_671_);
v_a_602_ = v___x_672_;
goto v___jp_601_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_fst_628_, 2);
lean_dec_ref(v___x_627_);
lean_del_object(v___x_623_);
lean_del_object(v___x_619_);
v_a_602_ = v_b_595_;
goto v___jp_601_;
}
}
else
{
lean_dec(v_fst_628_);
lean_dec_ref(v___x_627_);
lean_del_object(v___x_623_);
lean_del_object(v___x_619_);
v_a_602_ = v_b_595_;
goto v___jp_601_;
}
}
else
{
lean_object* v_a_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_685_; 
lean_del_object(v___x_623_);
lean_del_object(v___x_619_);
lean_dec_ref(v_b_595_);
v_a_678_ = lean_ctor_get(v___x_625_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_625_);
if (v_isSharedCheck_685_ == 0)
{
v___x_680_ = v___x_625_;
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_a_678_);
lean_dec(v___x_625_);
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
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_697_; 
lean_dec_ref(v_b_595_);
v_a_690_ = lean_ctor_get(v___x_615_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_697_ == 0)
{
v___x_692_ = v___x_615_;
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_615_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_695_; 
if (v_isShared_693_ == 0)
{
v___x_695_ = v___x_692_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_a_690_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
}
else
{
lean_object* v_a_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_705_; 
lean_dec_ref(v_b_595_);
v_a_698_ = lean_ctor_get(v___x_611_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_611_);
if (v_isSharedCheck_705_ == 0)
{
v___x_700_ = v___x_611_;
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_dec(v___x_611_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_703_; 
if (v_isShared_701_ == 0)
{
v___x_703_ = v___x_700_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_a_698_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
}
else
{
v_a_602_ = v_b_595_;
goto v___jp_601_;
}
}
v___jp_601_:
{
size_t v___x_603_; size_t v___x_604_; 
v___x_603_ = ((size_t)1ULL);
v___x_604_ = lean_usize_add(v_i_594_, v___x_603_);
v_i_594_ = v___x_604_;
v_b_595_ = v_a_602_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_localHypotheses_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_except_591_ = stack[0].m_obj;
lean_object* v_as_592_ = stack[1].m_obj;
size_t v_sz_593_ = stack[2].m_num;
size_t v_i_594_ = stack[3].m_num;
lean_object* v_b_595_ = stack[4].m_obj;
lean_object* v___y_596_ = stack[5].m_obj;
lean_object* v___y_597_ = stack[6].m_obj;
lean_object* v___y_598_ = stack[7].m_obj;
lean_object* v___y_599_ = stack[8].m_obj;
lean_object* v_res_706_;
v_res_706_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_localHypotheses_spec__2(v_except_591_, v_as_592_, v_sz_593_, v_i_594_, v_b_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_);
stack->m_obj
 = v_res_706_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_localHypotheses_spec__2___boxed(lean_object* v_except_707_, lean_object* v_as_708_, lean_object* v_sz_709_, lean_object* v_i_710_, lean_object* v_b_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
size_t v_sz_boxed_717_; size_t v_i_boxed_718_; lean_object* v_res_719_; 
v_sz_boxed_717_ = lean_unbox_usize(v_sz_709_);
lean_dec(v_sz_709_);
v_i_boxed_718_ = lean_unbox_usize(v_i_710_);
lean_dec(v_i_710_);
v_res_719_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_localHypotheses_spec__2(v_except_707_, v_as_708_, v_sz_boxed_717_, v_i_boxed_718_, v_b_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
lean_dec(v___y_713_);
lean_dec_ref(v___y_712_);
lean_dec_ref(v_as_708_);
lean_dec(v_except_707_);
return v_res_719_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(lean_object* v_as_720_, size_t v_sz_721_, size_t v_i_722_, lean_object* v_b_723_){
_start:
{
uint8_t v___x_725_; 
v___x_725_ = lean_usize_dec_lt(v_i_722_, v_sz_721_);
if (v___x_725_ == 0)
{
lean_object* v___x_726_; 
v___x_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_726_, 0, v_b_723_);
return v___x_726_;
}
else
{
lean_object* v_snd_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_745_; 
v_snd_727_ = lean_ctor_get(v_b_723_, 1);
v_isSharedCheck_745_ = !lean_is_exclusive(v_b_723_);
if (v_isSharedCheck_745_ == 0)
{
lean_object* v_unused_746_; 
v_unused_746_ = lean_ctor_get(v_b_723_, 0);
lean_dec(v_unused_746_);
v___x_729_ = v_b_723_;
v_isShared_730_ = v_isSharedCheck_745_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_snd_727_);
lean_dec(v_b_723_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_745_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_731_; lean_object* v_a_733_; lean_object* v_a_740_; 
v___x_731_ = lean_box(0);
v_a_740_ = lean_array_uget_borrowed(v_as_720_, v_i_722_);
if (lean_obj_tag(v_a_740_) == 0)
{
v_a_733_ = v_snd_727_;
goto v___jp_732_;
}
else
{
lean_object* v_val_741_; uint8_t v___x_742_; 
v_val_741_ = lean_ctor_get(v_a_740_, 0);
v___x_742_ = l_Lean_LocalDecl_isImplementationDetail(v_val_741_);
if (v___x_742_ == 0)
{
lean_object* v___x_743_; lean_object* v___x_744_; 
lean_inc(v_val_741_);
v___x_743_ = l_Lean_LocalDecl_toExpr(v_val_741_);
v___x_744_ = lean_array_push(v_snd_727_, v___x_743_);
v_a_733_ = v___x_744_;
goto v___jp_732_;
}
else
{
v_a_733_ = v_snd_727_;
goto v___jp_732_;
}
}
v___jp_732_:
{
lean_object* v___x_735_; 
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 1, v_a_733_);
lean_ctor_set(v___x_729_, 0, v___x_731_);
v___x_735_ = v___x_729_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v___x_731_);
lean_ctor_set(v_reuseFailAlloc_739_, 1, v_a_733_);
v___x_735_ = v_reuseFailAlloc_739_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
size_t v___x_736_; size_t v___x_737_; 
v___x_736_ = ((size_t)1ULL);
v___x_737_ = lean_usize_add(v_i_722_, v___x_736_);
v_i_722_ = v___x_737_;
v_b_723_ = v___x_735_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_720_ = stack[0].m_obj;
size_t v_sz_721_ = stack[1].m_num;
size_t v_i_722_ = stack[2].m_num;
lean_object* v_b_723_ = stack[3].m_obj;
lean_object* v_res_747_;
v_res_747_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(v_as_720_, v_sz_721_, v_i_722_, v_b_723_);
stack->m_obj
 = v_res_747_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___redArg___boxed(lean_object* v_as_748_, lean_object* v_sz_749_, lean_object* v_i_750_, lean_object* v_b_751_, lean_object* v___y_752_){
_start:
{
size_t v_sz_boxed_753_; size_t v_i_boxed_754_; lean_object* v_res_755_; 
v_sz_boxed_753_ = lean_unbox_usize(v_sz_749_);
lean_dec(v_sz_749_);
v_i_boxed_754_ = lean_unbox_usize(v_i_750_);
lean_dec(v_i_750_);
v_res_755_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(v_as_748_, v_sz_boxed_753_, v_i_boxed_754_, v_b_751_);
lean_dec_ref(v_as_748_);
return v_res_755_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5(lean_object* v_as_756_, size_t v_sz_757_, size_t v_i_758_, lean_object* v_b_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
uint8_t v___x_765_; 
v___x_765_ = lean_usize_dec_lt(v_i_758_, v_sz_757_);
if (v___x_765_ == 0)
{
lean_object* v___x_766_; 
v___x_766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_766_, 0, v_b_759_);
return v___x_766_;
}
else
{
lean_object* v_snd_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_785_; 
v_snd_767_ = lean_ctor_get(v_b_759_, 1);
v_isSharedCheck_785_ = !lean_is_exclusive(v_b_759_);
if (v_isSharedCheck_785_ == 0)
{
lean_object* v_unused_786_; 
v_unused_786_ = lean_ctor_get(v_b_759_, 0);
lean_dec(v_unused_786_);
v___x_769_ = v_b_759_;
v_isShared_770_ = v_isSharedCheck_785_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_snd_767_);
lean_dec(v_b_759_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_785_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_771_; lean_object* v_a_773_; lean_object* v_a_780_; 
v___x_771_ = lean_box(0);
v_a_780_ = lean_array_uget_borrowed(v_as_756_, v_i_758_);
if (lean_obj_tag(v_a_780_) == 0)
{
v_a_773_ = v_snd_767_;
goto v___jp_772_;
}
else
{
lean_object* v_val_781_; uint8_t v___x_782_; 
v_val_781_ = lean_ctor_get(v_a_780_, 0);
v___x_782_ = l_Lean_LocalDecl_isImplementationDetail(v_val_781_);
if (v___x_782_ == 0)
{
lean_object* v___x_783_; lean_object* v___x_784_; 
lean_inc(v_val_781_);
v___x_783_ = l_Lean_LocalDecl_toExpr(v_val_781_);
v___x_784_ = lean_array_push(v_snd_767_, v___x_783_);
v_a_773_ = v___x_784_;
goto v___jp_772_;
}
else
{
v_a_773_ = v_snd_767_;
goto v___jp_772_;
}
}
v___jp_772_:
{
lean_object* v___x_775_; 
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 1, v_a_773_);
lean_ctor_set(v___x_769_, 0, v___x_771_);
v___x_775_ = v___x_769_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v___x_771_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v_a_773_);
v___x_775_ = v_reuseFailAlloc_779_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
size_t v___x_776_; size_t v___x_777_; lean_object* v___x_778_; 
v___x_776_ = ((size_t)1ULL);
v___x_777_ = lean_usize_add(v_i_758_, v___x_776_);
v___x_778_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(v_as_756_, v_sz_757_, v___x_777_, v___x_775_);
return v___x_778_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_756_ = stack[0].m_obj;
size_t v_sz_757_ = stack[1].m_num;
size_t v_i_758_ = stack[2].m_num;
lean_object* v_b_759_ = stack[3].m_obj;
lean_object* v___y_760_ = stack[4].m_obj;
lean_object* v___y_761_ = stack[5].m_obj;
lean_object* v___y_762_ = stack[6].m_obj;
lean_object* v___y_763_ = stack[7].m_obj;
lean_object* v_res_787_;
v_res_787_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5(v_as_756_, v_sz_757_, v_i_758_, v_b_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
stack->m_obj
 = v_res_787_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5___boxed(lean_object* v_as_788_, lean_object* v_sz_789_, lean_object* v_i_790_, lean_object* v_b_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_){
_start:
{
size_t v_sz_boxed_797_; size_t v_i_boxed_798_; lean_object* v_res_799_; 
v_sz_boxed_797_ = lean_unbox_usize(v_sz_789_);
lean_dec(v_sz_789_);
v_i_boxed_798_ = lean_unbox_usize(v_i_790_);
lean_dec(v_i_790_);
v_res_799_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5(v_as_788_, v_sz_boxed_797_, v_i_boxed_798_, v_b_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
lean_dec(v___y_793_);
lean_dec_ref(v___y_792_);
lean_dec_ref(v_as_788_);
return v_res_799_;
}
}
lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2(lean_object* v_init_800_, lean_object* v_n_801_, lean_object* v_b_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_){
_start:
{
if (lean_obj_tag(v_n_801_) == 0)
{
lean_object* v_cs_808_; lean_object* v___x_809_; lean_object* v___x_810_; size_t v_sz_811_; size_t v___x_812_; lean_object* v___x_813_; 
v_cs_808_ = lean_ctor_get(v_n_801_, 0);
v___x_809_ = lean_box(0);
v___x_810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_810_, 0, v___x_809_);
lean_ctor_set(v___x_810_, 1, v_b_802_);
v_sz_811_ = lean_array_size(v_cs_808_);
v___x_812_ = ((size_t)0ULL);
v___x_813_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__4(v_init_800_, v_cs_808_, v_sz_811_, v___x_812_, v___x_810_, v___y_803_, v___y_804_, v___y_805_, v___y_806_);
if (lean_obj_tag(v___x_813_) == 0)
{
lean_object* v_a_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_828_; 
v_a_814_ = lean_ctor_get(v___x_813_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_828_ == 0)
{
v___x_816_ = v___x_813_;
v_isShared_817_ = v_isSharedCheck_828_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_dec(v___x_813_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_828_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v_fst_818_; 
v_fst_818_ = lean_ctor_get(v_a_814_, 0);
if (lean_obj_tag(v_fst_818_) == 0)
{
lean_object* v_snd_819_; lean_object* v___x_820_; lean_object* v___x_822_; 
v_snd_819_ = lean_ctor_get(v_a_814_, 1);
lean_inc(v_snd_819_);
lean_dec(v_a_814_);
v___x_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_820_, 0, v_snd_819_);
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 0, v___x_820_);
v___x_822_ = v___x_816_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_820_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
else
{
lean_object* v_val_824_; lean_object* v___x_826_; 
lean_inc_ref(v_fst_818_);
lean_dec(v_a_814_);
v_val_824_ = lean_ctor_get(v_fst_818_, 0);
lean_inc(v_val_824_);
lean_dec_ref_known(v_fst_818_, 1);
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 0, v_val_824_);
v___x_826_ = v___x_816_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_val_824_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
}
else
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_836_; 
v_a_829_ = lean_ctor_get(v___x_813_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_836_ == 0)
{
v___x_831_ = v___x_813_;
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_813_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_a_829_);
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
lean_object* v_vs_837_; lean_object* v___x_838_; lean_object* v___x_839_; size_t v_sz_840_; size_t v___x_841_; lean_object* v___x_842_; 
v_vs_837_ = lean_ctor_get(v_n_801_, 0);
v___x_838_ = lean_box(0);
v___x_839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_839_, 0, v___x_838_);
lean_ctor_set(v___x_839_, 1, v_b_802_);
v_sz_840_ = lean_array_size(v_vs_837_);
v___x_841_ = ((size_t)0ULL);
v___x_842_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5(v_vs_837_, v_sz_840_, v___x_841_, v___x_839_, v___y_803_, v___y_804_, v___y_805_, v___y_806_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_857_; 
v_a_843_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_857_ == 0)
{
v___x_845_ = v___x_842_;
v_isShared_846_ = v_isSharedCheck_857_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_842_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_857_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v_fst_847_; 
v_fst_847_ = lean_ctor_get(v_a_843_, 0);
if (lean_obj_tag(v_fst_847_) == 0)
{
lean_object* v_snd_848_; lean_object* v___x_849_; lean_object* v___x_851_; 
v_snd_848_ = lean_ctor_get(v_a_843_, 1);
lean_inc(v_snd_848_);
lean_dec(v_a_843_);
v___x_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_849_, 0, v_snd_848_);
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 0, v___x_849_);
v___x_851_ = v___x_845_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v___x_849_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
else
{
lean_object* v_val_853_; lean_object* v___x_855_; 
lean_inc_ref(v_fst_847_);
lean_dec(v_a_843_);
v_val_853_ = lean_ctor_get(v_fst_847_, 0);
lean_inc(v_val_853_);
lean_dec_ref_known(v_fst_847_, 1);
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 0, v_val_853_);
v___x_855_ = v___x_845_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_val_853_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
else
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_865_; 
v_a_858_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_865_ == 0)
{
v___x_860_ = v___x_842_;
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_842_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_863_; 
if (v_isShared_861_ == 0)
{
v___x_863_ = v___x_860_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_a_858_);
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
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_800_ = stack[0].m_obj;
lean_object* v_n_801_ = stack[1].m_obj;
lean_object* v_b_802_ = stack[2].m_obj;
lean_object* v___y_803_ = stack[3].m_obj;
lean_object* v___y_804_ = stack[4].m_obj;
lean_object* v___y_805_ = stack[5].m_obj;
lean_object* v___y_806_ = stack[6].m_obj;
lean_object* v_res_866_;
v_res_866_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2(v_init_800_, v_n_801_, v_b_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_);
stack->m_obj
 = v_res_866_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__4(lean_object* v_init_867_, lean_object* v_as_868_, size_t v_sz_869_, size_t v_i_870_, lean_object* v_b_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_){
_start:
{
uint8_t v___x_877_; 
v___x_877_ = lean_usize_dec_lt(v_i_870_, v_sz_869_);
if (v___x_877_ == 0)
{
lean_object* v___x_878_; 
v___x_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_878_, 0, v_b_871_);
return v___x_878_;
}
else
{
lean_object* v_snd_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_913_; 
v_snd_879_ = lean_ctor_get(v_b_871_, 1);
v_isSharedCheck_913_ = !lean_is_exclusive(v_b_871_);
if (v_isSharedCheck_913_ == 0)
{
lean_object* v_unused_914_; 
v_unused_914_ = lean_ctor_get(v_b_871_, 0);
lean_dec(v_unused_914_);
v___x_881_ = v_b_871_;
v_isShared_882_ = v_isSharedCheck_913_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_snd_879_);
lean_dec(v_b_871_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_913_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_883_; lean_object* v_a_884_; lean_object* v___x_885_; 
v___x_883_ = lean_box(0);
v_a_884_ = lean_array_uget_borrowed(v_as_868_, v_i_870_);
lean_inc(v_snd_879_);
v___x_885_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2(v_init_867_, v_a_884_, v_snd_879_, v___y_872_, v___y_873_, v___y_874_, v___y_875_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_904_; 
v_a_886_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_904_ == 0)
{
v___x_888_ = v___x_885_;
v_isShared_889_ = v_isSharedCheck_904_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_885_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_904_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
if (lean_obj_tag(v_a_886_) == 0)
{
lean_object* v___x_890_; lean_object* v___x_892_; 
v___x_890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_890_, 0, v_a_886_);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 0, v___x_890_);
v___x_892_ = v___x_881_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_890_);
lean_ctor_set(v_reuseFailAlloc_896_, 1, v_snd_879_);
v___x_892_ = v_reuseFailAlloc_896_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
lean_object* v___x_894_; 
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 0, v___x_892_);
v___x_894_ = v___x_888_;
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
else
{
lean_object* v_a_897_; lean_object* v___x_899_; 
lean_del_object(v___x_888_);
lean_dec(v_snd_879_);
v_a_897_ = lean_ctor_get(v_a_886_, 0);
lean_inc(v_a_897_);
lean_dec_ref_known(v_a_886_, 1);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 1, v_a_897_);
lean_ctor_set(v___x_881_, 0, v___x_883_);
v___x_899_ = v___x_881_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v___x_883_);
lean_ctor_set(v_reuseFailAlloc_903_, 1, v_a_897_);
v___x_899_ = v_reuseFailAlloc_903_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
size_t v___x_900_; size_t v___x_901_; 
v___x_900_ = ((size_t)1ULL);
v___x_901_ = lean_usize_add(v_i_870_, v___x_900_);
v_i_870_ = v___x_901_;
v_b_871_ = v___x_899_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_912_; 
lean_del_object(v___x_881_);
lean_dec(v_snd_879_);
v_a_905_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_912_ == 0)
{
v___x_907_ = v___x_885_;
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_a_905_);
lean_dec(v___x_885_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_910_; 
if (v_isShared_908_ == 0)
{
v___x_910_ = v___x_907_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_a_905_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_867_ = stack[0].m_obj;
lean_object* v_as_868_ = stack[1].m_obj;
size_t v_sz_869_ = stack[2].m_num;
size_t v_i_870_ = stack[3].m_num;
lean_object* v_b_871_ = stack[4].m_obj;
lean_object* v___y_872_ = stack[5].m_obj;
lean_object* v___y_873_ = stack[6].m_obj;
lean_object* v___y_874_ = stack[7].m_obj;
lean_object* v___y_875_ = stack[8].m_obj;
lean_object* v_res_915_;
v_res_915_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__4(v_init_867_, v_as_868_, v_sz_869_, v_i_870_, v_b_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_);
stack->m_obj
 = v_res_915_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_init_916_, lean_object* v_as_917_, lean_object* v_sz_918_, lean_object* v_i_919_, lean_object* v_b_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
size_t v_sz_boxed_926_; size_t v_i_boxed_927_; lean_object* v_res_928_; 
v_sz_boxed_926_ = lean_unbox_usize(v_sz_918_);
lean_dec(v_sz_918_);
v_i_boxed_927_ = lean_unbox_usize(v_i_919_);
lean_dec(v_i_919_);
v_res_928_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__4(v_init_916_, v_as_917_, v_sz_boxed_926_, v_i_boxed_927_, v_b_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec_ref(v_as_917_);
lean_dec_ref(v_init_916_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2___boxed(lean_object* v_init_929_, lean_object* v_n_930_, lean_object* v_b_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2(v_init_929_, v_n_930_, v_b_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec_ref(v_n_930_);
lean_dec_ref(v_init_929_);
return v_res_937_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___redArg(lean_object* v_as_938_, size_t v_sz_939_, size_t v_i_940_, lean_object* v_b_941_){
_start:
{
uint8_t v___x_943_; 
v___x_943_ = lean_usize_dec_lt(v_i_940_, v_sz_939_);
if (v___x_943_ == 0)
{
lean_object* v___x_944_; 
v___x_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_944_, 0, v_b_941_);
return v___x_944_;
}
else
{
lean_object* v_snd_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_963_; 
v_snd_945_ = lean_ctor_get(v_b_941_, 1);
v_isSharedCheck_963_ = !lean_is_exclusive(v_b_941_);
if (v_isSharedCheck_963_ == 0)
{
lean_object* v_unused_964_; 
v_unused_964_ = lean_ctor_get(v_b_941_, 0);
lean_dec(v_unused_964_);
v___x_947_ = v_b_941_;
v_isShared_948_ = v_isSharedCheck_963_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_snd_945_);
lean_dec(v_b_941_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_963_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_949_; lean_object* v_a_951_; lean_object* v_a_958_; 
v___x_949_ = lean_box(0);
v_a_958_ = lean_array_uget_borrowed(v_as_938_, v_i_940_);
if (lean_obj_tag(v_a_958_) == 0)
{
v_a_951_ = v_snd_945_;
goto v___jp_950_;
}
else
{
lean_object* v_val_959_; uint8_t v___x_960_; 
v_val_959_ = lean_ctor_get(v_a_958_, 0);
v___x_960_ = l_Lean_LocalDecl_isImplementationDetail(v_val_959_);
if (v___x_960_ == 0)
{
lean_object* v___x_961_; lean_object* v___x_962_; 
lean_inc(v_val_959_);
v___x_961_ = l_Lean_LocalDecl_toExpr(v_val_959_);
v___x_962_ = lean_array_push(v_snd_945_, v___x_961_);
v_a_951_ = v___x_962_;
goto v___jp_950_;
}
else
{
v_a_951_ = v_snd_945_;
goto v___jp_950_;
}
}
v___jp_950_:
{
lean_object* v___x_953_; 
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 1, v_a_951_);
lean_ctor_set(v___x_947_, 0, v___x_949_);
v___x_953_ = v___x_947_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v___x_949_);
lean_ctor_set(v_reuseFailAlloc_957_, 1, v_a_951_);
v___x_953_ = v_reuseFailAlloc_957_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
size_t v___x_954_; size_t v___x_955_; 
v___x_954_ = ((size_t)1ULL);
v___x_955_ = lean_usize_add(v_i_940_, v___x_954_);
v_i_940_ = v___x_955_;
v_b_941_ = v___x_953_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_938_ = stack[0].m_obj;
size_t v_sz_939_ = stack[1].m_num;
size_t v_i_940_ = stack[2].m_num;
lean_object* v_b_941_ = stack[3].m_obj;
lean_object* v_res_965_;
v_res_965_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___redArg(v_as_938_, v_sz_939_, v_i_940_, v_b_941_);
stack->m_obj
 = v_res_965_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_as_966_, lean_object* v_sz_967_, lean_object* v_i_968_, lean_object* v_b_969_, lean_object* v___y_970_){
_start:
{
size_t v_sz_boxed_971_; size_t v_i_boxed_972_; lean_object* v_res_973_; 
v_sz_boxed_971_ = lean_unbox_usize(v_sz_967_);
lean_dec(v_sz_967_);
v_i_boxed_972_ = lean_unbox_usize(v_i_968_);
lean_dec(v_i_968_);
v_res_973_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___redArg(v_as_966_, v_sz_boxed_971_, v_i_boxed_972_, v_b_969_);
lean_dec_ref(v_as_966_);
return v_res_973_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3(lean_object* v_as_974_, size_t v_sz_975_, size_t v_i_976_, lean_object* v_b_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
uint8_t v___x_983_; 
v___x_983_ = lean_usize_dec_lt(v_i_976_, v_sz_975_);
if (v___x_983_ == 0)
{
lean_object* v___x_984_; 
v___x_984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_984_, 0, v_b_977_);
return v___x_984_;
}
else
{
lean_object* v_snd_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_1003_; 
v_snd_985_ = lean_ctor_get(v_b_977_, 1);
v_isSharedCheck_1003_ = !lean_is_exclusive(v_b_977_);
if (v_isSharedCheck_1003_ == 0)
{
lean_object* v_unused_1004_; 
v_unused_1004_ = lean_ctor_get(v_b_977_, 0);
lean_dec(v_unused_1004_);
v___x_987_ = v_b_977_;
v_isShared_988_ = v_isSharedCheck_1003_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_snd_985_);
lean_dec(v_b_977_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_1003_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_989_; lean_object* v_a_991_; lean_object* v_a_998_; 
v___x_989_ = lean_box(0);
v_a_998_ = lean_array_uget_borrowed(v_as_974_, v_i_976_);
if (lean_obj_tag(v_a_998_) == 0)
{
v_a_991_ = v_snd_985_;
goto v___jp_990_;
}
else
{
lean_object* v_val_999_; uint8_t v___x_1000_; 
v_val_999_ = lean_ctor_get(v_a_998_, 0);
v___x_1000_ = l_Lean_LocalDecl_isImplementationDetail(v_val_999_);
if (v___x_1000_ == 0)
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
lean_inc(v_val_999_);
v___x_1001_ = l_Lean_LocalDecl_toExpr(v_val_999_);
v___x_1002_ = lean_array_push(v_snd_985_, v___x_1001_);
v_a_991_ = v___x_1002_;
goto v___jp_990_;
}
else
{
v_a_991_ = v_snd_985_;
goto v___jp_990_;
}
}
v___jp_990_:
{
lean_object* v___x_993_; 
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 1, v_a_991_);
lean_ctor_set(v___x_987_, 0, v___x_989_);
v___x_993_ = v___x_987_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v___x_989_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v_a_991_);
v___x_993_ = v_reuseFailAlloc_997_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
size_t v___x_994_; size_t v___x_995_; lean_object* v___x_996_; 
v___x_994_ = ((size_t)1ULL);
v___x_995_ = lean_usize_add(v_i_976_, v___x_994_);
v___x_996_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___redArg(v_as_974_, v_sz_975_, v___x_995_, v___x_993_);
return v___x_996_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_974_ = stack[0].m_obj;
size_t v_sz_975_ = stack[1].m_num;
size_t v_i_976_ = stack[2].m_num;
lean_object* v_b_977_ = stack[3].m_obj;
lean_object* v___y_978_ = stack[4].m_obj;
lean_object* v___y_979_ = stack[5].m_obj;
lean_object* v___y_980_ = stack[6].m_obj;
lean_object* v___y_981_ = stack[7].m_obj;
lean_object* v_res_1005_;
v_res_1005_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3(v_as_974_, v_sz_975_, v_i_976_, v_b_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_);
stack->m_obj
 = v_res_1005_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3___boxed(lean_object* v_as_1006_, lean_object* v_sz_1007_, lean_object* v_i_1008_, lean_object* v_b_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_){
_start:
{
size_t v_sz_boxed_1015_; size_t v_i_boxed_1016_; lean_object* v_res_1017_; 
v_sz_boxed_1015_ = lean_unbox_usize(v_sz_1007_);
lean_dec(v_sz_1007_);
v_i_boxed_1016_ = lean_unbox_usize(v_i_1008_);
lean_dec(v_i_1008_);
v_res_1017_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3(v_as_1006_, v_sz_boxed_1015_, v_i_boxed_1016_, v_b_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec_ref(v_as_1006_);
return v_res_1017_;
}
}
lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1(lean_object* v_t_1018_, lean_object* v_init_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v_root_1025_; lean_object* v_tail_1026_; lean_object* v___x_1027_; 
v_root_1025_ = lean_ctor_get(v_t_1018_, 0);
v_tail_1026_ = lean_ctor_get(v_t_1018_, 1);
lean_inc_ref(v_init_1019_);
v___x_1027_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2(v_init_1019_, v_root_1025_, v_init_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
lean_dec_ref(v_init_1019_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1064_; 
v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1030_ = v___x_1027_;
v_isShared_1031_ = v_isSharedCheck_1064_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_1027_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1064_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
if (lean_obj_tag(v_a_1028_) == 0)
{
lean_object* v_a_1032_; lean_object* v___x_1034_; 
v_a_1032_ = lean_ctor_get(v_a_1028_, 0);
lean_inc(v_a_1032_);
lean_dec_ref_known(v_a_1028_, 1);
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 0, v_a_1032_);
v___x_1034_ = v___x_1030_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_a_1032_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
else
{
lean_object* v_a_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; size_t v_sz_1039_; size_t v___x_1040_; lean_object* v___x_1041_; 
lean_del_object(v___x_1030_);
v_a_1036_ = lean_ctor_get(v_a_1028_, 0);
lean_inc(v_a_1036_);
lean_dec_ref_known(v_a_1028_, 1);
v___x_1037_ = lean_box(0);
v___x_1038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1037_);
lean_ctor_set(v___x_1038_, 1, v_a_1036_);
v_sz_1039_ = lean_array_size(v_tail_1026_);
v___x_1040_ = ((size_t)0ULL);
v___x_1041_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3(v_tail_1026_, v_sz_1039_, v___x_1040_, v___x_1038_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
if (lean_obj_tag(v___x_1041_) == 0)
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1055_; 
v_a_1042_ = lean_ctor_get(v___x_1041_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1044_ = v___x_1041_;
v_isShared_1045_ = v_isSharedCheck_1055_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_1041_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1055_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v_fst_1046_; 
v_fst_1046_ = lean_ctor_get(v_a_1042_, 0);
if (lean_obj_tag(v_fst_1046_) == 0)
{
lean_object* v_snd_1047_; lean_object* v___x_1049_; 
v_snd_1047_ = lean_ctor_get(v_a_1042_, 1);
lean_inc(v_snd_1047_);
lean_dec(v_a_1042_);
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 0, v_snd_1047_);
v___x_1049_ = v___x_1044_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_snd_1047_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
else
{
lean_object* v_val_1051_; lean_object* v___x_1053_; 
lean_inc_ref(v_fst_1046_);
lean_dec(v_a_1042_);
v_val_1051_ = lean_ctor_get(v_fst_1046_, 0);
lean_inc(v_val_1051_);
lean_dec_ref_known(v_fst_1046_, 1);
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 0, v_val_1051_);
v___x_1053_ = v___x_1044_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_val_1051_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
}
else
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
v_a_1056_ = lean_ctor_get(v___x_1041_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1058_ = v___x_1041_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___x_1041_);
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
}
else
{
lean_object* v_a_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1072_; 
v_a_1065_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1067_ = v___x_1027_;
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_a_1065_);
lean_dec(v___x_1027_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1070_; 
if (v_isShared_1068_ == 0)
{
v___x_1070_ = v___x_1067_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_a_1065_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_1018_ = stack[0].m_obj;
lean_object* v_init_1019_ = stack[1].m_obj;
lean_object* v___y_1020_ = stack[2].m_obj;
lean_object* v___y_1021_ = stack[3].m_obj;
lean_object* v___y_1022_ = stack[4].m_obj;
lean_object* v___y_1023_ = stack[5].m_obj;
lean_object* v_res_1073_;
v_res_1073_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1(v_t_1018_, v_init_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
stack->m_obj
 = v_res_1073_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1___boxed(lean_object* v_t_1074_, lean_object* v_init_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1(v_t_1074_, v_init_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec_ref(v_t_1074_);
return v_res_1081_;
}
}
lean_object* l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1(lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
lean_object* v_lctx_1089_; lean_object* v_decls_1090_; lean_object* v_hs_1091_; lean_object* v___x_1092_; 
v_lctx_1089_ = lean_ctor_get(v___y_1084_, 2);
v_decls_1090_ = lean_ctor_get(v_lctx_1089_, 1);
v_hs_1091_ = ((lean_object*)(l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1___closed__0));
v___x_1092_ = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1(v_decls_1090_, v_hs_1091_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_);
return v___x_1092_;
}
}
LEAN_EXPORT void l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1084_ = stack[0].m_obj;
lean_object* v___y_1085_ = stack[1].m_obj;
lean_object* v___y_1086_ = stack[2].m_obj;
lean_object* v___y_1087_ = stack[3].m_obj;
lean_object* v_res_1093_;
v_res_1093_ = l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1(v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_);
stack->m_obj
 = v_res_1093_;
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1___boxed(lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1(v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
return v_res_1099_;
}
}
lean_object* l_Lean_Meta_Rewrites_localHypotheses(lean_object* v_except_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_){
_start:
{
lean_object* v___x_1108_; 
v___x_1108_ = l_Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1(v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_);
if (lean_obj_tag(v___x_1108_) == 0)
{
lean_object* v_a_1109_; lean_object* v___x_1110_; size_t v_sz_1111_; size_t v___x_1112_; lean_object* v___x_1113_; 
v_a_1109_ = lean_ctor_get(v___x_1108_, 0);
lean_inc(v_a_1109_);
lean_dec_ref_known(v___x_1108_, 1);
v___x_1110_ = ((lean_object*)(l_Lean_Meta_Rewrites_localHypotheses___closed__0));
v_sz_1111_ = lean_array_size(v_a_1109_);
v___x_1112_ = ((size_t)0ULL);
v___x_1113_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_localHypotheses_spec__2(v_except_1102_, v_a_1109_, v_sz_1111_, v___x_1112_, v___x_1110_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_);
lean_dec(v_a_1109_);
return v___x_1113_;
}
else
{
lean_object* v_a_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1121_; 
v_a_1114_ = lean_ctor_get(v___x_1108_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1116_ = v___x_1108_;
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_a_1114_);
lean_dec(v___x_1108_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1119_; 
if (v_isShared_1117_ == 0)
{
v___x_1119_ = v___x_1116_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_a_1114_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Rewrites_localHypotheses_0interp(lean_interpreter_value* stack)
{
lean_object* v_except_1102_ = stack[0].m_obj;
lean_object* v_a_1103_ = stack[1].m_obj;
lean_object* v_a_1104_ = stack[2].m_obj;
lean_object* v_a_1105_ = stack[3].m_obj;
lean_object* v_a_1106_ = stack[4].m_obj;
lean_object* v_res_1122_;
v_res_1122_ = l_Lean_Meta_Rewrites_localHypotheses(v_except_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_);
stack->m_obj
 = v_res_1122_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_localHypotheses___boxed(lean_object* v_except_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_Lean_Meta_Rewrites_localHypotheses(v_except_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_);
lean_dec(v_a_1127_);
lean_dec_ref(v_a_1126_);
lean_dec(v_a_1125_);
lean_dec_ref(v_a_1124_);
lean_dec(v_except_1123_);
return v_res_1129_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7(lean_object* v_as_1130_, size_t v_sz_1131_, size_t v_i_1132_, lean_object* v_b_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_){
_start:
{
lean_object* v___x_1139_; 
v___x_1139_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7___redArg(v_as_1130_, v_sz_1131_, v_i_1132_, v_b_1133_);
return v___x_1139_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1130_ = stack[0].m_obj;
size_t v_sz_1131_ = stack[1].m_num;
size_t v_i_1132_ = stack[2].m_num;
lean_object* v_b_1133_ = stack[3].m_obj;
lean_object* v___y_1134_ = stack[4].m_obj;
lean_object* v___y_1135_ = stack[5].m_obj;
lean_object* v___y_1136_ = stack[6].m_obj;
lean_object* v___y_1137_ = stack[7].m_obj;
lean_object* v_res_1140_;
v_res_1140_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__3_spec__7(v_as_1130_, v_sz_1131_, v_i_1132_, v_b_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_);
stack->m_obj
 = v_res_1140_;
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6(lean_object* v_as_1153_, size_t v_sz_1154_, size_t v_i_1155_, lean_object* v_b_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v___x_1162_; 
v___x_1162_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___redArg(v_as_1153_, v_sz_1154_, v_i_1155_, v_b_1156_);
return v___x_1162_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1153_ = stack[0].m_obj;
size_t v_sz_1154_ = stack[1].m_num;
size_t v_i_1155_ = stack[2].m_num;
lean_object* v_b_1156_ = stack[3].m_obj;
lean_object* v___y_1157_ = stack[4].m_obj;
lean_object* v___y_1158_ = stack[5].m_obj;
lean_object* v___y_1159_ = stack[6].m_obj;
lean_object* v___y_1160_ = stack[7].m_obj;
lean_object* v_res_1163_;
v_res_1163_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6(v_as_1153_, v_sz_1154_, v_i_1155_, v_b_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_);
stack->m_obj
 = v_res_1163_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6___boxed(lean_object* v_as_1164_, lean_object* v_sz_1165_, lean_object* v_i_1166_, lean_object* v_b_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
size_t v_sz_boxed_1173_; size_t v_i_boxed_1174_; lean_object* v_res_1175_; 
v_sz_boxed_1173_ = lean_unbox_usize(v_sz_1165_);
lean_dec(v_sz_1165_);
v_i_boxed_1174_ = lean_unbox_usize(v_i_1166_);
lean_dec(v_i_1166_);
v_res_1175_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__2_spec__5_spec__6(v_as_1164_, v_sz_boxed_1173_, v_i_boxed_1174_, v_b_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
lean_dec_ref(v_as_1164_);
return v_res_1175_;
}
}
lean_object* l_Lean_Meta_Rewrites_createModuleTreeRef(lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_){
_start:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1206_ = ((lean_object*)(l_Lean_Meta_Rewrites_createModuleTreeRef___closed__0));
v___x_1207_ = ((lean_object*)(l_Lean_Meta_Rewrites_droppedKeys));
v___x_1208_ = lean_box(0);
v___x_1209_ = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(v___x_1206_, v___x_1207_, v___x_1208_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_);
return v___x_1209_;
}
}
LEAN_EXPORT void l_Lean_Meta_Rewrites_createModuleTreeRef_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1201_ = stack[0].m_obj;
lean_object* v_a_1202_ = stack[1].m_obj;
lean_object* v_a_1203_ = stack[2].m_obj;
lean_object* v_a_1204_ = stack[3].m_obj;
lean_object* v_res_1210_;
v_res_1210_ = l_Lean_Meta_Rewrites_createModuleTreeRef(v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_);
stack->m_obj
 = v_res_1210_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_createModuleTreeRef___boxed(lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l_Lean_Meta_Rewrites_createModuleTreeRef(v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_);
lean_dec(v_a_1214_);
lean_dec_ref(v_a_1213_);
lean_dec(v_a_1212_);
lean_dec_ref(v_a_1211_);
return v_res_1216_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_1824551397____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1218_ = lean_box(0);
v___x_1219_ = lean_st_mk_ref(v___x_1218_);
v___x_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1219_);
return v___x_1220_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_1824551397____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1221_;
v_res_1221_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_1824551397____hygCtx___hyg_2_();
stack->m_obj
 = v_res_1221_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_1824551397____hygCtx___hyg_2____boxed(lean_object* v_a_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn_00___x40_Lean_Meta_Tactic_Rewrites_1824551397____hygCtx___hyg_2_();
return v_res_1223_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_constantsPerImportTask(void){
_start:
{
lean_object* v___x_1224_; 
v___x_1224_ = lean_unsigned_to_nat(6500u);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_incPrio(lean_object* v_x_1225_, lean_object* v_x_1226_){
_start:
{
lean_object* v_snd_1227_; uint8_t v___x_1228_; 
v_snd_1227_ = lean_ctor_get(v_x_1226_, 1);
v___x_1228_ = lean_unbox(v_snd_1227_);
if (v___x_1228_ == 0)
{
lean_object* v_fst_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1241_; 
v_fst_1229_ = lean_ctor_get(v_x_1226_, 0);
v_isSharedCheck_1241_ = !lean_is_exclusive(v_x_1226_);
if (v_isSharedCheck_1241_ == 0)
{
lean_object* v_unused_1242_; 
v_unused_1242_ = lean_ctor_get(v_x_1226_, 1);
lean_dec(v_unused_1242_);
v___x_1231_ = v_x_1226_;
v_isShared_1232_ = v_isSharedCheck_1241_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_fst_1229_);
lean_dec(v_x_1226_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1241_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
uint8_t v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1238_; 
v___x_1233_ = 0;
v___x_1234_ = lean_unsigned_to_nat(2u);
v___x_1235_ = lean_nat_mul(v___x_1234_, v_x_1225_);
lean_dec(v_x_1225_);
v___x_1236_ = lean_box(v___x_1233_);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 1, v___x_1235_);
lean_ctor_set(v___x_1231_, 0, v___x_1236_);
v___x_1238_ = v___x_1231_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v___x_1236_);
lean_ctor_set(v_reuseFailAlloc_1240_, 1, v___x_1235_);
v___x_1238_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
lean_object* v___x_1239_; 
v___x_1239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1239_, 0, v_fst_1229_);
lean_ctor_set(v___x_1239_, 1, v___x_1238_);
return v___x_1239_;
}
}
}
else
{
lean_object* v_fst_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1253_; 
v_fst_1243_ = lean_ctor_get(v_x_1226_, 0);
v_isSharedCheck_1253_ = !lean_is_exclusive(v_x_1226_);
if (v_isSharedCheck_1253_ == 0)
{
lean_object* v_unused_1254_; 
v_unused_1254_ = lean_ctor_get(v_x_1226_, 1);
lean_dec(v_unused_1254_);
v___x_1245_ = v_x_1226_;
v_isShared_1246_ = v_isSharedCheck_1253_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_fst_1243_);
lean_dec(v_x_1226_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1253_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
uint8_t v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1250_; 
v___x_1247_ = 1;
v___x_1248_ = lean_box(v___x_1247_);
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 1, v_x_1225_);
lean_ctor_set(v___x_1245_, 0, v___x_1248_);
v___x_1250_ = v___x_1245_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v___x_1248_);
lean_ctor_set(v_reuseFailAlloc_1252_, 1, v_x_1225_);
v___x_1250_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
lean_object* v___x_1251_; 
v___x_1251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1251_, 0, v_fst_1243_);
lean_ctor_set(v___x_1251_, 1, v___x_1250_);
return v___x_1251_;
}
}
}
}
}
lean_object* l_Lean_Meta_Rewrites_rwFindDecls(lean_object* v_moduleRef_1256_, lean_object* v_ty_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_){
_start:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1263_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_ext;
v___x_1264_ = ((lean_object*)(l_Lean_Meta_Rewrites_createModuleTreeRef___closed__0));
v___x_1265_ = ((lean_object*)(l_Lean_Meta_Rewrites_droppedKeys));
v___x_1266_ = lean_unsigned_to_nat(6500u);
v___x_1267_ = lean_box(0);
v___x_1268_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwFindDecls___closed__0));
v___x_1269_ = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(v_moduleRef_1256_, v___x_1263_, v___x_1264_, v___x_1265_, v___x_1266_, v___x_1267_, v___x_1268_, v_ty_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_);
return v___x_1269_;
}
}
LEAN_EXPORT void l_Lean_Meta_Rewrites_rwFindDecls_0interp(lean_interpreter_value* stack)
{
lean_object* v_moduleRef_1256_ = stack[0].m_obj;
lean_object* v_ty_1257_ = stack[1].m_obj;
lean_object* v_a_1258_ = stack[2].m_obj;
lean_object* v_a_1259_ = stack[3].m_obj;
lean_object* v_a_1260_ = stack[4].m_obj;
lean_object* v_a_1261_ = stack[5].m_obj;
lean_object* v_res_1270_;
v_res_1270_ = l_Lean_Meta_Rewrites_rwFindDecls(v_moduleRef_1256_, v_ty_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_);
stack->m_obj
 = v_res_1270_;
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
lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg(lean_object* v_mctx_1279_, lean_object* v_x_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
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
LEAN_EXPORT void l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mctx_1279_ = stack[0].m_obj;
lean_object* v_x_1280_ = stack[1].m_obj;
lean_object* v___y_1281_ = stack[2].m_obj;
lean_object* v___y_1282_ = stack[3].m_obj;
lean_object* v___y_1283_ = stack[4].m_obj;
lean_object* v___y_1284_ = stack[5].m_obj;
lean_object* v_res_1303_;
v_res_1303_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg(v_mctx_1279_, v_x_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_);
stack->m_obj
 = v_res_1303_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg___boxed(lean_object* v_mctx_1304_, lean_object* v_x_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg(v_mctx_1304_, v_x_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
return v_res_1311_;
}
}
lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0(lean_object* v_00_u03b1_1312_, lean_object* v_mctx_1313_, lean_object* v_x_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_){
_start:
{
lean_object* v___x_1320_; 
v___x_1320_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg(v_mctx_1313_, v_x_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_);
return v___x_1320_;
}
}
LEAN_EXPORT void l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mctx_1313_ = stack[1].m_obj;
lean_object* v_x_1314_ = stack[2].m_obj;
lean_object* v___y_1315_ = stack[3].m_obj;
lean_object* v___y_1316_ = stack[4].m_obj;
lean_object* v___y_1317_ = stack[5].m_obj;
lean_object* v___y_1318_ = stack[6].m_obj;
lean_object* v_res_1321_;
v_res_1321_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0(lean_box(0), v_mctx_1313_, v_x_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_);
stack->m_obj
 = v_res_1321_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___boxed(lean_object* v_00_u03b1_1322_, lean_object* v_mctx_1323_, lean_object* v_x_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0(v_00_u03b1_1322_, v_mctx_1323_, v_x_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
return v_res_1330_;
}
}
lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(lean_object* v_x_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_){
_start:
{
lean_object* v___x_1337_; 
v___x_1337_ = l_Lean_Meta_saveState___redArg(v___y_1333_, v___y_1335_);
if (lean_obj_tag(v___x_1337_) == 0)
{
lean_object* v_a_1338_; lean_object* v_r_1339_; 
v_a_1338_ = lean_ctor_get(v___x_1337_, 0);
lean_inc(v_a_1338_);
lean_dec_ref_known(v___x_1337_, 1);
lean_inc(v___y_1335_);
lean_inc_ref(v___y_1334_);
lean_inc(v___y_1333_);
lean_inc_ref(v___y_1332_);
v_r_1339_ = lean_apply_5(v_x_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, lean_box(0));
if (lean_obj_tag(v_r_1339_) == 0)
{
lean_object* v_a_1340_; lean_object* v___x_1341_; 
v_a_1340_ = lean_ctor_get(v_r_1339_, 0);
lean_inc(v_a_1340_);
lean_dec_ref_known(v_r_1339_, 1);
v___x_1341_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1338_, v___y_1333_, v___y_1335_);
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1348_; 
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1348_ == 0)
{
lean_object* v_unused_1349_; 
v_unused_1349_ = lean_ctor_get(v___x_1341_, 0);
lean_dec(v_unused_1349_);
v___x_1343_ = v___x_1341_;
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
else
{
lean_dec(v___x_1341_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1346_; 
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 0, v_a_1340_);
v___x_1346_ = v___x_1343_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_a_1340_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
}
else
{
lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1357_; 
lean_dec(v_a_1340_);
v_a_1350_ = lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1352_ = v___x_1341_;
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_a_1350_);
lean_dec(v___x_1341_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1355_; 
if (v_isShared_1353_ == 0)
{
v___x_1355_ = v___x_1352_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_a_1350_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
}
}
else
{
lean_object* v_a_1358_; lean_object* v___x_1359_; 
v_a_1358_ = lean_ctor_get(v_r_1339_, 0);
lean_inc(v_a_1358_);
lean_dec_ref_known(v_r_1339_, 1);
v___x_1359_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1338_, v___y_1333_, v___y_1335_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1366_; 
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1366_ == 0)
{
lean_object* v_unused_1367_; 
v_unused_1367_ = lean_ctor_get(v___x_1359_, 0);
lean_dec(v_unused_1367_);
v___x_1361_ = v___x_1359_;
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
else
{
lean_dec(v___x_1359_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1364_; 
if (v_isShared_1362_ == 0)
{
lean_ctor_set_tag(v___x_1361_, 1);
lean_ctor_set(v___x_1361_, 0, v_a_1358_);
v___x_1364_ = v___x_1361_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_a_1358_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
}
else
{
lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1375_; 
lean_dec(v_a_1358_);
v_a_1368_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1370_ = v___x_1359_;
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1359_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1373_; 
if (v_isShared_1371_ == 0)
{
v___x_1373_ = v___x_1370_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_a_1368_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
}
}
else
{
lean_object* v_a_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1383_; 
lean_dec_ref(v_x_1331_);
v_a_1376_ = lean_ctor_get(v___x_1337_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1378_ = v___x_1337_;
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_a_1376_);
lean_dec(v___x_1337_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v___x_1381_; 
if (v_isShared_1379_ == 0)
{
v___x_1381_ = v___x_1378_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v_a_1376_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1331_ = stack[0].m_obj;
lean_object* v___y_1332_ = stack[1].m_obj;
lean_object* v___y_1333_ = stack[2].m_obj;
lean_object* v___y_1334_ = stack[3].m_obj;
lean_object* v___y_1335_ = stack[4].m_obj;
lean_object* v_res_1384_;
v_res_1384_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v_x_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
stack->m_obj
 = v_res_1384_;
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg___boxed(lean_object* v_x_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v_x_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec(v___y_1387_);
lean_dec_ref(v___y_1386_);
return v_res_1391_;
}
}
lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1(lean_object* v_00_u03b1_1392_, lean_object* v_x_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
lean_object* v___x_1399_; 
v___x_1399_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v_x_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_);
return v___x_1399_;
}
}
LEAN_EXPORT void l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1393_ = stack[1].m_obj;
lean_object* v___y_1394_ = stack[2].m_obj;
lean_object* v___y_1395_ = stack[3].m_obj;
lean_object* v___y_1396_ = stack[4].m_obj;
lean_object* v___y_1397_ = stack[5].m_obj;
lean_object* v_res_1400_;
v_res_1400_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1(lean_box(0), v_x_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_);
stack->m_obj
 = v_res_1400_;
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___boxed(lean_object* v_00_u03b1_1401_, lean_object* v_x_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1(v_00_u03b1_1401_, v_x_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
lean_dec(v___y_1404_);
lean_dec_ref(v___y_1403_);
return v_res_1408_;
}
}
lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0(lean_object* v___x_1409_, uint8_t v___x_1410_, lean_object* v___x_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
lean_object* v___x_1417_; 
v___x_1417_ = l_Lean_Meta_mkFreshExprMVar(v___x_1409_, v___x_1410_, v___x_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
if (lean_obj_tag(v___x_1417_) == 0)
{
lean_object* v_a_1418_; lean_object* v___x_1419_; uint8_t v_transparency_1420_; lean_object* v___x_1421_; uint8_t v___x_1422_; lean_object* v___y_1424_; uint8_t v___x_1442_; uint8_t v___x_1443_; 
v_a_1418_ = lean_ctor_get(v___x_1417_, 0);
lean_inc(v_a_1418_);
lean_dec_ref_known(v___x_1417_, 1);
v___x_1419_ = l_Lean_Meta_Context_config(v___y_1412_);
v_transparency_1420_ = lean_ctor_get_uint8(v___x_1419_, 9);
lean_dec_ref(v___x_1419_);
v___x_1421_ = l_Lean_Expr_mvarId_x21(v_a_1418_);
lean_dec(v_a_1418_);
v___x_1422_ = 1;
v___x_1442_ = 2;
v___x_1443_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_1420_, v___x_1442_);
if (v___x_1443_ == 0)
{
lean_object* v_keyedConfig_1444_; uint8_t v_trackZetaDelta_1445_; lean_object* v_zetaDeltaSet_1446_; lean_object* v_lctx_1447_; lean_object* v_localInstances_1448_; lean_object* v_defEqCtx_x3f_1449_; lean_object* v_synthPendingDepth_1450_; lean_object* v_customCanUnfoldPredicate_x3f_1451_; uint8_t v_univApprox_1452_; uint8_t v_inTypeClassResolution_1453_; uint8_t v_cacheInferType_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1463_; 
v_keyedConfig_1444_ = lean_ctor_get(v___y_1412_, 0);
v_trackZetaDelta_1445_ = lean_ctor_get_uint8(v___y_1412_, sizeof(void*)*7);
v_zetaDeltaSet_1446_ = lean_ctor_get(v___y_1412_, 1);
v_lctx_1447_ = lean_ctor_get(v___y_1412_, 2);
v_localInstances_1448_ = lean_ctor_get(v___y_1412_, 3);
v_defEqCtx_x3f_1449_ = lean_ctor_get(v___y_1412_, 4);
v_synthPendingDepth_1450_ = lean_ctor_get(v___y_1412_, 5);
v_customCanUnfoldPredicate_x3f_1451_ = lean_ctor_get(v___y_1412_, 6);
v_univApprox_1452_ = lean_ctor_get_uint8(v___y_1412_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1453_ = lean_ctor_get_uint8(v___y_1412_, sizeof(void*)*7 + 2);
v_cacheInferType_1454_ = lean_ctor_get_uint8(v___y_1412_, sizeof(void*)*7 + 3);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___y_1412_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1456_ = v___y_1412_;
v_isShared_1457_ = v_isSharedCheck_1463_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_1451_);
lean_inc(v_synthPendingDepth_1450_);
lean_inc(v_defEqCtx_x3f_1449_);
lean_inc(v_localInstances_1448_);
lean_inc(v_lctx_1447_);
lean_inc(v_zetaDeltaSet_1446_);
lean_inc(v_keyedConfig_1444_);
lean_dec(v___y_1412_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1463_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1458_; lean_object* v___x_1460_; 
v___x_1458_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1442_, v_keyedConfig_1444_);
if (v_isShared_1457_ == 0)
{
lean_ctor_set(v___x_1456_, 0, v___x_1458_);
v___x_1460_ = v___x_1456_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v___x_1458_);
lean_ctor_set(v_reuseFailAlloc_1462_, 1, v_zetaDeltaSet_1446_);
lean_ctor_set(v_reuseFailAlloc_1462_, 2, v_lctx_1447_);
lean_ctor_set(v_reuseFailAlloc_1462_, 3, v_localInstances_1448_);
lean_ctor_set(v_reuseFailAlloc_1462_, 4, v_defEqCtx_x3f_1449_);
lean_ctor_set(v_reuseFailAlloc_1462_, 5, v_synthPendingDepth_1450_);
lean_ctor_set(v_reuseFailAlloc_1462_, 6, v_customCanUnfoldPredicate_x3f_1451_);
lean_ctor_set_uint8(v_reuseFailAlloc_1462_, sizeof(void*)*7, v_trackZetaDelta_1445_);
lean_ctor_set_uint8(v_reuseFailAlloc_1462_, sizeof(void*)*7 + 1, v_univApprox_1452_);
lean_ctor_set_uint8(v_reuseFailAlloc_1462_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1453_);
lean_ctor_set_uint8(v_reuseFailAlloc_1462_, sizeof(void*)*7 + 3, v_cacheInferType_1454_);
v___x_1460_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
lean_object* v___x_1461_; 
v___x_1461_ = l_Lean_MVarId_refl(v___x_1421_, v___x_1422_, v___x_1460_, v___y_1413_, v___y_1414_, v___y_1415_);
lean_dec_ref(v___x_1460_);
v___y_1424_ = v___x_1461_;
goto v___jp_1423_;
}
}
}
else
{
lean_object* v___x_1464_; 
v___x_1464_ = l_Lean_MVarId_refl(v___x_1421_, v___x_1422_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
lean_dec_ref(v___y_1412_);
v___y_1424_ = v___x_1464_;
goto v___jp_1423_;
}
v___jp_1423_:
{
if (lean_obj_tag(v___y_1424_) == 0)
{
lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1432_; 
v_isSharedCheck_1432_ = !lean_is_exclusive(v___y_1424_);
if (v_isSharedCheck_1432_ == 0)
{
lean_object* v_unused_1433_; 
v_unused_1433_ = lean_ctor_get(v___y_1424_, 0);
lean_dec(v_unused_1433_);
v___x_1426_ = v___y_1424_;
v_isShared_1427_ = v_isSharedCheck_1432_;
goto v_resetjp_1425_;
}
else
{
lean_dec(v___y_1424_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1432_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v___x_1428_; lean_object* v___x_1430_; 
v___x_1428_ = lean_box(v___x_1422_);
if (v_isShared_1427_ == 0)
{
lean_ctor_set(v___x_1426_, 0, v___x_1428_);
v___x_1430_ = v___x_1426_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v___x_1428_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
else
{
lean_object* v_a_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1441_; 
v_a_1434_ = lean_ctor_get(v___y_1424_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v___y_1424_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1436_ = v___y_1424_;
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_a_1434_);
lean_dec(v___y_1424_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1439_; 
if (v_isShared_1437_ == 0)
{
v___x_1439_ = v___x_1436_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_a_1434_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
}
}
}
else
{
lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1472_; 
lean_dec_ref(v___y_1412_);
v_a_1465_ = lean_ctor_get(v___x_1417_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1467_ = v___x_1417_;
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v___x_1417_);
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
LEAN_EXPORT void l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1409_ = stack[0].m_obj;
uint8_t v___x_1410_ = stack[1].m_num;
lean_object* v___x_1411_ = stack[2].m_obj;
lean_object* v___y_1412_ = stack[3].m_obj;
lean_object* v___y_1413_ = stack[4].m_obj;
lean_object* v___y_1414_ = stack[5].m_obj;
lean_object* v___y_1415_ = stack[6].m_obj;
lean_object* v_res_1473_;
v_res_1473_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0(v___x_1409_, v___x_1410_, v___x_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
stack->m_obj
 = v_res_1473_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___boxed(lean_object* v___x_1474_, lean_object* v___x_1475_, lean_object* v___x_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_){
_start:
{
uint8_t v___x_2366__boxed_1482_; lean_object* v_res_1483_; 
v___x_2366__boxed_1482_ = lean_unbox(v___x_1475_);
v_res_1483_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0(v___x_1474_, v___x_2366__boxed_1482_, v___x_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
lean_dec(v___y_1478_);
return v_res_1483_;
}
}
lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(lean_object* v_mctx_1484_, lean_object* v_e_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_){
_start:
{
lean_object* v___x_1491_; uint8_t v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___f_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1491_, 0, v_e_1485_);
v___x_1492_ = 0;
v___x_1493_ = lean_box(0);
v___x_1494_ = lean_box(v___x_1492_);
v___f_1495_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1495_, 0, v___x_1491_);
lean_closure_set(v___f_1495_, 1, v___x_1494_);
lean_closure_set(v___f_1495_, 2, v___x_1493_);
v___x_1496_ = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___boxed), 8, 3);
lean_closure_set(v___x_1496_, 0, lean_box(0));
lean_closure_set(v___x_1496_, 1, v_mctx_1484_);
lean_closure_set(v___x_1496_, 2, v___f_1495_);
v___x_1497_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v___x_1496_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_);
if (lean_obj_tag(v___x_1497_) == 0)
{
return v___x_1497_;
}
else
{
lean_object* v_a_1498_; uint8_t v___y_1500_; uint8_t v___x_1510_; 
v_a_1498_ = lean_ctor_get(v___x_1497_, 0);
v___x_1510_ = l_Lean_Exception_isInterrupt(v_a_1498_);
if (v___x_1510_ == 0)
{
uint8_t v___x_1511_; 
lean_inc(v_a_1498_);
v___x_1511_ = l_Lean_Exception_isRuntime(v_a_1498_);
v___y_1500_ = v___x_1511_;
goto v___jp_1499_;
}
else
{
v___y_1500_ = v___x_1510_;
goto v___jp_1499_;
}
v___jp_1499_:
{
if (v___y_1500_ == 0)
{
lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1508_; 
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1508_ == 0)
{
lean_object* v_unused_1509_; 
v_unused_1509_ = lean_ctor_get(v___x_1497_, 0);
lean_dec(v_unused_1509_);
v___x_1502_ = v___x_1497_;
v_isShared_1503_ = v_isSharedCheck_1508_;
goto v_resetjp_1501_;
}
else
{
lean_dec(v___x_1497_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1508_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1504_; lean_object* v___x_1506_; 
v___x_1504_ = lean_box(v___y_1500_);
if (v_isShared_1503_ == 0)
{
lean_ctor_set_tag(v___x_1502_, 0);
lean_ctor_set(v___x_1502_, 0, v___x_1504_);
v___x_1506_ = v___x_1502_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v___x_1504_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
else
{
return v___x_1497_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Rewrites_dischargableWithRfl_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_mctx_1484_ = stack[0].m_obj;
lean_object* v_e_1485_ = stack[1].m_obj;
lean_object* v_a_1486_ = stack[2].m_obj;
lean_object* v_a_1487_ = stack[3].m_obj;
lean_object* v_a_1488_ = stack[4].m_obj;
lean_object* v_a_1489_ = stack[5].m_obj;
lean_object* v_res_1512_;
v_res_1512_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(v_mctx_1484_, v_e_1485_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_);
stack->m_obj
 = v_res_1512_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___boxed(lean_object* v_mctx_1513_, lean_object* v_e_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_){
_start:
{
lean_object* v_res_1520_; 
v_res_1520_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(v_mctx_1513_, v_e_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_);
lean_dec(v_a_1518_);
lean_dec_ref(v_a_1517_);
lean_dec(v_a_1516_);
lean_dec_ref(v_a_1515_);
return v_res_1520_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult(lean_object* v_r_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_){
_start:
{
lean_object* v_result_1527_; lean_object* v_eNew_1528_; lean_object* v___x_1529_; 
v_result_1527_ = lean_ctor_get(v_r_1521_, 2);
lean_inc_ref(v_result_1527_);
lean_dec_ref(v_r_1521_);
v_eNew_1528_ = lean_ctor_get(v_result_1527_, 0);
lean_inc_ref(v_eNew_1528_);
lean_dec_ref(v_result_1527_);
v___x_1529_ = l_Lean_Meta_ppExpr(v_eNew_1528_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v_a_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1540_; 
v_a_1530_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1540_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1532_ = v___x_1529_;
v_isShared_1533_ = v_isSharedCheck_1540_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_a_1530_);
lean_dec(v___x_1529_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1540_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1538_; 
v___x_1534_ = l_Std_Format_defWidth;
v___x_1535_ = lean_unsigned_to_nat(0u);
v___x_1536_ = l_Std_Format_pretty(v_a_1530_, v___x_1534_, v___x_1535_, v___x_1535_);
if (v_isShared_1533_ == 0)
{
lean_ctor_set(v___x_1532_, 0, v___x_1536_);
v___x_1538_ = v___x_1532_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v___x_1536_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
return v___x_1538_;
}
}
}
else
{
lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1548_; 
v_a_1541_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1543_ = v___x_1529_;
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_a_1541_);
lean_dec(v___x_1529_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1546_; 
if (v_isShared_1544_ == 0)
{
v___x_1546_ = v___x_1543_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_a_1541_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult_0interp(lean_interpreter_value* stack)
{
lean_object* v_r_1521_ = stack[0].m_obj;
lean_object* v_a_1522_ = stack[1].m_obj;
lean_object* v_a_1523_ = stack[2].m_obj;
lean_object* v_a_1524_ = stack[3].m_obj;
lean_object* v_a_1525_ = stack[4].m_obj;
lean_object* v_res_1549_;
v_res_1549_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult(v_r_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_);
stack->m_obj
 = v_res_1549_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult___boxed(lean_object* v_r_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult(v_r_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_);
lean_dec(v_a_1554_);
lean_dec_ref(v_a_1553_);
lean_dec(v_a_1552_);
lean_dec_ref(v_a_1551_);
return v_res_1556_;
}
}
lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorIdx___impl(uint8_t v_x_1557_){
_start:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1558_ = lean_box(v_x_1557_);
v___x_1559_ = lean_obj_tag_nat(v___x_1558_);
lean_dec(v___x_1558_);
return v___x_1559_;
}
}
LEAN_EXPORT void l_Lean_Meta_Rewrites_SideConditions_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1557_ = stack[0].m_num;
lean_object* v_res_1560_;
v_res_1560_ = l_Lean_Meta_Rewrites_SideConditions_ctorIdx___impl(v_x_1557_);
stack->m_obj
 = v_res_1560_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorIdx___impl___boxed(lean_object* v_x_1561_){
_start:
{
uint8_t v_x_4__boxed_1562_; lean_object* v_res_1563_; 
v_x_4__boxed_1562_ = lean_unbox(v_x_1561_);
v_res_1563_ = l_Lean_Meta_Rewrites_SideConditions_ctorIdx___impl(v_x_4__boxed_1562_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorElim___redArg(lean_object* v_k_1564_){
_start:
{
lean_inc(v_k_1564_);
return v_k_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorElim___redArg___boxed(lean_object* v_k_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l_Lean_Meta_Rewrites_SideConditions_ctorElim___redArg(v_k_1565_);
lean_dec(v_k_1565_);
return v_res_1566_;
}
}
lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorElim(lean_object* v_motive_1567_, lean_object* v_ctorIdx_1568_, uint8_t v_t_1569_, lean_object* v_h_1570_, lean_object* v_k_1571_){
_start:
{
lean_inc(v_k_1571_);
return v_k_1571_;
}
}
LEAN_EXPORT void l_Lean_Meta_Rewrites_SideConditions_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_1568_ = stack[1].m_obj;
uint8_t v_t_1569_ = stack[2].m_num;
lean_object* v_k_1571_ = stack[4].m_obj;
lean_object* v_res_1572_;
v_res_1572_ = l_Lean_Meta_Rewrites_SideConditions_ctorElim(lean_box(0), v_ctorIdx_1568_, v_t_1569_, lean_box(0), v_k_1571_);
stack->m_obj
 = v_res_1572_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorElim___boxed(lean_object* v_motive_1573_, lean_object* v_ctorIdx_1574_, lean_object* v_t_1575_, lean_object* v_h_1576_, lean_object* v_k_1577_){
_start:
{
uint8_t v_t_boxed_1578_; lean_object* v_res_1579_; 
v_t_boxed_1578_ = lean_unbox(v_t_1575_);
v_res_1579_ = l_Lean_Meta_Rewrites_SideConditions_ctorElim(v_motive_1573_, v_ctorIdx_1574_, v_t_boxed_1578_, v_h_1576_, v_k_1577_);
lean_dec(v_k_1577_);
lean_dec(v_ctorIdx_1574_);
return v_res_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_none_elim___redArg(lean_object* v_none_1580_){
_start:
{
lean_inc(v_none_1580_);
return v_none_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_none_elim___redArg___boxed(lean_object* v_none_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l_Lean_Meta_Rewrites_SideConditions_none_elim___redArg(v_none_1581_);
lean_dec(v_none_1581_);
return v_res_1582_;
}
}
lean_object* l_Lean_Meta_Rewrites_SideConditions_none_elim(lean_object* v_motive_1583_, uint8_t v_t_1584_, lean_object* v_h_1585_, lean_object* v_none_1586_){
_start:
{
lean_inc(v_none_1586_);
return v_none_1586_;
}
}
LEAN_EXPORT void l_Lean_Meta_Rewrites_SideConditions_none_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_1584_ = stack[1].m_num;
lean_object* v_none_1586_ = stack[3].m_obj;
lean_object* v_res_1587_;
v_res_1587_ = l_Lean_Meta_Rewrites_SideConditions_none_elim(lean_box(0), v_t_1584_, lean_box(0), v_none_1586_);
stack->m_obj
 = v_res_1587_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_none_elim___boxed(lean_object* v_motive_1588_, lean_object* v_t_1589_, lean_object* v_h_1590_, lean_object* v_none_1591_){
_start:
{
uint8_t v_t_boxed_1592_; lean_object* v_res_1593_; 
v_t_boxed_1592_ = lean_unbox(v_t_1589_);
v_res_1593_ = l_Lean_Meta_Rewrites_SideConditions_none_elim(v_motive_1588_, v_t_boxed_1592_, v_h_1590_, v_none_1591_);
lean_dec(v_none_1591_);
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_assumption_elim___redArg(lean_object* v_assumption_1594_){
_start:
{
lean_inc(v_assumption_1594_);
return v_assumption_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_assumption_elim___redArg___boxed(lean_object* v_assumption_1595_){
_start:
{
lean_object* v_res_1596_; 
v_res_1596_ = l_Lean_Meta_Rewrites_SideConditions_assumption_elim___redArg(v_assumption_1595_);
lean_dec(v_assumption_1595_);
return v_res_1596_;
}
}
lean_object* l_Lean_Meta_Rewrites_SideConditions_assumption_elim(lean_object* v_motive_1597_, uint8_t v_t_1598_, lean_object* v_h_1599_, lean_object* v_assumption_1600_){
_start:
{
lean_inc(v_assumption_1600_);
return v_assumption_1600_;
}
}
LEAN_EXPORT void l_Lean_Meta_Rewrites_SideConditions_assumption_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_1598_ = stack[1].m_num;
lean_object* v_assumption_1600_ = stack[3].m_obj;
lean_object* v_res_1601_;
v_res_1601_ = l_Lean_Meta_Rewrites_SideConditions_assumption_elim(lean_box(0), v_t_1598_, lean_box(0), v_assumption_1600_);
stack->m_obj
 = v_res_1601_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_assumption_elim___boxed(lean_object* v_motive_1602_, lean_object* v_t_1603_, lean_object* v_h_1604_, lean_object* v_assumption_1605_){
_start:
{
uint8_t v_t_boxed_1606_; lean_object* v_res_1607_; 
v_t_boxed_1606_ = lean_unbox(v_t_1603_);
v_res_1607_ = l_Lean_Meta_Rewrites_SideConditions_assumption_elim(v_motive_1602_, v_t_boxed_1606_, v_h_1604_, v_assumption_1605_);
lean_dec(v_assumption_1605_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim___redArg(lean_object* v_solveByElim_1608_){
_start:
{
lean_inc(v_solveByElim_1608_);
return v_solveByElim_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim___redArg___boxed(lean_object* v_solveByElim_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim___redArg(v_solveByElim_1609_);
lean_dec(v_solveByElim_1609_);
return v_res_1610_;
}
}
lean_object* l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim(lean_object* v_motive_1611_, uint8_t v_t_1612_, lean_object* v_h_1613_, lean_object* v_solveByElim_1614_){
_start:
{
lean_inc(v_solveByElim_1614_);
return v_solveByElim_1614_;
}
}
LEAN_EXPORT void l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_1612_ = stack[1].m_num;
lean_object* v_solveByElim_1614_ = stack[3].m_obj;
lean_object* v_res_1615_;
v_res_1615_ = l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim(lean_box(0), v_t_1612_, lean_box(0), v_solveByElim_1614_);
stack->m_obj
 = v_res_1615_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim___boxed(lean_object* v_motive_1616_, lean_object* v_t_1617_, lean_object* v_h_1618_, lean_object* v_solveByElim_1619_){
_start:
{
uint8_t v_t_boxed_1620_; lean_object* v_res_1621_; 
v_t_boxed_1620_ = lean_unbox(v_t_1617_);
v_res_1621_ = l_Lean_Meta_Rewrites_SideConditions_solveByElim_elim(v_motive_1616_, v_t_boxed_1620_, v_h_1618_, v_solveByElim_1619_);
lean_dec(v_solveByElim_1619_);
return v_res_1621_;
}
}
lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__0(lean_object* v_x_1622_, lean_object* v_x_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_){
_start:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1629_ = lean_box(0);
v___x_1630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1629_);
return v___x_1630_;
}
}
LEAN_EXPORT void l_Lean_Meta_Rewrites_solveByElim___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1622_ = stack[0].m_obj;
lean_object* v_x_1623_ = stack[1].m_obj;
lean_object* v___y_1624_ = stack[2].m_obj;
lean_object* v___y_1625_ = stack[3].m_obj;
lean_object* v___y_1626_ = stack[4].m_obj;
lean_object* v___y_1627_ = stack[5].m_obj;
lean_object* v_res_1631_;
v_res_1631_ = l_Lean_Meta_Rewrites_solveByElim___lam__0(v_x_1622_, v_x_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_);
stack->m_obj
 = v_res_1631_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__0___boxed(lean_object* v_x_1632_, lean_object* v_x_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_){
_start:
{
lean_object* v_res_1639_; 
v_res_1639_ = l_Lean_Meta_Rewrites_solveByElim___lam__0(v_x_1632_, v_x_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_);
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1636_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
lean_dec(v_x_1633_);
lean_dec(v_x_1632_);
return v_res_1639_;
}
}
lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__1(lean_object* v_x_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_){
_start:
{
uint8_t v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1646_ = 0;
v___x_1647_ = lean_box(v___x_1646_);
v___x_1648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1647_);
return v___x_1648_;
}
}
LEAN_EXPORT void l_Lean_Meta_Rewrites_solveByElim___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1640_ = stack[0].m_obj;
lean_object* v___y_1641_ = stack[1].m_obj;
lean_object* v___y_1642_ = stack[2].m_obj;
lean_object* v___y_1643_ = stack[3].m_obj;
lean_object* v___y_1644_ = stack[4].m_obj;
lean_object* v_res_1649_;
v_res_1649_ = l_Lean_Meta_Rewrites_solveByElim___lam__1(v_x_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_);
stack->m_obj
 = v_res_1649_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__1___boxed(lean_object* v_x_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_){
_start:
{
lean_object* v_res_1656_; 
v_res_1656_ = l_Lean_Meta_Rewrites_solveByElim___lam__1(v_x_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
lean_dec(v_x_1650_);
return v_res_1656_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0(lean_object* v_msgData_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
lean_object* v___x_1663_; lean_object* v_env_1664_; uint8_t v___x_1665_; lean_object* v_env_1666_; lean_object* v___x_1667_; lean_object* v_toCold_1668_; lean_object* v_mctx_1669_; lean_object* v_lctx_1670_; lean_object* v_options_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1663_ = lean_st_ref_get(v___y_1661_);
v_env_1664_ = lean_ctor_get(v___x_1663_, 0);
lean_inc_ref(v_env_1664_);
lean_dec(v___x_1663_);
v___x_1665_ = 0;
v_env_1666_ = l_Lean_Environment_setRecordingDeps(v_env_1664_, v___x_1665_);
v___x_1667_ = lean_st_ref_get(v___y_1659_);
v_toCold_1668_ = lean_ctor_get(v___y_1660_, 0);
v_mctx_1669_ = lean_ctor_get(v___x_1667_, 0);
lean_inc_ref(v_mctx_1669_);
lean_dec(v___x_1667_);
v_lctx_1670_ = lean_ctor_get(v___y_1658_, 2);
v_options_1671_ = lean_ctor_get(v_toCold_1668_, 2);
lean_inc_ref(v_options_1671_);
lean_inc_ref(v_lctx_1670_);
v___x_1672_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1672_, 0, v_env_1666_);
lean_ctor_set(v___x_1672_, 1, v_mctx_1669_);
lean_ctor_set(v___x_1672_, 2, v_lctx_1670_);
lean_ctor_set(v___x_1672_, 3, v_options_1671_);
v___x_1673_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1672_);
lean_ctor_set(v___x_1673_, 1, v_msgData_1657_);
v___x_1674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1673_);
return v___x_1674_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1657_ = stack[0].m_obj;
lean_object* v___y_1658_ = stack[1].m_obj;
lean_object* v___y_1659_ = stack[2].m_obj;
lean_object* v___y_1660_ = stack[3].m_obj;
lean_object* v___y_1661_ = stack[4].m_obj;
lean_object* v_res_1675_;
v_res_1675_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0(v_msgData_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
stack->m_obj
 = v_res_1675_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0___boxed(lean_object* v_msgData_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0(v_msgData_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
return v_res_1682_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(lean_object* v_msg_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_){
_start:
{
lean_object* v_ref_1689_; lean_object* v___x_1690_; lean_object* v_a_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1699_; 
v_ref_1689_ = lean_ctor_get(v___y_1686_, 2);
v___x_1690_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0(v_msg_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
v_a_1691_ = lean_ctor_get(v___x_1690_, 0);
v_isSharedCheck_1699_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1693_ = v___x_1690_;
v_isShared_1694_ = v_isSharedCheck_1699_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_a_1691_);
lean_dec(v___x_1690_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1699_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v___x_1695_; lean_object* v___x_1697_; 
lean_inc(v_ref_1689_);
v___x_1695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1695_, 0, v_ref_1689_);
lean_ctor_set(v___x_1695_, 1, v_a_1691_);
if (v_isShared_1694_ == 0)
{
lean_ctor_set_tag(v___x_1693_, 1);
lean_ctor_set(v___x_1693_, 0, v___x_1695_);
v___x_1697_ = v___x_1693_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v___x_1695_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1683_ = stack[0].m_obj;
lean_object* v___y_1684_ = stack[1].m_obj;
lean_object* v___y_1685_ = stack[2].m_obj;
lean_object* v___y_1686_ = stack[3].m_obj;
lean_object* v___y_1687_ = stack[4].m_obj;
lean_object* v_res_1700_;
v_res_1700_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(v_msg_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
stack->m_obj
 = v_res_1700_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg___boxed(lean_object* v_msg_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(v_msg_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
return v_res_1707_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1709_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__0));
v___x_1710_ = l_Lean_stringToMessageData(v___x_1709_);
return v___x_1710_;
}
}
lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__2(lean_object* v_x_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_){
_start:
{
lean_object* v___x_1717_; lean_object* v___x_1718_; 
v___x_1717_ = lean_obj_once(&l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1, &l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1_once, _init_l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1);
v___x_1718_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(v___x_1717_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_);
return v___x_1718_;
}
}
LEAN_EXPORT void l_Lean_Meta_Rewrites_solveByElim___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1711_ = stack[0].m_obj;
lean_object* v___y_1712_ = stack[1].m_obj;
lean_object* v___y_1713_ = stack[2].m_obj;
lean_object* v___y_1714_ = stack[3].m_obj;
lean_object* v___y_1715_ = stack[4].m_obj;
lean_object* v_res_1719_;
v_res_1719_ = l_Lean_Meta_Rewrites_solveByElim___lam__2(v_x_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_);
stack->m_obj
 = v_res_1719_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__2___boxed(lean_object* v_x_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l_Lean_Meta_Rewrites_solveByElim___lam__2(v_x_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
lean_dec(v___y_1724_);
lean_dec_ref(v___y_1723_);
lean_dec(v___y_1722_);
lean_dec_ref(v___y_1721_);
lean_dec(v_x_1720_);
return v_res_1726_;
}
}
lean_object* l_Lean_Meta_Rewrites_solveByElim(lean_object* v_goals_1736_, lean_object* v_depth_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_){
_start:
{
lean_object* v___f_1743_; lean_object* v___f_1744_; lean_object* v___f_1745_; uint8_t v___x_1746_; lean_object* v___x_1747_; uint8_t v___x_1748_; lean_object* v___x_1749_; uint8_t v___x_1750_; lean_object* v___x_1751_; lean_object* v_cfg_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___f_1743_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___closed__0));
v___f_1744_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___closed__1));
v___f_1745_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___closed__2));
v___x_1746_ = 0;
v___x_1747_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1747_, 0, v_depth_1737_);
lean_ctor_set(v___x_1747_, 1, v___f_1743_);
lean_ctor_set(v___x_1747_, 2, v___f_1744_);
lean_ctor_set(v___x_1747_, 3, v___f_1745_);
lean_ctor_set_uint8(v___x_1747_, sizeof(void*)*4, v___x_1746_);
v___x_1748_ = 1;
v___x_1749_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___closed__3));
v___x_1750_ = 1;
v___x_1751_ = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(v___x_1751_, 0, v___x_1747_);
lean_ctor_set(v___x_1751_, 1, v___x_1749_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*2, v___x_1750_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*2 + 1, v___x_1748_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*2 + 2, v___x_1746_);
v_cfg_1752_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v_cfg_1752_, 0, v___x_1751_);
lean_ctor_set_uint8(v_cfg_1752_, sizeof(void*)*1, v___x_1748_);
lean_ctor_set_uint8(v_cfg_1752_, sizeof(void*)*1 + 1, v___x_1748_);
lean_ctor_set_uint8(v_cfg_1752_, sizeof(void*)*1 + 2, v___x_1748_);
lean_ctor_set_uint8(v_cfg_1752_, sizeof(void*)*1 + 3, v___x_1746_);
v___x_1753_ = lean_box(0);
v___x_1754_ = ((lean_object*)(l_Lean_Meta_Rewrites_solveByElim___closed__4));
v___x_1755_ = l_Lean_Meta_SolveByElim_mkAssumptionSet(v___x_1746_, v___x_1746_, v___x_1753_, v___x_1753_, v___x_1754_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_object* v_a_1756_; lean_object* v_fst_1757_; lean_object* v_snd_1758_; lean_object* v___x_1759_; 
v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
lean_inc(v_a_1756_);
lean_dec_ref_known(v___x_1755_, 1);
v_fst_1757_ = lean_ctor_get(v_a_1756_, 0);
lean_inc(v_fst_1757_);
v_snd_1758_ = lean_ctor_get(v_a_1756_, 1);
lean_inc(v_snd_1758_);
lean_dec(v_a_1756_);
v___x_1759_ = l_Lean_Meta_SolveByElim_solveByElim(v_cfg_1752_, v_fst_1757_, v_snd_1758_, v_goals_1736_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_1759_) == 0)
{
lean_object* v_a_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1770_; 
v_a_1760_ = lean_ctor_get(v___x_1759_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1762_ = v___x_1759_;
v_isShared_1763_ = v_isSharedCheck_1770_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_a_1760_);
lean_dec(v___x_1759_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1770_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
if (lean_obj_tag(v_a_1760_) == 0)
{
lean_object* v___x_1764_; lean_object* v___x_1766_; 
v___x_1764_ = lean_box(0);
if (v_isShared_1763_ == 0)
{
lean_ctor_set(v___x_1762_, 0, v___x_1764_);
v___x_1766_ = v___x_1762_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v___x_1764_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
else
{
lean_object* v___x_1768_; lean_object* v___x_1769_; 
lean_del_object(v___x_1762_);
lean_dec(v_a_1760_);
v___x_1768_ = lean_obj_once(&l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1, &l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1_once, _init_l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1);
v___x_1769_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(v___x_1768_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_);
return v___x_1769_;
}
}
}
else
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1778_; 
v_a_1771_ = lean_ctor_get(v___x_1759_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1773_ = v___x_1759_;
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1759_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1776_; 
if (v_isShared_1774_ == 0)
{
v___x_1776_ = v___x_1773_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_a_1771_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
}
else
{
lean_object* v_a_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1786_; 
lean_dec_ref_known(v_cfg_1752_, 1);
lean_dec(v_goals_1736_);
v_a_1779_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1781_ = v___x_1755_;
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_a_1779_);
lean_dec(v___x_1755_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1784_; 
if (v_isShared_1782_ == 0)
{
v___x_1784_ = v___x_1781_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_a_1779_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Rewrites_solveByElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_goals_1736_ = stack[0].m_obj;
lean_object* v_depth_1737_ = stack[1].m_obj;
lean_object* v_a_1738_ = stack[2].m_obj;
lean_object* v_a_1739_ = stack[3].m_obj;
lean_object* v_a_1740_ = stack[4].m_obj;
lean_object* v_a_1741_ = stack[5].m_obj;
lean_object* v_res_1787_;
v_res_1787_ = l_Lean_Meta_Rewrites_solveByElim(v_goals_1736_, v_depth_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_);
stack->m_obj
 = v_res_1787_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___boxed(lean_object* v_goals_1788_, lean_object* v_depth_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_){
_start:
{
lean_object* v_res_1795_; 
v_res_1795_ = l_Lean_Meta_Rewrites_solveByElim(v_goals_1788_, v_depth_1789_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_);
lean_dec(v_a_1793_);
lean_dec_ref(v_a_1792_);
lean_dec(v_a_1791_);
lean_dec_ref(v_a_1790_);
return v_res_1795_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0(lean_object* v_00_u03b1_1796_, lean_object* v_msg_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_){
_start:
{
lean_object* v___x_1803_; 
v___x_1803_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___redArg(v_msg_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_);
return v___x_1803_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1797_ = stack[1].m_obj;
lean_object* v___y_1798_ = stack[2].m_obj;
lean_object* v___y_1799_ = stack[3].m_obj;
lean_object* v___y_1800_ = stack[4].m_obj;
lean_object* v___y_1801_ = stack[5].m_obj;
lean_object* v_res_1804_;
v_res_1804_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0(lean_box(0), v_msg_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_);
stack->m_obj
 = v_res_1804_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0___boxed(lean_object* v_00_u03b1_1805_, lean_object* v_msg_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l_Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0(v_00_u03b1_1805_, v_msg_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec(v___y_1808_);
lean_dec_ref(v___y_1807_);
return v_res_1812_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg(lean_object* v_e_1813_, lean_object* v___y_1814_){
_start:
{
uint8_t v___x_1816_; 
v___x_1816_ = l_Lean_Expr_hasMVar(v_e_1813_);
if (v___x_1816_ == 0)
{
lean_object* v___x_1817_; 
v___x_1817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1817_, 0, v_e_1813_);
return v___x_1817_;
}
else
{
lean_object* v___x_1818_; lean_object* v_mctx_1819_; lean_object* v___x_1820_; lean_object* v_fst_1821_; lean_object* v_snd_1822_; lean_object* v___x_1823_; lean_object* v_cache_1824_; lean_object* v_zetaDeltaFVarIds_1825_; lean_object* v_postponed_1826_; lean_object* v_diag_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1836_; 
v___x_1818_ = lean_st_ref_get(v___y_1814_);
v_mctx_1819_ = lean_ctor_get(v___x_1818_, 0);
lean_inc_ref(v_mctx_1819_);
lean_dec(v___x_1818_);
v___x_1820_ = l_Lean_instantiateMVarsCore(v_mctx_1819_, v_e_1813_);
v_fst_1821_ = lean_ctor_get(v___x_1820_, 0);
lean_inc(v_fst_1821_);
v_snd_1822_ = lean_ctor_get(v___x_1820_, 1);
lean_inc(v_snd_1822_);
lean_dec_ref(v___x_1820_);
v___x_1823_ = lean_st_ref_take(v___y_1814_);
v_cache_1824_ = lean_ctor_get(v___x_1823_, 1);
v_zetaDeltaFVarIds_1825_ = lean_ctor_get(v___x_1823_, 2);
v_postponed_1826_ = lean_ctor_get(v___x_1823_, 3);
v_diag_1827_ = lean_ctor_get(v___x_1823_, 4);
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1823_);
if (v_isSharedCheck_1836_ == 0)
{
lean_object* v_unused_1837_; 
v_unused_1837_ = lean_ctor_get(v___x_1823_, 0);
lean_dec(v_unused_1837_);
v___x_1829_ = v___x_1823_;
v_isShared_1830_ = v_isSharedCheck_1836_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_diag_1827_);
lean_inc(v_postponed_1826_);
lean_inc(v_zetaDeltaFVarIds_1825_);
lean_inc(v_cache_1824_);
lean_dec(v___x_1823_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1836_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v___x_1832_; 
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 0, v_snd_1822_);
v___x_1832_ = v___x_1829_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_snd_1822_);
lean_ctor_set(v_reuseFailAlloc_1835_, 1, v_cache_1824_);
lean_ctor_set(v_reuseFailAlloc_1835_, 2, v_zetaDeltaFVarIds_1825_);
lean_ctor_set(v_reuseFailAlloc_1835_, 3, v_postponed_1826_);
lean_ctor_set(v_reuseFailAlloc_1835_, 4, v_diag_1827_);
v___x_1832_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1833_ = lean_st_ref_put(v___y_1814_, v___x_1832_);
v___x_1834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1834_, 0, v_fst_1821_);
return v___x_1834_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1813_ = stack[0].m_obj;
lean_object* v___y_1814_ = stack[1].m_obj;
lean_object* v_res_1838_;
v_res_1838_ = l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg(v_e_1813_, v___y_1814_);
stack->m_obj
 = v_res_1838_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg___boxed(lean_object* v_e_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_){
_start:
{
lean_object* v_res_1842_; 
v_res_1842_ = l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg(v_e_1839_, v___y_1840_);
lean_dec(v___y_1840_);
return v_res_1842_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0(lean_object* v_e_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_){
_start:
{
lean_object* v___x_1849_; 
v___x_1849_ = l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg(v_e_1843_, v___y_1845_);
return v___x_1849_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1843_ = stack[0].m_obj;
lean_object* v___y_1844_ = stack[1].m_obj;
lean_object* v___y_1845_ = stack[2].m_obj;
lean_object* v___y_1846_ = stack[3].m_obj;
lean_object* v___y_1847_ = stack[4].m_obj;
lean_object* v_res_1850_;
v_res_1850_ = l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0(v_e_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_);
stack->m_obj
 = v_res_1850_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___boxed(lean_object* v_e_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_){
_start:
{
lean_object* v_res_1857_; 
v_res_1857_ = l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0(v_e_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_);
lean_dec(v___y_1855_);
lean_dec_ref(v___y_1854_);
lean_dec(v___y_1853_);
lean_dec_ref(v___y_1852_);
return v_res_1857_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1858_; double v___x_1859_; 
v___x_1858_ = lean_unsigned_to_nat(0u);
v___x_1859_ = lean_float_of_nat(v___x_1858_);
return v___x_1859_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2(lean_object* v_cls_1863_, lean_object* v_msg_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_){
_start:
{
lean_object* v_ref_1870_; lean_object* v___x_1871_; lean_object* v_a_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1917_; 
v_ref_1870_ = lean_ctor_get(v___y_1867_, 2);
v___x_1871_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Rewrites_solveByElim_spec__0_spec__0(v_msg_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_);
v_a_1872_ = lean_ctor_get(v___x_1871_, 0);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1874_ = v___x_1871_;
v_isShared_1875_ = v_isSharedCheck_1917_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_a_1872_);
lean_dec(v___x_1871_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1917_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1876_; lean_object* v_traceState_1877_; lean_object* v_env_1878_; lean_object* v_nextMacroScope_1879_; lean_object* v_ngen_1880_; lean_object* v_auxDeclNGen_1881_; lean_object* v_cache_1882_; lean_object* v_recordedDeps_1883_; lean_object* v_messages_1884_; lean_object* v_infoState_1885_; lean_object* v_snapshotTasks_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1916_; 
v___x_1876_ = lean_st_ref_take(v___y_1868_);
v_traceState_1877_ = lean_ctor_get(v___x_1876_, 4);
v_env_1878_ = lean_ctor_get(v___x_1876_, 0);
v_nextMacroScope_1879_ = lean_ctor_get(v___x_1876_, 1);
v_ngen_1880_ = lean_ctor_get(v___x_1876_, 2);
v_auxDeclNGen_1881_ = lean_ctor_get(v___x_1876_, 3);
v_cache_1882_ = lean_ctor_get(v___x_1876_, 5);
v_recordedDeps_1883_ = lean_ctor_get(v___x_1876_, 6);
v_messages_1884_ = lean_ctor_get(v___x_1876_, 7);
v_infoState_1885_ = lean_ctor_get(v___x_1876_, 8);
v_snapshotTasks_1886_ = lean_ctor_get(v___x_1876_, 9);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1888_ = v___x_1876_;
v_isShared_1889_ = v_isSharedCheck_1916_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_snapshotTasks_1886_);
lean_inc(v_infoState_1885_);
lean_inc(v_messages_1884_);
lean_inc(v_recordedDeps_1883_);
lean_inc(v_cache_1882_);
lean_inc(v_traceState_1877_);
lean_inc(v_auxDeclNGen_1881_);
lean_inc(v_ngen_1880_);
lean_inc(v_nextMacroScope_1879_);
lean_inc(v_env_1878_);
lean_dec(v___x_1876_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1916_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
uint64_t v_tid_1890_; lean_object* v_traces_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1915_; 
v_tid_1890_ = lean_ctor_get_uint64(v_traceState_1877_, sizeof(void*)*1);
v_traces_1891_ = lean_ctor_get(v_traceState_1877_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v_traceState_1877_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1893_ = v_traceState_1877_;
v_isShared_1894_ = v_isSharedCheck_1915_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_traces_1891_);
lean_dec(v_traceState_1877_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1915_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1895_; lean_object* v___x_1896_; double v___x_1897_; uint8_t v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1906_; 
v___x_1895_ = lean_box(0);
v___x_1896_ = lean_box(0);
v___x_1897_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__0);
v___x_1898_ = 0;
v___x_1899_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__1));
v___x_1900_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1900_, 0, v_cls_1863_);
lean_ctor_set(v___x_1900_, 1, v___x_1896_);
lean_ctor_set(v___x_1900_, 2, v___x_1899_);
lean_ctor_set_float(v___x_1900_, sizeof(void*)*3, v___x_1897_);
lean_ctor_set_float(v___x_1900_, sizeof(void*)*3 + 8, v___x_1897_);
lean_ctor_set_uint8(v___x_1900_, sizeof(void*)*3 + 16, v___x_1898_);
v___x_1901_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__2));
v___x_1902_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1900_);
lean_ctor_set(v___x_1902_, 1, v_a_1872_);
lean_ctor_set(v___x_1902_, 2, v___x_1901_);
lean_inc(v_ref_1870_);
v___x_1903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1903_, 0, v_ref_1870_);
lean_ctor_set(v___x_1903_, 1, v___x_1902_);
v___x_1904_ = l_Lean_PersistentArray_push___redArg(v_traces_1891_, v___x_1903_);
if (v_isShared_1894_ == 0)
{
lean_ctor_set(v___x_1893_, 0, v___x_1904_);
v___x_1906_ = v___x_1893_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___x_1904_);
lean_ctor_set_uint64(v_reuseFailAlloc_1914_, sizeof(void*)*1, v_tid_1890_);
v___x_1906_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
lean_object* v___x_1908_; 
if (v_isShared_1889_ == 0)
{
lean_ctor_set(v___x_1888_, 4, v___x_1906_);
v___x_1908_ = v___x_1888_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_env_1878_);
lean_ctor_set(v_reuseFailAlloc_1913_, 1, v_nextMacroScope_1879_);
lean_ctor_set(v_reuseFailAlloc_1913_, 2, v_ngen_1880_);
lean_ctor_set(v_reuseFailAlloc_1913_, 3, v_auxDeclNGen_1881_);
lean_ctor_set(v_reuseFailAlloc_1913_, 4, v___x_1906_);
lean_ctor_set(v_reuseFailAlloc_1913_, 5, v_cache_1882_);
lean_ctor_set(v_reuseFailAlloc_1913_, 6, v_recordedDeps_1883_);
lean_ctor_set(v_reuseFailAlloc_1913_, 7, v_messages_1884_);
lean_ctor_set(v_reuseFailAlloc_1913_, 8, v_infoState_1885_);
lean_ctor_set(v_reuseFailAlloc_1913_, 9, v_snapshotTasks_1886_);
v___x_1908_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
lean_object* v___x_1909_; lean_object* v___x_1911_; 
v___x_1909_ = lean_st_ref_put(v___y_1868_, v___x_1908_);
if (v_isShared_1875_ == 0)
{
lean_ctor_set(v___x_1874_, 0, v___x_1895_);
v___x_1911_ = v___x_1874_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v___x_1895_);
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
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1863_ = stack[0].m_obj;
lean_object* v_msg_1864_ = stack[1].m_obj;
lean_object* v___y_1865_ = stack[2].m_obj;
lean_object* v___y_1866_ = stack[3].m_obj;
lean_object* v___y_1867_ = stack[4].m_obj;
lean_object* v___y_1868_ = stack[5].m_obj;
lean_object* v_res_1918_;
v_res_1918_ = l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2(v_cls_1863_, v_msg_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_);
stack->m_obj
 = v_res_1918_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___boxed(lean_object* v_cls_1919_, lean_object* v_msg_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_){
_start:
{
lean_object* v_res_1926_; 
v_res_1926_ = l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2(v_cls_1919_, v_msg_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_);
lean_dec(v___y_1924_);
lean_dec_ref(v___y_1923_);
lean_dec(v___y_1922_);
lean_dec_ref(v___y_1921_);
return v_res_1926_;
}
}
lean_object* l_List_mapM_loop___at___00Lean_Meta_Rewrites_rwLemma_spec__1(lean_object* v_x_1927_, lean_object* v_x_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_){
_start:
{
if (lean_obj_tag(v_x_1927_) == 0)
{
lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1934_ = l_List_reverse___redArg(v_x_1928_);
v___x_1935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1934_);
return v___x_1935_;
}
else
{
lean_object* v_head_1936_; lean_object* v_tail_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1955_; 
v_head_1936_ = lean_ctor_get(v_x_1927_, 0);
v_tail_1937_ = lean_ctor_get(v_x_1927_, 1);
v_isSharedCheck_1955_ = !lean_is_exclusive(v_x_1927_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1939_ = v_x_1927_;
v_isShared_1940_ = v_isSharedCheck_1955_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_tail_1937_);
lean_inc(v_head_1936_);
lean_dec(v_x_1927_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1955_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1941_; 
v___x_1941_ = l_Lean_MVarId_assumption(v_head_1936_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_);
if (lean_obj_tag(v___x_1941_) == 0)
{
lean_object* v_a_1942_; lean_object* v___x_1944_; 
v_a_1942_ = lean_ctor_get(v___x_1941_, 0);
lean_inc(v_a_1942_);
lean_dec_ref_known(v___x_1941_, 1);
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 1, v_x_1928_);
lean_ctor_set(v___x_1939_, 0, v_a_1942_);
v___x_1944_ = v___x_1939_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_a_1942_);
lean_ctor_set(v_reuseFailAlloc_1946_, 1, v_x_1928_);
v___x_1944_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
v_x_1927_ = v_tail_1937_;
v_x_1928_ = v___x_1944_;
goto _start;
}
}
else
{
lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1954_; 
lean_del_object(v___x_1939_);
lean_dec(v_tail_1937_);
lean_dec(v_x_1928_);
v_a_1947_ = lean_ctor_get(v___x_1941_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1941_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1949_ = v___x_1941_;
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___x_1941_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1952_; 
if (v_isShared_1950_ == 0)
{
v___x_1952_ = v___x_1949_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_a_1947_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00Lean_Meta_Rewrites_rwLemma_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1927_ = stack[0].m_obj;
lean_object* v_x_1928_ = stack[1].m_obj;
lean_object* v___y_1929_ = stack[2].m_obj;
lean_object* v___y_1930_ = stack[3].m_obj;
lean_object* v___y_1931_ = stack[4].m_obj;
lean_object* v___y_1932_ = stack[5].m_obj;
lean_object* v_res_1956_;
v_res_1956_ = l_List_mapM_loop___at___00Lean_Meta_Rewrites_rwLemma_spec__1(v_x_1927_, v_x_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_);
stack->m_obj
 = v_res_1956_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Rewrites_rwLemma_spec__1___boxed(lean_object* v_x_1957_, lean_object* v_x_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
lean_object* v_res_1964_; 
v_res_1964_ = l_List_mapM_loop___at___00Lean_Meta_Rewrites_rwLemma_spec__1(v_x_1957_, v_x_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
return v_res_1964_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5(void){
_start:
{
lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1977_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_));
v___x_1978_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__4));
v___x_1979_ = l_Lean_Name_append(v___x_1978_, v___x_1977_);
return v___x_1979_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__7(void){
_start:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; 
v___x_1981_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__6));
v___x_1982_ = l_Lean_stringToMessageData(v___x_1981_);
return v___x_1982_;
}
}
lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0(lean_object* v_weight_1984_, lean_object* v_goal_1985_, lean_object* v_target_1986_, uint8_t v_symm_1987_, uint8_t v_side_1988_, lean_object* v_lem_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_){
_start:
{
lean_object* v___y_1996_; lean_object* v___y_1997_; lean_object* v___y_1998_; lean_object* v___y_1999_; uint8_t v___y_2000_; lean_object* v___y_2021_; lean_object* v___y_2022_; lean_object* v___y_2023_; lean_object* v___y_2024_; lean_object* v___y_2025_; lean_object* v_fst_2026_; uint8_t v_snd_2027_; uint8_t v___y_2052_; lean_object* v___y_2053_; lean_object* v___y_2054_; lean_object* v___y_2055_; lean_object* v___y_2056_; lean_object* v___y_2057_; uint8_t v___y_2074_; lean_object* v___y_2075_; uint8_t v_discharge_2076_; lean_object* v___y_2077_; lean_object* v___y_2078_; lean_object* v___y_2079_; lean_object* v___y_2080_; lean_object* v___y_2084_; lean_object* v___y_2085_; uint8_t v___y_2086_; uint8_t v___y_2087_; lean_object* v___y_2088_; lean_object* v___y_2089_; lean_object* v___y_2090_; lean_object* v___y_2091_; lean_object* v___y_2092_; uint8_t v___y_2093_; uint8_t v___y_2105_; uint8_t v___y_2106_; lean_object* v___y_2107_; lean_object* v___y_2108_; lean_object* v___y_2109_; lean_object* v___y_2110_; lean_object* v___y_2111_; lean_object* v___y_2112_; lean_object* v___y_2113_; uint8_t v___y_2114_; lean_object* v___y_2126_; lean_object* v___y_2206_; lean_object* v___y_2207_; lean_object* v___y_2208_; lean_object* v___y_2209_; lean_object* v_val_2224_; 
if (lean_obj_tag(v_lem_1989_) == 0)
{
lean_object* v_val_2235_; 
v_val_2235_ = lean_ctor_get(v_lem_1989_, 0);
lean_inc(v_val_2235_);
lean_dec_ref_known(v_lem_1989_, 1);
v_val_2224_ = v_val_2235_;
goto v___jp_2223_;
}
else
{
lean_object* v_val_2236_; lean_object* v___x_2237_; 
v_val_2236_ = lean_ctor_get(v_lem_1989_, 0);
lean_inc(v_val_2236_);
lean_dec_ref_known(v_lem_1989_, 1);
v___x_2237_ = l_Lean_Meta_saveState___redArg(v___y_1991_, v___y_1993_);
if (lean_obj_tag(v___x_2237_) == 0)
{
lean_object* v_a_2238_; lean_object* v___x_2239_; 
v_a_2238_ = lean_ctor_get(v___x_2237_, 0);
lean_inc(v_a_2238_);
lean_dec_ref_known(v___x_2237_, 1);
v___x_2239_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v_val_2236_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
if (lean_obj_tag(v___x_2239_) == 0)
{
lean_object* v_a_2240_; 
lean_dec(v_a_2238_);
v_a_2240_ = lean_ctor_get(v___x_2239_, 0);
lean_inc(v_a_2240_);
lean_dec_ref_known(v___x_2239_, 1);
v_val_2224_ = v_a_2240_;
goto v___jp_2223_;
}
else
{
lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2270_; 
lean_dec_ref(v_target_1986_);
lean_dec(v_goal_1985_);
lean_dec(v_weight_1984_);
v_a_2241_ = lean_ctor_get(v___x_2239_, 0);
v_isSharedCheck_2270_ = !lean_is_exclusive(v___x_2239_);
if (v_isSharedCheck_2270_ == 0)
{
v___x_2243_ = v___x_2239_;
v_isShared_2244_ = v_isSharedCheck_2270_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_dec(v___x_2239_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2270_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
uint8_t v___y_2246_; uint8_t v___x_2268_; 
v___x_2268_ = l_Lean_Exception_isInterrupt(v_a_2241_);
if (v___x_2268_ == 0)
{
uint8_t v___x_2269_; 
lean_inc(v_a_2241_);
v___x_2269_ = l_Lean_Exception_isRuntime(v_a_2241_);
v___y_2246_ = v___x_2269_;
goto v___jp_2245_;
}
else
{
v___y_2246_ = v___x_2268_;
goto v___jp_2245_;
}
v___jp_2245_:
{
if (v___y_2246_ == 0)
{
lean_object* v___x_2247_; 
lean_del_object(v___x_2243_);
lean_dec(v_a_2241_);
v___x_2247_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2238_, v___y_1991_, v___y_1993_);
if (lean_obj_tag(v___x_2247_) == 0)
{
lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2255_; 
v_isSharedCheck_2255_ = !lean_is_exclusive(v___x_2247_);
if (v_isSharedCheck_2255_ == 0)
{
lean_object* v_unused_2256_; 
v_unused_2256_ = lean_ctor_get(v___x_2247_, 0);
lean_dec(v_unused_2256_);
v___x_2249_ = v___x_2247_;
v_isShared_2250_ = v_isSharedCheck_2255_;
goto v_resetjp_2248_;
}
else
{
lean_dec(v___x_2247_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2255_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2251_; lean_object* v___x_2253_; 
v___x_2251_ = lean_box(0);
if (v_isShared_2250_ == 0)
{
lean_ctor_set(v___x_2249_, 0, v___x_2251_);
v___x_2253_ = v___x_2249_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v___x_2251_);
v___x_2253_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
return v___x_2253_;
}
}
}
else
{
lean_object* v_a_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2264_; 
v_a_2257_ = lean_ctor_get(v___x_2247_, 0);
v_isSharedCheck_2264_ = !lean_is_exclusive(v___x_2247_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2259_ = v___x_2247_;
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_a_2257_);
lean_dec(v___x_2247_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___x_2262_; 
if (v_isShared_2260_ == 0)
{
v___x_2262_ = v___x_2259_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_a_2257_);
v___x_2262_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
return v___x_2262_;
}
}
}
}
else
{
lean_object* v___x_2266_; 
lean_dec(v_a_2238_);
if (v_isShared_2244_ == 0)
{
v___x_2266_ = v___x_2243_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v_a_2241_);
v___x_2266_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
return v___x_2266_;
}
}
}
}
}
}
else
{
lean_object* v_a_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2278_; 
lean_dec(v_val_2236_);
lean_dec_ref(v_target_1986_);
lean_dec(v_goal_1985_);
lean_dec(v_weight_1984_);
v_a_2271_ = lean_ctor_get(v___x_2237_, 0);
v_isSharedCheck_2278_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2273_ = v___x_2237_;
v_isShared_2274_ = v_isSharedCheck_2278_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_a_2271_);
lean_dec(v___x_2237_);
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
v___jp_1995_:
{
if (v___y_2000_ == 0)
{
lean_object* v___x_2001_; 
lean_dec_ref(v___y_1997_);
v___x_2001_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1999_, v___y_1996_, v___y_1998_);
if (lean_obj_tag(v___x_2001_) == 0)
{
lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2009_; 
v_isSharedCheck_2009_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2009_ == 0)
{
lean_object* v_unused_2010_; 
v_unused_2010_ = lean_ctor_get(v___x_2001_, 0);
lean_dec(v_unused_2010_);
v___x_2003_ = v___x_2001_;
v_isShared_2004_ = v_isSharedCheck_2009_;
goto v_resetjp_2002_;
}
else
{
lean_dec(v___x_2001_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2009_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2005_; lean_object* v___x_2007_; 
v___x_2005_ = lean_box(0);
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 0, v___x_2005_);
v___x_2007_ = v___x_2003_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v___x_2005_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
}
else
{
lean_object* v_a_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2018_; 
v_a_2011_ = lean_ctor_get(v___x_2001_, 0);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_2013_ = v___x_2001_;
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_a_2011_);
lean_dec(v___x_2001_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2016_; 
if (v_isShared_2014_ == 0)
{
v___x_2016_ = v___x_2013_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_a_2011_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
return v___x_2016_;
}
}
}
}
else
{
lean_object* v___x_2019_; 
lean_dec_ref(v___y_1999_);
v___x_2019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2019_, 0, v___y_1997_);
return v___x_2019_;
}
}
v___jp_2020_:
{
lean_object* v___x_2028_; lean_object* v_mctx_2029_; lean_object* v_eNew_2030_; lean_object* v___x_2031_; 
v___x_2028_ = lean_st_ref_get(v___y_2025_);
v_mctx_2029_ = lean_ctor_get(v___x_2028_, 0);
lean_inc_ref_n(v_mctx_2029_, 2);
lean_dec(v___x_2028_);
v_eNew_2030_ = lean_ctor_get(v___y_2022_, 0);
lean_inc_ref(v_eNew_2030_);
v___x_2031_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(v_mctx_2029_, v_eNew_2030_, v___y_2023_, v___y_2025_, v___y_2024_, v___y_2021_);
if (lean_obj_tag(v___x_2031_) == 0)
{
lean_object* v_a_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2042_; 
v_a_2032_ = lean_ctor_get(v___x_2031_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2034_ = v___x_2031_;
v_isShared_2035_ = v_isSharedCheck_2042_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_a_2032_);
lean_dec(v___x_2031_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2042_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2036_; uint8_t v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2040_; 
v___x_2036_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2036_, 0, v_fst_2026_);
lean_ctor_set(v___x_2036_, 1, v_weight_1984_);
lean_ctor_set(v___x_2036_, 2, v___y_2022_);
lean_ctor_set(v___x_2036_, 3, v_mctx_2029_);
lean_ctor_set_uint8(v___x_2036_, sizeof(void*)*4, v_snd_2027_);
v___x_2037_ = lean_unbox(v_a_2032_);
lean_dec(v_a_2032_);
lean_ctor_set_uint8(v___x_2036_, sizeof(void*)*4 + 1, v___x_2037_);
v___x_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2038_, 0, v___x_2036_);
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 0, v___x_2038_);
v___x_2040_ = v___x_2034_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v___x_2038_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
else
{
lean_object* v_a_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2050_; 
lean_dec_ref(v_mctx_2029_);
lean_dec_ref(v_fst_2026_);
lean_dec_ref(v___y_2022_);
lean_dec(v_weight_1984_);
v_a_2043_ = lean_ctor_get(v___x_2031_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2045_ = v___x_2031_;
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_a_2043_);
lean_dec(v___x_2031_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2048_; 
if (v_isShared_2046_ == 0)
{
v___x_2048_ = v___x_2045_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_a_2043_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
}
v___jp_2051_:
{
lean_object* v___x_2058_; 
v___x_2058_ = l_Lean_Meta_Rewrites_rewriteResultLemma(v___y_2053_);
if (lean_obj_tag(v___x_2058_) == 1)
{
lean_object* v_val_2059_; lean_object* v___x_2060_; lean_object* v_a_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; uint8_t v___x_2064_; 
v_val_2059_ = lean_ctor_get(v___x_2058_, 0);
lean_inc(v_val_2059_);
lean_dec_ref_known(v___x_2058_, 1);
v___x_2060_ = l_Lean_instantiateMVars___at___00Lean_Meta_Rewrites_rwLemma_spec__0___redArg(v_val_2059_, v___y_2055_);
v_a_2061_ = lean_ctor_get(v___x_2060_, 0);
lean_inc(v_a_2061_);
lean_dec_ref(v___x_2060_);
v___x_2062_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__1));
v___x_2063_ = lean_unsigned_to_nat(4u);
v___x_2064_ = l_Lean_Expr_isAppOfArity(v_a_2061_, v___x_2062_, v___x_2063_);
if (v___x_2064_ == 0)
{
v___y_2021_ = v___y_2057_;
v___y_2022_ = v___y_2053_;
v___y_2023_ = v___y_2054_;
v___y_2024_ = v___y_2056_;
v___y_2025_ = v___y_2055_;
v_fst_2026_ = v_a_2061_;
v_snd_2027_ = v___x_2064_;
goto v___jp_2020_;
}
else
{
lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; 
v___x_2065_ = lean_unsigned_to_nat(3u);
v___x_2066_ = l_Lean_Expr_getAppNumArgs(v_a_2061_);
v___x_2067_ = lean_nat_sub(v___x_2066_, v___x_2065_);
lean_dec(v___x_2066_);
v___x_2068_ = lean_unsigned_to_nat(1u);
v___x_2069_ = lean_nat_sub(v___x_2067_, v___x_2068_);
lean_dec(v___x_2067_);
v___x_2070_ = l_Lean_Expr_getRevArg_x21(v_a_2061_, v___x_2069_);
lean_dec(v_a_2061_);
v___y_2021_ = v___y_2057_;
v___y_2022_ = v___y_2053_;
v___y_2023_ = v___y_2054_;
v___y_2024_ = v___y_2056_;
v___y_2025_ = v___y_2055_;
v_fst_2026_ = v___x_2070_;
v_snd_2027_ = v___y_2052_;
goto v___jp_2020_;
}
}
else
{
lean_object* v___x_2071_; lean_object* v___x_2072_; 
lean_dec(v___x_2058_);
lean_dec_ref(v___y_2053_);
lean_dec(v_weight_1984_);
v___x_2071_ = lean_box(0);
v___x_2072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2071_);
return v___x_2072_;
}
}
v___jp_2073_:
{
if (v_discharge_2076_ == 0)
{
lean_object* v___x_2081_; lean_object* v___x_2082_; 
lean_dec_ref(v___y_2075_);
lean_dec(v_weight_1984_);
v___x_2081_ = lean_box(0);
v___x_2082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2081_);
return v___x_2082_;
}
else
{
v___y_2052_ = v___y_2074_;
v___y_2053_ = v___y_2075_;
v___y_2054_ = v___y_2077_;
v___y_2055_ = v___y_2078_;
v___y_2056_ = v___y_2079_;
v___y_2057_ = v___y_2080_;
goto v___jp_2051_;
}
}
v___jp_2083_:
{
if (v___y_2093_ == 0)
{
lean_object* v___x_2094_; 
lean_dec_ref(v___y_2085_);
v___x_2094_ = l_Lean_Meta_SavedState_restore___redArg(v___y_2084_, v___y_2089_, v___y_2091_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_dec_ref_known(v___x_2094_, 1);
v___y_2074_ = v___y_2087_;
v___y_2075_ = v___y_2088_;
v_discharge_2076_ = v___y_2086_;
v___y_2077_ = v___y_2092_;
v___y_2078_ = v___y_2089_;
v___y_2079_ = v___y_2090_;
v___y_2080_ = v___y_2091_;
goto v___jp_2073_;
}
else
{
lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2102_; 
lean_dec_ref(v___y_2088_);
lean_dec(v_weight_1984_);
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2102_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2097_ = v___x_2094_;
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_dec(v___x_2094_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2100_; 
if (v_isShared_2098_ == 0)
{
v___x_2100_ = v___x_2097_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_a_2095_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
return v___x_2100_;
}
}
}
}
else
{
lean_object* v___x_2103_; 
lean_dec_ref(v___y_2088_);
lean_dec_ref(v___y_2084_);
lean_dec(v_weight_1984_);
v___x_2103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2103_, 0, v___y_2085_);
return v___x_2103_;
}
}
v___jp_2104_:
{
if (v___y_2114_ == 0)
{
lean_object* v___x_2115_; 
lean_dec_ref(v___y_2109_);
v___x_2115_ = l_Lean_Meta_SavedState_restore___redArg(v___y_2112_, v___y_2108_, v___y_2111_);
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_dec_ref_known(v___x_2115_, 1);
v___y_2074_ = v___y_2106_;
v___y_2075_ = v___y_2107_;
v_discharge_2076_ = v___y_2105_;
v___y_2077_ = v___y_2113_;
v___y_2078_ = v___y_2108_;
v___y_2079_ = v___y_2110_;
v___y_2080_ = v___y_2111_;
goto v___jp_2073_;
}
else
{
lean_object* v_a_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2123_; 
lean_dec_ref(v___y_2107_);
lean_dec(v_weight_1984_);
v_a_2116_ = lean_ctor_get(v___x_2115_, 0);
v_isSharedCheck_2123_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2118_ = v___x_2115_;
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_a_2116_);
lean_dec(v___x_2115_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2121_; 
if (v_isShared_2119_ == 0)
{
v___x_2121_ = v___x_2118_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v_a_2116_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
return v___x_2121_;
}
}
}
}
else
{
lean_object* v___x_2124_; 
lean_dec_ref(v___y_2112_);
lean_dec_ref(v___y_2107_);
lean_dec(v_weight_1984_);
v___x_2124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2124_, 0, v___y_2109_);
return v___x_2124_;
}
}
v___jp_2125_:
{
uint8_t v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
v___x_2127_ = 1;
v___x_2128_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__2));
v___x_2129_ = l_Lean_Meta_saveState___redArg(v___y_1991_, v___y_1993_);
if (lean_obj_tag(v___x_2129_) == 0)
{
lean_object* v_a_2130_; lean_object* v___x_2131_; 
v_a_2130_ = lean_ctor_get(v___x_2129_, 0);
lean_inc(v_a_2130_);
lean_dec_ref_known(v___x_2129_, 1);
lean_inc_ref(v___y_2126_);
v___x_2131_ = l_Lean_MVarId_rewrite(v_goal_1985_, v_target_1986_, v___y_2126_, v_symm_1987_, v___x_2128_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
if (lean_obj_tag(v___x_2131_) == 0)
{
lean_object* v_a_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2193_; 
lean_dec(v_a_2130_);
v_a_2132_ = lean_ctor_get(v___x_2131_, 0);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2134_ = v___x_2131_;
v_isShared_2135_ = v_isSharedCheck_2193_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_a_2132_);
lean_dec(v___x_2131_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2193_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v_eNew_2136_; lean_object* v_mvarIds_2137_; uint8_t v___x_2138_; 
v_eNew_2136_ = lean_ctor_get(v_a_2132_, 0);
v_mvarIds_2137_ = lean_ctor_get(v_a_2132_, 2);
v___x_2138_ = l_List_isEmpty___redArg(v_mvarIds_2137_);
if (v___x_2138_ == 0)
{
lean_del_object(v___x_2134_);
lean_dec_ref(v___y_2126_);
switch(v_side_1988_)
{
case 0:
{
v___y_2074_ = v___x_2127_;
v___y_2075_ = v_a_2132_;
v_discharge_2076_ = v___x_2138_;
v___y_2077_ = v___y_1990_;
v___y_2078_ = v___y_1991_;
v___y_2079_ = v___y_1992_;
v___y_2080_ = v___y_1993_;
goto v___jp_2073_;
}
case 1:
{
lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___x_2139_ = lean_box(0);
v___x_2140_ = l_Lean_Meta_saveState___redArg(v___y_1991_, v___y_1993_);
if (lean_obj_tag(v___x_2140_) == 0)
{
lean_object* v_a_2141_; lean_object* v___x_2142_; 
v_a_2141_ = lean_ctor_get(v___x_2140_, 0);
lean_inc(v_a_2141_);
lean_dec_ref_known(v___x_2140_, 1);
lean_inc(v_mvarIds_2137_);
v___x_2142_ = l_List_mapM_loop___at___00Lean_Meta_Rewrites_rwLemma_spec__1(v_mvarIds_2137_, v___x_2139_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
if (lean_obj_tag(v___x_2142_) == 0)
{
lean_dec_ref_known(v___x_2142_, 1);
lean_dec(v_a_2141_);
v___y_2052_ = v___x_2127_;
v___y_2053_ = v_a_2132_;
v___y_2054_ = v___y_1990_;
v___y_2055_ = v___y_1991_;
v___y_2056_ = v___y_1992_;
v___y_2057_ = v___y_1993_;
goto v___jp_2051_;
}
else
{
lean_object* v_a_2143_; uint8_t v___x_2144_; 
v_a_2143_ = lean_ctor_get(v___x_2142_, 0);
lean_inc(v_a_2143_);
lean_dec_ref_known(v___x_2142_, 1);
v___x_2144_ = l_Lean_Exception_isInterrupt(v_a_2143_);
if (v___x_2144_ == 0)
{
uint8_t v___x_2145_; 
lean_inc(v_a_2143_);
v___x_2145_ = l_Lean_Exception_isRuntime(v_a_2143_);
v___y_2105_ = v___x_2138_;
v___y_2106_ = v___x_2127_;
v___y_2107_ = v_a_2132_;
v___y_2108_ = v___y_1991_;
v___y_2109_ = v_a_2143_;
v___y_2110_ = v___y_1992_;
v___y_2111_ = v___y_1993_;
v___y_2112_ = v_a_2141_;
v___y_2113_ = v___y_1990_;
v___y_2114_ = v___x_2145_;
goto v___jp_2104_;
}
else
{
v___y_2105_ = v___x_2138_;
v___y_2106_ = v___x_2127_;
v___y_2107_ = v_a_2132_;
v___y_2108_ = v___y_1991_;
v___y_2109_ = v_a_2143_;
v___y_2110_ = v___y_1992_;
v___y_2111_ = v___y_1993_;
v___y_2112_ = v_a_2141_;
v___y_2113_ = v___y_1990_;
v___y_2114_ = v___x_2144_;
goto v___jp_2104_;
}
}
}
else
{
lean_object* v_a_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2153_; 
lean_dec(v_a_2132_);
lean_dec(v_weight_1984_);
v_a_2146_ = lean_ctor_get(v___x_2140_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2140_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2148_ = v___x_2140_;
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_a_2146_);
lean_dec(v___x_2140_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2151_; 
if (v_isShared_2149_ == 0)
{
v___x_2151_ = v___x_2148_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_a_2146_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
}
}
default: 
{
lean_object* v___x_2154_; lean_object* v___x_2155_; 
v___x_2154_ = lean_unsigned_to_nat(6u);
v___x_2155_ = l_Lean_Meta_saveState___redArg(v___y_1991_, v___y_1993_);
if (lean_obj_tag(v___x_2155_) == 0)
{
lean_object* v_a_2156_; lean_object* v___x_2157_; 
v_a_2156_ = lean_ctor_get(v___x_2155_, 0);
lean_inc(v_a_2156_);
lean_dec_ref_known(v___x_2155_, 1);
lean_inc(v_mvarIds_2137_);
v___x_2157_ = l_Lean_Meta_Rewrites_solveByElim(v_mvarIds_2137_, v___x_2154_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
if (lean_obj_tag(v___x_2157_) == 0)
{
lean_dec_ref_known(v___x_2157_, 1);
lean_dec(v_a_2156_);
v___y_2052_ = v___x_2127_;
v___y_2053_ = v_a_2132_;
v___y_2054_ = v___y_1990_;
v___y_2055_ = v___y_1991_;
v___y_2056_ = v___y_1992_;
v___y_2057_ = v___y_1993_;
goto v___jp_2051_;
}
else
{
lean_object* v_a_2158_; uint8_t v___x_2159_; 
v_a_2158_ = lean_ctor_get(v___x_2157_, 0);
lean_inc(v_a_2158_);
lean_dec_ref_known(v___x_2157_, 1);
v___x_2159_ = l_Lean_Exception_isInterrupt(v_a_2158_);
if (v___x_2159_ == 0)
{
uint8_t v___x_2160_; 
lean_inc(v_a_2158_);
v___x_2160_ = l_Lean_Exception_isRuntime(v_a_2158_);
v___y_2084_ = v_a_2156_;
v___y_2085_ = v_a_2158_;
v___y_2086_ = v___x_2138_;
v___y_2087_ = v___x_2127_;
v___y_2088_ = v_a_2132_;
v___y_2089_ = v___y_1991_;
v___y_2090_ = v___y_1992_;
v___y_2091_ = v___y_1993_;
v___y_2092_ = v___y_1990_;
v___y_2093_ = v___x_2160_;
goto v___jp_2083_;
}
else
{
v___y_2084_ = v_a_2156_;
v___y_2085_ = v_a_2158_;
v___y_2086_ = v___x_2138_;
v___y_2087_ = v___x_2127_;
v___y_2088_ = v_a_2132_;
v___y_2089_ = v___y_1991_;
v___y_2090_ = v___y_1992_;
v___y_2091_ = v___y_1993_;
v___y_2092_ = v___y_1990_;
v___y_2093_ = v___x_2159_;
goto v___jp_2083_;
}
}
}
else
{
lean_object* v_a_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2168_; 
lean_dec(v_a_2132_);
lean_dec(v_weight_1984_);
v_a_2161_ = lean_ctor_get(v___x_2155_, 0);
v_isSharedCheck_2168_ = !lean_is_exclusive(v___x_2155_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2163_ = v___x_2155_;
v_isShared_2164_ = v_isSharedCheck_2168_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_a_2161_);
lean_dec(v___x_2155_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2168_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v___x_2166_; 
if (v_isShared_2164_ == 0)
{
v___x_2166_ = v___x_2163_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v_a_2161_);
v___x_2166_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
return v___x_2166_;
}
}
}
}
}
}
else
{
lean_object* v___x_2169_; lean_object* v_mctx_2170_; lean_object* v___x_2171_; 
v___x_2169_ = lean_st_ref_get(v___y_1991_);
v_mctx_2170_ = lean_ctor_get(v___x_2169_, 0);
lean_inc_ref_n(v_mctx_2170_, 2);
lean_dec(v___x_2169_);
lean_inc_ref(v_eNew_2136_);
v___x_2171_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(v_mctx_2170_, v_eNew_2136_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
if (lean_obj_tag(v___x_2171_) == 0)
{
lean_object* v_a_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2184_; 
v_a_2172_ = lean_ctor_get(v___x_2171_, 0);
v_isSharedCheck_2184_ = !lean_is_exclusive(v___x_2171_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2174_ = v___x_2171_;
v_isShared_2175_ = v_isSharedCheck_2184_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_a_2172_);
lean_dec(v___x_2171_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2184_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2176_; uint8_t v___x_2177_; lean_object* v___x_2179_; 
v___x_2176_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2176_, 0, v___y_2126_);
lean_ctor_set(v___x_2176_, 1, v_weight_1984_);
lean_ctor_set(v___x_2176_, 2, v_a_2132_);
lean_ctor_set(v___x_2176_, 3, v_mctx_2170_);
lean_ctor_set_uint8(v___x_2176_, sizeof(void*)*4, v_symm_1987_);
v___x_2177_ = lean_unbox(v_a_2172_);
lean_dec(v_a_2172_);
lean_ctor_set_uint8(v___x_2176_, sizeof(void*)*4 + 1, v___x_2177_);
if (v_isShared_2135_ == 0)
{
lean_ctor_set_tag(v___x_2134_, 1);
lean_ctor_set(v___x_2134_, 0, v___x_2176_);
v___x_2179_ = v___x_2134_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v___x_2176_);
v___x_2179_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
lean_object* v___x_2181_; 
if (v_isShared_2175_ == 0)
{
lean_ctor_set(v___x_2174_, 0, v___x_2179_);
v___x_2181_ = v___x_2174_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v___x_2179_);
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
else
{
lean_object* v_a_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2192_; 
lean_dec_ref(v_mctx_2170_);
lean_del_object(v___x_2134_);
lean_dec(v_a_2132_);
lean_dec_ref(v___y_2126_);
lean_dec(v_weight_1984_);
v_a_2185_ = lean_ctor_get(v___x_2171_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2171_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2187_ = v___x_2171_;
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_a_2185_);
lean_dec(v___x_2171_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2190_; 
if (v_isShared_2188_ == 0)
{
v___x_2190_ = v___x_2187_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_a_2185_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
return v___x_2190_;
}
}
}
}
}
}
else
{
lean_object* v_a_2194_; uint8_t v___x_2195_; 
lean_dec_ref(v___y_2126_);
lean_dec(v_weight_1984_);
v_a_2194_ = lean_ctor_get(v___x_2131_, 0);
lean_inc(v_a_2194_);
lean_dec_ref_known(v___x_2131_, 1);
v___x_2195_ = l_Lean_Exception_isInterrupt(v_a_2194_);
if (v___x_2195_ == 0)
{
uint8_t v___x_2196_; 
lean_inc(v_a_2194_);
v___x_2196_ = l_Lean_Exception_isRuntime(v_a_2194_);
v___y_1996_ = v___y_1991_;
v___y_1997_ = v_a_2194_;
v___y_1998_ = v___y_1993_;
v___y_1999_ = v_a_2130_;
v___y_2000_ = v___x_2196_;
goto v___jp_1995_;
}
else
{
v___y_1996_ = v___y_1991_;
v___y_1997_ = v_a_2194_;
v___y_1998_ = v___y_1993_;
v___y_1999_ = v_a_2130_;
v___y_2000_ = v___x_2195_;
goto v___jp_1995_;
}
}
}
else
{
lean_object* v_a_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2204_; 
lean_dec_ref(v___y_2126_);
lean_dec_ref(v_target_1986_);
lean_dec(v_goal_1985_);
lean_dec(v_weight_1984_);
v_a_2197_ = lean_ctor_get(v___x_2129_, 0);
v_isSharedCheck_2204_ = !lean_is_exclusive(v___x_2129_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2199_ = v___x_2129_;
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_a_2197_);
lean_dec(v___x_2129_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v___x_2202_; 
if (v_isShared_2200_ == 0)
{
v___x_2202_ = v___x_2199_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_a_2197_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
}
}
v___jp_2205_:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; 
lean_inc_ref(v___y_2209_);
v___x_2210_ = l_Lean_stringToMessageData(v___y_2209_);
lean_inc_ref(v___y_2208_);
v___x_2211_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2211_, 0, v___y_2208_);
lean_ctor_set(v___x_2211_, 1, v___x_2210_);
lean_inc_ref(v___y_2207_);
v___x_2212_ = l_Lean_MessageData_ofExpr(v___y_2207_);
v___x_2213_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2213_, 0, v___x_2211_);
lean_ctor_set(v___x_2213_, 1, v___x_2212_);
lean_inc(v___y_2206_);
v___x_2214_ = l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2(v___y_2206_, v___x_2213_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
if (lean_obj_tag(v___x_2214_) == 0)
{
lean_dec_ref_known(v___x_2214_, 1);
v___y_2126_ = v___y_2207_;
goto v___jp_2125_;
}
else
{
lean_object* v_a_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2222_; 
lean_dec_ref(v___y_2207_);
lean_dec_ref(v_target_1986_);
lean_dec(v_goal_1985_);
lean_dec(v_weight_1984_);
v_a_2215_ = lean_ctor_get(v___x_2214_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2214_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2217_ = v___x_2214_;
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_a_2215_);
lean_dec(v___x_2214_);
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
v___jp_2223_:
{
lean_object* v_toCold_2225_; lean_object* v_options_2226_; uint8_t v_hasTrace_2227_; 
v_toCold_2225_ = lean_ctor_get(v___y_1992_, 0);
v_options_2226_ = lean_ctor_get(v_toCold_2225_, 2);
v_hasTrace_2227_ = lean_ctor_get_uint8(v_options_2226_, sizeof(void*)*1);
if (v_hasTrace_2227_ == 0)
{
v___y_2126_ = v_val_2224_;
goto v___jp_2125_;
}
else
{
lean_object* v_inheritedTraceOptions_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; uint8_t v___x_2231_; 
v_inheritedTraceOptions_2228_ = lean_ctor_get(v_toCold_2225_, 11);
v___x_2229_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2_00___x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_));
v___x_2230_ = lean_obj_once(&l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5, &l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5_once, _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5);
v___x_2231_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2228_, v_options_2226_, v___x_2230_);
if (v___x_2231_ == 0)
{
v___y_2126_ = v_val_2224_;
goto v___jp_2125_;
}
else
{
lean_object* v___x_2232_; 
v___x_2232_ = lean_obj_once(&l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__7, &l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__7_once, _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__7);
if (v_symm_1987_ == 0)
{
lean_object* v___x_2233_; 
v___x_2233_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2___closed__1));
v___y_2206_ = v___x_2229_;
v___y_2207_ = v_val_2224_;
v___y_2208_ = v___x_2232_;
v___y_2209_ = v___x_2233_;
goto v___jp_2205_;
}
else
{
lean_object* v___x_2234_; 
v___x_2234_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__8));
v___y_2206_ = v___x_2229_;
v___y_2207_ = v_val_2224_;
v___y_2208_ = v___x_2232_;
v___y_2209_ = v___x_2234_;
goto v___jp_2205_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Rewrites_rwLemma___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_weight_1984_ = stack[0].m_obj;
lean_object* v_goal_1985_ = stack[1].m_obj;
lean_object* v_target_1986_ = stack[2].m_obj;
uint8_t v_symm_1987_ = stack[3].m_num;
uint8_t v_side_1988_ = stack[4].m_num;
lean_object* v_lem_1989_ = stack[5].m_obj;
lean_object* v___y_1990_ = stack[6].m_obj;
lean_object* v___y_1991_ = stack[7].m_obj;
lean_object* v___y_1992_ = stack[8].m_obj;
lean_object* v___y_1993_ = stack[9].m_obj;
lean_object* v_res_2279_;
v_res_2279_ = l_Lean_Meta_Rewrites_rwLemma___lam__0(v_weight_1984_, v_goal_1985_, v_target_1986_, v_symm_1987_, v_side_1988_, v_lem_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
stack->m_obj
 = v_res_2279_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0___boxed(lean_object* v_weight_2280_, lean_object* v_goal_2281_, lean_object* v_target_2282_, lean_object* v_symm_2283_, lean_object* v_side_2284_, lean_object* v_lem_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_){
_start:
{
uint8_t v_symm_boxed_2291_; uint8_t v_side_boxed_2292_; lean_object* v_res_2293_; 
v_symm_boxed_2291_ = lean_unbox(v_symm_2283_);
v_side_boxed_2292_ = lean_unbox(v_side_2284_);
v_res_2293_ = l_Lean_Meta_Rewrites_rwLemma___lam__0(v_weight_2280_, v_goal_2281_, v_target_2282_, v_symm_boxed_2291_, v_side_boxed_2292_, v_lem_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
lean_dec(v___y_2289_);
lean_dec_ref(v___y_2288_);
lean_dec(v___y_2287_);
lean_dec_ref(v___y_2286_);
return v_res_2293_;
}
}
lean_object* l_Lean_Meta_Rewrites_rwLemma(lean_object* v_ctx_2294_, lean_object* v_goal_2295_, lean_object* v_target_2296_, uint8_t v_side_2297_, lean_object* v_lem_2298_, uint8_t v_symm_2299_, lean_object* v_weight_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_){
_start:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___f_2308_; lean_object* v___x_2309_; 
v___x_2306_ = lean_box(v_symm_2299_);
v___x_2307_ = lean_box(v_side_2297_);
v___f_2308_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___boxed), 11, 6);
lean_closure_set(v___f_2308_, 0, v_weight_2300_);
lean_closure_set(v___f_2308_, 1, v_goal_2295_);
lean_closure_set(v___f_2308_, 2, v_target_2296_);
lean_closure_set(v___f_2308_, 3, v___x_2306_);
lean_closure_set(v___f_2308_, 4, v___x_2307_);
lean_closure_set(v___f_2308_, 5, v_lem_2298_);
v___x_2309_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg(v_ctx_2294_, v___f_2308_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_);
return v___x_2309_;
}
}
LEAN_EXPORT void l_Lean_Meta_Rewrites_rwLemma_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_2294_ = stack[0].m_obj;
lean_object* v_goal_2295_ = stack[1].m_obj;
lean_object* v_target_2296_ = stack[2].m_obj;
uint8_t v_side_2297_ = stack[3].m_num;
lean_object* v_lem_2298_ = stack[4].m_obj;
uint8_t v_symm_2299_ = stack[5].m_num;
lean_object* v_weight_2300_ = stack[6].m_obj;
lean_object* v_a_2301_ = stack[7].m_obj;
lean_object* v_a_2302_ = stack[8].m_obj;
lean_object* v_a_2303_ = stack[9].m_obj;
lean_object* v_a_2304_ = stack[10].m_obj;
lean_object* v_res_2310_;
v_res_2310_ = l_Lean_Meta_Rewrites_rwLemma(v_ctx_2294_, v_goal_2295_, v_target_2296_, v_side_2297_, v_lem_2298_, v_symm_2299_, v_weight_2300_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_);
stack->m_obj
 = v_res_2310_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___boxed(lean_object* v_ctx_2311_, lean_object* v_goal_2312_, lean_object* v_target_2313_, lean_object* v_side_2314_, lean_object* v_lem_2315_, lean_object* v_symm_2316_, lean_object* v_weight_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_){
_start:
{
uint8_t v_side_boxed_2323_; uint8_t v_symm_boxed_2324_; lean_object* v_res_2325_; 
v_side_boxed_2323_ = lean_unbox(v_side_2314_);
v_symm_boxed_2324_ = lean_unbox(v_symm_2316_);
v_res_2325_ = l_Lean_Meta_Rewrites_rwLemma(v_ctx_2311_, v_goal_2312_, v_target_2313_, v_side_boxed_2323_, v_lem_2315_, v_symm_boxed_2324_, v_weight_2317_, v_a_2318_, v_a_2319_, v_a_2320_, v_a_2321_);
lean_dec(v_a_2321_);
lean_dec_ref(v_a_2320_);
lean_dec(v_a_2319_);
lean_dec_ref(v_a_2318_);
return v_res_2325_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(lean_object* v_type_2326_, lean_object* v_k_2327_, uint8_t v_cleanupAnnotations_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_){
_start:
{
lean_object* v___f_2334_; uint8_t v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; 
v___f_2334_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2334_, 0, v_k_2327_);
v___x_2335_ = 0;
v___x_2336_ = lean_box(0);
v___x_2337_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_2335_, v___x_2336_, v_type_2326_, v___f_2334_, v_cleanupAnnotations_2328_, v___x_2335_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
if (lean_obj_tag(v___x_2337_) == 0)
{
lean_object* v_a_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2345_; 
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
v_isSharedCheck_2345_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2340_ = v___x_2337_;
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_a_2338_);
lean_dec(v___x_2337_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v___x_2343_; 
if (v_isShared_2341_ == 0)
{
v___x_2343_ = v___x_2340_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v_a_2338_);
v___x_2343_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
return v___x_2343_;
}
}
}
else
{
lean_object* v_a_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2353_; 
v_a_2346_ = lean_ctor_get(v___x_2337_, 0);
v_isSharedCheck_2353_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2348_ = v___x_2337_;
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_a_2346_);
lean_dec(v___x_2337_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v___x_2351_; 
if (v_isShared_2349_ == 0)
{
v___x_2351_ = v___x_2348_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v_a_2346_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
return v___x_2351_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_2326_ = stack[0].m_obj;
lean_object* v_k_2327_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_2328_ = stack[2].m_num;
lean_object* v___y_2329_ = stack[3].m_obj;
lean_object* v___y_2330_ = stack[4].m_obj;
lean_object* v___y_2331_ = stack[5].m_obj;
lean_object* v___y_2332_ = stack[6].m_obj;
lean_object* v_res_2354_;
v_res_2354_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(v_type_2326_, v_k_2327_, v_cleanupAnnotations_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
stack->m_obj
 = v_res_2354_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg___boxed(lean_object* v_type_2355_, lean_object* v_k_2356_, lean_object* v_cleanupAnnotations_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2363_; lean_object* v_res_2364_; 
v_cleanupAnnotations_boxed_2363_ = lean_unbox(v_cleanupAnnotations_2357_);
v_res_2364_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(v_type_2355_, v_k_2356_, v_cleanupAnnotations_boxed_2363_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_);
lean_dec(v___y_2361_);
lean_dec_ref(v___y_2360_);
lean_dec(v___y_2359_);
lean_dec_ref(v___y_2358_);
return v_res_2364_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1(lean_object* v_00_u03b1_2365_, lean_object* v_type_2366_, lean_object* v_k_2367_, uint8_t v_cleanupAnnotations_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_){
_start:
{
lean_object* v___x_2374_; 
v___x_2374_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(v_type_2366_, v_k_2367_, v_cleanupAnnotations_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_);
return v___x_2374_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_2366_ = stack[1].m_obj;
lean_object* v_k_2367_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_2368_ = stack[3].m_num;
lean_object* v___y_2369_ = stack[4].m_obj;
lean_object* v___y_2370_ = stack[5].m_obj;
lean_object* v___y_2371_ = stack[6].m_obj;
lean_object* v___y_2372_ = stack[7].m_obj;
lean_object* v_res_2375_;
v_res_2375_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1(lean_box(0), v_type_2366_, v_k_2367_, v_cleanupAnnotations_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_);
stack->m_obj
 = v_res_2375_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___boxed(lean_object* v_00_u03b1_2376_, lean_object* v_type_2377_, lean_object* v_k_2378_, lean_object* v_cleanupAnnotations_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2385_; lean_object* v_res_2386_; 
v_cleanupAnnotations_boxed_2385_ = lean_unbox(v_cleanupAnnotations_2379_);
v_res_2386_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1(v_00_u03b1_2376_, v_type_2377_, v_k_2378_, v_cleanupAnnotations_boxed_2385_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_);
lean_dec(v___y_2383_);
lean_dec_ref(v___y_2382_);
lean_dec(v___y_2381_);
lean_dec_ref(v___y_2380_);
return v_res_2386_;
}
}
lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(lean_object* v_e_2387_, lean_object* v_k_2388_, uint8_t v_cleanupAnnotations_2389_, uint8_t v_preserveNondepLet_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_){
_start:
{
lean_object* v___f_2396_; uint8_t v___x_2397_; uint8_t v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; 
v___f_2396_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2396_, 0, v_k_2388_);
v___x_2397_ = 1;
v___x_2398_ = 0;
v___x_2399_ = lean_box(0);
v___x_2400_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2387_, v___x_2397_, v___x_2397_, v_preserveNondepLet_2390_, v___x_2398_, v___x_2399_, v___f_2396_, v_cleanupAnnotations_2389_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_);
if (lean_obj_tag(v___x_2400_) == 0)
{
lean_object* v_a_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2408_; 
v_a_2401_ = lean_ctor_get(v___x_2400_, 0);
v_isSharedCheck_2408_ = !lean_is_exclusive(v___x_2400_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2403_ = v___x_2400_;
v_isShared_2404_ = v_isSharedCheck_2408_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_a_2401_);
lean_dec(v___x_2400_);
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
v_reuseFailAlloc_2407_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2416_; 
v_a_2409_ = lean_ctor_get(v___x_2400_, 0);
v_isSharedCheck_2416_ = !lean_is_exclusive(v___x_2400_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2411_ = v___x_2400_;
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_a_2409_);
lean_dec(v___x_2400_);
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
}
LEAN_EXPORT void l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2387_ = stack[0].m_obj;
lean_object* v_k_2388_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_2389_ = stack[2].m_num;
uint8_t v_preserveNondepLet_2390_ = stack[3].m_num;
lean_object* v___y_2391_ = stack[4].m_obj;
lean_object* v___y_2392_ = stack[5].m_obj;
lean_object* v___y_2393_ = stack[6].m_obj;
lean_object* v___y_2394_ = stack[7].m_obj;
lean_object* v_res_2417_;
v_res_2417_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(v_e_2387_, v_k_2388_, v_cleanupAnnotations_2389_, v_preserveNondepLet_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_);
stack->m_obj
 = v_res_2417_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg___boxed(lean_object* v_e_2418_, lean_object* v_k_2419_, lean_object* v_cleanupAnnotations_2420_, lean_object* v_preserveNondepLet_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2427_; uint8_t v_preserveNondepLet_boxed_2428_; lean_object* v_res_2429_; 
v_cleanupAnnotations_boxed_2427_ = lean_unbox(v_cleanupAnnotations_2420_);
v_preserveNondepLet_boxed_2428_ = lean_unbox(v_preserveNondepLet_2421_);
v_res_2429_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(v_e_2418_, v_k_2419_, v_cleanupAnnotations_boxed_2427_, v_preserveNondepLet_boxed_2428_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
lean_dec(v___y_2425_);
lean_dec_ref(v___y_2424_);
lean_dec(v___y_2423_);
lean_dec_ref(v___y_2422_);
return v_res_2429_;
}
}
lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2(lean_object* v_00_u03b1_2430_, lean_object* v_e_2431_, lean_object* v_k_2432_, uint8_t v_cleanupAnnotations_2433_, uint8_t v_preserveNondepLet_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_){
_start:
{
lean_object* v___x_2440_; 
v___x_2440_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(v_e_2431_, v_k_2432_, v_cleanupAnnotations_2433_, v_preserveNondepLet_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_);
return v___x_2440_;
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2431_ = stack[1].m_obj;
lean_object* v_k_2432_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_2433_ = stack[3].m_num;
uint8_t v_preserveNondepLet_2434_ = stack[4].m_num;
lean_object* v___y_2435_ = stack[5].m_obj;
lean_object* v___y_2436_ = stack[6].m_obj;
lean_object* v___y_2437_ = stack[7].m_obj;
lean_object* v___y_2438_ = stack[8].m_obj;
lean_object* v_res_2441_;
v_res_2441_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2(lean_box(0), v_e_2431_, v_k_2432_, v_cleanupAnnotations_2433_, v_preserveNondepLet_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_);
stack->m_obj
 = v_res_2441_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___boxed(lean_object* v_00_u03b1_2442_, lean_object* v_e_2443_, lean_object* v_k_2444_, lean_object* v_cleanupAnnotations_2445_, lean_object* v_preserveNondepLet_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2452_; uint8_t v_preserveNondepLet_boxed_2453_; lean_object* v_res_2454_; 
v_cleanupAnnotations_boxed_2452_ = lean_unbox(v_cleanupAnnotations_2445_);
v_preserveNondepLet_boxed_2453_ = lean_unbox(v_preserveNondepLet_2446_);
v_res_2454_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2(v_00_u03b1_2442_, v_e_2443_, v_k_2444_, v_cleanupAnnotations_boxed_2452_, v_preserveNondepLet_boxed_2453_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_);
lean_dec(v___y_2450_);
lean_dec_ref(v___y_2449_);
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
return v_res_2454_;
}
}
lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(lean_object* v_f_2455_, lean_object* v_e_x27_2456_, lean_object* v_a_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_){
_start:
{
lean_object* v___x_2463_; 
lean_inc(v___y_2461_);
lean_inc_ref(v___y_2460_);
lean_inc(v___y_2459_);
lean_inc_ref(v___y_2458_);
lean_inc_ref(v_e_x27_2456_);
v___x_2463_ = lean_apply_7(v_f_2455_, v_a_2457_, v_e_x27_2456_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_, lean_box(0));
if (lean_obj_tag(v___x_2463_) == 0)
{
lean_object* v_a_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2472_; 
v_a_2464_ = lean_ctor_get(v___x_2463_, 0);
v_isSharedCheck_2472_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2472_ == 0)
{
v___x_2466_ = v___x_2463_;
v_isShared_2467_ = v_isSharedCheck_2472_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_a_2464_);
lean_dec(v___x_2463_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2472_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___x_2468_; lean_object* v___x_2470_; 
v___x_2468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2468_, 0, v_e_x27_2456_);
lean_ctor_set(v___x_2468_, 1, v_a_2464_);
if (v_isShared_2467_ == 0)
{
lean_ctor_set(v___x_2466_, 0, v___x_2468_);
v___x_2470_ = v___x_2466_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v___x_2468_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
}
else
{
lean_object* v_a_2473_; lean_object* v___x_2475_; uint8_t v_isShared_2476_; uint8_t v_isSharedCheck_2480_; 
lean_dec_ref(v_e_x27_2456_);
v_a_2473_ = lean_ctor_get(v___x_2463_, 0);
v_isSharedCheck_2480_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2475_ = v___x_2463_;
v_isShared_2476_ = v_isSharedCheck_2480_;
goto v_resetjp_2474_;
}
else
{
lean_inc(v_a_2473_);
lean_dec(v___x_2463_);
v___x_2475_ = lean_box(0);
v_isShared_2476_ = v_isSharedCheck_2480_;
goto v_resetjp_2474_;
}
v_resetjp_2474_:
{
lean_object* v___x_2478_; 
if (v_isShared_2476_ == 0)
{
v___x_2478_ = v___x_2475_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v_a_2473_);
v___x_2478_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
return v___x_2478_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2455_ = stack[0].m_obj;
lean_object* v_e_x27_2456_ = stack[1].m_obj;
lean_object* v_a_2457_ = stack[2].m_obj;
lean_object* v___y_2458_ = stack[3].m_obj;
lean_object* v___y_2459_ = stack[4].m_obj;
lean_object* v___y_2460_ = stack[5].m_obj;
lean_object* v___y_2461_ = stack[6].m_obj;
lean_object* v_res_2481_;
v_res_2481_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2455_, v_e_x27_2456_, v_a_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_);
stack->m_obj
 = v_res_2481_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0___boxed(lean_object* v_f_2482_, lean_object* v_e_x27_2483_, lean_object* v_a_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_){
_start:
{
lean_object* v_res_2490_; 
v_res_2490_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2482_, v_e_x27_2483_, v_a_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_);
lean_dec(v___y_2488_);
lean_dec_ref(v___y_2487_);
lean_dec(v___y_2486_);
lean_dec_ref(v___y_2485_);
return v_res_2490_;
}
}
lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg(lean_object* v_f_2491_, lean_object* v_x_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_){
_start:
{
switch(lean_obj_tag(v_x_2492_))
{
case 7:
{
lean_object* v_binderName_2499_; lean_object* v_binderType_2500_; lean_object* v_body_2501_; uint8_t v_binderInfo_2502_; lean_object* v___x_2503_; 
v_binderName_2499_ = lean_ctor_get(v_x_2492_, 0);
v_binderType_2500_ = lean_ctor_get(v_x_2492_, 1);
v_body_2501_ = lean_ctor_get(v_x_2492_, 2);
v_binderInfo_2502_ = lean_ctor_get_uint8(v_x_2492_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2500_);
lean_inc_ref(v_f_2491_);
v___x_2503_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2491_, v_binderType_2500_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_);
if (lean_obj_tag(v___x_2503_) == 0)
{
lean_object* v_a_2504_; lean_object* v_fst_2505_; lean_object* v_snd_2506_; lean_object* v___x_2507_; 
v_a_2504_ = lean_ctor_get(v___x_2503_, 0);
lean_inc(v_a_2504_);
lean_dec_ref_known(v___x_2503_, 1);
v_fst_2505_ = lean_ctor_get(v_a_2504_, 0);
lean_inc(v_fst_2505_);
v_snd_2506_ = lean_ctor_get(v_a_2504_, 1);
lean_inc(v_snd_2506_);
lean_dec(v_a_2504_);
lean_inc_ref(v_body_2501_);
v___x_2507_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2491_, v_body_2501_, v_snd_2506_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_);
if (lean_obj_tag(v___x_2507_) == 0)
{
lean_object* v_a_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2536_; 
v_a_2508_ = lean_ctor_get(v___x_2507_, 0);
v_isSharedCheck_2536_ = !lean_is_exclusive(v___x_2507_);
if (v_isSharedCheck_2536_ == 0)
{
v___x_2510_ = v___x_2507_;
v_isShared_2511_ = v_isSharedCheck_2536_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_a_2508_);
lean_dec(v___x_2507_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2536_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v_fst_2512_; lean_object* v_snd_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2535_; 
v_fst_2512_ = lean_ctor_get(v_a_2508_, 0);
v_snd_2513_ = lean_ctor_get(v_a_2508_, 1);
v_isSharedCheck_2535_ = !lean_is_exclusive(v_a_2508_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2515_ = v_a_2508_;
v_isShared_2516_ = v_isSharedCheck_2535_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_snd_2513_);
lean_inc(v_fst_2512_);
lean_dec(v_a_2508_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2535_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v___y_2518_; size_t v___x_2525_; size_t v___x_2526_; uint8_t v___x_2527_; 
v___x_2525_ = lean_ptr_addr(v_binderType_2500_);
v___x_2526_ = lean_ptr_addr(v_fst_2505_);
v___x_2527_ = lean_usize_dec_eq(v___x_2525_, v___x_2526_);
if (v___x_2527_ == 0)
{
lean_object* v___x_2528_; 
lean_inc(v_binderName_2499_);
lean_dec_ref_known(v_x_2492_, 3);
v___x_2528_ = l_Lean_Expr_forallE___override(v_binderName_2499_, v_fst_2505_, v_fst_2512_, v_binderInfo_2502_);
v___y_2518_ = v___x_2528_;
goto v___jp_2517_;
}
else
{
size_t v___x_2529_; size_t v___x_2530_; uint8_t v___x_2531_; 
v___x_2529_ = lean_ptr_addr(v_body_2501_);
v___x_2530_ = lean_ptr_addr(v_fst_2512_);
v___x_2531_ = lean_usize_dec_eq(v___x_2529_, v___x_2530_);
if (v___x_2531_ == 0)
{
lean_object* v___x_2532_; 
lean_inc(v_binderName_2499_);
lean_dec_ref_known(v_x_2492_, 3);
v___x_2532_ = l_Lean_Expr_forallE___override(v_binderName_2499_, v_fst_2505_, v_fst_2512_, v_binderInfo_2502_);
v___y_2518_ = v___x_2532_;
goto v___jp_2517_;
}
else
{
uint8_t v___x_2533_; 
v___x_2533_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2502_, v_binderInfo_2502_);
if (v___x_2533_ == 0)
{
lean_object* v___x_2534_; 
lean_inc(v_binderName_2499_);
lean_dec_ref_known(v_x_2492_, 3);
v___x_2534_ = l_Lean_Expr_forallE___override(v_binderName_2499_, v_fst_2505_, v_fst_2512_, v_binderInfo_2502_);
v___y_2518_ = v___x_2534_;
goto v___jp_2517_;
}
else
{
lean_dec(v_fst_2512_);
lean_dec(v_fst_2505_);
v___y_2518_ = v_x_2492_;
goto v___jp_2517_;
}
}
}
v___jp_2517_:
{
lean_object* v___x_2520_; 
if (v_isShared_2516_ == 0)
{
lean_ctor_set(v___x_2515_, 0, v___y_2518_);
v___x_2520_ = v___x_2515_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v___y_2518_);
lean_ctor_set(v_reuseFailAlloc_2524_, 1, v_snd_2513_);
v___x_2520_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
lean_object* v___x_2522_; 
if (v_isShared_2511_ == 0)
{
lean_ctor_set(v___x_2510_, 0, v___x_2520_);
v___x_2522_ = v___x_2510_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v___x_2520_);
v___x_2522_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
return v___x_2522_;
}
}
}
}
}
}
else
{
lean_dec(v_fst_2505_);
lean_dec_ref_known(v_x_2492_, 3);
return v___x_2507_;
}
}
else
{
lean_dec_ref_known(v_x_2492_, 3);
lean_dec_ref(v_f_2491_);
return v___x_2503_;
}
}
case 6:
{
lean_object* v_binderName_2537_; lean_object* v_binderType_2538_; lean_object* v_body_2539_; uint8_t v_binderInfo_2540_; lean_object* v___x_2541_; 
v_binderName_2537_ = lean_ctor_get(v_x_2492_, 0);
v_binderType_2538_ = lean_ctor_get(v_x_2492_, 1);
v_body_2539_ = lean_ctor_get(v_x_2492_, 2);
v_binderInfo_2540_ = lean_ctor_get_uint8(v_x_2492_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2538_);
lean_inc_ref(v_f_2491_);
v___x_2541_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2491_, v_binderType_2538_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_);
if (lean_obj_tag(v___x_2541_) == 0)
{
lean_object* v_a_2542_; lean_object* v_fst_2543_; lean_object* v_snd_2544_; lean_object* v___x_2545_; 
v_a_2542_ = lean_ctor_get(v___x_2541_, 0);
lean_inc(v_a_2542_);
lean_dec_ref_known(v___x_2541_, 1);
v_fst_2543_ = lean_ctor_get(v_a_2542_, 0);
lean_inc(v_fst_2543_);
v_snd_2544_ = lean_ctor_get(v_a_2542_, 1);
lean_inc(v_snd_2544_);
lean_dec(v_a_2542_);
lean_inc_ref(v_body_2539_);
v___x_2545_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2491_, v_body_2539_, v_snd_2544_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_);
if (lean_obj_tag(v___x_2545_) == 0)
{
lean_object* v_a_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2574_; 
v_a_2546_ = lean_ctor_get(v___x_2545_, 0);
v_isSharedCheck_2574_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2574_ == 0)
{
v___x_2548_ = v___x_2545_;
v_isShared_2549_ = v_isSharedCheck_2574_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_a_2546_);
lean_dec(v___x_2545_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2574_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
lean_object* v_fst_2550_; lean_object* v_snd_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2573_; 
v_fst_2550_ = lean_ctor_get(v_a_2546_, 0);
v_snd_2551_ = lean_ctor_get(v_a_2546_, 1);
v_isSharedCheck_2573_ = !lean_is_exclusive(v_a_2546_);
if (v_isSharedCheck_2573_ == 0)
{
v___x_2553_ = v_a_2546_;
v_isShared_2554_ = v_isSharedCheck_2573_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_snd_2551_);
lean_inc(v_fst_2550_);
lean_dec(v_a_2546_);
v___x_2553_ = lean_box(0);
v_isShared_2554_ = v_isSharedCheck_2573_;
goto v_resetjp_2552_;
}
v_resetjp_2552_:
{
lean_object* v___y_2556_; size_t v___x_2563_; size_t v___x_2564_; uint8_t v___x_2565_; 
v___x_2563_ = lean_ptr_addr(v_binderType_2538_);
v___x_2564_ = lean_ptr_addr(v_fst_2543_);
v___x_2565_ = lean_usize_dec_eq(v___x_2563_, v___x_2564_);
if (v___x_2565_ == 0)
{
lean_object* v___x_2566_; 
lean_inc(v_binderName_2537_);
lean_dec_ref_known(v_x_2492_, 3);
v___x_2566_ = l_Lean_Expr_lam___override(v_binderName_2537_, v_fst_2543_, v_fst_2550_, v_binderInfo_2540_);
v___y_2556_ = v___x_2566_;
goto v___jp_2555_;
}
else
{
size_t v___x_2567_; size_t v___x_2568_; uint8_t v___x_2569_; 
v___x_2567_ = lean_ptr_addr(v_body_2539_);
v___x_2568_ = lean_ptr_addr(v_fst_2550_);
v___x_2569_ = lean_usize_dec_eq(v___x_2567_, v___x_2568_);
if (v___x_2569_ == 0)
{
lean_object* v___x_2570_; 
lean_inc(v_binderName_2537_);
lean_dec_ref_known(v_x_2492_, 3);
v___x_2570_ = l_Lean_Expr_lam___override(v_binderName_2537_, v_fst_2543_, v_fst_2550_, v_binderInfo_2540_);
v___y_2556_ = v___x_2570_;
goto v___jp_2555_;
}
else
{
uint8_t v___x_2571_; 
v___x_2571_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_2540_, v_binderInfo_2540_);
if (v___x_2571_ == 0)
{
lean_object* v___x_2572_; 
lean_inc(v_binderName_2537_);
lean_dec_ref_known(v_x_2492_, 3);
v___x_2572_ = l_Lean_Expr_lam___override(v_binderName_2537_, v_fst_2543_, v_fst_2550_, v_binderInfo_2540_);
v___y_2556_ = v___x_2572_;
goto v___jp_2555_;
}
else
{
lean_dec(v_fst_2550_);
lean_dec(v_fst_2543_);
v___y_2556_ = v_x_2492_;
goto v___jp_2555_;
}
}
}
v___jp_2555_:
{
lean_object* v___x_2558_; 
if (v_isShared_2554_ == 0)
{
lean_ctor_set(v___x_2553_, 0, v___y_2556_);
v___x_2558_ = v___x_2553_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v___y_2556_);
lean_ctor_set(v_reuseFailAlloc_2562_, 1, v_snd_2551_);
v___x_2558_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
lean_object* v___x_2560_; 
if (v_isShared_2549_ == 0)
{
lean_ctor_set(v___x_2548_, 0, v___x_2558_);
v___x_2560_ = v___x_2548_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v___x_2558_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
}
}
}
else
{
lean_dec(v_fst_2543_);
lean_dec_ref_known(v_x_2492_, 3);
return v___x_2545_;
}
}
else
{
lean_dec_ref_known(v_x_2492_, 3);
lean_dec_ref(v_f_2491_);
return v___x_2541_;
}
}
case 10:
{
lean_object* v_data_2575_; lean_object* v_expr_2576_; lean_object* v___x_2577_; 
v_data_2575_ = lean_ctor_get(v_x_2492_, 0);
v_expr_2576_ = lean_ctor_get(v_x_2492_, 1);
lean_inc_ref(v_expr_2576_);
v___x_2577_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2491_, v_expr_2576_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_);
if (lean_obj_tag(v___x_2577_) == 0)
{
lean_object* v_a_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2600_; 
v_a_2578_ = lean_ctor_get(v___x_2577_, 0);
v_isSharedCheck_2600_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2600_ == 0)
{
v___x_2580_ = v___x_2577_;
v_isShared_2581_ = v_isSharedCheck_2600_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_a_2578_);
lean_dec(v___x_2577_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2600_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v_fst_2582_; lean_object* v_snd_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2599_; 
v_fst_2582_ = lean_ctor_get(v_a_2578_, 0);
v_snd_2583_ = lean_ctor_get(v_a_2578_, 1);
v_isSharedCheck_2599_ = !lean_is_exclusive(v_a_2578_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2585_ = v_a_2578_;
v_isShared_2586_ = v_isSharedCheck_2599_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_snd_2583_);
lean_inc(v_fst_2582_);
lean_dec(v_a_2578_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2599_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___y_2588_; size_t v___x_2595_; size_t v___x_2596_; uint8_t v___x_2597_; 
v___x_2595_ = lean_ptr_addr(v_expr_2576_);
v___x_2596_ = lean_ptr_addr(v_fst_2582_);
v___x_2597_ = lean_usize_dec_eq(v___x_2595_, v___x_2596_);
if (v___x_2597_ == 0)
{
lean_object* v___x_2598_; 
lean_inc(v_data_2575_);
lean_dec_ref_known(v_x_2492_, 2);
v___x_2598_ = l_Lean_Expr_mdata___override(v_data_2575_, v_fst_2582_);
v___y_2588_ = v___x_2598_;
goto v___jp_2587_;
}
else
{
lean_dec(v_fst_2582_);
v___y_2588_ = v_x_2492_;
goto v___jp_2587_;
}
v___jp_2587_:
{
lean_object* v___x_2590_; 
if (v_isShared_2586_ == 0)
{
lean_ctor_set(v___x_2585_, 0, v___y_2588_);
v___x_2590_ = v___x_2585_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v___y_2588_);
lean_ctor_set(v_reuseFailAlloc_2594_, 1, v_snd_2583_);
v___x_2590_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
lean_object* v___x_2592_; 
if (v_isShared_2581_ == 0)
{
lean_ctor_set(v___x_2580_, 0, v___x_2590_);
v___x_2592_ = v___x_2580_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v___x_2590_);
v___x_2592_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2591_;
}
v_reusejp_2591_:
{
return v___x_2592_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_x_2492_, 2);
return v___x_2577_;
}
}
case 8:
{
lean_object* v_declName_2601_; lean_object* v_type_2602_; lean_object* v_value_2603_; lean_object* v_body_2604_; uint8_t v_nondep_2605_; lean_object* v___x_2606_; 
v_declName_2601_ = lean_ctor_get(v_x_2492_, 0);
v_type_2602_ = lean_ctor_get(v_x_2492_, 1);
v_value_2603_ = lean_ctor_get(v_x_2492_, 2);
v_body_2604_ = lean_ctor_get(v_x_2492_, 3);
v_nondep_2605_ = lean_ctor_get_uint8(v_x_2492_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_2602_);
lean_inc_ref(v_f_2491_);
v___x_2606_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2491_, v_type_2602_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_);
if (lean_obj_tag(v___x_2606_) == 0)
{
lean_object* v_a_2607_; lean_object* v_fst_2608_; lean_object* v_snd_2609_; lean_object* v___x_2610_; 
v_a_2607_ = lean_ctor_get(v___x_2606_, 0);
lean_inc(v_a_2607_);
lean_dec_ref_known(v___x_2606_, 1);
v_fst_2608_ = lean_ctor_get(v_a_2607_, 0);
lean_inc(v_fst_2608_);
v_snd_2609_ = lean_ctor_get(v_a_2607_, 1);
lean_inc(v_snd_2609_);
lean_dec(v_a_2607_);
lean_inc_ref(v_value_2603_);
lean_inc_ref(v_f_2491_);
v___x_2610_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2491_, v_value_2603_, v_snd_2609_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_);
if (lean_obj_tag(v___x_2610_) == 0)
{
lean_object* v_a_2611_; lean_object* v_fst_2612_; lean_object* v_snd_2613_; lean_object* v___x_2614_; 
v_a_2611_ = lean_ctor_get(v___x_2610_, 0);
lean_inc(v_a_2611_);
lean_dec_ref_known(v___x_2610_, 1);
v_fst_2612_ = lean_ctor_get(v_a_2611_, 0);
lean_inc(v_fst_2612_);
v_snd_2613_ = lean_ctor_get(v_a_2611_, 1);
lean_inc(v_snd_2613_);
lean_dec(v_a_2611_);
lean_inc_ref(v_body_2604_);
v___x_2614_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2491_, v_body_2604_, v_snd_2613_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_);
if (lean_obj_tag(v___x_2614_) == 0)
{
lean_object* v_a_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2645_; 
v_a_2615_ = lean_ctor_get(v___x_2614_, 0);
v_isSharedCheck_2645_ = !lean_is_exclusive(v___x_2614_);
if (v_isSharedCheck_2645_ == 0)
{
v___x_2617_ = v___x_2614_;
v_isShared_2618_ = v_isSharedCheck_2645_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_a_2615_);
lean_dec(v___x_2614_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2645_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v_fst_2619_; lean_object* v_snd_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2644_; 
v_fst_2619_ = lean_ctor_get(v_a_2615_, 0);
v_snd_2620_ = lean_ctor_get(v_a_2615_, 1);
v_isSharedCheck_2644_ = !lean_is_exclusive(v_a_2615_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2622_ = v_a_2615_;
v_isShared_2623_ = v_isSharedCheck_2644_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_snd_2620_);
lean_inc(v_fst_2619_);
lean_dec(v_a_2615_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2644_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___y_2625_; size_t v___x_2632_; size_t v___x_2633_; uint8_t v___x_2634_; 
v___x_2632_ = lean_ptr_addr(v_type_2602_);
v___x_2633_ = lean_ptr_addr(v_fst_2608_);
v___x_2634_ = lean_usize_dec_eq(v___x_2632_, v___x_2633_);
if (v___x_2634_ == 0)
{
lean_object* v___x_2635_; 
lean_inc(v_declName_2601_);
lean_dec_ref_known(v_x_2492_, 4);
v___x_2635_ = l_Lean_Expr_letE___override(v_declName_2601_, v_fst_2608_, v_fst_2612_, v_fst_2619_, v_nondep_2605_);
v___y_2625_ = v___x_2635_;
goto v___jp_2624_;
}
else
{
size_t v___x_2636_; size_t v___x_2637_; uint8_t v___x_2638_; 
v___x_2636_ = lean_ptr_addr(v_value_2603_);
v___x_2637_ = lean_ptr_addr(v_fst_2612_);
v___x_2638_ = lean_usize_dec_eq(v___x_2636_, v___x_2637_);
if (v___x_2638_ == 0)
{
lean_object* v___x_2639_; 
lean_inc(v_declName_2601_);
lean_dec_ref_known(v_x_2492_, 4);
v___x_2639_ = l_Lean_Expr_letE___override(v_declName_2601_, v_fst_2608_, v_fst_2612_, v_fst_2619_, v_nondep_2605_);
v___y_2625_ = v___x_2639_;
goto v___jp_2624_;
}
else
{
size_t v___x_2640_; size_t v___x_2641_; uint8_t v___x_2642_; 
v___x_2640_ = lean_ptr_addr(v_body_2604_);
v___x_2641_ = lean_ptr_addr(v_fst_2619_);
v___x_2642_ = lean_usize_dec_eq(v___x_2640_, v___x_2641_);
if (v___x_2642_ == 0)
{
lean_object* v___x_2643_; 
lean_inc(v_declName_2601_);
lean_dec_ref_known(v_x_2492_, 4);
v___x_2643_ = l_Lean_Expr_letE___override(v_declName_2601_, v_fst_2608_, v_fst_2612_, v_fst_2619_, v_nondep_2605_);
v___y_2625_ = v___x_2643_;
goto v___jp_2624_;
}
else
{
lean_dec(v_fst_2619_);
lean_dec(v_fst_2612_);
lean_dec(v_fst_2608_);
v___y_2625_ = v_x_2492_;
goto v___jp_2624_;
}
}
}
v___jp_2624_:
{
lean_object* v___x_2627_; 
if (v_isShared_2623_ == 0)
{
lean_ctor_set(v___x_2622_, 0, v___y_2625_);
v___x_2627_ = v___x_2622_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v___y_2625_);
lean_ctor_set(v_reuseFailAlloc_2631_, 1, v_snd_2620_);
v___x_2627_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
lean_object* v___x_2629_; 
if (v_isShared_2618_ == 0)
{
lean_ctor_set(v___x_2617_, 0, v___x_2627_);
v___x_2629_ = v___x_2617_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v___x_2627_);
v___x_2629_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
return v___x_2629_;
}
}
}
}
}
}
else
{
lean_dec(v_fst_2612_);
lean_dec(v_fst_2608_);
lean_dec_ref_known(v_x_2492_, 4);
return v___x_2614_;
}
}
else
{
lean_dec(v_fst_2608_);
lean_dec_ref_known(v_x_2492_, 4);
lean_dec_ref(v_f_2491_);
return v___x_2610_;
}
}
else
{
lean_dec_ref_known(v_x_2492_, 4);
lean_dec_ref(v_f_2491_);
return v___x_2606_;
}
}
case 5:
{
lean_object* v_fn_2646_; lean_object* v_arg_2647_; lean_object* v___x_2648_; 
v_fn_2646_ = lean_ctor_get(v_x_2492_, 0);
v_arg_2647_ = lean_ctor_get(v_x_2492_, 1);
lean_inc_ref(v_fn_2646_);
lean_inc_ref(v_f_2491_);
v___x_2648_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2491_, v_fn_2646_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_);
if (lean_obj_tag(v___x_2648_) == 0)
{
lean_object* v_a_2649_; lean_object* v_fst_2650_; lean_object* v_snd_2651_; lean_object* v___x_2652_; 
v_a_2649_ = lean_ctor_get(v___x_2648_, 0);
lean_inc(v_a_2649_);
lean_dec_ref_known(v___x_2648_, 1);
v_fst_2650_ = lean_ctor_get(v_a_2649_, 0);
lean_inc(v_fst_2650_);
v_snd_2651_ = lean_ctor_get(v_a_2649_, 1);
lean_inc(v_snd_2651_);
lean_dec(v_a_2649_);
lean_inc_ref(v_arg_2647_);
v___x_2652_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2491_, v_arg_2647_, v_snd_2651_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_);
if (lean_obj_tag(v___x_2652_) == 0)
{
lean_object* v_a_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2679_; 
v_a_2653_ = lean_ctor_get(v___x_2652_, 0);
v_isSharedCheck_2679_ = !lean_is_exclusive(v___x_2652_);
if (v_isSharedCheck_2679_ == 0)
{
v___x_2655_ = v___x_2652_;
v_isShared_2656_ = v_isSharedCheck_2679_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_a_2653_);
lean_dec(v___x_2652_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2679_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v_fst_2657_; lean_object* v_snd_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2678_; 
v_fst_2657_ = lean_ctor_get(v_a_2653_, 0);
v_snd_2658_ = lean_ctor_get(v_a_2653_, 1);
v_isSharedCheck_2678_ = !lean_is_exclusive(v_a_2653_);
if (v_isSharedCheck_2678_ == 0)
{
v___x_2660_ = v_a_2653_;
v_isShared_2661_ = v_isSharedCheck_2678_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_snd_2658_);
lean_inc(v_fst_2657_);
lean_dec(v_a_2653_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2678_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v___y_2663_; size_t v___x_2670_; size_t v___x_2671_; uint8_t v___x_2672_; 
v___x_2670_ = lean_ptr_addr(v_fn_2646_);
v___x_2671_ = lean_ptr_addr(v_fst_2650_);
v___x_2672_ = lean_usize_dec_eq(v___x_2670_, v___x_2671_);
if (v___x_2672_ == 0)
{
lean_object* v___x_2673_; 
lean_dec_ref_known(v_x_2492_, 2);
v___x_2673_ = l_Lean_Expr_app___override(v_fst_2650_, v_fst_2657_);
v___y_2663_ = v___x_2673_;
goto v___jp_2662_;
}
else
{
size_t v___x_2674_; size_t v___x_2675_; uint8_t v___x_2676_; 
v___x_2674_ = lean_ptr_addr(v_arg_2647_);
v___x_2675_ = lean_ptr_addr(v_fst_2657_);
v___x_2676_ = lean_usize_dec_eq(v___x_2674_, v___x_2675_);
if (v___x_2676_ == 0)
{
lean_object* v___x_2677_; 
lean_dec_ref_known(v_x_2492_, 2);
v___x_2677_ = l_Lean_Expr_app___override(v_fst_2650_, v_fst_2657_);
v___y_2663_ = v___x_2677_;
goto v___jp_2662_;
}
else
{
lean_dec(v_fst_2657_);
lean_dec(v_fst_2650_);
v___y_2663_ = v_x_2492_;
goto v___jp_2662_;
}
}
v___jp_2662_:
{
lean_object* v___x_2665_; 
if (v_isShared_2661_ == 0)
{
lean_ctor_set(v___x_2660_, 0, v___y_2663_);
v___x_2665_ = v___x_2660_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v___y_2663_);
lean_ctor_set(v_reuseFailAlloc_2669_, 1, v_snd_2658_);
v___x_2665_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
lean_object* v___x_2667_; 
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 0, v___x_2665_);
v___x_2667_ = v___x_2655_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v___x_2665_);
v___x_2667_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
return v___x_2667_;
}
}
}
}
}
}
else
{
lean_dec(v_fst_2650_);
lean_dec_ref_known(v_x_2492_, 2);
return v___x_2652_;
}
}
else
{
lean_dec_ref_known(v_x_2492_, 2);
lean_dec_ref(v_f_2491_);
return v___x_2648_;
}
}
case 11:
{
lean_object* v_typeName_2680_; lean_object* v_idx_2681_; lean_object* v_struct_2682_; lean_object* v___x_2683_; 
v_typeName_2680_ = lean_ctor_get(v_x_2492_, 0);
v_idx_2681_ = lean_ctor_get(v_x_2492_, 1);
v_struct_2682_ = lean_ctor_get(v_x_2492_, 2);
lean_inc_ref(v_struct_2682_);
v___x_2683_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(v_f_2491_, v_struct_2682_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_);
if (lean_obj_tag(v___x_2683_) == 0)
{
lean_object* v_a_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2706_; 
v_a_2684_ = lean_ctor_get(v___x_2683_, 0);
v_isSharedCheck_2706_ = !lean_is_exclusive(v___x_2683_);
if (v_isSharedCheck_2706_ == 0)
{
v___x_2686_ = v___x_2683_;
v_isShared_2687_ = v_isSharedCheck_2706_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_a_2684_);
lean_dec(v___x_2683_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2706_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v_fst_2688_; lean_object* v_snd_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2705_; 
v_fst_2688_ = lean_ctor_get(v_a_2684_, 0);
v_snd_2689_ = lean_ctor_get(v_a_2684_, 1);
v_isSharedCheck_2705_ = !lean_is_exclusive(v_a_2684_);
if (v_isSharedCheck_2705_ == 0)
{
v___x_2691_ = v_a_2684_;
v_isShared_2692_ = v_isSharedCheck_2705_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_snd_2689_);
lean_inc(v_fst_2688_);
lean_dec(v_a_2684_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2705_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
lean_object* v___y_2694_; size_t v___x_2701_; size_t v___x_2702_; uint8_t v___x_2703_; 
v___x_2701_ = lean_ptr_addr(v_struct_2682_);
v___x_2702_ = lean_ptr_addr(v_fst_2688_);
v___x_2703_ = lean_usize_dec_eq(v___x_2701_, v___x_2702_);
if (v___x_2703_ == 0)
{
lean_object* v___x_2704_; 
lean_inc(v_idx_2681_);
lean_inc(v_typeName_2680_);
lean_dec_ref_known(v_x_2492_, 3);
v___x_2704_ = l_Lean_Expr_proj___override(v_typeName_2680_, v_idx_2681_, v_fst_2688_);
v___y_2694_ = v___x_2704_;
goto v___jp_2693_;
}
else
{
lean_dec(v_fst_2688_);
v___y_2694_ = v_x_2492_;
goto v___jp_2693_;
}
v___jp_2693_:
{
lean_object* v___x_2696_; 
if (v_isShared_2692_ == 0)
{
lean_ctor_set(v___x_2691_, 0, v___y_2694_);
v___x_2696_ = v___x_2691_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v___y_2694_);
lean_ctor_set(v_reuseFailAlloc_2700_, 1, v_snd_2689_);
v___x_2696_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
lean_object* v___x_2698_; 
if (v_isShared_2687_ == 0)
{
lean_ctor_set(v___x_2686_, 0, v___x_2696_);
v___x_2698_ = v___x_2686_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v___x_2696_);
v___x_2698_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
return v___x_2698_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_x_2492_, 3);
return v___x_2683_;
}
}
default: 
{
lean_object* v___x_2707_; lean_object* v___x_2708_; 
lean_dec_ref(v_f_2491_);
v___x_2707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2707_, 0, v_x_2492_);
lean_ctor_set(v___x_2707_, 1, v___y_2493_);
v___x_2708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2707_);
return v___x_2708_;
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2491_ = stack[0].m_obj;
lean_object* v_x_2492_ = stack[1].m_obj;
lean_object* v___y_2493_ = stack[2].m_obj;
lean_object* v___y_2494_ = stack[3].m_obj;
lean_object* v___y_2495_ = stack[4].m_obj;
lean_object* v___y_2496_ = stack[5].m_obj;
lean_object* v___y_2497_ = stack[6].m_obj;
lean_object* v_res_2709_;
v_res_2709_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg(v_f_2491_, v_x_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_);
stack->m_obj
 = v_res_2709_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___boxed(lean_object* v_f_2710_, lean_object* v_x_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_){
_start:
{
lean_object* v_res_2718_; 
v_res_2718_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg(v_f_2710_, v_x_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_);
lean_dec(v___y_2716_);
lean_dec_ref(v___y_2715_);
lean_dec(v___y_2714_);
lean_dec_ref(v___y_2713_);
return v_res_2718_;
}
}
lean_object* l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg(lean_object* v_f_2719_, lean_object* v_init_2720_, lean_object* v_e_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_){
_start:
{
lean_object* v___x_2727_; 
v___x_2727_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg(v_f_2719_, v_e_2721_, v_init_2720_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_);
if (lean_obj_tag(v___x_2727_) == 0)
{
lean_object* v_a_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2736_; 
v_a_2728_ = lean_ctor_get(v___x_2727_, 0);
v_isSharedCheck_2736_ = !lean_is_exclusive(v___x_2727_);
if (v_isSharedCheck_2736_ == 0)
{
v___x_2730_ = v___x_2727_;
v_isShared_2731_ = v_isSharedCheck_2736_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_a_2728_);
lean_dec(v___x_2727_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2736_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v_snd_2732_; lean_object* v___x_2734_; 
v_snd_2732_ = lean_ctor_get(v_a_2728_, 1);
lean_inc(v_snd_2732_);
lean_dec(v_a_2728_);
if (v_isShared_2731_ == 0)
{
lean_ctor_set(v___x_2730_, 0, v_snd_2732_);
v___x_2734_ = v___x_2730_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v_snd_2732_);
v___x_2734_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
return v___x_2734_;
}
}
}
else
{
lean_object* v_a_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2744_; 
v_a_2737_ = lean_ctor_get(v___x_2727_, 0);
v_isSharedCheck_2744_ = !lean_is_exclusive(v___x_2727_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2739_ = v___x_2727_;
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_a_2737_);
lean_dec(v___x_2727_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
lean_object* v___x_2742_; 
if (v_isShared_2740_ == 0)
{
v___x_2742_ = v___x_2739_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_a_2737_);
v___x_2742_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
return v___x_2742_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2719_ = stack[0].m_obj;
lean_object* v_init_2720_ = stack[1].m_obj;
lean_object* v_e_2721_ = stack[2].m_obj;
lean_object* v___y_2722_ = stack[3].m_obj;
lean_object* v___y_2723_ = stack[4].m_obj;
lean_object* v___y_2724_ = stack[5].m_obj;
lean_object* v___y_2725_ = stack[6].m_obj;
lean_object* v_res_2745_;
v_res_2745_ = l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg(v_f_2719_, v_init_2720_, v_e_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_);
stack->m_obj
 = v_res_2745_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg___boxed(lean_object* v_f_2746_, lean_object* v_init_2747_, lean_object* v_e_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_){
_start:
{
lean_object* v_res_2754_; 
v_res_2754_ = l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg(v_f_2746_, v_init_2747_, v_e_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
lean_dec(v___y_2752_);
lean_dec_ref(v___y_2751_);
lean_dec(v___y_2750_);
lean_dec_ref(v___y_2749_);
return v_res_2754_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(lean_object* v_op_2757_, lean_object* v_as_2758_, size_t v_i_2759_, size_t v_stop_2760_, lean_object* v_b_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_){
_start:
{
lean_object* v_a_2768_; uint8_t v___x_2772_; 
v___x_2772_ = lean_usize_dec_eq(v_i_2759_, v_stop_2760_);
if (v___x_2772_ == 0)
{
lean_object* v___x_2773_; lean_object* v___x_2774_; 
v___x_2773_ = lean_array_uget_borrowed(v_as_2758_, v_i_2759_);
lean_inc(v___y_2765_);
lean_inc_ref(v___y_2764_);
lean_inc(v___y_2763_);
lean_inc_ref(v___y_2762_);
lean_inc(v___x_2773_);
v___x_2774_ = lean_infer_type(v___x_2773_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_);
if (lean_obj_tag(v___x_2774_) == 0)
{
lean_object* v_a_2775_; lean_object* v___x_2776_; 
v_a_2775_ = lean_ctor_get(v___x_2774_, 0);
lean_inc(v_a_2775_);
lean_dec_ref_known(v___x_2774_, 1);
lean_inc_ref(v_op_2757_);
v___x_2776_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v_op_2757_, v_a_2775_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_);
if (lean_obj_tag(v___x_2776_) == 0)
{
lean_object* v_a_2777_; lean_object* v___x_2778_; 
v_a_2777_ = lean_ctor_get(v___x_2776_, 0);
lean_inc(v_a_2777_);
lean_dec_ref_known(v___x_2776_, 1);
v___x_2778_ = l_Array_append___redArg(v_b_2761_, v_a_2777_);
lean_dec(v_a_2777_);
v_a_2768_ = v___x_2778_;
goto v___jp_2767_;
}
else
{
lean_dec_ref(v_b_2761_);
if (lean_obj_tag(v___x_2776_) == 0)
{
lean_object* v_a_2779_; 
v_a_2779_ = lean_ctor_get(v___x_2776_, 0);
lean_inc(v_a_2779_);
lean_dec_ref_known(v___x_2776_, 1);
v_a_2768_ = v_a_2779_;
goto v___jp_2767_;
}
else
{
lean_dec_ref(v_op_2757_);
return v___x_2776_;
}
}
}
else
{
lean_object* v_a_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2787_; 
lean_dec_ref(v_b_2761_);
lean_dec_ref(v_op_2757_);
v_a_2780_ = lean_ctor_get(v___x_2774_, 0);
v_isSharedCheck_2787_ = !lean_is_exclusive(v___x_2774_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2782_ = v___x_2774_;
v_isShared_2783_ = v_isSharedCheck_2787_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_a_2780_);
lean_dec(v___x_2774_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2787_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v___x_2785_; 
if (v_isShared_2783_ == 0)
{
v___x_2785_ = v___x_2782_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v_a_2780_);
v___x_2785_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
return v___x_2785_;
}
}
}
}
else
{
lean_object* v___x_2788_; 
lean_dec_ref(v_op_2757_);
v___x_2788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2788_, 0, v_b_2761_);
return v___x_2788_;
}
v___jp_2767_:
{
size_t v___x_2769_; size_t v___x_2770_; 
v___x_2769_ = ((size_t)1ULL);
v___x_2770_ = lean_usize_add(v_i_2759_, v___x_2769_);
v_i_2759_ = v___x_2770_;
v_b_2761_ = v_a_2768_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_op_2757_ = stack[0].m_obj;
lean_object* v_as_2758_ = stack[1].m_obj;
size_t v_i_2759_ = stack[2].m_num;
size_t v_stop_2760_ = stack[3].m_num;
lean_object* v_b_2761_ = stack[4].m_obj;
lean_object* v___y_2762_ = stack[5].m_obj;
lean_object* v___y_2763_ = stack[6].m_obj;
lean_object* v___y_2764_ = stack[7].m_obj;
lean_object* v___y_2765_ = stack[8].m_obj;
lean_object* v_res_2789_;
v_res_2789_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(v_op_2757_, v_as_2758_, v_i_2759_, v_stop_2760_, v_b_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_);
stack->m_obj
 = v_res_2789_;
}
lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0(lean_object* v_op_2790_, lean_object* v_args_2791_, lean_object* v_body_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_){
_start:
{
lean_object* v___x_2798_; 
lean_inc_ref(v_op_2790_);
v___x_2798_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v_op_2790_, v_body_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_);
if (lean_obj_tag(v___x_2798_) == 0)
{
lean_object* v_a_2799_; lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2820_; 
v_a_2799_ = lean_ctor_get(v___x_2798_, 0);
v_isSharedCheck_2820_ = !lean_is_exclusive(v___x_2798_);
if (v_isSharedCheck_2820_ == 0)
{
v___x_2801_ = v___x_2798_;
v_isShared_2802_ = v_isSharedCheck_2820_;
goto v_resetjp_2800_;
}
else
{
lean_inc(v_a_2799_);
lean_dec(v___x_2798_);
v___x_2801_ = lean_box(0);
v_isShared_2802_ = v_isSharedCheck_2820_;
goto v_resetjp_2800_;
}
v_resetjp_2800_:
{
lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; uint8_t v___x_2806_; 
v___x_2803_ = l_Array_reverse___redArg(v_a_2799_);
v___x_2804_ = lean_unsigned_to_nat(0u);
v___x_2805_ = lean_array_get_size(v_args_2791_);
v___x_2806_ = lean_nat_dec_lt(v___x_2804_, v___x_2805_);
if (v___x_2806_ == 0)
{
lean_object* v___x_2808_; 
lean_dec_ref(v_op_2790_);
if (v_isShared_2802_ == 0)
{
lean_ctor_set(v___x_2801_, 0, v___x_2803_);
v___x_2808_ = v___x_2801_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v___x_2803_);
v___x_2808_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
return v___x_2808_;
}
}
else
{
uint8_t v___x_2810_; 
v___x_2810_ = lean_nat_dec_le(v___x_2805_, v___x_2805_);
if (v___x_2810_ == 0)
{
if (v___x_2806_ == 0)
{
lean_object* v___x_2812_; 
lean_dec_ref(v_op_2790_);
if (v_isShared_2802_ == 0)
{
lean_ctor_set(v___x_2801_, 0, v___x_2803_);
v___x_2812_ = v___x_2801_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v___x_2803_);
v___x_2812_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
return v___x_2812_;
}
}
else
{
size_t v___x_2814_; size_t v___x_2815_; lean_object* v___x_2816_; 
lean_del_object(v___x_2801_);
v___x_2814_ = ((size_t)0ULL);
v___x_2815_ = lean_usize_of_nat(v___x_2805_);
v___x_2816_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(v_op_2790_, v_args_2791_, v___x_2814_, v___x_2815_, v___x_2803_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_);
return v___x_2816_;
}
}
else
{
size_t v___x_2817_; size_t v___x_2818_; lean_object* v___x_2819_; 
lean_del_object(v___x_2801_);
v___x_2817_ = ((size_t)0ULL);
v___x_2818_ = lean_usize_of_nat(v___x_2805_);
v___x_2819_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(v_op_2790_, v_args_2791_, v___x_2817_, v___x_2818_, v___x_2803_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_);
return v___x_2819_;
}
}
}
}
else
{
lean_dec_ref(v_op_2790_);
return v___x_2798_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_op_2790_ = stack[0].m_obj;
lean_object* v_args_2791_ = stack[1].m_obj;
lean_object* v_body_2792_ = stack[2].m_obj;
lean_object* v___y_2793_ = stack[3].m_obj;
lean_object* v___y_2794_ = stack[4].m_obj;
lean_object* v___y_2795_ = stack[5].m_obj;
lean_object* v___y_2796_ = stack[6].m_obj;
lean_object* v_res_2821_;
v_res_2821_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0(v_op_2790_, v_args_2791_, v_body_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_);
stack->m_obj
 = v_res_2821_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed(lean_object* v_op_2822_, lean_object* v_args_2823_, lean_object* v_body_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_){
_start:
{
lean_object* v_res_2830_; 
v_res_2830_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0(v_op_2822_, v_args_2823_, v_body_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2827_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2825_);
lean_dec_ref(v_args_2823_);
return v_res_2830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3___boxed(lean_object* v_op_2831_, lean_object* v_a_2832_, lean_object* v_f_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_){
_start:
{
lean_object* v_res_2839_; 
v_res_2839_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3(v_op_2831_, v_a_2832_, v_f_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_);
lean_dec(v___y_2837_);
lean_dec_ref(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec_ref(v___y_2834_);
return v_res_2839_;
}
}
lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(lean_object* v_op_2840_, lean_object* v_e_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_){
_start:
{
switch(lean_obj_tag(v_e_2841_))
{
case 0:
{
lean_object* v___x_2847_; lean_object* v___x_2848_; 
lean_dec_ref_known(v_e_2841_, 1);
lean_dec_ref(v_op_2840_);
v___x_2847_ = ((lean_object*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___closed__0));
v___x_2848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2848_, 0, v___x_2847_);
return v___x_2848_;
}
case 7:
{
lean_object* v___f_2849_; uint8_t v___x_2850_; lean_object* v___x_2851_; 
v___f_2849_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2849_, 0, v_op_2840_);
v___x_2850_ = 0;
v___x_2851_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(v_e_2841_, v___f_2849_, v___x_2850_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_);
return v___x_2851_;
}
case 6:
{
lean_object* v___f_2852_; uint8_t v___x_2853_; uint8_t v___x_2854_; lean_object* v___x_2855_; 
v___f_2852_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2852_, 0, v_op_2840_);
v___x_2853_ = 0;
v___x_2854_ = 1;
v___x_2855_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(v_e_2841_, v___f_2852_, v___x_2853_, v___x_2854_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_);
return v___x_2855_;
}
case 8:
{
lean_object* v___f_2856_; uint8_t v___x_2857_; uint8_t v___x_2858_; lean_object* v___x_2859_; 
v___f_2856_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2856_, 0, v_op_2840_);
v___x_2857_ = 0;
v___x_2858_ = 1;
v___x_2859_ = l_Lean_Meta_lambdaLetTelescope___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(v_e_2841_, v___f_2856_, v___x_2857_, v___x_2858_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_);
return v___x_2859_;
}
default: 
{
lean_object* v___f_2860_; lean_object* v___x_2861_; 
lean_inc_ref(v_op_2840_);
v___f_2860_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3___boxed), 8, 1);
lean_closure_set(v___f_2860_, 0, v_op_2840_);
lean_inc(v_a_2845_);
lean_inc_ref(v_a_2844_);
lean_inc(v_a_2843_);
lean_inc_ref(v_a_2842_);
lean_inc_ref(v_e_2841_);
v___x_2861_ = lean_apply_6(v_op_2840_, v_e_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_, lean_box(0));
if (lean_obj_tag(v___x_2861_) == 0)
{
lean_object* v_a_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; 
v_a_2862_ = lean_ctor_get(v___x_2861_, 0);
lean_inc(v_a_2862_);
lean_dec_ref_known(v___x_2861_, 1);
v___x_2863_ = l_Array_reverse___redArg(v_a_2862_);
v___x_2864_ = l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg(v___f_2860_, v___x_2863_, v_e_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_);
return v___x_2864_;
}
else
{
lean_dec_ref(v___f_2860_);
lean_dec_ref(v_e_2841_);
return v___x_2861_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_op_2840_ = stack[0].m_obj;
lean_object* v_e_2841_ = stack[1].m_obj;
lean_object* v_a_2842_ = stack[2].m_obj;
lean_object* v_a_2843_ = stack[3].m_obj;
lean_object* v_a_2844_ = stack[4].m_obj;
lean_object* v_a_2845_ = stack[5].m_obj;
lean_object* v_res_2865_;
v_res_2865_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v_op_2840_, v_e_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_);
stack->m_obj
 = v_res_2865_;
}
lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3(lean_object* v_op_2866_, lean_object* v_a_2867_, lean_object* v_f_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_){
_start:
{
lean_object* v___x_2874_; 
v___x_2874_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v_op_2866_, v_f_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_);
if (lean_obj_tag(v___x_2874_) == 0)
{
lean_object* v_a_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2883_; 
v_a_2875_ = lean_ctor_get(v___x_2874_, 0);
v_isSharedCheck_2883_ = !lean_is_exclusive(v___x_2874_);
if (v_isSharedCheck_2883_ == 0)
{
v___x_2877_ = v___x_2874_;
v_isShared_2878_ = v_isSharedCheck_2883_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_a_2875_);
lean_dec(v___x_2874_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2883_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v___x_2879_; lean_object* v___x_2881_; 
v___x_2879_ = l_Array_append___redArg(v_a_2867_, v_a_2875_);
lean_dec(v_a_2875_);
if (v_isShared_2878_ == 0)
{
lean_ctor_set(v___x_2877_, 0, v___x_2879_);
v___x_2881_ = v___x_2877_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v___x_2879_);
v___x_2881_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
return v___x_2881_;
}
}
}
else
{
lean_dec_ref(v_a_2867_);
return v___x_2874_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_op_2866_ = stack[0].m_obj;
lean_object* v_a_2867_ = stack[1].m_obj;
lean_object* v_f_2868_ = stack[2].m_obj;
lean_object* v___y_2869_ = stack[3].m_obj;
lean_object* v___y_2870_ = stack[4].m_obj;
lean_object* v___y_2871_ = stack[5].m_obj;
lean_object* v___y_2872_ = stack[6].m_obj;
lean_object* v_res_2884_;
v_res_2884_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3(v_op_2866_, v_a_2867_, v_f_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_);
stack->m_obj
 = v_res_2884_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg___boxed(lean_object* v_op_2885_, lean_object* v_as_2886_, lean_object* v_i_2887_, lean_object* v_stop_2888_, lean_object* v_b_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_){
_start:
{
size_t v_i_boxed_2895_; size_t v_stop_boxed_2896_; lean_object* v_res_2897_; 
v_i_boxed_2895_ = lean_unbox_usize(v_i_2887_);
lean_dec(v_i_2887_);
v_stop_boxed_2896_ = lean_unbox_usize(v_stop_2888_);
lean_dec(v_stop_2888_);
v_res_2897_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(v_op_2885_, v_as_2886_, v_i_boxed_2895_, v_stop_boxed_2896_, v_b_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_);
lean_dec(v___y_2893_);
lean_dec_ref(v___y_2892_);
lean_dec(v___y_2891_);
lean_dec_ref(v___y_2890_);
lean_dec_ref(v_as_2886_);
return v_res_2897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___boxed(lean_object* v_op_2898_, lean_object* v_e_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_){
_start:
{
lean_object* v_res_2905_; 
v_res_2905_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v_op_2898_, v_e_2899_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_);
lean_dec(v_a_2903_);
lean_dec_ref(v_a_2902_);
lean_dec(v_a_2901_);
lean_dec_ref(v_a_2900_);
return v_res_2905_;
}
}
lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches(lean_object* v_00_u03b1_2906_, lean_object* v_op_2907_, lean_object* v_e_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_){
_start:
{
lean_object* v___x_2914_; 
v___x_2914_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v_op_2907_, v_e_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_);
return v___x_2914_;
}
}
LEAN_EXPORT void l_Lean_Meta_Rewrites_getSubexpressionMatches_0interp(lean_interpreter_value* stack)
{
lean_object* v_op_2907_ = stack[1].m_obj;
lean_object* v_e_2908_ = stack[2].m_obj;
lean_object* v_a_2909_ = stack[3].m_obj;
lean_object* v_a_2910_ = stack[4].m_obj;
lean_object* v_a_2911_ = stack[5].m_obj;
lean_object* v_a_2912_ = stack[6].m_obj;
lean_object* v_res_2915_;
v_res_2915_ = l_Lean_Meta_Rewrites_getSubexpressionMatches(lean_box(0), v_op_2907_, v_e_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_);
stack->m_obj
 = v_res_2915_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___boxed(lean_object* v_00_u03b1_2916_, lean_object* v_op_2917_, lean_object* v_e_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_){
_start:
{
lean_object* v_res_2924_; 
v_res_2924_ = l_Lean_Meta_Rewrites_getSubexpressionMatches(v_00_u03b1_2916_, v_op_2917_, v_e_2918_, v_a_2919_, v_a_2920_, v_a_2921_, v_a_2922_);
lean_dec(v_a_2922_);
lean_dec_ref(v_a_2921_);
lean_dec(v_a_2920_);
lean_dec_ref(v_a_2919_);
return v_res_2924_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0(lean_object* v_00_u03b1_2925_, lean_object* v_op_2926_, lean_object* v_as_2927_, size_t v_i_2928_, size_t v_stop_2929_, lean_object* v_b_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_){
_start:
{
lean_object* v___x_2936_; 
v___x_2936_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(v_op_2926_, v_as_2927_, v_i_2928_, v_stop_2929_, v_b_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_);
return v___x_2936_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_op_2926_ = stack[1].m_obj;
lean_object* v_as_2927_ = stack[2].m_obj;
size_t v_i_2928_ = stack[3].m_num;
size_t v_stop_2929_ = stack[4].m_num;
lean_object* v_b_2930_ = stack[5].m_obj;
lean_object* v___y_2931_ = stack[6].m_obj;
lean_object* v___y_2932_ = stack[7].m_obj;
lean_object* v___y_2933_ = stack[8].m_obj;
lean_object* v___y_2934_ = stack[9].m_obj;
lean_object* v_res_2937_;
v_res_2937_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0(lean_box(0), v_op_2926_, v_as_2927_, v_i_2928_, v_stop_2929_, v_b_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_);
stack->m_obj
 = v_res_2937_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___boxed(lean_object* v_00_u03b1_2938_, lean_object* v_op_2939_, lean_object* v_as_2940_, lean_object* v_i_2941_, lean_object* v_stop_2942_, lean_object* v_b_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_){
_start:
{
size_t v_i_boxed_2949_; size_t v_stop_boxed_2950_; lean_object* v_res_2951_; 
v_i_boxed_2949_ = lean_unbox_usize(v_i_2941_);
lean_dec(v_i_2941_);
v_stop_boxed_2950_ = lean_unbox_usize(v_stop_2942_);
lean_dec(v_stop_2942_);
v_res_2951_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__0(v_00_u03b1_2938_, v_op_2939_, v_as_2940_, v_i_boxed_2949_, v_stop_boxed_2950_, v_b_2943_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_);
lean_dec(v___y_2947_);
lean_dec_ref(v___y_2946_);
lean_dec(v___y_2945_);
lean_dec_ref(v___y_2944_);
lean_dec_ref(v_as_2940_);
return v_res_2951_;
}
}
lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3(lean_object* v_00_u03b1_2952_, lean_object* v_f_2953_, lean_object* v_x_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_){
_start:
{
lean_object* v___x_2961_; 
v___x_2961_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg(v_f_2953_, v_x_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_);
return v___x_2961_;
}
}
LEAN_EXPORT void l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2953_ = stack[1].m_obj;
lean_object* v_x_2954_ = stack[2].m_obj;
lean_object* v___y_2955_ = stack[3].m_obj;
lean_object* v___y_2956_ = stack[4].m_obj;
lean_object* v___y_2957_ = stack[5].m_obj;
lean_object* v___y_2958_ = stack[6].m_obj;
lean_object* v___y_2959_ = stack[7].m_obj;
lean_object* v_res_2962_;
v_res_2962_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3(lean_box(0), v_f_2953_, v_x_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_);
stack->m_obj
 = v_res_2962_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___boxed(lean_object* v_00_u03b1_2963_, lean_object* v_f_2964_, lean_object* v_x_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_){
_start:
{
lean_object* v_res_2972_; 
v_res_2972_ = l_Lean_Expr_traverseChildren___at___00Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3(v_00_u03b1_2963_, v_f_2964_, v_x_2965_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_);
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
return v_res_2972_;
}
}
lean_object* l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3(lean_object* v_00_u03b1_2973_, lean_object* v_f_2974_, lean_object* v_init_2975_, lean_object* v_e_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_){
_start:
{
lean_object* v___x_2982_; 
v___x_2982_ = l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg(v_f_2974_, v_init_2975_, v_e_2976_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_);
return v___x_2982_;
}
}
LEAN_EXPORT void l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2974_ = stack[1].m_obj;
lean_object* v_init_2975_ = stack[2].m_obj;
lean_object* v_e_2976_ = stack[3].m_obj;
lean_object* v___y_2977_ = stack[4].m_obj;
lean_object* v___y_2978_ = stack[5].m_obj;
lean_object* v___y_2979_ = stack[6].m_obj;
lean_object* v___y_2980_ = stack[7].m_obj;
lean_object* v_res_2983_;
v_res_2983_ = l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3(lean_box(0), v_f_2974_, v_init_2975_, v_e_2976_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_);
stack->m_obj
 = v_res_2983_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___boxed(lean_object* v_00_u03b1_2984_, lean_object* v_f_2985_, lean_object* v_init_2986_, lean_object* v_e_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_){
_start:
{
lean_object* v_res_2993_; 
v_res_2993_ = l_Lean_Expr_foldlM___at___00Lean_Meta_Rewrites_getSubexpressionMatches_spec__3(v_00_u03b1_2984_, v_f_2985_, v_init_2986_, v_e_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_);
lean_dec(v___y_2991_);
lean_dec_ref(v___y_2990_);
lean_dec(v___y_2989_);
lean_dec_ref(v___y_2988_);
return v_res_2993_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__3(size_t v_sz_2994_, size_t v_i_2995_, lean_object* v_bs_2996_){
_start:
{
uint8_t v___x_2997_; 
v___x_2997_ = lean_usize_dec_lt(v_i_2995_, v_sz_2994_);
if (v___x_2997_ == 0)
{
return v_bs_2996_;
}
else
{
lean_object* v_v_2998_; lean_object* v_fst_2999_; lean_object* v_snd_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3014_; 
v_v_2998_ = lean_array_uget(v_bs_2996_, v_i_2995_);
v_fst_2999_ = lean_ctor_get(v_v_2998_, 0);
v_snd_3000_ = lean_ctor_get(v_v_2998_, 1);
v_isSharedCheck_3014_ = !lean_is_exclusive(v_v_2998_);
if (v_isSharedCheck_3014_ == 0)
{
v___x_3002_ = v_v_2998_;
v_isShared_3003_ = v_isSharedCheck_3014_;
goto v_resetjp_3001_;
}
else
{
lean_inc(v_snd_3000_);
lean_inc(v_fst_2999_);
lean_dec(v_v_2998_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3014_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
lean_object* v___x_3004_; lean_object* v_bs_x27_3005_; lean_object* v___x_3006_; lean_object* v___x_3008_; 
v___x_3004_ = lean_unsigned_to_nat(0u);
v_bs_x27_3005_ = lean_array_uset(v_bs_2996_, v_i_2995_, v___x_3004_);
v___x_3006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3006_, 0, v_fst_2999_);
if (v_isShared_3003_ == 0)
{
lean_ctor_set(v___x_3002_, 0, v___x_3006_);
v___x_3008_ = v___x_3002_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v___x_3006_);
lean_ctor_set(v_reuseFailAlloc_3013_, 1, v_snd_3000_);
v___x_3008_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
size_t v___x_3009_; size_t v___x_3010_; lean_object* v___x_3011_; 
v___x_3009_ = ((size_t)1ULL);
v___x_3010_ = lean_usize_add(v_i_2995_, v___x_3009_);
v___x_3011_ = lean_array_uset(v_bs_x27_3005_, v_i_2995_, v___x_3008_);
v_i_2995_ = v___x_3010_;
v_bs_2996_ = v___x_3011_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__3_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2994_ = stack[0].m_num;
size_t v_i_2995_ = stack[1].m_num;
lean_object* v_bs_2996_ = stack[2].m_obj;
lean_object* v_res_3015_;
v_res_3015_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__3(v_sz_2994_, v_i_2995_, v_bs_2996_);
stack->m_obj
 = v_res_3015_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__3___boxed(lean_object* v_sz_3016_, lean_object* v_i_3017_, lean_object* v_bs_3018_){
_start:
{
size_t v_sz_boxed_3019_; size_t v_i_boxed_3020_; lean_object* v_res_3021_; 
v_sz_boxed_3019_ = lean_unbox_usize(v_sz_3016_);
lean_dec(v_sz_3016_);
v_i_boxed_3020_ = lean_unbox_usize(v_i_3017_);
lean_dec(v_i_3017_);
v_res_3021_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__3(v_sz_boxed_3019_, v_i_boxed_3020_, v_bs_3018_);
return v_res_3021_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0___redArg(lean_object* v_xs_3022_, lean_object* v_j_3023_){
_start:
{
lean_object* v_zero_3024_; uint8_t v_isZero_3025_; 
v_zero_3024_ = lean_unsigned_to_nat(0u);
v_isZero_3025_ = lean_nat_dec_eq(v_j_3023_, v_zero_3024_);
if (v_isZero_3025_ == 1)
{
lean_dec(v_j_3023_);
return v_xs_3022_;
}
else
{
lean_object* v___x_3026_; lean_object* v_snd_3027_; lean_object* v_snd_3028_; lean_object* v_one_3029_; lean_object* v_n_3030_; lean_object* v___x_3031_; lean_object* v_snd_3032_; lean_object* v_snd_3033_; uint8_t v___x_3034_; 
v___x_3026_ = lean_array_fget_borrowed(v_xs_3022_, v_j_3023_);
v_snd_3027_ = lean_ctor_get(v___x_3026_, 1);
v_snd_3028_ = lean_ctor_get(v_snd_3027_, 1);
v_one_3029_ = lean_unsigned_to_nat(1u);
v_n_3030_ = lean_nat_sub(v_j_3023_, v_one_3029_);
v___x_3031_ = lean_array_fget_borrowed(v_xs_3022_, v_n_3030_);
v_snd_3032_ = lean_ctor_get(v___x_3031_, 1);
v_snd_3033_ = lean_ctor_get(v_snd_3032_, 1);
v___x_3034_ = lean_nat_dec_lt(v_snd_3033_, v_snd_3028_);
if (v___x_3034_ == 0)
{
lean_dec(v_n_3030_);
lean_dec(v_j_3023_);
return v_xs_3022_;
}
else
{
lean_object* v___x_3035_; 
v___x_3035_ = lean_array_fswap(v_xs_3022_, v_j_3023_, v_n_3030_);
lean_dec(v_j_3023_);
v_xs_3022_ = v___x_3035_;
v_j_3023_ = v_n_3030_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0(lean_object* v_xs_3037_, lean_object* v_i_3038_, lean_object* v_fuel_3039_){
_start:
{
lean_object* v_zero_3040_; uint8_t v_isZero_3041_; 
v_zero_3040_ = lean_unsigned_to_nat(0u);
v_isZero_3041_ = lean_nat_dec_eq(v_fuel_3039_, v_zero_3040_);
if (v_isZero_3041_ == 1)
{
lean_dec(v_fuel_3039_);
lean_dec(v_i_3038_);
return v_xs_3037_;
}
else
{
lean_object* v___x_3042_; uint8_t v___x_3043_; 
v___x_3042_ = lean_array_get_size(v_xs_3037_);
v___x_3043_ = lean_nat_dec_lt(v_i_3038_, v___x_3042_);
if (v___x_3043_ == 0)
{
lean_dec(v_fuel_3039_);
lean_dec(v_i_3038_);
return v_xs_3037_;
}
else
{
lean_object* v_one_3044_; lean_object* v_n_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; 
v_one_3044_ = lean_unsigned_to_nat(1u);
v_n_3045_ = lean_nat_sub(v_fuel_3039_, v_one_3044_);
lean_dec(v_fuel_3039_);
lean_inc(v_i_3038_);
v___x_3046_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0___redArg(v_xs_3037_, v_i_3038_);
v___x_3047_ = lean_nat_add(v_i_3038_, v_one_3044_);
lean_dec(v_i_3038_);
v_xs_3037_ = v___x_3046_;
v_i_3038_ = v___x_3047_;
v_fuel_3039_ = v_n_3045_;
goto _start;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__2(size_t v_sz_3049_, size_t v_i_3050_, lean_object* v_bs_3051_){
_start:
{
uint8_t v___x_3052_; 
v___x_3052_ = lean_usize_dec_lt(v_i_3050_, v_sz_3049_);
if (v___x_3052_ == 0)
{
return v_bs_3051_;
}
else
{
lean_object* v_v_3053_; lean_object* v_fst_3054_; lean_object* v_snd_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3069_; 
v_v_3053_ = lean_array_uget(v_bs_3051_, v_i_3050_);
v_fst_3054_ = lean_ctor_get(v_v_3053_, 0);
v_snd_3055_ = lean_ctor_get(v_v_3053_, 1);
v_isSharedCheck_3069_ = !lean_is_exclusive(v_v_3053_);
if (v_isSharedCheck_3069_ == 0)
{
v___x_3057_ = v_v_3053_;
v_isShared_3058_ = v_isSharedCheck_3069_;
goto v_resetjp_3056_;
}
else
{
lean_inc(v_snd_3055_);
lean_inc(v_fst_3054_);
lean_dec(v_v_3053_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3069_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
lean_object* v___x_3059_; lean_object* v_bs_x27_3060_; lean_object* v___x_3061_; lean_object* v___x_3063_; 
v___x_3059_ = lean_unsigned_to_nat(0u);
v_bs_x27_3060_ = lean_array_uset(v_bs_3051_, v_i_3050_, v___x_3059_);
v___x_3061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3061_, 0, v_fst_3054_);
if (v_isShared_3058_ == 0)
{
lean_ctor_set(v___x_3057_, 0, v___x_3061_);
v___x_3063_ = v___x_3057_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3068_; 
v_reuseFailAlloc_3068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3068_, 0, v___x_3061_);
lean_ctor_set(v_reuseFailAlloc_3068_, 1, v_snd_3055_);
v___x_3063_ = v_reuseFailAlloc_3068_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
size_t v___x_3064_; size_t v___x_3065_; lean_object* v___x_3066_; 
v___x_3064_ = ((size_t)1ULL);
v___x_3065_ = lean_usize_add(v_i_3050_, v___x_3064_);
v___x_3066_ = lean_array_uset(v_bs_x27_3060_, v_i_3050_, v___x_3063_);
v_i_3050_ = v___x_3065_;
v_bs_3051_ = v___x_3066_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3049_ = stack[0].m_num;
size_t v_i_3050_ = stack[1].m_num;
lean_object* v_bs_3051_ = stack[2].m_obj;
lean_object* v_res_3070_;
v_res_3070_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__2(v_sz_3049_, v_i_3050_, v_bs_3051_);
stack->m_obj
 = v_res_3070_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__2___boxed(lean_object* v_sz_3071_, lean_object* v_i_3072_, lean_object* v_bs_3073_){
_start:
{
size_t v_sz_boxed_3074_; size_t v_i_boxed_3075_; lean_object* v_res_3076_; 
v_sz_boxed_3074_ = lean_unbox_usize(v_sz_3071_);
lean_dec(v_sz_3071_);
v_i_boxed_3075_ = lean_unbox_usize(v_i_3072_);
lean_dec(v_i_3072_);
v_res_3076_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__2(v_sz_boxed_3074_, v_i_boxed_3075_, v_bs_3073_);
return v_res_3076_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg(lean_object* v_forbidden_3077_, lean_object* v_as_3078_, size_t v_sz_3079_, size_t v_i_3080_, lean_object* v_b_3081_){
_start:
{
lean_object* v_a_3084_; uint8_t v___x_3088_; 
v___x_3088_ = lean_usize_dec_lt(v_i_3080_, v_sz_3079_);
if (v___x_3088_ == 0)
{
lean_object* v___x_3089_; 
v___x_3089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3089_, 0, v_b_3081_);
return v___x_3089_;
}
else
{
lean_object* v_a_3090_; lean_object* v_snd_3091_; lean_object* v_snd_3092_; lean_object* v_fst_3093_; lean_object* v_fst_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3152_; 
v_a_3090_ = lean_array_uget(v_as_3078_, v_i_3080_);
v_snd_3091_ = lean_ctor_get(v_a_3090_, 1);
lean_inc(v_snd_3091_);
v_snd_3092_ = lean_ctor_get(v_b_3081_, 1);
lean_inc(v_snd_3092_);
v_fst_3093_ = lean_ctor_get(v_a_3090_, 0);
v_fst_3094_ = lean_ctor_get(v_snd_3091_, 0);
v_isSharedCheck_3152_ = !lean_is_exclusive(v_snd_3091_);
if (v_isSharedCheck_3152_ == 0)
{
lean_object* v_unused_3153_; 
v_unused_3153_ = lean_ctor_get(v_snd_3091_, 1);
lean_dec(v_unused_3153_);
v___x_3096_ = v_snd_3091_;
v_isShared_3097_ = v_isSharedCheck_3152_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_fst_3094_);
lean_dec(v_snd_3091_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3152_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
lean_object* v_fst_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3150_; 
v_fst_3098_ = lean_ctor_get(v_b_3081_, 0);
v_isSharedCheck_3150_ = !lean_is_exclusive(v_b_3081_);
if (v_isSharedCheck_3150_ == 0)
{
lean_object* v_unused_3151_; 
v_unused_3151_ = lean_ctor_get(v_b_3081_, 1);
lean_dec(v_unused_3151_);
v___x_3100_ = v_b_3081_;
v_isShared_3101_ = v_isSharedCheck_3150_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_fst_3098_);
lean_dec(v_b_3081_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3150_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
lean_object* v_fst_3102_; lean_object* v_snd_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3149_; 
v_fst_3102_ = lean_ctor_get(v_snd_3092_, 0);
v_snd_3103_ = lean_ctor_get(v_snd_3092_, 1);
v_isSharedCheck_3149_ = !lean_is_exclusive(v_snd_3092_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3105_ = v_snd_3092_;
v_isShared_3106_ = v_isSharedCheck_3149_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_snd_3103_);
lean_inc(v_fst_3102_);
lean_dec(v_snd_3092_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3149_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
uint8_t v___x_3121_; 
v___x_3121_ = l_Lean_NameSet_contains(v_forbidden_3077_, v_fst_3093_);
if (v___x_3121_ == 0)
{
uint8_t v___x_3122_; 
v___x_3122_ = lean_unbox(v_fst_3094_);
lean_dec(v_fst_3094_);
if (v___x_3122_ == 0)
{
uint8_t v___x_3123_; 
lean_inc(v_fst_3093_);
lean_del_object(v___x_3105_);
lean_del_object(v___x_3100_);
v___x_3123_ = l_Lean_NameSet_contains(v_fst_3098_, v_fst_3093_);
if (v___x_3123_ == 0)
{
if (v___x_3088_ == 0)
{
lean_dec(v_fst_3093_);
lean_dec(v_a_3090_);
goto v___jp_3116_;
}
else
{
lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; 
lean_del_object(v___x_3096_);
v___x_3124_ = lean_array_push(v_snd_3103_, v_a_3090_);
v___x_3125_ = l_Lean_NameSet_insert(v_fst_3098_, v_fst_3093_);
v___x_3126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3126_, 0, v_fst_3102_);
lean_ctor_set(v___x_3126_, 1, v___x_3124_);
v___x_3127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3127_, 0, v___x_3125_);
lean_ctor_set(v___x_3127_, 1, v___x_3126_);
v_a_3084_ = v___x_3127_;
goto v___jp_3083_;
}
}
else
{
lean_dec(v_fst_3093_);
lean_dec(v_a_3090_);
goto v___jp_3116_;
}
}
else
{
uint8_t v___x_3128_; 
lean_del_object(v___x_3096_);
v___x_3128_ = l_Lean_NameSet_contains(v_fst_3102_, v_fst_3093_);
if (v___x_3128_ == 0)
{
lean_inc(v_fst_3093_);
goto v___jp_3107_;
}
else
{
if (v___x_3121_ == 0)
{
lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3136_; 
lean_del_object(v___x_3105_);
lean_del_object(v___x_3100_);
v_isSharedCheck_3136_ = !lean_is_exclusive(v_a_3090_);
if (v_isSharedCheck_3136_ == 0)
{
lean_object* v_unused_3137_; lean_object* v_unused_3138_; 
v_unused_3137_ = lean_ctor_get(v_a_3090_, 1);
lean_dec(v_unused_3137_);
v_unused_3138_ = lean_ctor_get(v_a_3090_, 0);
lean_dec(v_unused_3138_);
v___x_3130_ = v_a_3090_;
v_isShared_3131_ = v_isSharedCheck_3136_;
goto v_resetjp_3129_;
}
else
{
lean_dec(v_a_3090_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3136_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
lean_object* v___x_3133_; 
if (v_isShared_3131_ == 0)
{
lean_ctor_set(v___x_3130_, 1, v_snd_3103_);
lean_ctor_set(v___x_3130_, 0, v_fst_3102_);
v___x_3133_ = v___x_3130_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v_fst_3102_);
lean_ctor_set(v_reuseFailAlloc_3135_, 1, v_snd_3103_);
v___x_3133_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
lean_object* v___x_3134_; 
v___x_3134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3134_, 0, v_fst_3098_);
lean_ctor_set(v___x_3134_, 1, v___x_3133_);
v_a_3084_ = v___x_3134_;
goto v___jp_3083_;
}
}
}
else
{
lean_inc(v_fst_3093_);
goto v___jp_3107_;
}
}
}
}
else
{
lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3146_; 
lean_del_object(v___x_3105_);
lean_del_object(v___x_3100_);
lean_del_object(v___x_3096_);
lean_dec(v_fst_3094_);
v_isSharedCheck_3146_ = !lean_is_exclusive(v_a_3090_);
if (v_isSharedCheck_3146_ == 0)
{
lean_object* v_unused_3147_; lean_object* v_unused_3148_; 
v_unused_3147_ = lean_ctor_get(v_a_3090_, 1);
lean_dec(v_unused_3147_);
v_unused_3148_ = lean_ctor_get(v_a_3090_, 0);
lean_dec(v_unused_3148_);
v___x_3140_ = v_a_3090_;
v_isShared_3141_ = v_isSharedCheck_3146_;
goto v_resetjp_3139_;
}
else
{
lean_dec(v_a_3090_);
v___x_3140_ = lean_box(0);
v_isShared_3141_ = v_isSharedCheck_3146_;
goto v_resetjp_3139_;
}
v_resetjp_3139_:
{
lean_object* v___x_3143_; 
if (v_isShared_3141_ == 0)
{
lean_ctor_set(v___x_3140_, 1, v_snd_3103_);
lean_ctor_set(v___x_3140_, 0, v_fst_3102_);
v___x_3143_ = v___x_3140_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v_fst_3102_);
lean_ctor_set(v_reuseFailAlloc_3145_, 1, v_snd_3103_);
v___x_3143_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
lean_object* v___x_3144_; 
v___x_3144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3144_, 0, v_fst_3098_);
lean_ctor_set(v___x_3144_, 1, v___x_3143_);
v_a_3084_ = v___x_3144_;
goto v___jp_3083_;
}
}
}
v___jp_3107_:
{
lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3111_; 
v___x_3108_ = lean_array_push(v_snd_3103_, v_a_3090_);
v___x_3109_ = l_Lean_NameSet_insert(v_fst_3102_, v_fst_3093_);
if (v_isShared_3106_ == 0)
{
lean_ctor_set(v___x_3105_, 1, v___x_3108_);
lean_ctor_set(v___x_3105_, 0, v___x_3109_);
v___x_3111_ = v___x_3105_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v___x_3109_);
lean_ctor_set(v_reuseFailAlloc_3115_, 1, v___x_3108_);
v___x_3111_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3110_;
}
v_reusejp_3110_:
{
lean_object* v___x_3113_; 
if (v_isShared_3101_ == 0)
{
lean_ctor_set(v___x_3100_, 1, v___x_3111_);
v___x_3113_ = v___x_3100_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v_fst_3098_);
lean_ctor_set(v_reuseFailAlloc_3114_, 1, v___x_3111_);
v___x_3113_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
v_a_3084_ = v___x_3113_;
goto v___jp_3083_;
}
}
}
v___jp_3116_:
{
lean_object* v___x_3118_; 
if (v_isShared_3097_ == 0)
{
lean_ctor_set(v___x_3096_, 1, v_snd_3103_);
lean_ctor_set(v___x_3096_, 0, v_fst_3102_);
v___x_3118_ = v___x_3096_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v_fst_3102_);
lean_ctor_set(v_reuseFailAlloc_3120_, 1, v_snd_3103_);
v___x_3118_ = v_reuseFailAlloc_3120_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
lean_object* v___x_3119_; 
v___x_3119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3119_, 0, v_fst_3098_);
lean_ctor_set(v___x_3119_, 1, v___x_3118_);
v_a_3084_ = v___x_3119_;
goto v___jp_3083_;
}
}
}
}
}
}
v___jp_3083_:
{
size_t v___x_3085_; size_t v___x_3086_; 
v___x_3085_ = ((size_t)1ULL);
v___x_3086_ = lean_usize_add(v_i_3080_, v___x_3085_);
v_i_3080_ = v___x_3086_;
v_b_3081_ = v_a_3084_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_forbidden_3077_ = stack[0].m_obj;
lean_object* v_as_3078_ = stack[1].m_obj;
size_t v_sz_3079_ = stack[2].m_num;
size_t v_i_3080_ = stack[3].m_num;
lean_object* v_b_3081_ = stack[4].m_obj;
lean_object* v_res_3154_;
v_res_3154_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg(v_forbidden_3077_, v_as_3078_, v_sz_3079_, v_i_3080_, v_b_3081_);
stack->m_obj
 = v_res_3154_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg___boxed(lean_object* v_forbidden_3155_, lean_object* v_as_3156_, lean_object* v_sz_3157_, lean_object* v_i_3158_, lean_object* v_b_3159_, lean_object* v___y_3160_){
_start:
{
size_t v_sz_boxed_3161_; size_t v_i_boxed_3162_; lean_object* v_res_3163_; 
v_sz_boxed_3161_ = lean_unbox_usize(v_sz_3157_);
lean_dec(v_sz_3157_);
v_i_boxed_3162_ = lean_unbox_usize(v_i_3158_);
lean_dec(v_i_3158_);
v_res_3163_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg(v_forbidden_3155_, v_as_3156_, v_sz_boxed_3161_, v_i_boxed_3162_, v_b_3159_);
lean_dec_ref(v_as_3156_);
lean_dec(v_forbidden_3155_);
return v_res_3163_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__2(void){
_start:
{
lean_object* v___x_3167_; lean_object* v___x_3168_; 
v___x_3167_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__1));
v___x_3168_ = l_Lean_MessageData_ofFormat(v___x_3167_);
return v___x_3168_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__3(void){
_start:
{
lean_object* v___x_3169_; lean_object* v___x_3170_; 
v___x_3169_ = lean_box(1);
v___x_3170_ = l_Lean_MessageData_ofFormat(v___x_3169_);
return v___x_3170_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4(lean_object* v_a_3173_, lean_object* v_a_3174_){
_start:
{
if (lean_obj_tag(v_a_3173_) == 0)
{
lean_object* v___x_3175_; 
v___x_3175_ = l_List_reverse___redArg(v_a_3174_);
return v___x_3175_;
}
else
{
lean_object* v_head_3176_; lean_object* v_snd_3177_; lean_object* v_tail_3178_; lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3223_; 
v_head_3176_ = lean_ctor_get(v_a_3173_, 0);
lean_inc(v_head_3176_);
v_snd_3177_ = lean_ctor_get(v_head_3176_, 1);
lean_inc(v_snd_3177_);
v_tail_3178_ = lean_ctor_get(v_a_3173_, 1);
v_isSharedCheck_3223_ = !lean_is_exclusive(v_a_3173_);
if (v_isSharedCheck_3223_ == 0)
{
lean_object* v_unused_3224_; 
v_unused_3224_ = lean_ctor_get(v_a_3173_, 0);
lean_dec(v_unused_3224_);
v___x_3180_ = v_a_3173_;
v_isShared_3181_ = v_isSharedCheck_3223_;
goto v_resetjp_3179_;
}
else
{
lean_inc(v_tail_3178_);
lean_dec(v_a_3173_);
v___x_3180_ = lean_box(0);
v_isShared_3181_ = v_isSharedCheck_3223_;
goto v_resetjp_3179_;
}
v_resetjp_3179_:
{
lean_object* v_fst_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3221_; 
v_fst_3182_ = lean_ctor_get(v_head_3176_, 0);
v_isSharedCheck_3221_ = !lean_is_exclusive(v_head_3176_);
if (v_isSharedCheck_3221_ == 0)
{
lean_object* v_unused_3222_; 
v_unused_3222_ = lean_ctor_get(v_head_3176_, 1);
lean_dec(v_unused_3222_);
v___x_3184_ = v_head_3176_;
v_isShared_3185_ = v_isSharedCheck_3221_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_fst_3182_);
lean_dec(v_head_3176_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3221_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
lean_object* v_fst_3186_; lean_object* v_snd_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3220_; 
v_fst_3186_ = lean_ctor_get(v_snd_3177_, 0);
v_snd_3187_ = lean_ctor_get(v_snd_3177_, 1);
v_isSharedCheck_3220_ = !lean_is_exclusive(v_snd_3177_);
if (v_isSharedCheck_3220_ == 0)
{
v___x_3189_ = v_snd_3177_;
v_isShared_3190_ = v_isSharedCheck_3220_;
goto v_resetjp_3188_;
}
else
{
lean_inc(v_snd_3187_);
lean_inc(v_fst_3186_);
lean_dec(v_snd_3177_);
v___x_3189_ = lean_box(0);
v_isShared_3190_ = v_isSharedCheck_3220_;
goto v_resetjp_3188_;
}
v_resetjp_3188_:
{
lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3194_; 
v___x_3191_ = l_Lean_MessageData_ofName(v_fst_3182_);
v___x_3192_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__2, &l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__2_once, _init_l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__2);
if (v_isShared_3190_ == 0)
{
lean_ctor_set_tag(v___x_3189_, 7);
lean_ctor_set(v___x_3189_, 1, v___x_3192_);
lean_ctor_set(v___x_3189_, 0, v___x_3191_);
v___x_3194_ = v___x_3189_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3219_; 
v_reuseFailAlloc_3219_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3219_, 0, v___x_3191_);
lean_ctor_set(v_reuseFailAlloc_3219_, 1, v___x_3192_);
v___x_3194_ = v_reuseFailAlloc_3219_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
lean_object* v___x_3195_; lean_object* v___x_3197_; 
v___x_3195_ = lean_obj_once(&l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__3, &l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__3_once, _init_l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__3);
if (v_isShared_3185_ == 0)
{
lean_ctor_set_tag(v___x_3184_, 7);
lean_ctor_set(v___x_3184_, 1, v___x_3195_);
lean_ctor_set(v___x_3184_, 0, v___x_3194_);
v___x_3197_ = v___x_3184_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v___x_3194_);
lean_ctor_set(v_reuseFailAlloc_3218_, 1, v___x_3195_);
v___x_3197_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3196_;
}
v_reusejp_3196_:
{
lean_object* v___y_3199_; uint8_t v___x_3215_; 
v___x_3215_ = lean_unbox(v_fst_3186_);
lean_dec(v_fst_3186_);
if (v___x_3215_ == 0)
{
lean_object* v___x_3216_; 
v___x_3216_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__4));
v___y_3199_ = v___x_3216_;
goto v___jp_3198_;
}
else
{
lean_object* v___x_3217_; 
v___x_3217_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4___closed__5));
v___y_3199_ = v___x_3217_;
goto v___jp_3198_;
}
v___jp_3198_:
{
lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3212_; 
lean_inc_ref(v___y_3199_);
v___x_3200_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3200_, 0, v___y_3199_);
v___x_3201_ = l_Lean_MessageData_ofFormat(v___x_3200_);
v___x_3202_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3202_, 0, v___x_3201_);
lean_ctor_set(v___x_3202_, 1, v___x_3192_);
v___x_3203_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3203_, 0, v___x_3202_);
lean_ctor_set(v___x_3203_, 1, v___x_3195_);
v___x_3204_ = l_Nat_reprFast(v_snd_3187_);
v___x_3205_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3205_, 0, v___x_3204_);
v___x_3206_ = l_Lean_MessageData_ofFormat(v___x_3205_);
v___x_3207_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3207_, 0, v___x_3203_);
lean_ctor_set(v___x_3207_, 1, v___x_3206_);
v___x_3208_ = l_Lean_MessageData_paren(v___x_3207_);
v___x_3209_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3209_, 0, v___x_3197_);
lean_ctor_set(v___x_3209_, 1, v___x_3208_);
v___x_3210_ = l_Lean_MessageData_paren(v___x_3209_);
if (v_isShared_3181_ == 0)
{
lean_ctor_set(v___x_3180_, 1, v_a_3174_);
lean_ctor_set(v___x_3180_, 0, v___x_3210_);
v___x_3212_ = v___x_3180_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v___x_3210_);
lean_ctor_set(v_reuseFailAlloc_3214_, 1, v_a_3174_);
v___x_3212_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
v_a_3173_ = v_tail_3178_;
v_a_3174_ = v___x_3212_;
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
lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; 
v___x_3227_ = ((lean_object*)(l_Lean_Meta_Rewrites_rewriteCandidates___closed__0));
v___x_3228_ = l_Lean_NameSet_empty;
v___x_3229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3229_, 0, v___x_3228_);
lean_ctor_set(v___x_3229_, 1, v___x_3227_);
return v___x_3229_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__2(void){
_start:
{
lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; 
v___x_3230_ = lean_obj_once(&l_Lean_Meta_Rewrites_rewriteCandidates___closed__1, &l_Lean_Meta_Rewrites_rewriteCandidates___closed__1_once, _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__1);
v___x_3231_ = l_Lean_NameSet_empty;
v___x_3232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3232_, 0, v___x_3231_);
lean_ctor_set(v___x_3232_, 1, v___x_3230_);
return v___x_3232_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__3(void){
_start:
{
lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; 
v___x_3233_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_));
v___x_3234_ = ((lean_object*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__4));
v___x_3235_ = l_Lean_Name_append(v___x_3234_, v___x_3233_);
return v___x_3235_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__5(void){
_start:
{
lean_object* v___x_3237_; lean_object* v___x_3238_; 
v___x_3237_ = ((lean_object*)(l_Lean_Meta_Rewrites_rewriteCandidates___closed__4));
v___x_3238_ = l_Lean_stringToMessageData(v___x_3237_);
return v___x_3238_;
}
}
lean_object* l_Lean_Meta_Rewrites_rewriteCandidates(lean_object* v_hyps_3239_, lean_object* v_moduleRef_3240_, lean_object* v_target_3241_, lean_object* v_forbidden_3242_, lean_object* v_a_3243_, lean_object* v_a_3244_, lean_object* v_a_3245_, lean_object* v_a_3246_){
_start:
{
lean_object* v___x_3248_; lean_object* v___x_3249_; 
v___x_3248_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_rwFindDecls___boxed), 7, 1);
lean_closure_set(v___x_3248_, 0, v_moduleRef_3240_);
v___x_3249_ = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(v___x_3248_, v_target_3241_, v_a_3243_, v_a_3244_, v_a_3245_, v_a_3246_);
if (lean_obj_tag(v___x_3249_) == 0)
{
lean_object* v_a_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; size_t v_sz_3255_; size_t v___x_3256_; lean_object* v___x_3257_; 
v_a_3250_ = lean_ctor_get(v___x_3249_, 0);
lean_inc(v_a_3250_);
lean_dec_ref_known(v___x_3249_, 1);
v___x_3251_ = lean_unsigned_to_nat(0u);
v___x_3252_ = lean_array_get_size(v_a_3250_);
v___x_3253_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0(v_a_3250_, v___x_3251_, v___x_3252_);
v___x_3254_ = lean_obj_once(&l_Lean_Meta_Rewrites_rewriteCandidates___closed__2, &l_Lean_Meta_Rewrites_rewriteCandidates___closed__2_once, _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__2);
v_sz_3255_ = lean_array_size(v___x_3253_);
v___x_3256_ = ((size_t)0ULL);
v___x_3257_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg(v_forbidden_3242_, v___x_3253_, v_sz_3255_, v___x_3256_, v___x_3254_);
lean_dec_ref(v___x_3253_);
if (lean_obj_tag(v___x_3257_) == 0)
{
lean_object* v_a_3258_; lean_object* v___x_3260_; uint8_t v_isShared_3261_; uint8_t v_isSharedCheck_3302_; 
v_a_3258_ = lean_ctor_get(v___x_3257_, 0);
v_isSharedCheck_3302_ = !lean_is_exclusive(v___x_3257_);
if (v_isSharedCheck_3302_ == 0)
{
v___x_3260_ = v___x_3257_;
v_isShared_3261_ = v_isSharedCheck_3302_;
goto v_resetjp_3259_;
}
else
{
lean_inc(v_a_3258_);
lean_dec(v___x_3257_);
v___x_3260_ = lean_box(0);
v_isShared_3261_ = v_isSharedCheck_3302_;
goto v_resetjp_3259_;
}
v_resetjp_3259_:
{
lean_object* v_snd_3262_; lean_object* v_snd_3263_; lean_object* v___x_3265_; uint8_t v_isShared_3266_; uint8_t v_isSharedCheck_3300_; 
v_snd_3262_ = lean_ctor_get(v_a_3258_, 1);
lean_inc(v_snd_3262_);
lean_dec(v_a_3258_);
v_snd_3263_ = lean_ctor_get(v_snd_3262_, 1);
v_isSharedCheck_3300_ = !lean_is_exclusive(v_snd_3262_);
if (v_isSharedCheck_3300_ == 0)
{
lean_object* v_unused_3301_; 
v_unused_3301_ = lean_ctor_get(v_snd_3262_, 0);
lean_dec(v_unused_3301_);
v___x_3265_ = v_snd_3262_;
v_isShared_3266_ = v_isSharedCheck_3300_;
goto v_resetjp_3264_;
}
else
{
lean_inc(v_snd_3263_);
lean_dec(v_snd_3262_);
v___x_3265_ = lean_box(0);
v_isShared_3266_ = v_isSharedCheck_3300_;
goto v_resetjp_3264_;
}
v_resetjp_3264_:
{
lean_object* v_toCold_3276_; lean_object* v_options_3277_; uint8_t v_hasTrace_3278_; 
v_toCold_3276_ = lean_ctor_get(v_a_3245_, 0);
v_options_3277_ = lean_ctor_get(v_toCold_3276_, 2);
v_hasTrace_3278_ = lean_ctor_get_uint8(v_options_3277_, sizeof(void*)*1);
if (v_hasTrace_3278_ == 0)
{
lean_del_object(v___x_3265_);
goto v___jp_3267_;
}
else
{
lean_object* v_inheritedTraceOptions_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; uint8_t v___x_3282_; 
v_inheritedTraceOptions_3279_ = lean_ctor_get(v_toCold_3276_, 11);
v___x_3280_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1_00___x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_));
v___x_3281_ = lean_obj_once(&l_Lean_Meta_Rewrites_rewriteCandidates___closed__3, &l_Lean_Meta_Rewrites_rewriteCandidates___closed__3_once, _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__3);
v___x_3282_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3279_, v_options_3277_, v___x_3281_);
if (v___x_3282_ == 0)
{
lean_del_object(v___x_3265_);
goto v___jp_3267_;
}
else
{
lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3289_; 
v___x_3283_ = lean_obj_once(&l_Lean_Meta_Rewrites_rewriteCandidates___closed__5, &l_Lean_Meta_Rewrites_rewriteCandidates___closed__5_once, _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__5);
lean_inc(v_snd_3263_);
v___x_3284_ = lean_array_to_list(v_snd_3263_);
v___x_3285_ = lean_box(0);
v___x_3286_ = l_List_mapTR_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__4(v___x_3284_, v___x_3285_);
v___x_3287_ = l_Lean_MessageData_ofList(v___x_3286_);
if (v_isShared_3266_ == 0)
{
lean_ctor_set_tag(v___x_3265_, 7);
lean_ctor_set(v___x_3265_, 1, v___x_3287_);
lean_ctor_set(v___x_3265_, 0, v___x_3283_);
v___x_3289_ = v___x_3265_;
goto v_reusejp_3288_;
}
else
{
lean_object* v_reuseFailAlloc_3299_; 
v_reuseFailAlloc_3299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3299_, 0, v___x_3283_);
lean_ctor_set(v_reuseFailAlloc_3299_, 1, v___x_3287_);
v___x_3289_ = v_reuseFailAlloc_3299_;
goto v_reusejp_3288_;
}
v_reusejp_3288_:
{
lean_object* v___x_3290_; 
v___x_3290_ = l_Lean_addTrace___at___00Lean_Meta_Rewrites_rwLemma_spec__2(v___x_3280_, v___x_3289_, v_a_3243_, v_a_3244_, v_a_3245_, v_a_3246_);
if (lean_obj_tag(v___x_3290_) == 0)
{
lean_dec_ref_known(v___x_3290_, 1);
goto v___jp_3267_;
}
else
{
lean_object* v_a_3291_; lean_object* v___x_3293_; uint8_t v_isShared_3294_; uint8_t v_isSharedCheck_3298_; 
lean_dec(v_snd_3263_);
lean_del_object(v___x_3260_);
lean_dec_ref(v_hyps_3239_);
v_a_3291_ = lean_ctor_get(v___x_3290_, 0);
v_isSharedCheck_3298_ = !lean_is_exclusive(v___x_3290_);
if (v_isSharedCheck_3298_ == 0)
{
v___x_3293_ = v___x_3290_;
v_isShared_3294_ = v_isSharedCheck_3298_;
goto v_resetjp_3292_;
}
else
{
lean_inc(v_a_3291_);
lean_dec(v___x_3290_);
v___x_3293_ = lean_box(0);
v_isShared_3294_ = v_isSharedCheck_3298_;
goto v_resetjp_3292_;
}
v_resetjp_3292_:
{
lean_object* v___x_3296_; 
if (v_isShared_3294_ == 0)
{
v___x_3296_ = v___x_3293_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3297_; 
v_reuseFailAlloc_3297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3297_, 0, v_a_3291_);
v___x_3296_ = v_reuseFailAlloc_3297_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
return v___x_3296_;
}
}
}
}
}
}
v___jp_3267_:
{
size_t v_sz_3268_; lean_object* v___x_3269_; size_t v_sz_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3274_; 
v_sz_3268_ = lean_array_size(v_hyps_3239_);
v___x_3269_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__2(v_sz_3268_, v___x_3256_, v_hyps_3239_);
v_sz_3270_ = lean_array_size(v_snd_3263_);
v___x_3271_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__3(v_sz_3270_, v___x_3256_, v_snd_3263_);
v___x_3272_ = l_Array_append___redArg(v___x_3269_, v___x_3271_);
lean_dec_ref(v___x_3271_);
if (v_isShared_3261_ == 0)
{
lean_ctor_set(v___x_3260_, 0, v___x_3272_);
v___x_3274_ = v___x_3260_;
goto v_reusejp_3273_;
}
else
{
lean_object* v_reuseFailAlloc_3275_; 
v_reuseFailAlloc_3275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3275_, 0, v___x_3272_);
v___x_3274_ = v_reuseFailAlloc_3275_;
goto v_reusejp_3273_;
}
v_reusejp_3273_:
{
return v___x_3274_;
}
}
}
}
}
else
{
lean_object* v_a_3303_; lean_object* v___x_3305_; uint8_t v_isShared_3306_; uint8_t v_isSharedCheck_3310_; 
lean_dec_ref(v_hyps_3239_);
v_a_3303_ = lean_ctor_get(v___x_3257_, 0);
v_isSharedCheck_3310_ = !lean_is_exclusive(v___x_3257_);
if (v_isSharedCheck_3310_ == 0)
{
v___x_3305_ = v___x_3257_;
v_isShared_3306_ = v_isSharedCheck_3310_;
goto v_resetjp_3304_;
}
else
{
lean_inc(v_a_3303_);
lean_dec(v___x_3257_);
v___x_3305_ = lean_box(0);
v_isShared_3306_ = v_isSharedCheck_3310_;
goto v_resetjp_3304_;
}
v_resetjp_3304_:
{
lean_object* v___x_3308_; 
if (v_isShared_3306_ == 0)
{
v___x_3308_ = v___x_3305_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3309_; 
v_reuseFailAlloc_3309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3309_, 0, v_a_3303_);
v___x_3308_ = v_reuseFailAlloc_3309_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
return v___x_3308_;
}
}
}
}
else
{
lean_object* v_a_3311_; lean_object* v___x_3313_; uint8_t v_isShared_3314_; uint8_t v_isSharedCheck_3318_; 
lean_dec_ref(v_hyps_3239_);
v_a_3311_ = lean_ctor_get(v___x_3249_, 0);
v_isSharedCheck_3318_ = !lean_is_exclusive(v___x_3249_);
if (v_isSharedCheck_3318_ == 0)
{
v___x_3313_ = v___x_3249_;
v_isShared_3314_ = v_isSharedCheck_3318_;
goto v_resetjp_3312_;
}
else
{
lean_inc(v_a_3311_);
lean_dec(v___x_3249_);
v___x_3313_ = lean_box(0);
v_isShared_3314_ = v_isSharedCheck_3318_;
goto v_resetjp_3312_;
}
v_resetjp_3312_:
{
lean_object* v___x_3316_; 
if (v_isShared_3314_ == 0)
{
v___x_3316_ = v___x_3313_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3317_; 
v_reuseFailAlloc_3317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3317_, 0, v_a_3311_);
v___x_3316_ = v_reuseFailAlloc_3317_;
goto v_reusejp_3315_;
}
v_reusejp_3315_:
{
return v___x_3316_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Rewrites_rewriteCandidates_0interp(lean_interpreter_value* stack)
{
lean_object* v_hyps_3239_ = stack[0].m_obj;
lean_object* v_moduleRef_3240_ = stack[1].m_obj;
lean_object* v_target_3241_ = stack[2].m_obj;
lean_object* v_forbidden_3242_ = stack[3].m_obj;
lean_object* v_a_3243_ = stack[4].m_obj;
lean_object* v_a_3244_ = stack[5].m_obj;
lean_object* v_a_3245_ = stack[6].m_obj;
lean_object* v_a_3246_ = stack[7].m_obj;
lean_object* v_res_3319_;
v_res_3319_ = l_Lean_Meta_Rewrites_rewriteCandidates(v_hyps_3239_, v_moduleRef_3240_, v_target_3241_, v_forbidden_3242_, v_a_3243_, v_a_3244_, v_a_3245_, v_a_3246_);
stack->m_obj
 = v_res_3319_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rewriteCandidates___boxed(lean_object* v_hyps_3320_, lean_object* v_moduleRef_3321_, lean_object* v_target_3322_, lean_object* v_forbidden_3323_, lean_object* v_a_3324_, lean_object* v_a_3325_, lean_object* v_a_3326_, lean_object* v_a_3327_, lean_object* v_a_3328_){
_start:
{
lean_object* v_res_3329_; 
v_res_3329_ = l_Lean_Meta_Rewrites_rewriteCandidates(v_hyps_3320_, v_moduleRef_3321_, v_target_3322_, v_forbidden_3323_, v_a_3324_, v_a_3325_, v_a_3326_, v_a_3327_);
lean_dec(v_a_3327_);
lean_dec_ref(v_a_3326_);
lean_dec(v_a_3325_);
lean_dec_ref(v_a_3324_);
lean_dec(v_forbidden_3323_);
return v_res_3329_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1(lean_object* v_forbidden_3330_, lean_object* v_as_3331_, size_t v_sz_3332_, size_t v_i_3333_, lean_object* v_b_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_){
_start:
{
lean_object* v___x_3340_; 
v___x_3340_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___redArg(v_forbidden_3330_, v_as_3331_, v_sz_3332_, v_i_3333_, v_b_3334_);
return v___x_3340_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_forbidden_3330_ = stack[0].m_obj;
lean_object* v_as_3331_ = stack[1].m_obj;
size_t v_sz_3332_ = stack[2].m_num;
size_t v_i_3333_ = stack[3].m_num;
lean_object* v_b_3334_ = stack[4].m_obj;
lean_object* v___y_3335_ = stack[5].m_obj;
lean_object* v___y_3336_ = stack[6].m_obj;
lean_object* v___y_3337_ = stack[7].m_obj;
lean_object* v___y_3338_ = stack[8].m_obj;
lean_object* v_res_3341_;
v_res_3341_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1(v_forbidden_3330_, v_as_3331_, v_sz_3332_, v_i_3333_, v_b_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_);
stack->m_obj
 = v_res_3341_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1___boxed(lean_object* v_forbidden_3342_, lean_object* v_as_3343_, lean_object* v_sz_3344_, lean_object* v_i_3345_, lean_object* v_b_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_){
_start:
{
size_t v_sz_boxed_3352_; size_t v_i_boxed_3353_; lean_object* v_res_3354_; 
v_sz_boxed_3352_ = lean_unbox_usize(v_sz_3344_);
lean_dec(v_sz_3344_);
v_i_boxed_3353_ = lean_unbox_usize(v_i_3345_);
lean_dec(v_i_3345_);
v_res_3354_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__1(v_forbidden_3342_, v_as_3343_, v_sz_boxed_3352_, v_i_boxed_3353_, v_b_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_);
lean_dec(v___y_3350_);
lean_dec_ref(v___y_3349_);
lean_dec(v___y_3348_);
lean_dec_ref(v___y_3347_);
lean_dec_ref(v_as_3343_);
lean_dec(v_forbidden_3342_);
return v_res_3354_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0(lean_object* v_xs_3355_, lean_object* v_j_3356_, lean_object* v_h_3357_){
_start:
{
lean_object* v___x_3358_; 
v___x_3358_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0___redArg(v_xs_3355_, v_j_3356_);
return v___x_3358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_newGoal(lean_object* v_r_3359_){
_start:
{
uint8_t v_rfl_x3f_3360_; 
v_rfl_x3f_3360_ = lean_ctor_get_uint8(v_r_3359_, sizeof(void*)*4 + 1);
if (v_rfl_x3f_3360_ == 0)
{
lean_object* v_result_3361_; lean_object* v_eNew_3362_; lean_object* v___x_3363_; 
v_result_3361_ = lean_ctor_get(v_r_3359_, 2);
v_eNew_3362_ = lean_ctor_get(v_result_3361_, 0);
lean_inc_ref(v_eNew_3362_);
v___x_3363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3363_, 0, v_eNew_3362_);
return v___x_3363_;
}
else
{
lean_object* v___x_3364_; 
v___x_3364_ = lean_box(0);
return v___x_3364_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_newGoal___boxed(lean_object* v_r_3365_){
_start:
{
lean_object* v_res_3366_; 
v_res_3366_ = l_Lean_Meta_Rewrites_RewriteResult_newGoal(v_r_3365_);
lean_dec_ref(v_r_3365_);
return v_res_3366_;
}
}
lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0(lean_object* v_x_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_){
_start:
{
lean_object* v___x_3377_; 
lean_inc(v___y_3371_);
lean_inc_ref(v___y_3370_);
lean_inc(v___y_3369_);
lean_inc_ref(v___y_3368_);
v___x_3377_ = lean_apply_9(v_x_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_, lean_box(0));
return v___x_3377_;
}
}
LEAN_EXPORT void l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3367_ = stack[0].m_obj;
lean_object* v___y_3368_ = stack[1].m_obj;
lean_object* v___y_3369_ = stack[2].m_obj;
lean_object* v___y_3370_ = stack[3].m_obj;
lean_object* v___y_3371_ = stack[4].m_obj;
lean_object* v___y_3372_ = stack[5].m_obj;
lean_object* v___y_3373_ = stack[6].m_obj;
lean_object* v___y_3374_ = stack[7].m_obj;
lean_object* v___y_3375_ = stack[8].m_obj;
lean_object* v_res_3378_;
v_res_3378_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0(v_x_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
stack->m_obj
 = v_res_3378_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0___boxed(lean_object* v_x_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_){
_start:
{
lean_object* v_res_3389_; 
v_res_3389_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0(v_x_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
lean_dec(v___y_3383_);
lean_dec_ref(v___y_3382_);
lean_dec(v___y_3381_);
lean_dec_ref(v___y_3380_);
return v_res_3389_;
}
}
lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg(lean_object* v_mctx_3390_, lean_object* v_x_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_){
_start:
{
lean_object* v___f_3401_; lean_object* v___x_3402_; 
lean_inc(v___y_3395_);
lean_inc_ref(v___y_3394_);
lean_inc(v___y_3393_);
lean_inc_ref(v___y_3392_);
v___f_3401_ = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_3401_, 0, v_x_3391_);
lean_closure_set(v___f_3401_, 1, v___y_3392_);
lean_closure_set(v___f_3401_, 2, v___y_3393_);
lean_closure_set(v___f_3401_, 3, v___y_3394_);
lean_closure_set(v___f_3401_, 4, v___y_3395_);
v___x_3402_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp(lean_box(0), v_mctx_3390_, v___f_3401_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_);
if (lean_obj_tag(v___x_3402_) == 0)
{
return v___x_3402_;
}
else
{
lean_object* v_a_3403_; lean_object* v___x_3405_; uint8_t v_isShared_3406_; uint8_t v_isSharedCheck_3410_; 
v_a_3403_ = lean_ctor_get(v___x_3402_, 0);
v_isSharedCheck_3410_ = !lean_is_exclusive(v___x_3402_);
if (v_isSharedCheck_3410_ == 0)
{
v___x_3405_ = v___x_3402_;
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
else
{
lean_inc(v_a_3403_);
lean_dec(v___x_3402_);
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
LEAN_EXPORT void l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mctx_3390_ = stack[0].m_obj;
lean_object* v_x_3391_ = stack[1].m_obj;
lean_object* v___y_3392_ = stack[2].m_obj;
lean_object* v___y_3393_ = stack[3].m_obj;
lean_object* v___y_3394_ = stack[4].m_obj;
lean_object* v___y_3395_ = stack[5].m_obj;
lean_object* v___y_3396_ = stack[6].m_obj;
lean_object* v___y_3397_ = stack[7].m_obj;
lean_object* v___y_3398_ = stack[8].m_obj;
lean_object* v___y_3399_ = stack[9].m_obj;
lean_object* v_res_3411_;
v_res_3411_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg(v_mctx_3390_, v_x_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_);
stack->m_obj
 = v_res_3411_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___boxed(lean_object* v_mctx_3412_, lean_object* v_x_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_){
_start:
{
lean_object* v_res_3423_; 
v_res_3423_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg(v_mctx_3412_, v_x_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_);
lean_dec(v___y_3421_);
lean_dec_ref(v___y_3420_);
lean_dec(v___y_3419_);
lean_dec_ref(v___y_3418_);
lean_dec(v___y_3417_);
lean_dec_ref(v___y_3416_);
lean_dec(v___y_3415_);
lean_dec_ref(v___y_3414_);
return v_res_3423_;
}
}
lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0(lean_object* v_00_u03b1_3424_, lean_object* v_mctx_3425_, lean_object* v_x_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_){
_start:
{
lean_object* v___x_3436_; 
v___x_3436_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg(v_mctx_3425_, v_x_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_);
return v___x_3436_;
}
}
LEAN_EXPORT void l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mctx_3425_ = stack[1].m_obj;
lean_object* v_x_3426_ = stack[2].m_obj;
lean_object* v___y_3427_ = stack[3].m_obj;
lean_object* v___y_3428_ = stack[4].m_obj;
lean_object* v___y_3429_ = stack[5].m_obj;
lean_object* v___y_3430_ = stack[6].m_obj;
lean_object* v___y_3431_ = stack[7].m_obj;
lean_object* v___y_3432_ = stack[8].m_obj;
lean_object* v___y_3433_ = stack[9].m_obj;
lean_object* v___y_3434_ = stack[10].m_obj;
lean_object* v_res_3437_;
v_res_3437_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0(lean_box(0), v_mctx_3425_, v_x_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_);
stack->m_obj
 = v_res_3437_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___boxed(lean_object* v_00_u03b1_3438_, lean_object* v_mctx_3439_, lean_object* v_x_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_){
_start:
{
lean_object* v_res_3450_; 
v_res_3450_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0(v_00_u03b1_3438_, v_mctx_3439_, v_x_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_);
lean_dec(v___y_3448_);
lean_dec_ref(v___y_3447_);
lean_dec(v___y_3446_);
lean_dec_ref(v___y_3445_);
lean_dec(v___y_3444_);
lean_dec_ref(v___y_3443_);
lean_dec(v___y_3442_);
lean_dec_ref(v___y_3441_);
return v_res_3450_;
}
}
lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0(lean_object* v_expr_3451_, uint8_t v_symm_3452_, lean_object* v_r_3453_, lean_object* v_ref_3454_, lean_object* v_checkState_x3f_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_){
_start:
{
lean_object* v_ref_3465_; lean_object* v___x_3466_; 
v_ref_3465_ = lean_ctor_get(v___y_3462_, 2);
v___x_3466_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_3457_, v___y_3459_, v___y_3461_, v___y_3463_);
if (lean_obj_tag(v___x_3466_) == 0)
{
lean_object* v_a_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___y_3477_; 
v_a_3467_ = lean_ctor_get(v___x_3466_, 0);
lean_inc(v_a_3467_);
lean_dec_ref_known(v___x_3466_, 1);
v___x_3468_ = lean_box(v_symm_3452_);
v___x_3469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3469_, 0, v_expr_3451_);
lean_ctor_set(v___x_3469_, 1, v___x_3468_);
v___x_3470_ = lean_box(0);
v___x_3471_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3471_, 0, v___x_3469_);
lean_ctor_set(v___x_3471_, 1, v___x_3470_);
v___x_3472_ = l_Lean_Meta_Rewrites_RewriteResult_newGoal(v_r_3453_);
v___x_3473_ = l_Lean_Option_toLOption___redArg(v___x_3472_);
v___x_3474_ = lean_box(0);
lean_inc(v_ref_3465_);
v___x_3475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3475_, 0, v_ref_3465_);
if (lean_obj_tag(v_checkState_x3f_3455_) == 0)
{
v___y_3477_ = v_a_3467_;
goto v___jp_3476_;
}
else
{
lean_object* v_val_3480_; 
lean_dec(v_a_3467_);
v_val_3480_ = lean_ctor_get(v_checkState_x3f_3455_, 0);
lean_inc(v_val_3480_);
lean_dec_ref_known(v_checkState_x3f_3455_, 1);
v___y_3477_ = v_val_3480_;
goto v___jp_3476_;
}
v___jp_3476_:
{
lean_object* v___x_3478_; lean_object* v___x_3479_; 
v___x_3478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3478_, 0, v___y_3477_);
v___x_3479_ = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion(v_ref_3454_, v___x_3471_, v___x_3473_, v___x_3474_, v___x_3475_, v___x_3478_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_);
return v___x_3479_;
}
}
else
{
lean_object* v_a_3481_; lean_object* v___x_3483_; uint8_t v_isShared_3484_; uint8_t v_isSharedCheck_3488_; 
lean_dec(v_checkState_x3f_3455_);
lean_dec(v_ref_3454_);
lean_dec_ref(v_expr_3451_);
v_a_3481_ = lean_ctor_get(v___x_3466_, 0);
v_isSharedCheck_3488_ = !lean_is_exclusive(v___x_3466_);
if (v_isSharedCheck_3488_ == 0)
{
v___x_3483_ = v___x_3466_;
v_isShared_3484_ = v_isSharedCheck_3488_;
goto v_resetjp_3482_;
}
else
{
lean_inc(v_a_3481_);
lean_dec(v___x_3466_);
v___x_3483_ = lean_box(0);
v_isShared_3484_ = v_isSharedCheck_3488_;
goto v_resetjp_3482_;
}
v_resetjp_3482_:
{
lean_object* v___x_3486_; 
if (v_isShared_3484_ == 0)
{
v___x_3486_ = v___x_3483_;
goto v_reusejp_3485_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v_a_3481_);
v___x_3486_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3485_;
}
v_reusejp_3485_:
{
return v___x_3486_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_expr_3451_ = stack[0].m_obj;
uint8_t v_symm_3452_ = stack[1].m_num;
lean_object* v_r_3453_ = stack[2].m_obj;
lean_object* v_ref_3454_ = stack[3].m_obj;
lean_object* v_checkState_x3f_3455_ = stack[4].m_obj;
lean_object* v___y_3456_ = stack[5].m_obj;
lean_object* v___y_3457_ = stack[6].m_obj;
lean_object* v___y_3458_ = stack[7].m_obj;
lean_object* v___y_3459_ = stack[8].m_obj;
lean_object* v___y_3460_ = stack[9].m_obj;
lean_object* v___y_3461_ = stack[10].m_obj;
lean_object* v___y_3462_ = stack[11].m_obj;
lean_object* v___y_3463_ = stack[12].m_obj;
lean_object* v_res_3489_;
v_res_3489_ = l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0(v_expr_3451_, v_symm_3452_, v_r_3453_, v_ref_3454_, v_checkState_x3f_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_);
stack->m_obj
 = v_res_3489_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0___boxed(lean_object* v_expr_3490_, lean_object* v_symm_3491_, lean_object* v_r_3492_, lean_object* v_ref_3493_, lean_object* v_checkState_x3f_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_){
_start:
{
uint8_t v_symm_boxed_3504_; lean_object* v_res_3505_; 
v_symm_boxed_3504_ = lean_unbox(v_symm_3491_);
v_res_3505_ = l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0(v_expr_3490_, v_symm_boxed_3504_, v_r_3492_, v_ref_3493_, v_checkState_x3f_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_);
lean_dec(v___y_3502_);
lean_dec_ref(v___y_3501_);
lean_dec(v___y_3500_);
lean_dec_ref(v___y_3499_);
lean_dec(v___y_3498_);
lean_dec_ref(v___y_3497_);
lean_dec(v___y_3496_);
lean_dec_ref(v___y_3495_);
lean_dec_ref(v_r_3492_);
return v_res_3505_;
}
}
lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion(lean_object* v_ref_3506_, lean_object* v_r_3507_, lean_object* v_checkState_x3f_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_){
_start:
{
lean_object* v_expr_3518_; uint8_t v_symm_3519_; lean_object* v_mctx_3520_; lean_object* v___x_3521_; lean_object* v___f_3522_; lean_object* v___x_3523_; 
v_expr_3518_ = lean_ctor_get(v_r_3507_, 0);
lean_inc_ref(v_expr_3518_);
v_symm_3519_ = lean_ctor_get_uint8(v_r_3507_, sizeof(void*)*4);
v_mctx_3520_ = lean_ctor_get(v_r_3507_, 3);
lean_inc_ref(v_mctx_3520_);
v___x_3521_ = lean_box(v_symm_3519_);
v___f_3522_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0___boxed), 14, 5);
lean_closure_set(v___f_3522_, 0, v_expr_3518_);
lean_closure_set(v___f_3522_, 1, v___x_3521_);
lean_closure_set(v___f_3522_, 2, v_r_3507_);
lean_closure_set(v___f_3522_, 3, v_ref_3506_);
lean_closure_set(v___f_3522_, 4, v_checkState_x3f_3508_);
v___x_3523_ = l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg(v_mctx_3520_, v___f_3522_, v_a_3509_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_);
return v___x_3523_;
}
}
LEAN_EXPORT void l_Lean_Meta_Rewrites_RewriteResult_addSuggestion_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3506_ = stack[0].m_obj;
lean_object* v_r_3507_ = stack[1].m_obj;
lean_object* v_checkState_x3f_3508_ = stack[2].m_obj;
lean_object* v_a_3509_ = stack[3].m_obj;
lean_object* v_a_3510_ = stack[4].m_obj;
lean_object* v_a_3511_ = stack[5].m_obj;
lean_object* v_a_3512_ = stack[6].m_obj;
lean_object* v_a_3513_ = stack[7].m_obj;
lean_object* v_a_3514_ = stack[8].m_obj;
lean_object* v_a_3515_ = stack[9].m_obj;
lean_object* v_a_3516_ = stack[10].m_obj;
lean_object* v_res_3524_;
v_res_3524_ = l_Lean_Meta_Rewrites_RewriteResult_addSuggestion(v_ref_3506_, v_r_3507_, v_checkState_x3f_3508_, v_a_3509_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_);
stack->m_obj
 = v_res_3524_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___boxed(lean_object* v_ref_3525_, lean_object* v_r_3526_, lean_object* v_checkState_x3f_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_){
_start:
{
lean_object* v_res_3537_; 
v_res_3537_ = l_Lean_Meta_Rewrites_RewriteResult_addSuggestion(v_ref_3525_, v_r_3526_, v_checkState_x3f_3527_, v_a_3528_, v_a_3529_, v_a_3530_, v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_);
lean_dec(v_a_3535_);
lean_dec_ref(v_a_3534_);
lean_dec(v_a_3533_);
lean_dec_ref(v_a_3532_);
lean_dec(v_a_3531_);
lean_dec_ref(v_a_3530_);
lean_dec(v_a_3529_);
lean_dec_ref(v_a_3528_);
return v_res_3537_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3___redArg(lean_object* v_a_3538_, lean_object* v_b_3539_, lean_object* v_x_3540_){
_start:
{
if (lean_obj_tag(v_x_3540_) == 0)
{
lean_dec(v_b_3539_);
lean_dec_ref(v_a_3538_);
return v_x_3540_;
}
else
{
lean_object* v_key_3541_; lean_object* v_value_3542_; lean_object* v_tail_3543_; lean_object* v___x_3545_; uint8_t v_isShared_3546_; uint8_t v_isSharedCheck_3555_; 
v_key_3541_ = lean_ctor_get(v_x_3540_, 0);
v_value_3542_ = lean_ctor_get(v_x_3540_, 1);
v_tail_3543_ = lean_ctor_get(v_x_3540_, 2);
v_isSharedCheck_3555_ = !lean_is_exclusive(v_x_3540_);
if (v_isSharedCheck_3555_ == 0)
{
v___x_3545_ = v_x_3540_;
v_isShared_3546_ = v_isSharedCheck_3555_;
goto v_resetjp_3544_;
}
else
{
lean_inc(v_tail_3543_);
lean_inc(v_value_3542_);
lean_inc(v_key_3541_);
lean_dec(v_x_3540_);
v___x_3545_ = lean_box(0);
v_isShared_3546_ = v_isSharedCheck_3555_;
goto v_resetjp_3544_;
}
v_resetjp_3544_:
{
uint8_t v___x_3547_; 
v___x_3547_ = lean_string_dec_eq(v_key_3541_, v_a_3538_);
if (v___x_3547_ == 0)
{
lean_object* v___x_3548_; lean_object* v___x_3550_; 
v___x_3548_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3___redArg(v_a_3538_, v_b_3539_, v_tail_3543_);
if (v_isShared_3546_ == 0)
{
lean_ctor_set(v___x_3545_, 2, v___x_3548_);
v___x_3550_ = v___x_3545_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v_key_3541_);
lean_ctor_set(v_reuseFailAlloc_3551_, 1, v_value_3542_);
lean_ctor_set(v_reuseFailAlloc_3551_, 2, v___x_3548_);
v___x_3550_ = v_reuseFailAlloc_3551_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
return v___x_3550_;
}
}
else
{
lean_object* v___x_3553_; 
lean_dec(v_value_3542_);
lean_dec(v_key_3541_);
if (v_isShared_3546_ == 0)
{
lean_ctor_set(v___x_3545_, 1, v_b_3539_);
lean_ctor_set(v___x_3545_, 0, v_a_3538_);
v___x_3553_ = v___x_3545_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v_a_3538_);
lean_ctor_set(v_reuseFailAlloc_3554_, 1, v_b_3539_);
lean_ctor_set(v_reuseFailAlloc_3554_, 2, v_tail_3543_);
v___x_3553_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
return v___x_3553_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_x_3556_, lean_object* v_x_3557_){
_start:
{
if (lean_obj_tag(v_x_3557_) == 0)
{
return v_x_3556_;
}
else
{
lean_object* v_key_3558_; lean_object* v_value_3559_; lean_object* v_tail_3560_; lean_object* v___x_3562_; uint8_t v_isShared_3563_; uint8_t v_isSharedCheck_3583_; 
v_key_3558_ = lean_ctor_get(v_x_3557_, 0);
v_value_3559_ = lean_ctor_get(v_x_3557_, 1);
v_tail_3560_ = lean_ctor_get(v_x_3557_, 2);
v_isSharedCheck_3583_ = !lean_is_exclusive(v_x_3557_);
if (v_isSharedCheck_3583_ == 0)
{
v___x_3562_ = v_x_3557_;
v_isShared_3563_ = v_isSharedCheck_3583_;
goto v_resetjp_3561_;
}
else
{
lean_inc(v_tail_3560_);
lean_inc(v_value_3559_);
lean_inc(v_key_3558_);
lean_dec(v_x_3557_);
v___x_3562_ = lean_box(0);
v_isShared_3563_ = v_isSharedCheck_3583_;
goto v_resetjp_3561_;
}
v_resetjp_3561_:
{
lean_object* v___x_3564_; uint64_t v___x_3565_; uint64_t v___x_3566_; uint64_t v___x_3567_; uint64_t v_fold_3568_; uint64_t v___x_3569_; uint64_t v___x_3570_; uint64_t v___x_3571_; size_t v___x_3572_; size_t v___x_3573_; size_t v___x_3574_; size_t v___x_3575_; size_t v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3579_; 
v___x_3564_ = lean_array_get_size(v_x_3556_);
v___x_3565_ = lean_string_hash(v_key_3558_);
v___x_3566_ = 32ULL;
v___x_3567_ = lean_uint64_shift_right(v___x_3565_, v___x_3566_);
v_fold_3568_ = lean_uint64_xor(v___x_3565_, v___x_3567_);
v___x_3569_ = 16ULL;
v___x_3570_ = lean_uint64_shift_right(v_fold_3568_, v___x_3569_);
v___x_3571_ = lean_uint64_xor(v_fold_3568_, v___x_3570_);
v___x_3572_ = lean_uint64_to_usize(v___x_3571_);
v___x_3573_ = lean_usize_of_nat(v___x_3564_);
v___x_3574_ = ((size_t)1ULL);
v___x_3575_ = lean_usize_sub(v___x_3573_, v___x_3574_);
v___x_3576_ = lean_usize_land(v___x_3572_, v___x_3575_);
v___x_3577_ = lean_array_uget_borrowed(v_x_3556_, v___x_3576_);
lean_inc(v___x_3577_);
if (v_isShared_3563_ == 0)
{
lean_ctor_set(v___x_3562_, 2, v___x_3577_);
v___x_3579_ = v___x_3562_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v_key_3558_);
lean_ctor_set(v_reuseFailAlloc_3582_, 1, v_value_3559_);
lean_ctor_set(v_reuseFailAlloc_3582_, 2, v___x_3577_);
v___x_3579_ = v_reuseFailAlloc_3582_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
lean_object* v___x_3580_; 
v___x_3580_ = lean_array_uset(v_x_3556_, v___x_3576_, v___x_3579_);
v_x_3556_ = v___x_3580_;
v_x_3557_ = v_tail_3560_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3___redArg(lean_object* v_i_3584_, lean_object* v_source_3585_, lean_object* v_target_3586_){
_start:
{
lean_object* v___x_3587_; uint8_t v___x_3588_; 
v___x_3587_ = lean_array_get_size(v_source_3585_);
v___x_3588_ = lean_nat_dec_lt(v_i_3584_, v___x_3587_);
if (v___x_3588_ == 0)
{
lean_dec_ref(v_source_3585_);
lean_dec(v_i_3584_);
return v_target_3586_;
}
else
{
lean_object* v_es_3589_; lean_object* v___x_3590_; lean_object* v_source_3591_; lean_object* v_target_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; 
v_es_3589_ = lean_array_fget(v_source_3585_, v_i_3584_);
v___x_3590_ = lean_box(0);
v_source_3591_ = lean_array_fset(v_source_3585_, v_i_3584_, v___x_3590_);
v_target_3592_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3_spec__5___redArg(v_target_3586_, v_es_3589_);
v___x_3593_ = lean_unsigned_to_nat(1u);
v___x_3594_ = lean_nat_add(v_i_3584_, v___x_3593_);
lean_dec(v_i_3584_);
v_i_3584_ = v___x_3594_;
v_source_3585_ = v_source_3591_;
v_target_3586_ = v_target_3592_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2___redArg(lean_object* v_data_3596_){
_start:
{
lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v_nbuckets_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; 
v___x_3597_ = lean_array_get_size(v_data_3596_);
v___x_3598_ = lean_unsigned_to_nat(2u);
v_nbuckets_3599_ = lean_nat_mul(v___x_3597_, v___x_3598_);
v___x_3600_ = lean_unsigned_to_nat(0u);
v___x_3601_ = lean_box(0);
v___x_3602_ = lean_mk_array(v_nbuckets_3599_, v___x_3601_);
v___x_3603_ = lean_array_propagate_mark(v_data_3596_, v___x_3602_);
v___x_3604_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3___redArg(v___x_3600_, v_data_3596_, v___x_3603_);
return v___x_3604_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(lean_object* v_a_3605_, lean_object* v_x_3606_){
_start:
{
if (lean_obj_tag(v_x_3606_) == 0)
{
uint8_t v___x_3607_; 
v___x_3607_ = 0;
return v___x_3607_;
}
else
{
lean_object* v_key_3608_; lean_object* v_tail_3609_; uint8_t v___x_3610_; 
v_key_3608_ = lean_ctor_get(v_x_3606_, 0);
v_tail_3609_ = lean_ctor_get(v_x_3606_, 2);
v___x_3610_ = lean_string_dec_eq(v_key_3608_, v_a_3605_);
if (v___x_3610_ == 0)
{
v_x_3606_ = v_tail_3609_;
goto _start;
}
else
{
return v___x_3610_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3605_ = stack[0].m_obj;
lean_object* v_x_3606_ = stack[1].m_obj;
uint8_t v_res_3612_;
v_res_3612_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(v_a_3605_, v_x_3606_);
stack->m_num = v_res_3612_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg___boxed(lean_object* v_a_3613_, lean_object* v_x_3614_){
_start:
{
uint8_t v_res_3615_; lean_object* v_r_3616_; 
v_res_3615_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(v_a_3613_, v_x_3614_);
lean_dec(v_x_3614_);
lean_dec_ref(v_a_3613_);
v_r_3616_ = lean_box(v_res_3615_);
return v_r_3616_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1___redArg(lean_object* v_m_3617_, lean_object* v_a_3618_, lean_object* v_b_3619_){
_start:
{
lean_object* v_size_3620_; lean_object* v_buckets_3621_; lean_object* v___x_3623_; uint8_t v_isShared_3624_; uint8_t v_isSharedCheck_3664_; 
v_size_3620_ = lean_ctor_get(v_m_3617_, 0);
v_buckets_3621_ = lean_ctor_get(v_m_3617_, 1);
v_isSharedCheck_3664_ = !lean_is_exclusive(v_m_3617_);
if (v_isSharedCheck_3664_ == 0)
{
v___x_3623_ = v_m_3617_;
v_isShared_3624_ = v_isSharedCheck_3664_;
goto v_resetjp_3622_;
}
else
{
lean_inc(v_buckets_3621_);
lean_inc(v_size_3620_);
lean_dec(v_m_3617_);
v___x_3623_ = lean_box(0);
v_isShared_3624_ = v_isSharedCheck_3664_;
goto v_resetjp_3622_;
}
v_resetjp_3622_:
{
lean_object* v___x_3625_; uint64_t v___x_3626_; uint64_t v___x_3627_; uint64_t v___x_3628_; uint64_t v_fold_3629_; uint64_t v___x_3630_; uint64_t v___x_3631_; uint64_t v___x_3632_; size_t v___x_3633_; size_t v___x_3634_; size_t v___x_3635_; size_t v___x_3636_; size_t v___x_3637_; lean_object* v_bkt_3638_; uint8_t v___x_3639_; 
v___x_3625_ = lean_array_get_size(v_buckets_3621_);
v___x_3626_ = lean_string_hash(v_a_3618_);
v___x_3627_ = 32ULL;
v___x_3628_ = lean_uint64_shift_right(v___x_3626_, v___x_3627_);
v_fold_3629_ = lean_uint64_xor(v___x_3626_, v___x_3628_);
v___x_3630_ = 16ULL;
v___x_3631_ = lean_uint64_shift_right(v_fold_3629_, v___x_3630_);
v___x_3632_ = lean_uint64_xor(v_fold_3629_, v___x_3631_);
v___x_3633_ = lean_uint64_to_usize(v___x_3632_);
v___x_3634_ = lean_usize_of_nat(v___x_3625_);
v___x_3635_ = ((size_t)1ULL);
v___x_3636_ = lean_usize_sub(v___x_3634_, v___x_3635_);
v___x_3637_ = lean_usize_land(v___x_3633_, v___x_3636_);
v_bkt_3638_ = lean_array_uget_borrowed(v_buckets_3621_, v___x_3637_);
v___x_3639_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(v_a_3618_, v_bkt_3638_);
if (v___x_3639_ == 0)
{
lean_object* v___x_3640_; lean_object* v_size_x27_3641_; lean_object* v___x_3642_; lean_object* v_buckets_x27_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; uint8_t v___x_3649_; 
v___x_3640_ = lean_unsigned_to_nat(1u);
v_size_x27_3641_ = lean_nat_add(v_size_3620_, v___x_3640_);
lean_dec(v_size_3620_);
lean_inc(v_bkt_3638_);
v___x_3642_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3642_, 0, v_a_3618_);
lean_ctor_set(v___x_3642_, 1, v_b_3619_);
lean_ctor_set(v___x_3642_, 2, v_bkt_3638_);
v_buckets_x27_3643_ = lean_array_uset(v_buckets_3621_, v___x_3637_, v___x_3642_);
v___x_3644_ = lean_unsigned_to_nat(4u);
v___x_3645_ = lean_nat_mul(v_size_x27_3641_, v___x_3644_);
v___x_3646_ = lean_unsigned_to_nat(3u);
v___x_3647_ = lean_nat_div(v___x_3645_, v___x_3646_);
lean_dec(v___x_3645_);
v___x_3648_ = lean_array_get_size(v_buckets_x27_3643_);
v___x_3649_ = lean_nat_dec_le(v___x_3647_, v___x_3648_);
lean_dec(v___x_3647_);
if (v___x_3649_ == 0)
{
lean_object* v_val_3650_; lean_object* v___x_3652_; 
v_val_3650_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2___redArg(v_buckets_x27_3643_);
if (v_isShared_3624_ == 0)
{
lean_ctor_set(v___x_3623_, 1, v_val_3650_);
lean_ctor_set(v___x_3623_, 0, v_size_x27_3641_);
v___x_3652_ = v___x_3623_;
goto v_reusejp_3651_;
}
else
{
lean_object* v_reuseFailAlloc_3653_; 
v_reuseFailAlloc_3653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3653_, 0, v_size_x27_3641_);
lean_ctor_set(v_reuseFailAlloc_3653_, 1, v_val_3650_);
v___x_3652_ = v_reuseFailAlloc_3653_;
goto v_reusejp_3651_;
}
v_reusejp_3651_:
{
return v___x_3652_;
}
}
else
{
lean_object* v___x_3655_; 
if (v_isShared_3624_ == 0)
{
lean_ctor_set(v___x_3623_, 1, v_buckets_x27_3643_);
lean_ctor_set(v___x_3623_, 0, v_size_x27_3641_);
v___x_3655_ = v___x_3623_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3656_; 
v_reuseFailAlloc_3656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3656_, 0, v_size_x27_3641_);
lean_ctor_set(v_reuseFailAlloc_3656_, 1, v_buckets_x27_3643_);
v___x_3655_ = v_reuseFailAlloc_3656_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
return v___x_3655_;
}
}
}
else
{
lean_object* v___x_3657_; lean_object* v_buckets_x27_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3662_; 
lean_inc(v_bkt_3638_);
v___x_3657_ = lean_box(0);
v_buckets_x27_3658_ = lean_array_uset(v_buckets_3621_, v___x_3637_, v___x_3657_);
v___x_3659_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3___redArg(v_a_3618_, v_b_3619_, v_bkt_3638_);
v___x_3660_ = lean_array_uset(v_buckets_x27_3658_, v___x_3637_, v___x_3659_);
if (v_isShared_3624_ == 0)
{
lean_ctor_set(v___x_3623_, 1, v___x_3660_);
v___x_3662_ = v___x_3623_;
goto v_reusejp_3661_;
}
else
{
lean_object* v_reuseFailAlloc_3663_; 
v_reuseFailAlloc_3663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3663_, 0, v_size_3620_);
lean_ctor_set(v_reuseFailAlloc_3663_, 1, v___x_3660_);
v___x_3662_ = v_reuseFailAlloc_3663_;
goto v_reusejp_3661_;
}
v_reusejp_3661_:
{
return v___x_3662_;
}
}
}
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg(lean_object* v_m_3665_, lean_object* v_a_3666_){
_start:
{
lean_object* v_buckets_3667_; lean_object* v___x_3668_; uint64_t v___x_3669_; uint64_t v___x_3670_; uint64_t v___x_3671_; uint64_t v_fold_3672_; uint64_t v___x_3673_; uint64_t v___x_3674_; uint64_t v___x_3675_; size_t v___x_3676_; size_t v___x_3677_; size_t v___x_3678_; size_t v___x_3679_; size_t v___x_3680_; lean_object* v___x_3681_; uint8_t v___x_3682_; 
v_buckets_3667_ = lean_ctor_get(v_m_3665_, 1);
v___x_3668_ = lean_array_get_size(v_buckets_3667_);
v___x_3669_ = lean_string_hash(v_a_3666_);
v___x_3670_ = 32ULL;
v___x_3671_ = lean_uint64_shift_right(v___x_3669_, v___x_3670_);
v_fold_3672_ = lean_uint64_xor(v___x_3669_, v___x_3671_);
v___x_3673_ = 16ULL;
v___x_3674_ = lean_uint64_shift_right(v_fold_3672_, v___x_3673_);
v___x_3675_ = lean_uint64_xor(v_fold_3672_, v___x_3674_);
v___x_3676_ = lean_uint64_to_usize(v___x_3675_);
v___x_3677_ = lean_usize_of_nat(v___x_3668_);
v___x_3678_ = ((size_t)1ULL);
v___x_3679_ = lean_usize_sub(v___x_3677_, v___x_3678_);
v___x_3680_ = lean_usize_land(v___x_3676_, v___x_3679_);
v___x_3681_ = lean_array_uget_borrowed(v_buckets_3667_, v___x_3680_);
v___x_3682_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(v_a_3666_, v___x_3681_);
return v___x_3682_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_3665_ = stack[0].m_obj;
lean_object* v_a_3666_ = stack[1].m_obj;
uint8_t v_res_3683_;
v_res_3683_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg(v_m_3665_, v_a_3666_);
stack->m_num = v_res_3683_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg___boxed(lean_object* v_m_3684_, lean_object* v_a_3685_){
_start:
{
uint8_t v_res_3686_; lean_object* v_r_3687_; 
v_res_3686_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg(v_m_3684_, v_a_3685_);
lean_dec_ref(v_a_3685_);
lean_dec_ref(v_m_3684_);
v_r_3687_ = lean_box(v_res_3686_);
return v_r_3687_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg(lean_object* v_cfg_3688_, lean_object* v_as_x27_3689_, lean_object* v_b_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_){
_start:
{
if (lean_obj_tag(v_as_x27_3689_) == 0)
{
lean_object* v___x_3696_; 
lean_dec_ref(v_cfg_3688_);
v___x_3696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3696_, 0, v_b_3690_);
return v___x_3696_;
}
else
{
lean_object* v_head_3697_; lean_object* v_snd_3698_; lean_object* v_snd_3699_; lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3856_; 
v_head_3697_ = lean_ctor_get(v_as_x27_3689_, 0);
v_snd_3698_ = lean_ctor_get(v_head_3697_, 1);
v_snd_3699_ = lean_ctor_get(v_b_3690_, 1);
v_isSharedCheck_3856_ = !lean_is_exclusive(v_b_3690_);
if (v_isSharedCheck_3856_ == 0)
{
lean_object* v_unused_3857_; 
v_unused_3857_ = lean_ctor_get(v_b_3690_, 0);
lean_dec(v_unused_3857_);
v___x_3701_ = v_b_3690_;
v_isShared_3702_ = v_isSharedCheck_3856_;
goto v_resetjp_3700_;
}
else
{
lean_inc(v_snd_3699_);
lean_dec(v_b_3690_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3856_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
lean_object* v_tail_3703_; lean_object* v_fst_3704_; lean_object* v_fst_3705_; lean_object* v_snd_3706_; lean_object* v_fst_3707_; lean_object* v_snd_3708_; lean_object* v___x_3710_; uint8_t v_isShared_3711_; uint8_t v_isSharedCheck_3855_; 
v_tail_3703_ = lean_ctor_get(v_as_x27_3689_, 1);
v_fst_3704_ = lean_ctor_get(v_head_3697_, 0);
v_fst_3705_ = lean_ctor_get(v_snd_3698_, 0);
v_snd_3706_ = lean_ctor_get(v_snd_3698_, 1);
v_fst_3707_ = lean_ctor_get(v_snd_3699_, 0);
v_snd_3708_ = lean_ctor_get(v_snd_3699_, 1);
v_isSharedCheck_3855_ = !lean_is_exclusive(v_snd_3699_);
if (v_isSharedCheck_3855_ == 0)
{
v___x_3710_ = v_snd_3699_;
v_isShared_3711_ = v_isSharedCheck_3855_;
goto v_resetjp_3709_;
}
else
{
lean_inc(v_snd_3708_);
lean_inc(v_fst_3707_);
lean_dec(v_snd_3699_);
v___x_3710_ = lean_box(0);
v_isShared_3711_ = v_isSharedCheck_3855_;
goto v_resetjp_3709_;
}
v_resetjp_3709_:
{
lean_object* v___x_3712_; lean_object* v___x_3713_; 
v___x_3712_ = lean_box(0);
v___x_3713_ = l_Lean_getRemainingHeartbeats___redArg(v___y_3693_);
if (lean_obj_tag(v___x_3713_) == 0)
{
lean_object* v_a_3714_; lean_object* v___x_3716_; uint8_t v_isShared_3717_; uint8_t v_isSharedCheck_3846_; 
v_a_3714_ = lean_ctor_get(v___x_3713_, 0);
v_isSharedCheck_3846_ = !lean_is_exclusive(v___x_3713_);
if (v_isSharedCheck_3846_ == 0)
{
v___x_3716_ = v___x_3713_;
v_isShared_3717_ = v_isSharedCheck_3846_;
goto v_resetjp_3715_;
}
else
{
lean_inc(v_a_3714_);
lean_dec(v___x_3713_);
v___x_3716_ = lean_box(0);
v_isShared_3717_ = v_isSharedCheck_3846_;
goto v_resetjp_3715_;
}
v_resetjp_3715_:
{
uint8_t v_stopAtRfl_3718_; lean_object* v_max_3719_; lean_object* v_minHeartbeats_3720_; lean_object* v_goal_3721_; lean_object* v_target_3722_; uint8_t v_side_3723_; lean_object* v_mctx_3724_; uint8_t v___x_3725_; 
v_stopAtRfl_3718_ = lean_ctor_get_uint8(v_cfg_3688_, sizeof(void*)*5);
v_max_3719_ = lean_ctor_get(v_cfg_3688_, 0);
v_minHeartbeats_3720_ = lean_ctor_get(v_cfg_3688_, 1);
v_goal_3721_ = lean_ctor_get(v_cfg_3688_, 2);
v_target_3722_ = lean_ctor_get(v_cfg_3688_, 3);
v_side_3723_ = lean_ctor_get_uint8(v_cfg_3688_, sizeof(void*)*5 + 1);
v_mctx_3724_ = lean_ctor_get(v_cfg_3688_, 4);
v___x_3725_ = lean_nat_dec_lt(v_a_3714_, v_minHeartbeats_3720_);
lean_dec(v_a_3714_);
if (v___x_3725_ == 0)
{
lean_object* v___x_3726_; uint8_t v___x_3727_; 
v___x_3726_ = lean_array_get_size(v_snd_3708_);
v___x_3727_ = lean_nat_dec_le(v_max_3719_, v___x_3726_);
if (v___x_3727_ == 0)
{
lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; 
lean_del_object(v___x_3716_);
v___x_3728_ = lean_box(v_side_3723_);
lean_inc(v_snd_3706_);
lean_inc(v_fst_3705_);
lean_inc(v_fst_3704_);
lean_inc_ref(v_target_3722_);
lean_inc(v_goal_3721_);
lean_inc_ref_n(v_mctx_3724_, 2);
v___x_3729_ = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_rwLemma___boxed), 12, 7);
lean_closure_set(v___x_3729_, 0, v_mctx_3724_);
lean_closure_set(v___x_3729_, 1, v_goal_3721_);
lean_closure_set(v___x_3729_, 2, v_target_3722_);
lean_closure_set(v___x_3729_, 3, v___x_3728_);
lean_closure_set(v___x_3729_, 4, v_fst_3704_);
lean_closure_set(v___x_3729_, 5, v_fst_3705_);
lean_closure_set(v___x_3729_, 6, v_snd_3706_);
v___x_3730_ = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___boxed), 8, 3);
lean_closure_set(v___x_3730_, 0, lean_box(0));
lean_closure_set(v___x_3730_, 1, v_mctx_3724_);
lean_closure_set(v___x_3730_, 2, v___x_3729_);
v___x_3731_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v___x_3730_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_);
if (lean_obj_tag(v___x_3731_) == 0)
{
lean_object* v_a_3732_; 
v_a_3732_ = lean_ctor_get(v___x_3731_, 0);
lean_inc(v_a_3732_);
lean_dec_ref_known(v___x_3731_, 1);
if (lean_obj_tag(v_a_3732_) == 0)
{
lean_object* v___x_3734_; 
if (v_isShared_3711_ == 0)
{
v___x_3734_ = v___x_3710_;
goto v_reusejp_3733_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v_fst_3707_);
lean_ctor_set(v_reuseFailAlloc_3739_, 1, v_snd_3708_);
v___x_3734_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3733_;
}
v_reusejp_3733_:
{
lean_object* v___x_3736_; 
if (v_isShared_3702_ == 0)
{
lean_ctor_set(v___x_3701_, 1, v___x_3734_);
lean_ctor_set(v___x_3701_, 0, v___x_3712_);
v___x_3736_ = v___x_3701_;
goto v_reusejp_3735_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v___x_3712_);
lean_ctor_set(v_reuseFailAlloc_3738_, 1, v___x_3734_);
v___x_3736_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3735_;
}
v_reusejp_3735_:
{
v_as_x27_3689_ = v_tail_3703_;
v_b_3690_ = v___x_3736_;
goto _start;
}
}
}
else
{
lean_object* v_val_3740_; lean_object* v___x_3742_; uint8_t v_isShared_3743_; uint8_t v_isSharedCheck_3817_; 
v_val_3740_ = lean_ctor_get(v_a_3732_, 0);
v_isSharedCheck_3817_ = !lean_is_exclusive(v_a_3732_);
if (v_isSharedCheck_3817_ == 0)
{
v___x_3742_ = v_a_3732_;
v_isShared_3743_ = v_isSharedCheck_3817_;
goto v_resetjp_3741_;
}
else
{
lean_inc(v_val_3740_);
lean_dec(v_a_3732_);
v___x_3742_ = lean_box(0);
v_isShared_3743_ = v_isSharedCheck_3817_;
goto v_resetjp_3741_;
}
v_resetjp_3741_:
{
lean_object* v_result_3744_; lean_object* v_mctx_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; 
v_result_3744_ = lean_ctor_get(v_val_3740_, 2);
v_mctx_3745_ = lean_ctor_get(v_val_3740_, 3);
lean_inc(v_val_3740_);
v___x_3746_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult___boxed), 6, 1);
lean_closure_set(v___x_3746_, 0, v_val_3740_);
lean_inc_ref(v_mctx_3745_);
v___x_3747_ = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___boxed), 8, 3);
lean_closure_set(v___x_3747_, 0, lean_box(0));
lean_closure_set(v___x_3747_, 1, v_mctx_3745_);
lean_closure_set(v___x_3747_, 2, v___x_3746_);
v___x_3748_ = l_Lean_withoutModifyingState___at___00Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(v___x_3747_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_);
if (lean_obj_tag(v___x_3748_) == 0)
{
lean_object* v_a_3749_; uint8_t v___x_3750_; 
v_a_3749_ = lean_ctor_get(v___x_3748_, 0);
lean_inc(v_a_3749_);
lean_dec_ref_known(v___x_3748_, 1);
v___x_3750_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg(v_fst_3707_, v_a_3749_);
if (v___x_3750_ == 0)
{
lean_object* v_eNew_3751_; lean_object* v___x_3752_; 
v_eNew_3751_ = lean_ctor_get(v_result_3744_, 0);
lean_inc_ref(v_eNew_3751_);
lean_inc_ref(v_mctx_3745_);
v___x_3752_ = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(v_mctx_3745_, v_eNew_3751_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_);
if (lean_obj_tag(v___x_3752_) == 0)
{
if (v_stopAtRfl_3718_ == 0)
{
lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3757_; 
lean_dec_ref_known(v___x_3752_, 1);
lean_del_object(v___x_3742_);
v___x_3753_ = lean_box(0);
v___x_3754_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1___redArg(v_fst_3707_, v_a_3749_, v___x_3753_);
v___x_3755_ = lean_array_push(v_snd_3708_, v_val_3740_);
if (v_isShared_3711_ == 0)
{
lean_ctor_set(v___x_3710_, 1, v___x_3755_);
lean_ctor_set(v___x_3710_, 0, v___x_3754_);
v___x_3757_ = v___x_3710_;
goto v_reusejp_3756_;
}
else
{
lean_object* v_reuseFailAlloc_3762_; 
v_reuseFailAlloc_3762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3762_, 0, v___x_3754_);
lean_ctor_set(v_reuseFailAlloc_3762_, 1, v___x_3755_);
v___x_3757_ = v_reuseFailAlloc_3762_;
goto v_reusejp_3756_;
}
v_reusejp_3756_:
{
lean_object* v___x_3759_; 
if (v_isShared_3702_ == 0)
{
lean_ctor_set(v___x_3701_, 1, v___x_3757_);
lean_ctor_set(v___x_3701_, 0, v___x_3712_);
v___x_3759_ = v___x_3701_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3761_; 
v_reuseFailAlloc_3761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3761_, 0, v___x_3712_);
lean_ctor_set(v_reuseFailAlloc_3761_, 1, v___x_3757_);
v___x_3759_ = v_reuseFailAlloc_3761_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
v_as_x27_3689_ = v_tail_3703_;
v_b_3690_ = v___x_3759_;
goto _start;
}
}
}
else
{
lean_object* v_a_3763_; lean_object* v___x_3765_; uint8_t v_isShared_3766_; uint8_t v_isSharedCheck_3793_; 
v_a_3763_ = lean_ctor_get(v___x_3752_, 0);
v_isSharedCheck_3793_ = !lean_is_exclusive(v___x_3752_);
if (v_isSharedCheck_3793_ == 0)
{
v___x_3765_ = v___x_3752_;
v_isShared_3766_ = v_isSharedCheck_3793_;
goto v_resetjp_3764_;
}
else
{
lean_inc(v_a_3763_);
lean_dec(v___x_3752_);
v___x_3765_ = lean_box(0);
v_isShared_3766_ = v_isSharedCheck_3793_;
goto v_resetjp_3764_;
}
v_resetjp_3764_:
{
uint8_t v___x_3767_; 
v___x_3767_ = lean_unbox(v_a_3763_);
lean_dec(v_a_3763_);
if (v___x_3767_ == 0)
{
lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3772_; 
lean_del_object(v___x_3765_);
lean_del_object(v___x_3742_);
v___x_3768_ = lean_box(0);
v___x_3769_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1___redArg(v_fst_3707_, v_a_3749_, v___x_3768_);
v___x_3770_ = lean_array_push(v_snd_3708_, v_val_3740_);
if (v_isShared_3711_ == 0)
{
lean_ctor_set(v___x_3710_, 1, v___x_3770_);
lean_ctor_set(v___x_3710_, 0, v___x_3769_);
v___x_3772_ = v___x_3710_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3777_; 
v_reuseFailAlloc_3777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3777_, 0, v___x_3769_);
lean_ctor_set(v_reuseFailAlloc_3777_, 1, v___x_3770_);
v___x_3772_ = v_reuseFailAlloc_3777_;
goto v_reusejp_3771_;
}
v_reusejp_3771_:
{
lean_object* v___x_3774_; 
if (v_isShared_3702_ == 0)
{
lean_ctor_set(v___x_3701_, 1, v___x_3772_);
lean_ctor_set(v___x_3701_, 0, v___x_3712_);
v___x_3774_ = v___x_3701_;
goto v_reusejp_3773_;
}
else
{
lean_object* v_reuseFailAlloc_3776_; 
v_reuseFailAlloc_3776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3776_, 0, v___x_3712_);
lean_ctor_set(v_reuseFailAlloc_3776_, 1, v___x_3772_);
v___x_3774_ = v_reuseFailAlloc_3776_;
goto v_reusejp_3773_;
}
v_reusejp_3773_:
{
v_as_x27_3689_ = v_tail_3703_;
v_b_3690_ = v___x_3774_;
goto _start;
}
}
}
else
{
lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3782_; 
lean_dec(v_a_3749_);
lean_dec_ref(v_cfg_3688_);
v___x_3778_ = lean_unsigned_to_nat(1u);
v___x_3779_ = lean_mk_empty_array_with_capacity(v___x_3778_);
v___x_3780_ = lean_array_push(v___x_3779_, v_val_3740_);
if (v_isShared_3743_ == 0)
{
lean_ctor_set(v___x_3742_, 0, v___x_3780_);
v___x_3782_ = v___x_3742_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3792_; 
v_reuseFailAlloc_3792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3792_, 0, v___x_3780_);
v___x_3782_ = v_reuseFailAlloc_3792_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
lean_object* v___x_3784_; 
if (v_isShared_3711_ == 0)
{
v___x_3784_ = v___x_3710_;
goto v_reusejp_3783_;
}
else
{
lean_object* v_reuseFailAlloc_3791_; 
v_reuseFailAlloc_3791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3791_, 0, v_fst_3707_);
lean_ctor_set(v_reuseFailAlloc_3791_, 1, v_snd_3708_);
v___x_3784_ = v_reuseFailAlloc_3791_;
goto v_reusejp_3783_;
}
v_reusejp_3783_:
{
lean_object* v___x_3786_; 
if (v_isShared_3702_ == 0)
{
lean_ctor_set(v___x_3701_, 1, v___x_3784_);
lean_ctor_set(v___x_3701_, 0, v___x_3782_);
v___x_3786_ = v___x_3701_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3790_; 
v_reuseFailAlloc_3790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3790_, 0, v___x_3782_);
lean_ctor_set(v_reuseFailAlloc_3790_, 1, v___x_3784_);
v___x_3786_ = v_reuseFailAlloc_3790_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
lean_object* v___x_3788_; 
if (v_isShared_3766_ == 0)
{
lean_ctor_set(v___x_3765_, 0, v___x_3786_);
v___x_3788_ = v___x_3765_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v___x_3786_);
v___x_3788_ = v_reuseFailAlloc_3789_;
goto v_reusejp_3787_;
}
v_reusejp_3787_:
{
return v___x_3788_;
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
lean_object* v_a_3794_; lean_object* v___x_3796_; uint8_t v_isShared_3797_; uint8_t v_isSharedCheck_3801_; 
lean_dec(v_a_3749_);
lean_del_object(v___x_3742_);
lean_dec(v_val_3740_);
lean_del_object(v___x_3710_);
lean_dec(v_snd_3708_);
lean_dec(v_fst_3707_);
lean_del_object(v___x_3701_);
lean_dec_ref(v_cfg_3688_);
v_a_3794_ = lean_ctor_get(v___x_3752_, 0);
v_isSharedCheck_3801_ = !lean_is_exclusive(v___x_3752_);
if (v_isSharedCheck_3801_ == 0)
{
v___x_3796_ = v___x_3752_;
v_isShared_3797_ = v_isSharedCheck_3801_;
goto v_resetjp_3795_;
}
else
{
lean_inc(v_a_3794_);
lean_dec(v___x_3752_);
v___x_3796_ = lean_box(0);
v_isShared_3797_ = v_isSharedCheck_3801_;
goto v_resetjp_3795_;
}
v_resetjp_3795_:
{
lean_object* v___x_3799_; 
if (v_isShared_3797_ == 0)
{
v___x_3799_ = v___x_3796_;
goto v_reusejp_3798_;
}
else
{
lean_object* v_reuseFailAlloc_3800_; 
v_reuseFailAlloc_3800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3800_, 0, v_a_3794_);
v___x_3799_ = v_reuseFailAlloc_3800_;
goto v_reusejp_3798_;
}
v_reusejp_3798_:
{
return v___x_3799_;
}
}
}
}
else
{
lean_object* v___x_3803_; 
lean_dec(v_a_3749_);
lean_del_object(v___x_3742_);
lean_dec(v_val_3740_);
if (v_isShared_3711_ == 0)
{
v___x_3803_ = v___x_3710_;
goto v_reusejp_3802_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3808_, 0, v_fst_3707_);
lean_ctor_set(v_reuseFailAlloc_3808_, 1, v_snd_3708_);
v___x_3803_ = v_reuseFailAlloc_3808_;
goto v_reusejp_3802_;
}
v_reusejp_3802_:
{
lean_object* v___x_3805_; 
if (v_isShared_3702_ == 0)
{
lean_ctor_set(v___x_3701_, 1, v___x_3803_);
lean_ctor_set(v___x_3701_, 0, v___x_3712_);
v___x_3805_ = v___x_3701_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3807_; 
v_reuseFailAlloc_3807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3807_, 0, v___x_3712_);
lean_ctor_set(v_reuseFailAlloc_3807_, 1, v___x_3803_);
v___x_3805_ = v_reuseFailAlloc_3807_;
goto v_reusejp_3804_;
}
v_reusejp_3804_:
{
v_as_x27_3689_ = v_tail_3703_;
v_b_3690_ = v___x_3805_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3809_; lean_object* v___x_3811_; uint8_t v_isShared_3812_; uint8_t v_isSharedCheck_3816_; 
lean_del_object(v___x_3742_);
lean_dec(v_val_3740_);
lean_del_object(v___x_3710_);
lean_dec(v_snd_3708_);
lean_dec(v_fst_3707_);
lean_del_object(v___x_3701_);
lean_dec_ref(v_cfg_3688_);
v_a_3809_ = lean_ctor_get(v___x_3748_, 0);
v_isSharedCheck_3816_ = !lean_is_exclusive(v___x_3748_);
if (v_isSharedCheck_3816_ == 0)
{
v___x_3811_ = v___x_3748_;
v_isShared_3812_ = v_isSharedCheck_3816_;
goto v_resetjp_3810_;
}
else
{
lean_inc(v_a_3809_);
lean_dec(v___x_3748_);
v___x_3811_ = lean_box(0);
v_isShared_3812_ = v_isSharedCheck_3816_;
goto v_resetjp_3810_;
}
v_resetjp_3810_:
{
lean_object* v___x_3814_; 
if (v_isShared_3812_ == 0)
{
v___x_3814_ = v___x_3811_;
goto v_reusejp_3813_;
}
else
{
lean_object* v_reuseFailAlloc_3815_; 
v_reuseFailAlloc_3815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3815_, 0, v_a_3809_);
v___x_3814_ = v_reuseFailAlloc_3815_;
goto v_reusejp_3813_;
}
v_reusejp_3813_:
{
return v___x_3814_;
}
}
}
}
}
}
else
{
lean_object* v_a_3818_; lean_object* v___x_3820_; uint8_t v_isShared_3821_; uint8_t v_isSharedCheck_3825_; 
lean_del_object(v___x_3710_);
lean_dec(v_snd_3708_);
lean_dec(v_fst_3707_);
lean_del_object(v___x_3701_);
lean_dec_ref(v_cfg_3688_);
v_a_3818_ = lean_ctor_get(v___x_3731_, 0);
v_isSharedCheck_3825_ = !lean_is_exclusive(v___x_3731_);
if (v_isSharedCheck_3825_ == 0)
{
v___x_3820_ = v___x_3731_;
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
else
{
lean_inc(v_a_3818_);
lean_dec(v___x_3731_);
v___x_3820_ = lean_box(0);
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
v_resetjp_3819_:
{
lean_object* v___x_3823_; 
if (v_isShared_3821_ == 0)
{
v___x_3823_ = v___x_3820_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v_a_3818_);
v___x_3823_ = v_reuseFailAlloc_3824_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
return v___x_3823_;
}
}
}
}
else
{
lean_object* v___x_3826_; lean_object* v___x_3828_; 
lean_dec_ref(v_cfg_3688_);
lean_inc(v_snd_3708_);
v___x_3826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3826_, 0, v_snd_3708_);
if (v_isShared_3711_ == 0)
{
v___x_3828_ = v___x_3710_;
goto v_reusejp_3827_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v_fst_3707_);
lean_ctor_set(v_reuseFailAlloc_3835_, 1, v_snd_3708_);
v___x_3828_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3827_;
}
v_reusejp_3827_:
{
lean_object* v___x_3830_; 
if (v_isShared_3702_ == 0)
{
lean_ctor_set(v___x_3701_, 1, v___x_3828_);
lean_ctor_set(v___x_3701_, 0, v___x_3826_);
v___x_3830_ = v___x_3701_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3834_; 
v_reuseFailAlloc_3834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3834_, 0, v___x_3826_);
lean_ctor_set(v_reuseFailAlloc_3834_, 1, v___x_3828_);
v___x_3830_ = v_reuseFailAlloc_3834_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
lean_object* v___x_3832_; 
if (v_isShared_3717_ == 0)
{
lean_ctor_set(v___x_3716_, 0, v___x_3830_);
v___x_3832_ = v___x_3716_;
goto v_reusejp_3831_;
}
else
{
lean_object* v_reuseFailAlloc_3833_; 
v_reuseFailAlloc_3833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3833_, 0, v___x_3830_);
v___x_3832_ = v_reuseFailAlloc_3833_;
goto v_reusejp_3831_;
}
v_reusejp_3831_:
{
return v___x_3832_;
}
}
}
}
}
else
{
lean_object* v___x_3836_; lean_object* v___x_3838_; 
lean_dec_ref(v_cfg_3688_);
lean_inc(v_snd_3708_);
v___x_3836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3836_, 0, v_snd_3708_);
if (v_isShared_3711_ == 0)
{
v___x_3838_ = v___x_3710_;
goto v_reusejp_3837_;
}
else
{
lean_object* v_reuseFailAlloc_3845_; 
v_reuseFailAlloc_3845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3845_, 0, v_fst_3707_);
lean_ctor_set(v_reuseFailAlloc_3845_, 1, v_snd_3708_);
v___x_3838_ = v_reuseFailAlloc_3845_;
goto v_reusejp_3837_;
}
v_reusejp_3837_:
{
lean_object* v___x_3840_; 
if (v_isShared_3702_ == 0)
{
lean_ctor_set(v___x_3701_, 1, v___x_3838_);
lean_ctor_set(v___x_3701_, 0, v___x_3836_);
v___x_3840_ = v___x_3701_;
goto v_reusejp_3839_;
}
else
{
lean_object* v_reuseFailAlloc_3844_; 
v_reuseFailAlloc_3844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3844_, 0, v___x_3836_);
lean_ctor_set(v_reuseFailAlloc_3844_, 1, v___x_3838_);
v___x_3840_ = v_reuseFailAlloc_3844_;
goto v_reusejp_3839_;
}
v_reusejp_3839_:
{
lean_object* v___x_3842_; 
if (v_isShared_3717_ == 0)
{
lean_ctor_set(v___x_3716_, 0, v___x_3840_);
v___x_3842_ = v___x_3716_;
goto v_reusejp_3841_;
}
else
{
lean_object* v_reuseFailAlloc_3843_; 
v_reuseFailAlloc_3843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3843_, 0, v___x_3840_);
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
}
}
else
{
lean_object* v_a_3847_; lean_object* v___x_3849_; uint8_t v_isShared_3850_; uint8_t v_isSharedCheck_3854_; 
lean_del_object(v___x_3710_);
lean_dec(v_snd_3708_);
lean_dec(v_fst_3707_);
lean_del_object(v___x_3701_);
lean_dec_ref(v_cfg_3688_);
v_a_3847_ = lean_ctor_get(v___x_3713_, 0);
v_isSharedCheck_3854_ = !lean_is_exclusive(v___x_3713_);
if (v_isSharedCheck_3854_ == 0)
{
v___x_3849_ = v___x_3713_;
v_isShared_3850_ = v_isSharedCheck_3854_;
goto v_resetjp_3848_;
}
else
{
lean_inc(v_a_3847_);
lean_dec(v___x_3713_);
v___x_3849_ = lean_box(0);
v_isShared_3850_ = v_isSharedCheck_3854_;
goto v_resetjp_3848_;
}
v_resetjp_3848_:
{
lean_object* v___x_3852_; 
if (v_isShared_3850_ == 0)
{
v___x_3852_ = v___x_3849_;
goto v_reusejp_3851_;
}
else
{
lean_object* v_reuseFailAlloc_3853_; 
v_reuseFailAlloc_3853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3853_, 0, v_a_3847_);
v___x_3852_ = v_reuseFailAlloc_3853_;
goto v_reusejp_3851_;
}
v_reusejp_3851_:
{
return v___x_3852_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_3688_ = stack[0].m_obj;
lean_object* v_as_x27_3689_ = stack[1].m_obj;
lean_object* v_b_3690_ = stack[2].m_obj;
lean_object* v___y_3691_ = stack[3].m_obj;
lean_object* v___y_3692_ = stack[4].m_obj;
lean_object* v___y_3693_ = stack[5].m_obj;
lean_object* v___y_3694_ = stack[6].m_obj;
lean_object* v_res_3858_;
v_res_3858_ = l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg(v_cfg_3688_, v_as_x27_3689_, v_b_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_);
stack->m_obj
 = v_res_3858_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg___boxed(lean_object* v_cfg_3859_, lean_object* v_as_x27_3860_, lean_object* v_b_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_){
_start:
{
lean_object* v_res_3867_; 
v_res_3867_ = l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg(v_cfg_3859_, v_as_x27_3860_, v_b_3861_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_);
lean_dec(v___y_3865_);
lean_dec_ref(v___y_3864_);
lean_dec(v___y_3863_);
lean_dec_ref(v___y_3862_);
lean_dec(v_as_x27_3860_);
return v_res_3867_;
}
}
lean_object* l_Lean_Meta_Rewrites_takeListAux(lean_object* v_cfg_3868_, lean_object* v_seen_3869_, lean_object* v_acc_3870_, lean_object* v_xs_3871_, lean_object* v_a_3872_, lean_object* v_a_3873_, lean_object* v_a_3874_, lean_object* v_a_3875_){
_start:
{
lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; 
v___x_3877_ = lean_box(0);
v___x_3878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3878_, 0, v_seen_3869_);
lean_ctor_set(v___x_3878_, 1, v_acc_3870_);
v___x_3879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3879_, 0, v___x_3877_);
lean_ctor_set(v___x_3879_, 1, v___x_3878_);
v___x_3880_ = l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg(v_cfg_3868_, v_xs_3871_, v___x_3879_, v_a_3872_, v_a_3873_, v_a_3874_, v_a_3875_);
if (lean_obj_tag(v___x_3880_) == 0)
{
lean_object* v_a_3881_; lean_object* v___x_3883_; uint8_t v_isShared_3884_; uint8_t v_isSharedCheck_3895_; 
v_a_3881_ = lean_ctor_get(v___x_3880_, 0);
v_isSharedCheck_3895_ = !lean_is_exclusive(v___x_3880_);
if (v_isSharedCheck_3895_ == 0)
{
v___x_3883_ = v___x_3880_;
v_isShared_3884_ = v_isSharedCheck_3895_;
goto v_resetjp_3882_;
}
else
{
lean_inc(v_a_3881_);
lean_dec(v___x_3880_);
v___x_3883_ = lean_box(0);
v_isShared_3884_ = v_isSharedCheck_3895_;
goto v_resetjp_3882_;
}
v_resetjp_3882_:
{
lean_object* v_fst_3885_; 
v_fst_3885_ = lean_ctor_get(v_a_3881_, 0);
if (lean_obj_tag(v_fst_3885_) == 0)
{
lean_object* v_snd_3886_; lean_object* v_snd_3887_; lean_object* v___x_3889_; 
v_snd_3886_ = lean_ctor_get(v_a_3881_, 1);
lean_inc(v_snd_3886_);
lean_dec(v_a_3881_);
v_snd_3887_ = lean_ctor_get(v_snd_3886_, 1);
lean_inc(v_snd_3887_);
lean_dec(v_snd_3886_);
if (v_isShared_3884_ == 0)
{
lean_ctor_set(v___x_3883_, 0, v_snd_3887_);
v___x_3889_ = v___x_3883_;
goto v_reusejp_3888_;
}
else
{
lean_object* v_reuseFailAlloc_3890_; 
v_reuseFailAlloc_3890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3890_, 0, v_snd_3887_);
v___x_3889_ = v_reuseFailAlloc_3890_;
goto v_reusejp_3888_;
}
v_reusejp_3888_:
{
return v___x_3889_;
}
}
else
{
lean_object* v_val_3891_; lean_object* v___x_3893_; 
lean_inc_ref(v_fst_3885_);
lean_dec(v_a_3881_);
v_val_3891_ = lean_ctor_get(v_fst_3885_, 0);
lean_inc(v_val_3891_);
lean_dec_ref_known(v_fst_3885_, 1);
if (v_isShared_3884_ == 0)
{
lean_ctor_set(v___x_3883_, 0, v_val_3891_);
v___x_3893_ = v___x_3883_;
goto v_reusejp_3892_;
}
else
{
lean_object* v_reuseFailAlloc_3894_; 
v_reuseFailAlloc_3894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3894_, 0, v_val_3891_);
v___x_3893_ = v_reuseFailAlloc_3894_;
goto v_reusejp_3892_;
}
v_reusejp_3892_:
{
return v___x_3893_;
}
}
}
}
else
{
lean_object* v_a_3896_; lean_object* v___x_3898_; uint8_t v_isShared_3899_; uint8_t v_isSharedCheck_3903_; 
v_a_3896_ = lean_ctor_get(v___x_3880_, 0);
v_isSharedCheck_3903_ = !lean_is_exclusive(v___x_3880_);
if (v_isSharedCheck_3903_ == 0)
{
v___x_3898_ = v___x_3880_;
v_isShared_3899_ = v_isSharedCheck_3903_;
goto v_resetjp_3897_;
}
else
{
lean_inc(v_a_3896_);
lean_dec(v___x_3880_);
v___x_3898_ = lean_box(0);
v_isShared_3899_ = v_isSharedCheck_3903_;
goto v_resetjp_3897_;
}
v_resetjp_3897_:
{
lean_object* v___x_3901_; 
if (v_isShared_3899_ == 0)
{
v___x_3901_ = v___x_3898_;
goto v_reusejp_3900_;
}
else
{
lean_object* v_reuseFailAlloc_3902_; 
v_reuseFailAlloc_3902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3902_, 0, v_a_3896_);
v___x_3901_ = v_reuseFailAlloc_3902_;
goto v_reusejp_3900_;
}
v_reusejp_3900_:
{
return v___x_3901_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Rewrites_takeListAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_3868_ = stack[0].m_obj;
lean_object* v_seen_3869_ = stack[1].m_obj;
lean_object* v_acc_3870_ = stack[2].m_obj;
lean_object* v_xs_3871_ = stack[3].m_obj;
lean_object* v_a_3872_ = stack[4].m_obj;
lean_object* v_a_3873_ = stack[5].m_obj;
lean_object* v_a_3874_ = stack[6].m_obj;
lean_object* v_a_3875_ = stack[7].m_obj;
lean_object* v_res_3904_;
v_res_3904_ = l_Lean_Meta_Rewrites_takeListAux(v_cfg_3868_, v_seen_3869_, v_acc_3870_, v_xs_3871_, v_a_3872_, v_a_3873_, v_a_3874_, v_a_3875_);
stack->m_obj
 = v_res_3904_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_takeListAux___boxed(lean_object* v_cfg_3905_, lean_object* v_seen_3906_, lean_object* v_acc_3907_, lean_object* v_xs_3908_, lean_object* v_a_3909_, lean_object* v_a_3910_, lean_object* v_a_3911_, lean_object* v_a_3912_, lean_object* v_a_3913_){
_start:
{
lean_object* v_res_3914_; 
v_res_3914_ = l_Lean_Meta_Rewrites_takeListAux(v_cfg_3905_, v_seen_3906_, v_acc_3907_, v_xs_3908_, v_a_3909_, v_a_3910_, v_a_3911_, v_a_3912_);
lean_dec(v_a_3912_);
lean_dec_ref(v_a_3911_);
lean_dec(v_a_3910_);
lean_dec_ref(v_a_3909_);
lean_dec(v_xs_3908_);
return v_res_3914_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0(lean_object* v_00_u03b2_3915_, lean_object* v_m_3916_, lean_object* v_a_3917_){
_start:
{
uint8_t v___x_3918_; 
v___x_3918_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___redArg(v_m_3916_, v_a_3917_);
return v___x_3918_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_3916_ = stack[1].m_obj;
lean_object* v_a_3917_ = stack[2].m_obj;
uint8_t v_res_3919_;
v_res_3919_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0(lean_box(0), v_m_3916_, v_a_3917_);
stack->m_num = v_res_3919_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0___boxed(lean_object* v_00_u03b2_3920_, lean_object* v_m_3921_, lean_object* v_a_3922_){
_start:
{
uint8_t v_res_3923_; lean_object* v_r_3924_; 
v_res_3923_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0(v_00_u03b2_3920_, v_m_3921_, v_a_3922_);
lean_dec_ref(v_a_3922_);
lean_dec_ref(v_m_3921_);
v_r_3924_ = lean_box(v_res_3923_);
return v_r_3924_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1(lean_object* v_00_u03b2_3925_, lean_object* v_m_3926_, lean_object* v_a_3927_, lean_object* v_b_3928_){
_start:
{
lean_object* v___x_3929_; 
v___x_3929_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1___redArg(v_m_3926_, v_a_3927_, v_b_3928_);
return v___x_3929_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2(lean_object* v_cfg_3930_, lean_object* v_as_3931_, lean_object* v_as_x27_3932_, lean_object* v_b_3933_, lean_object* v_a_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_){
_start:
{
lean_object* v___x_3940_; 
v___x_3940_ = l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___redArg(v_cfg_3930_, v_as_x27_3932_, v_b_3933_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_);
return v___x_3940_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_3930_ = stack[0].m_obj;
lean_object* v_as_3931_ = stack[1].m_obj;
lean_object* v_as_x27_3932_ = stack[2].m_obj;
lean_object* v_b_3933_ = stack[3].m_obj;
lean_object* v___y_3935_ = stack[5].m_obj;
lean_object* v___y_3936_ = stack[6].m_obj;
lean_object* v___y_3937_ = stack[7].m_obj;
lean_object* v___y_3938_ = stack[8].m_obj;
lean_object* v_res_3941_;
v_res_3941_ = l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2(v_cfg_3930_, v_as_3931_, v_as_x27_3932_, v_b_3933_, lean_box(0), v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_);
stack->m_obj
 = v_res_3941_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2___boxed(lean_object* v_cfg_3942_, lean_object* v_as_3943_, lean_object* v_as_x27_3944_, lean_object* v_b_3945_, lean_object* v_a_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_){
_start:
{
lean_object* v_res_3952_; 
v_res_3952_ = l_List_forIn_x27_loop___at___00Lean_Meta_Rewrites_takeListAux_spec__2(v_cfg_3942_, v_as_3943_, v_as_x27_3944_, v_b_3945_, v_a_3946_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_);
lean_dec(v___y_3950_);
lean_dec_ref(v___y_3949_);
lean_dec(v___y_3948_);
lean_dec_ref(v___y_3947_);
lean_dec(v_as_x27_3944_);
lean_dec(v_as_3943_);
return v_res_3952_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0(lean_object* v_00_u03b2_3953_, lean_object* v_a_3954_, lean_object* v_x_3955_){
_start:
{
uint8_t v___x_3956_; 
v___x_3956_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(v_a_3954_, v_x_3955_);
return v___x_3956_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3954_ = stack[1].m_obj;
lean_object* v_x_3955_ = stack[2].m_obj;
uint8_t v_res_3957_;
v_res_3957_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0(lean_box(0), v_a_3954_, v_x_3955_);
stack->m_num = v_res_3957_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3958_, lean_object* v_a_3959_, lean_object* v_x_3960_){
_start:
{
uint8_t v_res_3961_; lean_object* v_r_3962_; 
v_res_3961_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Rewrites_takeListAux_spec__0_spec__0(v_00_u03b2_3958_, v_a_3959_, v_x_3960_);
lean_dec(v_x_3960_);
lean_dec_ref(v_a_3959_);
v_r_3962_ = lean_box(v_res_3961_);
return v_r_3962_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2(lean_object* v_00_u03b2_3963_, lean_object* v_data_3964_){
_start:
{
lean_object* v___x_3965_; 
v___x_3965_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2___redArg(v_data_3964_);
return v___x_3965_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3(lean_object* v_00_u03b2_3966_, lean_object* v_a_3967_, lean_object* v_b_3968_, lean_object* v_x_3969_){
_start:
{
lean_object* v___x_3970_; 
v___x_3970_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__3___redArg(v_a_3967_, v_b_3968_, v_x_3969_);
return v___x_3970_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_3971_, lean_object* v_i_3972_, lean_object* v_source_3973_, lean_object* v_target_3974_){
_start:
{
lean_object* v___x_3975_; 
v___x_3975_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3___redArg(v_i_3972_, v_source_3973_, v_target_3974_);
return v___x_3975_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_3976_, lean_object* v_x_3977_, lean_object* v_x_3978_){
_start:
{
lean_object* v___x_3979_; 
v___x_3979_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Rewrites_takeListAux_spec__1_spec__2_spec__3_spec__5___redArg(v_x_3977_, v_x_3978_);
return v___x_3979_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_findRewrites___closed__0(void){
_start:
{
lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; 
v___x_3980_ = lean_box(0);
v___x_3981_ = lean_unsigned_to_nat(16u);
v___x_3982_ = lean_mk_array(v___x_3981_, v___x_3980_);
return v___x_3982_;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_findRewrites___closed__1(void){
_start:
{
lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; 
v___x_3983_ = lean_obj_once(&l_Lean_Meta_Rewrites_findRewrites___closed__0, &l_Lean_Meta_Rewrites_findRewrites___closed__0_once, _init_l_Lean_Meta_Rewrites_findRewrites___closed__0);
v___x_3984_ = lean_unsigned_to_nat(0u);
v___x_3985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3985_, 0, v___x_3984_);
lean_ctor_set(v___x_3985_, 1, v___x_3983_);
return v___x_3985_;
}
}
lean_object* l_Lean_Meta_Rewrites_findRewrites(lean_object* v_hyps_3986_, lean_object* v_moduleRef_3987_, lean_object* v_goal_3988_, lean_object* v_target_3989_, lean_object* v_forbidden_3990_, uint8_t v_side_3991_, uint8_t v_stopAtRfl_3992_, lean_object* v_max_3993_, lean_object* v_leavePercentHeartbeats_3994_, lean_object* v_a_3995_, lean_object* v_a_3996_, lean_object* v_a_3997_, lean_object* v_a_3998_){
_start:
{
lean_object* v___x_4000_; lean_object* v_mctx_4001_; lean_object* v___x_4002_; 
v___x_4000_ = lean_st_ref_get(v_a_3996_);
v_mctx_4001_ = lean_ctor_get(v___x_4000_, 0);
lean_inc_ref(v_mctx_4001_);
lean_dec(v___x_4000_);
lean_inc_ref(v_target_3989_);
v___x_4002_ = l_Lean_Meta_Rewrites_rewriteCandidates(v_hyps_3986_, v_moduleRef_3987_, v_target_3989_, v_forbidden_3990_, v_a_3995_, v_a_3996_, v_a_3997_, v_a_3998_);
if (lean_obj_tag(v___x_4002_) == 0)
{
lean_object* v_a_4003_; lean_object* v_minHeartbeats_4005_; lean_object* v___y_4006_; lean_object* v___y_4007_; lean_object* v___y_4008_; lean_object* v___y_4009_; lean_object* v___x_4032_; 
v_a_4003_ = lean_ctor_get(v___x_4002_, 0);
lean_inc(v_a_4003_);
lean_dec_ref_known(v___x_4002_, 1);
v___x_4032_ = l_Lean_getMaxHeartbeats___redArg(v_a_3997_);
if (lean_obj_tag(v___x_4032_) == 0)
{
lean_object* v_a_4033_; lean_object* v___x_4034_; uint8_t v___x_4035_; 
v_a_4033_ = lean_ctor_get(v___x_4032_, 0);
lean_inc(v_a_4033_);
lean_dec_ref_known(v___x_4032_, 1);
v___x_4034_ = lean_unsigned_to_nat(0u);
v___x_4035_ = lean_nat_dec_eq(v_a_4033_, v___x_4034_);
lean_dec(v_a_4033_);
if (v___x_4035_ == 0)
{
lean_object* v___x_4036_; 
v___x_4036_ = l_Lean_getRemainingHeartbeats___redArg(v_a_3997_);
if (lean_obj_tag(v___x_4036_) == 0)
{
lean_object* v_a_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; 
v_a_4037_ = lean_ctor_get(v___x_4036_, 0);
lean_inc(v_a_4037_);
lean_dec_ref_known(v___x_4036_, 1);
v___x_4038_ = lean_nat_mul(v_leavePercentHeartbeats_3994_, v_a_4037_);
lean_dec(v_a_4037_);
v___x_4039_ = lean_unsigned_to_nat(100u);
v___x_4040_ = lean_nat_div(v___x_4038_, v___x_4039_);
lean_dec(v___x_4038_);
v_minHeartbeats_4005_ = v___x_4040_;
v___y_4006_ = v_a_3995_;
v___y_4007_ = v_a_3996_;
v___y_4008_ = v_a_3997_;
v___y_4009_ = v_a_3998_;
goto v___jp_4004_;
}
else
{
lean_object* v_a_4041_; lean_object* v___x_4043_; uint8_t v_isShared_4044_; uint8_t v_isSharedCheck_4048_; 
lean_dec(v_a_4003_);
lean_dec_ref(v_mctx_4001_);
lean_dec(v_max_3993_);
lean_dec_ref(v_target_3989_);
lean_dec(v_goal_3988_);
v_a_4041_ = lean_ctor_get(v___x_4036_, 0);
v_isSharedCheck_4048_ = !lean_is_exclusive(v___x_4036_);
if (v_isSharedCheck_4048_ == 0)
{
v___x_4043_ = v___x_4036_;
v_isShared_4044_ = v_isSharedCheck_4048_;
goto v_resetjp_4042_;
}
else
{
lean_inc(v_a_4041_);
lean_dec(v___x_4036_);
v___x_4043_ = lean_box(0);
v_isShared_4044_ = v_isSharedCheck_4048_;
goto v_resetjp_4042_;
}
v_resetjp_4042_:
{
lean_object* v___x_4046_; 
if (v_isShared_4044_ == 0)
{
v___x_4046_ = v___x_4043_;
goto v_reusejp_4045_;
}
else
{
lean_object* v_reuseFailAlloc_4047_; 
v_reuseFailAlloc_4047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4047_, 0, v_a_4041_);
v___x_4046_ = v_reuseFailAlloc_4047_;
goto v_reusejp_4045_;
}
v_reusejp_4045_:
{
return v___x_4046_;
}
}
}
}
else
{
v_minHeartbeats_4005_ = v___x_4034_;
v___y_4006_ = v_a_3995_;
v___y_4007_ = v_a_3996_;
v___y_4008_ = v_a_3997_;
v___y_4009_ = v_a_3998_;
goto v___jp_4004_;
}
}
else
{
lean_object* v_a_4049_; lean_object* v___x_4051_; uint8_t v_isShared_4052_; uint8_t v_isSharedCheck_4056_; 
lean_dec(v_a_4003_);
lean_dec_ref(v_mctx_4001_);
lean_dec(v_max_3993_);
lean_dec_ref(v_target_3989_);
lean_dec(v_goal_3988_);
v_a_4049_ = lean_ctor_get(v___x_4032_, 0);
v_isSharedCheck_4056_ = !lean_is_exclusive(v___x_4032_);
if (v_isSharedCheck_4056_ == 0)
{
v___x_4051_ = v___x_4032_;
v_isShared_4052_ = v_isSharedCheck_4056_;
goto v_resetjp_4050_;
}
else
{
lean_inc(v_a_4049_);
lean_dec(v___x_4032_);
v___x_4051_ = lean_box(0);
v_isShared_4052_ = v_isSharedCheck_4056_;
goto v_resetjp_4050_;
}
v_resetjp_4050_:
{
lean_object* v___x_4054_; 
if (v_isShared_4052_ == 0)
{
v___x_4054_ = v___x_4051_;
goto v_reusejp_4053_;
}
else
{
lean_object* v_reuseFailAlloc_4055_; 
v_reuseFailAlloc_4055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4055_, 0, v_a_4049_);
v___x_4054_ = v_reuseFailAlloc_4055_;
goto v_reusejp_4053_;
}
v_reusejp_4053_:
{
return v___x_4054_;
}
}
}
v___jp_4004_:
{
lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; 
lean_inc(v_max_3993_);
v___x_4010_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_4010_, 0, v_max_3993_);
lean_ctor_set(v___x_4010_, 1, v_minHeartbeats_4005_);
lean_ctor_set(v___x_4010_, 2, v_goal_3988_);
lean_ctor_set(v___x_4010_, 3, v_target_3989_);
lean_ctor_set(v___x_4010_, 4, v_mctx_4001_);
lean_ctor_set_uint8(v___x_4010_, sizeof(void*)*5, v_stopAtRfl_3992_);
lean_ctor_set_uint8(v___x_4010_, sizeof(void*)*5 + 1, v_side_3991_);
v___x_4011_ = lean_obj_once(&l_Lean_Meta_Rewrites_findRewrites___closed__1, &l_Lean_Meta_Rewrites_findRewrites___closed__1_once, _init_l_Lean_Meta_Rewrites_findRewrites___closed__1);
v___x_4012_ = lean_mk_empty_array_with_capacity(v_max_3993_);
lean_dec(v_max_3993_);
v___x_4013_ = lean_array_to_list(v_a_4003_);
v___x_4014_ = l_Lean_Meta_Rewrites_takeListAux(v___x_4010_, v___x_4011_, v___x_4012_, v___x_4013_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_);
lean_dec(v___x_4013_);
if (lean_obj_tag(v___x_4014_) == 0)
{
lean_object* v_a_4015_; lean_object* v___x_4017_; uint8_t v_isShared_4018_; uint8_t v_isSharedCheck_4023_; 
v_a_4015_ = lean_ctor_get(v___x_4014_, 0);
v_isSharedCheck_4023_ = !lean_is_exclusive(v___x_4014_);
if (v_isSharedCheck_4023_ == 0)
{
v___x_4017_ = v___x_4014_;
v_isShared_4018_ = v_isSharedCheck_4023_;
goto v_resetjp_4016_;
}
else
{
lean_inc(v_a_4015_);
lean_dec(v___x_4014_);
v___x_4017_ = lean_box(0);
v_isShared_4018_ = v_isSharedCheck_4023_;
goto v_resetjp_4016_;
}
v_resetjp_4016_:
{
lean_object* v___x_4019_; lean_object* v___x_4021_; 
v___x_4019_ = lean_array_to_list(v_a_4015_);
if (v_isShared_4018_ == 0)
{
lean_ctor_set(v___x_4017_, 0, v___x_4019_);
v___x_4021_ = v___x_4017_;
goto v_reusejp_4020_;
}
else
{
lean_object* v_reuseFailAlloc_4022_; 
v_reuseFailAlloc_4022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4022_, 0, v___x_4019_);
v___x_4021_ = v_reuseFailAlloc_4022_;
goto v_reusejp_4020_;
}
v_reusejp_4020_:
{
return v___x_4021_;
}
}
}
else
{
lean_object* v_a_4024_; lean_object* v___x_4026_; uint8_t v_isShared_4027_; uint8_t v_isSharedCheck_4031_; 
v_a_4024_ = lean_ctor_get(v___x_4014_, 0);
v_isSharedCheck_4031_ = !lean_is_exclusive(v___x_4014_);
if (v_isSharedCheck_4031_ == 0)
{
v___x_4026_ = v___x_4014_;
v_isShared_4027_ = v_isSharedCheck_4031_;
goto v_resetjp_4025_;
}
else
{
lean_inc(v_a_4024_);
lean_dec(v___x_4014_);
v___x_4026_ = lean_box(0);
v_isShared_4027_ = v_isSharedCheck_4031_;
goto v_resetjp_4025_;
}
v_resetjp_4025_:
{
lean_object* v___x_4029_; 
if (v_isShared_4027_ == 0)
{
v___x_4029_ = v___x_4026_;
goto v_reusejp_4028_;
}
else
{
lean_object* v_reuseFailAlloc_4030_; 
v_reuseFailAlloc_4030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4030_, 0, v_a_4024_);
v___x_4029_ = v_reuseFailAlloc_4030_;
goto v_reusejp_4028_;
}
v_reusejp_4028_:
{
return v___x_4029_;
}
}
}
}
}
else
{
lean_object* v_a_4057_; lean_object* v___x_4059_; uint8_t v_isShared_4060_; uint8_t v_isSharedCheck_4064_; 
lean_dec_ref(v_mctx_4001_);
lean_dec(v_max_3993_);
lean_dec_ref(v_target_3989_);
lean_dec(v_goal_3988_);
v_a_4057_ = lean_ctor_get(v___x_4002_, 0);
v_isSharedCheck_4064_ = !lean_is_exclusive(v___x_4002_);
if (v_isSharedCheck_4064_ == 0)
{
v___x_4059_ = v___x_4002_;
v_isShared_4060_ = v_isSharedCheck_4064_;
goto v_resetjp_4058_;
}
else
{
lean_inc(v_a_4057_);
lean_dec(v___x_4002_);
v___x_4059_ = lean_box(0);
v_isShared_4060_ = v_isSharedCheck_4064_;
goto v_resetjp_4058_;
}
v_resetjp_4058_:
{
lean_object* v___x_4062_; 
if (v_isShared_4060_ == 0)
{
v___x_4062_ = v___x_4059_;
goto v_reusejp_4061_;
}
else
{
lean_object* v_reuseFailAlloc_4063_; 
v_reuseFailAlloc_4063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4063_, 0, v_a_4057_);
v___x_4062_ = v_reuseFailAlloc_4063_;
goto v_reusejp_4061_;
}
v_reusejp_4061_:
{
return v___x_4062_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Rewrites_findRewrites_0interp(lean_interpreter_value* stack)
{
lean_object* v_hyps_3986_ = stack[0].m_obj;
lean_object* v_moduleRef_3987_ = stack[1].m_obj;
lean_object* v_goal_3988_ = stack[2].m_obj;
lean_object* v_target_3989_ = stack[3].m_obj;
lean_object* v_forbidden_3990_ = stack[4].m_obj;
uint8_t v_side_3991_ = stack[5].m_num;
uint8_t v_stopAtRfl_3992_ = stack[6].m_num;
lean_object* v_max_3993_ = stack[7].m_obj;
lean_object* v_leavePercentHeartbeats_3994_ = stack[8].m_obj;
lean_object* v_a_3995_ = stack[9].m_obj;
lean_object* v_a_3996_ = stack[10].m_obj;
lean_object* v_a_3997_ = stack[11].m_obj;
lean_object* v_a_3998_ = stack[12].m_obj;
lean_object* v_res_4065_;
v_res_4065_ = l_Lean_Meta_Rewrites_findRewrites(v_hyps_3986_, v_moduleRef_3987_, v_goal_3988_, v_target_3989_, v_forbidden_3990_, v_side_3991_, v_stopAtRfl_3992_, v_max_3993_, v_leavePercentHeartbeats_3994_, v_a_3995_, v_a_3996_, v_a_3997_, v_a_3998_);
stack->m_obj
 = v_res_4065_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_findRewrites___boxed(lean_object* v_hyps_4066_, lean_object* v_moduleRef_4067_, lean_object* v_goal_4068_, lean_object* v_target_4069_, lean_object* v_forbidden_4070_, lean_object* v_side_4071_, lean_object* v_stopAtRfl_4072_, lean_object* v_max_4073_, lean_object* v_leavePercentHeartbeats_4074_, lean_object* v_a_4075_, lean_object* v_a_4076_, lean_object* v_a_4077_, lean_object* v_a_4078_, lean_object* v_a_4079_){
_start:
{
uint8_t v_side_boxed_4080_; uint8_t v_stopAtRfl_boxed_4081_; lean_object* v_res_4082_; 
v_side_boxed_4080_ = lean_unbox(v_side_4071_);
v_stopAtRfl_boxed_4081_ = lean_unbox(v_stopAtRfl_4072_);
v_res_4082_ = l_Lean_Meta_Rewrites_findRewrites(v_hyps_4066_, v_moduleRef_4067_, v_goal_4068_, v_target_4069_, v_forbidden_4070_, v_side_boxed_4080_, v_stopAtRfl_boxed_4081_, v_max_4073_, v_leavePercentHeartbeats_4074_, v_a_4075_, v_a_4076_, v_a_4077_, v_a_4078_);
lean_dec(v_a_4078_);
lean_dec_ref(v_a_4077_);
lean_dec(v_a_4076_);
lean_dec_ref(v_a_4075_);
lean_dec(v_leavePercentHeartbeats_4074_);
lean_dec(v_forbidden_4070_);
return v_res_4082_;
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
